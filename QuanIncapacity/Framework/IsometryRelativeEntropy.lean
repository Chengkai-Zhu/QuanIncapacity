import QuanIncapacity.Framework.IsometryCompression
import QIT.Information.Renyi.IsometryImageMean

/-! Invariance of the actual EReal relative entropy under isometric
embedding, for supported input pairs, including singular states. -/

noncomputable section
open QIT

namespace QuanIncapacity

variable {a b : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

theorem relativeEntropy_isometry (V : ReferenceIsometry a b) (ρ σ : State a)
    (hs : Matrix.Supports ρ.matrix σ.matrix) :
    ((Channel.ofReferenceIsometry V).applyState ρ).relativeEntropy
      ((Channel.ofReferenceIsometry V).applyState σ) = ρ.relativeEntropy σ := by
  let N := Channel.ofReferenceIsometry V
  have hout := State.channel_map_supports N σ.pos hs
  have hcompress : V.matrix.conjTranspose * (N.applyState σ).matrix * V.matrix = σ.matrix := by
    change V.matrix.conjTranspose * MatrixMap.ofReferenceIsometry V σ.matrix * V.matrix = _
    rw [MatrixMap.ofReferenceIsometry_apply]
    simpa only [IsometryCompression.map_apply] using IsometryCompression.map_image V σ.matrix
  apply le_antisymm
  · exact State.relativeEntropy_dataProcessing_channel_ge ρ σ N
  · have h := State.relativeEntropyPSDReferenceTraceLogE_isometryImage_ge_compression
      ρ V (N.applyState σ).pos hout
    simpa only [State.relativeEntropy, hcompress] using h

end QuanIncapacity
