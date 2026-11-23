import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.TiedCB

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SpStd (B : ColBase) : Prop where
  X_on : ∀ i, i ≤ B.R.m → ∀ a b, (B.sp.X i).hT ((B.sp.X i).frame a) ((B.sp.X i).frame b) = if a = b then 1 else 0
  selfDual_span_frame_X : ∀ i, i ≤ B.R.m → (B.sp.X i).L0 = Submodule.span (𝓞 B.host.E) (Set.range (B.sp.X i).frame)
  P_on : ∀ a b, B.sp.X'.hT (B.sp.X'.frame a) (B.sp.X'.frame b) = if a = b then 1 else 0
  selfDual_span_frame_auxiliary : B.sp.X'.L0 = Submodule.span (𝓞 B.host.E) (Set.range B.sp.X'.frame)
  iX' : ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b →
    B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b
  z : ∃ c : B.host.E, ∀ b : Fin (B.sp.X B.R.m).rank, (b : ℕ) + 1 = (B.sp.X B.R.m).rank → B.sp.z = c • (B.sp.X B.R.m).frame b

structure HostHyp (d : ColDat) : Prop where
  embE_φ₀ : d.what₂.embLL.comp d.embE = d.host.φ₀
  piT_K : ∀ u, (d.piT u : d.host.E) ∈ d.host.K
  piG_K : ∀ i, (d.piG i : d.host.E) ∈ d.host.K
  cond_eq : d.cond = d.host.QS * d.host.q * d.host.d
  val_eq : ∀ w (x : d.what₂.LL), x ≠ 0 → d.what₂.places.val w x = ((vAdd (d.plEq w) x : ℤ) : WithTop ℤ)

variable {d : ColDat} (a : ColArgs d)

theorem gramN_eq (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) : CF.gramN (d.colRec a) i hi = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X i).hT ((d.sp.X i).frame _) ((d.sp.X i).frame _) = _
  rw [hS.X_on i hi, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem gramP_eq (hS : SpStd d.toColBase) : CF.gramP (d.colRec a) = 1 := by
  refine Matrix.ext fun x y => ?_
  show d.sp.X'.hT (d.sp.X'.frame _) (d.sp.X'.frame _) = _
  rw [hS.P_on, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem clsCrd_eq (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    CF.clsCrd (d.colRec a) u i hi c = (d.repr u i c).1.L := by
  show (d.clsLat u i c).map (((d.crd i hi : (d.sp.X i).V ≃ₗ[d.host.E] (Fin (d.R.N i) → d.host.E)) :
    (d.sp.X i).V →ₗ[d.host.E] (Fin (d.R.N i) → d.host.E)).restrictScalars (𝓞 d.host.E)) = _
  unfold ColDat.clsLat
  rw [dif_pos hi, ← Submodule.map_comp]
  convert Submodule.map_id _
  ext x j
  simp

theorem embT_eq (hH : HostHyp d) : CF.embT (d.colRec a) = d.X.embC d.σ₀ := by
  funext τ
  show d.host.φ₀.comp _ = (d.what₂.embLL).comp (d.embE.comp _)
  rw [← hH.embE_φ₀, RingHom.comp_assoc]

theorem T_eq (u : d.what₂.Word) : ((d.colRec a).mem u).A.T = d.T u := rfl

end Formalism.L2.Col
