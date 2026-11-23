import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocCocOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCocycleTangentContractionCohomologousTorsorStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem contr_chern_eq_tanCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) → (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) → ∀ κ : Fn1 A, IsContr w.1 v κ → ∃ u : Fn1 (A ⊗ B), IsCoc P.U u ∧ Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull u v)) := by
  intro R _ A B _ _ P hP v hv j hj w hch hw κ hκ
  obtain ⟨i, hi, U, ℓ, hU, hℓ, hcl⟩ := hch
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hcl
  obtain ⟨n, hn⟩ := hcl
  refine ⟨cocOf P.U n, isCoc_cocOf P.U n ?_, GlobalTheory.T.chernCocycle_tangentContraction_cohomologous_torsor R A B P hP v hv j hj w hw i hi U ℓ hU hℓ n hn κ hκ⟩
  intro T T' T'' a b h h' h''
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hn T) T') T'') a) b
  rw [e]
  have h0 : ℓ.1 T T' T'' a b = 0 := by
    have := (hℓ T T' T'' a b).1
    rw [h''] at this
    exact (Ideal.mem_bot).1 this
  change w.1 _ _ _ _ _ - ℓ.1 T T' T'' a b = 0
  rw [h0, sub_zero]
  exact hw _ _ _ _ _ h h' h''

end GlobalTheory.PtExt
