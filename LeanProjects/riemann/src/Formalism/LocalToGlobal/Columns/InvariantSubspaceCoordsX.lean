import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_asAlgebraHom_eq (a : MonoidAlgebra K A) : ρ.asAlgebraHom a = ∑ t : A, a.coeff t • ρ t := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp [Finsupp.sum_fintype]

theorem rf_coord_act (t : A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ t φ) = ((S.toCSD h).actMat (S.repCSD h ρ) t).mulVec (S.coordOf h S.outSec φ) := by
  have c : ∀ x, S.coordOf h S.outSec x = ⇑((S.toCSD h).basis.repr (S.res h x)) := fun x => rfl
  have e1 : (S.repCSD h ρ) t (S.res h φ) = S.res h (ρ t φ) := by
    show (S.res h) (ρ t ((S.res h).symm (S.res h φ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [c, c]
  unfold CSD.actMat
  rw [LinearMap.toMatrix_mulVec_repr, e1]

theorem rf_coord_ga (a : MonoidAlgebra K A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ.asAlgebraHom a φ) =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVec (S.coordOf h S.outSec φ) := by

  have hsum : ∀ {m : ℕ} (M : A → Matrix (Fin m) (Fin m) K) (c : A → K) (v : Fin m → K),
      (∑ t, c t • M t).mulVec v = ∑ t, c t • (M t).mulVec v := by
    intro m M c v
    rw [← Matrix.toLin'_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply]
  rw [rf_asAlgebraHom_eq, LinearMap.sum_apply, map_sum]
  unfold CSD.gaMat
  rw [hsum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [LinearMap.smul_apply, map_smul, rf_coord_act]

theorem rf_range_ga (a : MonoidAlgebra K A) :
    (LinearMap.range (ρ.asAlgebraHom a)).map (S.coordOf h S.outSec).toLinearMap =
      LinearMap.range ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin := by
  have e : (S.coordOf h S.outSec).toLinearMap ∘ₗ ρ.asAlgebraHom a =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin ∘ₗ (S.coordOf h S.outSec).toLinearMap := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    exact rf_coord_ga S h ρ a φ
  rw [← LinearMap.range_comp, e, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

private theorem range_subE_lemma {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (Z : Submodule K (Fin n → K)) :
    LinearMap.range (subE Z).mulVecLin = Z := by
  rw [Matrix.range_mulVecLin]
  have e : (subE Z).col = ⇑Z.subtype ∘ ⇑(subBasis Z) := by
    funext j i
    rfl
  rw [e, Set.range_comp, Submodule.span_image, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem invariantSubspace_coords_X (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : (mtildeKGSD W Ch sel mu).Ok) :
    (V0X W Ch sel mu Xg P).map ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).toLinearMap =
      LinearMap.range ((V0C W Ch sel mu h Xg P).E).mulVecLin := by
  unfold V0X
  rw [rf_range_ga]
  exact (range_subE_lemma _).symm

end Rows

section LvlPart

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_mem_lvlPart_iff (P : Subgroup A) (ψ : P →* Kˣ) (φ : S.EqFun) :
    S.coordOf h S.outSec φ ∈ (S.toCSD h).lvlPart (S.repCSD h ρ) P ψ ↔
      ∀ a : P, ρ (a : A) φ = ((ψ a : Kˣ) : K) • φ := by
  show (∀ a : P, ((S.toCSD h).actMat (S.repCSD h ρ) (a : A)).mulVec (S.coordOf h S.outSec φ) =
      ((ψ a : Kˣ) : K) • S.coordOf h S.outSec φ) ↔ _
  refine forall_congr' (fun a => ?_)
  rw [← rf_coord_act, ← map_smul]
  exact (S.coordOf h S.outSec).injective.eq_iff

end LvlPart

section RowsLvl

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem mem_lvlPartX_iff (h : (mtildeKGSD W Ch sel mu).Ok) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec φ ∈
        (MtildeKCSD W Ch sel mu h).lvlPart (g0Act W Ch sel mu h) P.grp P.chr ↔
      φ.1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine Iff.trans ?_ (mem_MtildeV_iff W Ch sel mu P φ.1).symm
  exact (rf_mem_lvlPart_iff _ h (g0HatRepEqFunX W Ch sel mu) P.grp P.chr φ).trans ⟨fun H => ⟨φ.2, H⟩, fun ⟨_, H⟩ => H⟩

end RowsLvl

end Formalism.L2.Col
