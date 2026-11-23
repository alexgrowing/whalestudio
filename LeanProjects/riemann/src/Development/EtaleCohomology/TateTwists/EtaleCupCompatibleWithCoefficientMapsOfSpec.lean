import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleCupProductNaturalInCoefficients

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCupCompatAlexanderWhitneyCocycleSpec : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

theorem etale_cochain_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (add_zero n) (-(p : ℤ)) s s h (add_zero s), Cochain.ofHom_v]
  rfl

theorem etale_cocycle_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (zcomp α (Cocycle.ofHom m) (add_zero n)).1 p s h U x = Sec.map (m.f s) (ev α.1 p s h U x) :=
  etale_cochain_comp_hom_evaluation_eq_map m α.1 p s h U x

theorem etale_cup_compatible_with_coefficient_maps_of_spec (hspec : EtaleCupCompatAlexanderWhitneyCocycleSpec) : EtaleCupProductNaturalInCoefficients := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, hγ⟩ := (hspec R μ hk).1 α β
  rw [(hspec R μ hk).2 α β γ hγ, cpost_mk, cpost_mk, cpost_mk]
  symm
  apply (hspec R ν hk).2
  intro N w h U x
  rw [etale_cocycle_comp_hom_evaluation_eq_map, hγ N w h U x]
  simp only [Sec.map]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, etale_cocycle_comp_hom_evaluation_eq_map, etale_cocycle_comp_hom_evaluation_eq_map]
  congr 1
  exact hc U _ _ w _ _ _

end LateralTheory.EtaleFoundations
