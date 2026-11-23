import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionFlattenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflattenStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionLimitSq

section Flat

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem good_sq_iff (z : Z) (J' : (Z ⟶ X) → L.ι) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) z (fun ψ _ => J' ψ) ↔ Good L z J' := by
  constructor
  · intro h ψ
    have := GlobalTheory.Algebraise.mem_wc.1 (h ψ)
    simpa using this
  · intro h ψ
    exact GlobalTheory.Algebraise.mem_wc.2 (by simpa using h ψ)

theorem eq_const_of_fin_one {α β : Type} (J : α → (Fin 1 → β)) : J = fun ψ _ => J ψ 0 :=
  funext fun ψ => funext fun κ => congrArg (J ψ) (Subsingleton.elim _ _)

theorem sval_flat {a n m : ℤ} {g : Y ⟶ X} {t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))}
    {s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g)
      (fun _ => n))}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j →
      gs r z _ (t.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j))
    (r : Z ⟶ Y) (z : Z) (J' : (Z ⟶ X) → L.ι) (hJ : Good L z J') :
    sval t r z J' = sval s r z (fun ψ _ => J' ψ) :=
  h Z r z (J' (r ≫ g)) (by simpa using hJ (r ≫ g))

end Flat

theorem existsUnique_sec_of_compatible_sq : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hm : (((2 * n : ℕ) : ℤ)) = 2 * (n : ℤ) := by push_cast; ring
  have hn2 : 1 ≤ 2 * n := by omega
  choose t ht using fun e => GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (fstG I e P.A).left (s e)
  have htc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι),
      Good P.L z J → sval (t (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (t e) r z J := by
    intro e Z r z J hJ
    rw [sval_flat (ht (e + 1)) _ z J hJ, sval_flat (ht e) r z J hJ]
    exact hs e Z r z _ ((good_sq_iff z J).2 hJ)
  obtain ⟨σ₀, hσ₀, hσ₀u⟩ := GlobalTheory.SectionLimit.existsUnique_sec_of_compatible hS R I P (2 * n) hn2 t htc
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.linComb_pow_section_unflatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ₀
  refine ⟨σ, fun e Z r z J hJ => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨J', rfl⟩ : ∃ J' : (Z ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff z J').1 hJ
    rw [← sval_flat hσ _ z J' hJ', hσ₀ e Z r z J' hJ', sval_flat (ht e) r z J' hJ']
  · obtain ⟨τ, hτ⟩ := GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ'
    have hτσ : τ = σ₀ := hσ₀u τ fun e Z r z J hJ => by
      rw [sval_flat hτ _ z J hJ, hσ' e Z r z _ ((good_sq_iff z J).2 hJ), ← sval_flat (ht e) r z J hJ]
    have hL := LB.isLB_linComb P.isLB (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (2 : ℤ))
    refine DVR.SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    obtain ⟨J', rfl⟩ : ∃ J' : (P.A.left ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff y J').1 hJ
    rw [← sval_flat hτ _ y J' hJ', ← sval_flat hσ _ y J' hJ', hτσ]

end GlobalTheory.SectionLimitSq
