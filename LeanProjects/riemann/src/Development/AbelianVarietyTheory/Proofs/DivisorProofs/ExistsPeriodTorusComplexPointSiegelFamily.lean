import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyNearbyPeriodsSameComponent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeLiftOfLevelSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisCongrLevelModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelPeriodOfSymplecticBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExistsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.SiegelPtAt

theorem sqrt_at_point (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ) (hk : 3 ≤ k)
    (hζ : σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k)) (p : Sp ℂ ⟶ F.X) :
    ∃ (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ F.univ.A.left), SqOf P F.univ p φ := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hζ' : IsUnit ζ := IsUnit.mk0 _ fun e => Complex.exp_ne_zero _ (by rw [← hζ, e, map_zero])
  obtain ⟨R, _, π, p₁, Q₁, φ₁, -, rfl, hQ₁, -⟩ := GlobalTheory.SiegelNearby.exists_etale_sqrt hL σ F (by omega) hζ' p
  obtain ⟨P, ψ, hpb⟩ := GlobalTheory.SiegelNearby.exists_polPB hL.polBaseChange Q₁ p₁
  exact ⟨P, ψ ≫ φ₁, (sqOf_calculus h k K ζ _ _ _ F.s F.univ π).1 p₁ Q₁ P φ₁ ψ hQ₁ hpb⟩

theorem levels_pull {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (hsq : SqOf P c p φ) :
    ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A),
      (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) ∧ (∀ a b, lev (a + b) = lev a * lev b) ∧
        ∀ a, lev a ^ k = 1 := by
  choose l hl hl' using fun a => GlobalTheory.SiegelNearby.exists_section_pull hsq.1 (c.lev a) k (c.lev_tors a)
  refine ⟨l, hl', fun a b => ?_, hl⟩
  have key := hsq.1.2 (𝟙_ (Over (Sp ℂ))) (l a) (l b) (toUnit _ ≫ c.lev a) (toUnit _ ≫ c.lev b)
    (by rw [Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left, hl']; exact congrArg (· ≫ _) (Category.id_comp p))
    (by rw [Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left, hl']; exact congrArg (· ≫ _) (Category.id_comp p))
  rw [← MonObj.comp_mul, ← c.lev_add, Over.comp_left, GlobalTheory.SiegelNearby.toUnit_left] at key
  apply Over.OverMorphism.ext
  apply hsq.1.1.hom_ext
  · rw [hl', ← key]; exact (Category.id_comp _).symm
  · rw [Over.w, Over.w]

theorem perLev_of_level (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A))
    (hg : P.g = h) (hk : 0 < k) (add : ∀ a b, lev (a + b) = lev a * lev b) (tors : ∀ a, lev a ^ k = 1)
    (weil : ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) →
      Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) :
    ∃ τ : Matrix (Fin h) (Fin h) ℂ, PerLev P τ k lev := by
  obtain ⟨u, Hm, χ, Ef, hAH, hEf, hbij, halt, hfree, hfin, hrank, hW⟩ := GlobalTheory.T.exists_appellHumbert_unimodular_riemannForm h P hg
  obtain ⟨l, hl, hdvd⟩ := GlobalTheory.T.exists_lattice_lift_of_level_section h k P lev u Ef hk add tors weil (fun x y e he => hW k x y e hk he)
  obtain ⟨B, hB, hBl⟩ := GlobalTheory.T.exists_symplectic_basis_congr_level_mod h k u.Λ Ef l hk hrank halt hbij hdvd
  let v : Fin h ⊕ Fin h → (Fin h → ℂ) := fun i => (B (Pi.single i 1) : Fin h → ℂ)
  have hv : ∀ i j, (hermForm Hm (v i) (v j)).im =
      (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ) := fun i j => by
    rw [← hEf, hB]
  obtain ⟨τ, T, hs, hp, hT⟩ := GlobalTheory.T.exists_siegel_period_of_symplectic_basis h Hm v hAH.1 hAH.2.1 hv
  obtain ⟨u', hex, hΛ⟩ := GlobalTheory.T.holUnif_comp_linearEquiv_exists h P.A P.L u T
  have hBa : ∀ a, (B a : Fin h → ℂ) = ∑ i, a i • v i := fun a => by
    conv_lhs => rw [show a = ∑ i, a i • (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp only [v, map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul]
  refine ⟨τ, hg, hs, hp, u', fun z => ?_, fun n a b e hn he => ?_, fun a => ?_⟩
  · rw [hΛ]
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := B.surjective ⟨T z, hz⟩
      refine ⟨a, T.injective ?_⟩
      rw [hT, ← hBa, ha]
    · rintro ⟨a, rfl⟩
      rw [hT, ← hBa]
      exact (B a).2
  · have := hW n (B a) (B b) e hn (by rw [hB]; exact he)
    rwa [hex, hex, map_smul, map_smul, hT, hT, ← hBa, ← hBa]
  · rw [hl, hex, map_smul, hT, ← hBa]
    obtain ⟨m, hm⟩ := hBl a
    have e : ((l a : u.Λ) : Fin h → ℂ) = (B a : Fin h → ℂ) + (k : ℂ) • (m : Fin h → ℂ) := by
      rw [← sub_eq_iff_eq_add', ← Submodule.coe_sub, hm, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ]
      norm_cast
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    rw [e, smul_add, smul_smul, inv_mul_cancel₀ hk', one_smul, u.ex_add, (u.ker _).2 m.2, _root_.mul_one]

theorem exists_ptAt : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ → ∃ τ : Matrix (Fin h) (Fin h) ℂ, PtAt F.univ p τ := by
  intro h k K _ ζ σ F _ hk hodd hζ p hp
  obtain ⟨P, φ, hsq⟩ := sqrt_at_point h k K ζ σ F hk hζ p
  obtain ⟨lev, hlev, add, tors⟩ := levels_pull F.univ p P φ hsq
  have weil := GlobalTheory.T.siegel_square_root_weil_pairing_standard h k K ζ σ F.X F.s F.univ p P φ lev hk hodd hζ hp hsq hlev add tors
  obtain ⟨τ, hτ⟩ := perLev_of_level h k P lev hsq.2.1 (by omega) add tors weil
  exact ⟨τ, P, lev, φ, hτ, hsq, hlev⟩

end GlobalTheory.SiegelPtAt
