import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormLtOneOfIrreducible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuationLeIffEqIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestValuation

open GlobalTheory.ZH.PsiForm

theorem norm_eq_one_of_isUnit {o F : Type} [CommRing o] [NormedField F] (f : o →+* F) (h : ∀ a, ‖f a‖ ≤ 1)
    {a : o} (ha : IsUnit a) : ‖f a‖ = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h3 : ‖f a‖ * ‖f b‖ = 1 := by rw [← norm_mul, ← map_mul, hb, map_one, norm_one]
  refine le_antisymm (h a) ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left (h b) (norm_nonneg _)
    _ = _ := mul_one _

theorem isUnit_of_norm_eq_one {V : Type} [CommRing V] [IsDomain V] {F : Type} [NormedField F]
    [Algebra (FractionRing V) F]
    (hle : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))
    {a : V} (ha : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a)‖ = 1) : IsUnit a := by
  have h0 : algebraMap V (FractionRing V) a ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at ha
    exact zero_ne_one ha
  obtain ⟨w, hw⟩ := (hle (algebraMap V (FractionRing V) a)⁻¹).1 (by rw [map_inv₀, norm_inv, ha, inv_one])
  refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_)
  rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]

theorem isPrimitiveRoot_map {o F : Type} [CommRing o] [IsDomain o] [Field F] [CharZero F] (f : o →+* F) {ζ : o}
    {n : ℕ} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (f ζ) n := by
  have h1 := h.isRoot_cyclotomic hn
  have h2 := h1.map (f := f)
  rw [Polynomial.map_cyclotomic] at h2
  exact (Polynomial.isRoot_cyclotomic_iff_charZero hn).1 h2

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → CharZero u.V ∧ IsUnit ((ρ.n : ℕ) : u.V) ∧ AdmBase u.V (IsLocalRing.maximalIdeal u.V) ∧ ‖((S.r * S.N : ℕ) : PadicAlgCl p)‖ = 1 ∧ IsPrimitiveRoot (y₀ (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) ∧ ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ ∧ ValOver ϖ (PadicAlgCl p) v ∧ NormIs u l ϖ Q v lam := by
  intro o Ω _ _ _ hA S ρ p _ y₀ u l hy
  haveI : IsDomain o := hA.ded.toIsDomain
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  have hN : ‖((S.r * S.N : ℕ) : PadicAlgCl p)‖ = 1 := by
    have := norm_eq_one_of_isUnit (y₀.comp (algebraMap o S.R)) hy S.unit
    rwa [map_natCast] at this
  have hpos : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  refine ⟨?_, ?_, ⟨inferInstance, inferInstance, inferInstance, u.complete⟩, hN,
    isPrimitiveRoot_map (y₀.comp (algebraMap o S.R)) (pow_pos hpos 2) S.prim, ?_⟩
  · exact ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  · have h1 : IsUnit ((S.r * S.N : ℕ) : u.V) :=
      isUnit_of_norm_eq_one u.norm_le (by rw [map_natCast, map_natCast, hN])
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast ?_) h1
    rw [ρ.N_eq, ← pow_mul]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by have := ρ.two_le; omega)) _
  · choose Q hQ using QForm.exists_QVal hϖ u.D
    have h0 := norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
    have h1 := norm_lt_one_of_irreducible u.norm_le hϖ
    obtain ⟨v, hv1, hv2⟩ := GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff p _ h0 h1
    refine ⟨ϖ, Q, v, _, hϖ, ?_, neg_pos.2 (Real.log_neg h0 h1), hQ, fun χ => ?_, hv1, hv2⟩
    · intro c n hc
      rw [hv2, norm_of_hasVal u.norm_le hϖ hc, Rat.cast_intCast]
    · have hc := u.D.toPre.P.isLB.cover
      let x : Sp u.V := IsLocalRing.closedPoint u.V
      have hx : (u.D.toPre.c χ).left x ∈ ⨆ i, u.D.toPre.P.L.U i := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      have htop : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U i :=
        ((IsLocalRing.closedPoint_mem_iff (R := u.V) _).1 hi).ge
      have e1 := l.q_eq χ (fun _ => i) htop
      have e2 := norm_of_hasVal u.norm_le hϖ
        (hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => i) htop)
      exact neg_injective (Real.exp_injective (e1.symm.trans e2))

end GlobalTheory.TestValuation
