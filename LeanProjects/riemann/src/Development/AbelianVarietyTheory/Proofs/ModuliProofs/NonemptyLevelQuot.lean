import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjDescendLowerLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCoverStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelTower

theorem zeta_eq_pow {n m : ℕ} (hm : 0 < m) (h : n ∣ m) : zeta n = zeta m ^ (m / n) := by
  obtain ⟨c, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  have hc : 0 < c := Nat.pos_of_mul_pos_left hm
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c hn, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x (rfl | rfl)
  · exact (baseKA l₂).ρ.2
  · rw [zeta_eq_pow l₂.A_pos h]
    exact pow_mem (baseKA l₂).ζ.2 _

theorem base_rho (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem base_zeta (l : Level H) : (((baseKA l).ζ : KA l) : ℂ) = zeta l.A := rfl

theorem exists_inclusion' {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') :
    ∃ j : F →+* F', ∀ x, ((j x : F') : ℂ) = ((x : F) : ℂ) :=
  ⟨(IntermediateField.inclusion h).toRingHom, fun x => IntermediateField.coe_inclusion h x⟩

theorem exists_inclusion {l l₂ : Level H} (h : l.A ∣ l₂.A) :
    ∃ j : KA l →+* KA l₂, (∀ x, ((j x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ j (baseKA l).ρ = (baseKA l₂).ρ ∧
      j (baseKA l).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  obtain ⟨j, hj⟩ := exists_inclusion' (KA_le h)
  refine ⟨j, hj, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [hj, base_rho, base_rho]
  · rw [hj, IntermediateField.coe_pow, base_zeta, base_zeta]
    exact zeta_eq_pow l₂.A_pos h

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x (rfl | rfl)
  · refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_natCast H.d).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem finite_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : j.Finite := by
  letI := j.toAlgebra
  exact Module.Finite.of_restrictScalars_finite ℚ K K'

theorem etale_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : Etale (spMap j) := by
  letI := j.toAlgebra
  haveI : Module.Finite K K' := finite_of_numberField j
  haveI : Algebra.FormallyEtale K K' := Algebra.FormallyEtale.of_isSeparable K K'
  haveI : Algebra.FinitePresentation K K' := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K K' := ⟨inferInstance, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr this

end GlobalTheory.LevelTower

namespace GlobalTheory

open LevelTower

theorem nonempty_levelQuot : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (LevelQuot l Xo₂) := by
  intro hL hL2 hTh E _ _ _ H D l l₂ Xo₂ hpq hdvd
  have hA : l.A ∣ l₂.A := hdvd.2.2
  obtain ⟨jK, hj, hjρ, hjζ⟩ := exists_inclusion hA
  haveI := finiteDimensional_KA l₂
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ :=
    GlobalTheory.LevelGroup.exists_group_action hL hL2 E H D l l₂ Xo₂ jK hpq hdvd hj
  have hq : IsQProjOver (Xo₂.s ≫ spMap jK) :=
    (isQProjOver_baseChange_and_finite_restrict _ _ jK Xo₂.X (Xo₂.s ≫ spMap jK)).2 Xo₂.s
      (finite_of_numberField jK) Xo₂.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    exists_isGaloisCover_of_isQProjOver (KA l) Xo₂.X (Xo₂.s ≫ spMap jK) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := GlobalTheory.T.isQProjOver_target_of_isGaloisCover (KA l) _ Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension D.dim (π ≫ sY) := by
    rw [hπ]
    haveI := Xo₂.smooth
    haveI : Etale (spMap jK) := etale_of_numberField jK
    haveI : SmoothOfRelativeDimension 0 (spMap jK) := inferInstance
    have := smoothOfRelativeDimension_comp D.dim 0 Xo₂.s (spMap jK)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension D.dim sY := GlobalTheory.T.smoothOfRelativeDimension_descends_etale_cover (KA l) _ Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨t', m, hνm, hp, ha, hk⟩ := GlobalTheory.T.exists_abelianTriple_descent_galoisCover hL hL2 hTh E H (KA l) _ Y π sY Ga ρ Xo₂.univ.t _ ν hG hqY
    Xo₂.univ.proper (obj_isAbelianScheme_dim_rigidified_sym E H D l₂ _ _ _ _ Xo₂.univ).2.1
    Xo₂.univ.ample Xo₂.univ.ktriv hν1 hνmul
  obtain ⟨ob, m', hη, hηA⟩ := obj_descend_lower_level hL hL2 E H D l l₂ _ _ (baseKA l) (baseKA l₂) jK _ Y π sY
    Xo₂.s Ga ρ Xo₂.univ (fun a => (ν a).φ) t' m hdvd hjρ hjζ
    hπ hG hνm hlow hp ha hk
  refine ⟨⟨Y, sY, hqY, hsY, ob, π, jK, hj, hπ, hG.fin, hG.etale, hG.onto, m', hη, hηA, ?_⟩⟩
  intro K _ _ y y' t mu mu' eM eA h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans K y y' t mu mu' eM eA h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

end GlobalTheory

end
