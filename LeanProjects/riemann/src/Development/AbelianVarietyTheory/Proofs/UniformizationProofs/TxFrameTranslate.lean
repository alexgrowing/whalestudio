import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ShortestVectorStrictOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffRecoveryByTorsionAverages
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubsingletonIffUnitThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaAverage
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

section Sums
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

theorem sumV_finset_sum {Ix K : Type} (s : Finset K) {x : K → Ix → F} {c : K → F} (h : ∀ k, SumV v (x k) (c k)) :
    SumV v (fun i => ∑ k ∈ s, x k i) (∑ k ∈ s, c k) := by
  classical
  intro q
  choose S hS using fun k => h k q
  refine ⟨s.biUnion S, fun T hT => ?_⟩
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  exact v.map_le_sum fun k hk => hS k T ((Finset.subset_biUnion_of_mem S hk).trans hT)

theorem nsmul_inj {X : Type} [AddCommGroup X] [Module.Free ℤ X] {m : ℕ} (hm : 0 < m) {a b : X} (h : m • a = m • b) :
    a = b := by
  have : (m : ℤ) • a = (m : ℤ) • b := by rwa [natCast_zsmul, natCast_zsmul]
  exact smul_right_injective X (by exact_mod_cast hm.ne') this

theorem sumV_average [IsAlgClosed F] [CharZero F] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {m : ℕ} (hm : 0 < m) (a : X → F) (u : (Multiplicative X →* Fˣ) → Fˣ) (c : (Multiplicative X →* Fˣ) → F)
    (hc : ∀ τ : Multiplicative X →* Fˣ, τ ^ (m ^ 2) = 1 →
      SumV v (fun χ => (u τ).val * (τ (Multiplicative.ofAdd (m • χ))).val * a χ) (c τ)) (χ₀ : X) :
    SumV v (fun z : X => a (χ₀ + m • z)) (((m : F) ^ (2 * Module.finrank ℤ X))⁻¹ *
      ∑ᶠ τ : {τ : Multiplicative X →* Fˣ // τ ^ (m ^ 2) = 1},
        ((u τ.1 * τ.1 (Multiplicative.ofAdd (m • χ₀)))⁻¹).val * c τ.1) := by
  classical
  have hN : 0 < m ^ 2 := pow_pos hm 2
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ m ^ 2 = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ m ^ 2 = 1}
  rw [finsum_eq_sum_of_fintype]
  have s := sumV_smul (((m : F) ^ (2 * Module.finrank ℤ X))⁻¹) (sumV_finset_sum Finset.univ
    fun τ : {t : Multiplicative X →* Fˣ // t ^ m ^ 2 = 1} =>
      sumV_smul ((u τ.1 * τ.1 (Multiplicative.ofAdd (m • χ₀)))⁻¹).val (hc τ.1 τ.2))
  have e : ∀ χ, ((m : F) ^ (2 * Module.finrank ℤ X))⁻¹ * ∑ τ : {t : Multiplicative X →* Fˣ // t ^ m ^ 2 = 1},
      ((u τ.1 * τ.1 (Multiplicative.ofAdd (m • χ₀)))⁻¹).val *
        ((u τ.1).val * (τ.1 (Multiplicative.ofAdd (m • χ))).val * a χ) =
      if ∃ z, m • χ = m • χ₀ + m ^ 2 • z then a χ else 0 := fun χ => by
    have e₁ : ∀ τ : {t : Multiplicative X →* Fˣ // t ^ m ^ 2 = 1},
        ((u τ.1 * τ.1 (Multiplicative.ofAdd (m • χ₀)))⁻¹).val *
          ((u τ.1).val * (τ.1 (Multiplicative.ofAdd (m • χ))).val * a χ) =
        ((τ.1 (Multiplicative.ofAdd (m • χ₀)))⁻¹).val * (τ.1 (Multiplicative.ofAdd (m • χ))).val * a χ := fun τ => by
      rw [mul_inv, Units.val_mul]
      linear_combination ((τ.1 (Multiplicative.ofAdd (m • χ₀)))⁻¹).val *
        (τ.1 (Multiplicative.ofAdd (m • χ))).val * a χ * (u τ.1).inv_mul
    simp only [e₁]
    rw [← Finset.sum_mul, GlobalTheory.TorsRecov.sum_tors F X _ hN]
    split_ifs
    · rw [Nat.cast_pow, ← pow_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hm0)]
    · rw [zero_mul, mul_zero]
  simp only [e] at s
  have := sumV_comp (f := fun z : X => χ₀ + m • z) (fun z z' h => nsmul_inj hm (add_left_cancel h))
    (fun β hβ => if_neg fun ⟨z, hz⟩ => hβ ⟨z, nsmul_inj hm (by rw [hz, smul_add, sq, mul_smul])⟩) s
  have e₂ : ∀ z : X, ∃ z', m • (χ₀ + m • z) = m • χ₀ + m ^ 2 • z' := fun z => ⟨z, by rw [smul_add, sq, mul_smul]⟩
  simpa only [e₂, if_true] using this

end Sums

section Frames
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_translate {t : Multiplicative D.X →* Fˣ} {g g₀ g' : GtPtF D F} (ht : IsTor t g₀) (hadd : g.IsAdd g₀ g') :
    g'.b = g.b ∧ ∀ χ z J, Good D.P.L z J → (val (g'.s χ) (𝟙 _) z J).val =
      cstH z (t (Multiplicative.ofAdd χ)).val * (val (g.s χ) (𝟙 _) z J).val := by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  rw [ht.1, _root_.mul_one] at hb
  refine ⟨hb, fun χ z J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have e := hs χ z J hJ
  have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
  rw [e₀, _root_.mul_one] at e
  rw [e, Units.val_mul, ht.2 χ z J hJ, cst_eq, mul_comm]

theorem coef_translate {k : ℕ} {t : Multiplicative D.X →* Fˣ} {g g₀ g' : GtPtF D F} (ht : IsTor t g₀)
    (hadd : g.IsAdd g₀ g') {w : Frm D F k g.b} (hw : w.IsGen) {w' : Frm D F k g'.b} {c : F}
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cstH z c * (val w (𝟙 _) z J).val) (s : Fam D F k) (χ : D.X) :
    coef s g' w' χ = c * (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  obtain ⟨hb, hs⟩ := val_translate ht hadd
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hv z J hJ, hs χ z J hJ, e₁]
  simp only [cst_eq, map_mul] at a ⊢
  linear_combination cstH z c * cstH z (t (Multiplicative.ofAdd χ)).val * a

theorem txFrame_translate [IsNoetherianRing R] (hM : MulPullSt) {N : ℕ} (hN : Odd N) {t : Multiplicative D.X →* Fˣ}
    (htN : t ^ N = 1) {p q : QkPt D F N} {g₀ : GtPtF D F} (hy : q.y = p.y) (ht : IsTor t g₀) (hadd : p.g.IsAdd g₀ q.g)
    {w : Frm D F N p.g.b} {w' : Frm D F N q.g.b} (hw : TXFrame N p w) (hw' : TXFrame N q w') (z J)
    (hJ : Good D.P.L z J) : (val w' (𝟙 _) z J).val =
      cstH z (t (Multiplicative.ofAdd p.y) ^ ((N + 1) / 2)).val * (val w (𝟙 _) z J).val := by
  obtain ⟨hb, hs⟩ := val_translate ht hadd
  obtain ⟨ν, hν⟩ := SymFrame.exists_nu (D := D) hM N
  obtain ⟨κ, hκ⟩ := SymFrame.exists_kap (D := D) hM N
  let u : ((TF (R := R) F).left.presheaf.stalk z)ˣ :=
    Units.map (cstH (R := R) z).toMonoidHom (t (Multiplicative.ofAdd p.y))
  have uN : u ^ N = 1 := by rw [← map_pow, ← MonoidHom.pow_apply, htN, MonoidHom.one_apply, map_one]
  have a₁ := hw.2.1 ν hν z J hJ
  have a₂ := hw.2.2 κ hκ z J hJ
  have b₁ := hw'.2.1 ν hν z J hJ
  have b₂ := hw'.2.2 κ hκ z J hJ
  have c₁ : val (q.g.s q.y) (𝟙 _) z J = u * val (p.g.s p.y) (𝟙 _) z J := by
    rw [hy]; exact Units.ext (hs p.y z J hJ)
  have c₂ : val ν q.g.b.left z J = val ν p.g.b.left z J := by rw [hb]
  have c₃ : val κ q.g.b.left z J = val κ p.g.b.left z J := by rw [hb]
  have c₄ : val (D.psi q.y) (jFK (R := R) F) z J = val (D.psi p.y) (jFK (R := R) F) z J := by rw [hy]
  rw [c₁, c₂, _root_.mul_assoc, ← a₁] at b₁
  rw [c₃, c₄, ← a₂] at b₂
  have b₃ := mul_right_cancel b₂
  obtain ⟨k, rfl⟩ := hN
  have alg : ∀ {U : Type} [CommGroup U] (x y u : U), x ^ 2 = u * y ^ 2 → x ^ (2 * k + 1) = y ^ (2 * k + 1) →
      u ^ (2 * k + 1) = 1 → x = u ^ (k + 1) * y := by
    intro U _ x y u h₁ h₂ h₃
    have a₁ := congrArg Additive.ofMul h₁
    have a₂ := congrArg Additive.ofMul h₂
    have a₃ := congrArg Additive.ofMul h₃
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₂ - k • a₁ - a₃
  rw [alg _ _ _ b₁ b₃ uN, show (2 * k + 1 + 1) / 2 = k + 1 by omega, Units.val_mul, ← map_pow]
  rfl

end Frames

attribute [local instance] gtGroup

theorem main : AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) (g' : GtPtF D.toPre F) (w' : Frm D.toPre F 1 g'.b), Cl.SeriesFrame m p g' w' →
  (GenV hϖ hv w' ((Q p.y : ℚ) / (m ^ 2 : ℕ)) ∧ GtV hϖ hv g' (fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / m) ∧
    ∀ χ, (Q p.y : ℚ) / (m ^ 2 : ℕ) + (QForm.bOf D.toPre Q p.y χ : ℚ) / m + Q χ = (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) ∧
  (∀ τ : Multiplicative D.toPre.X →* Fˣ, τ ^ (m ^ 2) = 1 → ∃ (q : QkPt D.toPre F (m ^ 2)) (g₀ : GtPtF D.toPre F) (x : TFK (R := V) F ⟶ A.A) (t : SecA A F (m ^ 2)) (c : F), q.y = p.y ∧ IsTor τ g₀ ∧ p.g.IsAdd g₀ q.g ∧ QkToAkU U.toUnifPre F (m ^ 2) q x ∧ ThC A ρ m th x t c) ∧
  (∀ c : (Multiplicative D.toPre.X →* Fˣ) → F, (∀ τ : Multiplicative D.toPre.X →* Fˣ, τ ^ (m ^ 2) = 1 → ∃ (q : QkPt D.toPre F (m ^ 2)) (g₀ : GtPtF D.toPre F) (x : TFK (R := V) F ⟶ A.A) (t : SecA A F (m ^ 2)), q.y = p.y ∧ IsTor τ g₀ ∧ p.g.IsAdd g₀ q.g ∧ QkToAkU U.toUnifPre F (m ^ 2) q x ∧ ThC A ρ m th x t (c τ)) →
    ∀ χ₀ : D.toPre.X, SumV v (fun a : D.toPre.X => coef ϑ g' w' (χ₀ + m • a))
      (((m : F) ^ (2 * Module.finrank ℤ D.toPre.X))⁻¹ * ∑ᶠ τ : {τ : Multiplicative D.toPre.X →* Fˣ // τ ^ (m ^ 2) = 1},
        ((τ.1 (Multiplicative.ofAdd p.y) ^ ((m ^ 2 + 1) / 2) * τ.1 (Multiplicative.ofAdd (m • χ₀)))⁻¹).val * c τ.1)) ∧
  ∀ (n r : ℕ) (χ₀ : D.toPre.X), 2 ≤ r → n * r = m ^ 2 → (∀ a, Q (m • χ₀ + p.y) ≤ Q (m • χ₀ + p.y + n • a)) →
    ∀ a : D.toPre.X, a ≠ 0 → Q (m • χ₀ + p.y) < Q (m • (χ₀ + m • a) + p.y) := by
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨-, h₁, h₂, h₃, h₄⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  intro V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE m hm p g' w' hS
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  obtain ⟨hg, hw', w, κ, hw, hκ, e⟩ := hS
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  refine ⟨?_, fun τ hτ => ?_, fun c hcτ χ₀ => ?_, fun n r χ₀ hr hnr hmin a ha => ?_⟩
  · obtain ⟨a₁, a₂, -⟩ := (TxVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv).2 m hm.pos p w hw _ hg κ hκ w' hw' e
    refine ⟨a₁, a₂, fun χ => ?_⟩
    have q₁ : QForm.bOf D.toPre Q (m • χ) p.y = m * QForm.bOf D.toPre Q p.y χ := by
      rw [QForm.bOf_comm D (Q := Q), ← QForm.bHom_apply hϖ D hQ, map_nsmul, QForm.bHom_apply, nsmul_eq_mul]
    have q₃ : Q (m • χ + p.y) = m ^ 2 * Q χ + m * QForm.bOf D.toPre Q p.y χ + Q p.y := by
      rw [← q₁, ← Q_nsmul hϖ hQ m χ]
      unfold QForm.bOf
      ring
    rw [q₃]
    push_cast
    field_simp
    ring
  · let q : QkPt D.toPre F (m ^ 2) := qkMk hB p.y (p.g + torusPt D.toPre F (Additive.ofMul τ)) (by
      rw [smul_add, qk_nsmul hB, ← map_nsmul, ← ofMul_pow, hτ, ofMul_one, map_zero, add_zero])
    obtain ⟨f, f₁, -, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F (m ^ 2) (pow_pos hm.pos 2)
    have t' : f q ^ (m ^ 2) = 1 := by
      rw [← map_qkMul hB f f₄, ← (f₃ _ _).2 (equiv_qkMul_self hB q), map_qkMul hB f f₄, pow_zero]
    obtain ⟨⟨t, c⟩, hT, -⟩ := GlobalTheory.existsUnique_thetaConst hL V A F ρ hN.2.1 m hm th (f q) t'
    exact ⟨q, _, f q, t, c, rfl, (isTor_iff _ _).2 (isTorusPtF_torusPt τ), (isAdd_iff_eq _ _ _).2 rfl,
      (f₁ _ _).2 rfl, hT⟩
  · have : CharZero (FractionRing V) := IsFractionRing.charZero V
    have : CharZero F := (algebraMap (FractionRing V) F).charZero_iff (algebraMap (FractionRing V) F).injective |>.1 this
    refine sumV_average hm.pos (coef ϑ g' w') (fun τ => τ (Multiplicative.ofAdd p.y) ^ ((m ^ 2 + 1) / 2)) c
      (fun τ hτ => ?_) χ₀
    obtain ⟨q, g₀, x, t, hy, ht, hadd, hx, hT⟩ := hcτ τ hτ
    obtain ⟨wq, hwq⟩ := (SymFrame.main hL V _ hA D F (m ^ 2) hm.pow q).1
    obtain ⟨wq', hwq', eq⟩ := ThetaConstVal.exists_frm D.toPre m q.g.b (m • q.g).b (nsmul_b m q.g) wq hwq.1 κ hκ.1
    have s := (AdicValSum.main V ϖ hϖ F v hv _ _ _ (ThetaSum.theta_const_sum hL V _ hA D A G hG U F w₀ ρ hN th ϑ hE m hm
      q x t (c τ) hx hT wq hwq _ ((isNsmul_iff_eq _ _ _).2 rfl) κ hκ wq' hwq' eq).1).1
    have ht' : IsTor (τ ^ m) (m • g₀) := by
      rw [(isTorusPtF_iff_eq g₀ τ).1 ((isTor_iff _ _).1 ht), ← map_nsmul, ← ofMul_pow]
      exact (isTor_iff _ _).2 (isTorusPtF_torusPt _)
    have hadd' : g'.IsAdd (m • g₀) (m • q.g) := (isAdd_iff_eq _ _ _).2 (by
      rw [(isAdd_iff_eq _ _ _).1 hadd, (isNsmul_iff_eq _ _ _).1 hg, smul_add])
    have hb := (val_translate ht hadd).1
    have co := coef_translate ht' hadd' hw' (w' := wq')
      (c := (τ (Multiplicative.ofAdd p.y) ^ ((m ^ 2 + 1) / 2)).val) (fun z J hJ => by
        have c₃ : val κ q.g.b.left z J = val κ p.g.b.left z J := by rw [hb]
        rw [← eq z J hJ, ← e z J hJ, c₃, Units.val_mul, Units.val_mul,
          txFrame_translate hL.1.mulPull hm.pow hτ hy ht hadd hw hwq z J hJ, _root_.mul_assoc]) ϑ
    have : coef ϑ (m • q.g) wq' = fun χ => (τ (Multiplicative.ofAdd p.y) ^ ((m ^ 2 + 1) / 2)).val *
        (τ (Multiplicative.ofAdd (m • χ))).val * coef ϑ g' w' χ := funext fun χ => by
      rw [co, ofAdd_nsmul, map_pow, MonoidHom.pow_apply]
    rwa [this] at s
  · have hn : 1 ≤ n := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at hnr
      exact (pow_pos hm.pos 2).ne hnr
    have := GlobalTheory.shortest_vector_strict_of_mul D.toPre.X Q (QForm.bHom hϖ D hQ)
      (fun a b => by rw [QForm.bHom_apply]; unfold QForm.bOf; ring)
      (fun a => by rw [QForm.bHom_apply, QForm.two_Q_eq hϖ D hQ]) (fun a h => QForm.Q_pos hϖ D hQ h) n r hn hr
      (m • χ₀ + p.y) hmin a (fun h => ha (nsmul_inj (pow_pos hm.pos 2) (by rw [← hnr, h, smul_zero])))
    have e₀ : (n * r) • a = m • m • a := by rw [hnr, sq, mul_smul]
    rwa [e₀, add_right_comm, ← smul_add] at this

end GlobalTheory.UT.ThetaAverage
end
