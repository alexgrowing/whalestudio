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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConstStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultipleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTermsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaConstVal
open GlobalTheory.TorusExt

theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨S, hS⟩ := h q
  have := v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) (f := x) fun i _ => hq i)
  rwa [sub_add_cancel] at this

theorem eq_zero_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (q0 : 0 < q) (i₀ : Ix) (h₀ : v (x i₀) = 0)
    (hq : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  classical
  obtain ⟨S, hS⟩ := h q
  have a := v.map_le_add (hS (insert i₀ S) (Finset.subset_insert _ _))
    (v.map_le_sum (s := (insert i₀ S).erase i₀) (f := x) fun i hi => hq i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S)]; ring
  have lt : v (x i₀) < v (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [h₀]
    exact lt_of_lt_of_le (by exact_mod_cast q0) a
  rw [e, v.map_add_eq_of_lt_left lt, h₀]

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_kap (hM : MulPullSt) [IsNoetherianRing R] (m : ℕ) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1), Normd κ := by
  obtain ⟨α, hα⟩ := hM _ D.P m
  have o : ∀ f : D.P.A ⟶ D.P.A, f = 𝟙 D.P.A ^ m → (1 : D.P.A ⟶ D.P.A).left ≫ f.left = (1 : D.P.A ⟶ D.P.A).left := by
    rintro _ rfl
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, one_pow]
  obtain ⟨κ, hκ, vκ⟩ := exists_gen D.P.isLB
    (φ' := ![𝟙 _, (𝟙 D.P.A ^ m).left, (1 : D.P.A ⟶ D.P.A).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Category.comp_id,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_zpow, ofMul_one, o _ rfl]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ α (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ α (1 : D.P.A ⟶ D.P.A).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hα (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hα _)))
  refine ⟨κ, hκ, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ (1 : D.P.A ⟶ D.P.A).left = eSec D.P.A := by
    rw [eSec, ← Over.comp_left, MonObj.comp_one, Hom.one_def, toUnit_unit, Category.id_comp]
  rw [val_pull hJ, vκ _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, val_one, Category.id_comp, e, mul_inv_cancel]

theorem exists_frm {F : Type} [Field F] [Algebra (FractionRing R) F] (m : ℕ) (b b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = b ^ m) (w : Frm D F (m ^ 2) b) (hw : w.IsGen) (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1))
    (hκ : κ.IsGen) : ∃ w' : Frm D F 1 b', w'.IsGen ∧
      ∀ z J, Good D.P.L z J → val w (𝟙 _) z J * val κ b.left z J = val w' (𝟙 _) z J := by
  subst hb
  have o₁ : b.left ≫ (𝟙 D.P.A ^ m).left = (b ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have o₂ : b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (DegPre.zeroF D F).left := by
    rw [← Over.comp_left, MonObj.comp_one]; rfl
  obtain ⟨w', hw', vw⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F (b ^ m)) (ε' := DegPre.lineε 1)
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      apply Additive.ofMul.injective
      simp only [DegPre.lineφ, DegPre.lineε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Category.comp_id, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_zpow, ofMul_one, o₁, o₂]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ w (LB.pullGen D.P.L _ _ κ b.left))
    (mulGen_isGen _ _ _ _ _ _ _ hw (pullGen_isGen _ _ _ _ hκ _))
  refine ⟨w', hw', fun z J hJ => ?_⟩
  rw [vw _ _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp]

end

attribute [local instance] gtGroup

theorem pow_eq_one_of_nsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {M : Type} [Group M] (f : QkPt D F k → M)
    (hf : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') (p : QkPt D F k) (hy : p.y = 0) (j : ℕ) (hj : j • p.g = 0) :
    f p ^ j = 1 := by
  have z : ∀ i : ℕ, k • (i • p.g) = iota hB F 0 := fun i => by
    rw [smul_comm, qk_nsmul hB, hy, map_zero, smul_zero]
  let r : ℕ → QkPt D F k := fun i => qkMk hB 0 (i • p.g) (z i)
  have radd : ∀ i i', f (r (i + i')) = f (r i) * f (r i') := fun i i' => by
    rw [← hf _ _ _ (qkAdd_qkAdd hB (r i) (r i'))]
    exact congrArg f (qk_ext (add_zero _).symm (add_smul i i' p.g))
  have r0 : f (r 0) = 1 := mul_eq_left.1 (radd 0 0).symm
  have r1 : r 1 = p := qk_ext hy.symm (one_smul ℕ p.g)
  have rpow : ∀ i, f (r i) = f p ^ i := fun i => by
    induction i with
    | zero => rw [r0, pow_zero]
    | succ i ih => rw [radd, ih, r1, pow_succ]
  rw [← rpow, ← r0]
  exact congrArg f (qk_ext rfl (hj.trans (zero_smul ℕ p.g).symm))

theorem exists_terms : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → ∃ w' : Frm D.toPre F 1 (m • p.g).b, w'.IsGen ∧ SumV v (coef ϑ (m • p.g) w') c ∧ GenV hϖ hv w' ((Q p.y : ℚ) / (m ^ 2 : ℕ)) ∧ GtV hϖ hv (m • p.g) (fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / m) ∧ ∀ χ, (((Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) ≤ v (coef ϑ (m • p.g) w' χ) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm p x t c hx hT
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL V _ hA D F (m ^ 2) hm.pow p).1
  obtain ⟨κ, hκ⟩ := exists_kap D.toPre hL.1.mulPull m
  obtain ⟨w', hw', e⟩ := exists_frm D.toPre m p.g.b (m • p.g).b (nsmul_b m p.g) w hw.1 κ hκ.1
  have hg : GtPtF.IsNsmul m p.g (m • p.g) := (isNsmul_iff_eq _ _ _).2 rfl
  have s := (GlobalTheory.T.thetaConstant_eq_sum_thetaTerms_odd_multiple hL V _ hA D A G hG U F w₀ ρ hN th ϑ hE m hm p x t c hx hT w hw _ hg κ hκ w' hw' e).1
  obtain ⟨a₁, a₂, a₃⟩ := (GlobalTheory.T.valuations_symmetricFrame_and_terms hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv).2 m hm.pos p w hw _ hg κ hκ w' hw' e
  exact ⟨w', hw', (AdicValSum.main V ϖ hϖ F v hv _ _ _ s).1, a₁, a₂, a₃ ϑ hP.1⟩

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → (∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → (∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c) ∧ (v c = 0 → ∃ z, p.y = m • z)) ∧ ∀ n, 2 ≤ n → n ∣ m → ∀ (p : QkPt D.toPre F (m ^ 2)) x, p.y = 0 → QkToAkU U.toUnifPre F (m ^ 2) p x → ∃ (p' : QkPt D.toPre F (m ^ 2)) (x' : _) (t : _) (c : F), p'.y = 0 ∧ QkToAkU U.toUnifPre F (m ^ 2) p' x' ∧ (x' ^ m * (x ^ m)⁻¹) ^ n = 1 ∧ ThC A ρ m th x' t c ∧ v c = 0 := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm hu
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have T := exists_terms hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP m hm
  have m0 : (0 : ℚ) < (m ^ 2 : ℕ) := by exact_mod_cast pow_pos hm.pos 2
  have q0 : (0 : ℚ) < 1 / (m ^ 2 : ℕ) := one_div_pos.2 m0
  have pos : ∀ χ : D.toPre.X, χ ≠ 0 → (1 : ℚ) / (m ^ 2 : ℕ) ≤ (Q χ : ℚ) / (m ^ 2 : ℕ) := fun χ h =>
    div_le_div_of_nonneg_right (by exact_mod_cast QForm.Q_pos hϖ D hQ h) m0.le
  refine ⟨fun p x t c hx hT => ?_, fun n hn hnm p x hy hx => ?_⟩
  · obtain ⟨w', -, s, -, -, a⟩ := T p x t c hx hT
    have k : ∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c := fun q hq =>
      le_of_sumV s fun χ => (WithTop.coe_le_coe.2 (hq χ)).trans (a χ)
    refine ⟨k, fun h0 => by_contra fun hz => ?_⟩
    have := k _ fun χ => pos (m • χ + p.y) fun e => hz ⟨-χ, by rw [smul_neg]; exact eq_neg_of_add_eq_zero_right e⟩
    rw [h0] at this
    exact absurd (by exact_mod_cast this) q0.not_ge
  · have hB := D.tau_bimult
    obtain ⟨d, rfl⟩ := hnm
    obtain ⟨h, o, g₂, ho, hh, hg₂, hv₂⟩ := GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv ϑ hP n hn
      (isUnit_of_mul_isUnit_left (by rwa [Nat.cast_mul] at hu)) ((n * d) • p.g) 0
    obtain ⟨h', hh'⟩ := (gt_onto_divisible_kernel hL V _ hA D F).2.1 (n * d) hm.pos h
    rw [isZero_iff_eq] at ho
    rw [isNsmul_iff_eq] at hh hh'
    rw [isAdd_iff_eq] at hg₂
    have z₁ : (n * d * n) • h' = 0 := by rw [_root_.mul_comm (n * d) n, mul_smul, ← hh', ← hh, ho]
    have z₂ : (n * d) ^ 2 • h' = iota hB F 0 := by
      rw [map_zero, show (n * d) ^ 2 = d * (n * d * n) by ring, mul_smul, z₁, smul_zero]
    obtain ⟨f, f₁, -, -, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F ((n * d) ^ 2) (pow_pos hm.pos 2)
    let r : QkPt D.toPre F ((n * d) ^ 2) := qkMk hB 0 h' z₂
    let p' := qkAdd hB p r
    have y' : p'.y = 0 := (add_zero _).trans hy
    have fp : f p' = x * f r := ((f₁ p x).1 hx).symm ▸ f₄ _ _ _ (qkAdd_qkAdd hB p r)
    have hx' : QkToAkU U.toUnifPre F ((n * d) ^ 2) p' (f p') := (f₁ _ _).2 rfl
    have t' : f p' ^ ((n * d) ^ 2) = 1 := pow_eq_one_of_nsmul hB f f₄ p' y' _ (by rw [qk_nsmul hB, y', map_zero])
    obtain ⟨⟨t, c⟩, hT, -⟩ := GlobalTheory.T.existsUnique_theta_const_of_odd hL V A F ρ hN.2.1 (n * d) hm th (f p') t'
    refine ⟨p', f p', t, c, y', hx', ?_, hT, ?_⟩
    · rw [fp, mul_pow x, mul_inv_cancel_comm, ← pow_mul]
      exact pow_eq_one_of_nsmul hB f f₄ r rfl _ z₁
    · obtain ⟨w', hw', s, a₁, a₂, a⟩ := T p' _ t c hx' hT
      have e : g₂ = (n * d) • p'.g := by
        rw [hg₂, hh']; exact (smul_add _ _ _).symm
      subst e
      refine eq_zero_of_sumV s q0 0 ?_ fun χ hχ => (WithTop.coe_le_coe.2 (pos _ fun e => hχ ?_)).trans (a χ)
      · rw [hv₂ w' _ _ hw' a₂ a₁, y', QForm.Q_zero hϖ D hQ, bOf_zero_left hϖ hQ]
        simp
      · rw [y', add_zero] at e
        by_contra h0
        have b₁ := QForm.Q_pos hϖ D hQ h0
        have b₂ := Q_nsmul hϖ hQ (n * d) χ
        rw [e, QForm.Q_zero hϖ D hQ] at b₂
        have b₃ : (0 : ℤ) < ((n * d : ℕ) : ℤ) ^ 2 := by exact_mod_cast pow_pos hm.pos 2
        exact absurd b₂ (mul_pos b₃ (by omega)).ne

end GlobalTheory.UT.ThetaConstVal
end
