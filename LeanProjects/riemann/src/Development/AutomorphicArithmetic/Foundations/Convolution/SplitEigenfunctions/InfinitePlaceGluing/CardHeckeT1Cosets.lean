import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatHerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosetsStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.ResW GlobalTheory.LFun Formalism.L2.Host

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section Loc

variable {E : Type} [Field E] [NumberField E]

private theorem card_heckeT1_cosets (w : HeightOneSpectrum (𝓞 E)) (ϖ : w.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E w ϖ) :
    Nat.card {q : GL (Fin 2) (w.adicCompletion E) ⧸ KGL w 2 // Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ 1 q.out ≠ 0} =
      Formalism.UG.qV E w + 1 := by
  have h := Formalism.UG.P.Tj_double_coset_decomposition E w 2 ϖ (mem_Ov_of_isUnifV hϖ) hϖ 1 (by norm_num)
  have hq : 2 ≤ Formalism.UG.qV E w := one_lt_absNorm w
  have hcard : Nat.card {q : GL (Fin 2) (w.adicCompletion E) ⧸ KGL w 2 //
      Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ 1 q.out ≠ 0} =
      Nat.card {x : GL (Fin 2) (w.adicCompletion E) ⧸ Formalism.UG.GLint (Fin 2) (Formalism.UG.Ov E w) |
        Formalism.UG.Tj ℤ 2 (Formalism.UG.Ov E w) ϖ 1 x.out ≠ 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => GlobalTheory.TjCount.Tj_complex_ne_zero_iff _ _ _ _ _)
  rw [← hcard] at h
  simp only [Finset.prod_range_one, zero_add, pow_one, Nat.sub_zero] at h
  have hq' : ((Formalism.UG.qV E w : ℤ) - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ Formalism.UG.qV E w := by exact_mod_cast hq
    omega
  have e : (Nat.card {q : GL (Fin 2) (w.adicCompletion E) ⧸ KGL w 2 //
      Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ 1 q.out ≠ 0} : ℤ) = (Formalism.UG.qV E w : ℤ) + 1 :=
    mul_right_cancel₀ hq' (h.trans (by ring))
  exact_mod_cast e

private theorem sq_le_of_bound {t r : ℝ} (ht : 1 ≤ t) (hr : 0 < r) (h : t * (r + r⁻¹) ≤ t ^ 2 + 1) : r ^ 2 ≤ t ^ 2 := by
  by_contra hlt
  push_neg at hlt
  have hrt : t < r := lt_of_pow_lt_pow_left₀ 2 hr.le hlt
  have h5 : t * r ^ 2 + t ≤ (t ^ 2 + 1) * r := by
    have := mul_le_mul_of_nonneg_right h hr.le
    have e : t * (r + r⁻¹) * r = t * r ^ 2 + t := by
      field_simp
    rwa [e] at this
  have h6 : 0 < (t * r - 1) * (r - t) := by
    apply mul_pos <;> nlinarith
  nlinarith

private theorem pair_star {a b : ℂˣ} (hs : Multiset.map star ({a, b} : Multiset ℂˣ) = Multiset.map (·⁻¹) ({a, b} : Multiset ℂˣ)) :
    (star a = a⁻¹ ∧ star b = b⁻¹) ∨ (star a = b⁻¹ ∧ star b = a⁻¹) := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at hs
  rcases Multiset.cons_eq_cons.1 hs with ⟨h, h'⟩ | ⟨-, c, h1, h2⟩
  · exact .inl ⟨h, Multiset.singleton_inj.1 h'⟩
  · obtain ⟨e1, -⟩ := Multiset.singleton_eq_cons_iff _ |>.1 h1
    obtain ⟨e2, -⟩ := Multiset.singleton_eq_cons_iff _ |>.1 h2
    exact .inr ⟨e2.symm, e1⟩

private theorem loc_sat (w : HeightOneSpectrum (𝓞 E)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion E)) V) (hU : GlobalTheory.LGrp.IsUnitarisable ρ) (a b : ℂˣ)
    (hB : HasSatGL w ρ {a, b}) :
    ‖(a * b : ℂ)‖ = 1 ∧ starRingEnd ℂ (a + b : ℂ) * (a * b) = a + b ∧ ‖(a : ℂ)‖ ^ 2 ≤ Formalism.UG.qV E w := by
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hs := GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable E w 2 V ρ x _ hU hx
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  obtain ⟨B0, h1, h2, h3⟩ := hU
  have k1 := GlobalTheory.T.norm_heckeEigenvalue_le_card_cosets _ (KGL w 2) V ρ B0.flip (fun u v => h1 v u) (fun u hu => h2 u hu) (fun g u v => h3 g v u) _ x _
    (fun g => by
      unfold Formalism.UG.Tj
      exact (norm_indicator_le_norm_self _ _).trans (by simp))
    (GlobalTheory.TjCount.tj_cosets_finite_card_le E w 2 ϖ hϖ 1 (by norm_num)).1 hx.1 (hx.2.2.2 ϖ hϖ 1 (by norm_num))
  rw [card_heckeT1_cosets w ϖ hϖ] at k1
  have hq2 : 2 ≤ Formalism.UG.qV E w := one_lt_absNorm w
  set q := Formalism.UG.qV E w with hq
  set t : ℝ := (q : ℝ) ^ (1 / 2 : ℝ) with ht
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have ht2 : t ^ 2 = q := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
    norm_num
  have ht1 : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ q)) (by norm_num)
  have e : ‖satEig q 2 {a, b} 1‖ = t * ‖(a + b : ℂ)‖ := by
    unfold satEig
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    norm_num [Multiset.esymm, Multiset.powersetCard_one, add_comm]
    exact Or.inl (by rw [ht])
  rw [e] at k1
  have hA : (a : ℂ) ≠ 0 := a.ne_zero
  have hB0 : (b : ℂ) ≠ 0 := b.ne_zero
  have hr : 0 < ‖(a : ℂ)‖ := norm_pos_iff.2 hA
  have cv : ∀ u v : ℂˣ, star u = v⁻¹ → starRingEnd ℂ (u : ℂ) = (v : ℂ)⁻¹ := fun u v h => by
    have := congrArg (fun y : ℂˣ => (y : ℂ)) h
    simpa using this
  rcases pair_star hs with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have c1 := cv _ _ e1
    have c2 := cv _ _ e2
    have n1 : ‖(a : ℂ)‖ = 1 := by
      have := congrArg norm c1
      rw [RCLike.norm_conj, norm_inv] at this
      nlinarith [mul_inv_cancel₀ hr.ne']
    have n2 : ‖(b : ℂ)‖ = 1 := by
      have := congrArg norm c2
      rw [RCLike.norm_conj, norm_inv] at this
      have hr' : 0 < ‖(b : ℂ)‖ := norm_pos_iff.2 hB0
      nlinarith [mul_inv_cancel₀ hr'.ne']
    refine ⟨by rw [norm_mul, n1, n2, one_mul], ?_, ?_⟩
    · rw [map_add, c1, c2]
      field_simp
      ring
    · rw [n1]
      norm_num
      omega
  · have c1 := cv _ _ e1
    have c2 := cv _ _ e2
    have n1 : ‖(a : ℂ)‖ = ‖(b : ℂ)‖⁻¹ := by
      have := congrArg norm c1
      rwa [RCLike.norm_conj, norm_inv] at this
    refine ⟨by rw [norm_mul, n1, inv_mul_cancel₀ (norm_ne_zero_iff.2 hB0)], ?_, ?_⟩
    · rw [map_add, c1, c2]
      field_simp
    · have hbe : (b : ℂ) = (starRingEnd ℂ (a : ℂ))⁻¹ := by rw [c1, inv_inv]
      have e3 : ‖(a + b : ℂ)‖ = ‖(a : ℂ)‖ + ‖(a : ℂ)‖⁻¹ := by
        have hn : (a : ℂ) * starRingEnd ℂ (a : ℂ) = (‖(a : ℂ)‖ : ℂ) ^ 2 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          push_cast
          rfl
        have hc0 : starRingEnd ℂ (a : ℂ) ≠ 0 := (map_ne_zero _).2 hA
        have e4 : (a + b : ℂ) = a * ((1 + (‖(a : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
          rw [hbe]
          push_cast
          rw [← hn]
          field_simp
        rw [e4, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        field_simp
      rw [e3] at k1
      have := sq_le_of_bound ht1 hr (by simpa using k1 |>.trans (by push_cast; rw [ht2]))
      rwa [ht2] at this

end Loc

section Glob

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem isUnitary_of_cenN {P : CuspSub E 2} {ω : HChar ℚ} (hc : CenN P ω) (hu : Unit1 ω) : P.IsUnitary := by
  obtain ⟨κ, hκ⟩ := Central.exists_hasCentral E 2 P
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 P.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
  refine (CG.isUnitary_mk P).1 ⟨κ, fun z => ?_, CuspSub.hasCentral_iff.1 hκ⟩
  have h1 : φ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin 2) z) = ((κ.1 z : ℂˣ) : ℂ) * φ.1 g :=
    congrArg (fun f : Sm E 2 => f.1 g) (hκ z φ hφ)
  have h2 := hc φ hφ z g
  have e : Matrix.GeneralLinearGroup.scalar (Fin 2) z * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) z :=
    Units.ext (Matrix.scalar_commute _ (fun _ => Commute.all _ _) g.val).eq
  rw [e, h1] at h2
  have h3 := mul_right_cancel₀ hg h2
  rw [h3]
  exact hu _

private theorem exists_norm {P : CuspSub E 2} (hu : P.IsUnitary) :
    ∃ χ : HChar E, GlobalTheory.DiscSpec.IsNormalised (P.twist χ) ∧ ∀ v, χ.UnrAt v ∧ ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := by
  have hcex := (GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨2, P⟩).1
  have hr : rexp (⟨2, P⟩ : Letter E) = 0 := ((GlobalTheory.T.cuspidalLetterRealExponent_eq_zero_iff_isUnitary E ⟨2, P⟩ (by norm_num)).1).2 hu
  have hd : (0 : ℝ) < ((2 : ℕ) : ℝ) * Module.finrank ℚ E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    positivity
  have hre : (cex (⟨2, P⟩ : Letter E)).re = 0 := by
    have h := hr
    unfold rexp at h
    rcases div_eq_zero_iff.1 h with h | h
    · exact h
    · exact absurd h hd.ne'
  have hdc : (((2 : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ)) = ((((2 : ℕ) : ℝ) * Module.finrank ℚ E : ℝ) : ℂ) := by
    push_cast
    ring
  obtain ⟨χ, hz, hv, -, -⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (-(cex (⟨2, P⟩ : Letter E)) / (((2 : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ)))
  have hzre : (-(cex (⟨2, P⟩ : Letter E)) / (((2 : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ))).re = 0 := by
    rw [hdc, Complex.div_ofReal_re, Complex.neg_re, hre]
    simp
  refine ⟨χ, ?_, fun v => ⟨(hv v).1, ?_⟩⟩
  · have h4 := GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨2, P.twist χ⟩
    refine h4.2.2.2.1.1 (h4.2.2.2.2 0 ?_)
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 P.ne_bot
    refine ⟨mulChi 2 χ φ, ⟨φ, hφ, rfl⟩, fun h => h0 ((mulChi 2 χ).map_eq_zero_iff.1 h), ?_⟩
    have e1 : zc E 2 φ = cex (⟨2, P⟩ : Letter E) • φ := hcex φ hφ
    have e2 : cex (⟨2, P⟩ : Letter E) + ((2 : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ) *
        (-(cex (⟨2, P⟩ : Letter E)) / (((2 : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ))) = 0 := by
      have : (((2 : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0 := by
        rw [hdc]
        exact_mod_cast hd.ne'
      rw [mul_div_cancel₀ _ this]
      ring
    change zc E 2 (mulChi 2 χ φ) = (0 : ℂ) • mulChi 2 χ φ
    rw [hz, e1, ← add_smul, e2, zero_smul, map_zero, zero_smul]
  · have hq : 0 < Ideal.absNorm v.asIdeal := zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    rw [(hv v).2, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re, hzre]
    simp

end Glob

end UpperTheory.ConvolutionTheory.RankTwoDescent

open UpperTheory.ConvolutionTheory.RankTwoDescent in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.satU_of :
    SatU := by
  intro E _ _ _ D P ω χ hc hu _ w α β hB
  obtain ⟨κ, hn, hκ⟩ := exists_norm (isUnitary_of_cenN hc hu)
  have hD := (GlobalTheory.T.cuspForm_sqIntegrable_and_isDiscrete_splitCentre E 2).2 _ hn
  have hU : GlobalTheory.LGrp.IsUnitarisable ((P.twist κ).locRep w) := PositivityTheory.Rg.Rs.SatakeHermitian.isUnitarisable_locRepD hD w
  have hB' : GlobalTheory.LFun.HasSatGL w ((P.twist κ).locRep w) {α * κ.val w, β * κ.val w} := by
    simpa using CG.HasSat.twist (π := CG.mk P) hB (hκ w).1
  obtain ⟨k1, k2, k3⟩ := loc_sat w _ hU _ _ hB'
  have hc1 := (hκ w).2
  set c : ℂ := ((κ.val w : ℂˣ) : ℂ) with hcdef
  have hc0 : c ≠ 0 := (κ.val w).ne_zero
  have hcc : starRingEnd ℂ c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]
    simp
  simp only [Units.val_mul, ← hcdef] at k1 k2 k3
  refine ⟨?_, ?_, ?_⟩
  · rw [show (α : ℂ) * c * (β * c) = α * β * (c * c) by ring, norm_mul, norm_mul c c, hc1, mul_one, mul_one] at k1
    exact k1
  · have e : starRingEnd ℂ ((α : ℂ) * c + β * c) * (α * c * (β * c)) =
        starRingEnd ℂ ((α : ℂ) + β) * (α * β) * (starRingEnd ℂ c * c) * c := by
      simp only [map_add, map_mul]
      ring
    rw [e, hcc, mul_one] at k2
    exact mul_right_cancel₀ hc0 (k2.trans (by ring))
  · rw [norm_mul, hc1, mul_one] at k3
    exact k3

end
