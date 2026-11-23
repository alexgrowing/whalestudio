import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.GoodOperatorConjugation

variable {F : Type} [Field F] [NumberField F]

theorem v_lt_of_max {w : Pl F} {y : w.adicCompletionIntegers F}
    (hy : y ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F)) : Valued.v (y : w.adicCompletion F) < 1 := by
  refine lt_of_le_of_ne y.2 fun h1 => mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hy) ?_
  have h0 : (y : w.adicCompletion F) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have hi : (y : w.adicCompletion F)⁻¹ ∈ w.adicCompletionIntegers F := by
    show Valued.v ((y : w.adicCompletion F)⁻¹) ≤ 1
    rw [map_inv₀, h1, inv_one]
  exact ⟨⟨y, ⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩

theorem congruence_subgroup_entry_valuations_alt {w : Pl F} {c : ℕ} (hc : c ≠ 0) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w c) :
    (∀ a b, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) a b) ≤ 1) ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) < 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) < 1 := by
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' := Subgroup.mem_comap.1 hk
  change ![(0 : (w.adicCompletionIntegers F) ⧸ (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)), 1] ᵥ* _ =
    ![0, 1] at hk'
  rw [funext_iff, Fin.forall_fin_two] at hk'
  simp [Matrix.vecMul, dotProduct] at hk'
  obtain ⟨h1, h2⟩ := hk'
  have hle : IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.pow_le_self hc
  refine ⟨fun a b => (k a b).2, v_lt_of_max (hle ?_), ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  · have : k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) :=
      hle (Ideal.Quotient.eq.1 (by rw [h2, map_one]))
    have h3 := v_lt_of_max this
    simpa using h3

theorem tr_conj {R : Type} [CommRing R] (X : GL (Fin 2) R) (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (((X⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * T * (X : Matrix (Fin 2) (Fin 2) R)) = Matrix.trace T := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem det_conj' {R : Type} [CommRing R] (X : GL (Fin 2) R) (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.det (((X⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * T * (X : Matrix (Fin 2) (Fin 2) R)) = Matrix.det T := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_mul]

variable [IsTotallyReal F]

theorem good_of {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) {W : List (Pl F)} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c W a) : (mkDat c χ).Good a := by
  intro f hf x h
  have hf' : ∀ g (h : Hc c), f (g * h) = χ h * f g := hf
  have hzc : ∀ z, zc F z ∈ Hc c := fun z => Subgroup.mem_sup_right ⟨z, rfl⟩
  have hχz : ∀ z, χ ⟨zc F z, hzc z⟩ = ω.1 (finId F z) := fun z =>
    (hχ ⟨zc F z, hzc z⟩).2 1 (Subgroup.one_mem _) z (one_mul _).symm
  have hK : f ∈ Hi.fixd (Hi.rtr ℂ (GF F) ℂ) (Kc c) := by
    intro u hu
    funext g
    have hu' : u ∈ Hc c := Subgroup.mem_sup_left hu
    have h1 : χ ⟨u, hu'⟩ = 1 := by
      rw [(hχ ⟨u, hu'⟩).2 u hu 1 (by rw [map_one, mul_one]), map_one, map_one]
    rw [Hi.rtr_apply, hf' g ⟨u, hu'⟩, h1, Units.val_one, one_mul]
  have hs := (ha.act (GF F → ℂ) (Hi.rtr ℂ (GF F) ℂ) f hK).1
  obtain ⟨k, hk, z, hz⟩ := (hχ h).1
  have hfix := congrFun (hs k hk) x
  simp only [Hi.rtr_apply, Finset.sum_apply] at hfix
  change ∑ i, f (x * (h : GF F) * a i) = (χ h : ℂ) * ∑ i, f (x * a i)
  rw [(hχ h).2 k hk z hz, ← hχz z, ← hfix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hz, ← hf' (x * k * a i) ⟨zc F z, hzc z⟩]
  have hc := Subgroup.mem_center_iff.1 (zc_center z) (a i)
  congr 1
  simp only [mul_assoc]
  rw [hc]

theorem reg_of {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) {W : List (Pl F)} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c W a) {w : Pl F} (hw : w ∈ W) (hc : c w ≠ 0) : (mkDat c χ).Reg a := by
  classical
  intro γ x i hmem
  obtain ⟨k, hk, z, hz⟩ := (hχ ⟨_, hmem⟩).1
  have hz' : (a i)⁻¹ * (x⁻¹ * jF F γ * x) = k * zc F z := hz
  have e : x⁻¹ * jF F γ * x = a i * (k * zc F z) := by rw [← hz', mul_inv_cancel_left]
  obtain ⟨u, hu⟩ := ha.loc i w hc
  let φ : GF F →* GL (Fin 2) (w.adicCompletion F) := Matrix.GeneralLinearGroup.map (pLoc F w)
  let ψ : F →+* w.adicCompletion F := (pLoc F w).comp (algebraMap F (Af F))
  let r : ℕ := W.count w
  have hr : 0 < r := List.count_pos_iff.2 hw
  let p : w.adicCompletion F := ((atFin w (unif w) ^ r : (w.adicCompletion F)ˣ) : w.adicCompletion F)
  let zw : w.adicCompletion F := pLoc F w (z : Af F)
  have e2 := congrArg (fun g => ((φ g : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) e
  simp only [map_mul, map_inv, Units.val_mul] at e2
  obtain ⟨M, hMk⟩ : ∃ M : Matrix (Fin 2) (Fin 2) (w.adicCompletion F),
      ((φ k : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) = M := ⟨_, rfl⟩
  rw [hMk] at e2
  have hA : ((φ (a i) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![p, (u : w.adicCompletion F); 0, 1] := by
    rw [show φ (a i) = _ from hu]; rfl
  have hZ : ((φ (zc F z) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![zw, 0; 0, zw] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, zw, zc, Matrix.GeneralLinearGroup.map]
  have hT : ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![ψ (γ 0 0), ψ (γ 0 1); ψ (γ 1 0), ψ (γ 1 1)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have htr : ψ (γ.val.trace) = zw * (p * M 0 0 + u * M 1 0 + M 1 1) := by
    have := tr_conj (φ x) ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)))
    rw [e2, hA, hZ, hT, Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of,
      Matrix.trace_fin_two_of] at this
    rw [Matrix.trace_fin_two, map_add]
    change ψ (γ 0 0) + ψ (γ 1 1) = _
    rw [← this]; ring
  have hdet : ψ (γ.val.det) = zw ^ 2 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) := by
    have := det_conj' (φ x) ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)))
    rw [e2, hA, hZ, hT, Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.det_fin_two_of,
      Matrix.det_fin_two_of] at this
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
    change ψ (γ 0 0) * ψ (γ 1 1) - ψ (γ 0 1) * ψ (γ 1 0) = _
    rw [← this]; ring

  have hkl : φ k ∈ K1 w (c w) := Subgroup.mem_iInf.1 hk w
  obtain ⟨hM, hM10, hM11⟩ := congruence_subgroup_entry_valuations_alt hc hkl
  simp only [hMk] at hM hM10 hM11
  have hp : Valued.v p < 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      unif_spec w
    have h2 : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    show Valued.v (((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) ^ r) < 1
    rw [map_pow, h1]
    exact pow_lt_one₀ zero_le h2 hr.ne'
  have hu1 : Valued.v (u : w.adicCompletion F) ≤ 1 := u.2
  have ht : Valued.v (p * M 0 0 + u * M 1 0 + M 1 1) = 1 := by
    have h1 : Valued.v (p * M 0 0 + u * M 1 0 + (M 1 1 - 1)) < 1 := by
      refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) hM11
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' (hM 0 0)) hp
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hu1) hM10
    rw [show p * M 0 0 + u * M 1 0 + M 1 1 = 1 + (p * M 0 0 + u * M 1 0 + (M 1 1 - 1)) by ring]
    exact Valuation.map_one_add_of_lt _ h1
  have hzw : zw ≠ 0 := (Units.map (pLoc F w).toMonoidHom z).ne_zero
  have ht0 : p * M 0 0 + u * M 1 0 + M 1 1 ≠ 0 := fun e => by rw [e, map_zero] at ht; exact zero_ne_one ht
  refine ⟨fun h0 => ?_, fun h4 => ?_⟩
  · rw [h0, map_zero] at htr
    exact mul_ne_zero hzw ht0 htr.symm
  · have h5 := congrArg ψ h4
    rw [map_pow, map_mul, htr, hdet, map_ofNat] at h5
    have h6 : (p * M 0 0 + u * M 1 0 + M 1 1) ^ 2 = 4 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hzw)
      linear_combination h5
    have h7 := congrArg Valued.v h6
    rw [map_pow, ht, one_pow] at h7
    have h4v : Valued.v (4 : w.adicCompletion F) ≤ 1 := by
      have := natCast_mem (w.adicCompletionIntegers F) 4
      rw [Nat.cast_ofNat] at this
      exact this
    have hd : Valued.v (M 0 0 * M 1 1 - M 0 1 * M 1 0) ≤ 1 := by
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hM _ _) (hM _ _)
    have : Valued.v (4 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0))) < 1 := by
      rw [map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' h4v) (lt_of_le_of_lt (mul_le_of_le_one_right' hd) hp)
    exact absurd h7 (ne_of_gt this)

end UpperTheory.Esk.GoodOperatorConjugation

namespace UpperTheory.Esk

theorem dGood : AMem → DGood := by
  intro _ F _ _ _ c ω χ hχ W n a ha
  exact ⟨GoodOperatorConjugation.good_of hχ ha, fun ⟨w, hw, hc⟩ => GoodOperatorConjugation.reg_of hχ ha hw hc⟩

end UpperTheory.Esk
