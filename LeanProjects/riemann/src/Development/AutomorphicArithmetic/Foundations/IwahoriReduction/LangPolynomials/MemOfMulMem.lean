import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormOfDvd
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ToBasis
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ContOf
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ExistsTau
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.IwOpsRedUn
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.SerMulPow
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepUniq
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepAdd
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepSmul
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.IsUnitNat
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepFrob
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Period
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PConj
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DivEqZeroOfCg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.HtvExpand
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormSubLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}

private theorem norm_pow_anti (n' n : ℕ) (h : n' ≤ n) : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one.le h

private theorem cg_mono {n' n : ℕ} (h : n' ≤ n) {x y : Qbar l} (hc : Cg n x y) : Cg n' x y :=
  le_trans hc (norm_pow_anti n' n h)

private theorem cg_trans {n : ℕ} {x y z : Qbar l} (h1 : Cg n x y) (h2 : Cg n y z) : Cg n x z := by
  have e : x - z = (x - y) + (y - z) := by ring
  unfold Cg at *
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

private theorem cg_sub {n : ℕ} {x y x' y' : Qbar l} (h1 : Cg n x y) (h2 : Cg n x' y') : Cg n (x - x') (y - y') := by
  have e : x - x' - (y - y') = (x - y) + -(x' - y') := by ring
  unfold Cg at *
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [norm_neg]

private theorem cg_mul {n : ℕ} {x y w : Qbar l} (hw : ‖w‖ ≤ 1) (h1 : Cg n x y) : Cg n (w * x) (w * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖w‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := by gcongr
    _ ≤ _ := by rwa [one_mul]

private theorem cg_sum {n : ℕ} {ι : Type} (T : Finset ι) (x y : ι → Qbar l) (h : ∀ i ∈ T, Cg n (x i) (y i)) :
    Cg n (∑ i ∈ T, x i) (∑ i ∈ T, y i) := by
  unfold Cg at *
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) h

private theorem norm_nat_le (d : ℕ) : ‖(d : Qbar l)‖ ≤ 1 := by
  have h : (d : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (d : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  have h1 := PadicInt.norm_le_one (d : ℤ_[l])
  rw [PadicInt.norm_def] at h1
  exact_mod_cast h1

private theorem norm_padic_nat (d : ℕ) (hd : ¬ l ∣ d) : ‖(d : ℚ_[l])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hd)

private theorem norm_nat_eq (d : ℕ) (hd : ¬ l ∣ d) : ‖(d : Qbar l)‖ = 1 := by
  have h : (d : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (d : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact norm_padic_nat d hd

private theorem exists_unit (d : ℕ) (hd : ¬ l ∣ d) : ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = d := by
  have h : IsUnit (d : ℤ_[l]) := PadicInt.isUnit_iff.2 (by
    rw [PadicInt.norm_def]
    simpa using norm_padic_nat (l := l) d hd)
  exact ⟨h.unit, h.unit_spec⟩

private theorem exists_ine_un (hl : l ≠ 2) (hA : OverL l A) (d : ℕ) (hd : ¬ l ∣ d) (m : ℕ) :
    ∃ t ∈ Ine (F := ℚ) A, (cycMod ℚ Ω l m t)⁻¹ = un d hd m := by
  obtain ⟨u, hu⟩ := exists_unit (l := l) d hd
  obtain ⟨t, ht, e⟩ := (pFrobEx l hl Ω A hA).2.2 u⁻¹
  refine ⟨t, ht, Units.ext ?_⟩
  have h1 : (cycMod ℚ Ω l m t)⁻¹ = Units.map (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)).toMonoidHom u := by
    simp [cycMod, e]
  rw [h1]
  simp [un, hu]

private theorem mem_of_mul_mem (c : Coef l) {θ y : Qbar l} (h1 : ‖θ‖ = 1) (hy : y ∈ c.O) (h0 : y ≠ 0)
    (hθ : θ * y ∈ c.O) : θ ∈ c.O := by
  obtain ⟨β⟩ := (pBasEx l c).1
  have hinv := ((pBasEx l c).2 β).2.2.2
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at h1
  rcases ValuationRing.dvd_total (⟨y, hy⟩ : c.O) ⟨θ * y, hθ⟩ with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h2 : θ * y = y * k := congrArg Subtype.val hk
    have h3 : θ = k := by
      apply mul_right_cancel₀ h0
      rw [h2, mul_comm]
    rw [h3]; exact k.2
  · have h2 : y = θ * y * k := congrArg Subtype.val hk
    have h3 : θ⁻¹ = k := by
      apply mul_left_cancel₀ (mul_ne_zero hθ0 h0)
      rw [← h2, mul_assoc, mul_comm θ, mul_assoc, inv_mul_cancel₀ hθ0, mul_one]
    have h4 : θ⁻¹ ∈ c.O := by rw [h3]; exact k.2
    have := hinv θ⁻¹ h4 (by rw [norm_inv, h1, inv_one])
    rwa [inv_inv] at this

private theorem eig_at (hl : l ≠ 2) (hA : OverL l A) {c : Coef l} {Z : Sy Ω l} (hZ : IwI c A Z) {a : Qbar l} {fr : G ℚ Ω}
    (hfr : fr ∈ Dec (F := ℚ) A) (E : ∀ m, ∀ s ∈ Hm l A m, Z m (fr * s * fr⁻¹) 1 = a * Z m s 1) (m : ℕ) {s : G ℚ Ω}
    (hs : s ∈ Hm l A m) {t : G ℚ Ω} (ht : t ∈ Ine (F := ℚ) A) :
    Z m (fr * s * fr⁻¹) (cycMod ℚ Ω l m t)⁻¹ = a * Z m s (cycMod ℚ Ω l m t)⁻¹ := by
  have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
  have hsk : cycMod ℚ Ω l m s = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2
  have hs' : fr * s * fr⁻¹ ∈ Hm l A m := by
    refine Subgroup.mem_inf.2 ⟨conj_mem_Ine hfr hsI, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have ht' : fr * t * fr⁻¹ ∈ Ine (F := ℚ) A := conj_mem_Ine hfr ht
  have h1 := (pConj l hl Ω A hA c Z hZ m _ hs' _ ht').2 1
  have hc : cycMod ℚ Ω l m (fr * t * fr⁻¹) = cycMod ℚ Ω l m t := by
    rw [map_mul, map_mul, map_inv, mul_comm (cycMod ℚ Ω l m fr), mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (fr * t * fr⁻¹) * (fr * s * fr⁻¹) * (fr * t * fr⁻¹)⁻¹ = fr * (t * s * t⁻¹) * fr⁻¹ := by group
  have h2 := pConj l hl Ω A hA c Z hZ m s hs t ht
  have h3 := E m _ h2.1
  have h4 := h2.2 1
  rw [hconj, hc, one_mul] at h1
  rw [one_mul] at h4
  rw [← h1, h3, h4]

private theorem sharp_eig (hl : l ≠ 2) (hA : OverL l A) {c : Coef l} {Z : Sy Ω l} (hZ : IwI c A Z) {a : Qbar l} {fr : G ℚ Ω}
    (hfr : fr ∈ Dec (F := ℚ) A) (E : ∀ m, ∀ s ∈ Hm l A m, Z m (fr * s * fr⁻¹) 1 = a * Z m s 1) (d : ℕ) (hd : ¬ l ∣ d) (m : ℕ)
    {s : G ℚ Ω} (hs : s ∈ Hm l A m) : sharp d hd Z m (fr * s * fr⁻¹) 1 = a * sharp d hd Z m s 1 := by
  obtain ⟨t, ht, e⟩ := exists_ine_un (Ω := Ω) hl hA d hd m
  simp only [sharp, tr, one_mul]
  rw [E m s hs, ← e, eig_at hl hA hZ hfr E m hs ht]
  ring

private theorem pack (hl : l ≠ 2) (hA : OverL l A) {j : Ω →+* Qbar l} (Φ : Fr l A j) {c : Coef l} (β : Bas c) {ζ : ℕ → Ω}
    (hζ : Roots l ζ) {Y : Sy Ω l} (hY : IwI c A Y) {D : Fin β.d → PowerSeries Φ.R} (hD : Rep Φ β ζ Y D) {a : Qbar l}
    (ha : ‖a‖ = 1) (E : ∀ m, ∀ s ∈ Hm l A m, Y m (Φ.fr * s * Φ.fr⁻¹) 1 = a * Y m s 1) :
    ∃ (a₁ : c.O) (Gs : PowerSeries (Qbar l)) (v : ℂ_[l]), (∀ i, Φ.tw 1 (D i) = Φ.act (β.mat a₁) D i) ∧ ‖v‖ = 1 ∧
      (∀ n, Gs.coeff n ∈ c.O) ∧
      (∀ n, Φ.lam β (fun i => (D i).coeff n) = v * algebraMap (PadicAlgCl l) ℂ_[l] (Gs.coeff n)) ∧
      ((a₁ : PadicAlgCl l) = a ∨ Gs = 0) := by
  by_cases haO : a ∈ c.O
  · let a' : c.O := ⟨a, haO⟩
    have hinv := ((pBasEx l c).2 β).2.2.2 a haO ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    have hu : IsUnit a' := IsUnit.of_mul_eq_one ⟨a⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
    have hfr := pRepFrob l hl Ω A hA j Φ c β ζ hζ Y D a' hD E
    obtain ⟨v, hv, hper⟩ := pPeriod l hl Ω A hA j Φ c β a' hu
    have hx : ∀ n, ∃ o : c.O, Φ.lam β (fun i => (D i).coeff n) = v * algebraMap (PadicAlgCl l) ℂ_[l] (o : PadicAlgCl l) := by
      intro n
      refine hper _ fun i => ?_
      have := congrArg (PowerSeries.coeff n) (hfr i)
      simpa [Fr.tw, Fr.act, PowerSeries.coeff_C_mul] using this
    choose o ho using hx
    refine ⟨a', PowerSeries.mk fun n => (o n : PadicAlgCl l), v, hfr, hv, fun n => ?_, fun n => ?_, Or.inl rfl⟩
    · rw [PowerSeries.coeff_mk]; exact (o n).2
    · rw [PowerSeries.coeff_mk]; exact ho n
  · have hz : ∀ m, ∀ s ∈ Hm l A m, Y m s 1 = 0 := by
      intro m s hs
      by_contra h0
      have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
      refine haO (mem_of_mul_mem c ha (hY.int m s hsI 1) h0 ?_)
      rw [← E m s hs]
      exact hY.int m _ (conj_mem_Ine Φ.fr_dec hsI) 1
    have h0 := pRepUniq l hl Ω A hA j Φ c β ζ hζ Y Y D 0 hD
      ((pRepAdd l hl Ω A hA j Φ c β ζ hζ).2 Y hz) (fun _ _ _ => rfl)
    subst h0
    refine ⟨1, 0, 1, fun i => ?_, by simp, fun n => by simp [zero_mem], fun n => ?_, Or.inr rfl⟩
    · simp [Fr.tw, Fr.act]
    · simp [Fr.lam]

private theorem exists_approx (v : ℂ_[l]) (hv : ‖v‖ = 1) : ∃ vm : ℕ → Qbar l,
    (∀ m, ‖algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v‖ ≤ ‖(l : ℂ_[l]) ^ m‖) ∧ ∀ m, ‖vm m‖ = 1 ∧ Cg m (vm (m + 1)) (vm m) := by
  have hn : ∀ n, ‖(l : ℂ_[l]) ^ n‖ = ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n
    rw [norm_pow, norm_pow, ← PadicComplex.coe_natCast]
    congr 1
    exact PadicComplex.norm_extends l _
  have hal : ∀ x : Qbar l, ‖algebraMap (PadicAlgCl l) ℂ_[l] x‖ = ‖x‖ := fun x => PadicComplex.norm_extends l x
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one
  have hl0 : 0 < ‖((l : ℕ) : Qbar l)‖ := norm_pos_iff.2 GlobalTheory.LambdaValuationPowers.natCast_ne_zero
  have hex : ∀ m : ℕ, ∃ y : Qbar l, ‖algebraMap (PadicAlgCl l) ℂ_[l] y - v‖ ≤ ‖(l : ℂ_[l]) ^ (m + 1)‖ := by
    intro m
    have hr : 0 < ‖(l : ℂ_[l]) ^ (m + 1)‖ := by
      rw [hn, norm_pow]; exact pow_pos hl0 _
    obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt v hr
    refine ⟨y, ?_⟩
    rw [dist_comm, dist_eq_norm] at hy
    exact hy.le
  choose vm hvm using hex
  have hlt : ∀ m, ‖algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v‖ < 1 := by
    intro m
    refine (hvm m).trans_lt ?_
    rw [hn, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hl1 (by omega)
  refine ⟨vm, fun m => (hvm m).trans ?_, fun m => ⟨?_, ?_⟩⟩
  · rw [hn, hn]; exact norm_pow_anti m (m + 1) (by omega)
  · rw [← hal]
    apply le_antisymm
    · have e : algebraMap (PadicAlgCl l) ℂ_[l] (vm m) = (algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) + v := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hlt m).le hv.le)
    · have e : v = algebraMap (PadicAlgCl l) ℂ_[l] (vm m) + -(algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) := by ring
      have h1 : ‖v‖ ≤ _ := (congrArg norm e).le.trans (IsUltrametricDist.norm_add_le_max _ _)
      rw [hv, norm_neg] at h1
      rcases le_max_iff.1 h1 with h | h
      · exact h
      · exact absurd h (not_le.2 (hlt m))
  · unfold Cg
    rw [← hal, map_sub]
    have e : algebraMap (PadicAlgCl l) ℂ_[l] (vm (m + 1)) - algebraMap (PadicAlgCl l) ℂ_[l] (vm m) =
        (algebraMap (PadicAlgCl l) ℂ_[l] (vm (m + 1)) - v) + -(algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine (hvm (m + 1)).trans ?_
      rw [hn]; exact norm_pow_anti m _ (by omega)
    · rw [norm_neg]
      refine (hvm m).trans ?_
      rw [hn]; exact norm_pow_anti m _ (by omega)

private theorem sum_step {m : ℕ} (ψ : DirichletCharacter (Qbar l) (l ^ m)) (d₀ : ℕ) (hd : ¬ l ∣ d₀) (n : ℕ)
    (h h' T : (ZMod (l ^ m))ˣ → Qbar l) (w : Qbar l) (h1 : ∀ b, Cg n (h b) (h' b))
    (h2 : ∀ b, Cg n (h' b - (d₀ : Qbar l) * h' (b * un d₀ hd m)) (w * T b)) :
    Cg n ((1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b)
      (w * ∑ b : (ZMod (l ^ m))ˣ, ψ b * T b) := by
  have hu : ((un d₀ hd m : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = (d₀ : ZMod (l ^ m)) := by simp [un]
  have hinv : ψ⁻¹ (d₀ : ZMod (l ^ m)) * ψ (d₀ : ZMod (l ^ m)) = 1 := by
    rw [← hu, MulChar.inv_apply, Ring.inverse_unit, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hre : ∑ b : (ZMod (l ^ m))ˣ, ψ b * h (b * un d₀ hd m) =
      ψ⁻¹ (d₀ : ZMod (l ^ m)) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight (un d₀ hd m)) _ _ fun b => ?_
    simp only [Equiv.coe_mulRight, Units.val_mul, map_mul, hu]
    linear_combination (-(ψ b * h (b * un d₀ hd m))) * hinv
  have key : (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b =
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * (h b - (d₀ : Qbar l) * h (b * un d₀ hd m)) := by
    have e : ∀ b : (ZMod (l ^ m))ˣ, ψ b * (h b - (d₀ : Qbar l) * h (b * un d₀ hd m)) =
        ψ b * h b - (d₀ : Qbar l) * (ψ b * h (b * un d₀ hd m)) := fun b => by ring
    simp only [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hre]
    ring
  rw [key, Finset.mul_sum]
  have e2 : ∀ b : (ZMod (l ^ m))ˣ, w * (ψ b * T b) = ψ b * (w * T b) := fun b => by ring
  simp only [e2]
  refine cg_sum _ _ _ fun b _ => cg_mul (DirichletCharacter.unit_norm_eq_one ψ b).le ?_
  exact cg_trans (cg_sub (h1 b) (cg_mul (norm_nat_le d₀) (h1 _))) (h2 b)

theorem pCore : SCore := by
  intro l _ hl Ω _ _ _ A hA c Z a j d₀ e₀ m₀ ζ hZ ha E hj hd hζ hP
  obtain ⟨Φ⟩ := pFrEx3 l hl Ω A hA j hj
  obtain ⟨β⟩ := (pBasEx l c).1
  have hHP : HasPres β A ζ Z := by
    refine ⟨e₀, max m₀ 1, fun m hm => ?_⟩
    obtain ⟨ι, _, P, o, h1, h2, h3⟩ := hP m (le_of_max_le_left hm)
    obtain ⟨P', hP', -⟩ := pToBasis l hl Ω A hA c β ζ hζ j hj Z m (m - e₀) ι P o (le_of_max_le_right hm) h1 h2 h3
    exact ⟨P', hP'⟩
  have hCont := pContOf l hl Ω A hA c β ζ hζ Z hZ hHP
  have hops := pIwOps l hl Ω A hA c Z hZ d₀ hd
  have hHS := pKumEx l hl Ω A hA c β ζ hζ Z hZ hCont d₀ hd
  obtain ⟨D, hD⟩ := pRepEx l hl Ω A hA j Φ c β ζ hζ _ hops.2 hHS
  have E' : ∀ m, ∀ s ∈ Hm l A m, Z m (Φ.fr * s * Φ.fr⁻¹) 1 = a * Z m s 1 := E Φ.fr Φ.fr_dec Φ.fr_frob Φ.fr_cyc
  obtain ⟨a₁, Gs, v, htw, hv, hGs, hlam, hor⟩ := pack hl hA Φ β hζ hops.2 hD ha
    (fun m s hs => sharp_eig hl hA hZ Φ.fr_dec E' d₀ hd m hs)
  have hGn : ∀ n, ‖Gs.coeff n‖ ≤ 1 := fun n => GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hGs n)
  obtain ⟨vm, hvm, hvm2⟩ := exists_approx v hv
  obtain ⟨c₁, m₁, hcl⟩ := pClause1 l hl Ω A hA j Φ c β ζ hζ hj Z hZ d₀ hd D a₁ Gs v vm hD htw hGn hlam hvm e₀
  refine ⟨Gs, vm, max c₁ e₀, max m₁ 1, hGs, hvm2, ?_, ?_⟩
  · intro m hm ι _ P o h1 h2 h3 ψ
    obtain ⟨P', hP', hcg⟩ := pToBasis l hl Ω A hA c β ζ hζ j hj Z m (m - e₀) ι P o (le_of_max_le_right hm) h1 h2 h3
    have hc := hcl m (le_of_max_le_left hm) P' hP'
    have hT : ∀ (N : ℕ) (z : Qbar l), vm m * (a₁ : PadicAlgCl l) ^ m * tval Gs N z = vm m * a ^ m * tval Gs N z := by
      intro N z
      rcases hor with e | e
      · rw [e]
      · simp [e, tval]
    exact sum_step ψ d₀ hd (m - max c₁ e₀) (fun b => htv j (ζ m) P o (b : ZMod (l ^ m)).val)
      (fun b => htv j (ζ m) (fun i => (P' i).map (R0 A).subtype) β.val (b : ZMod (l ^ m)).val)
      (fun b => tval Gs (l ^ (3 * m)) (j (ζ m) ^ (b : ZMod (l ^ m)).val)) (vm m * a ^ m)
      (fun b => cg_mono (Nat.sub_le_sub_left (le_max_right _ _) m) (hcg b))
      (fun b => by
        have := hc b
        rw [hT] at this
        exact cg_mono (Nat.sub_le_sub_left (le_max_left _ _) m) this)
  · intro φ k hk hsp
    obtain ⟨g, hg, c₂, Z', hZ', hC', rel⟩ := pDiv l hl Ω A hA c Z hZ hCont φ k hk hsp
    have ops' := pIwOps l hl Ω A hA c Z' hZ' d₀ hd
    have hHS' := pKumEx l hl Ω A hA c β ζ hζ Z' hZ' hC' d₀ hd
    obtain ⟨D', hD'⟩ := pRepEx l hl Ω A hA j Φ c β ζ hζ _ ops'.2 hHS'
    have hθn : ‖φ (g : ZMod l) * (g : Qbar l) ^ k‖ = 1 := by
      have hcop : g.Coprime l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hg).symm
      have h1 := DirichletCharacter.unit_norm_eq_one φ (ZMod.unitOfCoprime g hcop)
      rw [ZMod.coe_unitOfCoprime] at h1
      rw [norm_mul, norm_pow, norm_nat_eq g hg, h1, one_pow, one_mul]
    have hrel : ∀ m, ∀ s ∈ Hm l A m, ∀ x, (l : Qbar l) ^ c₂ * sharp d₀ hd Z m s x =
        sharp d₀ hd Z' m s (x * un g hg m) - φ (g : ZMod l) * (g : Qbar l) ^ k * sharp d₀ hd Z' m s x := by
      intro m s hs x
      have r1 := rel m s hs x
      have r2 := rel m s hs (x * un d₀ hd m)
      simp only [sharp, tr] at r1 r2 ⊢
      rw [mul_right_comm x (un d₀ hd m) (un g hg m)] at r2
      linear_combination r1 - (d₀ : Qbar l) * r2
    by_cases hθ : φ (g : ZMod l) * (g : Qbar l) ^ k ∈ c.O
    · let θ : c.O := ⟨_, hθ⟩
      have R1 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ D ((l : c.O) ^ c₂) hD
      have R2 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ D' θ hD'
      have R3 := (pRepAdd l hl Ω A hA j Φ c β ζ hζ).1 _ _ _ _ R1 R2
      have R4 := pRepTr l hl Ω A hA j Φ c β ζ hζ _ ops'.2 g hg D' hD'
      have heq := pRepUniq l hl Ω A hA j Φ c β ζ hζ _ _ _ _ R3 R4 (fun m s hs => by
        have h1 := hrel m s hs 1
        have e : (((l : c.O) ^ c₂ : c.O) : PadicAlgCl l) = (l : Qbar l) ^ c₂ := by simp
        rw [e]
        change _ + (φ (g : ZMod l) * (g : Qbar l) ^ k) * _ = sharp d₀ hd Z' m s (1 * un g hg m)
        rw [h1]
        ring)
      refine pClause2 l hl Ω A hA j Φ hj c β D D' Gs v g c₂ k φ θ hg rfl hv hGn hlam fun i => ?_
      have := congrFun heq i
      rw [eq_sub_iff_add_eq]
      exact this
    · have hz' : ∀ m, ∀ s ∈ Hm l A m, ∀ x, sharp d₀ hd Z' m s x = 0 := by
        intro m s hs x
        by_contra h0
        have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
        refine hθ (mem_of_mul_mem c hθn (ops'.2.int m s hsI x) h0 ?_)
        have h1 := hrel m s hs x
        have e : φ (g : ZMod l) * (g : Qbar l) ^ k * sharp d₀ hd Z' m s x =
            sharp d₀ hd Z' m s (x * un g hg m) - (l : Qbar l) ^ c₂ * sharp d₀ hd Z m s x := by
          rw [h1]; ring
        rw [e]
        exact c.O.sub_mem (ops'.2.int m s hsI _) (c.O.mul_mem (pow_mem (natCast_mem _ _) _) (hops.2.int m s hsI x))
      have hz : ∀ m, ∀ s ∈ Hm l A m, sharp d₀ hd Z m s 1 = 0 := by
        intro m s hs
        have h1 := hrel m s hs 1
        rw [hz' m s hs, hz' m s hs, mul_zero, sub_zero] at h1
        exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ GlobalTheory.LambdaValuationPowers.natCast_ne_zero)
      have h0 := pRepUniq l hl Ω A hA j Φ c β ζ hζ _ _ D 0 hD
        ((pRepAdd l hl Ω A hA j Φ c β ζ hζ).2 _ hz) (fun _ _ _ => rfl)
      have hG0 : Gs = 0 := by
        ext n
        have h1 := hlam n
        have hv0 : v ≠ 0 := by rintro rfl; simp at hv
        have h2 : Φ.lam β (fun i => (D i).coeff n) = 0 := by simp [h0, Fr.lam]
        rw [h2] at h1
        have h3 := (mul_eq_zero.1 h1.symm).resolve_left hv0
        simpa using h3
      rw [hG0]
      intro n
      exact ⟨0, fun r _ ξ _ => by simp [Cg, intg, mass, tval]⟩

end UpperTheory.Kd.C7
