import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaRunParametersUniformTorusStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaSumBound

theorem finsum_mem_le_card_mul {α ι : Type*} [Fintype ι] (g : ι → α) (S : Set α)
    (hS : S ⊆ Set.range g) (f : α → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ a ∈ S, f a ≤ M) :
    ∑ᶠ (a : α) (_ : a ∈ S), f a ≤ Fintype.card ι * M := by
  classical
  have hfin : S.Finite := (Set.finite_range g).subset hS
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have h1 : ∑ a ∈ hfin.toFinset, f a ≤ hfin.toFinset.card • M :=
    Finset.sum_le_card_nsmul _ _ _ fun a ha => hf a (hfin.mem_toFinset.1 ha)
  have h2 : hfin.toFinset.card ≤ Fintype.card ι := by
    have : hfin.toFinset ⊆ Finset.univ.image g := by
      intro a ha
      obtain ⟨i, rfl⟩ := hS (hfin.mem_toFinset.1 ha)
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact (Finset.card_le_card this).trans (Finset.card_image_le.trans (by simp))
  rw [nsmul_eq_mul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hM)

theorem exists_coords {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι)
    (hv : v ∈ ZSpan.fundamentalDomain b) (hL : ((5 : ℂ) ^ 2) • v ∈ lat b) :
    ∃ k : κ → Fin 25, ∑ i, (((k i : ℕ) : ℝ) / 25) • b i = v := by
  have e : ((5 : ℂ) ^ 2) • v = (25 : ℝ) • v := by
    rw [← Complex.coe_smul]; congr 1; push_cast; norm_num
  rw [e] at hL
  have h1 := (b.mem_span_iff_repr_mem ℤ _).1 hL
  have h2 : ∀ i, ∃ k : Fin 25, ((k : ℕ) : ℝ) / 25 = b.repr v i := by
    intro i
    obtain ⟨n, hn⟩ := h1 i
    obtain ⟨h3, h4⟩ := hv i
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, eq_intCast] at hn
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hn1 : (n : ℝ) < 25 := by linarith
    have hn0' : 0 ≤ n := by exact_mod_cast hn0
    have hn1' : n < 25 := by exact_mod_cast hn1
    refine ⟨⟨n.toNat, by omega⟩, ?_⟩
    have : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hn0'
    simp only [this]
    linarith
  choose k hk using h2
  refine ⟨k, ?_⟩
  simp only [hk]
  exact b.sum_repr v

theorem log_le_of_bounds {K S la th c k B p3 p1 f t : ℝ} (hK : 0 < K) (hS : 0 < S) (hla : 0 < la)
    (hth : 0 < th) (hc : 0 < c) (hk : 0 < k) (hB : 0 ≤ B) (hf : 0 < f) (ht : la ^ 2 * t ≤ f)
    (h1 : la < th → S ≤ K * (Real.exp p3 * (k * (c / la ^ 2)) ^ B *
      Real.exp (-(Real.pi * (c / la ^ 2) / 5 ^ 4))) ^ 2)
    (h2 : th ≤ la → S ≤ K * Real.exp p1 ^ 2) :
    Real.log S ≤ (Real.log K + 2 * |p3| + 2 * B * |Real.log (k * c)| + 2 * |p1| +
      2 * Real.pi * c / (5 ^ 4 * th ^ 2)) + 4 * B * Real.log (1 + 1 / la) -
      2 * Real.pi * c / (5 ^ 4 * f) * t := by
  have hpi := Real.pi_pos
  have hl0 : 0 ≤ Real.log (1 + 1 / la) := Real.log_nonneg (by have := one_div_pos.2 hla; linarith)
  have hd : 2 * Real.pi * c / (5 ^ 4 * f) * t ≤ 2 * Real.pi * c / (5 ^ 4 * la ^ 2) := by
    have : t ≤ f / la ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    calc 2 * Real.pi * c / (5 ^ 4 * f) * t ≤ 2 * Real.pi * c / (5 ^ 4 * f) * (f / la ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  have hth0 : 0 ≤ 2 * Real.pi * c / (5 ^ 4 * th ^ 2) := by positivity
  have a3 := abs_nonneg p3
  have a1 := abs_nonneg p1
  have ak : 0 ≤ B * |Real.log (k * c)| := by positivity
  have aB := mul_nonneg hB hl0
  rcases lt_or_ge la th with h | h
  · have h3 := Real.log_le_log hS (h1 h)
    rw [Real.log_mul hK.ne' (by positivity), Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp,
      Real.log_rpow (by positivity)] at h3
    have h4 : Real.log (k * (c / la ^ 2)) ≤ |Real.log (k * c)| + 2 * Real.log (1 + 1 / la) := by
      have e : k * (c / la ^ 2) = (k * c) * (1 / la) ^ 2 := by field_simp
      rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have := Real.log_le_log (one_div_pos.2 hla) (show 1 / la ≤ 1 + 1 / la by linarith)
      have := le_abs_self (Real.log (k * c))
      push_cast
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hB
    have e : 2 * Real.pi * c / (5 ^ 4 * la ^ 2) = 2 * (Real.pi * (c / la ^ 2) / 5 ^ 4) := by
      field_simp
    have := le_abs_self p3
    push_cast at h3
    linarith
  · have h3 := Real.log_le_log hS (h2 h)
    rw [Real.log_mul hK.ne' (by positivity), Real.log_pow, Real.log_exp] at h3
    have h4 : 2 * Real.pi * c / (5 ^ 4 * la ^ 2) ≤ 2 * Real.pi * c / (5 ^ 4 * th ^ 2) := by
      gcongr
    have := le_abs_self p1
    push_cast at h3
    linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem two_le_rank (X : Data E r) (ξ : Fin r → E) (h : X.IsIso ξ) : 2 ≤ r := by
  obtain ⟨-, h1, h2⟩ := h
  rcases r with _ | _ | r
  · exact absurd (Subsingleton.elim _ _) h2
  · exfalso
    have hd := X.Gm_det
    have h0 : ξ 0 ≠ 0 := fun h0 => h2 (funext fun i => by fin_cases i; exact h0)
    simp only [herm, cc, Nat.reduceAdd, Fin.sum_univ_one, Matrix.det_fin_one, mul_eq_zero,
      map_eq_zero, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero] at h1 hd
    simp_all
  · omega

theorem firstMinimum_sq_mul_iInf_height_le_card (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E}
    (hξ : ξ ∈ X.Λ) (h0 : ξ ≠ 0) : X.la1 x ^ 2 * ⨅ τ, X.tt ξ x τ ≤ Fintype.card X.Ψ := by
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    unfold Data.c
    have : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).2 X.ξ0_ne
    positivity
  have hpos : ∀ v : Fin r → E, v ≠ 0 → ∀ τ : X.Ψ, 0 < X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv0 τ
    have hne : Data.emb τ.1 v ≠ 0 := by
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hv0
      intro h
      exact (map_ne_zero τ.1).2 ha (congrFun h a)
    exact mul_pos (hc τ) (X.maj_pos hx τ hne)
  have hlb : ∀ t ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}, 0 ≤ t := by
    rintro _ ⟨v, -, hv, rfl⟩
    exact Finset.sum_nonneg fun τ _ => (hpos v hv τ).le
  have h1 : X.la1 x ^ 2 ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) := by
    unfold Data.la1 Data.firstMinimumSq
    rw [Real.sq_sqrt (Real.sInf_nonneg hlb)]
    exact csInf_le ⟨0, hlb⟩ ⟨ξ, hξ, h0, rfl⟩
  have ht0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => (one_div_pos.2 (hpos ξ h0 τ)).le
  refine (mul_le_mul_of_nonneg_right h1 ht0).trans ?_
  rw [Finset.sum_mul]
  calc _ ≤ ∑ _τ : X.Ψ, (1 : ℝ) := by
        refine Finset.sum_le_sum fun τ _ => ?_
        have h2 : ⨅ τ, X.tt ξ x τ ≤ X.tt ξ x τ := ciInf_le (Set.finite_range _).bddBelow τ
        refine (mul_le_mul_of_nonneg_left h2 (hpos ξ h0 τ).le).trans (le_of_eq ?_)
        exact mul_one_div_cancel (hpos ξ h0 τ).ne'
    _ = _ := by simp

omit [IsCMField E] in
theorem prod_eq_sq (T : PT E) (s : (Fin 1 → Vsp T.dim) → ℂ) (a : Fin T.r → Vsp T.dim) :
    ∏ b, T.ptN2 1 s (fun _ => a b) / T.l2 1 s =
      (∏ j, Real.sqrt (T.ptN2 1 s fun _ => a j) / Real.sqrt (T.l2 1 s)) ^ 2 := by
  have hp : ∀ v, 0 ≤ T.ptN2 1 s v := fun v => by unfold PT.ptN2; positivity
  have hl : 0 ≤ T.l2 1 s := MeasureTheory.integral_nonneg hp
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [div_pow, Real.sq_sqrt (hp _), Real.sq_sqrt hl]

omit [IsCMField E] in

theorem finsum_le (T : PT E) (S : Set (Fin T.r → Vsp T.dim))
    (hS : ∀ a ∈ S, (∀ j, a j ∈ ZSpan.fundamentalDomain T.b) ∧ ∀ j, ((5 : ℂ) ^ 2) • a j ∈ T.L)
    (f : (Fin T.r → Vsp T.dim) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ a ∈ S, f a ≤ M) :
    ∑ᶠ (a) (_ : a ∈ S), f a ≤ (25 : ℝ) ^ (2 * (Module.finrank ℚ E * T.r) * T.r) * M := by
  have h := finsum_mem_le_card_mul
    (fun (k : Fin T.r → Fin (2 * Fintype.card (Idx T.dim)) → Fin 25) (j : Fin T.r) =>
      ∑ i, (((k j i : ℕ) : ℝ) / 25) • T.b i) S (fun a ha => by
        choose k hk using fun j => exists_coords T.b (a j) ((hS a ha).1 j) ((hS a ha).2 j)
        exact ⟨k, funext hk⟩) f M hM hf
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hM)
  have hN : Fintype.card (Idx T.dim) ≤ Module.finrank ℚ E * T.r := by
    rw [Fintype.card_sigma, ← NumberField.Embeddings.card E ℂ]
    calc _ ≤ ∑ _τ : E →+* ℂ, T.r := Finset.sum_le_sum fun τ _ => by
          have := T.dim_conj τ
          simp only [Fintype.card_fin]; omega
      _ = _ := by simp
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ (by omega))

theorem growth_decay : TStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (PT.f E : ℝ) ≤ PT.rd E → (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E → (∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ PT.f E ∧ (X.p0 ≤ m ∨ r - X.p0 ≤ m)) → ∃ C A' : ℝ, 0 ≤ A' ∧ ∀ x ∈ X.dom, ∀ A : TorusAt X.toData x, 0 < (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) → Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) ≤ C + A' * Real.log (1 + 1 / X.la1 x) ∧ ∀ ξ : Fin r → E, X.toData.IsIso ξ → Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) ≤ C + A' * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card))) * ⨅ τ, X.tt ξ x τ := by
  intro hT E _ _ _ r X ⟨ξ0, hξ0⟩ hf1 hf2 hrd ⟨m, hm1, hmf, hmp⟩
  have hr : 2 ≤ r := two_le_rank X.toData ξ0 hξ0
  have hf : 1 ≤ PT.f E := (Nat.one_le_pow _ _ hm1).trans hmf
  have hfR : (0 : ℝ) < PT.f E := by exact_mod_cast hf
  have hcard : Fintype.card X.Ψ = PT.f E := QuadraticCoefficientForms.card_Psi X.toData
  obtain ⟨τ0⟩ : Nonempty X.Ψ := Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos X.toData)
  obtain ⟨q, R0, hth, hP⟩ := GlobalTheory.T.exists_thetaRunParameters_uniform_torus E r m (by nlinarith) hm1 hmf hf1 hf2 hrd
  have hrd0 : 0 < PT.rd E := by linarith
  have hds : (0 : ℝ) < dstar (E := E) m := by
    unfold dstar; exact_mod_cast Nat.mul_pos (by omega) hm1
  have hRR : (0 : ℝ) < RR (E := E) := by unfold RR; positivity
  have hrd2 : |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card) = PT.rd E ^ 2 := by
    have h1 : (X.Ψ.card : ℝ) = PT.f E := by rw [← hcard]; simp
    have h2 : (Module.finrank ℚ E : ℝ) = 2 * PT.f E := by
      have h3 := NumberField.IsTotallyComplex.finrank E
      have : Module.finrank ℚ E = 2 * PT.f E := by unfold PT.f; omega
      exact_mod_cast this
    unfold PT.rd
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), h1, h2]
    congr 1
    push_cast
    field_simp
  set p1 : ℝ := 1 + (PT.f E * r : ℕ) * Real.log (1 + 6 * Real.sqrt ((PT.f E * r : ℕ) * q)) with hp1
  set p3 : ℝ := r * (p1 + Real.log (2 * (3 * (dstar (E := E) m : ℝ)) ^ dstar (E := E) m) +
    dstar (E := E) m) with hp3
  set k : ℝ := 4 * RR (E := E) * (dstar (E := E) m : ℝ) ^ 2 with hk
  set B : ℝ := (r * dstar (E := E) m : ℝ) / 4 with hB
  set c : ℝ := 2 * PT.f E / PT.rd E ^ 2 with hc
  set K : ℝ := (25 : ℝ) ^ (2 * (Module.finrank ℚ E * r) * r) with hK
  have hB0 : 0 ≤ B := by positivity
  refine ⟨Real.log K + 2 * |p3| + 2 * B * |Real.log (k * c)| + 2 * |r * p1| +
      2 * Real.pi * c / (5 ^ 4 * th (E := E) q R0 ^ 2), 4 * B, by positivity, ?_⟩
  intro x hx A hS
  have hAr : A.T.r = r := by
    have h1 := A.T.dim_conj τ0.1
    rw [A.dim_pos, A.dim_neg] at h1
    have := X.p0_le
    omega
  obtain ⟨P, hq, hR, hm⟩ := hP A.T hAr (by
    rcases hmp with h | h
    · exact ⟨τ0.1, by rw [A.dim_pos]; exact h⟩
    · exact ⟨_, by rw [A.dim_neg τ0]; exact h⟩)
  have hla : A.T.la1 = X.la1 x :=
    (TorusAtPf.torusAtLa1_holds E r X.toData x hx A.T
      (TorusAtDataPf.torusAtIs_holds E r X.toData x A)).1
  have hla0 : 0 < X.la1 x := by
    rw [← hla]
    apply first_minimum_pos
    have hN : 0 < 2 * Fintype.card (Idx A.T.dim) := by
      have : Nonempty (Idx A.T.dim) := by
        rcases Nat.eq_zero_or_pos X.p0 with h | h
        · exact ⟨⟨_, ⟨0, by rw [A.dim_neg τ0]; omega⟩⟩⟩
        · exact ⟨⟨τ0.1, ⟨0, by rw [A.dim_pos τ0]; omega⟩⟩⟩
      have := Fintype.card_pos (α := Idx A.T.dim)
      omega
    exact ⟨A.T.b ⟨0, hN⟩, Submodule.subset_span ⟨_, rfl⟩, A.T.b.ne_zero _⟩
  have e1 : P.p1 = p1 := by simp only [Par.p1, PT.gA, hAr, hq, hp1]
  have e3 : P.p3 = p3 := by simp only [Par.p3, Par.p2, e1, hAr, hm, hp3]
  have ek : P.ka0 = k := by simp only [Par.ka0, hm, hk]
  have key := fun (t : ℝ) (ht : X.la1 x ^ 2 * t ≤ PT.f E) =>
    log_le_of_bounds (K := K) (k := k) (c := c) (B := B) (p3 := p3) (p1 := r * p1)
      (by positivity) hS hla0 hth (by positivity) (by positivity) hB0 hfR ht
      (fun h => by
        have eph : P.ph = c / X.la1 x ^ 2 := by
          simp only [Par.ph, PT.ph, hq, hR, hla, if_pos h, hc]
          field_simp
        have hK' : K = (25 : ℝ) ^ (2 * (Module.finrank ℚ E * A.T.r) * A.T.r) := by rw [hAr]
        rw [hK']
        refine finsum_le A.T _ (fun a ha => ⟨ha.1, ha.2.1⟩) _ _ (by positivity) fun a ha => ?_
        rw [prod_eq_sq]
        refine pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => by positivity) ?_ 2
        have := (hT E A.T 1 P 5 (by norm_num) a (by exact_mod_cast ha.2.1)
          (by exact_mod_cast ha.2.2) A.s A.s_mem A.s_ne).1 (by rw [eph]; positivity)
        rw [e3, ek, eph, hm] at this
        have h5 : (A.T.r : ℝ) = r := by exact_mod_cast hAr
        rwa [h5, Nat.cast_ofNat] at this)
      (fun h => by
        have eph : P.ph = 0 := by
          simp only [Par.ph, PT.ph, hq, hR, hla, if_neg (not_lt.2 h)]
        have hK' : K = (25 : ℝ) ^ (2 * (Module.finrank ℚ E * A.T.r) * A.T.r) := by rw [hAr]
        rw [hK']
        refine finsum_le A.T _ (fun a ha => ⟨ha.1, ha.2.1⟩) _ _ (by positivity) fun a ha => ?_
        rw [prod_eq_sq]
        refine pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => by positivity) ?_ 2
        have := (hT E A.T 1 P 5 (by norm_num) a (by exact_mod_cast ha.2.1)
          (by exact_mod_cast ha.2.2) A.s A.s_mem A.s_ne).2 eph
        rw [e1] at this
        have h5 : (A.T.r : ℝ) = r := by exact_mod_cast hAr
        rwa [h5] at this)
  refine ⟨by simpa using key 0 (by simpa using hfR.le), fun ξ hξ => ?_⟩
  have := key _ (by rw [← hcard]; exact firstMinimum_sq_mul_iInf_height_le_card X.toData hx hξ.1 hξ.2.2)
  have e : 8 * Real.pi * (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card))) =
      2 * Real.pi * c / (5 ^ 4 * PT.f E) := by
    rw [hrd2, hc]; field_simp; norm_num
  rw [e]
  exact this

end GlobalTheory.ThetaSumBound
