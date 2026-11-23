import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MmatMulVec

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem herm_smul_left' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  unfold herm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem smul_mem_of_int {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) {c : E} (hc : IsIntegral ℤ c)
    {v : Fin r → E} (hv : v ∈ L) : c • v ∈ L := by
  first
  | exact L.smul_mem (⟨c, hc⟩ : 𝓞 E) hv
  | simpa using L.smul_mem (⟨c, hc⟩ : 𝓞 E) hv

namespace DataX

variable {r : ℕ} (X : DataX E r)

theorem discr_mul_hermitian_integral {v w : Fin r → E} (hv : v ∈ X.Λ) (hw : w ∈ X.Λ) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * (X.ξ0 * herm X.Gm v w)) := by
  have h := d4l2_dual_int' (-(X.ξ0 * herm X.Gm v w)) (fun γ => by
    obtain ⟨k, hk⟩ := X.EF_int ((γ : E) • v) (smul_mem_of_int X.Λ (RingOfIntegers.isIntegral_coe γ) hv) w hw
    refine ⟨k, ?_⟩
    rw [← hk]
    unfold EFf
    rw [herm_smul_left']
    congr 1; ring)
  have : ((NumberField.discr E).natAbs : E) * (X.ξ0 * herm X.Gm v w) =
      -(((NumberField.discr E).natAbs : E) * -(X.ξ0 * herm X.Gm v w)) := by ring
  rw [this]; exact h.neg

theorem Mmat_cong (u : Fin 2 → Fin r → E) (hmem : ∀ i, u i ∈ X.Λ) (β : Matrix (Fin 2) (Fin 2) E)
    (hβ : ∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((X.g * dEnat E : ℕ) : E) / 2 * γ) :
    ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u β *ᵥ v - v = (X.g : E) • y := by
  intro v hv
  choose γ hγi hγ using hβ
  set d := (NumberField.discr E).natAbs with hd
  have hint : ∀ k, IsIntegral ℤ ((d : E) * (X.ξ0 * herm X.Gm v (u k))) :=
    fun k => X.discr_mul_hermitian_integral hv (hmem k)
  have hc : ∀ i k, IsIntegral ℤ (X.κ0 / 2 * d * γ i k * herm X.Gm v (u k)) := by
    intro i k
    rcases X.κ0_xi with h | h
    · have e1 : X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) = γ i k * ((d : E) * (X.ξ0 * herm X.Gm v (u k))) := by
        rw [h]; ring
      rw [e1]; exact (hγi i k).mul (hint k)
    · have e1 : X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) = -(γ i k * ((d : E) * (X.ξ0 * herm X.Gm v (u k)))) := by
        rw [h]; ring
      rw [e1]; exact ((hγi i k).mul (hint k)).neg
  set c : Fin 2 → E := fun i => ∑ k, X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) with hcdef
  have hci : ∀ i, IsIntegral ℤ (c i) := fun i => by
    simp only [hcdef, Fin.sum_univ_two]; exact (hc i 0).add (hc i 1)
  refine ⟨∑ i, c i • u i, Submodule.sum_mem _ fun i _ => smul_mem_of_int X.Λ (hci i) (hmem i), ?_⟩
  rw [X.Mmat_mulVec, add_sub_cancel_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  simp only [hcdef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hγ i k, hd]
  unfold dEnat
  push_cast
  ring

theorem g_smul_mem {y : Fin r → E} (hy : y ∈ X.Λ) : (X.g : E) • y ∈ X.Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hy _

theorem exists_gamma (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (hmem : ∀ i, u i ∈ X.Λ)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : b ∈ X.LZ X.g) :
    ∃ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) ∧
      ∀ τ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.zmat u b τ := by
  obtain ⟨β, hβh, hβi, rfl⟩ := hb
  have hiso := hu.1
  have hγc : ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u β *ᵥ v - v = (X.g : E) • y :=
    X.Mmat_cong u hmem β hβi
  have hγc' : ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u (-β) *ᵥ v - v = (X.g : E) • y :=
    X.Mmat_cong u hmem (-β) (fun i k => by
      obtain ⟨γ', h1, h2⟩ := hβi i k
      exact ⟨-γ', h1.neg, by simp [h2]⟩)
  have hstab : IsUStab X.Gm X.Λ (X.gam u hiso β) := by
    refine ⟨fun x y => X.herm_Mmat u hiso β hβh x y, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨y, hy, hyeq⟩ := hγc x hx
      have e1 : X.Mmat u β *ᵥ x = x + (X.g : E) • y := by rw [← hyeq]; abel
      show X.Mmat u β *ᵥ x ∈ X.Λ
      rw [e1]; exact X.Λ.add_mem hx (X.g_smul_mem hy)
    · change X.Mmat u β *ᵥ x ∈ X.Λ at hx
      have hinv : X.Mmat u (-β) *ᵥ (X.Mmat u β *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, X.Mmat_mul u hiso, neg_add_cancel, Data.Mmat_zero, Matrix.one_mulVec]
      obtain ⟨y, hy, hyeq⟩ := hγc' _ hx
      have e1 : X.Mmat u (-β) *ᵥ (X.Mmat u β *ᵥ x) = X.Mmat u β *ᵥ x + (X.g : E) • y := by
        rw [← hyeq]; abel
      rw [← hinv, e1]; exact X.Λ.add_mem hx (X.g_smul_mem hy)
  exact ⟨X.gam u hiso β, X.cong _ hstab hγc, hγc, fun τ => X.Mmat_map u β τ⟩

theorem LZ_periodic (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (hmem : ∀ i, u i ∈ X.Λ)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P)
    (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : b ∈ X.LZ X.g) (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    P (X.Zb u b x) = P x := by
  obtain ⟨γ, hγΓ, hγc, hmap⟩ := X.exists_gamma u hu hmem b hb
  have e1 : X.Zb u b x = lact γ x := funext fun τ => by
    show X.zmat u b τ * mat x τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
    rw [hmap]
  rw [e1, hP.2.2 γ hγΓ x hx, hχ γ hγΓ hγc, one_mul]

noncomputable def c0E : E := ((X.g * dEnat E : ℕ) : E) / 2

theorem cc_c0E : cc X.c0E = X.c0E := by
  unfold c0E cc
  first
  | rw [map_div₀, map_natCast, map_ofNat]
  | simp

theorem tau_c0E (τ : E →+* ℂ) : τ X.c0E = ((((X.g * dEnat E : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
  unfold c0E
  rw [map_div₀, map_natCast, map_ofNat]
  push_cast
  try ring

theorem mem_LZ_of (w : Fin 2 → Fin 2 → E) (hwi : ∀ i k, IsIntegral ℤ (w i k))
    (hwh : ∀ i k, cc (w i k) = w k i) :
    X.embH (Matrix.of fun i k => X.c0E * w i k) ∈ X.LZ X.g := by
  refine ⟨Matrix.of fun i k => X.c0E * w i k, fun i k => ?_, fun i k => ⟨w i k, hwi i k, rfl⟩, rfl⟩
  show cc (X.c0E * w i k) = X.c0E * w k i
  have hm : cc (X.c0E * w i k) = cc X.c0E * cc (w i k) := map_mul (IsCMField.complexConj E) _ _
  rw [hm, X.cc_c0E, hwh i k]

theorem pairR_of (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (w : Fin 2 → Fin 2 → E) :
    X.pairR χ (X.embH (Matrix.of fun i k => X.c0E * w i k)) =
      (((X.g * dEnat E : ℕ) : ℝ) / 2) *
        (∑ τ : X.Ψ, ∑ i, ∑ k, χ τ i k * τ.1 (w i k)).re := by
  unfold Data.pairR Data.embH
  simp only [Matrix.of_apply, map_mul, tau_c0E]
  rw [← Complex.re_ofReal_mul]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem freq_entry (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hf : X.IsFreqZ X.g χ) (z : X.Ψ → ℂ)
    (w : 𝓞 E → Fin 2 → Fin 2 → E) (hwi : ∀ γ i k, IsIntegral ℤ (w γ i k))
    (hwh : ∀ γ i k, cc (w γ i k) = w γ k i)
    (hterm : ∀ γ : 𝓞 E, (∑ τ : X.Ψ, ∑ i, ∑ k, χ τ i k * τ.1 (w γ i k)).re =
      2 * (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((X.g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
  refine X.exists_emb_int z X.g X.g_pos fun γ => ?_
  obtain ⟨k, hk⟩ := hf _ (X.mem_LZ_of (w γ) (hwi γ) (hwh γ))
  rw [X.pairR_of, hterm γ] at hk
  refine ⟨k, ?_⟩
  rw [← hk]
  unfold dEnat
  push_cast
  ring

theorem freq_to_beta (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hχ : IsHermFam χ) (hf : X.IsFreqZ X.g χ) :
    ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧ χ = X.embH β ∧
      ∀ i k, IsIntegral ℤ (((X.g * dEnat E ^ 2 : ℕ) : E) * β i k) := by
  have hreal : ∀ τ i, (χ τ i i).im = 0 := fun τ i => by
    have := congrArg Complex.im (hχ τ i i)
    simp only [Complex.conj_im] at this
    linarith
  have hcc_int : ∀ γ : 𝓞 E, IsIntegral ℤ (cc (γ : E)) := fun γ => isIntegral_cc γ.isIntegral_coe

  obtain ⟨ω01, hω01, hi01⟩ := X.freq_entry χ hf (fun τ => χ τ 0 1)
    (fun γ => ![![0, (γ : E)], ![cc (γ : E), 0]])
    (fun γ i k => by fin_cases i <;> fin_cases k <;> simp [isIntegral_zero, γ.isIntegral_coe, hcc_int])
    (fun γ i k => by fin_cases i <;> fin_cases k <;> simp [cc_cc, cc_zero])
    (fun γ => by
      rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_zero, mul_zero, zero_add, add_zero, emb_cc]
      rw [hχ τ 0 1]
      simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring)

  have hdiag : ∀ j : Fin 2, ∃ ω : E, (∀ τ : X.Ψ, χ τ j j = τ.1 ω) ∧
      IsIntegral ℤ (((X.g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
    intro j
    refine X.freq_entry χ hf (fun τ => χ τ j j)
      (fun γ i k => if i = j ∧ k = j then (γ : E) + cc (γ : E) else 0)
      (fun γ i k => by split_ifs; exact γ.isIntegral_coe.add (hcc_int γ); exact isIntegral_zero)
      (fun γ i k => by
        by_cases h : i = j ∧ k = j
        · rw [if_pos h, if_pos ⟨h.2, h.1⟩, show cc ((γ : E) + cc (γ : E)) = cc (γ : E) + cc (cc (γ : E)) from
            map_add (IsCMField.complexConj E) _ _, cc_cc, add_comm]
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), cc_zero])
      (fun γ => ?_)
    rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hs : ∑ i, ∑ k, χ τ i k * τ.1 (if i = j ∧ k = j then (γ : E) + cc (γ : E) else 0) =
        χ τ j j * τ.1 ((γ : E) + cc (γ : E)) := by
      rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [hk]
      · simp
      · intro i _ hi; apply Finset.sum_eq_zero; intro k _; simp [hi]
      · simp
    rw [hs, map_add, emb_cc]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, hreal]
    ring
  obtain ⟨ω00, hω00, hi00⟩ := hdiag 0
  obtain ⟨ω11, hω11, hi11⟩ := hdiag 1
  obtain ⟨τ0⟩ := X.nonempty_Psi
  have hcc_diag : ∀ (ω : E) (j : Fin 2), (∀ τ : X.Ψ, χ τ j j = τ.1 ω) → cc ω = ω := by
    intro ω j hω
    apply τ0.1.injective
    rw [emb_cc, ← hω τ0, ← hχ τ0 j j]
  refine ⟨!![ω00, ω01; cc ω01, ω11], fun i k => ?_, ?_, fun i k => ?_⟩
  · fin_cases i <;> fin_cases k <;> simp [cc_cc, hcc_diag ω00 0 hω00, hcc_diag ω11 1 hω11]
  · funext τ i k
    fin_cases i <;> fin_cases k
    · simp [Data.embH, hω00 τ]
    · simp [Data.embH, hω01 τ]
    · simp only [Data.embH]
      simp [hχ τ 0 1, hω01 τ, emb_cc]
    · simp [Data.embH, hω11 τ]
  · unfold dEnat
    fin_cases i <;> fin_cases k
    · simpa using hi00
    · simpa using hi01
    · have := isIntegral_cc hi01
      simpa [cc_mul, cc] using this
    · simpa using hi11

end DataX

end ReciprocityTheory.ChartRestriction.G.FD
