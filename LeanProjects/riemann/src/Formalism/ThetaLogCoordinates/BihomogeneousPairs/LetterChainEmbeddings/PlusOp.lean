import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeEqualHolds

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality

section plusop
variable {p : ℕ} [Fact p.Prime]

noncomputable abbrev po_d {σ : Type} (v : σ) : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] :=
  (pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap

theorem po_Fsum {σ ι : Type} [DecidableEq ι]
    (Dc : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (hcomm : ∀ a b, Commute (Dc a) (Dc b))
    (Λ : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hdiv : ∀ a k l, ∀ x ∈ Λ l, ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (Dc a ^ k) x) ∈ Λ (l + k))
    (L n : ℕ) (hn : Nat.log p n ≤ L) (S : Finset ι) :
    ∀ j ≤ n, ∀ l, ∀ x ∈ Λ l,
      (((p : ℚ_[p]) ^ (S.card * L) * ((j.factorial : ℚ_[p]) ^ 2)⁻¹) • ((∑ c ∈ S, Dc c) ^ j) x) ∈ Λ (l + j) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  induction S using Finset.induction_on with
  | empty =>
    intro j _ l x hx
    rcases j with _ | j
    · simpa using hx
    · simp
  | insert a S ha ih =>
    intro j hj l x hx
    have hc : Commute (Dc a) (∑ c ∈ S, Dc c) := Commute.sum_right _ _ _ (fun c _ => hcomm a c)
    rw [Finset.sum_insert ha, hc.add_pow j, Finset.card_insert_of_notMem ha,
      LinearMap.sum_apply, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hkj : k ≤ j := by rw [Finset.mem_range] at hk; omega
    have hfac := Nat.choose_mul_factorial_mul_factorial hkj
    have hne : ((j.choose k : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkj).ne'
    have hk0 : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    have hjk0 : (((j - k).factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have key : (((j.factorial : ℚ_[p]) ^ 2))⁻¹ * ((j.choose k : ℕ) : ℚ_[p]) =
        (((j.choose k : ℕ) : ℚ_[p]))⁻¹ * ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ *
          ((((j - k).factorial : ℚ_[p]) ^ 2))⁻¹) := by
      rw [← hfac]
      push_cast
      field_simp
    have eq : ((p : ℚ_[p]) ^ ((S.card + 1) * L) * ((j.factorial : ℚ_[p]) ^ 2)⁻¹) •
        (Dc a ^ k * (∑ c ∈ S, Dc c) ^ (j - k) *
          ((j.choose k : ℕ) : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])) x =
        ((p : ℚ_[p]) ^ L * (((j.choose k : ℕ) : ℚ_[p]))⁻¹) • ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (Dc a ^ k)
          (((p : ℚ_[p]) ^ (S.card * L) * (((j - k).factorial : ℚ_[p]) ^ 2)⁻¹) •
            ((∑ c ∈ S, Dc c) ^ (j - k)) x)) := by
      simp only [Module.End.mul_apply, Module.End.natCast_apply,
        map_smul, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul]
      congr 1
      rw [mul_assoc, key, add_mul, one_mul, pow_add]
      ring
    rw [eq]
    have h1 := ih (j - k) (by omega) l x hx
    have h2 := hdiv a k _ _ h1
    rw [show l + (j - k) + k = l + j by omega] at h2
    refine smul_mem_of_norm _ ?_ h2
    rw [norm_mul, norm_pow, Padic.norm_p]
    have h3 : ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ L :=
      (norm_choose_inv_le j k hkj).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hn))
    calc ((p : ℝ)⁻¹) ^ L * ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ ((p : ℝ)⁻¹) ^ L * (p : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]

theorem po_pow_right {σ : Type} (v : σ) {a : MvPolynomial σ ℚ_[p]} (ha : pderiv v a = 0)
    (g : MvPolynomial σ ℚ_[p]) (k : ℕ) : (po_d v ^ k) (a * g) = a * (po_d v ^ k) g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    show pderiv v (a * _) = a * pderiv v _
    rw [pderiv_mul, ha, zero_mul, zero_add]

theorem po_pow_left {σ τ : Type} (f : τ → σ) (hf : Function.Injective f) (u : τ)
    (y : MvPolynomial τ ℚ_[p]) {g : MvPolynomial σ ℚ_[p]} (hg : pderiv (f u) g = 0) (k : ℕ) :
    (po_d (f u) ^ k) (rename f y * g) = rename f ((po_d u ^ k) y) * g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    show pderiv (f u) (_ * g) = rename f (pderiv u _) * g
    rw [pderiv_mul, hg, mul_zero, add_zero, pderiv_rename hf]

theorem po_int {σ : Type} (v : σ) (k : ℕ) {y : MvPolynomial σ ℚ_[p]} (hy : y ∈ IntPol p σ) :
    ((k.factorial : ℚ_[p])⁻¹ • (po_d v ^ k) y) ∈ IntPol p σ := by
  rw [intPol_iff_bnd] at hy ⊢
  have h := contr_divDeriv (p := p) v k 1 zero_le_one y hy
  intro m
  simpa using h m

variable {N r : ℕ} [NeZero r] {D : BlockData N}

theorem pderiv_xi_rename_chainEmb_eq_zero (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (c : Fin r) :
    pderiv (xiVar N r D.T.t c) (rename (chainEmb N r D.T.t) y) = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (vars_rename _ _ h)
  exact xi_notin (D := D) c ⟨a, ha⟩

omit [NeZero r] in
theorem po_xi_inj {t : ℕ} : Function.Injective (xiVar N r t) := by
  intro a b h
  simpa [xiVar] using h

noncomputable abbrev po_R (p : ℕ) [Fact p.Prime] (N r t b : ℕ) : Submodule ℚ_[p] (MvPolynomial (BVar N r t) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p]
    {m | (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b}

omit [NeZero r] in
theorem po_R_step {t b : ℕ} (c : Fin r) {g : MvPolynomial (BVar N r t) ℚ_[p]} (hg : g ∈ po_R p N r t b) :
    pderiv (xiVar N r t c) g ∈ po_R p N r t (b - 1) := by
  classical
  rw [mem_restrictSupport_iff] at hg ⊢
  intro m hm
  have hm' : m + Finsupp.single (xiVar N r t c) 1 ∈ g.support := by
    rw [Finset.mem_coe, mem_support_iff, coeff_pderiv] at hm
    rw [mem_support_iff]
    exact left_ne_zero_of_mul hm
  obtain ⟨h1, h2⟩ := hg (Finset.mem_coe.mpr hm')
  refine ⟨fun v hv => h1 v ?_, ?_⟩
  · rw [Finsupp.mem_support_iff] at hv ⊢
    rw [Finsupp.add_apply]
    omega
  · simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h2
    rw [Finset.sum_eq_single c (fun d _ hd => Finsupp.single_eq_of_ne (fun h => hd (po_xi_inj h)))
      (fun h => absurd (Finset.mem_univ c) h), Finsupp.single_eq_same] at h2
    omega

omit [NeZero r] in
theorem po_R_pow {t : ℕ} (c : Fin r) (k : ℕ) : ∀ (b : ℕ) {g : MvPolynomial (BVar N r t) ℚ_[p]},
    g ∈ po_R p N r t b → (po_d (xiVar N r t c) ^ k) g ∈ po_R p N r t (b - k) := by
  induction k with
  | zero => intro b g hg; simpa using hg
  | succ k ih =>
    intro b g hg
    rw [pow_succ', Module.End.mul_apply, ← Nat.sub_sub]
    exact po_R_step c (ih b hg)

omit [NeZero r] in
theorem po_xi_div {t b : ℕ} (c : Fin r) (k : ℕ) {g : MvPolynomial (BVar N r t) ℚ_[p]}
    (hg : g ∈ XiPolZ p N r t b) :
    ((k.factorial : ℚ_[p])⁻¹ • (po_d (xiVar N r t c) ^ k) g) ∈ XiPolZ p N r t (b - k) := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hg
  exact Submodule.mem_inf.mpr ⟨(po_R p N r t (b - k)).smul_mem _ (po_R_pow c k b h1), po_int _ k h2⟩

theorem po_Y_iter (hU : HypU p (r := r) D) (c : Fin r) (j : Fin D.T.t → ℕ) :
    ∀ k (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (po_d (D.uPos, c) ^ k) y ∈ Y p (r := r) (D.lettersAt j (jp + k)) D.T.J D.T.thr := by
  intro k
  induction k with
  | zero => intro jp y hy; rw [pow_zero, Module.End.one_apply, add_zero]; exact hy
  | succ k ih =>
    intro jp y hy
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact hU j (jp + k) c _ (ih jp y hy)

theorem po_coord (hU : HypU p (r := r) D) (j : Fin D.T.t → ℕ) (c : Fin r) (k jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k) x) ∈ Lat p D (r := r) j (jp + k) := by
  intro x hx
  have := span_map_mem ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
    ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k)) _ (Lat p D (r := r) j (jp + k)) ?_ x hx
  · simpa using this
  rintro v ⟨y, hy, g, hg, rfl⟩
  have hg' := po_xi_div c k hg
  have e : ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k))
      (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t) ((k.factorial : ℚ_[p])⁻¹ • (po_d (D.uPos, c) ^ k) y) *
        ((k.factorial : ℚ_[p])⁻¹ • (po_d (xiVar N r D.T.t c) ^ k) g) := by
    have h1 := po_pow_left (p := p) (chainEmb N r D.T.t) chainEmb_inj (D.uPos, c) y
      (xi_free hg' (fun d => wU_ne_xi (D := D) c d)) k
    rw [← Module.End.mul_eq_comp, (commute_pderiv _ _).mul_pow, LinearMap.smul_apply, Module.End.mul_apply,
      po_pow_right _ (pderiv_xi_rename_chainEmb_eq_zero (D := D) y c), map_smul, smul_mul_assoc, ← h1, mul_smul_comm, map_smul,
      smul_smul, sq, mul_inv]
    rfl
  rw [e, Nat.sub_sub] at *
  exact Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (po_Y_iter hU c j k jp y (yz_y hy)))
    (po_int _ k (yz_int hy)), _, hg', rfl⟩

end plusop

theorem lattice_plus_holds : LatPlus := by
  intro p _ N r _ D hB hU j jp m L hmL x hx
  classical
  have hcomm : ∀ a b : Fin r, Commute (po_d (p := p) (wU D a) ∘ₗ po_d (xiVar N r D.T.t a))
      (po_d (wU D b) ∘ₗ po_d (xiVar N r D.T.t b)) := by
    intro a b
    simp only [← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have h := po_Fsum (fun c : Fin r => po_d (p := p) (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) hcomm
    (fun l => Lat p D (r := r) j l) (fun a k l x hx => po_coord hU j a k l x hx) L m hmL Finset.univ
    m le_rfl jp x hx
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

end Formalism.InvariantFactorPaths.KP.LL
