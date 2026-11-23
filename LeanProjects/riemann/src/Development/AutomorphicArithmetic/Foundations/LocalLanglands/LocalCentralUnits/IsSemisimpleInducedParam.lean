import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.Zero.LLC.InducedExistence

private def per (n : ℕ) (b : ℂ) : Submodule ℂ (ℤ → ℂ) where
  carrier := {f | ∀ j, f (j + n) = b * f j}
  add_mem' := fun {f g} hf hg j => by simp only [Pi.add_apply, hf j, hg j]; ring
  zero_mem' := fun j => by simp
  smul_mem' := fun c f hf j => by simp only [Pi.smul_apply, hf j, smul_eq_mul]; ring

private theorem per_add_mul {n : ℕ} {b : ℂ} (hb : b ≠ 0) {f : ℤ → ℂ} (hf : f ∈ per n b) (m j : ℤ) :
    f (j + m * n) = b ^ m * f j := by
  induction m using Int.induction_on generalizing j with
  | zero => simp
  | succ m ih =>
    have := hf (j + m * n)
    rw [ih] at this
    rw [show j + ((m : ℤ) + 1) * n = j + m * n + n by ring, this, zpow_add_one₀ hb]
    ring
  | pred m ih =>
    have h1 := hf (j + (-(m : ℤ) - 1) * n)
    rw [show j + (-(m : ℤ) - 1) * n + n = j + (-(m : ℤ)) * n by ring, ih] at h1
    rw [zpow_sub_one₀ hb]
    field_simp
    rw [h1]
    field_simp

private def perExt (n : ℕ) (hn : 0 < n) (b : ℂ) (g : Fin n → ℂ) (j : ℤ) : ℂ :=
  b ^ (j / n) * g ⟨(j % n).toNat, by
    have h1 : 0 ≤ j % n := Int.emod_nonneg _ (by omega)
    have h2 : j % n < n := Int.emod_lt_of_pos _ (by omega)
    omega⟩

private theorem perExt_mem {n : ℕ} (hn : 0 < n) {b : ℂ} (hb : b ≠ 0) (g : Fin n → ℂ) :
    perExt n hn b g ∈ per n b := fun j => by
  have hn' : (n : ℤ) ≠ 0 := by omega
  have h1 : (j + n) / n = j / n + 1 := Int.add_ediv_of_dvd_right (dvd_refl _) |>.trans (by rw [Int.ediv_self hn'])
  have h2 : (j + n) % n = j % n := Int.add_emod_right _ _
  simp only [perExt, h1, h2, zpow_add_one₀ hb]
  ring

private theorem perExt_coe {n : ℕ} (hn : 0 < n) (b : ℂ) (g : Fin n → ℂ) (i : Fin n) :
    perExt n hn b g (i : ℕ) = g i := by
  have h1 : ((i : ℕ) : ℤ) / n = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h2 : ((i : ℕ) : ℤ) % n = (i : ℕ) := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [perExt, h1, h2, zpow_zero, one_mul, Int.toNat_natCast]

private def perEquiv (n : ℕ) (hn : 0 < n) {b : ℂ} (hb : b ≠ 0) : per n b ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun f i := f.1 (i : ℕ)
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun g := ⟨perExt n hn b g, perExt_mem hn hb g⟩
  left_inv f := Subtype.ext (funext fun j => by
    have hn' : (n : ℤ) ≠ 0 := by omega
    have h0 : 0 ≤ j % n := Int.emod_nonneg _ hn'
    have h1 : (((j % n).toNat : ℕ) : ℤ) = j % n := Int.toNat_of_nonneg h0
    have h2 := per_add_mul hb f.2 (j / n) (j % n)
    have h3 : j % n + j / n * n = j := by
      have := Int.emod_add_mul_ediv j n
      linarith
    rw [h3] at h2
    simp only [perExt]
    rw [h2, h1])
  right_inv g := funext fun i => perExt_coe hn b g i

@[simp] private theorem perEquiv_apply {n : ℕ} {hn : 0 < n} {b : ℂ} {hb : b ≠ 0} (f : per n b) (i : Fin n) :
    perEquiv n hn hb f i = f.1 (i : ℕ) := rfl

private theorem perEquiv_symm {n : ℕ} {hn : 0 < n} {b : ℂ} {hb : b ≠ 0} (g : Fin n → ℂ) (i : Fin n) :
    ((perEquiv n hn hb).symm g).1 (i : ℕ) = g i := perExt_coe hn b g i

private theorem isSemisimple_of_pow_eq {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) {N : ℕ}
    (hN : N ≠ 0) {s : ℂ} (hs : s ≠ 0) (h : T ^ N = s • 1) : T.IsSemisimple := by
  have hsep : (X ^ N - C s : ℂ[X]).Separable := separable_X_pow_sub_C s (by exact_mod_cast hN) hs
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree ?_
  simp [h, Algebra.algebraMap_eq_smul_one]

private theorem single_mem {ι G : Type*} [Fintype ι] [DecidableEq ι] (χ : ι → G → ℂ)
    (hχ : ∀ i i', i ≠ i' → ∃ g, χ i g ≠ χ i' g) (U : Submodule ℂ (ι → ℂ))
    (hU : ∀ g, ∀ u ∈ U, (fun i => χ i g * u i) ∈ U) (i : ι) :
    ∀ (s : ℕ) (u : ι → ℂ), u ∈ U → u i ≠ 0 → (Finset.univ.filter fun k => u k ≠ 0).card = s →
      Pi.single i 1 ∈ U := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro u hu hi hs
    by_cases hex : ∃ i', i' ≠ i ∧ u i' ≠ 0
    · obtain ⟨i', hne, hi'⟩ := hex
      obtain ⟨g, hg⟩ := hχ i i' hne.symm
      let u' : ι → ℂ := (fun k => χ k g * u k) - χ i' g • u
      have hu' : u' ∈ U := U.sub_mem (hU g u hu) (U.smul_mem _ hu)
      have h1 : u' i ≠ 0 := by
        have : u' i = (χ i g - χ i' g) * u i := by simp [u']; ring
        rw [this]
        exact mul_ne_zero (sub_ne_zero.2 hg) hi
      have h2 : u' i' = 0 := by simp [u']
      have hlt : (Finset.univ.filter fun k => u' k ≠ 0).card < s := by
        rw [← hs]
        refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          intro h0
          exact hk (by simp [u', h0])
        · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ i', hi'⟩)
          exact (Finset.mem_filter.1 this).2 h2
      exact ih _ hlt u' hu' h1 rfl
    · have h4 : (u i)⁻¹ • u = Pi.single i 1 := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [hi]
        · have : u k = 0 := by
            by_contra h0
            exact hex ⟨k, hk, h0⟩
          simp [hk, this]
      exact h4 ▸ U.smul_mem _ hu

private theorem det_shift {n : ℕ} (hn : 0 < n) {b : ℂ} (hb : b ≠ 0) (S : Module.End ℂ (per n b))
    (hS : ∀ f j, (S f).1 j = f.1 (j + 1)) : LinearMap.det S = (-1) ^ (n - 1) * b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let e := perEquiv (m + 1) hn hb
  let wt : Fin (m + 1) → ℂ := fun k => if k = 0 then b else 1
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := (Matrix.diagonal wt).submatrix (finRotate (m + 1)) id
  have hM : e.conj S = Matrix.toLin' M := by
    refine LinearMap.ext fun g => funext fun i => ?_
    have h1 : (e.conj S) g i = (e.symm g).1 ((i : ℕ) + 1) := by
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      show (S (e.symm g)).1 ((i : ℕ) : ℤ) = _
      rw [hS]
    have h2 : (Matrix.toLin' M) g i = wt (finRotate (m + 1) i) * g (finRotate (m + 1) i) := by
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, M, Matrix.diagonal_apply]
    rw [h1, h2]
    by_cases hi : (i : ℕ) = m
    · have hl : i = Fin.last m := Fin.ext hi
      have h3 := (e.symm g).2 0
      have h4 : (e.symm g).1 0 = g 0 := by
        simpa using perEquiv_symm (hn := hn) (hb := hb) g 0
      rw [hl, finRotate_last]
      simp only [wt, if_true]
      rw [← h4, ← h3]
      congr 1
      simp
    · have hlt : (i : ℕ) < m := by omega
      have h5 : finRotate (m + 1) i = ⟨(i : ℕ) + 1, by omega⟩ := finRotate_of_lt hlt
      have h6 : ((i : ℕ) : ℤ) + 1 = (((⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) : ℕ) : ℤ) := by simp
      have h7 : wt ⟨(i : ℕ) + 1, by omega⟩ = 1 := if_neg fun h0 => by
        have := congrArg Fin.val h0
        simp at this
      rw [h5, h6, perEquiv_symm, h7, one_mul]
  have hdet : LinearMap.det S = LinearMap.det (e.conj S) := (LinearMap.det_conj S e).symm
  rw [hdet, hM, LinearMap.det_toLin', Matrix.det_permute, Matrix.det_diagonal, sign_finRotate]
  simp [wt, Finset.prod_ite_eq']

section Weil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private def cj (φ : Weil h) (m : ℤ) (t : Ine (F := E) A) : Ine (F := E) A :=
  ⟨((φ ^ m * ineIncl h t * (φ ^ m)⁻¹ : Weil h) : G E Ω), deg_eq_zero_iff.mp (by simp)⟩

private theorem ineIncl_cj (φ : Weil h) (m : ℤ) (t : Ine (F := E) A) :
    ineIncl h (cj φ m t) = φ ^ m * ineIncl h t * (φ ^ m)⁻¹ := rfl

private theorem continuous_cj (φ : Weil h) (m : ℤ) : Continuous (cj φ m) := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun t : Ine (F := E) A => ((φ ^ m : Weil h) : G E Ω) * (t : G E Ω) * (((φ ^ m : Weil h) : G E Ω))⁻¹
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

private theorem eta_cj {φ : Weil h} {η : ℤ → (Ine (F := E) A →* ℂˣ)}
    (h1 : ∀ (j : ℤ) (t t' : Ine (F := E) A), ineIncl h t' = φ * ineIncl h t * φ⁻¹ → η j t' = η (j + 1) t)
    (m j : ℤ) (t : Ine (F := E) A) : η (j + m) t = η j (cj φ m t) := by
  induction m using Int.induction_on generalizing j t with
  | zero =>
    have : cj φ 0 t = t := Subtype.ext (by simp [cj])
    simp [this]
  | succ m ih =>
    have e1 : j + ((m : ℤ) + 1) = (j + 1) + m := by ring
    rw [e1, ih (j + 1) t]
    refine (h1 j (cj φ m t) (cj φ (m + 1) t) ?_).symm
    rw [ineIncl_cj, ineIncl_cj]
    group
  | pred m ih =>
    have e1 : j + (-(m : ℤ) - 1) = (j - 1) + (-(m : ℤ)) := by ring
    rw [e1, ih (j - 1) t]
    have := h1 (j - 1) (cj φ (-(m : ℤ) - 1) t) (cj φ (-(m : ℤ)) t) (by
      rw [ineIncl_cj, ineIncl_cj]
      group)
    rw [this, sub_add_cancel]

private def tau {φ : Weil h} (hφ : deg φ = 1) (σ : Weil h) : Ine (F := E) A :=
  ⟨(((φ ^ deg σ)⁻¹ * σ : Weil h) : G E Ω), deg_eq_zero_iff.mp (by simp [hφ])⟩

private theorem tau_mul {φ : Weil h} (hφ : deg φ = 1) (σ σ' : Weil h) :
    tau hφ (σ * σ') = cj φ (-deg σ') (tau hφ σ) * tau hφ σ' := by
  have key : (φ ^ deg (σ * σ'))⁻¹ * (σ * σ') =
      (φ ^ (-deg σ') * ((φ ^ deg σ)⁻¹ * σ) * (φ ^ (-deg σ'))⁻¹) * ((φ ^ deg σ')⁻¹ * σ') := by
    rw [deg_mul, zpow_add]
    group
  exact Subtype.ext (congrArg (Subtype.val : Weil h → G E Ω) key)

private theorem tau_ineIncl {φ : Weil h} (hφ : deg φ = 1) (t : Ine (F := E) A) : tau hφ (ineIncl h t) = t :=
  Subtype.ext (by simp [tau])

private theorem tau_zpow {φ : Weil h} (hφ : deg φ = 1) (m : ℤ) : tau hφ (φ ^ m) = 1 :=
  Subtype.ext (by simp [tau, hφ])

private def act {φ : Weil h} (hφ : deg φ = 1) (η : ℤ → (Ine (F := E) A →* ℂˣ)) (σ : Weil h) :
    Module.End ℂ (ℤ → ℂ) where
  toFun f j := ((η (j + deg σ) (tau hφ σ) : ℂˣ) : ℂ) * f (j + deg σ)
  map_add' f g := funext fun j => by simp [mul_add]
  map_smul' c f := funext fun j => by simp; ring

private theorem act_mem {φ : Weil h} (hφ : deg φ = 1) {η : ℤ → (Ine (F := E) A →* ℂˣ)} {n : ℕ} {b : ℂ}
    (h2 : ∀ j j' : ℤ, η j = η j' ↔ (n : ℤ) ∣ j - j') (σ : Weil h) {f : ℤ → ℂ} (hf : f ∈ per n b) :
    act hφ η σ f ∈ per n b := fun j => by
  have e1 : η (j + n + deg σ) = η (j + deg σ) := (h2 _ _).2 ⟨1, by ring⟩
  show ((η (j + n + deg σ) (tau hφ σ) : ℂˣ) : ℂ) * f (j + n + deg σ) =
    b * (((η (j + deg σ) (tau hφ σ) : ℂˣ) : ℂ) * f (j + deg σ))
  rw [e1, show j + n + deg σ = j + deg σ + n by ring, hf]
  ring

private def rho0 {φ : Weil h} (hφ : deg φ = 1) {η : ℤ → (Ine (F := E) A →* ℂˣ)} {n : ℕ} (b : ℂ)
    (h1 : ∀ (j : ℤ) (t t' : Ine (F := E) A), ineIncl h t' = φ * ineIncl h t * φ⁻¹ → η j t' = η (j + 1) t)
    (h2 : ∀ j j' : ℤ, η j = η j' ↔ (n : ℤ) ∣ j - j') : Representation ℂ (Weil h) (per n b) where
  toFun σ := (act hφ η σ).restrict fun f hf => act_mem hφ h2 σ hf
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun j => by
    show ((η (j + deg (1 : Weil h)) (tau hφ 1) : ℂˣ) : ℂ) * f.1 (j + deg (1 : Weil h)) = f.1 j
    have : tau hφ (1 : Weil h) = 1 := by simpa using tau_zpow hφ 0
    rw [this, deg_one]
    simp)
  map_mul' σ σ' := LinearMap.ext fun f => Subtype.ext (funext fun j => by
    show ((η (j + deg (σ * σ')) (tau hφ (σ * σ')) : ℂˣ) : ℂ) * f.1 (j + deg (σ * σ')) =
      ((η (j + deg σ) (tau hφ σ) : ℂˣ) : ℂ) *
        (((η (j + deg σ + deg σ') (tau hφ σ') : ℂˣ) : ℂ) * f.1 (j + deg σ + deg σ'))
    have e1 := eta_cj h1 (-deg σ') (j + deg σ + deg σ') (tau hφ σ)
    rw [show j + deg σ + deg σ' + -deg σ' = j + deg σ by ring] at e1
    rw [tau_mul, map_mul, deg_mul, ← add_assoc, ← e1, Units.val_mul]
    ring)

section Rho

variable {φ : Weil h} (hφ : deg φ = 1) {η : ℤ → (Ine (F := E) A →* ℂˣ)} {n : ℕ} {b : ℂ}
  (h1 : ∀ (j : ℤ) (t t' : Ine (F := E) A), ineIncl h t' = φ * ineIncl h t * φ⁻¹ → η j t' = η (j + 1) t)
  (h2 : ∀ j j' : ℤ, η j = η j' ↔ (n : ℤ) ∣ j - j')

private theorem rho_ine (t : Ine (F := E) A) (f : per n b) (j : ℤ) :
    (rho0 hφ b h1 h2 (ineIncl h t) f).1 j = ((η j t : ℂˣ) : ℂ) * f.1 j := by
  show ((η (j + deg (ineIncl h t)) (tau hφ (ineIncl h t)) : ℂˣ) : ℂ) * f.1 (j + deg (ineIncl h t)) = _
  rw [tau_ineIncl, deg_ineIncl, add_zero]

private theorem rho_zpow (m : ℤ) (f : per n b) (j : ℤ) :
    (rho0 hφ b h1 h2 (φ ^ m) f).1 j = f.1 (j + m) := by
  show ((η (j + deg (φ ^ m)) (tau hφ (φ ^ m)) : ℂˣ) : ℂ) * f.1 (j + deg (φ ^ m)) = _
  have : deg (φ ^ m) = m := by simp [hφ]
  rw [tau_zpow, this]
  simp

include h1 h2 in
private theorem isSmooth_inducedParam (hn : 0 < n) (h0 : IsOpen ((η 0).ker : Set (Ine (F := E) A))) :
    IsSmooth (rho0 hφ b h1 h2) := by
  have hk : ∀ j : ℤ, IsOpen {t : Ine (F := E) A | η j t = 1} := fun j => by
    have : {t : Ine (F := E) A | η j t = 1} = cj φ j ⁻¹' ((η 0).ker : Set (Ine (F := E) A)) := by
      ext t
      have e1 := eta_cj h1 j 0 t
      rw [zero_add] at e1
      simp [e1, MonoidHom.mem_ker]
    rw [this]
    exact h0.preimage (continuous_cj φ j)
  refine IsSmooth.of_open (U := ⋂ i : Fin n, {t : Ine (F := E) A | η ((i : ℕ) : ℤ) t = 1})
    (isOpen_iInter_of_finite fun i => hk _) (by simp) fun t ht => ?_
  refine LinearMap.ext fun f => Subtype.ext (funext fun j => ?_)
  rw [rho_ine]
  have hn' : (n : ℤ) ≠ 0 := by omega
  have e0 : 0 ≤ j % n := Int.emod_nonneg _ hn'
  have e1 : j % n < n := Int.emod_lt_of_pos _ (by omega)
  have e2 : (((j % n).toNat : ℕ) : ℤ) = j % n := Int.toNat_of_nonneg e0
  let i : Fin n := ⟨(j % n).toNat, by omega⟩
  have e3 : η j = η (((i : ℕ)) : ℤ) := (h2 _ _).2 (by
    show (n : ℤ) ∣ j - (((j % n).toNat : ℕ) : ℤ)
    rw [e2]
    exact Int.dvd_self_sub_emod)
  have e4 : η (((i : ℕ)) : ℤ) t = 1 := Set.mem_iInter.1 ht i
  rw [e3, e4]
  simp

include h1 h2 in
private theorem isSemisimple_inducedParam (hn : 0 < n) (hb : b ≠ 0) (hs : IsSmooth (rho0 hφ b h1 h2)) (σ : Weil h) :
    Module.End.IsSemisimple (rho0 hφ b h1 h2 σ) := by
  have := compactSpace_Ine (E := E) A
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ (σ ^ n)
  have hfin : Finite (Ine (F := E) A ⧸ ((rho0 hφ b h1 h2).comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hs
  obtain ⟨m, hm0, -, hm⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (H := ((rho0 hφ b h1 h2).comp (ineIncl h)).ker) Subgroup.index_ne_zero_of_finite τ
  have e1 : rho0 hφ b h1 h2 (φ ^ deg (σ ^ n)) = (b ^ deg σ) • 1 :=
    LinearMap.ext fun f => Subtype.ext (funext fun j => by
      rw [rho_zpow, deg_pow, mul_comm]
      simpa using per_add_mul hb f.2 (deg σ) j)
  have e2 : rho0 hφ b h1 h2 (ineIncl h τ) ^ m = 1 := by
    rw [← map_pow, ← map_pow]
    exact hm
  have e3 : rho0 hφ b h1 h2 σ ^ (n * m) = ((b ^ deg σ) ^ m) • 1 := by
    rw [pow_mul, ← map_pow, hτ, map_mul, e1, smul_mul_assoc, one_mul, _root_.smul_pow, e2]
  exact isSemisimple_of_pow_eq _ (by positivity) (pow_ne_zero _ (zpow_ne_zero _ hb)) e3

end Rho

end Weil

end UpperTheory.Zero.LLC.InducedExistence

open UpperTheory.Zero.LLC.InducedExistence in
theorem UpperTheory.Zero.LLC.indEx :
    UpperTheory.Zero.LLC.IndEx := by
  intro E Ω _ _ _ _ _ A w h φ hφ n hn η h0 h1 h2 c hc
  classical
  have hb : ((-1 : ℂ) ^ (n - 1) * c) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hc
  obtain ⟨b, hbdef⟩ : ∃ b, b = (-1 : ℂ) ^ (n - 1) * c := ⟨_, rfl⟩
  rw [← hbdef] at hb
  let e := perEquiv n hn hb
  haveI : FiniteDimensional ℂ (per n b) := Module.Finite.equiv e.symm
  have hsm := isSmooth_inducedParam (b := b) hφ h1 h2 hn h0
  let a0 : WDRep h (per n b) :=
    { ρ := rho0 hφ b h1 h2
      N := 0
      smooth := hsm
      semisimple := isSemisimple_inducedParam hφ h1 h2 hn hb hsm
      nilpotent := IsNilpotent.zero
      comm := fun σ => by simp }
  let a := a0.transport e
  have hV : WD.mk a = WD.mk a0 := (WD.sound (a0.iso_transport e)).symm
  have hρ : ∀ σ g, a.ρ σ g = e (a0.ρ σ (e.symm g)) := fun σ g => rfl
  have hact : ∀ (t : Ine (F := E) A) (g : Fin n → ℂ) (i : Fin n),
      a.ρ (ineIncl h t) g i = ((η ((i : ℕ) : ℤ) t : ℂˣ) : ℂ) * g i := fun t g i => by
    rw [hρ]
    show (rho0 hφ b h1 h2 (ineIncl h t) (e.symm g)).1 ((i : ℕ) : ℤ) = _
    rw [rho_ine, perEquiv_symm]
  have hsh : ∀ (m : ℤ) (g : Fin n → ℂ) (i : Fin n),
      a.ρ (φ ^ m) g i = (e.symm g).1 (((i : ℕ) : ℤ) + m) := fun m g i => by
    rw [hρ]
    show (rho0 hφ b h1 h2 (φ ^ m) (e.symm g)).1 ((i : ℕ) : ℤ) = _
    rw [rho_zpow]
  refine ⟨WD.mk a, ⟨n, a, rfl, ?_⟩, by simp, ?_, fun t => ?_, fun hw => ⟨n, a, rfl, fun σ hσ => ?_⟩⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have : Nontrivial (Subrepresentation a.ρ) := ⟨⊥, ⊤, fun h' => by
      have := congrArg Subrepresentation.toSubmodule h'
      exact bot_ne_top (α := Submodule ℂ (Fin n → ℂ)) this⟩
    refine ⟨fun U => ?_⟩
    by_cases hU : U.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
    · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.1 hu0
      let χ : Fin n → Ine (F := E) A → ℂ := fun i t => ((η ((i : ℕ) : ℤ) t : ℂˣ) : ℂ)
      have hχ : ∀ i i', i ≠ i' → ∃ t, χ i t ≠ χ i' t := fun i i' hne => by
        by_contra hall
        push_neg at hall
        have e1 : η ((i : ℕ) : ℤ) = η ((i' : ℕ) : ℤ) := MonoidHom.ext fun t => Units.ext (hall t)
        have e2 := (h2 _ _).1 e1
        have e3 := Int.eq_zero_of_abs_lt_dvd e2 (abs_lt.2 ⟨by omega, by omega⟩)
        exact hne (Fin.ext (by omega))
      have hst : ∀ t, ∀ u ∈ U.toSubmodule, (fun i => χ i t * u i) ∈ U.toSubmodule := fun t u hu => by
        have e1 := U.apply_mem_toSubmodule (ineIncl h t) hu
        have e2 : a.ρ (ineIncl h t) u = fun i => χ i t * u i := funext fun i => hact t u i
        rwa [e2] at e1
      have hk : ∀ k : Fin n, (Pi.single k 1 : Fin n → ℂ) ∈ U.toSubmodule := fun k => by
        have hv := U.apply_mem_toSubmodule (φ ^ (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ))) hu
        refine single_mem χ hχ U.toSubmodule hst k _ _ hv ?_ rfl
        rw [hsh, add_sub_cancel, perEquiv_symm]
        exact hi
      refine eq_top_iff.2 fun g _ => ?_
      have e1 : g = ∑ k, g k • (Pi.single k 1 : Fin n → ℂ) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]
      rw [e1]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hk k)
  · have hS : ∀ (f : per n b) (j : ℤ), (a0.ρ φ f).1 j = f.1 (j + 1) := fun f j => by
      have := rho_zpow hφ h1 h2 1 f j
      rwa [zpow_one] at this
    rw [hV, WD.eig_mk, ← Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _),
      det_shift hn hb _ hS, hbdef, ← mul_assoc, ← mul_pow]
    simp
  · have e1 : e.conj (a0.ρ (ineIncl h t)) = diagEnd fun i : Fin n => ((η ((i : ℕ) : ℤ) t : ℂˣ) : ℂ) :=
      LinearMap.ext fun g => funext fun i => hact t g i
    rw [WD.inePol_of_mem_Ine _ t.2, hV, WD.charPol_mk]
    show (a0.ρ (ineIncl h t)).charpoly = _
    rw [← e.charpoly_conj, e1, charpoly_diagEnd]
    exact Fin.prod_univ_eq_prod_range (fun k : ℕ => X - C ((η (k : ℤ) t : ℂˣ) : ℂ)) n
  · let t : Ine (F := E) A := ⟨σ, hσ.1⟩
    have e0 : σ = ineIncl h t := Subtype.ext rfl
    have e1 : a0.ρ σ = 1 := by
      rw [e0]
      refine LinearMap.ext fun f => Subtype.ext (funext fun j => ?_)
      show (rho0 hφ b h1 h2 (ineIncl h t) f).1 j = f.1 j
      rw [rho_ine, hw j t hσ]
      simp
    exact (a0.iso_transport e).ρ_eq_one e1

end
