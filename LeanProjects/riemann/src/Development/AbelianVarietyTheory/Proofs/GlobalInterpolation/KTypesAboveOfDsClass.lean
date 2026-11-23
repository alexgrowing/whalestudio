import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.LowestKTypeDetermines

variable {n : ℕ} {ε ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

theorem Kset_sub {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : g ∈ UJset ε := by
  have hg1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  show gᴴ * Jm ε * g = Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hg1, Matrix.one_mul]

theorem symm_inter (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) :
    ∀ g ∈ UJset ε, ∀ v, T.symm (τ g v) = σ g (T.symm v) := by
  intro g hg v
  apply T.injective
  rw [h g hg]; simp

theorem uEquiv_symm (h : UEquiv ε σ τ) : UEquiv ε τ σ := by
  obtain ⟨T, h⟩ := h
  exact ⟨T.symm, symm_inter T h⟩

theorem uEquiv_trans {H'' : Type} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    {υ : Matrix (Fin n) (Fin n) ℂ → (H'' →L[ℂ] H'')} (h : UEquiv ε σ τ) (h' : UEquiv ε τ υ) : UEquiv ε σ υ := by
  obtain ⟨T, h⟩ := h
  obtain ⟨T', h'⟩ := h'
  exact ⟨T.trans T', fun g hg v => by simp [h g hg, h' g hg]⟩

theorem wt_transfer (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Kset ε) σ μ v) : IsWtOn (Kset ε) τ μ (T v) := by
  intro θ hθ
  rw [← h _ (Kset_sub hθ), hv θ hθ, map_smul]

theorem ktype_transfer (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (hS : IsKTypeOf ε σ Λ S) :
    IsKTypeOf ε τ Λ (S.map (T.toLinearEquiv : H →ₗ[ℂ] H')) := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ⟨T v, ⟨v, hv, rfl⟩, by simpa using hv0, wt_transfer T h hvw⟩, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, h2 g hg x hx, h g (Kset_sub hg) x⟩
  · intro S' hle hst
    rcases h3 (S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H')) (by
        intro x hx
        obtain ⟨y, hy, e⟩ := hle hx
        have : y = x := T.injective e
        exact this ▸ hy) (by
        intro g hg x hx
        show T (σ g x) ∈ S'
        rw [h g (Kset_sub hg)]
        exact hst g hg _ hx) with e | e
    · left
      rw [eq_bot_iff]
      intro x hx
      have : T.symm x ∈ S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H') := by
        show T (T.symm x) ∈ S'
        simpa using hx
      rw [e] at this
      simpa using this
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [← e] at hx
      exact hx
  · rintro μ _ ⟨x, hx, rfl⟩ h0 hw
    have := wt_transfer T.symm (symm_inter T h) hw
    refine h5 μ x hx (by rintro rfl; simp at h0) ?_
    simpa using this

theorem exists_ktype_of_uEquiv (h : UEquiv ε σ τ) {Λ : Fin n → ℝ} (hS : ∃ S, IsKTypeOf ε σ Λ S) :
    ∃ S, IsKTypeOf ε τ Λ S := by
  obtain ⟨T, h⟩ := h
  obtain ⟨S, hS⟩ := hS
  exact ⟨_, ktype_transfer T h hS⟩

theorem submatrix_mem_Kset (s : Equiv.Perm (Fin n)) (hε : ∀ a, ε' a = ε (s a)) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Kset ε') : g.submatrix s.symm s.symm ∈ Kset ε := by
  have hJ : Jm ε = (Jm ε').submatrix s.symm s.symm := by
    ext i j
    simp [Jm, Matrix.diagonal_apply, hε]
  refine ⟨?_, ?_⟩
  · have h1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv]
  · rw [hJ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg.2]

theorem wt_perm (s : Equiv.Perm (Fin n)) (hε : ∀ a, ε' a = ε (s a))
    (hσ : ∀ g, σ' g = σ (g.submatrix s.symm s.symm)) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Kset ε) σ μ v) : IsWtOn (Kset ε') σ' (μ ∘ s) v := by
  intro θ hθ
  have e : (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).submatrix s.symm s.symm =
      Matrix.diagonal fun a => Complex.exp (((θ ∘ s.symm) a : ℂ) * Complex.I) :=
    Matrix.submatrix_diagonal_equiv _ _
  have h1 := submatrix_mem_Kset s hε hθ
  rw [e] at h1
  rw [hσ, e, hv _ h1, ← Equiv.sum_comp s]
  simp

theorem root_comp (s : Equiv.Perm (Fin n)) (a b : Fin n) : root (s a) (s b) ∘ s = root a b := by
  funext i
  simp [root, Pi.single_apply]

theorem lt_of_perm_lt {s : Equiv.Perm (Fin n)} (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {a b : Fin n}
    (h : s a < s b) (he : ε (s a) = ε (s b)) : a < b := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact h1
  · exact absurd h (by simp [h1])
  · exact absurd h (not_lt.2 (hs b a h1 he.symm).le)

theorem cDom_perm (s : Equiv.Perm (Fin n)) (hε : ∀ a, ε' a = ε (s a))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {μ Λ : Fin n → ℝ} (h : CDom ε μ Λ) :
    CDom ε' (μ ∘ s) (Λ ∘ s) := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun a b => c (s a) (s b), fun a b h => ⟨lt_of_perm_lt hs (hc _ _ h).1 (hc _ _ h).2, ?_⟩, ?_⟩
  · rw [hε, hε]; exact (hc _ _ h).2
  · funext i
    have := congrFun e (s i)
    simp only [Pi.sub_apply, Finset.sum_apply] at this
    simp only [Pi.sub_apply, Function.comp_apply, this, Finset.sum_apply]
    rw [← Equiv.sum_comp s]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp s]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← root_comp s a b]
    rfl

theorem ktype_perm (s : Equiv.Perm (Fin n)) (hε : ∀ a, ε' a = ε (s a))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    (hσ : ∀ g, σ' g = σ (g.submatrix s.symm s.symm)) {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) : IsKTypeOf ε' σ' (Λ ∘ s) S := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩ := hS
  have hε' : ∀ a, ε a = ε' (s.symm a) := fun a => by rw [hε]; simp
  have hσ' : ∀ g, σ g = σ' (g.submatrix s.symm.symm s.symm.symm) := fun g => by
    rw [hσ]; simp [Matrix.submatrix_submatrix]
  refine ⟨h1, fun g hg x hx => ?_, fun S' hle hst => h3 S' hle fun g hg x hx => ?_,
    ⟨v, hv, hv0, wt_perm s hε hσ hvw⟩, fun μ x hx h0 hw => ?_⟩
  · rw [hσ]; exact h2 _ (submatrix_mem_Kset s hε hg) x hx
  · rw [hσ']; exact hst _ (submatrix_mem_Kset s.symm hε' hg) x hx
  · have := cDom_perm s hε hs (h5 _ x hx h0 (wt_perm s.symm hε' hσ' hw))
    simpa [Function.comp_assoc] using this

theorem rhoC_perm (s : Equiv.Perm (Fin n)) (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) :
    rhoC (ε ∘ s) = rhoC ε ∘ s := by
  funext a
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ s) b = (ε ∘ s) a).card =
      (univ.filter fun b => s a < b ∧ ε b = ε (s a)).card := by
    refine Finset.card_equiv s fun b => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun h => ⟨hs _ _ h.1 h.2.symm, h.2⟩, fun h => ⟨lt_of_perm_lt hs h.1 h.2.symm, h.2⟩⟩
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ s) b = (ε ∘ s) a).card =
      (univ.filter fun b => b < s a ∧ ε b = ε (s a)).card := by
    refine Finset.card_equiv s fun b => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun h => ⟨hs _ _ h.1 h.2, h.2⟩, fun h => ⟨lt_of_perm_lt hs h.1 h.2, h.2⟩⟩
  simp only [rhoC, Function.comp_apply] at h1 h2 ⊢
  rw [h1, h2]

theorem lowK_add (ε : Fin n → Bool) (lam : Fin n → ℝ) : lowK ε lam + (2 : ℝ) • rhoC ε = lam + Formalism.QuantumDeterminants.rhoStd n := by
  funext a
  have := Formalism.REAL.rhoStd n ε a
  simp only [lowK, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

theorem strictAnti_add_rho {lam : Fin n → ℝ} (h : StrictAnti lam) : StrictAnti (lam + Formalism.QuantumDeterminants.rhoStd n) := by
  intro a b hab
  have h1 := h hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Pi.add_apply, Formalism.QuantumDeterminants.rhoStd]
  linarith

theorem nsq_add_cone {x : Fin n → ℝ} (hx : Antitone x) {c : Fin n → Fin n → ℕ} (hc : ∀ a b, c a b ≠ 0 → a < b) :
    nsq x + nsq (∑ a, ∑ b, (c a b : ℝ) • root a b) ≤ nsq (x + ∑ a, ∑ b, (c a b : ℝ) • root a b) := by
  set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • root a b with hQ
  have hroot : ∀ a b, ∑ i, x i * root a b i = x a - x b := by
    intro a b
    simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have hdot : 0 ≤ ∑ i, x i * Q i := by
    have : ∑ i, x i * Q i = ∑ a, ∑ b, (c a b : ℝ) * (x a - x b) := by
      simp only [hQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← hroot]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h : c a b = 0
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hx (hc a b h).le))
  have : nsq (x + Q) = nsq x + 2 * ∑ i, x i * Q i + nsq Q := by
    simp only [nsq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

theorem nsq_nonneg (x : Fin n → ℝ) : 0 ≤ nsq x :=
  Finset.sum_nonneg (s := univ) (f := fun i => x i * x i) fun _ _ => mul_self_nonneg _

theorem eq_zero_of_nsq {x : Fin n → ℝ} (h : nsq x ≤ 0) : x = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).1
    (show ∑ j, x j * x j = 0 from le_antisymm h (nsq_nonneg x)) i (Finset.mem_univ i)
  exact mul_self_eq_zero.1 this

theorem nsq_comp (s : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : nsq (x ∘ s) = nsq x :=
  Equiv.sum_comp s fun a => x a * x a

theorem isDS_of_isHCDS {lam : Fin n → ℝ} (hl : IsHCParam lam) (h : IsHCDS ε lam σ) : IsDS ε lam σ := by
  obtain ⟨⟨c1, c2, c3, c4, c5⟩, -, h1, h2⟩ := h
  refine ⟨c1, c2, c3, c4, c5, h1.exists, fun μ S hS => ?_⟩
  obtain ⟨c, hc, rfl⟩ := h2 μ S hS
  unfold vNormSq
  rw [add_right_comm, lowK_add]
  have := nsq_add_cone (strictAnti_add_rho hl.1).antitone hc
  linarith [nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)]

theorem param_eq {lam mu : Fin n → ℝ} (hl : IsHCParam lam) (hm : IsHCParam mu) (hσ : IsDS ε lam σ)
    (s : Equiv.Perm (Fin n)) (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (hτ : IsHCDS (ε ∘ s) mu τ)
    (he : UEquiv (ε ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) τ) : s = 1 ∧ mu = lam := by
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, hmin⟩ := hσ
  obtain ⟨-, -, h1, h2⟩ := hτ
  obtain ⟨S₁, hS₁⟩ := exists_ktype_of_uEquiv he
    ⟨S, ktype_perm (ε' := ε ∘ s) s (fun _ => rfl) hs (fun _ => rfl) hS⟩
  obtain ⟨c, hc, e⟩ := h2 _ _ hS₁
  obtain ⟨S₂, hS₂⟩ := exists_ktype_of_uEquiv (uEquiv_symm he) h1.exists
  have h3 := hmin _ _ (ktype_perm (ε := ε ∘ s) (ε' := ε) (σ' := σ) s.symm (fun a => by simp)
    (fun a b hab h => lt_of_perm_lt hs (by simpa using hab) h)
    (fun g => by simp [Matrix.submatrix_submatrix]) hS₂)
  unfold vNormSq at h3
  have e1 : (lowK (ε ∘ s) mu ∘ s.symm + (2 : ℝ) • rhoC ε) ∘ s = mu + Formalism.QuantumDeterminants.rhoStd n := by
    rw [← lowK_add (ε ∘ s), rhoC_perm s hs]
    funext a
    simp
  have e2 : (lam + Formalism.QuantumDeterminants.rhoStd n) ∘ s = mu + Formalism.QuantumDeterminants.rhoStd n + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
    rw [← lowK_add (ε ∘ s) mu, add_right_comm, ← e, ← lowK_add ε lam, rhoC_perm s hs]
    rfl
  rw [lowK_add, ← nsq_comp s, ← nsq_comp s (_ + (2 : ℝ) • rhoC ε), e1, e2] at h3
  have h4 := nsq_add_cone (strictAnti_add_rho hm.1).antitone hc
  rw [eq_zero_of_nsq (x := ∑ a, ∑ b, (c a b : ℝ) • root a b) (by linarith), add_zero] at e2
  have h5 : StrictMono s := fun a b hab => by
    have := strictAnti_add_rho hm.1 hab
    rw [← e2] at this
    exact (strictAnti_add_rho hl.1).lt_iff_gt.1 this
  have h6 : s = 1 := by
    have := Subsingleton.elim (h5.orderIsoOfSurjective _ s.surjective) (OrderIso.refl _)
    exact Equiv.ext fun a => DFunLike.congr_fun this a
  subst h6
  exact ⟨rfl, (add_right_cancel (e2 : lam + Formalism.QuantumDeterminants.rhoStd n = mu + Formalism.QuantumDeterminants.rhoStd n)).symm⟩

theorem exists_model (h : DSClass) (ε : Fin n → Bool) {lam : Fin n → ℝ} (hl : IsHCParam lam) :
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (π : Matrix (Fin n) (Fin n) ℂ → (G →L[ℂ] G)), IsHCDS ε lam π ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → UEquiv ε σ π := by
  obtain ⟨G, _, _, π, hπ, hex⟩ := h n
  refine ⟨G ε lam, _, _, π ε lam, hπ ε lam hl, fun H _ _ σ hσ => ?_⟩
  obtain ⟨s, mu, hm, hs, he⟩ := hex ε H σ ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := param_eq hl hm hσ s hs (hπ _ _ hm) he
  exact he

theorem dsUnique_of_dsClass (h : DSClass) : DSUnique := by
  intro n ε lam H _ _ σ H' _ _ σ' hl hσ hσ'
  obtain ⟨G, _, _, π, -, key⟩ := exists_model h ε hl
  exact uEquiv_trans (key H σ hσ) (uEquiv_symm (key H' σ' hσ'))

theorem dsExists_of_dsClass (h : DSClass) : DSExists := by
  intro n ε lam hl
  obtain ⟨G, _, _, π, hπ, -⟩ := exists_model h ε hl
  exact ⟨G, _, _, π, isDS_of_isHCDS hl hπ⟩

theorem kTypesAbove_of_dsClass (h : DSClass) : KTypesAbove := by
  intro n ε lam H _ _ σ hl hσ μ S hS
  obtain ⟨G, _, _, π, hπ, key⟩ := exists_model h ε hl
  obtain ⟨S', hS'⟩ := exists_ktype_of_uEquiv (key H σ hσ) ⟨S, hS⟩
  exact hπ.2.2.2 μ S' hS'

theorem lowKMultOne_of_dsClass (h : DSClass) : LowKMultOne := by
  intro n ε lam H _ _ σ hl hσ S S' hS hS'
  obtain ⟨G, _, _, π, hπ, key⟩ := exists_model h ε hl
  obtain ⟨T, hT⟩ := key H σ hσ
  exact Submodule.map_injective_of_injective (f := (T.toLinearEquiv : H →ₗ[ℂ] G)) T.injective
    (hπ.2.2.1.unique (ktype_transfer T hT hS) (ktype_transfer T hT hS'))

end GlobalTheory.LowestKTypeDetermines
