import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TrOf

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem qdet_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp only [qdet, qminor, Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def,
    map_add, apply_ite φ, map_zero, AlgHom.commutes]

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

def rl (e : P ≃ Q) : TV n M P ≃ₗ[ℂ] TV n M Q :=
  LinearEquiv.funCongrLeft ℂ M (e.symm.arrowCongr (Equiv.refl (Fin n)))

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem rl_apply (e : P ≃ Q) (f : TV n M P) (J : Q → Fin n) : rl e f J = f (J ∘ e) := rfl

theorem tE_rl (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    tE Finset.univ E a b (rl e f) = rl e (tE Finset.univ E a b f) := by
  funext J
  simp only [tE_apply, rl_apply]
  congr 1
  refine (Fintype.sum_equiv e.symm _ _ fun q => ?_)
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [← Function.update_comp_eq_of_injective J e.injective (e.symm q) b, Equiv.apply_symm_apply]

theorem conj_tE (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    (rl (n := n) (M := M) e).conjAlgEquiv ℂ (tE Finset.univ E a b) = tE Finset.univ E a b := by
  refine LinearMap.ext fun g => ?_
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← tE_rl, LinearEquiv.apply_symm_apply]

theorem cA_rl {C : Type} [DecidableEq C] (e : P ≃ Q) (col : P → C) (b : P → Fin n) (f : TV n M P) :
    cA (col ∘ e.symm) (b ∘ e.symm) (rl e f) = cA col b f := by
  simp only [cA_apply, alt_apply, rl_apply]
  symm
  refine Finset.sum_equiv (Equiv.permCongr e) (fun σ => ?_) (fun σ _ => ?_)
  · simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]
    exact ⟨fun h q => h _, fun h p => by simpa using h (e p)⟩
  · rw [Equiv.Perm.sign_permCongr]
    congr 2
    funext x
    simp [Equiv.permCongr_apply]

theorem cA_congr {C C' : Type} [DecidableEq C] [DecidableEq C'] (c1 : Q → C) (c2 : Q → C')
    (h : ∀ p q, c1 p = c1 q ↔ c2 p = c2 q) (b : Q → Fin n) : (cA c1 b : TV n M Q →ₗ[ℂ] M) = cA c2 b := by
  have : colG c1 = colG c2 := by
    ext σ
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, h]
  simp only [cA, this]

theorem transfer (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℤ) (ℓ : M →ₗ[ℂ] ℂ)
    {C C' : Type} [DecidableEq C] [DecidableEq C'] (col : P → C) (col' : Q → C')
    (hcol : ∀ q q', col' q = col' q' ↔ col (e.symm q) = col (e.symm q')) (b co : P → Fin n)
    (h : ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset Q) E), ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S ≠ 0 ∧
      ∀ u : ℂ, (ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset Q) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co (e.symm p) = k).card : ℂ))) •
          (ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S)) :
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S) := by
  obtain ⟨S', hS', hne, heig⟩ := h
  set φ := (rl (n := n) (M := M) e).conjAlgEquiv ℂ with hφdef
  set K := ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S' with hK
  have hsymm : ∀ T f, φ.symm T f = (rl e).symm (T (rl e f)) := fun T f => rfl
  have key : ∀ f, ℓ (cA col b (φ.symm S' f)) = K (rl e f) := by
    intro f
    simp only [hK, LinearMap.comp_apply, hsymm]
    rw [← cA_rl e col b, LinearEquiv.apply_symm_apply, cA_congr col' (col ∘ e.symm) hcol]
  have hq : ∀ u f, rl e (qdet (tE (Finset.univ : Finset P) E) u f) = qdet (tE (Finset.univ : Finset Q) E) u (rl e f) := by
    intro u f
    have h1 : φ (qdet (tE (Finset.univ : Finset P) E) u) = qdet (tE (Finset.univ : Finset Q) E) u := by
      have := qdet_map (φ : Module.End ℂ (TV n M P) →ₐ[ℂ] Module.End ℂ (TV n M Q)) (tE (Finset.univ : Finset P) E) u
      simpa [conj_tE, hφdef] using this
    rw [← h1]
    simp only [hφdef, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  have hcard : ∀ k, (Finset.univ.filter fun p => co (e.symm p) = k).card = (Finset.univ.filter fun p => co p = k).card :=
    fun k => Finset.card_equiv e.symm (by simp)
  refine ⟨φ.symm S', ?_, ?_, ?_⟩
  · have hle : envAlg (fun _ : Unit => tE (Finset.univ : Finset Q) E) ≤
        (envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E)).comap φ.symm.toAlgHom := by
      refine Algebra.adjoin_le ?_
      rintro T ⟨_, a, c, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_comap]
      change φ.symm (tE Finset.univ E a c) ∈ _
      rw [φ.symm_apply_eq.mpr (conj_tE e E a c).symm]
      exact Algebra.subset_adjoin ⟨(), a, c, rfl⟩
    exact hle hS'
  · intro h0
    apply hne
    refine LinearMap.ext fun g => ?_
    have := LinearMap.congr_fun h0 ((rl e).symm g)
    simp only [LinearMap.comp_apply] at this
    rw [key, LinearEquiv.apply_symm_apply] at this
    simpa using this
  · intro u
    refine LinearMap.ext fun f => ?_
    have := LinearMap.congr_fun (heig u) (rl e f)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this ⊢
    rw [key, key, hq, this]
    simp only [hK, LinearMap.comp_apply, hcard]

theorem zero_case (E : Fin 0 → Fin 0 → Module.End ℂ M) (l : Fin 0 → ℤ) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin 0) :
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have : IsEmpty P := ⟨fun p => (b p).elim0⟩
  have hσ : ∀ σ : Equiv.Perm P, σ = 1 := fun σ => Equiv.ext fun p => isEmptyElim p
  have hG : colG col = {1} := by
    ext σ
    simp [colG, hσ σ]
  have hqd : ∀ u, qdet (tE (Finset.univ : Finset P) E) u = 1 := by
    intro u
    simp [qdet, qminor]
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, fun h0 => hv ?_, fun u => ?_⟩
  · have := LinearMap.congr_fun h0 (fun _ => v)
    simpa [cA_apply, alt_apply, hG] using this
  · rw [hqd]
    refine LinearMap.ext fun x => ?_
    simp

def cI {C : Type} [DecidableEq C] (col : P → C) (p : P) : ℕ :=
  (Fintype.equivFin (Set.range col) ⟨col p, p, rfl⟩ : ℕ)

theorem cI_eq {C : Type} [DecidableEq C] (col : P → C) (p q : P) : cI col p = cI col q ↔ col p = col q := by
  simp only [cI, Fin.val_inj, Equiv.apply_eq_iff_eq, Subtype.ext_iff]

omit [DecidableEq P] in
theorem exists_sort {α : Type} [LinearOrder α] (key : P → α) :
    ∃ e : P ≃ Fin (Fintype.card P), Monotone (key ∘ e.symm) :=
  ⟨(Fintype.equivFin P).trans (Tuple.sort (key ∘ (Fintype.equivFin P).symm)).symm,
    Tuple.monotone_sort (key ∘ (Fintype.equivFin P).symm)⟩

end TrOf

theorem trans_of (hT : TransFin) : Trans := by
  intro n M _ _ E hE l hl ℓ hℓ hW P _ _ C _ col b co hb hco
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact TrOf.zero_case E l ℓ hℓ col b co
  set a : P → ℕ := TrOf.cI col with ha
  set v : P → ℤ := fun p => l (co p) + ((Finset.univ.filter fun q => a q < a p ∧ co q = co p).card : ℤ) with hv
  obtain ⟨e, he⟩ := TrOf.exists_sort (fun p => toLex (a p, OrderDual.toDual (v p)))
  have hle : ∀ i j : Fin (Fintype.card P), i ≤ j → a (e.symm i) ≤ a (e.symm j) ∧
      (a (e.symm i) = a (e.symm j) → v (e.symm j) ≤ v (e.symm i)) := by
    intro i j hij
    have := he hij
    simp only [Function.comp_apply, Prod.Lex.toLex_le_toLex, OrderDual.toDual_le_toDual] at this
    rcases this with h | ⟨h1, h2⟩
    · exact ⟨h.le, fun h' => absurd h' h.ne⟩
    · exact ⟨h1.le, fun _ => h2⟩
  have hmono : Monotone (a ∘ e.symm) := fun i j hij => (hle i j hij).1
  have hainj : ∀ p q, a p = a q ↔ col p = col q := TrOf.cI_eq col
  have htab : IsTab (a ∘ e.symm) (b ∘ e.symm) := by
    refine ⟨fun i j h1 h2 => e.symm.injective (hb.1 _ _ ((hainj _ _).1 h1) h2), fun i k hk => ?_⟩
    obtain ⟨q, hq1, hq2⟩ := hb.2 (e.symm i) k hk
    exact ⟨e q, by simp [(hainj _ _).2 hq1], by simpa using hq2⟩
  have hco' : ∀ i j : Fin (Fintype.card P), a (e.symm i) = a (e.symm j) → co (e.symm i) = co (e.symm j) → i = j :=
    fun i j h1 h2 => e.symm.injective (hco _ _ ((hainj _ _).1 h1) h2)
  have hcnt : ∀ j : Fin (Fintype.card P), (Finset.univ.filter fun p => p < j ∧ co (e.symm p) = co (e.symm j)).card =
      (Finset.univ.filter fun q => a q < a (e.symm j) ∧ co q = co (e.symm j)).card := by
    intro j
    refine Finset.card_equiv e.symm (fun p => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_left fun hc => ⟨fun hp => lt_of_le_of_ne (hmono hp.le) (fun h => hp.ne (hco' p j h hc)),
      fun h => ?_⟩
    by_contra hp
    exact absurd (hmono (not_lt.1 hp)) (not_le.2 h)
  have hord : ∀ i j : Fin (Fintype.card P), i < j → (a ∘ e.symm) i = (a ∘ e.symm) j →
      l ((co ∘ e.symm) j) + ((Finset.univ.filter fun p => p < j ∧ (co ∘ e.symm) p = (co ∘ e.symm) j).card : ℤ) ≤
        l ((co ∘ e.symm) i) + ((Finset.univ.filter fun p => p < i ∧ (co ∘ e.symm) p = (co ∘ e.symm) i).card : ℤ) := by
    intro i j hij h
    simp only [Function.comp_apply] at h ⊢
    rw [hcnt i, hcnt j]
    exact (hle i j hij.le).2 h
  have := hT n M E hE l hl ℓ hℓ hW hn (Fintype.card P) (a ∘ e.symm) (b ∘ e.symm) (co ∘ e.symm) hmono htab hord
  exact TrOf.transfer e E l ℓ col (a ∘ e.symm) (fun q q' => hainj _ _) b co this

end PositivityTheory.Rg.Cz

end
