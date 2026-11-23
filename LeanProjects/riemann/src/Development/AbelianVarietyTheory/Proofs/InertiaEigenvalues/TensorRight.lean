import Mathlib

namespace GlobalTheory.Cyc.FontW

def Dv (l r : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup M :=
  (nsmulAddMonoidHom (l ^ r) : M →+ M).range

theorem mem_Dv {l r : ℕ} {M : Type*} [AddCommGroup M] {x : M} :
    x ∈ Dv l r M ↔ ∃ y, l ^ r • y = x := Iff.rfl

theorem Dv_map {l r : ℕ} {M M' F : Type*} [AddCommGroup M] [AddCommGroup M'] [FunLike F M M']
    [AddMonoidHomClass F M M'] (f : F) {x : M} (hx : x ∈ Dv l r M) : f x ∈ Dv l r M' := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨f y, (map_nsmul f _ _).symm⟩

theorem Dv_smul {l r : ℕ} {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (a : A) {x : M}
    (hx : x ∈ Dv l r M) : a • x ∈ Dv l r M := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨a • y, smul_comm _ _ _⟩

def Cpl (l : ℕ) (M : Type*) [AddCommGroup M] : Prop :=
  (∀ x : M, (∀ r, x ∈ Dv l r M) → x = 0) ∧
    ∀ f : ℕ → M, (∀ r, f (r + 1) - f r ∈ Dv l r M) → ∃ L, ∀ r, L - f r ∈ Dv l r M

theorem Cpl.equiv {l : ℕ} {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (e : M ≃+ M')
    (h : Cpl l M') : Cpl l M := by
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact e.injective (by rw [map_zero]; exact h.1 _ fun r => Dv_map e (hx r))
  · obtain ⟨L, hL⟩ := h.2 (fun r => e (f r)) fun r => by
      rw [← map_sub]; exact Dv_map e (hf r)
    refine ⟨e.symm L, fun r => ?_⟩
    have := Dv_map e.symm (hL r)
    rwa [map_sub, e.symm_apply_apply] at this

theorem Cpl.pi {l : ℕ} {M : Type*} [AddCommGroup M] (ι : Type*) (h : Cpl l M) : Cpl l (ι → M) := by
  refine ⟨fun x hx => funext fun i => ?_, fun f hf => ?_⟩
  · exact h.1 _ fun r => Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hx r)
  · choose L hL using fun i => h.2 (fun r => f r i) fun r =>
      Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hf r)
    refine ⟨L, fun r => ?_⟩
    choose y hy using fun i => mem_Dv.1 (hL i r)
    exact mem_Dv.2 ⟨y, funext hy⟩

theorem Cpl.tensor_left {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R P M) := by
  classical
  let b := Module.Free.chooseBasis R P
  exact Cpl.equiv ((TensorProduct.equivFinsuppOfBasisLeft b).toAddEquiv.trans
    Finsupp.addEquivFunOnFinite) (h.pi _)

theorem Cpl.tensor_right {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R M P) :=
  Cpl.equiv (TensorProduct.comm R M P).toAddEquiv h.tensor_left

theorem cpl_witt (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [PerfectRing k p] :
    Cpl p (WittVector p k) := by
  have key : ∀ (r : ℕ) (x : WittVector p k), x ∈ Dv p r (WittVector p k) ↔
      x ∈ ((Ideal.span {(p : WittVector p k)}) ^ r • ⊤ : Submodule (WittVector p k) (WittVector p k)) := by
    intro r x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton', mem_Dv]
    simp [mul_comm]
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact IsHausdorff.haus (I := Ideal.span {(p : WittVector p k)}) inferInstance x fun n =>
      SModEq.zero.2 ((key n x).1 (hx n))
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : WittVector p k)}) inferInstance
      (f := f) ((AdicCompletion.isAdicCauchy_iff _ _ f).2 fun n => by
        rw [SModEq.sub_mem, ← key, ← neg_sub]; exact neg_mem (hf n))
    refine ⟨L, fun r => ?_⟩
    have := hL r
    rw [SModEq.sub_mem, ← key] at this
    rw [← neg_sub]; exact neg_mem this

theorem sum_translate {G X : Type*} [Group G] [AddCommMonoid X] (N : Subgroup G) (S : Finset G)
    (hS : ∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) (f : G → X) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (σ : G) :
    ∑ s ∈ S, f (σ * s) = ∑ s ∈ S, f s := by
  choose π hπ huniq using hS
  refine Finset.sum_nbij' (fun s => π (σ * s)) (fun t => π (σ⁻¹ * t)) (fun s _ => (hπ _).1)
    (fun s _ => (hπ _).1) (fun s hs => ?_) (fun t ht => ?_) (fun s _ => ?_)
  · refine (huniq _ s ⟨hs, ?_⟩).symm
    have := N.inv_mem (hπ (σ * s)).2
    simpa [mul_assoc] using this
  · refine (huniq _ t ⟨ht, ?_⟩).symm
    have := N.inv_mem (hπ (σ⁻¹ * t)).2
    simpa [mul_assoc] using this
  · have := hf (π (σ * s)) _ (hπ (σ * s)).2
    rw [← this]; simp

section Avg

variable {G A M : Type*} [Group G] [CommRing A] [AddCommGroup M] [Module A M] (l : ℕ)
  (𝓕 : Filter G) (a : G → A → A) (ρ : G → M →+ M)

theorem avg_step (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) (k : ℕ) (hk : ∀ g, c g ∈ Dv l k M) :
    ∃ b ∈ Dv l k M, (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l (k + 1) M := by
  obtain ⟨N, hN, hNF, hNW, S, hS, β, hβ, hsum⟩ := htr _ (hcont (k + 1))
  have hβ' : ∀ g, ∀ n ∈ N, a (g * n) β = a g β := fun g n hn => by rw [amul, hβ n hn]
  have hρ : ∀ σ, ρ σ (∑ s ∈ S, a s β • c s) = ∑ s ∈ S, a (σ * s) β • ρ σ (c s) := by
    intro σ
    rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [semi, amul]
  refine ⟨-∑ s ∈ S, a s β • c s, neg_mem (sum_mem fun s _ => Dv_smul _ (hk s)), fun r => ?_,
    fun σ => ?_⟩
  · obtain ⟨N', hN', hNF', hNW', -⟩ := htr _ (hcont r)
    filter_upwards [hNF, hNF'] with n hn hn'
    refine sub_mem (hNW' hn') ?_
    rw [map_neg, hρ, neg_sub_neg, ← Finset.sum_sub_distrib]
    refine sum_mem fun s _ => ?_
    have h1 : n * s = s * (s⁻¹ * n * s) := by group
    have h2 : a (n * s) β = a s β := by
      rw [h1]; exact hβ' _ _ (by simpa using hN.conj_mem n hn s⁻¹)
    rw [h2, ← smul_sub]
    refine Dv_smul _ ?_
    have h3 : c s - ρ n (c s) = c n - ρ s (c (s⁻¹ * n * s)) := by
      have h4 := hc n s
      rw [h1, hc] at h4
      rw [sub_eq_sub_iff_add_eq_add, h4]
    rw [h3]
    exact sub_mem (hNW' hn') (Dv_map _ (hNW' (by simpa using hN'.conj_mem n hn' s⁻¹)))
  · have h1 : ∑ s ∈ S, a (σ * s) β = 1 := by
      rw [sum_translate N S hS (fun g => a g β) hβ' σ, hsum]
    have h2 : c σ - (ρ σ (-∑ s ∈ S, a s β • c s) - -∑ s ∈ S, a s β • c s) =
        ∑ s ∈ S, a (σ * s) β • c (σ * s) - ∑ s ∈ S, a s β • c s := by
      rw [map_neg, hρ]
      simp only [hc, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, h1, one_smul]
      abel
    rw [h2, ← QuotientAddGroup.eq_iff_sub_mem]
    have h3 := sum_translate N S hS
      (fun g => QuotientAddGroup.mk' (Dv l (k + 1) M) (a g β • c g)) (fun g n hn => by
        rw [hβ' g n hn]
        refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
        rw [hc, smul_add, add_sub_cancel_left]
        exact Dv_smul _ (Dv_map _ (hNW hn))) σ
    rw [← map_sum, ← map_sum] at h3
    exact h3

theorem avg_cob (hM : Cpl l M) (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) : ∃ b, ∀ g, c g = ρ g b - b := by
  let P : ℕ → M → Prop := fun k b => (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l k M
  have h0 : P 0 0 := ⟨by simpa using hcont, fun g => mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
  have hstep : ∀ k b, P k b → ∃ b', P (k + 1) b' ∧ b' - b ∈ Dv l k M := by
    intro k b hb
    obtain ⟨d, hd, h1, h2⟩ := avg_step l 𝓕 a ρ amul ρmul semi htr (fun g => c g - (ρ g b - b))
      (fun g h => by simp only [hc, ρmul, map_sub]; abel) hb.1 k hb.2
    have e : ∀ g, c g - (ρ g (b + d) - (b + d)) = c g - (ρ g b - b) - (ρ g d - d) := fun g => by
      rw [map_add]; abel
    refine ⟨b + d, ⟨?_, ?_⟩, by simpa using hd⟩
    · simpa only [e] using h1
    · simpa only [e] using h2
  choose nx hnx using hstep
  let f : (k : ℕ) → {b // P k b} := fun k =>
    Nat.rec ⟨0, h0⟩ (fun k b => ⟨nx k b.1 b.2, (hnx k b.1 b.2).1⟩) k
  obtain ⟨L, hL⟩ := hM.2 (fun k => (f k).1) fun k => (hnx k (f k).1 (f k).2).2
  refine ⟨L, fun g => sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : c g - (ρ g L - L) = (c g - (ρ g (f r).1 - (f r).1)) - (ρ g (L - (f r).1) - (L - (f r).1)) := by
    rw [map_sub]; abel
  rw [e]
  exact sub_mem ((f r).2.2 g) (sub_mem (Dv_map _ (hL r)) (hL r))

end Avg

end GlobalTheory.Cyc.FontW
