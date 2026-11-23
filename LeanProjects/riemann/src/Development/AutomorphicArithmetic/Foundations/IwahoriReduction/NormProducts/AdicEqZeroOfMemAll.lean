import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
open GlobalTheory.KZ
open scoped Topology

private theorem UpperTheory.Kd.K4.mittagLeffler_algebraic (C B : ℕ → Type) [∀ r, AddCommGroup (C r)] [∀ r, AddCommGroup (B r)]
    (P : ∀ r, C (r + 1) →+ C r) (p : ∀ r, B (r + 1) →+ B r) (d : ∀ r, B r →+ C r) (N : ∀ r, ℕ → AddSubgroup (C r))
    (F : ∀ r, ℕ → C r) (hp : ∀ r, Function.Surjective (p r)) (hd : ∀ r b, P r (d (r + 1) b) = d r (p r b))
    (hN : ∀ r m n, m ≤ n → N r n ≤ N r m) (hP : ∀ r n a, a ∈ N (r + 1) n → P r a ∈ N r n)
    (h1 : ∀ r n, ∃ b, F r (n + 1) - (F r n + d r b) ∈ N r n)
    (h2 : ∀ r n, ∃ b, P r (F (r + 1) n) - (F r n + d r b) ∈ N r n) :
    ∃ β : ∀ r, ℕ → B r, (∀ r n, (F r (n + 1) + d r (β r (n + 1))) - (F r n + d r (β r n)) ∈ N r n) ∧
      ∀ r n, P r (F (r + 1) n + d (r + 1) (β (r + 1) n)) - (F r n + d r (β r n)) ∈ N r n := by
  have step : ∀ k (b : B k), ∃ b' : B (k + 1),
      P k (F (k + 1) (k + 1) + d (k + 1) b') - (F k k + d k b) ∈ N k k := by
    intro k b
    obtain ⟨b1, hb1⟩ := h1 (k + 1) k
    obtain ⟨b2, hb2⟩ := h2 k k
    obtain ⟨b', hb'⟩ := hp k (b - b2 - p k b1)
    refine ⟨b', ?_⟩
    have := (N k k).add_mem (hP _ _ _ hb1) hb2
    convert this using 1
    simp only [map_add, map_sub, hd, hb']
    abel
  choose st hst using step
  let b : ∀ k, B k := fun k => Nat.rec (motive := B) 0 st k
  have hb : ∀ k, b (k + 1) = st k (b k) := fun k => rfl
  let Q : ℕ → ∀ r, C r := fun j => Nat.rec (motive := fun _ => ∀ r, C r) (fun r => F r r + d r (b r))
    (fun _ q r => P r (q (r + 1))) j
  have hQ0 : ∀ r, Q 0 r = F r r + d r (b r) := fun r => rfl
  have hQs : ∀ j r, Q (j + 1) r = P r (Q j (r + 1)) := fun j r => rfl
  have hA : ∀ j r, Q (j + 1) r - Q j r ∈ N r (r + j) := by
    intro j
    induction j with
    | zero => intro r; rw [hQs, hQ0, hQ0, hb]; exact hst r (b r)
    | succ j ih =>
      intro r
      rw [hQs (j + 1), hQs j r, ← map_sub]
      exact hN r _ _ (by omega) (hP _ _ _ (ih (r + 1)))
  have hF : ∀ r n m, n ≤ m → ∃ a, F r m - (F r n + d r a) ∈ N r n := by
    intro r n m hm
    induction m, hm using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ m hm ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨a', ha'⟩ := h1 r m
      refine ⟨a + a', ?_⟩
      convert (N r n).add_mem (hN r _ _ hm ha') ha using 1
      simp only [map_add]
      abel
  have hB : ∀ n j r, n ≤ r + j → ∃ a, Q j r - (F r n + d r a) ∈ N r n := by
    intro n j
    induction j with
    | zero =>
      intro r hr
      obtain ⟨a, ha⟩ := hF r n r hr
      refine ⟨a + b r, ?_⟩
      convert ha using 1
      simp only [map_add, hQ0]
      abel
    | succ j ih =>
      intro r hr
      obtain ⟨a, ha⟩ := ih (r + 1) (by omega)
      obtain ⟨a', ha'⟩ := h2 r n
      refine ⟨a' + p r a, ?_⟩
      convert (N r n).add_mem (hP _ _ _ ha) ha' using 1
      simp only [map_add, map_sub, hQs, hd]
      abel
  choose β hβ using fun r n => hB n n r (by omega)
  refine ⟨β, fun r n => ?_, fun r n => ?_⟩
  · convert (N r n).sub_mem ((N r n).add_mem (hN r n _ (by omega) (hA n r)) (hβ r n))
      (hN r n _ (by omega) (hβ r (n + 1))) using 1
    abel
  · convert (N r n).sub_mem ((N r n).add_mem (hN r n _ (by omega) (hA n r)) (hβ r n))
      (hP _ _ _ (hβ (r + 1) n)) using 1
    rw [hQs, map_sub]
    abel

private theorem UpperTheory.Kd.K4.mem_adicPower_iff (l : ℕ) [Fact l.Prime] {B : Type} [AddCommGroup B] [Module ℤ_[l] B] (n : ℕ) (y : B) :
    y ∈ ((idl l) ^ n • ⊤ : Submodule ℤ_[l] B) ↔ ∃ d, y = (l : ℤ_[l]) ^ n • d := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨d, -, h⟩
    exact ⟨d, h.symm⟩
  · rintro ⟨d, h⟩
    exact ⟨d, trivial, h.symm⟩

private theorem UpperTheory.Kd.K4.exists_adic_limit_of_sub_mem_pow_smul (l : ℕ) [Fact l.Prime] {B : Type} [AddCommGroup B] [Module ℤ_[l] B]
    [IsAdicComplete (idl l) B] (u : ℕ → B) (h : ∀ n, u (n + 1) - u n ∈ ((idl l) ^ n • ⊤ : Submodule ℤ_[l] B)) :
    ∃ y, ∀ n, y - u n ∈ ((idl l) ^ n • ⊤ : Submodule ℤ_[l] B) := by
  have hm : ∀ m n, m ≤ n → u n - u m ∈ ((idl l) ^ m • ⊤ : Submodule ℤ_[l] B) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have e : u (n + 1) - u m = (u (n + 1) - u n) + (u n - u m) := by abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mono_left (Ideal.pow_le_pow_right hn) (h n)) ih
  obtain ⟨L, hL⟩ := (IsAdicComplete.toIsPrecomplete : IsPrecomplete (idl l) B).prec (f := u)
    (fun {m n} hmn => SModEq.symm (SModEq.sub_mem.2 (hm m n hmn)))
  refine ⟨L, fun n => ?_⟩
  exact SModEq.sub_mem.1 (hL n).symm

private theorem UpperTheory.Kd.K4.adic_eq_zero_of_mem_all (l : ℕ) [Fact l.Prime] {B : Type} [AddCommGroup B] [Module ℤ_[l] B]
    [IsAdicComplete (idl l) B] (a : B) (h : ∀ n, a ∈ ((idl l) ^ n • ⊤ : Submodule ℤ_[l] B)) : a = 0 :=
  (IsAdicComplete.toIsHausdorff : IsHausdorff (idl l) B).haus a fun n => SModEq.zero.2 (h n)

private theorem UpperTheory.Kd.K4.fiberSum_push_hecke {X X' : Type} [Group X] [Group X'] [Fintype X'] [DecidableEq X]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (π : X' →* X) (g : X') (T : Module.End R M) (b : X' → M) (x : X) :
    ∑ x' ∈ Finset.univ.filter (fun x' => π x' = x), (T (b (x' * g)) - b x') =
      T (∑ x' ∈ Finset.univ.filter (fun x' => π x' = x * π g), b x') -
        ∑ x' ∈ Finset.univ.filter (fun x' => π x' = x), b x' := by
  rw [Finset.sum_sub_distrib, map_sum]
  congr 1
  refine Finset.sum_equiv (Equiv.mulRight g) (fun y => ?_) (fun y _ => rfl)
  simp

theorem UpperTheory.Kd.K4.ml3 :
    ∀ (l : ℕ) [Fact l.Prime] (B : Type) [AddCommGroup B] [Module ℤ_[l] B] [IsAdicComplete (idl l) B] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
      (A : ℕ → Type) [∀ r, Group (A r)] [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)] (π : ∀ r, A (r + 1) →* A r) (κ : ∀ r, Γ →* A r)
      (σ : Γ →* Module.End ℤ_[l] B) (F : ∀ r : ℕ, ℕ → Γ → A r → B),
      (∀ r, Function.Surjective (π r)) → (∀ r s, π r (κ (r + 1) s) = κ r s) → (∀ r, IsLocallyConstant (κ r)) →
      (∀ (n : ℕ) b s, ∀ᶠ t in 𝓝 s, ∃ d, σ t b - σ s b = (l : ℤ_[l]) ^ n • d) →
      (∀ r n s x, ∀ᶠ t in 𝓝 s, ∃ d, F r n t x - F r n s x = (l : ℤ_[l]) ^ n • d) →
      (∀ r n s t x, ∃ d, F r n (s * t) x - (F r n s x + σ s (F r n t (x * κ r s))) = (l : ℤ_[l]) ^ n • d) →
      (∀ r n, ∃ b : A r → B, ∀ s x, ∃ d, F r (n + 1) s x - (F r n s x + (σ s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d) →
      (∀ r n, ∃ b : A r → B, ∀ s x, ∃ d, GlobalTheory.KA.push (π r) (F (r + 1) n) s x - (F r n s x + (σ s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d) →
      ∃ Y : ∀ r : ℕ, Γ → A r → B, (∀ r s t x, Y r (s * t) x = Y r s x + σ s (Y r t (x * κ r s))) ∧
        (∀ r (n : ℕ) s x, ∀ᶠ t in 𝓝 s, ∃ d, Y r t x - Y r s x = (l : ℤ_[l]) ^ n • d) ∧ (∀ r, Y r = GlobalTheory.KA.push (π r) (Y (r + 1))) ∧
        ∀ r n, ∃ b : A r → B, ∀ s x, ∃ d, Y r s x - (F r n s x + (σ s (b (x * κ r s)) - b x)) = (l : ℤ_[l]) ^ n • d := by
  intro l _ B _ _ _ Γ _ _ A _ _ _ π κ σ F hπ hκ hlc hσc hFc hFz h1 h2
  let D : ℕ → Submodule ℤ_[l] B := fun n => (idl l) ^ n • ⊤
  have hDmono : ∀ {m n}, m ≤ n → D n ≤ D m := fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have hDσ : ∀ s n y, y ∈ D n → σ s y ∈ D n := by
    intro s n y hy
    obtain ⟨e, rfl⟩ := (UpperTheory.Kd.K4.mem_adicPower_iff l n y).1 hy
    exact (UpperTheory.Kd.K4.mem_adicPower_iff l n _).2 ⟨σ s e, map_smul _ _ _⟩
  let N : ∀ r, ℕ → AddSubgroup (Γ → A r → B) := fun r n =>
    { carrier := {f | ∀ s x, f s x ∈ D n}
      add_mem' := fun ha hb s x => (D n).add_mem (ha s x) (hb s x)
      zero_mem' := fun _ _ => (D n).zero_mem
      neg_mem' := fun ha s x => (D n).neg_mem (ha s x) }
  let P : ∀ r, (Γ → A (r + 1) → B) →+ (Γ → A r → B) := fun r =>
    { toFun := GlobalTheory.KA.push (π r)
      map_zero' := by funext s x; simp [GlobalTheory.KA.push]
      map_add' := fun a b => by funext s x; simp [GlobalTheory.KA.push, Finset.sum_add_distrib] }
  let p : ∀ r, (A (r + 1) → B) →+ (A r → B) := fun r =>
    { toFun := fun b x => ∑ x' ∈ Finset.univ.filter (fun x' => π r x' = x), b x'
      map_zero' := by funext x; simp
      map_add' := fun a b => by funext x; simp [Finset.sum_add_distrib] }
  let d : ∀ r, (A r → B) →+ (Γ → A r → B) := fun r =>
    { toFun := fun b s x => σ s (b (x * κ r s)) - b x
      map_zero' := by funext s x; simp
      map_add' := fun a b => by
        funext s x
        simp only [Pi.add_apply, map_add]
        abel }
  have hp : ∀ r, Function.Surjective (p r) := by
    intro r b
    choose τ hτ using hπ r
    refine ⟨fun y => if τ (π r y) = y then b (π r y) else 0, ?_⟩
    funext x
    change ∑ x' ∈ Finset.univ.filter (fun x' => π r x' = x), (if τ (π r x') = x' then b (π r x') else 0) = b x
    rw [Finset.sum_eq_single (τ x)]
    · simp [hτ]
    · intro y hy hne
      rw [(Finset.mem_filter.1 hy).2, if_neg (Ne.symm hne)]
    · intro h
      exact absurd (by simp [hτ]) h
  have hd : ∀ r b, P r (d (r + 1) b) = d r (p r b) := by
    intro r b
    funext s x
    have := UpperTheory.Kd.K4.fiberSum_push_hecke (π r) (κ (r + 1) s) (σ s) b x
    rw [hκ] at this
    exact this
  have hN : ∀ r m n, m ≤ n → N r n ≤ N r m := fun r m n h f hf s x => hDmono h (hf s x)
  have hP : ∀ r n a, a ∈ N (r + 1) n → P r a ∈ N r n := by
    intro r n a ha s x
    change ∑ x' ∈ Finset.univ.filter (fun x' => π r x' = x), a s x' ∈ D n
    exact Submodule.sum_mem _ fun y _ => ha s y
  obtain ⟨β, hβ1, hβ2⟩ := UpperTheory.Kd.K4.mittagLeffler_algebraic (fun r => Γ → A r → B) (fun r => A r → B) P p d N F hp hd hN hP
    (fun r n => by
      obtain ⟨b, h⟩ := h1 r n
      exact ⟨b, fun s x => (UpperTheory.Kd.K4.mem_adicPower_iff l n _).2 (h s x)⟩)
    (fun r n => by
      obtain ⟨b, h⟩ := h2 r n
      exact ⟨b, fun s x => (UpperTheory.Kd.K4.mem_adicPower_iff l n _).2 (h s x)⟩)
  choose Y hY using fun r s x => UpperTheory.Kd.K4.exists_adic_limit_of_sub_mem_pow_smul l (fun n => (F r n + d r (β r n)) s x) (fun n => hβ1 r n s x)
  have hYN : ∀ r n, Y r - (F r n + d r (β r n)) ∈ N r n := fun r n s x => hY r s x n
  refine ⟨Y, fun r s t x => ?_, fun r n s x => ?_, fun r => ?_, fun r n => ⟨β r n, fun s x => (UpperTheory.Kd.K4.mem_adicPower_iff l n _).1 (hY r s x n)⟩⟩
  · refine sub_eq_zero.1 (UpperTheory.Kd.K4.adic_eq_zero_of_mem_all l _ fun n => ?_)
    have e : Y r (s * t) x - (Y r s x + σ s (Y r t (x * κ r s))) =
        (F r n (s * t) x - (F r n s x + σ s (F r n t (x * κ r s)))) +
        ((Y r - (F r n + d r (β r n))) (s * t) x - (Y r - (F r n + d r (β r n))) s x -
          σ s ((Y r - (F r n + d r (β r n))) t (x * κ r s))) := by
      have hdv : ∀ s x, d r (β r n) s x = σ s (β r n (x * κ r s)) - β r n x := fun _ _ => rfl
      simp only [Pi.sub_apply, Pi.add_apply, hdv, map_sub, map_add, map_mul, mul_assoc, Module.End.mul_apply]
      abel
    rw [e]
    exact (D n).add_mem ((UpperTheory.Kd.K4.mem_adicPower_iff l n _).2 (hFz r n s t x))
      ((D n).sub_mem ((D n).sub_mem (hYN r n _ _) (hYN r n _ _)) (hDσ s n _ (hYN r n _ _)))
  · have hk : ∀ᶠ t in 𝓝 s, κ r t = κ r s := (hlc r).eventually_eq s
    filter_upwards [hFc r n s x, hσc n (β r n (x * κ r s)) s, hk] with t ht1 ht2 ht3
    refine (UpperTheory.Kd.K4.mem_adicPower_iff l n _).1 ?_
    have hdt : d r (β r n) t x = σ t (β r n (x * κ r s)) - β r n x := by
      change σ t (β r n (x * κ r t)) - β r n x = _
      rw [ht3]
    have hds : d r (β r n) s x = σ s (β r n (x * κ r s)) - β r n x := rfl
    have e : Y r t x - Y r s x = ((Y r - (F r n + d r (β r n))) t x - (Y r - (F r n + d r (β r n))) s x) +
        ((F r n t x - F r n s x) + (σ t (β r n (x * κ r s)) - σ s (β r n (x * κ r s)))) := by
      simp only [Pi.sub_apply, Pi.add_apply, hdt, hds]
      abel
    rw [e]
    exact (D n).add_mem ((D n).sub_mem (hYN r n _ _) (hYN r n _ _))
      ((D n).add_mem ((UpperTheory.Kd.K4.mem_adicPower_iff l n _).2 ht1) ((UpperTheory.Kd.K4.mem_adicPower_iff l n _).2 ht2))
  · funext s x
    refine sub_eq_zero.1 (UpperTheory.Kd.K4.adic_eq_zero_of_mem_all l _ fun n => ?_)
    have h : Y r - P r (Y (r + 1)) ∈ N r n := by
      convert (N r n).sub_mem ((N r n).sub_mem (hYN r n) (hβ2 r n)) (hP r n _ (hYN (r + 1) n)) using 1
      rw [map_sub]
      abel
    exact h s x
