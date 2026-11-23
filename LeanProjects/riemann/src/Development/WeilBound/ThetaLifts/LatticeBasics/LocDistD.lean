import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.LocDistC

open Filter Topology GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.LD

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}

theorem nonarch_mat (n d : ℕ) : NonarchimedeanAddGroup (Matrix (Fin n) (Fin d) k) :=
  haveI := nonarch_pi (Fin d) k
  nonarch_pi (Fin n) (Fin d → k)

theorem lc_mat (n d : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))

def Claim (c : k → ℂ) (n d : ℕ) : Prop :=
  ∀ l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ, Eqv c l → (∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) → ∀ φ ∈ SB _, l φ = 0

theorem step_chart (hc : ∀ a ≠ 0, c a ≠ 0) (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) {n d : ℕ} (ih : Claim c n d)
    {l : (Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, (∀ X, X 0 0 = 0 → φ X = 0) → l φ = 0 := by
  have := nonarch_pi (Fin d) k
  have := nonarch_mat (k := k) n d
  have := lc_mat (k := k) n d
  intro φ hφ hz
  let L := l ∘ₗ LinearMap.funLeft ℂ ℂ (chE (k := k) (n := n) (d := d))
  have hL : ∀ F, L F = l fun X => F (chE X) := fun _ => rfl
  have e : φ = fun X => φ (chR (chE X)) := by
    ext X
    by_cases hX : X 0 0 = 0
    · rw [hz X hX, hz _ (by simpa [chR, chE] using hX)]
    · rw [chR_chE X hX]
  rw [e, ← hL fun y => φ (chR y)]
  refine kill_tens {z | z.1 0 ≠ 0} L (fun F hF hF0 ψ hψ => ?_) (sb_chR hφ hz)
    fun z h => hz _ (by simpa [chR] using h)
  let T : ∀ ψ : Matrix (Fin n) (Fin d) k → ℂ, ((Fin (n + 1) → k) × (Fin d → k) → ℂ) →ₗ[ℂ] ℂ := fun ψ =>
    { toFun := fun F => L fun z => F z.1 * ψ z.2
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; simp [add_mul]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_assoc] }
  refine kill_tens {x : Fin (n + 1) → k | x 0 ≠ 0} (T ψ) (fun f hf hf0 => ?_) hF fun z h => hF0 z h
  replace hf0 : ∀ x, x 0 = 0 → f x = 0 := fun x hx => hf0 x (not_not.2 hx)
  let m : ∀ ψ : Matrix (Fin n) (Fin d) k → ℂ, ((Fin d → k) → ℂ) →ₗ[ℂ] ℂ := fun ψ =>
    { toFun := fun g => T ψ fun z => f z.1 * g z.2
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  have hm : ∀ ψ g, m ψ g = l fun X => f (chE X).1.1 * g (chE X).1.2 * ψ (chE X).2 := fun _ _ => rfl
  have sb : ∀ ψ ∈ SB _, ∀ g ∈ SB (Fin d → k), (fun X => f (chE X).1.1 * g (chE X).1.2 * ψ (chE X).2) ∈ SB _ := fun ψ hψ g hg =>
    sb_chE (sb_tens (sb_tens hf hg) hψ) fun y hy => by simp [hf0 _ hy]
  have inv : ∀ ψ ∈ SB _, ∀ g ∈ SB _, ∀ a, m ψ (fun x => g (x + a)) = m ψ g := fun ψ hψ g hg a => by
    rw [hm, hm, ← hl.unip hc h0 h1 a _ (sb ψ hψ g hg)]
    congr 1; ext X
    by_cases hX : X 0 0 = 0
    · rw [hf0 _ (by simpa [chE] using hX), hf0 _ (by simpa [chE, mul_blk_zero] using hX)]; simp
    · rw [chE_unip X hX]
  obtain ⟨g₀, hg₀⟩ := exists_bump (Fin d → k)
  obtain ⟨_, -, hs⟩ := bump_ratio hg₀ hg₀
  refine (hs _ (inv ψ hψ)).2 ?_
  let l₁ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => f (chE X).1.1 * g₀ (chE X).1.2 * ψ (chE X).2
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  refine ih l₁ (fun h hh => ?_) (fun ψ hψ hψ0 => hd _ (sb ψ hψ _ hg₀.1) fun X hX => ?_) ψ hψ
  · have hg₁ : Bump fun u => g₀ (u ᵥ* h) :=
      ⟨sb_comp (· ᵥ* h) (· ᵥ* h⁻¹) (by fun_prop) (by fun_prop)
        (fun x => by simp [mul_nonsing_inv h hh.isUnit]) hg₀.1, fun _ => hg₀.2.1 _, by simpa using hg₀.2.2⟩
    obtain ⟨s, ps, hs⟩ := bump_ratio hg₀ hg₁
    obtain ⟨t, pt, ht⟩ := hl (blk 1 0 h) (by simpa [det_blk] using hh)
    refine ⟨t * s, mul_pos pt ps, fun ψ hψ => ?_⟩
    have a := ht _ (sb ψ hψ _ hg₀.1)
    simp only [chE_levi, det_blk, one_mul] at a
    have b := (hs _ (inv _ (sb_right hψ hh))).1
    refine b.trans ((congrArg ((s : ℂ) * ·) a).trans ?_)
    show _ * (_ * l₁ ψ) = _
    push_cast; ring
  · by_cases hX0 : X 0 0 = 0
    · rw [hf0 _ (by simpa [chE] using hX0)]; simp
    · rw [hψ0 _ (hX.chE hX0), mul_zero]

theorem step_row (hc : ∀ a ≠ 0, c a ≠ 0) {n d : ℕ} {l : (Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hz : ∀ φ ∈ SB _, (∀ X, X 0 0 = 0 → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, (∀ X, X 0 = 0 → φ X = 0) → l φ = 0 := by
  have := nonarch_mat (k := k) (n + 1) (d + 1)
  intro φ hφ h0
  refine kill_loc l hφ fun x hx => ?_
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (fun h => hx (h0 x h) : x 0 ≠ 0)
  refine ⟨{X | X 0 j ≠ 0}, (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds hj, fun ψ hψ hψ0 => ?_⟩
  have hh : (swap k 0 j).det ≠ 0 := (isUnit_det_of_left_inverse (swap_mul_self 0 j)).ne_zero
  obtain ⟨t, pt, ht⟩ := hl _ hh
  have a := ht ψ hψ
  rw [hz _ (sb_right hψ hh) fun X hX => hψ0 _ (by simpa [mul_swap_apply_right] using hX)] at a
  exact (mul_eq_zero.1 a.symm).resolve_left (mul_ne_zero (hc _ hh) (by exact_mod_cast pt.ne'))

theorem step_closed {n d : ℕ} (ih : Claim c n d) {l : (Matrix (Fin (n + 1)) (Fin d) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) (hz : ∀ φ ∈ SB _, (∀ X, X 0 = 0 → φ X = 0) → l φ = 0) :
    ∀ φ ∈ SB _, l φ = 0 := by
  have := nonarch_pi (Fin d) k
  obtain ⟨g₀, hg₀⟩ := exists_bump (Fin d → k)
  let cn : (Fin d → k) → Matrix (Fin n) (Fin d) k → Matrix (Fin (n + 1)) (Fin d) k := fun y Y => Matrix.of (Fin.cons y Y)
  let tl : Matrix (Fin (n + 1)) (Fin d) k → Matrix (Fin n) (Fin d) k := fun X => X.submatrix Fin.succ id
  have ccn : Continuous fun z : (Fin d → k) × Matrix (Fin n) (Fin d) k => cn z.1 z.2 := by
    refine continuous_matrix fun i j => ?_
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [cn] <;> fun_prop
  have ctl : Continuous tl := by fun_prop
  have hcn : ∀ X, cn (X 0) (tl X) = X := fun X => by
    ext i j; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have sb : ∀ ψ ∈ SB _, (fun X => g₀ (X 0) * ψ (tl X)) ∈ SB (Matrix (Fin (n + 1)) (Fin d) k) := fun ψ hψ =>
    sb_comp (fun X => (X 0, tl X)) (fun z => cn z.1 z.2) (by fun_prop) ccn hcn (sb_tens hg₀.1 hψ)
  let l₂ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => g₀ (X 0) * ψ (tl X)
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  have eq : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, (∀ X, X 0 = 0 → φ X = φ' X) → l φ = l φ' := fun φ hφ φ' hφ' h => by
    rw [← sub_eq_zero, ← map_sub]
    exact hz _ (sub_mem hφ hφ') fun X hX => sub_eq_zero.2 (h X hX)
  have z := ih l₂ (fun h hh => ?_) fun ψ hψ hψ0 => hd _ (sb ψ hψ) fun X hX => ?_
  · intro φ hφ
    have hr : (fun Y => φ (cn 0 Y)) ∈ SB _ :=
      sb_comp (cn 0) tl (ccn.comp (Continuous.prodMk_right 0)) ctl (fun Y => rfl) hφ
    refine (eq φ hφ _ (sb _ hr) fun X hX => ?_).trans (z _ hr)
    have := hcn X
    rw [hX] at this
    rw [this, hX, hg₀.2.2, one_mul]
  · obtain ⟨t, pt, ht⟩ := hl h hh
    refine ⟨t, pt, fun ψ hψ => (eq _ (sb _ (sb_right hψ hh)) _ (sb_right (sb ψ hψ) hh) fun X hX => ?_).trans (ht _ (sb ψ hψ))⟩
    have : (X * h) 0 = 0 := by ext j; simp [mul_apply, hX]
    rw [hX, this]; rfl
  · obtain ⟨v, hv, h⟩ := hX
    rw [hψ0 (tl X) ⟨v, hv, funext fun i => congrFun h i.succ⟩, mul_zero]

theorem claim (hc : ∀ a ≠ 0, c a ≠ 0) (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) (hϖ : ∀ t : ℝ, 0 < t → c ϖ * t ≠ 1) (n : ℕ) :
    ∀ d, Claim c n d := by
  have zero : ∀ n, Claim c n 0 := fun n l _ h φ hφ => h φ hφ fun X ⟨v, hv, _⟩ => absurd (Subsingleton.elim _ _) hv
  induction n with
  | zero =>
    rintro (_ | d)
    · exact zero _
    intro l hl _ φ hφ
    obtain ⟨t, pt, ht⟩ := hl (blk ϖ 0 1) (by simp [det_blk, h0])
    have a := ht φ hφ
    have e : ∀ y : Matrix (Fin 0) (Fin (d + 1)) k, y * blk ϖ (0 : Fin d → k) 1 = y := fun y => by ext i; exact i.elim0
    simp only [e, det_blk, det_one, mul_one] at a
    by_contra h
    exact hϖ t pt (mul_right_cancel₀ h (by rw [← a, one_mul]))
  | succ n ih =>
    rintro (_ | d)
    · exact zero _
    exact fun l hl hd => step_closed (ih _) hl hd (step_row hc hl (step_chart hc h0 h1 (ih d) hl hd))

end GlobalTheory.ThK.Dbl.LD
