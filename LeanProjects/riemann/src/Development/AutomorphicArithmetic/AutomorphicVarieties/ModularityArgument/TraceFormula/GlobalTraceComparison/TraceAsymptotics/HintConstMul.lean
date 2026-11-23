import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private def lin {κ : Type} (c : κ → ℂ) : List κ → Ex κ
  | [] => Ex.smul 0 Ex.one
  | p :: L => Ex.add (Ex.smul (c p) (Ex.gen p)) (lin c L)

private theorem ev_lin {κ : Type} (c x : κ → ℂ) (L : List κ) :
    (lin c L).ev x = (L.map fun p => c p * x p).sum := by
  induction L with
  | nil => simp [lin, Ex.ev]
  | cons p L ih => simp [lin, Ex.ev, ih]

private theorem fn_lin {κ : Type} {G : Type} [Group G] (K : Subgroup G) (g : κ → G → ℂ) (c : κ → ℂ)
    (L : List κ) (y : G) : (lin c L).fn K g y = (L.map fun p => c p * g p y).sum := by
  induction L with
  | nil => simp [lin, Ex.fn]
  | cons p L ih => simp [lin, Ex.fn, ih]

private theorem ev_bind {ι κ : Type} (x : κ → ℂ) (τ : ι → Ex κ) (e : Ex ι) :
    (e.bind τ).ev x = e.ev fun i => (τ i).ev x := by
  induction e with
  | one => rfl
  | gen i => rfl
  | smul c a ih => simp [Ex.bind, Ex.ev, ih]
  | add a b iha ihb => simp [Ex.bind, Ex.ev, iha, ihb]
  | mul a b iha ihb => simp [Ex.bind, Ex.ev, iha, ihb]

private theorem hint_const_mul {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (hc : c ≠ 0) (u : H → ℂ) :
    hint K (fun z => c * u z) = c * hint K u := by
  have hs : rStab (fun z => c * u z) = rStab u := by
    ext g
    simp [rStab, hc]
  unfold hint
  rw [hs]
  have := smul_finsum (M := ℂ) c (fun q : H ⧸ (rStab u ⊓ K) => u q.out)
  simp only [smul_eq_mul] at this
  rw [← mul_assoc, mul_comm c, mul_assoc, this]

private def tco (q a b : ℕ) (c₁ c₂ : ℂˣ) (j : ℕ) (p : Fin (a + 1) × Fin (b + 1)) : ℂ :=
  cf q a b j p * (c₁ : ℂ) ^ (p.1 : ℕ) * (c₂ : ℂ) ^ (p.2 : ℕ)

private def tEx (q a b : ℕ) (c₁ c₂ : ℂˣ) (j : ℕ) : Ex (Fin (a + 1) × Fin (b + 1)) :=
  lin (tco q a b c₁ c₂ j) Finset.univ.toList

private theorem ev_tEx (q a b : ℕ) (c₁ c₂ : ℂˣ) (j : ℕ) (x : Fin (a + 1) × Fin (b + 1) → ℂ) :
    (tEx q a b c₁ c₂ j).ev x = ∑ p, tco q a b c₁ c₂ j p * x p := by
  rw [tEx, ev_lin]
  exact Finset.sum_map_toList _ _

private theorem fn_tEx {G : Type} [Group G] (K : Subgroup G) (q a b : ℕ) (c₁ c₂ : ℂˣ) (j : ℕ)
    (g : Fin (a + 1) × Fin (b + 1) → G → ℂ) (y : G) :
    (tEx q a b c₁ c₂ j).fn K g y = ∑ p, tco q a b c₁ c₂ j p * g p y := by
  rw [tEx, fn_lin]
  exact Finset.sum_map_toList _ _

theorem rCtEx : RCtEx := by
  intro hEx hLin hUnit hT hMul hSat hMu _ E _ _ _ w hs μ hμ n a b h
  subst h
  have hq : qV E w ≠ 0 := by
    unfold qV
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  obtain ⟨hK, hmul, hval⟩ := hMu E w μ hμ a b
  have hy : ∀ y : GLw (a + b) w, ((toSub (UL (a + b) w) y : UL (a + b) w) : GLw (a + b) w) = y := by
    intro y
    have hm : y ∈ UL (a + b) w := by simp [UL, hs]
    simp [toSub, hm]
  have hne : ∀ m, chi μ a b w m ≠ 0 := fun m => Units.ne_zero _
  let t : Fin (a + b + 1) → Ex (Fin (a + 1) × Fin (b + 1)) :=
    fun j => tEx (qV E w) a b (μ.val w ^ b) (μ.val w ^ a) j
  have key : ∀ e : Ex (Fin (a + b + 1)),
      (fun m => chi μ a b w m * ct rfl w (fn1 (a + b) w e) m) = fn2 a b w (e.bind t) := by
    intro e
    induction e with
    | one =>
      funext m
      show chi μ a b w m * ct rfl w ((KGL w (a + b) : Set _).indicator 1) m = (K2 a b w : Set _).indicator 1 m
      rw [hUnit E w (a + b) a b rfl]
      by_cases hm : m ∈ K2 a b w
      · simp [Set.indicator, hm, hK m hm]
      · simp [Set.indicator, hm]
    | gen j =>
      funext m
      show chi μ a b w m * ct rfl w (Tj ℂ (a + b) (Ov E w) (unif w) j) m =
        (t j).fn (K2 a b w) (fun p y => Tj ℂ a (Ov E w) (unif w) p.1 y.1 * Tj ℂ b (Ov E w) (unif w) p.2 y.2) m
      rw [hT E w (a + b) a b rfl j m, fn_tEx, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h0 : Tj ℂ a (Ov E w) (unif w) p.1 m.1 * Tj ℂ b (Ov E w) (unif w) p.2 m.2 = 0
      · simp [h0]
      · rw [hval p.1 p.2 m (Nat.lt_succ_iff.mp p.1.2) (Nat.lt_succ_iff.mp p.2.2) h0]
        simp only [tco]
        ring
    | smul c e ih =>
      have h1 : fn1 (a + b) w (Ex.smul c e) = fun y => c * fn1 (a + b) w e y := rfl
      have hH := (hEx E (a + b) w e).1
      have h2 := (hLin E w (a + b) a b rfl _ _ c hH hH).2
      show _ = fun y => c * fn2 a b w (e.bind t) y
      rw [h1, h2, ← ih]
      funext m
      ring
    | add e₁ e₂ ih₁ ih₂ =>
      have h1 : fn1 (a + b) w (Ex.add e₁ e₂) = fun y => fn1 (a + b) w e₁ y + fn1 (a + b) w e₂ y := rfl
      have h2 := (hLin E w (a + b) a b rfl _ _ 1 (hEx E (a + b) w e₁).1 (hEx E (a + b) w e₂).1).1
      show _ = fun y => fn2 a b w (e₁.bind t) y + fn2 a b w (e₂.bind t) y
      rw [h1, h2, ← ih₁, ← ih₂]
      funext m
      ring
    | mul e₁ e₂ ih₁ ih₂ =>
      have h1 : fn1 (a + b) w (Ex.mul e₁ e₂) =
          cv (KGL w (a + b)) (fn1 (a + b) w e₁) (fn1 (a + b) w e₂) := rfl
      show _ = fun y => hint (K2 a b w) fun z => fn2 a b w (e₁.bind t) z * fn2 a b w (e₂.bind t) (z⁻¹ * y)
      rw [h1, hMul E w (a + b) a b rfl _ _ (hEx E (a + b) w e₁).1 (hEx E (a + b) w e₂).1, ← ih₁, ← ih₂]
      funext m
      show chi μ a b w m * hint (K2 a b w) (fun z => ct rfl w (fn1 (a + b) w e₁) z *
          ct rfl w (fn1 (a + b) w e₂) (z⁻¹ * m)) = _
      rw [← hint_const_mul _ _ (hne m)]
      congr 1
      funext z
      have hc : chi μ a b w m = chi μ a b w z * chi μ a b w (z⁻¹ * m) := by
        rw [← hmul, mul_inv_cancel_left]
      rw [hc]
      ring
  refine ⟨t, ?_, ?_⟩
  · intro e
    rw [← key e]
    funext m
    have hf : (fun y : GLw (a + b) w => (fun x : UL (a + b) w => fn1 (a + b) w e x.1) (toSub _ y)) =
        fn1 (a + b) w e := by
      funext y
      show fn1 (a + b) w e (toSub (UL (a + b) w) y : UL (a + b) w).1 = _
      rw [hy]
    unfold ctMu
    rw [hf]
    rfl
  · intro e B₁ B₂ h₁ h₂
    unfold ev2 ev1
    rw [ev_bind]
    congr 1
    funext j
    show (tEx (qV E w) a b (μ.val w ^ b) (μ.val w ^ a) j).ev _ = satEig (qV E w) (a + b) (un μ a b w B₁ B₂) j
    rw [ev_tEx]
    have := hSat (qV E w) a b hq B₁ B₂ (μ.val w ^ b) (μ.val w ^ a) h₁ h₂ j
    rw [show un μ a b w B₁ B₂ = B₁.map (· * μ.val w ^ b) + B₂.map (· * μ.val w ^ a) from rfl, this]
    rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
