import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TorsStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.GroupHomologyLongExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImageRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.L1MapDomainLeAndL1FaceDSingleLe

open CategoryTheory

namespace UpperTheory.V.KH

theorem shift (G : Type) [Group G] (A s b : ℕ) (hs : 1 ≤ s) (hb : 1 ≤ b) (m : ℕ) :
    ∀ (X : ℕ → Type) [∀ p, MulAction G (X p)]
      (d : ∀ p, permRep G (X (p + 1)) ⟶ permRep G (X p)) (M : Rep ℤ G) (e : permRep G (X 0) ⟶ M),
      Function.Surjective e.hom → Function.Exact (d 0).hom e.hom →
      (∀ p, p < m → Function.Exact (d (p + 1)).hom (d p).hom) →
      (∀ p, p ≤ m → OrbLe G (X p) A) → (∀ p, p ≤ m → StabLe G (X p) s) →
      (∀ y : X (m + 1), l1 ((d m).hom (Finsupp.single y 1)) ≤ b) →
      TorsLe (groupHomology M m) (bound m A s b) := by
  induction m with
  | zero =>
    intro X _ d M e he h0 _ ho _ hl
    have := base G (X 0) (X 1) M e (d 0).hom.toLinearMap A b he h0 (ho 0 le_rfl) hb hl
    simpa [bound] using this
  | succ m ih =>
    intro X _ d M e he h0 hx ho hst hl
    obtain ⟨K, p, i, hp, hi, hpi, hie⟩ := imageRep G _ _ _ (d 0) e h0
    have h1 : Function.Exact (d 1).hom p.hom := by
      intro y
      rw [← hx 0 (Nat.succ_pos m) y, ← hpi y]
      constructor
      · intro h; rw [h, map_zero]
      · intro h; exact hi (by rw [h, map_zero])
    have hK := ih (fun q => X (q + 1)) (fun q => d (q + 1)) K p hp h1
      (fun q hq => hx (q + 1) (by omega)) (fun q hq => ho (q + 1) (by omega))
      (fun q hq => hst (q + 1) (by omega)) hl
    have hC := permCard G s m A (X 0) (ho 0 (by omega)) (hst 0 (by omega)) hs
    obtain ⟨u, v, huv⟩ := (les G _ _ _ i e hi hie he m).2
    refine transport.2.2.1 _ _ _ ?_ (torsStep _ _ _ u v _ _ huv hC hK)
    unfold bound
    rw [mul_left_comm, ← pow_add]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hs ?_)
    have : s ^ m ≤ s ^ (m + 1) := Nat.pow_le_pow_right hs (by omega)
    have h2 := Nat.mul_le_mul_left (m * A) this
    nlinarith

theorem main (G : Type) [Group G] (X : ℕ → Type) [∀ p, MulAction G (X p)] (C : PermCx G X)
    (m A s b : ℕ) (hs : 1 ≤ s) (hb : 1 ≤ b) (hx : C.ExactTo m)
    (ho : ∀ p, p ≤ m → OrbLe G (X p) A) (hst : ∀ p, p ≤ m → StabLe G (X p) s)
    (hl : ∀ y : X (m + 1), l1 (C.d m (Finsupp.single y 1)) ≤ b) :
    TorsLe (HZ G m) (bound m A s b) :=
  shift G A s b hs hb m X
    (fun p => Rep.ofHom ⟨C.d p, fun g => LinearMap.ext fun f => C.d_equiv p g f⟩)
    (Rep.trivial ℤ G ℤ) (Rep.ofHom ⟨C.ε, fun g => LinearMap.ext fun f => C.ε_equiv g f⟩)
    hx.1 hx.2.1 hx.2.2 ho hst hl

theorem mainFace (G : Type) [Group G] (X : ℕ → Type) [∀ p, MulAction G (X p)]
    (face : ∀ p, Fin (p + 2) → X (p + 1) → X p)
    (h : ∀ p i (g : G) (x : X (p + 1)), face p i (g • x) = g • face p i x)
    (m A s : ℕ) (hs : 1 ≤ s) (hx : FaceExactTo X face m)
    (ho : ∀ p, p ≤ m → OrbLe G (X p) A) (hst : ∀ p, p ≤ m → StabLe G (X p) s) :
    TorsLe (HZ G m) (bound m A s (m + 2)) :=
  main G X (faceCx G X face h) m A s (m + 2) hs (by omega) hx ho hst
    (fun y => l1_mapDomain_le_and_l1_faceD_single_le.2 _ _ _ (face m) y)

theorem log_bound (m A s b : ℕ) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    Real.log (bound m A s b) = A * Real.log b + m * A * (s : ℝ) ^ m * Real.log s := by
  have h1 : (0 : ℝ) < s := by exact_mod_cast hs
  have h2 : (0 : ℝ) < b := by exact_mod_cast hb
  unfold bound
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem TorsLe.log_le {M : Type} [AddCommGroup M] {m A s b : ℕ} (hs : 1 ≤ s) (hb : 1 ≤ b)
    (h : TorsLe M (bound m A s b)) :
    Real.log (Nat.card (AddCommGroup.torsion M)) ≤
      A * Real.log b + m * A * (s : ℝ) ^ m * Real.log s := by
  rw [← log_bound m A s b hs hb]
  haveI := h.1
  have : 0 < Nat.card (AddCommGroup.torsion M) := Nat.card_pos
  exact Real.log_le_log (by exact_mod_cast this) (by exact_mod_cast h.2)

end UpperTheory.V.KH

namespace UpperTheory.V.KH

theorem TorsLe.log_le_exp {M : Type} [AddCommGroup M] {m A s : ℕ} {a σ : ℝ} (hs : 1 ≤ s)
    (hA : (A : ℝ) ≤ Real.exp a) (hσ : (s : ℝ) ≤ Real.exp σ)
    (h : TorsLe M (bound m A s (m + 2))) :
    Real.log (Nat.card (AddCommGroup.torsion M)) ≤ Real.exp (a + (m + 1) * σ + 2 * m) := by
  refine (h.log_le hs (by omega)).trans ?_
  have h1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have h2 : Real.log ((m + 2 : ℕ) : ℝ) ≤ m + 1 := by
    have := Real.log_le_sub_one_of_pos (x := ((m + 2 : ℕ) : ℝ)) (by positivity)
    push_cast at this ⊢; linarith
  have h3 : Real.log s ≤ s := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have h4 : (1 : ℝ) ≤ (s : ℝ) ^ (m + 1) := one_le_pow₀ h1
  have h5 : (s : ℝ) ^ (m + 1) ≤ Real.exp ((m + 1) * σ) := by
    have := pow_le_pow_left₀ (by positivity) hσ (m + 1)
    rw [← Real.exp_nat_mul] at this
    exact_mod_cast this
  have h6 : (2 * m + 1 : ℝ) ≤ Real.exp (2 * m) := Real.add_one_le_exp _
  have h7 : (s : ℝ) ^ m * Real.log s ≤ (s : ℝ) ^ (m + 1) := by
    rw [pow_succ]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
  calc (A : ℝ) * Real.log ((m + 2 : ℕ) : ℝ) + m * A * (s : ℝ) ^ m * Real.log s
      ≤ A * ((m + 1) * (s : ℝ) ^ (m + 1)) + m * A * (s : ℝ) ^ (m + 1) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (h2.trans ?_) hA0) ?_
        · exact le_mul_of_one_le_right (by positivity) h4
        · rw [mul_assoc (m * A : ℝ)]
          exact mul_le_mul_of_nonneg_left h7 (by positivity)
    _ = A * (s : ℝ) ^ (m + 1) * (2 * m + 1) := by ring
    _ ≤ Real.exp a * Real.exp ((m + 1) * σ) * Real.exp (2 * m) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]

end UpperTheory.V.KH
