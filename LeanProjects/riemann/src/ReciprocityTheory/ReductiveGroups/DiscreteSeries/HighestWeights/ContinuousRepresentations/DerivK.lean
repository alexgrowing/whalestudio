import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Blocks

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma onepCurve_zero (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    onepCurve ε hX 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simp [onepCurve]

lemma hasDerivAt_mul_of_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : ℝ → A} {a b : A}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    HasDerivAt (fun t => f t * g t) (a + b) 0 := by
  have h := hf.mul hg
  rw [hf0, hg0, one_mul, mul_one] at h
  exact h

theorem derivExists_of_split (h : DerivExistsAllPosStatement) (ε : Fin n → Bool)
    (p : Bool → ℕ) (emb : ∀ s, KG (fun _ : Fin (p s) => true) →* KG ε)
    (hemb : ∀ s, Continuous (emb s))
    (blk : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (p s)) (Fin (p s)) ℂ)
    (hblk : ∀ s X, inK ε X → inK (fun _ : Fin (p s) => true) (blk s X))
    (hsplit : ∀ X (hX : inK ε X) (t : ℝ),
      toMK (emb true (onepCurve _ (hblk true X hX) t)) *
          toMK (emb false (onepCurve _ (hblk false X hX) t)) =
        NormedSpace.exp ((t : ℂ) • X))
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (τ : KG ε →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) :
    ∃ dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V),
      ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
        (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0 := by
  choose dτs hdτs using fun s => h (p s) V (τ.comp (emb s)) (hτ.comp (hemb s))
  refine ⟨(dτs true).comp (blk true) + (dτs false).comp (blk false), fun X hX γ hγ => ?_⟩
  have hγeq : ∀ t, γ t = emb true (onepCurve _ (hblk true X hX) t) *
      emb false (onepCurve _ (hblk false X hX) t) := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact (hγ t).trans (hsplit X hX t).symm
  have hd1 := hdτs true (blk true X) (hblk true X hX) (onepCurve _ (hblk true X hX))
    (toMK_onepCurve _ (hblk true X hX))
  have hd2 := hdτs false (blk false X) (hblk false X hX) (onepCurve _ (hblk false X hX))
    (toMK_onepCurve _ (hblk false X hX))
  have hprod := hasDerivAt_mul_of_one hd1 hd2 (by simp [onepCurve_zero]) (by simp [onepCurve_zero])
  have hfun : (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) =
      fun t => (((τ.comp (emb true)) (onepCurve _ (hblk true X hX) t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) *
        (((τ.comp (emb false)) (onepCurve _ (hblk false X hX) t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
    funext t
    rw [hγeq t, map_mul]
    rfl
  rw [hfun]
  simpa using hprod

theorem derivExists_of (h : DerivExistsAllPosStatement) : DerivExistsStatement := by
  intro n ε V _ _ _ τ hτ
  refine derivExists_of_split h ε (blkP ε) (blkEmbed ε) (continuous_blkEmbed ε) (blkRes ε)
    (fun s X hX => inK_blkRes hX s) (fun X hX t => ?_) V τ hτ
  have hc := blk_curve hX (onepCurve ε hX) (toMK_onepCurve ε hX)
    (onepCurve _ (inK_blkRes hX true)) (toMK_onepCurve _ (inK_blkRes hX true))
    (onepCurve _ (inK_blkRes hX false)) (toMK_onepCurve _ (inK_blkRes hX false)) t
  have h1 := congrArg toMK hc
  rw [toMK_onepCurve] at h1
  exact h1.symm

end ReciprocityTheory.ChartRestriction.DS.HW
