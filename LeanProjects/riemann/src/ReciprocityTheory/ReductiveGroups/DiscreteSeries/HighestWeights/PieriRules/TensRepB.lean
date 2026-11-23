import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Lin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensL_add_left (m m' : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (m + m') S = tensL m S + tensL m' S := by
  ext x i
  simp [tensL_apply, add_smul, Finset.sum_add_distrib]

theorem tensL_smul_left (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (c • m) S = c • tensL m S := by
  ext x i
  simp [tensL_apply, mul_smul, Finset.smul_sum]

theorem tensL_add_right (m : Matrix ι ι ℂ) (S S' : V →L[ℂ] V) :
    tensL m (S + S') = tensL m S + tensL m S' := by
  ext x i
  simp [tensL_apply, smul_add, Finset.sum_add_distrib]

theorem tensL_smul_right (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL m (c • S) = c • tensL m S := by
  ext x i
  simp [tensL_apply, Finset.smul_sum, smul_comm c]

theorem tensL_one_apply (S : V →L[ℂ] V) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensL (1 : Matrix ι ι ℂ) S x i = S (x i) := by
  simp [tensL_apply, Matrix.one_apply]

theorem tensL_id_apply (m : Matrix ι ι ℂ) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensL m (1 : V →L[ℂ] V) x i = ∑ j, m i j • x j := by
  simp [tensL_apply]

end Lin

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]

def tensD (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) where
  toFun X := tensL (dρ X) 1 + tensL 1 (T.dτ X)
  map_add' X Y := by
    simp only [map_add, tensL_add_left, tensL_add_right]
    abel
  map_smul' c X := by
    simp only [map_smul, tensL_smul_left, tensL_smul_right, RingHom.id_apply, smul_add]

theorem tensD_apply (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensD T dρ X x i = T.dτ X (x i) + ∑ j, dρ X i j • x j := by
  simp [tensD, Matrix.one_apply, add_comm]

theorem tens_curve_zero {X : Matrix (Fin n) (Fin n) ℂ} (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ 0 = 1 := by
  apply onep_KG_ext
  rw [hγ]
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
  simp

theorem tensD_hasDeriv (ρ : KG ε →* unitary (Matrix ι ι ℂ))
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (hd : ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
      (dρ X i j) 0) :
    HasDerivAt (fun t : ℝ => ((tensTau T ρ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
      PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
      (tensD T dρ X) 0 := by
  have h0 := tens_curve_zero γ hγ
  have hD := hasDerivAt_tensL (V := T.V) hd (T.hasDeriv X hX γ hγ)
  simp only [tensTau_coe, tensOp_eq]
  convert hD using 1
  simp [tensD, h0]

theorem tensD_units (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (a b : Fin n) :
    ((tensD T dρ (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
      Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
      tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b := by
  refine LinearMap.ext fun x => PiLp.ext fun i => ?_
  simp [tensAct, tensD_apply, kunits]

include T in

def tensKRep (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) : KRep ε where
  V := PiLp 2 (fun _ : ι => T.V)
  τ := tensTau T ρ
  cont := tensTau_cont T ρ hc
  dτ := tensD T dρ
  hasDeriv X hX γ hγ := tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ)

theorem tensKRep_units (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) :
    (tensKRep T ρ dρ hc hd).units = tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) :=
  funext fun a => funext fun b => tensD_units T dρ a b

theorem tensKRep_op (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) (k : KG ε) :
    (tensKRep T ρ dρ hc hd).op k = tensOp T ρ k :=
  tensTau_coe T ρ k

theorem tensRep : TensRepStatement := by
  intro n ε Λ T ι _ _ ρ dρ hc hd
  exact ⟨tensTau T ρ, tensD T dρ, tensTau_cont T ρ hc,
    fun X hX γ hγ => tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ), fun a b => tensD_units T dρ a b⟩

end ReciprocityTheory.ChartRestriction.DS.HW
