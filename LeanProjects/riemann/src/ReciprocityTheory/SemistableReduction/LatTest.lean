import ReciprocityTheory.SemistableReduction.LatSemiSt

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ratEmb_conj (σ : ℚ →+* ℂ) (x : ℚ) : σ x = conj (σ x) := by
  rw [eq_ratCast σ x, map_ratCast]

def ratHermitianOne : HermForm ℚ 1 where
  c := RingHom.id ℚ
  c_invol := fun _ => rfl
  c_emb := fun σ x => ratEmb_conj σ x
  G := 1
  G_herm := fun a b => by rw [Subsingleton.elim a b]; rfl

def ratMajorantOne : Majorant ratHermitianOne where
  H := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  major := fun σ => by simp [ratHermitianOne]
  conj_compat := fun σ => by simp

def hermQ (r : ℕ) : HermForm ℚ r where
  c := RingHom.id ℚ
  c_invol := fun _ => rfl
  c_emb := fun σ x => ratEmb_conj σ x
  G := 1
  G_herm := fun a b => by
    by_cases h : a = b
    · subst h; rfl
    · simp [h, Ne.symm h]

def majQ (r : ℕ) : Majorant (hermQ r) where
  H := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  major := fun σ => by simp [hermQ]
  conj_compat := fun σ => by simp

example (a : ℕ) : IsTriEquivariant (fun _ : Fin 1 => a) (fun x => x 0 0 ^ a) := by
  intro x b _ _ _
  simp [triChar, Matrix.mul_apply, mul_pow, mul_comm]

example (c : ℂ) : IsTriEquivariant (fun _ : Fin 0 => 0) (fun _ => c) := by
  intro x b _ _ _
  simp [triChar]

example (c : ℂ) : IsBW (fun _ : Fin 0 => 0) (fun _ => c) := by
  refine ⟨differentiableOn_const c, ?_, ?_⟩
  · intro x b _ _ _
    simp [triChar]
  · intro x hx
    simp at hx

example : IsOpen (Metric.ball (0 : ℂ) 1) ∧ Balanced ℂ (Metric.ball (0 : ℂ) 1) ∧
    DifferentiableOn ℂ (fun z : ℂ => z) (Metric.ball 0 1) ∧
    ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖(fun z : ℂ => z) w‖ ≤ 1 := by
  refine ⟨Metric.isOpen_ball, balanced_ball_zero, differentiableOn_id, fun w hw => ?_⟩
  simpa using (Metric.mem_ball.mp hw).le

example : let V := EuclideanSpace ℂ (Fin 0)
    Differentiable ℂ (fun _ : V => (1 : ℂ)) ∧ (∃ _z : V, (1 : ℂ) ≠ 0) ∧
    (∀ v : V, ∃ l ∈ (⊤ : AddSubgroup V), ‖v - l‖ ≤ 0) ∧ 5 * (0 : ℝ) < (1 : ℕ) := by
  refine ⟨differentiable_const 1, ⟨0, one_ne_zero⟩, fun v => ⟨v, trivial, by simp⟩, by norm_num⟩

example (x y : Fin 1 → ℂ) : jForm 1 x y = conj (x 0) * y 0 := by
  simp [jForm, sgn]

example : (Real.exp (1 / 3) + 1) * ((1 : ℕ) : ℝ) < ((4 : ℕ) : ℝ) := by
  have h1 : Real.exp (1 / 3) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
  have h2 := Real.exp_one_lt_d9
  push_cast
  linarith

example (r : ℕ) (u : Fin r → ℂ) :
    normSq (((1 : Matrix (Fin r) (Fin r) ℂ) * (1 : Matrix (Fin r) (Fin r) ℚ).map (Rat.castHom ℂ) *
      (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹) *ᵥ u) ≤ Real.exp (2 / (3 * (r : ℝ))) * normSq u := by
  have h0 : 0 ≤ normSq u := Finset.sum_nonneg fun k _ => by positivity
  have h1 : 1 ≤ Real.exp (2 / (3 * (r : ℝ))) := Real.one_le_exp (by positivity)
  simp only [Matrix.map_one, map_zero, map_one, inv_one, mul_one, one_mulVec]
  nlinarith

example (x : Matrix (Fin 1) (Fin 1) ℂ) : leadMinor x 0 = x 0 0 := by
  simp [leadMinor, Matrix.det_unique]

abbrev QI : Type := CyclotomicField 4 ℚ

instance : IsCyclotomicExtension {4} ℚ QI := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension (n := 4) (K := ℚ)

instance : IsCMField QI :=
  IsCyclotomicExtension.Rat.isCMField QI (S := {4}) ⟨4, rfl, by norm_num⟩

example : Nonempty (QI →+* ℂ) := inferInstance

def hermQI : HermForm QI 1 where
  c := (IsCMField.complexConj QI : QI →+* QI)
  c_invol := fun x => IsCMField.complexConj_apply_apply QI x
  c_emb := fun σ x => IsCMField.complexEmbedding_complexConj QI σ x
  G := 1
  G_herm := fun a b => by rw [Subsingleton.elim a b]; simp

def intLat (K : Type) [Field K] [NumberField K] (r : ℕ) : Submodule (𝓞 K) (Fin r → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)

theorem mem_intLat {K : Type} [Field K] [NumberField K] {r : ℕ} (x : Fin r → K) :
    x ∈ intLat K r ↔ ∀ a, IsIntegralElt (x a) := by
  simp only [intLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  rfl

theorem hermQI_h (x y : Fin 1 → QI) :
    hermQI.h x y = IsCMField.complexConj QI (x 0) * y 0 := by
  simp [HermForm.h, hermQI]

theorem emb_zeta4 (φ : QI →+* ℂ) :
    ∃ s : ℤ, s ^ 2 = 1 ∧ φ (IsCyclotomicExtension.zeta 4 ℚ QI) = s * Complex.I := by
  have hz := IsCyclotomicExtension.zeta_spec 4 ℚ QI
  have h4 : (φ (IsCyclotomicExtension.zeta 4 ℚ QI)) ^ 4 = 1 := by
    rw [← map_pow, hz.pow_eq_one, map_one]
  have hp : IsPrimitiveRoot (φ (IsCyclotomicExtension.zeta 4 ℚ QI)) 4 :=
    hz.map_of_injective φ.injective
  set z := φ (IsCyclotomicExtension.zeta 4 ℚ QI)
  have h2 : z ^ 2 ≠ 1 := by
    intro h
    have := hp.dvd_of_pow_eq_one 2 h
    norm_num at this
  have hsq : z ^ 2 = -1 := by
    have : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
      have : (z ^ 2 - 1) * (z ^ 2 + 1) = z ^ 4 - 1 := by ring
      rw [this, h4, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) h2
    · exact eq_neg_of_add_eq_zero_left h
  have hf : (z - Complex.I) * (z + Complex.I) = 0 := by
    have : (z - Complex.I) * (z + Complex.I) = z ^ 2 - Complex.I ^ 2 := by ring
    rw [this, hsq, Complex.I_sq, sub_self]
  rcases mul_eq_zero.1 hf with h | h
  · exact ⟨1, by norm_num, by rw [sub_eq_zero.1 h]; simp⟩
  · exact ⟨-1, by norm_num, by rw [eq_neg_of_add_eq_zero_left h]; simp⟩

theorem cover_QI (φ : QI →+* ℂ) (w : ℂ) : ∃ l : QI, IsIntegralElt l ∧ ‖φ l - w‖ ^ 2 ≤ 1 := by
  obtain ⟨s, hs, he⟩ := emb_zeta4 φ
  have hz := IsCyclotomicExtension.zeta_spec 4 ℚ QI
  have hint : IsIntegral ℤ (IsCyclotomicExtension.zeta 4 ℚ QI) := hz.isIntegral (by norm_num)
  set ζ := IsCyclotomicExtension.zeta 4 ℚ QI with hζ
  set a : ℤ := round w.re with ha_def
  set b : ℤ := round w.im with hb_def
  refine ⟨(a : QI) + ((s * b : ℤ) : QI) * ζ, ?_, ?_⟩
  · refine ⟨(a : 𝓞 QI) + ((s * b : ℤ) : 𝓞 QI) * ⟨ζ, hint⟩, ?_⟩
    simp only [map_add, map_mul, map_intCast]
    rfl
  · have hs' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
    have h1 : φ ((a : QI) + ((s * b : ℤ) : QI) * ζ) = (a : ℂ) + (b : ℂ) * Complex.I := by
      rw [map_add, map_mul, map_intCast, map_intCast, he]
      push_cast
      linear_combination (b : ℂ) * Complex.I * hs'
    rw [h1]
    have hre : ((a : ℂ) + (b : ℂ) * Complex.I - w).re = (a : ℝ) - w.re := by simp
    have him : ((a : ℂ) + (b : ℂ) * Complex.I - w).im = (b : ℝ) - w.im := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have ha := abs_sub_round w.re
    have hb := abs_sub_round w.im
    rw [abs_le] at ha hb
    nlinarith [ha.1, ha.2, hb.1, hb.2]

theorem approx_hyps_QI (φ : QI →+* ℂ) :
    let σ : Unit → QI →+* ℂ := fun _ => φ
    let Q : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
    let v : Fin 1 → Fin 1 → QI := fun _ _ => 1
    1 ≤ 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (∀ i, (Q i).det ≠ 0) ∧
    (∀ i x y, σ i (hermQI.h x y) =
      jForm 1 (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) ∧
    IsIntegralOn hermQI (intLat QI 1) ∧
    (∀ w : Unit → Fin 1 → ℂ, ∃ l ∈ intLat QI 1,
      ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ (1 : ℝ) ^ 2) ∧
    (∀ j, v j ∈ intLat QI 1) ∧ LinearIndependent QI v ∧
    (∀ j, majSq σ Q (v j) ≤ (1 : ℝ) ^ 2) := by
  intro σ Q v
  refine ⟨le_rfl, one_pos, one_pos, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [Q]
  · intro i x y
    show φ (hermQI.h x y) = _
    rw [hermQI_h, map_mul, IsCMField.complexEmbedding_complexConj]
    simp [jForm, sgn, embVec, Q, σ]
  · intro x hx y hy
    rw [hermQI_h]
    rw [mem_intLat] at hx hy
    obtain ⟨z0, hz0⟩ := hx 0
    obtain ⟨z1, hz1⟩ := hy 0
    have hi : IsIntegral ℤ (IsCMField.complexConj QI (z0 : QI)) := by
      have := (NumberField.RingOfIntegers.isIntegral_coe z0).map
        ((IsCMField.complexConj QI : QI →+* QI)).toIntAlgHom
      simpa using this
    refine ⟨⟨_, hi⟩ * z1, ?_⟩
    show (IsCMField.complexConj QI (z0 : QI)) * (z1 : QI) = _
    rw [hz0, hz1]
  · intro w
    obtain ⟨l, hl, hn⟩ := cover_QI φ (w () 0)
    refine ⟨fun _ => l, (mem_intLat _).2 (fun _ => hl), ?_⟩
    simpa [normSq, embVec, Q, σ] using hn
  · intro j
    rw [mem_intLat]
    intro a
    exact ⟨1, by simp [v]⟩
  · refine linearIndependent_unique_iff.2 ?_
    intro h
    have := congrFun h 0
    simp [v] at this
  · intro j
    simp [majSq, normSq, embVec, Q, σ, v]

end ReciprocityTheory.MultiplicativeHeights
