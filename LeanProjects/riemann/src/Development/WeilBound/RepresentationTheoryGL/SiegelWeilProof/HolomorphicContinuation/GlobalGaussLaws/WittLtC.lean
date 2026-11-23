import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtB

open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def hyp : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

theorem cc_one : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)

theorem cc_zero : FD.cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)

theorem cc_neg (t : E) : FD.cc (-t) = -FD.cc t := map_neg (IsCMField.complexConj E) t

theorem cc_div_two (t : E) : FD.cc (t / 2) = FD.cc t / 2 := by
  show IsCMField.complexConj E (t / 2) = _
  rw [map_div₀, map_ofNat]
  rfl

theorem exists_pair {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) {z : n → E} (hz0 : z ≠ 0) (hz : hf G z z = 0) :
    ∃ w : n → E, hf G z w = 1 ∧ hf G w w = 0 := by
  have hu : z ᵥ* G ≠ 0 := by
    intro h
    apply hz0
    have h1 := congrArg (· ᵥ* G⁻¹) h
    simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at h1
    rwa [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det G).1 ((Matrix.isUnit_iff_isUnit_det G).2 hd.isUnit)),
      Matrix.vecMul_one] at h1
  obtain ⟨b, hb⟩ : ∃ b, (z ᵥ* G) b ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  set c := (z ᵥ* G) b with hc
  let v : n → E := c⁻¹ • Pi.single b 1
  let w0 : n → E := FD.cc ∘ v
  have hw0 : hf G z w0 = 1 := by
    have e1 : FD.cc ∘ w0 = v := by ext i; exact cc_cc (v i)
    simp only [hf]
    rw [e1, Matrix.dotProduct_mulVec]
    simp only [v, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hb
  set a := hf G w0 w0 with ha
  have haa : FD.cc a = a := by rw [ha, ← hf_symm hG]
  refine ⟨w0 + (-(a / 2)) • z, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hz, hw0]; ring
  · have hzw : hf G w0 z = 1 := by rw [hf_symm hG, hw0, cc_one]
    rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right, hf_smul_right, hz, hw0, hzw,
      cc_neg, cc_div_two, haa, ← ha]
    ring

set_option maxHeartbeats 1600000 in

theorem split {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) {z : n → E} (hz0 : z ≠ 0) (hz : hf G z z = 0) :
    ∃ (m : ℕ) (e : Fin 2 ⊕ Fin m ≃ n) (G2 : Matrix (Fin m) (Fin m) E) (P : Matrix n n E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm ∧ (∀ a b, FD.cc (G2 a b) = G2 b a) ∧
        G2.det ≠ 0 := by
  obtain ⟨w, hzw, hww⟩ := exists_pair hG hd hz0 hz
  have hwz : hf G w z = 1 := by rw [hf_symm hG, hzw, cc_one]
  let L : (n → E) →ₗ[E] (Fin 2 → E) :=
    { toFun := fun x => ![hf G x z, hf G x w]
      map_add' := fun x y => by ext i; fin_cases i <;> simp [hf_add_left]
      map_smul' := fun t x => by ext i; fin_cases i <;> simp [hf_smul_left] }
  have hLz : L z = ![0, 1] := by ext i; fin_cases i <;> simp [L, hz, hzw]
  have hLw : L w = ![1, 0] := by ext i; fin_cases i <;> simp [L, hwz, hww]
  have hLs : Function.Surjective L := by
    intro v
    refine ⟨v 0 • w + v 1 • z, ?_⟩
    rw [map_add, map_smul, map_smul, hLz, hLw]
    ext i; fin_cases i <;> simp
  set K := LinearMap.ker L
  have hrk : Module.finrank E K + 2 = Fintype.card n := by
    show Module.finrank E (LinearMap.ker L) + 2 = _
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hLs, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at h
    omega
  set m := Module.finrank E K
  let bK : Module.Basis (Fin m) E K := Module.finBasis E K
  have hK : ∀ i, hf G (bK i : n → E) z = 0 ∧ hf G (bK i : n → E) w = 0 := by
    intro i
    have h := (bK i).2
    rw [LinearMap.mem_ker] at h
    exact ⟨congrFun h 0, congrFun h 1⟩
  let cols : Fin 2 ⊕ Fin m → (n → E) := Sum.elim ![z, w] fun i => (bK i : n → E)
  have hcard : Fintype.card (Fin 2 ⊕ Fin m) = Fintype.card n := by simp; omega
  let e : Fin 2 ⊕ Fin m ≃ n := Fintype.equivOfCardEq hcard
  let G2 : Matrix (Fin m) (Fin m) E := fun i j => hf G (bK i : n → E) (bK j : n → E)
  let P : Matrix n n E := fun k j => cols (e.symm j) k
  have hentry : ∀ s t, hf G (cols s) (cols t) = fromBlocks hyp 0 0 G2 s t := by
    rintro (i | i) (j | j)
    · fin_cases i <;> fin_cases j <;> simp [cols, hyp, hz, hzw, hwz, hww]
    · fin_cases i
      · simp [cols]
        rw [hf_symm hG (bK j : n → E) z, (hK j).1, cc_zero]
      · simp [cols]
        rw [hf_symm hG (bK j : n → E) w, (hK j).2, cc_zero]
    · fin_cases j
      · simp [cols, (hK i).1]
      · simp [cols, (hK i).2]
    · rfl
  have hT : Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm := by
    ext a b
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply]
    exact hentry (e.symm a) (e.symm b)
  have hlin : ∀ (γ : Fin 2 ⊕ Fin m → E) (y : n → E),
      hf G (∑ s, γ s • cols s) y = ∑ s, γ s * hf G (cols s) y := by
    intro γ y
    let Ly : (n → E) →ₗ[E] E :=
      { toFun := fun x => hf G x y
        map_add' := fun x x' => hf_add_left G x x' y
        map_smul' := fun t x => hf_smul_left G t x y }
    have h1 : hf G (∑ s, γ s • cols s) y = Ly (∑ s, γ s • cols s) := rfl
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  have hP : P.det ≠ 0 := by
    have hinj : Function.Injective P.mulVec := by
      intro α β hαβ
      have h0 : P *ᵥ (α - β) = 0 := by rw [Matrix.mulVec_sub, hαβ, sub_self]
      set γ : n → E := α - β with hγ
      have hsum : ∑ s, γ (e s) • cols s = 0 := by
        rw [← h0]
        ext k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, P]
        rw [← e.sum_comp]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Equiv.symm_apply_apply]
        ring
      have hz1 : γ (e (Sum.inl 1)) = 0 := by
        have h := hlin (fun s => γ (e s)) z
        rw [hsum] at h
        have h' : ∑ s, γ (e s) * hf G (cols s) z = γ (e (Sum.inl 1)) := by
          have hc : ∀ s, hf G (cols s) z = fromBlocks hyp 0 0 G2 s (Sum.inl 0) := fun s => hentry s (Sum.inl 0)
          simp only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]
          simp
        rw [← h', ← h]
        simp [hf]
      have hw1 : γ (e (Sum.inl 0)) = 0 := by
        have h := hlin (fun s => γ (e s)) w
        rw [hsum] at h
        have h' : ∑ s, γ (e s) * hf G (cols s) w = γ (e (Sum.inl 0)) := by
          have hc : ∀ s, hf G (cols s) w = fromBlocks hyp 0 0 G2 s (Sum.inl 1) := fun s => hentry s (Sum.inl 1)
          simp only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]
          simp
        rw [← h', ← h]
        simp [hf]
      have hrest : ∑ i, γ (e (Sum.inr i)) • bK i = 0 := by
        apply Subtype.ext
        have := hsum
        simp only [Fintype.sum_sum_type, Fin.sum_univ_two, hz1, hw1, zero_smul, zero_add] at this
        simpa [cols] using this
      have hcoef := (Fintype.linearIndependent_iff.1 bK.linearIndependent) _ hrest
      have hγ0 : γ = 0 := by
        funext k
        obtain ⟨s, rfl⟩ := e.surjective k
        rcases s with i | i
        · fin_cases i
          · exact hw1
          · exact hz1
        · exact hcoef i
      have := congrFun hγ0
      funext k
      have hk := this k
      simp only [hγ, Pi.sub_apply, Pi.zero_apply] at hk
      exact sub_eq_zero.mp hk
    have hu : IsUnit P := Matrix.mulVec_injective_iff_isUnit.1 hinj
    exact ((Matrix.isUnit_iff_isUnit_det P).1 hu).ne_zero
  have hG2 : ∀ a b, FD.cc (G2 a b) = G2 b a := fun a b => (hf_symm hG _ _).symm
  have hdetP : (P.map FD.cc).det ≠ 0 := by
    have : (P.map FD.cc).det = IsCMField.complexConj E P.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) P).symm
    rw [this]
    exact (map_ne_zero _).2 hP
  have hdetT : ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).det ≠ 0 := by
    rw [← hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hP hd) hdetP
  have hG2d : G2.det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hdetT
    intro h
    rw [h, mul_zero] at hdetT
    exact hdetT rfl
  exact ⟨m, e, G2, P, hP, hT, hG2, hG2d⟩

end PositivityTheory.Rg.Sw.Glob.WLt

end
