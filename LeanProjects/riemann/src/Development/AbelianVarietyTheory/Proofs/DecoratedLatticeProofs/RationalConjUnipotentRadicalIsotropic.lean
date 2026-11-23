import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst

noncomputable section

open NumberField Matrix Formalism.MainNotions.S Formalism.UG

namespace GlobalTheory.CuspGeo

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (hg : cT s g * J * g = J) (x y : Fin n → A) : hform s J (g *ᵥ x) (g *ᵥ y) = hform s J x y := by
  have h1 : ∀ x y : Fin n → A, hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := fun x y => by
    simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, Function.comp_apply]
  have h2 : s ∘ (g *ᵥ x) = g.map s *ᵥ (s ∘ x) := funext fun i => RingHom.map_mulVec s g x i
  rw [h1, h1, h2]
  conv_rhs => rw [← hg, ← mulVec_mulVec, ← mulVec_mulVec, cT, mulVec_transpose]
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm]

theorem inUnipRad_conj (I : AutInst) {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA WA' : Submodule A (Fin I.n → A)) (g gi m : Matrix (Fin I.n) (Fin I.n) A) (hgi : gi * g = 1)
    (hU : ∀ x y, hform s JA (g *ᵥ x) (g *ᵥ y) = hform s JA x y) (h1 : ∀ x ∈ WA, g *ᵥ x ∈ WA')
    (h2 : ∀ y ∈ WA', ∃ x ∈ WA, y = g *ᵥ x) (hm : I.InUnipRad s JA WA' m) :
    I.InUnipRad s JA WA (gi * m * g) := by
  obtain ⟨m1, m2, m3⟩ := hm
  have e : gi * m * g - 1 = gi * (m - 1) * g := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgi]
  have e' : ∀ z, (gi * m * g - 1) *ᵥ z = gi *ᵥ ((m - 1) *ᵥ (g *ᵥ z)) := fun z => by
    rw [e, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have back : ∀ x, gi *ᵥ (g *ᵥ x) = x := fun x => by rw [mulVec_mulVec, hgi, one_mulVec]
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
  · rw [e', m1 _ (h1 x hx), mulVec_zero]
  · have hy' : g *ᵥ y ∈ {y | ∀ x ∈ WA', hform s JA x y = 0} := fun x' hx' => by
      obtain ⟨x, hx, rfl⟩ := h2 x' hx'
      rw [hU]; exact hy x hx
    obtain ⟨x, hx, hxe⟩ := h2 _ (m2 _ hy')
    rw [e', hxe, back]; exact hx
  · rw [e', ← hU, mulVec_mulVec _ g gi, mul_eq_one_comm.1 hgi, one_mulVec]
    exact m3 (g *ᵥ y) _ (h1 x hx)

theorem span_map_mulVec {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ} (c : Matrix (Fin n) (Fin n) E)
    (W : Submodule E (Fin n → E)) :
    (∀ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)),
      c.map ι *ᵥ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _))) ∧
    ∀ y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _)),
      ∃ x ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)), y = c.map ι *ᵥ x := by
  have key : ∀ w : Fin n → E, (c.map ι *ᵥ fun i => ι (w i)) = fun i => ι ((c *ᵥ w) i) := fun w =>
    funext fun i => (RingHom.map_mulVec ι c w i).symm
  constructor
  · intro x hx
    have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _)) ≤
        (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _))).comap
          (c.map ι).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, mulVecLin_apply, key]
      exact Submodule.subset_span ⟨c *ᵥ w, ⟨w, hw, rfl⟩, rfl⟩
    exact this hx
  · intro y hy
    have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W.map c.mulVecLin : Set _)) ≤
        (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set _))).map (c.map ι).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨w, hw, rfl⟩, by rw [mulVecLin_apply, key]; rfl⟩
    obtain ⟨x, hx, rfl⟩ := this hy
    exact ⟨x, hx, rfl⟩

theorem naconj : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧
    ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  intro I γ hγ W hW
  obtain ⟨c, hcU, hinf, hfin⟩ := hγ
  have hcU' : cT (starRingEnd I.E) (c : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * (c : Matrix (Fin I.n) (Fin I.n) I.E) =
      I.J := hcU
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  refine ⟨W.map (c : Matrix (Fin I.n) (Fin I.n) I.E).mulVecLin, ⟨?_, ?_⟩, fun m hm => ?_⟩
  · intro h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
    have : (c : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = 0 := by
      rw [← Submodule.mem_bot I.E, ← h]
      exact ⟨w, hw, rfl⟩
    apply hw0
    rw [← one_mulVec w, ← c.inv_mul, ← mulVec_mulVec, this, mulVec_zero]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, hform_mulVec_mulVec _ _ _ hcU']
    exact hW.2 x hx y hy
  obtain ⟨hmi, hmf⟩ := hm
  refine ⟨fun v => ?_, ?_⟩
  · have hst : ∀ y : I.E, I.φ v (star y) = star (I.φ v y) := fun y => hcm.2.2.2 (I.φ v) y
    have hPd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
    have hPP : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ hPd
    have hPP' : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPd
    have hg : I.P v * uMat (γ.1 v) * (I.P v)⁻¹ = (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) := by
      rw [hinf v, Matrix.mul_assoc, Matrix.mul_assoc, hPP', Matrix.mul_one, ← Matrix.mul_assoc, hPP',
        Matrix.one_mul]
    have hu : ∀ a : Formalism.REAL.UJ (I.ε v), uMat a⁻¹ * uMat a = 1 := fun a => by simp [uMat]
    have hmul : ∀ a b : Formalism.REAL.UJ (I.ε v), uMat (a * b) = uMat a * uMat b := fun a b => by simp [uMat]
    have hgi : (I.P v * uMat ((γ.1 v)⁻¹) * (I.P v)⁻¹) * (I.P v * uMat (γ.1 v) * (I.P v)⁻¹) = 1 := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hPd]
      rw [← Matrix.mul_assoc (uMat _), hu, Matrix.one_mul, hPP']
    have hconj : I.P v * uMat ((γ⁻¹ * m * γ).1 v) * (I.P v)⁻¹ = (I.P v * uMat ((γ.1 v)⁻¹) * (I.P v)⁻¹) *
        (I.P v * uMat (m.1 v) * (I.P v)⁻¹) * (I.P v * uMat (γ.1 v) * (I.P v)⁻¹) := by
      show I.P v * uMat ((γ.1 v)⁻¹ * m.1 v * γ.1 v) * (I.P v)⁻¹ = _
      rw [hmul, hmul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hPd]
    have hU : cT (starRingEnd ℂ) ((c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.J.map (I.φ v) *
        (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      have e : cT (starRingEnd ℂ) ((c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
          (cT (starRingEnd I.E) (c : Matrix (Fin I.n) (Fin I.n) I.E)).map (I.φ v) := by
        ext a b
        simp only [cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
        exact (hst _).symm
      rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hcU']
    obtain ⟨s1, s2⟩ := span_map_mulVec (I.φ v) (c : Matrix (Fin I.n) (Fin I.n) I.E) W
    rw [hconj]
    refine inUnipRad_conj I _ _ _ _ _ _ _ hgi ?_ ?_ ?_ (hmi v)
    · rw [hg]; exact hform_mulVec_mulVec _ _ _ hU
    · rw [hg]; exact s1
    · rw [hg]; exact s2
  · have hfm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by simp [AutInst.fmat]
    have hgi : I.fmat γ.2⁻¹ * I.fmat γ.2 = 1 := by rw [← hfm, inv_mul_cancel]; simp [AutInst.fmat]
    have hconj : I.fmat (γ⁻¹ * m * γ).2 = I.fmat γ.2⁻¹ * I.fmat m.2 * I.fmat γ.2 := by
      show I.fmat (γ.2⁻¹ * m.2 * γ.2) = _
      rw [hfm, hfm]
    have hU : cT (sigR I.cm.sig (Af I.F)) (I.fmat γ.2) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat γ.2 =
        I.J.map (inclE (F := I.F) (Af I.F)) := γ.2.2
    obtain ⟨s1, s2⟩ := span_map_mulVec (inclE (F := I.F) (Af I.F)) (c : Matrix (Fin I.n) (Fin I.n) I.E) W
    rw [hconj]
    refine inUnipRad_conj I _ _ _ _ _ _ _ hgi ?_ ?_ ?_ hmf
    · exact hform_mulVec_mulVec _ _ _ hU
    · rw [hfin]; exact s1
    · rw [hfin]; exact s2

end GlobalTheory.CuspGeo
