import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace WA

variable {k r : ℕ}

def Kl (Z : Q.Mx k r) : Prop :=
  ∀ a : Fin r, Z *ᵥ bvec (eI k r a) = 0 ∧ Z *ᵥ bvec (esI k r a) = 0 ∧
    Zᴴ *ᵥ bvec (eI k r a) = 0 ∧ Zᴴ *ᵥ bvec (esI k r a) = 0

theorem skew_ct {X : Q.Mx k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0) : Xᴴ = -(Hpk k r * X * Hpk k r) := by
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
  calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, Qx2.hpk_sq', Matrix.mul_one]
    _ = -(Hpk k r * X * Hpk k r) := by rw [h1, Matrix.neg_mul]

theorem kl_of_lev {X : Q.Mx k r} (hX : Q.inLieLev k r (Fin.last r) X) : Kl X := by
  intro a
  have ha : a.val < (Fin.last r).val := a.isLt
  obtain ⟨h1, h2⟩ := hX.2 a ha
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [skew_ct hX.1, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Qx8.hpk_e, ← Matrix.mulVec_mulVec, h2,
      Matrix.mulVec_zero, neg_zero]
  · rw [skew_ct hX.1, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Qx8.hpk_es, ← Matrix.mulVec_mulVec, h1,
      Matrix.mulVec_zero, neg_zero]

theorem kl_add {Z Z' : Q.Mx k r} (h : Kl Z) (h' : Kl Z') : Kl (Z + Z') := by
  intro a
  obtain ⟨a1, a2, a3, a4⟩ := h a
  obtain ⟨b1, b2, b3, b4⟩ := h' a
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.add_mulVec, Matrix.conjTranspose_add, a1, a2, a3, a4, b1, b2, b3, b4, add_zero]

theorem kl_smul {Z : Q.Mx k r} (c : ℂ) (h : Kl Z) : Kl (c • Z) := by
  intro a
  obtain ⟨a1, a2, a3, a4⟩ := h a
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.smul_mulVec, Matrix.conjTranspose_smul, a1, a2, a3, a4, smul_zero]

theorem kl_mul {Z Z' : Q.Mx k r} (h : Kl Z) (h' : Kl Z') : Kl (Z * Z') := by
  intro a
  obtain ⟨a1, a2, a3, a4⟩ := h a
  obtain ⟨b1, b2, b3, b4⟩ := h' a
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, b1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, b2, Matrix.mulVec_zero]
  · rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, a3, Matrix.mulVec_zero]
  · rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, a4, Matrix.mulVec_zero]

theorem kl_sub {Z Z' : Q.Mx k r} (h : Kl Z) (h' : Kl Z') : Kl (Z - Z') := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Z']
  exact kl_add h (kl_smul _ h')

theorem kl_zero : Kl (0 : Q.Mx k r) := by
  intro a; simp

theorem kl_sum {ι : Type*} (s : Finset ι) (Z : ι → Q.Mx k r) (h : ∀ i ∈ s, Kl (Z i)) : Kl (∑ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using kl_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact kl_add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem glc_of_kl {Z : Q.Mx k r} (h : Kl Z) : GLc k r Z := by
  have e1 : ∀ a : Fin r, ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) *ᵥ bvec (eI k r a) = 0 := fun a => by
    rw [← Matrix.mulVec_mulVec, Qx8.hpk_e, ← Matrix.mulVec_mulVec, (h a).2.2.2, Matrix.mulVec_zero]
  have e2 : ∀ a : Fin r, ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) *ᵥ bvec (esI k r a) = 0 := fun a => by
    rw [← Matrix.mulVec_mulVec, Qx8.hpk_es, ← Matrix.mulVec_mulVec, (h a).2.2.1, Matrix.mulVec_zero]
  refine ⟨⟨Qx2.hpart1_lie Z, fun a _ => ⟨?_, ?_⟩⟩, ⟨Qx2.hpart2_lie Z, fun a _ => ⟨?_, ?_⟩⟩⟩
  · unfold hpart1; rw [Matrix.smul_mulVec, Matrix.sub_mulVec, (h a).1, e1, sub_zero, smul_zero]
  · unfold hpart1; rw [Matrix.smul_mulVec, Matrix.sub_mulVec, (h a).2.1, e2, sub_zero, smul_zero]
  · unfold hpart2; rw [Matrix.smul_mulVec, Matrix.add_mulVec, (h a).1, e1, add_zero, smul_zero]
  · unfold hpart2; rw [Matrix.smul_mulVec, Matrix.add_mulVec, (h a).2.1, e2, add_zero, smul_zero]

theorem kl_of_glc {Z : Q.Mx k r} (h : GLc k r Z) : Kl Z := by
  rw [← Qx5.hpart_sum Z]
  exact kl_add (kl_of_lev h.1) (kl_smul _ (kl_of_lev h.2))

theorem glc_of_gwc {z : Fin (2 * r + k + 1) → ℂ} {Z : Q.Mx k r} (h : GWc k r z Z) : GLc k r Z :=
  ⟨h.1.1, h.2.1⟩

end WA

namespace WA

variable {k r : ℕ}

theorem idx_cases (p : Fin (2 * r + k + 1)) :
    (∃ j : Fin (k + 1), p = wI k r j) ∨ (∃ a : Fin r, p = eI k r a) ∨ (∃ a : Fin r, p = esI k r a) := by
  by_cases h1 : p.val < r
  · exact Or.inr (Or.inl ⟨⟨p.val, h1⟩, Fin.ext rfl⟩)
  · by_cases h2 : p.val ≤ r + k
    · exact Or.inl ⟨⟨p.val - r, by omega⟩, Fin.ext (by simp [wI]; omega)⟩
    · refine Or.inr (Or.inr ⟨⟨2 * r + k - p.val, by have := p.isLt; omega⟩, Fin.ext ?_⟩)
      simp [esI]; have := p.isLt; omega

theorem mulVec_bvec_apply (Z : Q.Mx k r) (p q : Fin (2 * r + k + 1)) : (Z *ᵥ bvec q) p = Z p q := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem kl_entry_col {Z : Q.Mx k r} (h : Kl Z) (p : Fin (2 * r + k + 1)) (a : Fin r) :
    Z p (eI k r a) = 0 ∧ Z p (esI k r a) = 0 := by
  constructor
  · have e := congrFun (h a).1 p
    rwa [mulVec_bvec_apply] at e
  · have e := congrFun (h a).2.1 p
    rwa [mulVec_bvec_apply] at e

theorem kl_entry_row {Z : Q.Mx k r} (h : Kl Z) (q : Fin (2 * r + k + 1)) (a : Fin r) :
    Z (eI k r a) q = 0 ∧ Z (esI k r a) q = 0 := by
  constructor
  · have e := congrFun (h a).2.2.1 q
    rw [mulVec_bvec_apply, Matrix.conjTranspose_apply] at e
    simpa using e
  · have e := congrFun (h a).2.2.2 q
    rw [mulVec_bvec_apply, Matrix.conjTranspose_apply] at e
    simpa using e

theorem wI_ne_eI (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ eI k r a := by
  intro h; have := congrArg Fin.val h; simp [wI, eI] at this; omega

theorem wI_ne_esI (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ esI k r a := by
  intro h; have := congrArg Fin.val h; simp [wI, esI] at this; have := a.isLt; have := j.isLt; omega

theorem kl_single (a b : Fin (k + 1)) : Kl (Matrix.single (wI k r a) (wI k r b) (1 : ℂ)) := by
  intro c
  have hb1 := wI_ne_eI (k := k) b c
  have hb2 := wI_ne_esI (k := k) b c
  have ha1 := wI_ne_eI (k := k) a c
  have ha2 := wI_ne_esI (k := k) a c
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext p <;>
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
      hb1, hb2, ha1, ha2, ]

theorem kl_decomp {Z : Q.Mx k r} (h : Kl Z) :
    Z = ∑ a : Fin (k + 1), ∑ b : Fin (k + 1), Z (wI k r a) (wI k r b) • Matrix.single (wI k r a) (wI k r b) (1 : ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rcases idx_cases (k := k) p with ⟨i, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases idx_cases (k := k) q with ⟨j, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have inj : ∀ x y : Fin (k + 1), wI k r x = wI k r y ↔ x = y := fun x y =>
        ⟨fun e => Fin.ext (by have := congrArg Fin.val e; simp [wI] at this; omega), fun e => e ▸ rfl⟩
      simp only [inj]
      rw [Finset.sum_eq_single i (fun x _ hx => by
        rw [Finset.sum_eq_zero]; intro y _; rw [if_neg]; rintro ⟨h1, _⟩; exact hx h1) (by simp)]
      rw [Finset.sum_eq_single j (fun y _ hy => by rw [if_neg]; rintro ⟨_, h2⟩; exact hy h2) (by simp)]
      simp
    · rw [(kl_entry_col h _ c).1]
      refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
      rw [if_neg]; rintro ⟨_, h2⟩; exact wI_ne_eI y c h2
    · rw [(kl_entry_col h _ c).2]
      refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
      rw [if_neg]; rintro ⟨_, h2⟩; exact wI_ne_esI y c h2
  · rw [(kl_entry_row h q a).1]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
    rw [if_neg]; rintro ⟨h1, _⟩; exact wI_ne_eI x a h1
  · rw [(kl_entry_row h q a).2]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_).symm
    rw [if_neg]; rintro ⟨h1, _⟩; exact wI_ne_esI x a h1

end WA

namespace WA

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rc_loc {D : Set (Q.Mx k r)} (hD : IsOpen D) {f f₂ : Q.Mx k r → E}
    (h : ∀ x ∈ Q.Glev k r (Fin.last r) ∩ D, f x = f₂ x) {g Z : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D)
    (hZ : GLc k r Z) : Rc Z f g = Rc Z f₂ g := by
  unfold Rc
  rw [Qx2.rd_loc hD h hg hZ.1, Qx2.rd_loc hD h hg hZ.2]

theorem rc_left (Z : Q.Mx k r) (f : Q.Mx k r → E) (h g : Q.Mx k r) :
    Rc Z (fun x => f (h * x)) g = Rc Z f (h * g) := by
  unfold Rc RdV
  simp only [Matrix.mul_assoc]

theorem rc_zeroZ (f : Q.Mx k r → E) (g : Q.Mx k r) : Rc (0 : Q.Mx k r) f g = 0 := by
  unfold Rc RdV hpart1 hpart2
  simp

theorem rc_zeroF (Z : Q.Mx k r) (g : Q.Mx k r) : Rc Z (fun _ => (0 : E)) g = 0 := by
  unfold Rc RdV
  simp

theorem smooth_fsum {D : Set (Q.Mx k r)} {ι : Type*} (s : Finset ι) (f : ι → Q.Mx k r → E)
    (h : ∀ i ∈ s, Q.SmoothLev k r (Fin.last r) D (f i)) :
    Q.SmoothLev k r (Fin.last r) D (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Qx2.smooth_zero (E := E) (k := k) (r := r) (i := Fin.last r) (D := D))
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact Qx2.smooth_add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem rc_fsum (hS : RcSmooth) {D : Set (Q.Mx k r)} (hD : IsOpen D) {ι : Type*} (s : Finset ι)
    (f : ι → Q.Mx k r → E) (h : ∀ i ∈ s, Q.SmoothLev k r (Fin.last r) D (f i)) {Z : Q.Mx k r} (hZ : GLc k r Z)
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) :
    Rc Z (fun x => ∑ i ∈ s, f i x) g = ∑ i ∈ s, Rc Z (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rc_zeroF (E := E) Z g
  | insert j s hj ih =>
    have h1 := h j (Finset.mem_insert_self _ _)
    have h2 := smooth_fsum s f fun i hi => h i (Finset.mem_insert_of_mem hi)
    have e := (hS k r E D (f j) (fun x => ∑ i ∈ s, f i x) hD h1 h2 Z hZ).2.1 1 g hg
    simp only [one_smul] at e
    simp only [Finset.sum_insert hj]
    rw [e, ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem rc_add (hL : RcLin) {D : Set (Q.Mx k r)} (hD : IsOpen D) {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D)
    {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') : Rc (Z + Z') f g = Rc Z f g + Rc Z' f g := by
  have := hL k r E D f hD hf g hg 1 Z Z' hZ hZ'
  simpa using this

theorem rc_smul (hL : RcLin) {D : Set (Q.Mx k r)} (hD : IsOpen D) {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D)
    (a : ℂ) {Z : Q.Mx k r} (hZ : GLc k r Z) : Rc (a • Z) f g = a • Rc Z f g := by
  have := hL k r E D f hD hf g hg a Z 0 hZ (glc_of_kl kl_zero)
  rw [add_zero, rc_zeroZ, add_zero] at this
  exact this

theorem rc_lincomb (hL : RcLin) {D : Set (Q.Mx k r)} (hD : IsOpen D) {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Zs : ι → Q.Mx k r) (hZ : ∀ i ∈ s, GLc k r (Zs i)) :
    Rc (∑ i ∈ s, c i • Zs i) f g = ∑ i ∈ s, c i • Rc (Zs i) f g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rc_zeroZ f g
  | insert j s hj ih =>
    have hj' := hZ j (Finset.mem_insert_self _ _)
    have hs' : ∀ i ∈ s, GLc k r (Zs i) := fun i hi => hZ i (Finset.mem_insert_of_mem hi)
    have hsum : GLc k r (∑ i ∈ s, c i • Zs i) :=
      glc_of_kl (kl_sum _ _ fun i hi => kl_smul _ (kl_of_glc (hs' i hi)))
    rw [Finset.sum_insert hj, Finset.sum_insert hj, rc_add hL hD hf hg (glc_of_kl (kl_smul _ (kl_of_glc hj'))) hsum,
      rc_smul hL hD hf hg _ hj', ih hs']

end WA

namespace WA

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smooth_clm {D : Set (Q.Mx k r)} {f : Q.Mx k r → E} (hf : Q.SmoothLev k r (Fin.last r) D f)
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E') :
    Q.SmoothLev k r (Fin.last r) D (fun x => L (f x)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  exact ⟨U, fun x => L (F x), hU, hgU, (L.restrictScalars ℝ).contDiff.comp_contDiffOn hF,
    fun g hg hgl => by show L (f g) = L (F g); rw [he g hg hgl]⟩

theorem wordR_nil (f : Q.Mx k r → E) : wordR [] f = f := rfl

theorem wordR_cons (Z : Q.Mx k r) (w : List (Q.Mx k r)) (f : Q.Mx k r → E) :
    wordR (Z :: w) f = Rc Z (wordR w f) := rfl

theorem word_smooth (hS : RcSmooth) {D : Set (Q.Mx k r)} (hD : IsOpen D) {J : Q.Mx k r → E}
    (hJ : Q.SmoothLev k r (Fin.last r) D J) :
    ∀ w : List (Q.Mx k r), (∀ Z ∈ w, GLc k r Z) → Q.SmoothLev k r (Fin.last r) D (wordR w J) := by
  intro w
  induction w with
  | nil => intro _; exact hJ
  | cons Z w ih =>
    intro hw
    rw [wordR_cons]
    exact (hS k r E D _ _ hD (ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
      (ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) Z (hw Z List.mem_cons_self)).1

theorem glc_getD {w : List (Q.Mx k r)} (hw : ∀ Z ∈ w, GLc k r Z) (i : ℕ) : GLc k r (w.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact glc_of_kl kl_zero
  | some Y => exact hw Y (List.mem_of_getElem? h)

theorem glc_set {w : List (Q.Mx k r)} (hw : ∀ Z ∈ w, GLc k r Z) (i : ℕ) {X : Q.Mx k r} (hX : GLc k r X) :
    ∀ Z ∈ w.set i X, GLc k r Z := by
  intro Z hZ
  rcases List.mem_or_eq_of_mem_set hZ with h | h
  · exact hw Z h
  · exact h ▸ hX

theorem glc_comm {A B : Q.Mx k r} (hA : GLc k r A) (hB : GLc k r B) : GLc k r (A * B - B * A) :=
  glc_of_kl (kl_sub (kl_mul (kl_of_glc hA) (kl_of_glc hB)) (kl_mul (kl_of_glc hB) (kl_of_glc hA)))

section cov

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem word_left (hS : RcSmooth) {D : Set (Q.Mx k r)} (hD : IsOpen D) {U : Set (Q.Mx k r)}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (_hDl : ∀ h ∈ U, ∀ g ∈ D, h * g ∈ D) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJs : Q.SmoothLev k r (Fin.last r) D J)
    (hJl : ∀ h ∈ U, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, J (h * g) = (π h).comp (J g)) :
    ∀ w : List (Q.Mx k r), (∀ Z ∈ w, GLc k r Z) →
      ∀ h ∈ U, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, wordR w J (h * g) = (π h).comp (wordR w J g) := by
  intro w
  induction w with
  | nil => intro _; exact hJl
  | cons Z w ih =>
    intro hw h hh g hg
    have hw' : ∀ Y ∈ w, GLc k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hZ := hw Z List.mem_cons_self
    have hF := word_smooth hS hD hJs w hw'
    show Rc Z (wordR w J) (h * g) = (π h).comp (Rc Z (wordR w J) g)
    rw [← rc_left]
    rw [rc_loc hD (f₂ := fun x => (ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)) (wordR w J x))
      (fun x hx => ih hw' h hh x hx) hg hZ]
    exact (hS k r _ D _ _ hD hF hF Z hZ).2.2 _ (ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)) g hg

theorem word_comm (hS : RcSmooth) (hC : RcComm) {D : Set (Q.Mx k r)} (hD : IsOpen D)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJs : Q.SmoothLev k r (Fin.last r) D J) {A : Q.Mx k r} (hA : GLc k r A)
    (L₀ : Wq →L[ℂ] Wq) (hAJ : ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, Rc A J g = (J g).comp L₀) :
    ∀ w : List (Q.Mx k r), (∀ Z ∈ w, GLc k r Z) → ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
      Rc A (wordR w J) g = (wordR w J g).comp L₀ +
        ∑ i ∈ Finset.range w.length, wordR (w.set i (A * w.getD i 0 - w.getD i 0 * A)) J g := by
  intro w
  induction w with
  | nil => intro _ g hg; rw [wordR_nil]; simp [hAJ g hg]
  | cons Z w ih =>
    intro hw g hg
    have hw' : ∀ Y ∈ w, GLc k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hZ := hw Z List.mem_cons_self
    have hF := word_smooth hS hD hJs w hw'
    set M : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip L₀ with hM
    have hMap : ∀ X : Wq →L[ℂ] Wp, M X = X.comp L₀ := fun X => rfl
    have hsm : ∀ i ∈ Finset.range w.length,
        Q.SmoothLev k r (Fin.last r) D (wordR (w.set i (A * w.getD i 0 - w.getD i 0 * A)) J) :=
      fun i _ => word_smooth hS hD hJs _ (glc_set hw' i (glc_comm hA (glc_getD hw' i)))
    have hsum := smooth_fsum (Finset.range w.length)
      (fun i => wordR (w.set i (A * w.getD i 0 - w.getD i 0 * A)) J) hsm
    have hc := hC k r _ D _ hD hF A Z hA hZ g hg
    rw [wordR_cons, eq_add_of_sub_eq hc]
    rw [rc_loc hD (f₂ := fun x => (1 : ℂ) • M (wordR w J x) +
        ∑ i ∈ Finset.range w.length, wordR (w.set i (A * w.getD i 0 - w.getD i 0 * A)) J x)
      (fun x hx => by rw [one_smul, hMap]; exact ih hw' x hx) hg hZ]
    have e1 := (hS k r _ D _ _ hD (smooth_clm hF M) hsum Z hZ).2.1 1 g hg
    beta_reduce at e1
    have e2 := (hS k r _ D _ _ hD hF hF Z hZ).2.2 _ M g hg
    beta_reduce at e2
    rw [e1, one_smul, e2, hMap, rc_fsum hS hD _ _ hsm hZ hg]
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, wordR_cons]
    abel

end cov

end WA

namespace WA

section psv

variable {TT : ℝ}

theorem psv_congr {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : ℂ → V}
    (h : ∀ ζ, TT < Complex.normSq ζ → f ζ = g ζ) (hf : PSV TT f) : PSV TT g := by
  obtain ⟨n, a, v, ha, he⟩ := hf
  exact ⟨n, a, v, ha, fun ζ hζ => (h ζ hζ).symm.trans (he ζ hζ)⟩

variable (hPS : PSCalc) (hT : 0 < TT) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
include hPS hT

theorem psc_add {f g : ℂ → V} (hf : PSV TT f) (hg : PSV TT g) : PSV TT (fun ζ => f ζ + g ζ) :=
  ((hPS TT hT).2.2.2.2.2.2.2 V V).1 f g hf hg

theorem psc_smul {a : ℂ → ℂ} {f : ℂ → V} (ha : PS TT a) (hf : PSV TT f) : PSV TT (fun ζ => a ζ • f ζ) :=
  ((hPS TT hT).2.2.2.2.2.2.2 V V).2.1 a f ha hf

theorem psc_lin {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V'] (L : V →ₗ[ℂ] V') {f : ℂ → V}
    (hf : PSV TT f) : PSV TT (fun ζ => L (f ζ)) :=
  ((hPS TT hT).2.2.2.2.2.2.2 V V').2.2.1 L f hf

theorem psc_dz {f : ℂ → V} (hf : PSV TT f) : PSV TT (dZV f) :=
  (((hPS TT hT).2.2.2.2.2.2.2 V V).2.2.2.1 f hf).1

theorem psc_dzb {f : ℂ → V} (hf : PSV TT f) : PSV TT (dZbV f) :=
  (((hPS TT hT).2.2.2.2.2.2.2 V V).2.2.2.1 f hf).2

theorem psc_const (v : V) : PSV TT (fun _ => v) :=
  ((hPS TT hT).2.2.2.2.2.2.2 V V).2.2.2.2 v

theorem ps_const (c : ℂ) : PS TT (fun _ => c) := (hPS TT hT).1 c

theorem psc_fsum {ι : Type*} (s : Finset ι) (f : ι → ℂ → V) (h : ∀ i ∈ s, PSV TT (f i)) :
    PSV TT (fun ζ => ∑ i ∈ s, f i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact psv_congr (fun ζ _ => by simp) (psc_const hPS hT (0 : V))
  | insert j s hj ih =>
    refine psv_congr (fun ζ _ => by rw [Finset.sum_insert hj]) (psc_add hPS hT (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

end psv

theorem glc_lincomb {k r : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Zs : ι → Q.Mx k r)
    (h : ∀ i ∈ s, GLc k r (Zs i)) : GLc k r (∑ i ∈ s, c i • Zs i) :=
  glc_of_kl (kl_sum _ _ fun i hi => kl_smul _ (kl_of_glc (h i hi)))

theorem glc_add {k r : ℕ} {Z Z' : Q.Mx k r} (h : GLc k r Z) (h' : GLc k r Z') : GLc k r (Z + Z') :=
  glc_of_kl (kl_add (kl_of_glc h) (kl_of_glc h'))

theorem glc_smul {k r : ℕ} (c : ℂ) {Z : Q.Mx k r} (h : GLc k r Z) : GLc k r (c • Z) :=
  glc_of_kl (kl_smul c (kl_of_glc h))

end WA

open WA in
theorem word_polynomial_vector_holds : WordPSVOfCut := by
  intro hLin hS hC hLeft hRight hSec hDec hPS Wp Wq _ _ _ _ _ _ P Bs hpl hk hsec Φ X₀ hX₀ c hc
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hTpos : 0 < P.TT := hTT ▸ mul_pos Bs.T_pos Bs.T'_pos
  have hk1 : 1 ≤ P.k := by omega
  have hmu : ∀ ζ, NF.muZ P.k P.r Bs.μsec ζ = mu0 P.k P.r Bs.z Bs.z' ζ := fun ζ => by rw [hsec]; rfl
  have hDo : IsOpen (Dp P.k P.r Bs.z Bs.z') := Qx5.Dp_open _ _ _ _
  have hJs : Q.SmoothLev P.k P.r (Fin.last P.r) (Dp P.k P.r Bs.z Bs.z')
      ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) := Qx5.slice_smooth Φ.2 hc
  have hJl : ∀ h ∈ UWset P.k P.r Bs.z, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dp P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (h * g) = (Bs.π h).comp ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) := by
    intro h hh g hg
    have e := Φ.2.2.2 (c, g) ⟨hc, hg.1, hg.2⟩ h hh 1 (Qx8.uw_one Bs.z')
    rw [Matrix.mul_one, Bs.π'_rep.1] at e
    rw [e]; ext v; simp
  have hJr : ∀ h ∈ UWset P.k P.r Bs.z', ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dp P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (g * h) = ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g).comp (Bs.π' h) := by
    intro h hh g hg
    have e := Φ.2.2.2 (c, g) ⟨hc, hg.1, hg.2⟩ 1 (Qx8.uw_one Bs.z) h hh
    rw [Matrix.one_mul, Bs.π_rep.1] at e
    rw [e]; ext v; simp
  have hDl : ∀ h ∈ UWset P.k P.r Bs.z, ∀ g ∈ Dp P.k P.r Bs.z Bs.z', h * g ∈ Dp P.k P.r Bs.z Bs.z' := by
    intro h hh g hg
    have e := Qx5.GG_inv hh (Qx8.uw_one Bs.z') g
    rw [Matrix.mul_one] at e
    show 0 < Q.GGl P.k P.r Bs.z Bs.z' (h * g)
    rw [e]; exact hg
  have hDr : ∀ h ∈ UWset P.k P.r Bs.z', ∀ g ∈ Dp P.k P.r Bs.z Bs.z', g * h ∈ Dp P.k P.r Bs.z Bs.z' := by
    intro h hh g hg
    have e := Qx5.GG_inv (Qx8.uw_one Bs.z) hh g
    rw [Matrix.one_mul] at e
    show 0 < Q.GGl P.k P.r Bs.z Bs.z' (g * h)
    rw [e]; exact hg
  set J := (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c with hJ
  have hWs := word_smooth hS hDo hJs
  have hWl := word_left hS hDo hDl hJs hJl
  have main : ∀ n : ℕ, ∀ w : List (Q.Mx P.k P.r), w.length = n → (∀ Z ∈ w, GLc P.k P.r Z) →
      PSV P.TT (fun ζ => wordR w J (mu0 P.k P.r Bs.z Bs.z' ζ)) := by
    intro n
    induction n with
    | zero =>
      intro w hl _
      rw [List.length_eq_zero_iff.mp hl]
      refine psv_congr (fun ζ hζ => ?_) (psc_const hPS hTpos X₀)
      rw [wordR_nil, ← hmu]
      exact (hX₀ c hc ζ hζ).symm
    | succ n ih =>
      intro w hl hw
      obtain ⟨Z, w', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      have hl' : w'.length = n := by simpa using hl
      have hw' : ∀ Y ∈ w', GLc P.k P.r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
      have hZ := hw Z List.mem_cons_self
      have hF := hWs w' hw'
      have hFl := hWl w' hw'
      have hIH := ih w' hl' hw'
      have hunit : ∀ p : Fin (P.k + 1) × Fin (P.k + 1), PSV P.TT (fun ζ =>
          Rc (Matrix.single (wI P.k P.r p.1) (wI P.k P.r p.2) (1 : ℂ)) (wordR w' J) (mu0 P.k P.r Bs.z Bs.z' ζ)) := by
        intro p
        obtain ⟨n₁, n₂, B₁, b₁, B₂, b₂, β₁, β₂, hB₁, hB₂, hb₁, hb₂, hβ₁, hβ₂, hde⟩ :=
          hDec P.k P.r Bs.z Bs.z' hk1 Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos p.1 p.2
        rw [hTT] at hb₁ hb₂ hβ₁ hβ₂ hde
        have hT1 : ∀ t, PSV P.TT (fun ζ => (wordR w' J (mu0 P.k P.r Bs.z Bs.z' ζ)).comp (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π' (B₁ t)) +
            ∑ i ∈ Finset.range w'.length, wordR (w'.set i (B₁ t * w'.getD i 0 - w'.getD i 0 * B₁ t)) J
              (mu0 P.k P.r Bs.z Bs.z' ζ)) := by
          intro t
          refine psc_add hPS hTpos ?_ (psc_fsum hPS hTpos _ _ fun i _ =>
            ih _ (by simp [hl']) (glc_set hw' i (glc_comm (glc_of_gwc (hB₁ t)) (glc_getD hw' i))))
          exact psc_lin hPS hTpos ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π' (B₁ t))).toLinearMap hIH
        have hT2 : ∀ t, PSV P.TT (fun ζ => (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π (B₂ t)).comp (wordR w' J (mu0 P.k P.r Bs.z Bs.z' ζ))) :=
          fun t => psc_lin hPS hTpos (ContinuousLinearMap.compL ℂ Wq Wp Wp (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π (B₂ t))).toLinearMap hIH
        have hT3 := psc_dz hPS hTpos hIH
        have hT4 := psc_dzb hPS hTpos hIH
        refine psv_congr (fun ζ hζ => ?_) (psc_add hPS hTpos (psc_add hPS hTpos (psc_add hPS hTpos
          (psc_fsum hPS hTpos Finset.univ _ fun t _ => psc_smul hPS hTpos (hb₁ t) (hT1 t))
          (psc_fsum hPS hTpos Finset.univ _ fun t _ => psc_smul hPS hTpos (hb₂ t) (hT2 t)))
          (psc_smul hPS hTpos hβ₁ hT3)) (psc_smul hPS hTpos hβ₂ hT4))
        obtain ⟨hη, hηb, hμ, hSD⟩ := hSec P.k P.r Bs.z Bs.z' hk1 Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos ζ
          (hTT ▸ hζ)
        have hLB : ∀ t, GLc P.k P.r ((mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * B₂ t * mu0 P.k P.r Bs.z Bs.z' ζ) ∧
            Rc ((mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * B₂ t * mu0 P.k P.r Bs.z Bs.z' ζ) (wordR w' J) (mu0 P.k P.r Bs.z Bs.z' ζ) =
              (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π (B₂ t)).comp (wordR w' J (mu0 P.k P.r Bs.z Bs.z' ζ)) :=
          fun t => hLeft P.k P.r Bs.z Wp Wq Bs.π Bs.π_rep Bs.π_cont Bs.z_mem _ _ hDo hDl hF hFl _ hμ (B₂ t) (hB₂ t)
        have hmid : (mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * (∑ t, b₂ t ζ • B₂ t) * mu0 P.k P.r Bs.z Bs.z' ζ =
            ∑ t, b₂ t ζ • ((mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * B₂ t * mu0 P.k P.r Bs.z Bs.z' ζ) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Matrix.mul_smul, Matrix.smul_mul]
        have hG1 : GLc P.k P.r (∑ t, b₁ t ζ • B₁ t) := glc_lincomb _ _ _ fun t _ => glc_of_gwc (hB₁ t)
        have hG2 : GLc P.k P.r (∑ t, b₂ t ζ • ((mu0 P.k P.r Bs.z Bs.z' ζ)⁻¹ * B₂ t * mu0 P.k P.r Bs.z Bs.z' ζ)) :=
          glc_lincomb _ _ _ fun t _ => (hLB t).1
        have hGη := glc_smul (β₁ ζ) hη
        have hGηb := glc_smul (β₂ ζ) hηb
        rw [hde ζ hζ, hmid, rc_add hLin hDo hF hμ (glc_add (glc_add hG1 hG2) hGη) hGηb,
          rc_add hLin hDo hF hμ (glc_add hG1 hG2) hGη, rc_add hLin hDo hF hμ hG1 hG2,
          rc_lincomb hLin hDo hF hμ _ _ _ fun t _ => glc_of_gwc (hB₁ t),
          rc_lincomb hLin hDo hF hμ _ _ _ fun t _ => (hLB t).1,
          rc_smul hLin hDo hF hμ _ hη, rc_smul hLin hDo hF hμ _ hηb,
          (hSD _ _ hF).1, (hSD _ _ hF).2]
        congr 1
        congr 1
        congr 1
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [word_comm hS hC hDo hJs (glc_of_gwc (hB₁ t)) (Formalism.FourierDecayAlt.P.QrD.ecOp Bs.π' (B₁ t))
            (fun g hg => (hRight P.k P.r Bs.z' Wp Wq Bs.π' Bs.π'_rep Bs.π'_cont Bs.z'_mem _ _ hDo hDr hJs hJr g hg
              (B₁ t) (hB₁ t)).2) w' hw' _ hμ]
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [(hLB t).2]
      have hZdec := kl_decomp (kl_of_glc hZ)
      rw [← Fintype.sum_prod_type' (f := fun a b => Z (wI P.k P.r a) (wI P.k P.r b) •
        Matrix.single (wI P.k P.r a) (wI P.k P.r b) (1 : ℂ))] at hZdec
      refine psv_congr (fun ζ hζ => ?_) (psc_fsum hPS hTpos Finset.univ _
        fun p _ => psc_smul hPS hTpos (ps_const hPS hTpos (Z (wI P.k P.r p.1) (wI P.k P.r p.2))) (hunit p))
      obtain ⟨-, -, hμ, -⟩ := hSec P.k P.r Bs.z Bs.z' hk1 Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos ζ (hTT ▸ hζ)
      rw [wordR_cons]
      conv_rhs => rw [hZdec]
      rw [rc_lincomb hLin hDo hF hμ _ _ _ fun p _ => glc_of_kl (kl_single p.1 p.2)]
  intro w hw
  exact psv_congr (fun ζ _ => by simp only [hmu]) (main _ w rfl hw)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
