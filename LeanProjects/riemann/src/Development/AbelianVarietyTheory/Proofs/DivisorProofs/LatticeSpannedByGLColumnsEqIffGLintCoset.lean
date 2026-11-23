import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLatCoset

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def vec (y : Fin m → w.adicCompletion E) : B.A := ∑ i, e.symm (y i) • b i

def crd (a : B.A) : Fin m → w.adicCompletion E := fun i => e (b.repr a i)

def IntV (y : Fin m → w.adicCompletion E) : Prop := ∀ i, y i ∈ Ov E w

lemma vec_crd (a : B.A) : vec e b (crd e b a) = a := by
  simp [vec, crd, b.sum_repr]

lemma crd_vec (y : Fin m → w.adicCompletion E) : crd e b (vec e b y) = y := by
  funext i; simp only [vec, crd]; rw [Module.Basis.repr_sum_self]; simp

lemma sum_cols (M : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (x : Fin m → w.adicCompletion E) :
    ∑ j, e.symm (x j) • vec e b (fun i => M i j) = vec e b (M *ᵥ x) := by
  simp only [vec, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma memOv (x : w.adicCompletion E) : x ∈ Ov E w ↔ Valued.v x ≤ 1 := by
  simp [Ov, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

lemma intV_mulVec {M : Matrix (Fin m) (Fin m) (w.adicCompletion E)} (hM : ∀ i j, M i j ∈ Ov E w)
    {z : Fin m → w.adicCompletion E} (hz : IntV z) : IntV (M *ᵥ z) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hz j)

lemma intV_single (j : Fin m) : IntV (w := w) (Pi.single j 1) := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · simp [Subring.one_mem]
  · simp [Pi.single_apply, h, Subring.zero_mem]

lemma gl_vec (h : GL (Fin m) (w.adicCompletion E)) (z : Fin m → w.adicCompletion E) :
    (↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ ((↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

lemma gl_vec' (h : GL (Fin m) (w.adicCompletion E)) (z : Fin m → w.adicCompletion E) :
    (↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ ((↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

lemma preserves_iff (h : GL (Fin m) (w.adicCompletion E)) :
    (∀ z, IntV ((↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) ↔ IntV z) ↔ h ∈ GLint (Fin m) (Ov E w) := by
  constructor
  · intro H
    have hh : ∀ i j, (↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w := by
      intro i j
      have := (H (Pi.single j 1)).2 (intV_single j) i
      simpa [Matrix.mulVec_single_one] using this
    have hi : ∀ i j, (↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w := by
      intro i j
      have := (H ((↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ Pi.single j 1)).1 (by rw [gl_vec']; exact intV_single j) i
      simpa [Matrix.mulVec_single_one] using this
    have inj : Function.Injective ((Ov E w).subtype.mapMatrix :
        Matrix (Fin m) (Fin m) (Ov E w) →+* Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
      intro A A' hAA
      exact Matrix.ext fun i j => Subtype.ext (congrArg (fun M : Matrix (Fin m) (Fin m) (w.adicCompletion E) => M i j) hAA)
    let M1 : Matrix (Fin m) (Fin m) (Ov E w) := Matrix.of fun i j => ⟨_, hh i j⟩
    let M2 : Matrix (Fin m) (Fin m) (Ov E w) := Matrix.of fun i j => ⟨_, hi i j⟩
    have e1 : (Ov E w).subtype.mapMatrix M1 = ↑h := Matrix.ext fun i j => rfl
    have e2 : (Ov E w).subtype.mapMatrix M2 = ↑h⁻¹ := Matrix.ext fun i j => rfl
    let k : GL (Fin m) (Ov E w) :=
      ⟨M1, M2, inj (by rw [map_mul, map_one, e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]),
        inj (by rw [map_mul, map_one, e1, e2, ← Units.val_mul, inv_mul_cancel, Units.val_one])⟩
    exact ⟨k, Units.ext (Matrix.ext fun i j => rfl)⟩
  · rintro ⟨k, rfl⟩ z
    have ent : ∀ (k : GL (Fin m) (Ov E w)) i j,
        ((bc (Ov E w).subtype k : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w :=
      fun k i j => (k.val i j).2
    constructor
    · intro hz
      have := intV_mulVec (ent k⁻¹) hz
      rwa [map_inv, gl_vec] at this
    · exact intV_mulVec (ent k)

lemma mem_lat (hI : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (g : GLw m w) (a : B.A) :
    a ∈ GlobalTheory.TwLat.lat e b g ↔
      IntV ((↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a) := by
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have : crd e b (∑ i, e.symm ((↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) • b i) =
          (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ Pi.single j 1 := by
        rw [Matrix.mulVec_single_one]
        exact crd_vec e b _
      rw [this, gl_vec]
      exact intV_single j
    | zero =>
      have : crd e b (0 : B.A) = 0 := by funext i; simp [crd]
      rw [this, Matrix.mulVec_zero]
      intro i; exact Subring.zero_mem _
    | add x y _ _ hx hy =>
      have : crd e b (x + y) = crd e b x + crd e b y := by funext i; simp [crd]
      rw [this, Matrix.mulVec_add]
      intro i; exact Subring.add_mem _ (hx i) (hy i)
    | smul c x _ hx =>
      have hc : e (algebraMap K.O K.E c) ∈ Ov E w := (memOv _).2 ((hI _).1 ⟨c, rfl⟩)
      have : crd e b (c • x) = e (algebraMap K.O K.E c) • crd e b x := by
        funext i; simp only [crd, Pi.smul_apply, smul_eq_mul]; rw [← algebraMap_smul K.E c x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
      rw [this, Matrix.mulVec_smul]
      intro i; exact Subring.mul_mem _ hc (hx i)
  · intro hx
    set x := (↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a with hxdef
    have hr : ∀ j, e.symm (x j) ∈ (algebraMap K.O K.E).range := fun j =>
      (hI _).2 (by rw [RingEquiv.apply_symm_apply]; exact (memOv _).1 (hx j))
    choose c hc using hr
    have hsum : a = ∑ j, c j • vec e b (fun i => (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) := by
      simp_rw [← algebraMap_smul K.E (c _), hc]
      rw [sum_cols, hxdef, gl_vec', vec_crd]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lat_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) →
    (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) →
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ)
    (b : Module.Basis (Fin m) K.E B.A),
    (∀ g g' : GLw m w, GlobalTheory.TwLat.lat e b g = GlobalTheory.TwLat.lat e b g' ↔ g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w m) ∧
      ∀ g : GLw m w, GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e _ hI _ B m b
  refine ⟨fun g g' => ?_, fun g => ?_⟩
  · show _ ↔ g⁻¹ * g' ∈ GLint (Fin m) (Ov E w)
    rw [SetLike.ext_iff, ← preserves_iff]
    simp only [mem_lat e b hI]
    constructor
    · intro H z
      have := H (vec e b ((↑g' : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z))
      rw [crd_vec, gl_vec] at this
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec]
    · intro H a
      have := H ((↑g'⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a)
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec, gl_vec'] at this
  · refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff]
    intro a _
    have hsum : a = ∑ j, e.symm (((↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a) j) •
        vec e b (fun i => (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) := by
      rw [sum_cols, gl_vec', vec_crd]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))

end GlobalTheory.TwLatCoset
