import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColFin
import Formalism.LocalToGlobal.GlobalTheory.GL4.FockSelfImEqZero

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree Formalism.L2.GlobalTheoryTheory.HLatOps
open Formalism.REAL (fockF)

section NF

variable {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

private theorem fockF_sub_right {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) (h : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  refine Finset.sum_subset h fun m _ hm => ?_
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

private theorem fockF_add_left_eq_add {σ : Type} (f f' g : MvPolynomial σ ℂ) :
    fockF (f + f') g = fockF f g + fockF f' g := by
  classical
  rw [fockF_sub_right (f + f') g _ MvPolynomial.support_add,
    fockF_sub_right f g (f.support ∪ f'.support) Finset.subset_union_left,
    fockF_sub_right f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

private theorem fockF_add_right_lemma_3 {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]
  ring

private theorem fockF_smul_left_eq_mul {σ : Type} (z : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (z • f) g = z * fockF f g := by
  rw [fockF_sub_right (z • f) g f.support MvPolynomial.support_smul,
    fockF_sub_right f g f.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

private theorem fockF_smul_right_eq_conj_mul {σ : Type} (z : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (z • g) = starRingEnd ℂ z * fockF f g := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul', starRingEnd_apply]
  ring

theorem nfAll_add_left (p p' q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam (p + p') q = nfAll lam p q + nfAll lam p' q := by
  unfold nfAll
  rw [fockF_add_left_eq_add, add_div]

theorem nfAll_add_right (p q q' : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam p (q + q') = nfAll lam p q + nfAll lam p q' := by
  unfold nfAll
  rw [fockF_add_right_lemma_3, add_div]

theorem nfAll_smul_left (z : ℂ) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam (z • p) q = z * nfAll lam p q := by
  unfold nfAll
  rw [fockF_smul_left_eq_mul, mul_div_assoc]

theorem nfAll_smul_right (z : ℂ) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p (z • q) = starRingEnd ℂ z * nfAll lam p q := by
  unfold nfAll
  rw [fockF_smul_right_eq_conj_mul, mul_div_assoc]

theorem nfAll_zero_left (q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam 0 q = 0 := by
  unfold nfAll fockF
  simp

theorem nfAll_zero_right (p : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam p 0 = 0 := by
  unfold nfAll fockF
  simp

theorem nfAll_sum_left {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ι × Fin n × Fin n) ℂ) (q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (∑ i ∈ s, f i) q = ∑ i ∈ s, nfAll lam (f i) q := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact nfAll_zero_left lam q
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, nfAll_add_left, ih]

theorem nfAll_sum_right {κ : Type} (s : Finset κ) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) (f : κ → MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p (∑ i ∈ s, f i) = ∑ i ∈ s, nfAll lam p (f i) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact nfAll_zero_right lam p
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, nfAll_add_right, ih]

theorem extProd_real : ∃ s : ℝ, (∏ τ, fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))) = (s : ℂ) := by
  refine ⟨∏ τ, (fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))).re, ?_⟩
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Formalism.GradedWeylDivisibility.LFockb_fockF_self, Complex.ofReal_re]

theorem nfAll_self_im (p : MvPolynomial (ι × Fin n × Fin n) ℂ) : (nfAll lam p p).im = 0 := by
  obtain ⟨s, hs⟩ := extProd_real lam
  unfold nfAll
  rw [hs, Formalism.GradedWeylDivisibility.LFockb_fockF_self, ← Complex.ofReal_div, Complex.ofReal_im]

theorem fockF_int_real {σ : Type} (p q : MvPolynomial σ ℤ) :
    ∃ r : ℝ, fockF (MvPolynomial.map (Int.castRingHom ℂ) p) (MvPolynomial.map (Int.castRingHom ℂ) q) = (r : ℂ) := by
  refine ⟨∑ m ∈ (MvPolynomial.map (Int.castRingHom ℂ) p).support,
    (((p.coeff m : ℤ) : ℝ) * ((q.coeff m : ℤ) : ℝ) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ)), ?_⟩
  unfold fockF
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.coeff_map]

theorem nfAll_int_real (p q : MvPolynomial (ι × Fin n × Fin n) ℤ) :
    ((nfAll lam (MvPolynomial.map (Int.castRingHom ℂ) p) (MvPolynomial.map (Int.castRingHom ℂ) q)).re : ℂ) =
      nfAll lam (MvPolynomial.map (Int.castRingHom ℂ) p) (MvPolynomial.map (Int.castRingHom ℂ) q) := by
  obtain ⟨r, hr⟩ := fockF_int_real p q
  obtain ⟨s, hs⟩ := extProd_real lam
  unfold nfAll
  rw [hr, hs, ← Complex.ofReal_div, Complex.ofReal_re]

def gramZ (Z : ZBasis lam) : Matrix Z.J0 Z.J0 ℝ :=
  Matrix.of fun k k' => (nfAll lam (MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ k')) (MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ k))).re

end NF

section Rec

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u) (hTV : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0))

def invFr (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : GL (Fin (D.R.N 0)) ℂ :=
  brpGL ℂ (Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹) (by
    rw [Matrix.det_reindex_self, Matrix.det_nonsing_inv]
    exact ((CV.Q_good c τ).1 v).ringInverse)

theorem invFr_det (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    (invFr CV v c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ).det = (((CV.Q c τ).X v)⁻¹).det := by
  show ((Matrix.reindex (CV.eQ c τ) (CV.eQ c τ)) ((CV.Q c τ).X v)⁻¹).det = _
  exact Matrix.det_reindex_self _ _

def tcAt (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) : Pol ℂ D.what₂.Tau (D.R.N 0) :=
  actP ((D.fm u).lam 0) (invFr CV v c) (MvPolynomial.map v.embedding (CV.co x c))

theorem tcAt_add (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (x y : ((D.fm u).lat 0).V) :
    tcAt CV v c (x + y) = tcAt CV v c x + tcAt CV v c y := by
  simp only [tcAt, map_add, Pi.add_apply]

theorem tcAt_smul (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (a : D.what₂.LL) (x : ((D.fm u).lat 0).V) :
    tcAt CV v c (a • x) = v.embedding a • tcAt CV v c x := by
  unfold tcAt
  rw [map_smul, Pi.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    ← MvPolynomial.smul_eq_C_mul, map_smul]

theorem majorant_lattice_eq_sum (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V) :
    majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y =
      ∑ c, nfAll ((D.fm u).lam 0) (tcAt CV v c y) (tcAt CV v c x) := by
  refine sesq_ext (G := fun x y => ∑ c, nfAll ((D.fm u).lam 0) (tcAt CV v c y) (tcAt CV v c x)) (σ := v.embedding) (exists_im_ne_zero v) (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v) ⟨?_, ?_, ?_, ?_⟩ ?_ x y
  · intro x x' y
    simp only [tcAt_add, nfAll_add_right, Finset.sum_add_distrib]
  · intro x y y'
    simp only [tcAt_add, nfAll_add_left, Finset.sum_add_distrib]
  · intro a x y
    simp only [tcAt_smul, nfAll_smul_right, Finset.mul_sum]
  · intro a x y
    simp only [tcAt_smul, nfAll_smul_left, Finset.mul_sum]
  · intro x
    apply Complex.ext
    · rw [CV.inf v x, Complex.re_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      unfold tcAt
      rw [← actAll_eq_actP]
      rfl
    · rw [Complex.im_sum, Finset.sum_eq_zero fun c _ => nfAll_self_im _ _]
      unfold majAt
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [Complex.mul_im]
      ring

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
