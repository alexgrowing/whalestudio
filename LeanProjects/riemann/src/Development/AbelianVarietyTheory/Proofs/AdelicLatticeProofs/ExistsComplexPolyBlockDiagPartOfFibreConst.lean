import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvalComplexPolyEqZeroOnRatZariskiClosureStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroupStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangula
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsMultiplierDescendBlockDiagPartOfRatIdempotStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.FibreDescent

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def rtr (g : Matrix ι ι ℂ) : MvPolynomial (ι × ι) ℂ →ₐ[ℂ] MvPolynomial (ι × ι) ℂ :=
  MvPolynomial.aeval fun ij : ι × ι => ∑ k, g k ij.2 • MvPolynomial.X (ij.1, k)

omit [Fintype ι] [DecidableEq ι] in
lemma evC_add (p q : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (p + q) y = evC p y + evC q y := by
  simp [evC]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_mul (p q : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (p * q) y = evC p y * evC q y := by
  simp [evC]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_smul (c : ℂ) (p : MvPolynomial (ι × ι) ℂ) (y : Matrix ι ι ℂ) : evC (c • p) y = c * evC p y := by
  simp [evC, MvPolynomial.smul_eval]

omit [DecidableEq ι] in
lemma evC_rtr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (rtr g f) y = evC f (y * g) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, rtr]
  | add p q hp hq => rw [map_add, evC_add, evC_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, evC_mul, evC_mul, hp]
    congr 1
    simp [evC, rtr, Matrix.mul_apply, MvPolynomial.smul_eval, mul_comm]

omit [DecidableEq ι] in
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq => rw [map_add, evC_add, evC_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, evC_mul, evC_mul, hp]
    congr 1
    simp [evC, ltr, Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_map (p : MvPolynomial (ι × ι) ℚ) (y : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) p) y = ev p y := by
  rw [evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]

omit [DecidableEq ι] in

lemma exists_fg_rtr (f : MvPolynomial (ι × ι) ℂ) :
    ∃ V : Submodule ℂ (MvPolynomial (ι × ι) ℂ), V.FG ∧ ∀ g, rtr g f ∈ V := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span ℂ {MvPolynomial.C a}, Submodule.fg_span (Set.finite_singleton _), fun g => ?_⟩
    apply Submodule.subset_span
    simp [rtr]
  | add p q hp hq =>
    obtain ⟨V, hV, h⟩ := hp
    obtain ⟨V', hV', h'⟩ := hq
    refine ⟨V ⊔ V', hV.sup hV', fun g => ?_⟩
    rw [map_add]
    exact Submodule.add_mem_sup (h g) (h' g)
  | mul_X p ij hp =>
    obtain ⟨V, hV, h⟩ := hp
    refine ⟨V * Submodule.span ℂ (Set.range MvPolynomial.X),
      hV.mul (Submodule.fg_span (Set.finite_range _)), fun g => ?_⟩
    rw [map_mul]
    refine Submodule.mul_mem_mul (h g) ?_
    rw [rtr, MvPolynomial.aeval_X]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

omit [DecidableEq ι] in

lemma exists_finset_rtr (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ p ∈ s, ∃ g ∈ Γ, p = rtr g f) ∧
      ∀ g ∈ Γ, rtr g f ∈ Submodule.span ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  obtain ⟨V, hV, h⟩ := exists_fg_rtr f
  have hle : Submodule.span ℂ ((fun g => rtr g f) '' Γ) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨g, -, rfl⟩
    exact h g
  have hfg : (Submodule.span ℂ ((fun g => rtr g f) '' Γ)).FG := by
    have : Module.Finite ℂ V := Module.Finite.iff_fg.2 hV
    exact Module.Finite.iff_fg.1 (Submodule.finiteDimensional_of_le hle)
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  refine ⟨s, fun p hp => ?_, fun g hg => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hs hp
    exact ⟨g, hg, rfl⟩
  · rw [← hspan]
    exact Submodule.subset_span ⟨g, hg, rfl⟩

def multIdeal (Γ : Set (Matrix ι ι ℂ)) (π : Matrix ι ι ℂ → Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {b | ∀ g ∈ Γ, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ,
    evC b (π x) * evC f (x * g) = evC b' (π x)}
  zero_mem' := fun g _ => ⟨0, fun x _ => by simp [evC]⟩
  add_mem' := by
    intro a b ha hb g hg
    obtain ⟨a', ha'⟩ := ha g hg
    obtain ⟨b', hb'⟩ := hb g hg
    exact ⟨a' + b', fun x hx => by rw [evC_add, evC_add, add_mul, ha' x hx, hb' x hx]⟩
  smul_mem' := by
    intro c b hb g hg
    obtain ⟨b', hb'⟩ := hb g hg
    exact ⟨c * b', fun x hx => by rw [smul_eq_mul, evC_mul, evC_mul, mul_assoc, hb' x hx]⟩

omit [DecidableEq ι] in
lemma exists_common_zero (D : Ideal (MvPolynomial (ι × ι) ℂ)) (hD : D ≠ ⊤) :
    ∃ z : Matrix ι ι ℂ, ∀ b ∈ D, evC b z = 0 := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal D hD
  obtain ⟨x, rfl⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  refine ⟨Matrix.of fun i j => x (i, j), fun b hb => ?_⟩
  have := (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).1 (hle hb)
  simpa [evC, MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ClassFin.FibreDescent

open GlobalTheory.ClassFin.FibreDescent in

theorem GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC f x = evC b (blk e x) := by
  intro ι _ _ Γ e hΓ he htri f hf
  have hmul : ∀ x ∈ Γ, ∀ y ∈ Γ, blk e (x * y) = blk e x * blk e y := fun x hx y hy =>
    ((GlobalTheory.ClassFin.blk_mul_of_triangular ι e ℂ he).2.1 x y (htri x hx) (htri y hy)).1
  have hpre : IsPre (blk e '' Γ) := GlobalTheory.ClassFin.isPre_blk_image ι Γ e hΓ.toIsPre he htri
  obtain ⟨-, hm, hadj, hdet⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι _ hpre ℂ
  obtain ⟨s, hs, hspan⟩ := exists_finset_rtr Γ f
  obtain ⟨b₀, ⟨x₀, hx₀, hb₀⟩, hb⟩ := GlobalTheory.T.exists_multiplier_descend_blockDiagPartOfRatIdempotent ι Γ e hΓ.closed ⟨1, hΓ.one_mem⟩ s (by
    intro p hp x hx x' hx' hxx
    obtain ⟨g, hg, rfl⟩ := hs p hp
    rw [evC_rtr, evC_rtr]
    exact hf _ (hΓ.mul_mem _ hx _ hg) _ (hΓ.mul_mem _ hx' _ hg)
      (by rw [hmul _ hx _ hg, hmul _ hx' _ hg, hxx]))
  have hb₀D : b₀ ∈ multIdeal Γ (blk e) f := by
    intro g hg
    have key : ∀ p ∈ Submodule.span ℂ (s : Set (MvPolynomial (ι × ι) ℂ)),
        ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b₀ (blk e x) * evC p x = evC b' (blk e x) := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem p hp => exact hb p hp
      | zero => exact ⟨0, fun x _ => by simp [evC]⟩
      | add p q _ _ hp hq =>
        obtain ⟨a', ha'⟩ := hp
        obtain ⟨b', hb'⟩ := hq
        exact ⟨a' + b', fun x hx => by rw [evC_add, evC_add, mul_add, ha' x hx, hb' x hx]⟩
      | smul c p _ hp =>
        obtain ⟨a', ha'⟩ := hp
        exact ⟨c • a', fun x hx => by rw [evC_smul, evC_smul, ← ha' x hx]; ring⟩
    obtain ⟨b', hb'⟩ := key _ (hspan g hg)
    exact ⟨b', fun x hx => by rw [← hb' x hx, evC_rtr]⟩
  have hstab : ∀ h ∈ Γ, rtr (blk e h) b₀ ∈ multIdeal Γ (blk e) f := by
    intro h hh g hg
    obtain ⟨b', hb'⟩ := hb₀D (h.adjugate * g) (hΓ.mul_mem _ (hΓ.adj_mem _ hh) _ hg)
    refine ⟨rtr (blk e h) b', fun x hx => ?_⟩
    rw [evC_rtr, evC_rtr, ← hmul _ hx _ hh, ← hb' _ (hΓ.mul_mem _ hx _ hh), Matrix.mul_assoc,
      ← Matrix.mul_assoc h, Matrix.mul_adjugate, hΓ.det_eq _ hh, one_smul, Matrix.one_mul]
  have htop : multIdeal Γ (blk e) f = ⊤ := by
    by_contra hD
    obtain ⟨z, hz⟩ := exists_common_zero _ hD
    have hzp : z ∈ pts (blk e '' Γ) ℂ := by
      intro p hp
      rw [← evC_map]
      refine hz _ fun g _ => ⟨0, fun x hx => ?_⟩
      rw [evC_map, hp _ ⟨x, hx, rfl⟩]
      simp [evC]
    have hx₀p : blk e x₀ ∈ pts (blk e '' Γ) ℂ := fun p hp => hp _ ⟨x₀, hx₀, rfl⟩
    have := GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure ι _ hpre.aut_mem (ltr z b₀) (by
      rintro _ ⟨h, hh, rfl⟩
      rw [evC_ltr, ← evC_rtr]
      exact hz _ (hstab h hh)) _ (hm _ (hadj z hzp) _ hx₀p)
    rw [evC_ltr, ← Matrix.mul_assoc, Matrix.mul_adjugate, hdet z hzp, one_smul, Matrix.one_mul] at this
    exact hb₀ this
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ multIdeal Γ (blk e) f := htop ▸ Submodule.mem_top
  obtain ⟨b, hb⟩ := h1 1 hΓ.one_mem
  refine ⟨b, fun x hx => ?_⟩
  rw [← hb x hx, Matrix.mul_one]
  simp [evC]
