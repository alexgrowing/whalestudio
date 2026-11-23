import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.HasDerivAtExt

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TPresMain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma sl_congr (hD : IsOpen D) {f f' : Mx k r → E} (hf : SmoothLev k r i D f)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
  rw [← h g ⟨hgG, hg.2⟩]
  exact hfF g hg.1 hgG

lemma sl_add {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') :
    SmoothLev k r i D (f + f') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  simp only [Pi.add_apply, hfF g hg.1 hgG, hfF' g hg.2 hgG]

lemma sl_zero : SmoothLev k r i D (0 : Mx k r → E) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

def SmoothG (k r : ℕ) (i : Fin (r + 1)) (c : Mx k r → ℂ) : Prop :=
  ∃ c' : Mx k r → ℂ, ContDiff ℝ ∞ c' ∧ ∀ x ∈ Glev k r i, c x = c' x

lemma sg_const (v : ℂ) : SmoothG k r i (fun _ => v) := by
  exact ⟨fun _ => v, contDiff_const, fun _ _ => rfl⟩

lemma sg_mul {c d : Mx k r → ℂ} (hc : SmoothG k r i c) (hd : SmoothG k r i d) :
    SmoothG k r i (fun x => c x * d x) := by
  obtain ⟨c', hc', hcc⟩ := hc
  obtain ⟨d', hd', hdd⟩ := hd
  exact ⟨fun x => c' x * d' x, hc'.mul hd', fun x hx => by simp only [hcc x hx, hdd x hx]⟩

lemma sg_sub {c d : Mx k r → ℂ} (hc : SmoothG k r i c) (hd : SmoothG k r i d) :
    SmoothG k r i (fun x => c x - d x) := by
  obtain ⟨c', hc', hcc⟩ := hc
  obtain ⟨d', hd', hdd⟩ := hd
  exact ⟨fun x => c' x - d' x, hc'.sub hd', fun x hx => by simp only [hcc x hx, hdd x hx]⟩

lemma sl_smul_fun {c : Mx k r → ℂ} (hc : SmoothG k r i c) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) : SmoothLev k r i D (fun x => c x • f x) := by
  obtain ⟨c', hc', hcc⟩ := hc
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => c' x • F x, hU, hgU, hc'.contDiffOn.smul hF, fun g hg hgG => ?_⟩
  simp only [hcc g hgG, hfF g hg hgG]

lemma sl_csmul (c : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) : SmoothLev k r i D (c • f) := by
  exact sl_smul_fun (sg_const c) hf

lemma sl_sum {ι : Type*} (s : Finset ι) (f : ι → Mx k r → E) (hf : ∀ j ∈ s, SmoothLev k r i D (f j)) :
    SmoothLev k r i D (∑ j ∈ s, f j) := by
  exact Finset.sum_induction _ (fun g => SmoothLev k r i D g) (fun _ _ ha hb => sl_add ha hb) sl_zero hf

lemma sl_sum' {ι : Type*} [Fintype ι] (f : ι → Mx k r → E) (hf : ∀ j, SmoothLev k r i D (f j)) :
    SmoothLev k r i D (fun x => ∑ j, f j x) := by
  have e : (fun x => ∑ j, f j x) = ∑ j, f j := by
    funext x
    exact (Finset.sum_apply x Finset.univ f).symm
  rw [e]
  exact sl_sum _ _ fun j _ => hf j

lemma sl_neg {f : Mx k r → E} (hf : SmoothLev k r i D f) : SmoothLev k r i D (-f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, fun x => -F x, hU, hgU, hF.neg, fun g hg hgG => by simp only [Pi.neg_apply, hfF g hg hgG]⟩

end Smooth

lemma exp_first_hermitian_mem_level (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := by
  exact Formalism.FourierDecayAlt.Q.TPresLie.exp_hpart1_mem i p q t

lemma exp_second_hermitian_mem_level (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := by
  exact Formalism.FourierDecayAlt.Q.TPresLie.exp_hpart2_mem i p q t

section Rd

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

private lemma Glev_mul_mem {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  refine ⟨?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg.1, hh.1]
  · obtain ⟨e1, e2⟩ := hg.2 a ha
    obtain ⟨f1, f2⟩ := hh.2 a ha
    exact ⟨by rw [← Matrix.mulVec_mulVec, f1, e1], by rw [← Matrix.mulVec_mulVec, f2, e2]⟩

private lemma continuousAt_mul_exp_smul_of_mem_Glev (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    {g : Mx k r} (hg : g ∈ Glev k r i) :
    ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
  (Formalism.FourierDecayAlt.Q.TPresLie.hasDerivAt_ext i X hX (fun x => x) (fun x => x) Set.univ g isOpen_univ
    (Set.mem_univ _) hg contDiffOn_id (fun _ _ _ => rfl)).continuousAt

lemma rdV_local (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (hD : IsOpen D) (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) : RdV X f g = RdV X f' g := by
  simp only [RdV]
  apply Filter.EventuallyEq.deriv_eq
  have hc := continuousAt_mul_exp_smul_of_mem_Glev X hX hg.1
  have hD' : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' D ∈ 𝓝 (0 : ℝ) := by
    apply hc.preimage_mem_nhds
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
    exact hD.mem_nhds hg.2
  filter_upwards [hD'] with t ht
  exact h _ ⟨Glev_mul_mem hg.1 (hX t), ht⟩

lemma rdV_clm (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) : RdV X (fun y => L (f y)) g = L (RdV X f g) := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hd := Formalism.FourierDecayAlt.Q.TPresLie.hasDerivAt_ext i X hX f F U g hU hgU hg.1 hF hfF
  have hd2 : HasDerivAt (fun t : ℝ => L (f (g * NormedSpace.exp ((t : ℂ) • X))))
      (L (fderiv ℝ F g (g * X))) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  simp only [RdV]
  rw [hd2.deriv, hd.deriv]

lemma eh_local (hD : IsOpen D) (p q : Fin (mdim k r i)) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i p) (posL k r i q) f g = EH k r (posL k r i p) (posL k r i q) f' g := by
  simp only [EH, EabH]
  rw [rdV_local _ (exp_first_hermitian_mem_level p q) hD f f' h g hg, rdV_local _ (exp_second_hermitian_mem_level p q) hD f f' h g hg]

lemma eh_clm (p q : Fin (mdim k r i)) (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i p) (posL k r i q) (fun y => L (f y)) g =
      L (EH k r (posL k r i p) (posL k r i q) f g) := by
  simp only [EH, EabH]
  rw [rdV_clm _ (exp_first_hermitian_mem_level p q) L f hf g hg, rdV_clm _ (exp_second_hermitian_mem_level p q) L f hf g hg, map_add, map_smul]

lemma mulX_cd (X : Mx k r) : ContDiff ℝ ∞ (fun g : Mx k r => g * X) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun j _ => ((contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin (2 * r + k + 1) → ℂ) a)).mul
    contDiff_const

lemma eh_smooth (p q : Fin (mdim k r i)) (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (EH k r (posL k r i p) (posL k r i q) f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  have hdF := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hF).2
  refine ⟨U, fun g => fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) +
    Complex.I • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)),
    hU, hgU, ?_, fun g hg hgG => ?_⟩
  · exact (hdF.clm_apply (mulX_cd _).contDiffOn).add
      ((hdF.clm_apply (mulX_cd _).contDiffOn).const_smul Complex.I)
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [rdV_ext i _ (exp_first_hermitian_mem_level p q) f F U g hU hg hgG hF hfF,
      rdV_ext i _ (exp_second_hermitian_mem_level p q) f F U g hU hg hgG hF hfF]

end Rd

section Fold

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

lemma top_smooth (hD : IsOpen D) (c : ℂ) (p q : Fin (mdim k r i)) (f : Mx k r → E)
    (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (Top (EH k r) c (posL k r i p) (posL k r i q) f) := by
  refine sl_add (f := fun g => if posL k r i p = posL k r i q then c • f g else 0) ?_ (eh_smooth p q f hf)
  by_cases hpq : posL k r i p = posL k r i q
  · simp only [hpq, ↓reduceIte]
    exact sl_csmul c hf
  · simp only [hpq, ↓reduceIte]
    exact sl_zero

lemma top_local (hD : IsOpen D) (c : ℂ) (p q : Fin (mdim k r i)) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    Top (EH k r) c (posL k r i p) (posL k r i q) f g = Top (EH k r) c (posL k r i p) (posL k r i q) f' g := by
  simp only [Formalism.QuantumDeterminants.Top]
  rw [eh_local hD p q f f' h g hg, h g hg]

lemma top_clm (c : ℂ) (p q : Fin (mdim k r i)) (L : E →L[ℂ] E') (f : Mx k r → E)
    (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    Top (EH k r) c (posL k r i p) (posL k r i q) (fun y => L (f y)) g =
      L (Top (EH k r) c (posL k r i p) (posL k r i q) f g) := by
  simp only [Formalism.QuantumDeterminants.Top]
  rw [eh_clm p q L f hf g hg]
  split_ifs <;> simp only [map_add, map_smul, map_zero]

def foldP (k r : ℕ) (i : Fin (r + 1)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) (f : Mx k r → E) : Mx k r → E :=
  (l.map fun x => Top (EH k r) x.1 (posL k r i x.2.1) (posL k r i x.2.2)).foldr (fun T h => T h) f

lemma iteratedOperator_nil (f : Mx k r → E) : foldP k r i [] f = f := rfl

lemma iteratedOperator_cons (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (f : Mx k r → E) :
    foldP k r i (x :: l) f = Top (EH k r) x.1 (posL k r i x.2.1) (posL k r i x.2.2) (foldP k r i l f) := rfl

lemma iteratedOperator_smooth (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) : SmoothLev k r i D (foldP k r i l f) := by
  induction l with
  | nil => rw [iteratedOperator_nil]; exact hf
  | cons x l ih => rw [iteratedOperator_cons]; exact top_smooth hD _ _ _ _ ih

lemma iteratedOperator_congr (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) :
    ∀ g ∈ Glev k r i ∩ D, foldP k r i l f g = foldP k r i l f' g := by
  induction l with
  | nil => intro g hg; rw [iteratedOperator_nil, iteratedOperator_nil]; exact h g hg
  | cons x l ih =>
    intro g hg
    rw [iteratedOperator_cons, iteratedOperator_cons]
    exact top_local hD x.1 x.2.1 x.2.2 _ _ ih g hg

lemma iteratedOperator_clm_comp (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    ∀ g ∈ Glev k r i ∩ D, foldP k r i l (fun y => L (f y)) g = L (foldP k r i l f g) := by
  induction l with
  | nil => intro g hg; rw [iteratedOperator_nil, iteratedOperator_nil]
  | cons x l ih =>
    intro g hg
    rw [iteratedOperator_cons, iteratedOperator_cons, top_local hD x.1 x.2.1 x.2.2 _ (fun y => L (foldP k r i l f y)) ih g hg]
    exact top_clm x.1 x.2.1 x.2.2 L _ (iteratedOperator_smooth hD l f hf) g hg

lemma qminor_eq {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ) (f : Mx k r → E) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f =
      ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
        foldP k r i (List.ofFn fun m : Fin t => (u - ((m : ℕ) : ℂ), α (σ m), β m)) f) := by
  simp only [qminorOp, foldP, List.map_ofFn, Function.comp_def] <;> rfl

lemma qminor_smooth (hD : IsOpen D) {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f) := by
  rw [qminor_eq]
  exact sl_sum _ _ fun σ _ => sl_csmul _ (iteratedOperator_smooth hD _ _ hf)

lemma qminor_local (hD : IsOpen D) {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ)
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f g =
      qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f' g := by
  rw [qminor_eq, qminor_eq]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [iteratedOperator_congr hD _ f f' h g hg]

lemma qminor_clm (hD : IsOpen D) {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u (fun y => L (f y)) g =
      L (qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f g) := by
  rw [qminor_eq, qminor_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [iteratedOperator_clm_comp hD _ L f hf g hg]

end Fold

end Formalism.FourierDecayAlt.Q.TPresMain
