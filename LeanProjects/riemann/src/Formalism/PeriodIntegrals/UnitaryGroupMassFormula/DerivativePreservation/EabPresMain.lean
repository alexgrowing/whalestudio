import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DerivativePreservation.HasDerivAtExt

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.EabLie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma hpart_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) •
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) ∈ Glev k r i) ∧
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) •
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) ∈ Glev k r i) :=
  ⟨exp_hpart1_mem i p q, exp_hpart2_mem i p q⟩

theorem eab_smooth (i : Fin (r + 1)) (D : Set (Mx k r)) (p q : Fin (mdim k r i))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (EH k r (posL k r i p) (posL k r i q) f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  set X₁ := hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)
  set X₂ := hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)
  obtain ⟨h1, h2⟩ := hpart_mem (k := k) i p q
  refine ⟨U, fun x => fderiv ℝ F x (x * X₁) + Complex.I • fderiv ℝ F x (x * X₂), hU, hg₀U, ?_, ?_⟩
  · have hd := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    have s1 : ContDiffOn ℝ ∞ (fun x : Mx k r => fderiv ℝ F x (x * X₁)) U :=
      hd.clm_apply (mulRightRealCLM X₁).contDiff.contDiffOn
    have s2 : ContDiffOn ℝ ∞ (fun x : Mx k r => fderiv ℝ F x (x * X₂)) U :=
      hd.clm_apply (mulRightRealCLM X₂).contDiff.contDiffOn
    exact s1.add (s2.const_smul Complex.I)
  · intro x hx hxG
    show RdV X₁ f x + Complex.I • RdV X₂ f x = _
    rw [rdV_ext i X₁ h1 f F U x hU hx hxG hF hfF, rdV_ext i X₂ h2 f F U x hU hx hxG hF hfF]

lemma rdV_left (i : Fin (r + 1)) (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r))
    (hD : IsOpen D) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) (hL : LeftEq k r z i D f)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) (n : Mx k r) (hn : n ∈ Nlev k r i) :
    RdV X f (n * g) = psi k r z cStd n • RdV X f g := by
  have hmul : ∀ a b : Mx k r, a ∈ Glev k r i → b ∈ Glev k r i → a * b ∈ Glev k r i := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, fun c hc => ?_⟩
    · show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
      have h1 : aᴴ * Hpk k r * a = Hpk k r := ha1
      have h2 : bᴴ * Hpk k r * b = Hpk k r := hb1
      rw [Matrix.conjTranspose_mul]
      calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
        _ = Hpk k r := by rw [h1, h2]
    · obtain ⟨e1, e2⟩ := ha2 c hc
      obtain ⟨f1, f2⟩ := hb2 c hc
      exact ⟨by rw [← Matrix.mulVec_mulVec, f1, e1], by rw [← Matrix.mulVec_mulVec, f2, e2]⟩
  obtain ⟨U1, F1, hU1, hgU1, hF1, hfF1⟩ := hf g hg
  have hd := hasDerivAt_ext i X hX f F1 U1 g hU1 hgU1 hg.1 hF1 hfF1
  have hpath : ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
    (hasDerivAt_ext i X hX (fun y : Mx k r => y) (fun y => y) Set.univ g isOpen_univ (Set.mem_univ _) hg.1
      contDiffOn_id (fun _ _ _ => rfl)).continuousAt
  have hev : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ D := by
    apply hpath.preimage_mem_nhds
    have e0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
    rw [e0]
    exact hD.mem_nhds hg.2
  have heq : (fun t : ℝ => f (n * g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      fun t => psi k r z cStd n • f (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hev] with t ht
    rw [mul_assoc]
    exact hL _ ⟨hmul _ _ hg.1 (hX t), ht⟩ n hn
  have h2 : HasDerivAt (fun t : ℝ => f (n * g * NormedSpace.exp ((t : ℂ) • X)))
      (psi k r z cStd n • fderiv ℝ F1 g (g * X)) 0 := (hd.const_smul _).congr_of_eventuallyEq heq
  show deriv (fun t : ℝ => f (n * g * NormedSpace.exp ((t : ℂ) • X))) 0 = psi k r z cStd n • RdV X f g
  rw [h2.deriv, rdV_ext i X hX f F1 U1 g hU1 hgU1 hg.1 hF1 hfF1]

theorem eab_left (i : Fin (r + 1)) (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r))
    (hD : IsOpen D) (p q : Fin (mdim k r i)) (f : Mx k r → E) (hf : SmoothLev k r i D f)
    (hL : LeftEq k r z i D f) :
    LeftEq k r z i D (EH k r (posL k r i p) (posL k r i q) f) := by
  have hX1 := (hpart_mem i p q).1
  have hX2 := (hpart_mem i p q).2
  intro g hg n hn
  simp only [EH, EabH]
  rw [rdV_left i z D hD _ hX1 f hf hL g hg n hn, rdV_left i z D hD _ hX2 f hf hL g hg n hn, smul_add,
    smul_comm Complex.I]

theorem eab_lin (i : Fin (r + 1)) (D : Set (Mx k r)) (p q : Fin (mdim k r i))
    (f f₂ : Mx k r → E) (s : ℂ) (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i p) (posL k r i q) (fun x => f x + s • f₂ x) g =
      EH k r (posL k r i p) (posL k r i q) f g + s • EH k r (posL k r i p) (posL k r i q) f₂ g := by
  have hX1 := (hpart_mem i p q).1
  have hX2 := (hpart_mem i p q).2
  obtain ⟨U1, F1, hU1, hgU1, hF1, hfF1⟩ := hf g hg
  obtain ⟨U2, F2, hU2, hgU2, hF2, hfF2⟩ := hf₂ g hg
  have hU : IsOpen (U1 ∩ U2) := hU1.inter hU2
  have hgU : g ∈ U1 ∩ U2 := ⟨hgU1, hgU2⟩
  have hF1' : ContDiffOn ℝ ∞ F1 (U1 ∩ U2) := hF1.mono Set.inter_subset_left
  have hF2' : ContDiffOn ℝ ∞ F2 (U1 ∩ U2) := hF2.mono Set.inter_subset_right
  have hFs : ContDiffOn ℝ ∞ (fun x => F1 x + s • F2 x) (U1 ∩ U2) := hF1'.add (hF2'.const_smul s)
  have hfs : ∀ x ∈ U1 ∩ U2, x ∈ Glev k r i → f x + s • f₂ x = F1 x + s • F2 x :=
    fun x hx hxG => by rw [hfF1 x hx.1 hxG, hfF2 x hx.2 hxG]
  have hd1 : DifferentiableAt ℝ F1 g :=
    (hF1.differentiableOn (by simp)).differentiableAt (hU1.mem_nhds hgU1)
  have hd2 : DifferentiableAt ℝ F2 g :=
    (hF2.differentiableOn (by simp)).differentiableAt (hU2.mem_nhds hgU2)
  have key : ∀ X : Mx k r, (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) →
      RdV X (fun x => f x + s • f₂ x) g = RdV X f g + s • RdV X f₂ g := by
    intro X hX
    have hfd : fderiv ℝ (fun x => F1 x + s • F2 x) g = fderiv ℝ F1 g + s • fderiv ℝ F2 g :=
      (hd1.hasFDerivAt.add (hd2.hasFDerivAt.const_smul s)).fderiv
    rw [rdV_ext i X hX (fun x => f x + s • f₂ x) (fun x => F1 x + s • F2 x) (U1 ∩ U2) g hU hgU hg.1 hFs hfs,
      rdV_ext i X hX f F1 U1 g hU1 hgU1 hg.1 hF1 hfF1, rdV_ext i X hX f₂ F2 U2 g hU2 hgU2 hg.1 hF2 hfF2, hfd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp only [EH, EabH]
  rw [key _ hX1, key _ hX2]
  simp only [smul_add]
  rw [smul_comm Complex.I s]
  abel

end Formalism.FourierDecayAlt.Q.EabLie

namespace Formalism.FourierDecayAlt.Q

theorem eabPres_main : EabPres := by
  intro E _ _ k r z i D a b f f₂ s hD hf hf₂
  exact ⟨EabLie.eab_smooth i D a b f hf, fun _ hL => EabLie.eab_left i z D hD a b f hf hL,
    fun g hg => EabLie.eab_lin i D a b f f₂ s hf hf₂ g hg⟩

end Formalism.FourierDecayAlt.Q
