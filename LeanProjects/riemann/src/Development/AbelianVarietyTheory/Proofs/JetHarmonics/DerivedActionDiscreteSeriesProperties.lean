import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset Filter Topology
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory.DerivedAction

open PI.UpqRep PI.UnitaryGroupMassFormula.CapelliEig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}

theorem exp_mem {X : Mx k r} (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  refine CCRuleCW.exp_mem_UH (Hpk k r) _ ?_
  have hL : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]

theorem one_mem : (1 : Mx k r) ∈ UH (Hpk k r) := by
  show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem lie_conj {X g : Mx k r} (hX : InLieHpk k r X) (hg : g ∈ UH (Hpk k r)) :
    InLieHpk k r (g⁻¹ * X * g) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
  have hi1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have hL : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have A : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hU]
      _ = (g * g⁻¹)ᴴ * Hpk k r * g := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [hi1, conjTranspose_one, Matrix.one_mul]
  have B : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hU]
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, hi1, Matrix.mul_one]
  show (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g)
        = gᴴ * (Xᴴ * ((g⁻¹)ᴴ * Hpk k r)) + (Hpk k r * g⁻¹) * X * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * g := by
          rw [A, B]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hL]; simp

theorem lie_conj' {X g : Mx k r} (hX : InLieHpk k r X) (hg : g ∈ UH (Hpk k r)) :
    InLieHpk k r (g * X * g⁻¹) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
  have := lie_conj hX (unitary_Hecke_group k r g hg).2.1
  rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at this

theorem hasDerivAt_local {X g : Mx k r} (hX : InLieHpk k r X) {f F : Mx k r → H} {U : Set (Mx k r)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUH (Hpk k r) h → f h = F h)
    (hg : g ∈ UH (Hpk k r)) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ h0.symm
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds hgU)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with t ht
  exact hfF _ ht ((unitary_Hecke_group k r g hg).2.2 _ (exp_mem hX t))

theorem exists_lin {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    ∃ L : Mx k r →L[ℝ] H, ∀ X, InLieHpk k r X → dsig (k := k) (r := r) σ X v = L X ∧
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) σ X v) 0 := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 one_mem
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have h := hasDerivAt_local hX hU h1 hF hfF one_mem
  simp only [Matrix.one_mul] at h
  have e : dsig (k := k) (r := r) σ X v = fderiv ℝ F 1 X := h.deriv
  exact ⟨e, e ▸ h⟩

theorem hasDerivAt_dsig {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) σ X v) 0 := by
  obtain ⟨L, hL⟩ := exists_lin hv
  exact (hL X hX).2

theorem hasDerivAt_apply {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    (T : H →L[ℂ] H) :
    HasDerivAt (fun t : ℝ => T (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (T (dsig (k := k) (r := r) σ X v)) 0 :=
  (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dsig hX hv)

theorem dsig_zero (X : Mx k r) : dsig (k := k) (r := r) σ X (0 : H) = 0 := by
  simp [dsig]

theorem dsig_add {X : Mx k r} (hX : InLieHpk k r X) {v w : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (v + w) = dsig (k := k) (r := r) σ X v + dsig (k := k) (r := r) σ X w := by
  have h := (hasDerivAt_dsig hX hv).add (hasDerivAt_dsig hX hw)
  rw [← h.deriv]
  unfold dsig
  congr 1
  funext t
  simp

theorem dsig_smul {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (a • v) = a • dsig (k := k) (r := r) σ X v := by
  have h := (hasDerivAt_dsig hX hv).const_smul a
  rw [← h.deriv]
  unfold dsig
  congr 1
  funext t
  simp

theorem dsig_smooth (hσ : IsDSHpk k r ε mu σ) {X : Mx k r} (hX : InLieHpk k r X) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hv g₀ hg₀
  let L : Mx k r →L[ℝ] Mx k r := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hL : ∀ x, L x = x * X := by intro x; simp [L]
  refine ⟨U, fun g => fderiv ℝ F g (L g), hU, hgU, ?_, ?_⟩
  · exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  · intro g hg hgH
    have h1 := hasDerivAt_local hX hU hg hF hfF hgH
    have h2 := hasDerivAt_apply hX hv (σ g)
    have e : (fun u : ℝ => σ (g * NormedSpace.exp ((u : ℂ) • X)) v) =
        fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v) := by
      funext t
      rw [Hecke_multiplication k r ε mu H σ hσ g hgH _ (exp_mem hX t)]
      rfl
    rw [e] at h1
    simp only [hL]
    exact h2.unique h1

theorem dsig_conj (hσ : IsDSHpk k r ε mu σ) {X g : Mx k r} (hX : InLieHpk k r X) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hg : g ∈ UH (Hpk k r)) :
    σ g (dsig (k := k) (r := r) σ X v) = dsig (k := k) (r := r) σ (g * X * g⁻¹) (σ g v) := by
  rw [← (hasDerivAt_apply hX hv (σ g)).deriv]
  unfold dsig
  congr 1
  funext t
  obtain ⟨hu, hi, hm⟩ := unitary_Hecke_group k r g hg
  have hi1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have e1 : σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v) = σ (g * NormedSpace.exp ((t : ℂ) • X)) v := by
    rw [Hecke_multiplication k r ε mu H σ hσ g hg _ (exp_mem hX t)]; rfl
  have e2 : σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g v) =
      σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g) v := by
    rw [Hecke_multiplication k r ε mu H σ hσ _ (exp_mem (lie_conj' hX hg) t) g hg]; rfl
  have e3 : (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, e2, e3, Matrix.exp_conj _ _ hu, Matrix.mul_assoc _ g⁻¹ g, hi1, Matrix.mul_one]

theorem dsig_kfin [CompleteSpace H] (hK : PI.KFinSmooth) (hmu : IsHCParam mu) (hσ : IsDSHpk k r ε mu σ)
    {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : IsKFinHpk (k := k) (r := r) σ v) :
    IsKFinHpk (k := k) (r := r) σ (dsig (k := k) (r := r) σ X v) := by
  obtain ⟨S, hfd, hvS, hS⟩ := hv
  have hsm : ∀ x ∈ S, x ∈ smoothVecs (k := k) (r := r) σ := fun x hx =>
    hK k r ε mu H σ hmu hσ x ⟨S, hfd, hx, hS⟩
  refine ⟨Submodule.span ℂ {y | ∃ Y, InLieHpk k r Y ∧ ∃ s ∈ S, y = dsig (k := k) (r := r) σ Y s}, ?_,
    Submodule.subset_span ⟨X, hX, v, hvS, rfl⟩, ?_⟩
  · obtain ⟨fs, hfs⟩ := (Submodule.fg_iff_finiteDimensional S).2 hfd
    have hfsS : ∀ x : fs, (x : H) ∈ S := fun x => hfs ▸ Submodule.subset_span x.2
    choose L hL using fun x : fs => exists_lin (hsm x (hfsS x))
    let b := Module.finBasis ℝ (Mx k r)
    let T : Submodule ℂ H := Submodule.span ℂ (Set.range fun p : fs × Fin (Module.finrank ℝ (Mx k r)) =>
      L p.1 (b p.2))
    haveI : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
    rintro _ ⟨Y, hY, s, hs, rfl⟩
    rw [← hfs] at hs hsm
    show dsig (k := k) (r := r) σ Y s ∈ T
    induction hs using Submodule.span_induction with
    | mem y hy =>
      rw [(hL ⟨y, hy⟩ Y hY).1, ← b.sum_repr Y, map_sum]
      refine T.sum_mem fun j _ => ?_
      rw [map_smul]
      exact T.smul_of_tower_mem _ (Submodule.subset_span ⟨(⟨y, hy⟩, j), rfl⟩)
    | zero => rw [dsig_zero]; exact T.zero_mem
    | add x y hx hy ihx ihy => rw [dsig_add hY (hsm x hx) (hsm y hy)]; exact T.add_mem ihx ihy
    | smul a x hx ih => rw [dsig_smul hY a (hsm x hx)]; exact T.smul_mem a ih
  · intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨Y, hY, s, hs, rfl⟩ := hy
      rw [dsig_conj hσ hY (hsm s hs) hg.1]
      exact Submodule.subset_span ⟨_, lie_conj' hY hg.1, _, hS g hg s hs, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

theorem dsig_skew (hσ : IsDSHpk k r ε mu σ) {X : Mx k r} (hX : InLieHpk k r X) {v w : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    ⟪dsig (k := k) (r := r) σ X v, w⟫_ℂ = -⟪v, dsig (k := k) (r := r) σ X w⟫_ℂ := by
  obtain ⟨h1, hunit⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hσ
  have h := (hasDerivAt_dsig hX hv).inner ℂ (hasDerivAt_dsig hX hw)
  have e : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) v, σ (NormedSpace.exp ((t : ℂ) • X)) w⟫_ℂ) =
      fun _ => ⟪v, w⟫_ℂ := by
    funext t
    exact (LinearMap.norm_map_iff_inner_map_map
      ((σ (NormedSpace.exp ((t : ℂ) • X)) : H →L[ℂ] H) : H →ₗ[ℂ] H)).1 (hunit _ (exp_mem hX t)) v w
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, h1, ContinuousLinearMap.one_apply] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem dsig_TK (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDS ε mu) {X : Mx k r} (hX : InLieHpk k r X) :
    ∀ v ∈ R.TK, v ∈ R.sm ∧ dsig (k := k) (r := r) R.σ X v ∈ R.TK := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hy
    have hs := hK k r ε mu R.H R.σ hR.1 hR.2 v₀ hv₀
    refine ⟨smooth_right_action k r ε mu R.H R.σ hR.2 v₀ hs g hg, ?_⟩
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
    have hi1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have h := dsig_conj hR.2 (lie_conj hX hg) hs hg
    have e : g * (g⁻¹ * X * g) * g⁻¹ = X := by
      calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hi1, Matrix.one_mul, Matrix.mul_one]
    rw [e] at h
    rw [← h]
    exact Submodule.subset_span ⟨g, hg, _, dsig_kfin hK hR.1 hR.2 (lie_conj hX hg) hv₀, rfl⟩
  | zero => exact ⟨R.smSub.zero_mem, by rw [dsig_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    exact ⟨R.smSub.add_mem ihx.1 ihy.1, by rw [dsig_add hX ihx.1 ihy.1]; exact Submodule.add_mem _ ihx.2 ihy.2⟩
  | smul a x _ ih =>
    exact ⟨R.smSub.smul_mem a ih.1, by rw [dsig_smul hX a ih.1]; exact Submodule.smul_mem _ a ih.2⟩

theorem derived_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ X, PI.UpqRep.InLieHpk k r X → (∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧ HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) 0) ∧ (∀ v ∈ R.sm, ∀ g ∈ GG k r, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (g * X * g⁻¹) (R.σ g v)) ∧ (∀ v, R.KFin v → R.KFin (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) ∧ (∀ v ∈ R.TK, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.TK) ∧ (∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, PI.UpqRep.dsig (k := k) (r := r) R.σ X w⟫_ℂ) :=
  fun hK _ _ _ _ R hR _ hX =>
    ⟨fun _ hv => ⟨dsig_smooth hR.2 hX hv, hasDerivAt_dsig hX hv⟩, fun _ hv _ hg => dsig_conj hR.2 hX hv hg,
      fun _ hv => dsig_kfin hK hR.1 hR.2 hX hv, fun v hv => (dsig_TK hK R hR hX v hv).2,
      fun _ hv _ hw => dsig_skew hR.2 hX hv hw⟩

end GlobalTheory.DerivedAction
