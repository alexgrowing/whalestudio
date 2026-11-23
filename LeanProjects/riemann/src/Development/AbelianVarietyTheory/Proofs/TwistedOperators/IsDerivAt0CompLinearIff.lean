import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsoOfSamePeriodMatrixLevel
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections
noncomputable section

namespace GlobalTheory.ThetaWitness

theorem isDerivAt0_comp_linear_iff {g g' : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g' → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem ex_eq_of_der {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {t : SAB H S}
    {y₁ y₂ : Sp ℂ ⟶ S} (hy : y₁ = y₂) {D : Datum H} {g₁ g₂ : ℕ} {ty : Fin g₁ → (E →+* ℂ)}
    {P : D.La →+ (Fin g₁ → ℂ)} (hP : IsPeriod D ty P) {e₁ : (Fin g₁ → ℂ) → (Over.mk y₁ ⟶ t.G)}
    (he₁ : GlobalTheory.UnifPoint.IsExp e₁) (hk₁ : ∀ z, e₁ z = 1 ↔ z ∈ P.range)
    {e₂ : (Fin g₂ → ℂ) → (Over.mk y₂ ⟶ t.G)} (he₂ : GlobalTheory.UnifPoint.IsExp e₂) (hc₂ : {z | e₂ z = 1}.Countable)
    (L : (Fin g₁ → ℂ) ≃ₗ[ℂ] (Fin g₂ → ℂ))
    (huniq : ∀ w w' v, IsDerivAt0 (fun z => (e₁ z).left) w v → IsDerivAt0 (fun z => (e₁ z).left) w' v → w = w')
    (hb : ∀ a, ∃ v, IsDerivAt0 (fun z => (e₁ z).left) (Pi.single a 1) v ∧
      IsDerivAt0 (fun z => (e₂ z).left) (L (Pi.single a 1)) v) :
    ∀ z, (e₁ z).left = (e₂ (L z)).left := by
  subst hy
  have hL : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hLd : Differentiable ℂ L := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hhol : IsHolTo Set.univ (fun z => (e₂ (L z)).left) := fun U f => by
    obtain ⟨h1, h2⟩ := he₂.2.2.1 U f
    refine ⟨?_, ?_⟩
    · exact h1.preimage hL
    · refine h2.comp hLd.differentiableOn ?_
      intro z hz; exact ⟨trivial, hz.2⟩
  obtain ⟨h, hh⟩ := GlobalTheory.UnifPoint.exists_linearEquiv_of_period hP he₁ hk₁ (e₀ := fun z => e₂ (L z))
    (fun z w => by simp only [map_add]; exact he₂.1 _ _) (he₂.2.1.comp L.surjective) hhol
    (by
      refine (hc₂.preimage_of_injOn L.injective.injOn).mono ?_
      intro z hz; exact hz)
  have hid : ∀ a, h (Pi.single a 1) = Pi.single a 1 := fun a => by
    obtain ⟨v, h1, h2⟩ := hb a
    have d2 := (isDerivAt0_comp_linear_iff _ he₂.2.2.1 L.toLinearMap _ v).2 h2
    have d3 : IsDerivAt0 (fun z => (e₁ (h z)).left) (Pi.single a 1) v := by
      convert d2 using 2 with z
      rw [hh]; rfl
    have d4 := (isDerivAt0_comp_linear_iff _ he₁.2.2.1 h.toLinearMap _ v).1 d3
    exact huniq _ _ v d4 h1
  have hlin : h.toLinearMap = LinearMap.id :=
    LinearMap.pi_ext' fun a => LinearMap.ext_ring (by simpa using hid a)
  have hid' : ∀ z, h z = z := fun z => LinearMap.congr_fun hlin z
  intro z
  rw [← hh z, hid']

end GlobalTheory.ThetaWitness

namespace GlobalTheory.ThetaWitness

theorem theta_value_indep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W₁ W₂ : UnfAt U k x)
    (Y₁ : UnitAt W₁) (Y₂ : UnitAt W₂) (v : Fin r → E),
    Complex.exp (-(Real.pi / 2 * hermForm Y₁.Hm (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2)
        (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2))) *
        Y₁.θ (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) =
      Complex.exp (-(Real.pi / 2 * hermForm Y₂.Hm (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2)
        (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2))) *
        Y₂.θ (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W₁ W₂ Y₁ Y₂ v
  let L : (Fin W₁.g → ℂ) ≃ₗ[ℂ] (Fin W₂.g → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ (W₂.e.trans W₁.e.symm)
  have hL : ∀ z j, L z j = z (W₁.e.symm (W₂.e j)) := fun z j => rfl
  have hLd : Differentiable ℂ L := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hp : (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2) =
      L (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) := by
    funext j
    rw [hL]
    generalize hs : W₁.e (W₁.e.symm (W₂.e j)) = s
    rw [Equiv.apply_symm_apply] at hs
    subst hs; rfl
  rw [hp]
  generalize (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) = z

  have hPL : ∀ a, L (W₁.Pm a) = W₂.Pm ((W₂.φ k).symm (W₁.φ k a)) := fun a => by
    funext j
    rw [hL, W₁.pm_eq, W₂.pm_eq, LinearEquiv.apply_symm_apply]
    generalize hs : W₁.e (W₁.e.symm (W₂.e j)) = s
    rw [Equiv.apply_symm_apply] at hs
    subst hs; rfl
  have hEF : ∀ a b, (W₂.F.Di (W₂.ik k)).EF ((W₂.φ k).symm (W₁.φ k a)) ((W₂.φ k).symm (W₁.φ k b)) =
      (W₁.F.Di (W₁.ik k)).EF a b := fun a b => by
    have h1 := W₂.isom k ((W₂.φ k).symm (W₁.φ k a)) ((W₂.φ k).symm (W₁.φ k b))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← W₁.isom k a b] at h1
    exact_mod_cast h1

  have hspan : Submodule.span ℝ (Set.range W₁.Pm) = ⊤ := W₁.per.2.2.2.1
  have hHH : ∀ z w, hermForm Y₂.Hm (L z) (L w) = hermForm Y₁.Hm z w := fun z w => by
    have := GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im Y₂.Hm L.toLinearMap Y₁.Hm LinearMap.id hspan (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [LinearEquiv.coe_coe, LinearMap.id_coe, id_eq]
      rw [hPL, hPL, Y₂.c1, Y₁.c1, hEF]) z w
    simpa using this

  have hexp : ∀ W : UnfAt U k x, GlobalTheory.UnifPoint.IsExp (W.F.ex (W.ik k) W.Pm) := fun W =>
    ⟨W.F.ex_add _ _ W.per, W.F.ex_onto _ _ W.per, GlobalTheory.ClassUniq.isHolTo_ex W.F _ _ W.per,
      (W.F.ex_diff _ _ W.per).1, (W.F.ex_diff _ _ W.per).2⟩
  have hLs : ∀ a, L (Pi.single a 1) = Pi.single (W₂.e.symm (W₁.e a)) 1 := fun a => by
    funext j
    rw [hL]
    simp only [Pi.single_apply]
    exact if_congr (by rw [Equiv.symm_apply_eq, Equiv.eq_symm_apply]) rfl rfl
  have hex : ∀ z, (W₁.F.ex (W₁.ik k) W₁.Pm z).left = (W₂.F.ex (W₂.ik k) W₂.Pm (L z)).left :=
    ex_eq_of_der (t := Xo.univ.t) (W₁.pt.symm.trans W₂.pt) W₁.per (hexp W₁) (W₁.F.ex_ker _ _ W₁.per) (hexp W₂)
      ((GlobalTheory.UnifPoint.countable_periods W₂.per).mono fun z hz => (W₂.F.ex_ker _ _ W₂.per z).1 hz) L
      (fun w w' v h h' => by
        have tn := GlobalTheory.isDerivAt0_ex_isTanAt _ _ _ _ Xo _ _ _ W₁.F (W₁.ik k) W₁.Pm W₁.per
        exact (tn.2.2 v (tn.1 w v h)).unique h h')
      (fun a => ⟨(U.un k x).u (W₁.e a).1 (W₁.e a).2, by simpa using W₁.der (W₁.e a).1 (W₁.e a).2, by
        rw [hLs]; simpa using W₂.der (W₁.e a).1 (W₁.e a).2⟩)

  have hper1 : ∀ a ∈ W₁.Pm.range, ∀ z, W₁.F.ex (W₁.ik k) W₁.Pm (z + a) = W₁.F.ex (W₁.ik k) W₁.Pm z :=
    fun a ha z => by
      rw [W₁.F.ex_add _ _ W₁.per, (W₁.F.ex_ker _ _ W₁.per a).2 ha]
      exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (W₂.F.ex (W₂.ik k) W₂.Pm (L z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [← hex]; exact hz
  have hspan' : Submodule.span ℝ (W₁.Pm.range : Set (Fin W₁.g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hspan
  have hfr : ∀ j z, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Y₂.fr j (L z) = Y₁.fr j z :=
    GlobalTheory.UnitFrameGen.frames_eq W₁.Pm.range hspan' (fun j => {z | ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex W₁.F _ _ W₁.per _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hper1 a ha]; exact hz)
      Y₁.fr (fun j z => Y₂.fr j (L z))
      (fun j j' z => valAt' (W₁.F.ex (W₁.ik k) W₁.Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Y₁.Hm z a).re + Real.pi / 2 * (hermForm Y₁.Hm a a).re))
      Y₁.c2 (fun j => (Y₂.c2 j).comp hLd.differentiableOn fun z hz => tr j z hz) Y₁.c3
      (fun j j' z h1 h2 => Y₁.c4 j j' z ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := Y₂.c4 j j' (L z) ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [← hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [map_zero] at t0 ⊢
        rw [Y₁.c5 j hz, Y₂.c5 j t0])
      (by
        rintro j _ ⟨a, rfl⟩ z hz
        exact GlobalTheory.UnitFrameGen.norm_factor Y₁.Hm _ _ _ _ _ (Y₁.c6 a j z).1 ((Y₁.c6 a j z).2 hz))
      (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := GlobalTheory.UnitFrameGen.norm_factor Y₂.Hm _ _ _ _ _ (Y₂.c6 ((W₂.φ k).symm (W₁.φ k a)) j (L z)).1
          ((Y₂.c6 ((W₂.φ k).symm (W₁.φ k a)) j (L z)).2 (tr j z hz))
        rw [← hPL, hHH, hHH, ← map_add] at this
        exact this)

  have hθ : Y₂.θ (L z) = Y₁.θ z := by
    obtain ⟨j, hj⟩ := hcov z
    have hw0 : (W₁.F.ex (W₁.ik k) W₁.Pm z).left ≫ Xo.univ.t.G.hom = (U.un k x).x :=
      (Over.w (W₁.F.ex (W₁.ik k) W₁.Pm z)).trans W₁.pt.symm
    let p : Over.mk (U.un k x).x ⟶ Xo.univ.t.G := Over.homMk (W₁.F.ex (W₁.ik k) W₁.Pm z).left hw0
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := Y₁.c7 j z _ e1 e2 hj
    have v2 := Y₂.c7 j (L z) _ (e1.trans (hex z)) e2 (tr j z hj)
    rw [hfr j z hj] at v2
    exact mul_right_cancel₀ (Y₁.c3 j z hj) (v2.symm.trans v1)
  rw [hHH, hθ]

end GlobalTheory.ThetaWitness
