import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocFlath
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FixedDense
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.AwayPartMulIotaWPart

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem proj_range {G H X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G H) (σ : Representation ℂ G X) (τ : Representation ℂ G Y) (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hσ : ∀ x, ∃ U : Subgroup G, IsCompact (U : Set G) ∧ IsOpen (U : Set G) ∧ ∀ u ∈ U, σ u x = x)
    (hτ : GroundTheory.Automorphic.IsAdmissible τ) (i : Y →ₗ[ℂ] H) (f : X →ₗ[ℂ] H) (hi : ∀ g y, i (τ g y) = ρ g (i y))
    (hf : ∀ g x, f (σ g x) = ρ g (f x)) {x₀ : X} {y₀ : Y} (h0 : inner ℂ (i y₀) (f x₀) ≠ 0) :
    ∃ f' : X →ₗ[ℂ] H, f' ≠ 0 ∧ (∀ g x, f' (σ g x) = ρ g (f' x)) ∧ ∀ x, f' x ∈ LinearMap.range i := by
  let W := (LinearMap.range i).topologicalClosure
  let L : G → H →ₗᵢ[ℂ] H := fun g => ⟨ρ g, hρ g⟩
  have hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g v hv =>
    map_mem_closure (L g).continuous hv fun z ⟨y, hy⟩ => ⟨τ g y, by rw [hi, hy]; try rfl⟩
  have hP : ∀ g v, W.starProjection (ρ g v) = ρ g (W.starProjection v) := fun g v => by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW g _ (W.starProjection_apply_mem v)) fun w hw => ?_
    have e : w = ρ g (ρ g⁻¹ w) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [← map_sub, e]
    exact ((L g).inner_map_map _ _).trans (W.starProjection_inner_eq_zero v _ (hW _ _ hw))
  refine ⟨W.starProjection.toLinearMap ∘ₗ f, fun e => h0 ?_, fun g x => ?_, fun x => ?_⟩
  · have h1 : W.starProjection (f x₀) = 0 := LinearMap.congr_fun e x₀
    have h2 := W.starProjection_inner_eq_zero (f x₀) (i y₀) (Submodule.le_topologicalClosure _ ⟨y₀, rfl⟩)
    rw [h1, sub_zero] at h2
    exact inner_eq_zero_symm.1 h2
  · exact (congrArg W.starProjection (hf g x)).trans (hP g _)
  · obtain ⟨U, hc, ho, hU⟩ := hσ x
    let ρ' : Representation ℂ G W := (⟨W, fun g _ hv => hW g _ hv⟩ : Subrepresentation ρ).toRepresentation
    let J : Y →ₗ[ℂ] W := i.codRestrict W fun y => Submodule.le_topologicalClosure _ ⟨y, rfl⟩
    have hd : DenseRange J := fun v => by
      rw [closure_subtype]
      refine closure_mono ?_ v.2
      rintro _ ⟨y, rfl⟩
      exact ⟨J y, ⟨y, rfl⟩, rfl⟩
    have h1 := fixedDense G W Y ρ' τ J U hc (fun g v => hρ g v) hτ.1 (fun g y => Subtype.ext (hi g y)) hd
      ⟨_, W.starProjection_apply_mem (f x)⟩ fun u hu => Subtype.ext (by
        show ρ u (W.starProjection (f x)) = W.starProjection (f x)
        rw [← hP, ← hf, hU u hu])
    have := hτ.2 U hc ho
    have h2 : IsClosed (((fixedVectors τ U).map J : Submodule ℂ W) : Set W) := Submodule.closed_of_finiteDimensional _
    obtain ⟨y, -, hy⟩ := closure_minimal (t := (((fixedVectors τ U).map J : Submodule ℂ W) : Set W))
      (by rintro _ ⟨y, hy, rfl⟩; exact Submodule.mem_map_of_mem (mem_fixedVectors.2 hy)) h2 h1
    exact ⟨y, congrArg Subtype.val hy⟩

set_option maxHeartbeats 800000 in
open PositivityTheory.Rg.Rs.C3.Fl in
theorem UpperTheory.ConvolutionTheory.Dp.locIff :
    UpperTheory.ConvolutionTheory.Dp.LocIff := by
  intro E _ _ _ n μ _ π V h w σ
  obtain ⟨J, hi, -, -, hJ'⟩ := UpperTheory.ConvolutionTheory.Dp.locEmb E n μ π V h
  have hJ := hJ' w
  constructor
  · rintro ⟨f, h0, hf⟩
    exact ⟨J ∘ₗ f, fun e => h0 (LinearMap.ext fun x => hi ((LinearMap.congr_fun e x).trans (map_zero J).symm)),
      fun g x => (congrArg J (hf g x)).trans (hJ g _)⟩
  rintro ⟨f, h0, hf⟩
  obtain ⟨D⟩ := nonempty_adelicDecomposition _ (Cm.isIrreducible_toModule π) (Cm.isAdmissible_toModule π)
  obtain ⟨j, hj0, hj⟩ := (locFlath E n π D w
    { V := D.finite.W w, ρ := D.finite.π w, smooth := (D.finite.isAdmissible w).1, irred := D.finite.isIrreducible w }).2
    ⟨Representation.Equiv.refl _⟩
  have hm : ∀ a b v, RG μ (a * b) v = RG μ a (RG μ b v) := fun a b v => by
    simp only [RG]
    rw [retractOne_mul, UnitaryRep.map_mul]; rfl
  have h1 : ∀ v, RG μ 1 v = v := fun v => by
    have e : retractOne (1 : AdelicGLn.AdelicGL E n) = 1 := retractOne_coe 1
    simp only [RG, e, UnitaryRep.map_one]; rfl
  have hn : ∀ a v, ‖RG μ a v‖ = ‖v‖ := fun a v => UnitaryRep.norm_map _ _ _
  have hin : ∀ a u v, inner ℂ (RG μ a u) v = inner ℂ u (RG μ a⁻¹ v) := fun a u v => by
    have e : v = RG μ a (RG μ a⁻¹ v) := by rw [← hm, mul_inv_cancel, h1]
    conv_lhs => rw [e]
    exact (⟨(RG μ a).toLinearMap, hn a⟩ : LL μ →ₗᵢ[ℂ] LL μ).inner_map_map _ _
  let i : D.finite.W w →ₗ[ℂ] LL μ := V.subtype ∘ₗ J ∘ₗ j
  have hi' : ∀ g y, i (D.finite.π w g y) = RG μ (iota n w g) (i y) := fun g y =>
    congrArg Subtype.val ((congrArg J (hj g y)).trans (hJ g _))
  have hex : ∃ a, wPart n w a = 1 ∧ ∃ y x, inner ℂ (RG μ a (i y)) (f x).1 ≠ 0 := by
    by_contra hno
    push Not at hno
    let S : Submodule ℂ (LL μ) := Submodule.span ℂ {v | ∃ a y, wPart n w a = 1 ∧ v = RG μ a (i y)}
    have hS : ∀ v, v ∈ Sᗮ ↔ ∀ a y, wPart n w a = 1 → inner ℂ (RG μ a (i y)) v = 0 := fun v => by
      refine ⟨fun hv a y ha => hv _ (Submodule.subset_span ⟨a, y, ha, rfl⟩), fun hv u hu => ?_⟩
      induction hu using Submodule.span_induction with
      | mem u hu => obtain ⟨a, y, ha, rfl⟩ := hu; exact hv a y ha
      | zero => simp
      | add u u' _ _ h1 h2 => rw [inner_add_left, h1, h2, add_zero]
      | smul c u _ h1 => rw [inner_smul_left, h1, mul_zero]
    rcases h.summand.irred (V ⊓ Sᗮ) inf_le_left (h.summand.closed.inter S.isClosed_orthogonal) (fun g v hv =>
      ⟨h.summand.inv g v hv.1, (hS _).2 fun a y ha => by
        have e : rightRegularRep (rationalGLOne E n) μ g v = RG μ (g⁻¹.1)⁻¹ v := by
          simp only [RG, Subgroup.coe_inv, inv_inv, retractOne_coe]
        rw [e, ← hin, ← hm, ← awayPart_mul_iota_wPart (w := w) (g⁻¹.1 * a), hm, ← hi']
        exact (hS v).1 hv.2 _ _ (wPart_awayPart _)⟩) with hb | hb
    · refine h0 (LinearMap.ext fun x => Subtype.ext ?_)
      have : (f x).1 ∈ V ⊓ Sᗮ := ⟨(f x).2, (hS _).2 fun a y ha => hno a ha y x⟩
      rwa [hb] at this
    · refine hj0 (LinearMap.ext fun y => hi (Subtype.ext ?_))
      have h2 : i y ∈ V ⊓ Sᗮ := hb.ge (J (j y)).2
      have h3 := (hS _).1 h2.2 1 y (map_one _)
      rw [h1] at h3
      have h4 : i y = 0 := inner_self_eq_zero.1 h3
      exact h4.trans (congrArg Subtype.val (map_zero J)).symm
  obtain ⟨a, ha, y, x, hne⟩ := hex
  rw [hin] at hne
  obtain ⟨f', h2, h3, h4⟩ := proj_range (localRepresentationL2 μ w) σ.ρ (D.finite.π w) (fun g v => hn _ v)
    (fun x => (isSmooth_iff_forall_exists σ.ρ).1 σ.smooth x) (D.finite.isAdmissible w) i
    ((RG μ a⁻¹).toLinearMap ∘ₗ V.subtype ∘ₗ f) hi' (fun g x => by
      show RG μ a⁻¹ (f (σ.ρ g x)).1 = RG μ (iota n w g) (RG μ a⁻¹ (f x).1)
      rw [hf, ← hm, ← commute_iota (by rw [map_inv, ha, inv_one]), hm]
      rfl) hne
  have hk : Function.Injective (V.subtype ∘ₗ J) := V.injective_subtype.comp hi
  have h5 : ∀ x, f' x ∈ LinearMap.range (V.subtype ∘ₗ J) := fun x => (h4 x).elim fun y e => ⟨j y, e⟩
  let t := LinearEquiv.ofInjective _ hk
  have ht : ∀ x, (J (t.symm ⟨f' x, h5 x⟩)).1 = f' x := fun x => congrArg Subtype.val (t.apply_symm_apply ⟨f' x, h5 x⟩)
  refine ⟨t.symm.toLinearMap ∘ₗ f'.codRestrict _ h5, fun e => h2 (LinearMap.ext fun x => ?_), fun g x => hi (Subtype.ext ?_)⟩
  · have e1 : t.symm ⟨f' x, h5 x⟩ = 0 := LinearMap.congr_fun e x
    rw [← ht, e1, map_zero]
    rfl
  · refine (ht _).trans ((h3 g x).trans ?_)
    rw [← ht x]
    exact (congrArg Subtype.val (hJ g _)).symm
