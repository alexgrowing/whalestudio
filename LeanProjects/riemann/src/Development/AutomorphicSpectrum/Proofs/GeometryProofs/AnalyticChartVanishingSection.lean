import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPair
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt

variable {X : Scheme.{0}}

abbrev cst (s : X ⟶ Sp ℂ) (V : X.Opens) : ℂ →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)).hom

theorem top_le_spMap (hV' : X.Opens) (hV : IsAffineOpen hV') (ψ : Γ(X, hV') →+* ℂ) :
    ⊤ ≤ (spMap ψ ≫ hV.fromSpec) ⁻¹ᵁ hV' := by
  have h : ∀ p, hV.fromSpec p ∈ hV' := fun p => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨p, rfl⟩
  have e := h (spMap ψ (show Sp ℂ from IsLocalRing.closedPoint ℂ))
  rw [← Scheme.Hom.comp_apply] at e
  exact (top_le_iff_centre _ hV').2 e

theorem val_spMap {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) (a : Γ(X, V)) :
    valAt' (spMap ψ ≫ hV.fromSpec) V a = ψ a :=
  (valAt'_fromSpec hV _ a).trans (valAt'_spMap ψ a)

theorem eq_spMap {V : X.Opens} (hV : IsAffineOpen V) (y : Sp ℂ ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V) :
    y = spMap (valHom y V h) ≫ hV.fromSpec := by
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact h (Set.mem_univ p)
  have hl : IsOpenImmersion.lift hV.fromSpec y hr ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, V) →+* ℂ, spMap φ = IsOpenImmersion.lift hV.fromSpec y hr :=
    ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr)).hom, Spec.map_preimage _⟩
  rw [← hφ] at hl
  have e : valHom y V h = φ := RingHom.ext fun a => by
    show valAt' y V a = φ a
    rw [← hl]
    exact val_spMap hV φ a
  rw [e, hl]

theorem fromSpec_comp_structure_map (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) : hV.fromSpec ≫ s = spMap (cst s V) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  exact (Spec.map_comp _ _).symm

theorem over_iff (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) :
    (spMap ψ ≫ hV.fromSpec) ≫ s = 𝟙 _ ↔ ψ.comp (cst s V) = RingHom.id ℂ := by
  rw [Category.assoc, fromSpec_comp_structure_map]
  constructor
  · intro h
    have e : spMap (ψ.comp (cst s V)) = spMap (RingHom.id ℂ) := (Spec.map_comp _ _).trans (h.trans (Spec.map_id _).symm)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  · intro h
    refine (Spec.map_comp _ _).symm.trans ?_
    exact (congrArg spMap h).trans (Spec.map_id _)

theorem comp_cst (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) (y : Sp ℂ ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V)
    (hy : y ≫ s = 𝟙 _) : (valHom y V h).comp (cst s V) = RingHom.id ℂ :=
  (over_iff s hV _).1 (by rw [← eq_spMap hV y h]; exact hy)

theorem isOpen_near {E : Type} [TopologicalSpace E] {T : Set E} (hT : IsOpen T) {n : ℕ} (v : Fin n → E → ℂ)
    (c : Fin n → ℂ) (ε : ℝ) (hv : ∀ j, ContinuousOn (v j) T) : IsOpen {b ∈ T | ∀ j, ‖v j b - c j‖ < ε} := by
  rw [isOpen_iff_mem_nhds]
  rintro b ⟨hb, hj⟩
  have h : ∀ j, ∀ᶠ y in 𝓝 b, ‖v j y - c j‖ < ε := fun j =>
    (((hv j).continuousAt (hT.mem_nhds hb)).sub continuousAt_const).norm.eventually_lt continuousAt_const (hj j)
  filter_upwards [hT.mem_nhds hb, Filter.eventually_all.2 h] with y h₁ h₂ using ⟨h₁, h₂⟩

theorem isChart_of_data (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) {D M : ℕ} (g : Fin M → Γ(X, V))
    (f : Fin D → Γ(X, V)) {B₀ : Set (Fin D → ℂ)} {ε : ℝ} (Ψ : (Fin D → ℂ) → (Γ(X, V) →+* ℂ)) (ψ₀ : Γ(X, V) →+* ℂ)
    (o : IsOpen B₀) (a₁ : ∀ b ∈ B₀, (Ψ b).comp (cst s V) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i)
    (a₂ : ∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B₀)
    (a₃ : ∀ ψ : Γ(X, V) →+* ℂ, ψ.comp (cst s V) = RingHom.id ℂ → (∀ j, ‖ψ (g j) - ψ₀ (g j)‖ < ε) →
      (fun i => ψ (f i)) ∈ B₀ ∧ Ψ (fun i => ψ (f i)) = ψ) :
    IsChart s {b ∈ B₀ | ∀ j, ‖Ψ b (g j) - ψ₀ (g j)‖ < ε} (fun b => spMap (Ψ b) ≫ hV.fromSpec) := by
  have oB : IsOpen {b ∈ B₀ | ∀ j, ‖Ψ b (g j) - ψ₀ (g j)‖ < ε} :=
    isOpen_near o (fun j b => Ψ b (g j)) _ ε fun j => (a₂ (g j)).continuousOn
  refine ⟨oB, ?_, fun b hb => (over_iff s hV _).2 (a₁ b hb.1).1, ?_⟩
  · exact isHolTo_comp (isHolTo_spMap oB fun a => (a₂ a).mono fun b hb => hb.1) hV.fromSpec
  intro m B' y oB' hy ov b₀ h₀ b₁ h₁ e
  have oT : IsOpen {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} := (hy V 0).1
  have dv : ∀ a : Γ(X, V), DifferentiableOn ℂ (fun b => valAt' (y b) V a) {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} := fun a => (hy V a).2
  have oT' := isOpen_near oT (fun j b => valAt' (y b) V (g j)) (fun j => ψ₀ (g j)) ε fun j => (dv (g j)).continuousOn
  have v₀ : ∀ a, valAt' (y b₀) V a = Ψ b₁ a := fun a => by rw [e]; exact val_spMap hV _ a
  have m₀ : b₀ ∈ {b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} | ∀ j, ‖valAt' (y b) V (g j) - ψ₀ (g j)‖ < ε} :=
    ⟨⟨h₀, by rw [e]; exact top_le_spMap V hV _⟩, fun j => by rw [v₀]; exact h₁.2 j⟩
  obtain ⟨δ, δ0, hδ⟩ := Metric.isOpen_iff.1 oT' b₀ m₀
  refine ⟨δ, fun b i => valAt' (y b) V (f i), δ0, fun b hb => (hδ hb).1.1,
    differentiableOn_pi.2 fun i => (dv (f i)).mono fun b hb => (hδ hb).1, funext fun i => ?_, fun b hb => ?_⟩
  · show valAt' (y b₀) V (f i) = b₁ i
    rw [v₀]; exact (a₁ b₁ h₁.1).2 i
  · have t := (hδ hb).1.2
    have k := a₃ (valHom (y b) V t) (comp_cst s hV _ t (ov b (hδ hb).1.1)) (hδ hb).2
    have k₂ : Ψ (fun i => valAt' (y b) V (f i)) = valHom (y b) V t := k.2
    refine ⟨⟨k.1, fun j => ?_⟩, ?_⟩
    · rw [k₂]; exact (hδ hb).2 j
    · show y b = spMap (Ψ (fun i => valAt' (y b) V (f i))) ≫ hV.fromSpec
      rw [k₂]; exact eq_spMap hV _ t

theorem res_cst (s : X ⟶ Sp ℂ) {U V : X.Opens} (h : V ≤ U) (c : ℂ) :
    (X.presheaf.map (homOfLE h).op).hom (cst s U c) = cst s V c :=
  congr($(Scheme.Hom.appLE_map s (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))

theorem exists_std (s : X ⟶ Sp ℂ) [Smooth s] (q : X) (M : X.Opens) (hq : q ∈ M) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (D : ℕ), V ≤ M ∧ q ∈ V ∧ (cst s V).IsStandardSmoothOfRelativeDimension D := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s q
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h2 : y = s q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact hle hp
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(X, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  obtain ⟨a, haM, hqa⟩ := hU.exists_basicOpen_le (V := M) ⟨q, hq⟩ hp
  refine ⟨X.basicOpen a, hU.basicOpen a, n, haM, hqa, ?_⟩
  have := hU.isLocalization_basicOpen a
  have h1 : (algebraMap Γ(X, U) Γ(X, X.basicOpen a)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway a
  have h2 : (cst s U).IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have h3 := h1.comp h2
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact (res_cst s (X.basicOpen_le a) c).symm

theorem isDomain_of_le {Z V : X.Opens} [AlgebraicGeometry.IsIntegral Z.toScheme] (h : V ≤ Z) {q : X} (hq : q ∈ V) :
    IsDomain Γ(X, V) := by
  haveI : Nonempty V.toScheme := ⟨⟨q, hq⟩⟩
  haveI : AlgebraicGeometry.IsIntegral V.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE h)
  haveI : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨q, hq⟩, trivial⟩⟩
  exact MulEquiv.isDomain Γ(V.toScheme, ⊤) (Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv.toMulEquiv

theorem exists_chart : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ))
    (f : Fin D → A) (a : A), IsOpen O → O.Nonempty →
    (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0) →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W N : X.Opens) (x : Sp ℂ ⟶ X), Smooth s →
    IsCptGen ξ → genPt ξ ∈ W → x ≫ s = 𝟙 _ → genPt ξ ⤳ centre x → centre x ∈ N →
    ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsChart s B Y ∧ b₁ ∈ B ∧
      Y b₁ = x ∧ (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) ∧
      ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W := by
  intro hring X s Ω _ ξ W N x hs hξ hW hxs hgx hxN
  haveI := hs
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨Z, hZ, -, hZi⟩ := cpt_open_integral X Ω ξ hξ
  obtain ⟨V, hV, D, hVM, hxV, hstd⟩ := exists_std s (centre x) (N ⊓ Z) ⟨hxN, (hZ _).2 hgx⟩
  letI alg : Algebra ℂ Γ(X, V) := (cst s V).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D ℂ Γ(X, V) := hstd
  haveI : IsDomain Γ(X, V) := isDomain_of_le (hVM.trans inf_le_right) hxV
  have hxt : ⊤ ≤ x ⁻¹ᵁ V := (top_le_iff_centre x V).2 hxV
  have h₀ : (valHom x V hxt).comp (algebraMap ℂ Γ(X, V)) = RingHom.id ℂ := comp_cst s hV x hxt hxs
  obtain ⟨M, g, f, B₀, ε, Ψ, ε0, o, a₁, a₂, a₃⟩ := anChart_alg D (RingHom.id ℂ) (valHom x V hxt) h₀
  have hc := isChart_of_data s hV g f Ψ (valHom x V hxt) o a₁ a₂ a₃
  have m₁ := a₃ _ h₀ fun _ => by simpa using ε0
  have hY : ∀ b, centre (spMap (Ψ b) ≫ hV.fromSpec) ∈ V := fun b => (top_le_iff_centre _ V).1 (top_le_spMap V hV _)
  refine ⟨D, _, _, fun i => valHom x V hxt (f i), hc, ⟨m₁.1, fun j => ?_⟩, ?_, fun b _ => ⟨(hVM (hY b)).1, (hZ _).1 (hVM (hY b)).2⟩, ?_⟩
  · rw [m₁.2]; simpa using ε0
  · show spMap (Ψ fun i => valHom x V hxt (f i)) ≫ hV.fromSpec = x
    rw [m₁.2]; exact (eq_spMap hV x hxt).symm
  intro O oO sO nO
  have hgV : genPt ξ ∈ V := genPt_mem hgx hxV
  obtain ⟨a, haW, haξ⟩ := hV.exists_basicOpen_le (V := W) ⟨genPt ξ, hW⟩ hgV
  have a0 : a ≠ 0 := by
    rintro rfl
    simp at haξ
  by_contra hc'
  push_neg at hc'
  refine a0 (hring Γ(X, V) D O Ψ f a oO nO (fun b hb => a₁ b (sO hb).1) fun b hb => ?_)
  by_contra hne
  refine hc' b hb (haW ?_)
  have hv : valAt' (spMap (Ψ b) ≫ hV.fromSpec) V a ≠ 0 := by rw [val_spMap]; exact hne
  exact (valAt'_ne_zero_iff _ V (top_le_spMap V hV _) a _).1 hv

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt
