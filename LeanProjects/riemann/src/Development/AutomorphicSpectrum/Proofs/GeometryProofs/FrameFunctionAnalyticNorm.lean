import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NotIsLineFnZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesAnalyticStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEigenLineGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionsFlatAgreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicChartNearPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentOpenStalksDomainStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueLocallyRegularFunctionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointValueHolomorphicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Cmp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem valAt_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (h : IsCptGen ξ) {R : Type} [CommRing R]
    [IsLocalRing R] {z : Sp R ⟶ X} {a : Ω} {r r' : R} (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨p, s, e, rfl⟩ := h₁
  obtain ⟨p', s', e', rfl⟩ := h₂
  have : s = s' := h.inj ⟨centre z, p⟩ (e.trans e'.symm)
  rw [this]

theorem chg_eq {U : Set (Xo.XF c)} {τ : E →+* ℂ} {σ : c.F →+* ℂ} {Φ : CFn Xo c} {φ : FrameFn Xo c}
    (hΦ : IsUnitAn τ σ Φ) (hφ : IsLineFn U τ φ) {y : Sp ℂ ⟶ Xo.XF c} {v v' : Vecs y D.p} {w w' : Vecs y D.q}
    (h : IsFramed U τ σ y v w) (h' : IsFramed U τ σ y v' w') {κ : ℂ} (e : φ ℂ y v w = κ * Φ y v w) :
    φ ℂ y v' w' = κ * Φ y v' w' := by
  have mono : ∀ {v : Vecs y D.p} {w : Vecs y D.q}, IsFramed U τ σ y v w → IsFramed Set.univ τ σ y v w :=
    fun h => ⟨h.1, Set.subset_univ _, h.2.2⟩
  choose A hA _ using fun i => h.2.2.1.2 (v' i) (h'.2.2.1.1 i)
  choose B hB _ using fun j => h.2.2.2.2 (w' j) (h'.2.2.2.1 j)
  have hmix : IsFramed U τ σ y v' w := ⟨h.1, h.2.1, h'.2.2.1, h.2.2.2⟩
  have d₁ := hφ.chg ℂ σ y v w v' w (Matrix.of A) 1 h hmix hA (FlatModel.isComb_one fun j => (h.2.2.2.1 j).1)
  have dA : (Matrix.of A).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, Matrix.det_one, _root_.mul_one] at d₁
    exact hφ.ne ℂ σ y v w h d₁.symm
  have c₁ := hφ.chg ℂ σ y v w v' w' (Matrix.of A) (Matrix.of B) h h' hA hB
  have c₂ := hΦ.chg y v w v' w' (Matrix.of A) (Matrix.of B) (mono h) (mono h') hA hB
  apply mul_right_cancel₀ dA
  rw [c₁, _root_.mul_assoc, c₂, ← _root_.mul_assoc, e]

theorem iMulti_eq_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ} {b e : Fin n → V}
    (he : LinearIndependent K e) (h : Submodule.span K (Set.range b) = Submodule.span K (Set.range e)) :
    ∃ d : K, exteriorPower.ιMulti K n b = d • exteriorPower.ιMulti K n e := by
  classical
  let S := Submodule.span K (Set.range e)
  let B : Module.Basis (Fin n) K S := Module.Basis.span he
  let g : S [⋀^Fin n]→ₗ[K] ⋀[K]^n V := (exteriorPower.ιMulti K n).compLinearMap S.subtype
  have key : g = (LinearMap.toSpanSingleton K _ (g B)).compAlternatingMap B.det := by
    refine Module.Basis.ext_alternating B fun v hv => ?_
    let s : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have e₁ : (fun i => B (v i)) = (B ∘ s) := rfl
    rw [e₁, AlternatingMap.map_perm]
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.toSpanSingleton_apply]
    rw [AlternatingMap.map_perm, Module.Basis.det_self]
    simp
  have hb : ∀ i, b i ∈ S := fun i => by
    show b i ∈ Submodule.span K (Set.range e)
    rw [← h]; exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨B.det (fun i => ⟨b i, hb i⟩), ?_⟩
  have e₁ : exteriorPower.ιMulti K n b = g (fun i => ⟨b i, hb i⟩) := rfl
  have e₂ : exteriorPower.ιMulti K n e = g B := by
    show _ = exteriorPower.ιMulti K n (fun i => ((B i : S) : V))
    congr 1
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply he i).symm
  rw [e₁, e₂]
  conv_lhs => rw [key]
  simp

theorem eq_zero_on_ball {d : ℕ} {h : (Fin d → ℂ) → ℂ} (hd : DifferentiableOn ℂ h (ball 0 1)) {ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ z ∈ ball (0 : Fin d → ℂ) 1, z ∈ ball (0 : Fin d → ℂ) ε → h z = 0) :
    ∀ z ∈ ball (0 : Fin d → ℂ) 1, h z = 0 := by
  intro z hz
  let L : ℂ → (Fin d → ℂ) := fun t => t • z
  have hL : Continuous L := by fun_prop
  let S : Set ℂ := L ⁻¹' ball 0 1
  have hSo : IsOpen S := isOpen_ball.preimage hL
  have hSc : IsPreconnected S := by
    have : Convex ℝ S := by
      intro a ha b hb s t hs ht hst
      have := (convex_ball (0 : Fin d → ℂ) 1) ha hb hs ht hst
      show (s • a + t • b) • z ∈ ball (0 : Fin d → ℂ) 1
      rwa [add_smul, smul_assoc, smul_assoc]
    exact this.isPreconnected
  have h0S : (0 : ℂ) ∈ S := by simp [S, L]
  have h1S : (1 : ℂ) ∈ S := by simpa [S, L] using hz
  have hl : DifferentiableOn ℂ (fun t => h (L t)) S :=
    hd.comp (by fun_prop) (fun t ht => ht)
  have han := hl.analyticOnNhd hSo
  have hev : (fun t => h (L t)) =ᶠ[𝓝 0] 0 := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℂ), L t ∈ ball (0 : Fin d → ℂ) 1 :=
      hL.continuousAt.eventually_mem (by simpa [L] using isOpen_ball.mem_nhds (mem_ball_self one_pos))
    have h2 : ∀ᶠ t in 𝓝 (0 : ℂ), L t ∈ ball (0 : Fin d → ℂ) ε :=
      hL.continuousAt.eventually_mem (by simpa [L] using isOpen_ball.mem_nhds (mem_ball_self hε))
    filter_upwards [h1, h2] with t a b using h0 _ a b
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hSc h0S hev h1S
  simpa [L] using this

theorem mem_basicOpen {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (χ : Γ(X, V) →+* ℂ) (g : Γ(X, V))
    (h : χ g ≠ 0) : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ X.basicOpen g := by
  intro t _
  have hm : (spMap χ) t ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g := by
    rw [hV.fromSpec_preimage_basicOpen]
    let t' : PrimeSpectrum ℂ := t
    show χ g ∉ t'.asIdeal
    rw [Ideal.eq_bot_of_prime t'.asIdeal]
    simpa using h
  exact hm

theorem comp_mem {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (χ : Γ(X, V) →+* ℂ) (t : Sp ℂ) :
    (spMap χ ≫ hV.fromSpec) t ∈ V := by
  have h : (spMap χ ≫ hV.fromSpec) t ∈ Set.range hV.fromSpec := ⟨spMap χ t, by simp⟩
  rwa [hV.range_fromSpec] at h

theorem exists_near {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {d : ℕ}
    {ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)} (hψ : IsHolPts (ball 0 1) ψ)
    (h0 : ∀ g : Γ(X, V), (∀ z ∈ ball (0 : Fin d → ℂ) 1, ψ z g = 0) → g = 0) (W : X.Opens) {p : X} (hpV : p ∈ V)
    (hpW : p ∈ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ ball (0 : Fin d → ℂ) 1, z ∈ ball (0 : Fin d → ℂ) ε ∧ ⊤ ≤ (spMap (ψ z) ≫ hV.fromSpec) ⁻¹ᵁ W := by
  obtain ⟨g, hg, hpg⟩ := hV.exists_basicOpen_le (V := W) ⟨p, hpW⟩ hpV
  by_contra hcon
  push_neg at hcon
  have hz : ∀ z ∈ ball (0 : Fin d → ℂ) 1, z ∈ ball (0 : Fin d → ℂ) ε → ψ z g = 0 := by
    intro z h₁ h₂
    by_contra hne
    exact hcon z h₁ h₂ ((mem_basicOpen hV (ψ z) g hne).trans
      (Scheme.Hom.preimage_mono _ hg))
  have := h0 g (eq_zero_on_ball (hψ.2 g) hε hz)
  subst this
  simp at hpg

end GlobalTheory.CompanionTheory.Ar.Flat.Cmp

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Cmp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def vecAt {S : Scheme.{0}} {G : Over S} {R R' : Type} [CommRing R] [CommRing R'] (χ : R →+* R') {x : Sp R ⟶ S}
    {y : Sp R' ⟶ S} (e : spMap χ ≫ x = y) (v : epsAt x ⟶ G) : epsAt y ⟶ G :=
  Over.homMk (spMap (dualMap χ) ≫ v.left) (by
    subst e
    have hw := Over.w v
    have h2 : spMap (dualMap χ) ≫ spMap (algebraMap R (DualNumber R)) =
        spMap (algebraMap R' (DualNumber R')) ≫ spMap χ := by
      have h3 : (dualMap χ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp χ :=
        RingHom.ext fun r => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [h3]
    show (spMap (dualMap χ) ≫ v.left) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap χ ≫ x
    rw [Category.assoc, hw]
    show spMap (dualMap χ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = _
    rw [← Category.assoc, h2, Category.assoc])

variable {O : Type} [CommRing O] {β : O →+* c.F}

theorem ext_frames {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {τ : E →+* ℂ} {σ : c.F →+* ℂ}
    {Φ : CFn Xo c} {φ : FrameFn Xo c}
    (hO : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (hτ : τ (H.rt : E) = H.rt0) (hΦ : IsUnitAn τ σ Φ) (hφ : IsLineFn U τ φ) {a : ⋀[Z.Ω]^D.p Z.V}
    {b : ⋀[Z.Ω]^D.q Z.V} (hr : Represents Y U τ Z.M a b φ)
    (ha : ∀ c₁ : Fin D.p → Z.V, LinearIndependent Z.Ω c₁ →
      Submodule.span Z.Ω (Set.range c₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) →
      ∃ α : Z.Ω, a = α • exteriorPower.ιMulti Z.Ω D.p c₁)
    (hb : ∀ c₂ : Fin D.q → Z.V, LinearIndependent Z.Ω c₂ →
      Submodule.span Z.Ω (Set.range c₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) →
      ∃ α : Z.Ω, b = α • exteriorPower.ιMulti Z.Ω D.q c₂)
    (W : (Xo.XF c).Opens) (hgW : genPt Z.ξ₀ ∈ W) {κ₀ : ℂ}
    (hW : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ y ⁻¹ᵁ W → Set.range y ⊆ U →
      ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ σ y v w ∧ φ ℂ y v w = κ₀ * Φ y v w) :
    ∀ (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ σ y v w → φ ℂ y v w = κ₀ * Φ y v w := by
  intro y₀ v₀ w₀ hf
  obtain ⟨U', hU', hdom⟩ := GlobalTheory.T.component_open_stalks_domain _ H D l Xo c O β Y U Z hO
  obtain ⟨V₀, hV₀, c₁, c₂, vR, wR, hy₀, l₁, s₁, l₂, s₂, hfr⟩ := GlobalTheory.T.component_point_value_holomorphic _ H D l Xo c O β Y U Z τ σ y₀ hO hτ hf.1 hf.2.1
  obtain ⟨α, hα⟩ := ha c₁ l₁ s₁
  obtain ⟨κ', hκ'⟩ := hb c₂ l₂ s₂
  have eU : ∀ χ : Γ(Xo.XF c, V₀) →+* ℂ, spMap χ ≫ under hV₀.fromSpec = under (spMap χ ≫ hV₀.fromSpec) :=
    fun χ => (Category.assoc _ _ _).symm
  let vat : ∀ χ : Γ(Xo.XF c, V₀) →+* ℂ, Vecs (spMap χ ≫ hV₀.fromSpec) D.p := fun χ a => vecAt χ (eU χ) (vR a)
  let wat : ∀ χ : Γ(Xo.XF c, V₀) →+* ℂ, Vecs (spMap χ ≫ hV₀.fromSpec) D.q := fun χ a => vecAt χ (eU χ) (wR a)
  have val : ∀ χ : Γ(Xo.XF c, V₀) →+* ℂ, (spMap χ ≫ hV₀.fromSpec) ≫ pullback.snd _ _ = spMap σ →
      Set.range (spMap χ ≫ hV₀.fromSpec) ⊆ U → IsFramed U τ σ _ (vat χ) (wat χ) ∧
        ValAt (Z.ξ₀ ≫ Y.j) ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (α / κ') (φ ℂ _ (vat χ) (wat χ)) := by
    intro χ h1 h2
    obtain ⟨f1, f2, f3⟩ := hfr χ (vat χ) (wat χ) h1 h2 (fun _ => rfl) (fun _ => rfl)
    exact ⟨f1, hr ℂ σ _ _ _ c₁ c₂ α κ' f1 hα hκ' f2 f3⟩
  have hrange : Set.range y₀ ⊆ Set.range hV₀.fromSpec := by
    rw [hV₀.range_fromSpec]
    rintro _ ⟨t, rfl⟩
    exact hy₀ (show t ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : Γ(Xo.XF c, V₀) →+* ℂ, spMap χ₀ ≫ hV₀.fromSpec = y₀ :=
    ⟨(Spec.preimage (IsOpenImmersion.lift hV₀.fromSpec y₀ hrange)).hom, by simp [spMap]⟩
  have hval₀ : ∃ r₀, ValAt (Z.ξ₀ ≫ Y.j) (y₀ ≫ Y.j) (α / κ') r₀ := by
    rw [← hχ₀]
    exact ⟨_, (val χ₀ (by rw [hχ₀]; exact hf.1) (by rw [hχ₀]; exact hf.2.1)).2⟩
  obtain ⟨r₀, hr₀⟩ := hval₀
  obtain ⟨W₁, hW₁, hsec⟩ := GlobalTheory.T.value_locally_regular_function _ _ Y.j Z.Ω (Z.ξ₀ ≫ Y.j) Z.gen y₀ _ r₀ hr₀
  have hcU : centre y₀ ∈ U := hf.2.1 ⟨_, rfl⟩
  have hy₀' : ⊤ ≤ y₀ ⁻¹ᵁ (V₀ ⊓ U' ⊓ W₁) := by
    intro t ht
    have hU'' : y₀ t ∈ (U' : Set (Xo.XF c)) := by rw [hU']; exact hf.2.1 ⟨t, rfl⟩
    exact ⟨⟨hy₀ ht, hU''⟩, hW₁ ht⟩
  have hsm : SmoothOfRelativeDimension D.dim
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  obtain ⟨V, hV, ψ, hle, hhol, hψ0, hover, hinj⟩ := GlobalTheory.T.holomorphic_chart_near_point c.F σ (Xo.XF c) (pullback.snd _ _) D.dim hsm y₀ _ hf.1 hy₀'
    (hdom _ hcU)
  obtain ⟨g, hg⟩ := hsec V hV (hle.trans inf_le_right)
  have hVV₀ : V ≤ V₀ := hle.trans (inf_le_left.trans inf_le_left)
  let res : Γ(Xo.XF c, V₀) →+* Γ(Xo.XF c, V) := ((Xo.XF c).presheaf.map (homOfLE hVV₀).op).hom
  have hpt : ∀ z, spMap ((ψ z).comp res) ≫ hV₀.fromSpec = spMap (ψ z) ≫ hV.fromSpec := by
    intro z
    have h1 : spMap res ≫ hV₀.fromSpec = hV.fromSpec := by
      have := hV₀.map_fromSpec hV (homOfLE hVV₀).op
      simpa [spMap, res] using this
    rw [← h1, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ψ' : (Fin D.dim → ℂ) → (Γ(Xo.XF c, V₀) →+* ℂ) := fun z => (ψ z).comp res
  have hin : ∀ z, Set.range (spMap (ψ z) ≫ hV.fromSpec) ⊆ U := by
    intro z
    rw [← hU']
    rintro _ ⟨t, rfl⟩
    exact (hle.trans (inf_le_left.trans inf_le_right)) (Cmp.comp_mem hV (ψ z) t)
  have val' : ∀ z ∈ ball (0 : Fin D.dim → ℂ) 1, IsFramed U τ σ _ (vat (ψ' z)) (wat (ψ' z)) ∧
      φ ℂ _ (vat (ψ' z)) (wat (ψ' z)) = ψ z g := by
    intro z hz
    obtain ⟨f1, f2⟩ := val (ψ' z) (by rw [hpt]; exact hover z hz) (by rw [hpt]; exact hin z)
    refine ⟨f1, ?_⟩
    have key : ∀ r, ValAt (Z.ξ₀ ≫ Y.j) ((spMap (ψ' z) ≫ hV₀.fromSpec) ≫ Y.j) (α / κ') r → r = ψ z g := fun r hr => by
      rw [hpt] at hr
      exact hg _ r hr
    exact key _ f2
  have hol : DifferentiableOn ℂ (fun z => Φ (spMap (ψ' z) ≫ hV₀.fromSpec) (vat (ψ' z)) (wat (ψ' z))) (ball 0 1) :=
    hΦ.hol Γ(Xo.XF c, V₀) hV₀.fromSpec vR wR D.dim (ball 0 1) ψ' (fun z => vat (ψ' z)) (fun z => wat (ψ' z)) isOpen_ball
      (fun r => hhol.2 (res r))
      (fun z hz => ⟨⟨(val' z hz).1.1, Set.subset_univ _, (val' z hz).1.2.2⟩, fun _ => rfl, fun _ => rfl⟩)
  have m0 : (0 : Fin D.dim → ℂ) ∈ ball (0 : Fin D.dim → ℂ) 1 := mem_ball_self one_pos
  have hcont : ContinuousAt (fun z => ψ z g - κ₀ * Φ (spMap (ψ' z) ≫ hV₀.fromSpec) (vat (ψ' z)) (wat (ψ' z))) 0 :=
    ((hhol.2 g).continuousOn.continuousAt (isOpen_ball.mem_nhds m0)).sub
      (continuousAt_const.mul (hol.continuousOn.continuousAt (isOpen_ball.mem_nhds m0)))
  have hpV : genPt Z.ξ₀ ∈ V := by
    have hs : genPt Z.ξ₀ ⤳ centre y₀ := (Z.closure _).1 hcU
    refine hs.mem_open V.isOpen ?_
    rw [← hψ0]
    exact Cmp.comp_mem hV (ψ 0) _
  have hz : ψ 0 g - κ₀ * Φ (spMap (ψ' 0) ≫ hV₀.fromSpec) (vat (ψ' 0)) (wat (ψ' 0)) = 0 := by
    by_contra hne
    obtain ⟨ε, hε, hb'⟩ := Metric.eventually_nhds_iff_ball.1 (hcont.eventually_ne hne)
    obtain ⟨z, h1, h2, h3⟩ := Cmp.exists_near hV hhol hinj W hpV hgW hε
    refine hb' z h2 ?_
    obtain ⟨v', w', hf', he'⟩ := hW (spMap (ψ' z) ≫ hV₀.fromSpec) (by rw [hpt]; exact hover z h1)
      (by rw [hpt]; exact h3) (by rw [hpt]; exact hin z)
    rw [← (val' z h1).2, chg_eq hΦ hφ hf' (val' z h1).1 he', sub_self]
  have fin : ∀ (y' : Sp ℂ ⟶ Xo.XF c) (_ : y' = y₀) (v' : Vecs y' D.p) (w' : Vecs y' D.q), IsFramed U τ σ y' v' w' →
      φ ℂ y' v' w' = κ₀ * Φ y' v' w' → φ ℂ y₀ v₀ w₀ = κ₀ * Φ y₀ v₀ w₀ := by
    rintro y' rfl v' w' h1 h2
    exact chg_eq hΦ hφ h1 hf h2
  exact fin _ ((hpt 0).trans hψ0) _ _ (val' 0 m0).1 ((val' 0 m0).2.trans (sub_eq_zero.1 hz))

end GlobalTheory.CompanionTheory.Ar.Flat.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem flat_eq_const_mul_unitAn : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (φ : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → Z.IsGeom → IsUnitAn τ σ Φ → IsLineFn U τ φ → FlatOnModel Z τ φ → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ y v w, IsFramed U τ σ y v w → φ ℂ y v w = κ * Φ y v w := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ φ hO hpq hτ hσ hgeo hΦ hL hF
  obtain ⟨h1, h2, -, ⟨p₀, hp₀⟩⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hO hτ
  obtain ⟨N₁, hN₁, b₁, sb₁, fb₁⟩ := h1 p₀ hp₀
  obtain ⟨N₂, hN₂, b₂, sb₂, fb₂⟩ := h2 p₀ hp₀
  have l₁ := (fb₁ p₀ hp₀ hN₁).1
  have l₂ := (fb₂ p₀ hp₀ hN₂).1
  obtain ⟨f, κ₀, W, hκ₀, hgW, hgen, hpts⟩ :=
    GlobalTheory.T.eigen_frames_analytic hR hG E H D l Xo c O β Y U Z τ σ Φ b₁ b₂ hO hpq hτ hσ hgeo hΦ l₁ sb₁ l₂ sb₂
  obtain ⟨φ₀, hL₀, hrep⟩ := GlobalTheory.T.wedge_eigen_line_generator E H D l Xo c O β Y U Z τ _ _ hO hτ hgen
  have hF₀ := FlatOnModel.of_gen hL₀ hgen hrep
  obtain ⟨x, hx, hsc⟩ := GlobalTheory.T.frame_functions_flat_agree E H D l Xo c O β Y U Z τ φ₀ φ hO hτ hgeo hL₀ hF₀ hL hF
  have hext := Cmp.ext_frames Z hO hτ hΦ hL₀ hrep
    (fun c₁ lc sc => by
      obtain ⟨d, hd⟩ := Cmp.iMulti_eq_smul lc (sb₁.trans sc.symm)
      exact ⟨f * d, by rw [hd, smul_smul]⟩)
    (fun c₂ lc sc => Cmp.iMulti_eq_smul lc (sb₂.trans sc.symm))
    W hgW (κ₀ := κ₀)
    (fun y h₁ h₂ h₃ => by
      obtain ⟨v, w, hf, hv, hval⟩ := hpts y h₁ h₂ h₃
      have := hrep ℂ σ y v w b₁ b₂ f 1 hf rfl (one_smul _ _).symm hv.1 hv.2
      rw [div_one] at this
      exact ⟨v, w, hf, Cmp.valAt_unique Z.gen this hval⟩)
  refine ⟨σ x * κ₀, mul_ne_zero ((map_ne_zero σ).2 hx) hκ₀, fun y v w hf => ?_⟩
  rw [hsc ℂ σ y v w hf, hext y v w hf, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat
