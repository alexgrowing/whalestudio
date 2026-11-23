import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AnChart
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace PositivityTheory.Xgn.HolomorphicChart

theorem der_zero {K A : Type} [Field K] [CommRing A] [Algebra K A] {d : ℕ} (z : Fin d → A)
    (hsp : Submodule.span A (Set.range fun i => KaehlerDifferential.D K A (z i)) = ⊤)
    (ψ : A →+* ℂ) (δ : A →+ ℂ) (hmul : ∀ a b, δ (a * b) = ψ a * δ b + ψ b * δ a)
    (hK : ∀ k, δ (algebraMap K A k) = 0) (hz : ∀ i, δ (z i) = 0) (a : A) : δ a = 0 := by
  let : Algebra A ℂ := ψ.toAlgebra
  let : Algebra K ℂ := (ψ.comp (algebraMap K A)).toAlgebra
  have : IsScalarTower K A ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let L : A →ₗ[K] ℂ :=
    { toFun := δ
      map_add' := δ.map_add
      map_smul' := fun k a => by
        rw [Algebra.smul_def, hmul, hK, mul_zero, add_zero]; rfl }
  let D : Derivation K A ℂ := Derivation.mk' L fun a b => hmul a b
  have h0 : D.liftKaehlerDifferential = 0 := by
    apply LinearMap.ext_on_range hsp
    intro i
    rw [Derivation.liftKaehlerDifferential_comp_D]
    exact hz i
  have := D.liftKaehlerDifferential_comp_D a
  rw [h0] at this
  exact this.symm

theorem der_zero_loc {K A A' : Type} [Field K] [CommRing A] [Algebra K A] [CommRing A'] [Algebra K A'] [Algebra A A']
    [IsScalarTower K A A'] (g : A) [IsLocalization.Away g A'] {d : ℕ} (z : Fin d → A)
    (hsp : Submodule.span A (Set.range fun i => KaehlerDifferential.D K A (z i)) = ⊤)
    (ψ : A' →+* ℂ) (δ : A' →+ ℂ) (hmul : ∀ a b, δ (a * b) = ψ a * δ b + ψ b * δ a)
    (hK : ∀ k, δ (algebraMap K A' k) = 0) (hz : ∀ i, δ (algebraMap A A' (z i)) = 0) (a : A') : δ a = 0 := by
  have h := der_zero z hsp (ψ.comp (algebraMap A A')) (δ.comp (algebraMap A A').toAddMonoidHom)
    (fun a b => by simpa using hmul (algebraMap A A' a) (algebraMap A A' b))
    (fun k => by simpa [← IsScalarTower.algebraMap_apply] using hK k) hz
  have h' : ∀ b, δ (algebraMap A A' b) = 0 := h
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g) a
  have hu : ψ (algebraMap A A' s) ≠ 0 := ((IsLocalization.map_units A' s).map ψ).ne_zero
  have := hmul a (algebraMap A A' s)
  rw [hs, h', h', mul_zero, zero_add] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hu

theorem stdSmooth {K A A' : Type} [Field K] [CommRing A] [Algebra K A] [CommRing A'] [Algebra K A'] [Algebra A A']
    [IsScalarTower K A A'] (g : A) [IsLocalization.Away g A'] [Algebra.Smooth K A] [Nontrivial A] {d : ℕ} (z : Fin d → A)
    (hli : LinearIndependent A (fun i => KaehlerDifferential.D K A (z i)))
    (hsp : Submodule.span A (Set.range fun i => KaehlerDifferential.D K A (z i)) = ⊤) :
    Algebra.IsStandardSmoothOfRelativeDimension d K A' := by
  let b : Module.Basis (Fin d) A Ω[A⁄K] := Module.Basis.mk hli hsp.ge
  have : Algebra.IsStandardSmooth K A := Algebra.IsStandardSmooth.of_basis_kaehlerDifferential b (by
    rintro _ ⟨i, rfl⟩; exact ⟨z i, by simp [b]⟩)
  have : Algebra.IsStandardSmoothOfRelativeDimension d K A :=
    (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth d).2 (by simpa using rank_eq_card_basis b)
  have := Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := A') g
  simpa using Algebra.IsStandardSmoothOfRelativeDimension.trans d 0 K A A'

theorem chart_alt_bis {K A : Type} [Field K] [CommRing A] [Algebra K A] (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K A]
    (σ : K →+* ℂ) (ψ₀ : A →+* ℂ) (h₀ : ψ₀.comp (algebraMap K A) = σ) (z : Fin d → A)
    (H : ∀ δ : A →+ ℂ, (∀ a b, δ (a * b) = ψ₀ a * δ b + ψ₀ b * δ a) → (∀ k, δ (algebraMap K A k) = 0) →
      (∀ i, δ (z i) = 0) → ∀ a, δ a = 0) :
    ∃ (O : Set (Fin d → ℂ)) (Φ : (Fin d → ℂ) → (A →+* ℂ)), IsOpen O ∧ (fun i => ψ₀ (z i)) ∈ O ∧
      (∀ u ∈ O, (Φ u).comp (algebraMap K A) = σ ∧ ∀ i, Φ u (z i) = u i) ∧
      (∀ a, DifferentiableOn ℂ (fun u => Φ u a) O) ∧
      ∀ {J : Type} (l : Filter J) (y : J → (A →+* ℂ)), (∀ a, Tendsto (fun t => y t a) l (𝓝 (ψ₀ a))) →
        (∀ᶠ t in l, (y t).comp (algebraMap K A) = σ) → ∀ᶠ t in l, Φ (fun i => y t (z i)) = y t := by
  obtain ⟨N, g, f, B, ε, Ψ, ε0, oB, a₁, a₂, a₃⟩ := anChart_alg d σ ψ₀ h₀
  obtain ⟨mB, e₀⟩ := a₃ ψ₀ h₀ (fun j => by simpa using ε0)
  set b₀ : Fin d → ℂ := fun i => ψ₀ (f i) with hb₀
  have nB : B ∈ 𝓝 b₀ := oB.mem_nhds mB
  have dA : ∀ a, DifferentiableAt ℂ (fun b => Ψ b a) b₀ := fun a => (a₂ a).differentiableAt nB
  let G : (Fin d → ℂ) → (Fin d → ℂ) := fun b i => Ψ b (z i)
  have cd : ContDiffAt ℂ 1 G b₀ := contDiffAt_pi.2 fun i =>
    GlobalTheory.SCV.contDiffAt_of_differentiableOn (a₂ (z i)) nB 1
  let F := fderiv ℂ G b₀
  have hF : HasFDerivAt G F b₀ := (cd.differentiableAt one_ne_zero).hasFDerivAt
  have inj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun v hv => by
    let δ : A →+ ℂ :=
      { toFun := fun a => fderiv ℂ (fun b => Ψ b a) b₀ v
        map_zero' := by simp
        map_add' := fun a a' => by
          simp only [map_add]
          rw [fderiv_fun_add (dA a) (dA a')]; rfl }
    have hδ := H δ (fun a a' => by
        show fderiv ℂ (fun b => Ψ b (a * a')) b₀ v = _
        simp only [map_mul]
        rw [fderiv_fun_mul (dA a) (dA a'), e₀]; rfl)
      (fun k => by
        show fderiv ℂ (fun b => Ψ b (algebraMap K A k)) b₀ v = 0
        have : (fun b => Ψ b (algebraMap K A k)) =ᶠ[𝓝 b₀] fun _ => σ k := by
          filter_upwards [nB] with b hb using congrArg (fun φ : K →+* ℂ => φ k) (a₁ b hb).1
        rw [this.fderiv_eq]; simp)
      (fun i => by
        show fderiv ℂ (fun b => Ψ b (z i)) b₀ v = 0
        have := congrFun hv i
        rw [show F = _ from fderiv_pi (fun i => dA (z i))] at this
        exact this)
    funext i
    have h1 : fderiv ℂ (fun b => Ψ b (f i)) b₀ v = 0 := hδ (f i)
    have : (fun b => Ψ b (f i)) =ᶠ[𝓝 b₀] fun b => b i := by
      filter_upwards [nB] with b hb using (a₁ b hb).2 i
    rw [this.fderiv_eq, (hasFDerivAt_apply (𝕜 := ℂ) i b₀).fderiv] at h1
    exact h1
  let F' : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ) := (LinearEquiv.ofInjectiveEndo F.toLinearMap inj).toContinuousLinearEquiv
  let T := cd.toOpenPartialHomeomorph G (f' := F') hF one_ne_zero
  have mS : b₀ ∈ T.source := cd.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero
  have mT : G b₀ ∈ T.target := T.map_source mS
  have cI : ContDiffAt ℂ 1 T.symm (G b₀) := cd.to_localInverse (f' := F') hF one_ne_zero
  have lI : T.symm (G b₀) = b₀ := T.left_inv mS
  have hG : G b₀ = fun i => ψ₀ (z i) := by simp only [G, e₀]
  have nO : {u | u ∈ T.target ∧ ContDiffAt ℂ 1 T.symm u ∧ T.symm u ∈ B} ∈ 𝓝 (G b₀) := by
    filter_upwards [T.open_target.mem_nhds mT, cI.eventually (by simp),
      cI.continuousAt.preimage_mem_nhds (lI.symm ▸ nB)] with u h1 h2 h3 using ⟨h1, h2, h3⟩
  refine ⟨interior {u | u ∈ T.target ∧ ContDiffAt ℂ 1 T.symm u ∧ T.symm u ∈ B}, fun u => Ψ (T.symm u), isOpen_interior,
    hG ▸ mem_interior_iff_mem_nhds.2 nO, fun u hu => ?_, fun a u hu => ?_, fun l y hy hσ => ?_⟩
  · obtain ⟨h1, -, h3⟩ := interior_subset hu
    exact ⟨(a₁ _ h3).1, fun i => congrFun (T.right_inv h1) i⟩
  · obtain ⟨-, h2, h3⟩ := interior_subset hu
    exact (((a₂ a).differentiableAt (oB.mem_nhds h3)).comp u (h2.differentiableAt one_ne_zero)).differentiableWithinAt
  · have t₁ : ∀ᶠ t in l, ∀ j, ‖y t (g j) - ψ₀ (g j)‖ < ε := eventually_all.2 fun j => by
      simpa [dist_eq_norm] using Metric.tendsto_nhds.1 (hy (g j)) ε ε0
    have t₂ : ∀ᶠ t in l, (fun i => y t (f i)) ∈ T.source :=
      (tendsto_pi_nhds.2 fun i => hy (f i)) (T.open_source.mem_nhds mS)
    filter_upwards [t₁, t₂, hσ] with t h1 h2 h3
    obtain ⟨-, h4⟩ := a₃ (y t) h3 h1
    have h5 : (fun i => y t (z i)) = T (fun i => y t (f i)) := by
      show _ = G _
      simp only [G, h4]
    rw [h5, T.left_inv h2, h4]

theorem exists_perm {d : ℕ} (p : Fin d → Prop) :
    ∃ (a : ℕ) (π : Equiv.Perm (Fin d)), a ≤ d ∧ ∀ i, (π i).val < a ↔ p i := by
  classical
  have ha : Fintype.card {i // p i} ≤ d := (Fintype.card_subtype_le p).trans (by simp)
  have e : {i // p i} ≃ {i : Fin d // i.val < Fintype.card {i // p i}} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype (fun i : Fin d => i.val < _), Fin.card_filter_val_lt, min_eq_right ha])
  refine ⟨_, e.extendSubtype, ha, fun i => ⟨fun h => ?_, fun h => e.extendSubtype_mem i h⟩⟩
  by_contra h'
  exact e.extendSubtype_not_mem i h' h

theorem ring_chart {K A : Type} [Field K] [CommRing A] [Algebra K A] (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K A]
    (σ : K →+* ℂ) (ψ₀ : A →+* ℂ) (h₀ : ψ₀.comp (algebraMap K A) = σ) (z : Fin d → A)
    (H : ∀ δ : A →+ ℂ, (∀ a b, δ (a * b) = ψ₀ a * δ b + ψ₀ b * δ a) → (∀ k, δ (algebraMap K A k) = 0) →
      (∀ i, δ (z i) = 0) → ∀ a, δ a = 0) (k : ℕ) :
    ∃ (a : ℕ) (ψ : (Fin d → ℂ) → (A →+* ℂ)), a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ ψ 0 = ψ₀ ∧ Set.InjOn ψ (ball 0 1) ∧
      (∀ w ∈ ball (0 : Fin d → ℂ) 1, (ψ w).comp (algebraMap K A) = σ ∧
        ((∀ i : Fin d, i.val < k → ψ w (z i) ≠ 0) ↔ w ∈ punct d a 1)) ∧
      ∀ (m : ℕ) (U : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (A →+* ℂ)), IsOpen U →
        (∀ a, DifferentiableOn ℂ (fun b => y b a) U) → (∀ b ∈ U, (y b).comp (algebraMap K A) = σ) →
        ∀ b₀ ∈ U, y b₀ = ψ₀ → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ U ∧
          DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = ψ (κ b) := by
  obtain ⟨O, Φ, oO, mO, a₁, a₂, a₃⟩ := chart_alt_bis d σ ψ₀ h₀ z H
  set c : Fin d → ℂ := fun i => ψ₀ (z i) with hc
  have e₀ : Φ c = ψ₀ := by
    simpa using a₃ (pure ()) (fun _ => ψ₀) (fun _ => tendsto_const_nhds) (by simpa using h₀)
  obtain ⟨a, π, ha, hπ⟩ := exists_perm (fun i : Fin d => i.val < k ∧ c i = 0)
  obtain ⟨r, r0, hr⟩ : ∃ r > 0, ball c r ⊆ {u | u ∈ O ∧ ∀ i, c i ≠ 0 → u i ≠ 0} := by
    apply Metric.mem_nhds_iff.1
    refine inter_mem (oO.mem_nhds mO) (eventually_all.2 fun i => ?_)
    by_cases h : c i = 0
    · simp [h]
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne h] with u hu _ using hu
  have rC : (r : ℂ) ≠ 0 := by exact_mod_cast r0.ne'
  let L : (Fin d → ℂ) → (Fin d → ℂ) := fun w i => c i + r * w (π i)
  have dL : Differentiable ℂ L := differentiable_pi.2 fun i => by fun_prop
  have mL : ∀ w ∈ ball (0 : Fin d → ℂ) 1, L w ∈ ball c r := fun w hw => by
    rw [mem_ball, dist_pi_lt_iff r0]
    intro i
    have := (dist_pi_lt_iff one_pos).1 (mem_ball.1 hw) (π i)
    simp only [Pi.zero_apply, dist_zero_right] at this
    simp only [L, dist_self_add_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg r0.le]
    exact mul_lt_of_lt_one_right r0 this
  have zL : ∀ w ∈ ball (0 : Fin d → ℂ) 1, ∀ i, Φ (L w) (z i) = c i + r * w (π i) := fun w hw i =>
    (a₁ _ (hr (mL w hw)).1).2 i
  refine ⟨a, fun w => Φ (L w), ha, ⟨isOpen_ball, fun x => (a₂ x).comp dL.differentiableOn fun w hw => (hr (mL w hw)).1⟩,
    ?_, fun w hw w' hw' h => ?_, fun w hw => ⟨(a₁ _ (hr (mL w hw)).1).1, ?_⟩, fun m U y oU hy hσ b₀ hb₀ hy₀ => ?_⟩
  · rw [← e₀]; show Φ (L 0) = Φ c; congr 1; funext i; simp [L]
  · funext j
    obtain ⟨i, rfl⟩ := π.surjective j
    have h1 := zL w hw i
    have h2 := zL w' hw' i
    have h3 : Φ (L w) = Φ (L w') := h
    rw [h3, h2] at h1
    exact (mul_left_cancel₀ rC (add_left_cancel h1)).symm
  · refine ⟨fun h => ⟨hw, fun j hj => ?_⟩, fun h i hi => ?_⟩
    · obtain ⟨i, rfl⟩ := π.surjective j
      obtain ⟨h1, h2⟩ := (hπ i).1 hj
      have := h i h1
      rw [zL w hw, h2, zero_add] at this
      exact right_ne_zero_of_mul this
    · by_cases h' : c i = 0
      · rw [zL w hw, h', zero_add]
        exact mul_ne_zero rC (h.2 _ ((hπ i).2 ⟨hi, h'⟩))
      · rw [zL w hw]
        exact (hr (mL w hw)).2 i h'
  · let κ : (Fin m → ℂ) → (Fin d → ℂ) := fun b j => (y b (z (π.symm j)) - c (π.symm j)) / r
    have dκ : DifferentiableOn ℂ κ U := differentiableOn_pi.2 fun j => by
      simp only [κ, div_eq_mul_inv]; exact ((hy _).sub_const _).mul_const _
    have κ0 : κ b₀ = 0 := by funext j; simp [κ, hy₀, hc]
    have nU := oU.mem_nhds hb₀
    have t₁ := a₃ (𝓝 b₀) y (fun x => by
      have := ((hy x).differentiableAt nU).continuousAt
      rwa [ContinuousAt, hy₀] at this) (by filter_upwards [nU] with b hb using hσ b hb)
    have t₂ : ∀ᶠ b in 𝓝 b₀, κ b ∈ ball (0 : Fin d → ℂ) 1 :=
      (dκ.differentiableAt nU).continuousAt.preimage_mem_nhds (by rw [κ0]; exact ball_mem_nhds _ one_pos)
    obtain ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 (inter_mem nU (t₁.and t₂))
    refine ⟨ε, κ, ε0, fun b hb => (hε hb).1, dκ.mono fun b hb => (hε hb).1, κ0, fun b hb => ⟨(hε hb).2.2, ?_⟩⟩
    rw [← (hε hb).2.1]
    show _ = Φ (L (κ b))
    congr 1
    funext i
    simp only [L, κ, Equiv.symm_apply_apply]
    field_simp
    ring

noncomputable def ptHom {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (V : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V) : Γ(X, V) →+* ℂ :=
  (y.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem ptHom_spec {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ y ⁻¹ᵁ V) :
    spMap (ptHom y V h) ≫ hV.fromSpec = y := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec y hV (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  show Spec.map (y.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ hV.fromSpec = y
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem fromSpec_str {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ s = spMap (@algebraMap K Γ(X, V) _ _ (Geo.ResK.secAlgebra s V)) := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at this
  exact this.symm

theorem over_iff {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {V : X.Opens} (hV : IsAffineOpen V)
    (σ : K →+* ℂ) (ψ : Γ(X, V) →+* ℂ) :
    spMap ψ ≫ hV.fromSpec ≫ s = spMap σ ↔ ψ.comp (@algebraMap K Γ(X, V) _ _ (Geo.ResK.secAlgebra s V)) = σ := by
  rw [fromSpec_str, ← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp]
  exact ⟨fun h => congrArg CommRingCat.Hom.hom h, fun h => by rw [h]⟩

theorem centre_mem {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) :
    centre (spMap ψ ≫ hV.fromSpec) ∈ V := by
  have : centre (spMap ψ ≫ hV.fromSpec) ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
  rwa [hV.range_fromSpec] at this

theorem centre_mem_basicOpen {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) (f : Γ(X, V)) :
    centre (spMap ψ ≫ hV.fromSpec) ∈ X.basicOpen f ↔ ψ f ≠ 0 := by
  have : centre (spMap ψ ≫ hV.fromSpec) ∈ X.basicOpen f ↔ centre (spMap ψ) ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f := Iff.rfl
  rw [this, hV.fromSpec_preimage_basicOpen]
  show ψ f ∉ IsLocalRing.maximalIdeal ℂ ↔ _
  simp

theorem top_le_iff {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (V : X.Opens) : ⊤ ≤ y ⁻¹ᵁ V ↔ centre y ∈ V := by
  refine ⟨fun h => h (Set.mem_univ _), fun h p _ => ?_⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  exact h

theorem smooth_sec {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) [Smooth s] {V : X.Opens} (hV : IsAffineOpen V) :
    @Algebra.Smooth K _ Γ(X, V) _ (Geo.ResK.secAlgebra s V) := by
  have h1 : (s.appLE ⊤ V (fun _ _ => trivial)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
  exact RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv h1

theorem sec_tower {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) :
    @algebraMap K Γ(X, V) _ _ (Geo.ResK.secAlgebra s V) =
      (X.presheaf.map (homOfLE h).op).hom.comp (@algebraMap K Γ(X, U) _ _ (Geo.ResK.secAlgebra s U)) := by
  have := Scheme.Hom.appLE_map s (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op
  exact congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ φ).hom) this.symm

end PositivityTheory.Xgn.HolomorphicChart

open PositivityTheory.Xgn.HolomorphicChart in
theorem PositivityTheory.Xgn.exists_holomorphic_chart_at_point : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ) (T : Set X), SmoothOfRelativeDimension d s → Geo.ResK.HasSncCoords s d T → ∀ (x : Sp ℂ ⟶ X) (W : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ∃ (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W ∧ a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ Set.InjOn ψ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ (centre (spMap (ψ z) ≫ hV.fromSpec) ∉ T ↔ z ∈ punct d a 1)) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = spMap (ψ (κ b)) ≫ hV.fromSpec := by
  intro K _ σ X s d T hs ⟨n, Vs, hcov, hVs⟩ x W hx hW
  obtain ⟨j, hj⟩ := hcov (centre x)
  obtain ⟨z, k, -, hz, hT⟩ := hVs j
  have hU : IsAffineOpen (Vs j : X.Opens) := (Vs j).2
  obtain ⟨g, hgW, hg⟩ := hU.exists_basicOpen_le ⟨centre x, (top_le_iff x W).1 hW⟩ hj
  have hV : IsAffineOpen (X.basicOpen g) := hU.basicOpen g
  have hxV : ⊤ ≤ x ⁻¹ᵁ X.basicOpen g := (top_le_iff x _).2 hg
  let := Geo.ResK.secAlgebra s (Vs j)
  let := Geo.ResK.secAlgebra s (X.basicOpen g)
  have := hU.isLocalization_basicOpen g
  have : IsScalarTower K Γ(X, (Vs j : X.Opens)) Γ(X, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq' (sec_tower s (X.basicOpen_le g))
  have := SmoothOfRelativeDimension.smooth d s
  have := smooth_sec s hU
  have : Nontrivial Γ(X, (Vs j : X.Opens)) :=
    ((ptHom x _ hxV).comp (algebraMap Γ(X, (Vs j : X.Opens)) Γ(X, X.basicOpen g))).domain_nontrivial
  have := stdSmooth (K := K) (A' := Γ(X, X.basicOpen g)) g z hz.1 hz.2
  have h₀ := (over_iff s hV σ (ptHom x _ hxV)).1 (by rw [← Category.assoc, ptHom_spec x hV hxV, hx])
  obtain ⟨a, ψ, ha, hol, e₀, inj, a₁, a₂⟩ := ring_chart d σ (ptHom x _ hxV) h₀
    (fun i => algebraMap Γ(X, (Vs j : X.Opens)) Γ(X, X.basicOpen g) (z i))
    (fun δ h1 h2 h3 => der_zero_loc g z hz.2 _ δ h1 h2 h3) k
  refine ⟨X.basicOpen g, hV, a, ψ, hgW, ha, hol, by rw [e₀, ptHom_spec], inj,
    fun w hw => ⟨(over_iff s hV σ _).2 (a₁ w hw).1, ?_⟩, fun m B y oB hy hσ b₀ hb₀ hy₀ => ?_⟩
  · rw [← (a₁ w hw).2]
    have c₁ := centre_mem hV (ψ w)
    have c₂ : centre (spMap (ψ w) ≫ hV.fromSpec) ∈ (Vs j : X.Opens) := X.basicOpen_le g c₁
    have c₃ : ∀ i, centre (spMap (ψ w) ≫ hV.fromSpec) ∈ X.basicOpen (z i) ↔
        ψ w (algebraMap Γ(X, (Vs j : X.Opens)) Γ(X, X.basicOpen g) (z i)) ≠ 0 := fun i => by
      rw [← centre_mem_basicOpen hV, RingHom.algebraMap_toAlgebra, Scheme.basicOpen_res]
      exact ⟨fun h => ⟨c₁, h⟩, fun h => h.2⟩
    have c₄ := Set.ext_iff.1 hT (centre (spMap (ψ w) ≫ hV.fromSpec))
    constructor
    · intro h i hi
      rw [← c₃]
      by_contra h'
      exact h (c₄.2 ⟨c₂, i, hi, h'⟩).2
    · intro h h'
      obtain ⟨-, i, hi, h''⟩ := c₄.1 ⟨c₂, h'⟩
      exact h'' ((c₃ i).2 (h i hi))
  · classical
    let U := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ X.basicOpen g}
    let y' : (Fin m → ℂ) → (Γ(X, X.basicOpen g) →+* ℂ) := fun b =>
      if h : ⊤ ≤ y b ⁻¹ᵁ X.basicOpen g then ptHom (y b) _ h else ptHom x _ hxV
    have hy' : ∀ b ∈ U, spMap (y' b) ≫ hV.fromSpec = y b := fun b hb => by
      simp only [y', dif_pos hb.2, ptHom_spec]
    obtain ⟨ε, κ, ε0, b₁, b₂, b₃, b₄⟩ := a₂ m U y' (hy (X.basicOpen g) 0).1
      (fun f => (hy (X.basicOpen g) f).2.congr fun b hb => by
        simp only [y', valAt', dif_pos hb.2]; rfl)
      (fun b hb => (over_iff s hV σ _).1 (by rw [← Category.assoc, hy' b hb, hσ b hb.1]))
      b₀ ⟨hb₀, by rw [hy₀]; exact hxV⟩ (by subst hy₀; exact dif_pos hxV)
    exact ⟨ε, κ, ε0, fun b hb => (b₁ hb).1, b₂, b₃, fun b hb => ⟨(b₄ b hb).1, by rw [← (b₄ b hb).2, hy' b (b₁ hb)]⟩⟩
