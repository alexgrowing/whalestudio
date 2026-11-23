import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsoOfSamePeriodMatrixLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {g m : ℕ} {Y : Scheme.{0}}

theorem isDerivAt0_comp_linMap {e : (Fin m → ℂ) → (Sp ℂ ⟶ Y)} (hol : IsHolTo Set.univ e)
    (D : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ)) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e (D w) v) : IsDerivAt0 (fun z => e (D z)) w v := by
  obtain ⟨h1, h2⟩ := hv
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  refine ⟨by show _ = e (D 0); rw [map_zero]; exact h1, fun U h f => ?_⟩
  rw [h2 U h f]
  obtain ⟨hopen, hdiff⟩ := hol U f
  have h0mem : (0 : Fin m → ℂ) ∈ {b | b ∈ Set.univ ∧ ⊤ ≤ (TopologicalSpace.Opens.map (e b).base).obj U} := by
    refine ⟨Set.mem_univ _, ?_⟩
    have hv' : (TopologicalSpace.Opens.map v.base).obj U = ⊤ := top_le_iff.1 h
    rw [← h1]
    simp [hv']
  have hφ : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (D 0) := by
    rw [map_zero]
    exact (hdiff 0 h0mem).differentiableAt (hopen.mem_nhds h0mem)
  have hDd : DifferentiableAt ℂ (⇑(LinearMap.toContinuousLinearMap D)) 0 :=
    (LinearMap.toContinuousLinearMap D).differentiableAt
  have hc := fderiv_comp (0 : Fin g → ℂ) hφ hDd
  have hDf : fderiv ℂ (⇑D) 0 = LinearMap.toContinuousLinearMap D :=
    (LinearMap.toContinuousLinearMap D).fderiv
  rw [show (fun z => valAt' (e (D z)) U f) = (fun z => valAt' (e z) U f) ∘ ⇑D from rfl, hc, hDf]
  simp

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem ex_zero_left (u : HolUnif A L g) : (u.ex 0).left = η[A].left := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  have h1 : u.ex 0 = 1 := by simpa using h
  rw [h1, Hom.one_def]
  simp

theorem isHolTo_ex (u : HolUnif A L g) : IsHolTo Set.univ (fun z => (u.ex z).left) := by
  intro U f
  simpa using u.hol U f

theorem isDerivAt0_of_isDiff (u : HolUnif A L g) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (ht : IsTangent v)
    (hd : u.IsDiff w v) : IsDerivAt0 (fun z => (u.ex z).left) w v.left := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif.IsDiff at hd
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent at ht
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  exact ⟨ht.trans (ex_zero_left u).symm, hd⟩

theorem isDerivAt0_of_fibre {Q : Out.PolAV (Sp ℂ)} {X : Scheme.{0}} (ψ : Q.A.left ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (u : HolUnif Q.A Q.L Q.g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)) (hF : ∀ z, (u.ex (F z)).left ≫ ψ = e z)
    {w : Fin g → ℂ} {t : epsR ℂ ⟶ Q.A} (ht : IsTangent t) (hd : u.IsDiff (F w) t) :
    IsDerivAt0 e w (t.left ≫ ψ) := by
  have h4 := isDerivAt0_comp_linMap (isHolTo_ex u) F (isDerivAt0_of_isDiff u ht hd)
  have he : e = fun z => (u.ex (F z)).left ≫ ψ := funext fun z => (hF z).symm
  subst he
  obtain ⟨h41, h42⟩ := h4
  have hval : ∀ (y : Sp ℂ ⟶ Q.A.left) (U : X.Opens) (f : ↑(X.presheaf.obj (Opposite.op U))),
      valAt' (y ≫ ψ) U f = valAt' y (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
    intro y U f
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
    by_cases hy : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj (ψ ⁻¹ᵁ U)
    · rw [dif_pos hy, dif_pos (show ⊤ ≤ (y ≫ ψ) ⁻¹ᵁ U from hy)]
      simp only [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    · rw [dif_neg hy, dif_neg (show ¬ ⊤ ≤ (y ≫ ψ) ⁻¹ᵁ U from hy)]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  refine ⟨by rw [← Category.assoc, h41], fun U h f => ?_⟩
  have h' : ⊤ ≤ (TopologicalSpace.Opens.map t.left.base).obj (ψ ⁻¹ᵁ U) := h
  simp only [hval]
  rw [← h42 (ψ ⁻¹ᵁ U) h' ((ψ.app U).hom f)]
  simp only [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]

theorem isDiff_map {Q : Out.PolAV (Sp ℂ)} (u u' : HolUnif Q.A Q.L Q.g) (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)) (hG : ∀ z, u.ex (G z) = u'.ex z) {w : Fin Q.g → ℂ}
    {t : epsR ℂ ⟶ Q.A} (ht : IsTangent t) (hd : u'.IsDiff w t) : u.IsDiff (G w) t := by
  have h4 := isDerivAt0_of_isDiff u' ht hd
  simp_rw [← hG] at h4
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.VerticalDeriv.exists_isDerivAt0 (isHolTo_ex u) (G w)
  have h1 := isDerivAt0_comp_linMap (isHolTo_ex u) G hv₀
  have heq := GlobalTheory.VerticalDeriv.isDerivAt0_unique h1 h4
  rw [heq] at hv₀
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif.IsDiff
  exact hv₀.2

end GlobalTheory.CompanionTheory.Ar.Flat.PerGram

namespace GlobalTheory.CompanionTheory.Ar.Flat

open PerGram in

theorem hodgeGram_iff_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → Hm.IsHermitian → (∀ x y, (hermForm Hm (P x) (P y)).im = (FU.Di i).EF x y) → ∀ (y : Sp ℂ ⟶ Xo.X), y = FU.u i P → ∀ (m : ℕ) (v : Fin m → (epsAt y ⟶ Xo.univ.t.G)) (W : Fin m → Fin g → ℂ) (Γ : Matrix (Fin m) (Fin m) ℂ), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (W a) (v a).left) → (IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L y v Γ ↔ ∀ a b, Γ a b = Real.pi * hermForm Hm (W a) (W b)) := by
  intro E _ _ _ H D l Xo σ g ty FU i P Hm hP _ hIm y hy m v W Γ hd
  subst hy
  have key : ∀ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback Q.A Xo.univ.t.G (FU.u i P) ψ → LBIso Q.L (Xo.univ.t.PP.L.pull ψ) →
      ∃ (u : HolUnif Q.A Q.L Q.g) (H₂ : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ)
        (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ)), u.IsAH H₂ χ ∧ (∀ t, IsTangent t → ∃! w, u.IsDiff w t) ∧
        (∀ w, ∃! t, IsTangent t ∧ u.IsDiff w t) ∧ (∀ z w, hermForm H₂ (F z) (F w) = hermForm Hm z w) ∧
        ∀ a, ∃ t : epsR ℂ ⟶ Q.A, IsTangent t ∧ u.IsDiff (F (W a)) t ∧ t.left ≫ ψ = (v a).left := by
    intro Q ψ hQ hQL
    obtain ⟨u, H₂, χ, F, hAH, d₁, d₂, -, hF, -, hE⟩ :=
      GlobalTheory.familyUnif_fibre_theta GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1.weil E H D l Xo σ g ty FU i P hP
        Q ψ hQ hQL
    refine ⟨u, H₂, χ, F, hAH, d₁, d₂, fun z w => ?_, fun a => ?_⟩
    · refine GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im H₂ F.toLinearMap Hm LinearMap.id hP.2.2.2.1 ?_ z w
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (hE a b).trans (hIm a b).symm
    · obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F (W a))
      exact ⟨t, h₁, h₂, GlobalTheory.VerticalDeriv.isDerivAt0_unique
        (isDerivAt0_of_fibre ψ u F.toLinearMap hF h₁ h₂) (hd a)⟩
  unfold IsHodgeGram
  constructor
  · rintro ⟨Q, ψ, v', u', Hm', χ', W', hQ, hQL, hAH, hv, hΓ⟩ a b
    obtain ⟨u, H₂, χ, F, hAH₂, d₁, d₂, hH, ht⟩ := key Q ψ hQ hQL.symm
    obtain ⟨G, hG, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo Q.A Q.isAb Q.L Q.g Q.g u d₁ d₂ u'.ex u'.ex_add
      (isHolTo_ex u')
    have hW : ∀ c, G (W' c) = F (W c) := fun c => by
      obtain ⟨t, h₁, h₂, h₃⟩ := ht c
      have e : v' c = t := Over.OverMorphism.ext
        (hQ.1.hom_ext ((hv c).1.trans h₃.symm) (by rw [Over.w, Over.w]))
      have h₄ : u'.IsDiff (W' c) t := e ▸ (hv c).2
      exact (d₁ t h₁).unique (isDiff_map u u' d₂ G hG h₁ h₄) h₂
    rw [hΓ, ← GlobalTheory.UnifCompare.hermForm_eq Q.isLB u' u hAH hAH₂ G hG, hW, hW, hH]
  · intro hΓ
    obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper
      Xo.univ.ample Xo.univ.ktriv ℂ (FU.u i P)
    obtain ⟨u, H₂, χ, F, hAH₂, -, -, hH, ht⟩ := key Q ψ hQ hQL
    choose t h₁ h₂ h₃ using ht
    exact ⟨Q, ψ, t, u, H₂, χ, fun a => F (W a), hQ, hQL.symm, hAH₂, fun a => ⟨h₃ a, h₂ a⟩,
      fun a b => by rw [hΓ, hH]⟩

end GlobalTheory.CompanionTheory.Ar.Flat
