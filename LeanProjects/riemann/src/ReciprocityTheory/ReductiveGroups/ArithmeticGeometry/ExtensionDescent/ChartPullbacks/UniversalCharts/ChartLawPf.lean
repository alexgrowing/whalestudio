import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

theorem jetAug_zero_injective (κ : Type) : Function.Injective (jetAug R κ 0) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h : RingHom.ker (jetAug R κ 0) = ⊥ := by
    rw [← pow_one (RingHom.ker (jetAug R κ 0))]
    exact ker_jetAug_pow (R := R) κ 0
  have : a ∈ RingHom.ker (jetAug R κ 0) := ha
  rw [h] at this
  exact this

theorem jetAug_eq_comp (κ : Type) (m : ℕ) : jetAug R κ m = (jetAug R κ 0).comp (jetZeroR R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm

theorem aug_iff {κ : Type} {d m : ℕ} (ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m) :
    (jetAug R κ m).comp ψ = jetAug R (Fin d) m ↔ ∀ j, jetZeroR R κ m (ψ (zR m j)) = 0 := by
  constructor
  · intro h j
    apply jetAug_zero_injective κ
    rw [map_zero, ← AlgHom.comp_apply, ← jetAug_eq_comp, ← AlgHom.comp_apply, h, jetAug_zR]
  · intro h
    apply jet_ext
    intro j
    rw [AlgHom.comp_apply, jetAug_eq_comp, AlgHom.comp_apply, h j, map_zero, jetAug_zR]

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem chartLawLoc : ChartLawLocSt := by
  intro R _ _ G _ _ hsm d v hv
  haveI := hsm
  obtain ⟨n, x, hx⟩ := univChartLoc G
  have htan : ∀ i, IsTan (v i) := fun i => (isTan_iff _).mpr (hv.1 i)
  let M : Fin d → Fin n → R := fun i => tcoord hx (v i) (htan i)
  let L : (Fin d → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R M
  have hL : ∀ c, L c = ∑ i, c i • M i := fun c => Fintype.linearCombination_apply R M c
  have hprod : ∀ c, ∃ h : IsTan (prodPts c v), tcoord hx _ h = L c := fun c => by
    obtain ⟨h, e⟩ := prodPts_tan hx c v htan
    exact ⟨h, e.trans (hL c).symm⟩
  have hbij : Function.Bijective L := by
    constructor
    · intro c c' hcc
      obtain ⟨h, e⟩ := hprod c
      obtain ⟨h', e'⟩ := hprod c'
      have hw : prodPts c v = prodPts c' v := tan_ext hx h h' (by rw [e, e', hcc])
      have ht : IsTangent (prodPts c v) := (isTan_iff _).mp h
      exact (hv.2 _ ht).unique ((isLieComb_iff c v _).mpr rfl) ((isLieComb_iff c' v _).mpr hw)
    · intro t
      have hw := isTan_dualLift hx t
      obtain ⟨c, hc, -⟩ := hv.2 _ ((isTan_iff _).mp hw)
      refine ⟨c, ?_⟩
      obtain ⟨h, e⟩ := hprod c
      rw [← e, ← tcoord_congr hx ((isLieComb_iff c v _).mp hc) hw h, tcoord_eq hx _ hw t rfl]
  let Le := LinearEquiv.ofBijective L hbij
  have hx' := isUnivChart_sub hx Le
  refine ⟨fun m => spMap (jetSub Le.toLinearMap m) ≫ x m, hx'.1, hx'.2.1, ?_, ?_⟩
  · intro j
    refine ⟨dualLift (Pi.single j 1), by rw [dualLift_zR, Pi.single_eq_same], fun i hij => ?_, ?_⟩
    · rw [dualLift_zR, Pi.single_eq_of_ne hij, TrivSqZeroExt.inr_zero]
    · rw [algOverHom_eq, ← Category.assoc, spMap_comp, dualLift_comp_jetSub]
      have : Le.toLinearMap (Pi.single j 1) = M j := by
        show L (Pi.single j 1) = M j
        rw [hL]
        simp [Pi.single_apply]
      rw [this]
      exact (tcoord_spec hx (v j) (htan j)).symm
  · intro κ m y hy
    have hy' : spMap (jetAug R κ m) ≫ y = 1 := by
      rw [jetAug_eq_comp, ← spMap_comp, Category.assoc]
      rw [algOverHom_eq] at hy
      rw [hy]
      exact comp_one' _
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := hx'.2.2 (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) y hy'
    refine ⟨ψ, ⟨(aug_iff ψ).mp h1, h2⟩, ?_⟩
    rintro ψ₂ ⟨h3, h4⟩
    exact hu ψ₂ ⟨(aug_iff ψ₂).mpr h3, h4⟩

theorem exists_isLieBasis [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (hsm : Smooth G.hom) :
    ∃ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v := by
  haveI := hsm
  obtain ⟨n, x, hx⟩ := univChartLoc G
  let v : Fin n → (epsR R ⟶ G) := fun i => spMap (dualLift (Pi.single i 1)) ≫ x 1
  have htan : ∀ i, IsTan (v i) := fun i => isTan_dualLift hx _
  have hM : ∀ i, tcoord hx (v i) (htan i) = Pi.single i 1 := fun i => tcoord_eq hx _ _ _ rfl
  refine ⟨n, v, fun i => (isTan_iff _).mp (htan i), fun w hw => ?_⟩
  have hw' : IsTan w := (isTan_iff _).mpr hw
  have key : ∀ c, IsLieComb c v w ↔ tcoord hx w hw' = c := by
    intro c
    obtain ⟨h, e⟩ := prodPts_tan hx c v htan
    have e2 : tcoord hx _ h = c := by
      rw [e]
      simp only [hM]
      exact sum_single c
    rw [isLieComb_iff]
    constructor
    · intro hwc
      rw [tcoord_congr hx hwc hw' h, e2]
    · intro hc
      exact tan_ext hx hw' h (hc.trans e2.symm)
  exact ⟨tcoord hx w hw', (key _).mpr rfl, fun c hc => ((key c).mp hc).symm⟩

end ReciprocityTheory.ChartRestriction.G.Chart
