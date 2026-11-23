import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem chart_of_basis [IsLocalRing R] [Smooth G.hom] {d : ℕ} {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G, IsUnivChart G d x ∧
      ∀ j, v j = spMap (dualLift (Pi.single j 1)) ≫ x 1 := by
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
  refine ⟨fun m => spMap (jetSub Le.toLinearMap m) ≫ x m, hx', fun j => Eq.symm ?_⟩
  rw [← Category.assoc, spMap_comp, dualLift_comp_jetSub]
  have : Le.toLinearMap (Pi.single j 1) = M j := by
    show L (Pi.single j 1) = M j
    rw [hL]
    simp [Pi.single_apply]
  rw [this]
  exact (tcoord_spec hx (v j) (htan j)).symm

theorem basis_of_chart {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsLieBasis (G := G) (fun i : Fin n => (spMap (dualLift (Pi.single i 1)) ≫ x 1 : epsR R ⟶ G)) := by
  let v : Fin n → (epsR R ⟶ G) := fun i => spMap (dualLift (Pi.single i 1)) ≫ x 1
  have htan : ∀ i, IsTan (v i) := fun i => isTan_dualLift hx _
  have hM : ∀ i, tcoord hx (v i) (htan i) = Pi.single i 1 := fun i => tcoord_eq hx _ _ _ rfl
  refine ⟨fun i => (isTan_iff _).mp (htan i), fun w hw => ?_⟩
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

theorem isLieBasis_iso {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G')} (hv : IsLieBasis fun i => v i ≫ e.hom) : IsLieBasis v := by
  have tan : ∀ w : epsR R ⟶ G', IsTangent (w ≫ e.hom) ↔ IsTangent w := fun w => by
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    rw [IsTangent, IsTangent, ← IsMonHom.one_hom e.hom, Over.comp_left, Over.comp_left, ← Category.assoc, cancel_mono]
  have pr : ∀ u : Fin n → (epsR R ⟶ G'), (List.ofFn u).prod ≫ e.hom = (List.ofFn fun i => u i ≫ e.hom).prod := fun u =>
    (map_list_prod (IsMonHom.monoidHom e.hom (epsR R)) _).trans (by rw [List.map_ofFn]; rfl)
  have comb : ∀ c w, IsLieComb c (fun i => v i ≫ e.hom) (w ≫ e.hom) ↔ IsLieComb c v w := fun c w => by
    constructor
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => u i ≫ e.inv, fun i => ?_, ?_⟩
      · rw [Over.comp_left, hu, Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
      · rw [← cancel_mono e.hom, pr, hw]; simp
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => u i ≫ e.hom, fun i => by rw [Over.comp_left, hu, Category.assoc]; rfl, pr u⟩
  refine ⟨fun i => (tan _).1 (hv.1 i), fun w hw => ?_⟩
  simpa only [comb] using hv.2 _ ((tan w).2 hw)

theorem isLieBasis_baseChange [IsLocalRing R] [Smooth G.hom] {R' : Type} [CommRing R'] (f : R →+* R')
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) {d : ℕ} {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {v' : Fin d → (epsR R' ⟶ G')} (hv' : ∀ j, (v' j).left ≫ φ = Geo.Tor.spMap (dualMapR f) ≫ (v j).left) :
    IsLieBasis v' := by
  let _ := f.toAlgebra
  obtain ⟨x, hx, hxv⟩ := chart_of_basis hv
  obtain ⟨x', hx', e'⟩ := tanBC_alg (R' := R') G d x hx
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G (fB R R'))
  refine isLieBasis_iso e ?_
  convert basis_of_chart hx' using 2 with j
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have s : (algebraMap R R' ∘ Pi.single j (1 : R) : Fin d → R') = Pi.single j 1 := by
    funext i; by_cases hij : i = j <;> simp [hij, Pi.single_apply]
  have := e' (Pi.single j 1)
  rw [s] at this
  rw [Over.comp_left, Category.assoc, heφ, hv', hxv]
  exact this.symm

end ReciprocityTheory.ChartRestriction.G.Chart
