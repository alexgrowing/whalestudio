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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem top_le_iff_centre (y : Sp ℂ ⟶ X) (U : X.Opens) : ⊤ ≤ y ⁻¹ᵁ U ↔ centre y ∈ U :=
  ⟨fun h => h trivial, fun h => (Scheme.preimage_eq_top_of_closedPoint_mem y h).ge⟩

theorem val_germ (y : Sp ℂ ⟶ X) (N : X.Opens) (h : centre y ∈ N) (v : Γ(X, N)) :
    (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ N (centre y) h v) = valAt' y N v := by
  have e := congrArg (fun q => q.hom v) (germ_stalkClosedPointTo_eq y N h)
  rw [valAt'_of _ _ ((top_le_iff_centre y N).2 h)]
  simp only [valAt]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

def genV (ξ : Sp Ω ⟶ X) (N : X.Opens) (h : genPt ξ ∈ N) : Γ(X, N) →+* Ω :=
  ((X.presheaf.germ N (genPt ξ) h) ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (N : X.Opens) {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) (h : genPt ξ ∈ N) (v : Γ(X, N)) :
    genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q hN v) = genV ξ N h v := by
  have e := X.presheaf.germ_stalkSpecializes hN hq
  simp only [genMap, genV]
  rw [← e]
  rfl

theorem genPt_mem {N : X.Opens} {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) : genPt ξ ∈ N :=
  hq.mem_open N.isOpen hN

theorem ValAt.of_section {y : Sp ℂ ⟶ X} {N : X.Opens} (hy : centre y ∈ N) (h : genPt ξ ⤳ centre y) {v : Γ(X, N)}
    {a : Ω} (ha : genMap ξ ⟨centre y, h⟩ (X.presheaf.germ N (centre y) hy v) = a) :
    ValAt ξ y a (valAt' y N v) :=
  ⟨h, _, ha, val_germ y N hy v⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem ValAt.unique (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h₁, s, hs, rfl⟩ := h
  obtain ⟨h₂, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h₁⟩ (hs.trans hs'.symm)]

theorem ValAt.mul {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b r') : ValAt ξ z (a * b) (r * r') := by
  obtain ⟨h₁, s, hs, rfl⟩ := h
  obtain ⟨h₂, s', hs', rfl⟩ := h'
  exact ⟨h₁, s * s', by rw [map_mul, hs]; congr 1, map_mul _ _ _⟩

theorem ValAt.one {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) :=
  ⟨h, 1, map_one _, map_one _⟩

theorem ValAt.exists_of_mem {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem ValAt.exists_ne_zero (hξ : IsCptGen ξ) {z : Sp ℂ ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : unitAt ξ ⟨centre z, h⟩ a) : ∃ r : ℂ, r ≠ 0 ∧ ValAt ξ z a r := by
  obtain ⟨r, hr⟩ := ValAt.exists_of_mem h ha.2.1
  obtain ⟨r', hr'⟩ := ValAt.exists_of_mem h ha.2.2
  have e := ValAt.unique hξ (ValAt.mul hr hr') (by rw [mul_inv_cancel₀ ha.1]; exact ValAt.one h)
  exact ⟨r, left_ne_zero_of_mul_eq_one e, hr⟩

theorem exists_section {q : X} (h : genPt ξ ⤳ q) {a : Ω} (ha : a ∈ regAt ξ ⟨q, h⟩) (M : X.Opens) (hM : q ∈ M) :
    ∃ (N : X.Opens) (hq : q ∈ N) (v : Γ(X, N)), N ≤ M ∧ genMap ξ ⟨q, h⟩ (X.presheaf.germ N q hq v) = a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨N, hq, v, hv⟩ := TopCat.Presheaf.germ_exist X.presheaf s
  refine ⟨N ⊓ M, ⟨hq, hM⟩, X.presheaf.map (homOfLE inf_le_left).op v, inf_le_right, ?_⟩
  have e : X.presheaf.germ (N ⊓ M) q ⟨hq, hM⟩ (X.presheaf.map (homOfLE inf_le_left).op v) =
      X.presheaf.germ N q hq v := TopCat.Presheaf.germ_res_apply _ _ _ _ _
  exact congrArg (genMap ξ ⟨q, h⟩) (e.trans hv)

theorem exists_unit_section (hξ : IsCptGen ξ) {q : X} (h : genPt ξ ⤳ q) {a : Ω} (ha : unitAt ξ ⟨q, h⟩ a)
    (M : X.Opens) (hM : q ∈ M) :
    ∃ (N : X.Opens) (hq : q ∈ N) (v : Γ(X, N)), N ≤ M ∧ IsUnit v ∧
      genMap ξ ⟨q, h⟩ (X.presheaf.germ N q hq v) = a := by
  obtain ⟨N₁, h₁, v, l₁, e₁⟩ := exists_section h ha.2.1 M hM
  obtain ⟨N₂, h₂, w, l₂, e₂⟩ := exists_section h ha.2.2 M hM
  let i₁ : N₁ ⊓ N₂ ⟶ N₁ := homOfLE inf_le_left
  let i₂ : N₁ ⊓ N₂ ⟶ N₂ := homOfLE inf_le_right
  have hq : q ∈ N₁ ⊓ N₂ := ⟨h₁, h₂⟩
  have g₁ : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₁.op v) = X.presheaf.germ N₁ q h₁ v :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have g₂ : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₂.op w) = X.presheaf.germ N₂ q h₂ w :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have one : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₁.op v * X.presheaf.map i₂.op w) =
      X.presheaf.germ (N₁ ⊓ N₂) q hq 1 := by
    apply hξ.inj ⟨q, h⟩
    rw [map_mul, g₁, g₂, map_mul, e₁, e₂, mul_inv_cancel₀ ha.1, map_one, map_one]
  obtain ⟨N₃, h₃, j₁, j₂, e₃⟩ := TopCat.Presheaf.germ_eq X.presheaf q hq hq _ _ one
  have hj : j₁ = j₂ := Subsingleton.elim _ _
  subst hj
  refine ⟨N₃, h₃, X.presheaf.map (j₁ ≫ i₁).op v, (leOfHom (j₁ ≫ i₁)).trans l₁, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one (X.presheaf.map (j₁ ≫ i₂).op w) ?_
    rw [map_mul, map_one] at e₃
    simpa [op_comp, Functor.map_comp] using e₃
  · rw [TopCat.Presheaf.germ_res_apply, e₁]

theorem unitAt_div_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {a b : Ω} (ha : Λ.IsGenAt p a) (hb : Λ.IsGenAt p b) :
    unitAt ξ p (b / a) := by
  have h₁ : b ∈ Submodule.span (regAt ξ p) {a} := by
    rw [← ha.2, hb.2]; exact Submodule.mem_span_singleton_self b
  have h₂ : a ∈ Submodule.span (regAt ξ p) {b} := by
    rw [← hb.2, ha.2]; exact Submodule.mem_span_singleton_self a
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h₁
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.1 h₂
  have hc' : (c : Ω) * a = b := hc
  have he' : (e : Ω) * b = a := he
  refine ⟨div_ne_zero hb.1 ha.1, ?_, ?_⟩
  · rw [← hc', mul_div_cancel_right₀ _ ha.1]; exact c.2
  · rw [inv_div, ← he', mul_div_cancel_right₀ _ hb.1]; exact e.2

theorem isGenAt_mul_of_unitAt {Λ : Lat ξ Ω} {p : Cpt ξ} {a u : Ω} (ha : Λ.IsGenAt p a) (hu : unitAt ξ p u) :
    Λ.IsGenAt p (u * a) := by
  refine ⟨mul_ne_zero hu.1 ha.1, ?_⟩
  rw [ha.2]
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, hu.2.2⟩, ?_⟩
    show u⁻¹ * (u * a) = a
    rw [← _root_.mul_assoc, inv_mul_cancel₀ hu.1, _root_.one_mul]
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, hu.2.1⟩, rfl⟩

structure IsChart (s : X ⟶ Sp ℂ) {d : ℕ} (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) : Prop where
  isOpen : IsOpen B
  hol : IsHolTo B Y
  isOver : ∀ b ∈ B, Y b ≫ s = 𝟙 _
  factor : ∀ (m : ℕ) (B' : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B' → IsHolTo B' y →
    (∀ b ∈ B', y b ≫ s = 𝟙 _) → ∀ b₀ ∈ B', ∀ b₁ ∈ B, y b₀ = Y b₁ →
    ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B' ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧
      κ b₀ = b₁ ∧ ∀ b ∈ ball b₀ ε, κ b ∈ B ∧ y b = Y (κ b)

theorem IsChart.mono {s : X ⟶ Sp ℂ} {d : ℕ} {B B₂ : Set (Fin d → ℂ)} {Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)}
    (h : IsChart s B Y) (o : IsOpen B₂) (l : B₂ ⊆ B) : IsChart s B₂ Y where
  isOpen := o
  hol := fun U f => by
    have e : {b ∈ B₂ | ⊤ ≤ Y b ⁻¹ᵁ U} = B₂ ∩ {b ∈ B | ⊤ ≤ Y b ⁻¹ᵁ U} := by
      ext b; exact ⟨fun hb => ⟨hb.1, l hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
    rw [e]
    exact ⟨o.inter (h.hol U f).1, (h.hol U f).2.mono Set.inter_subset_right⟩
  isOver := fun b hb => h.isOver b (l hb)
  factor := fun m B' y oB hy ov b₀ h₀ b₁ h₁ e => by
    obtain ⟨ε, κ, ε0, sub, dκ, k₀, hκ⟩ := h.factor m B' y oB hy ov b₀ h₀ b₁ (l h₁) e
    have c : ContinuousAt κ b₀ := (dκ.differentiableAt (ball_mem_nhds _ ε0)).continuousAt
    have m₂ : κ ⁻¹' B₂ ∈ 𝓝 b₀ := c.preimage_mem_nhds (o.mem_nhds (k₀ ▸ h₁))
    obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem m₂ (ball_mem_nhds b₀ ε0))
    have sb : ball b₀ δ ⊆ ball b₀ ε := fun b hb => (hδ hb).2
    exact ⟨δ, κ, δ0, sb.trans sub, dκ.mono sb, k₀, fun b hb => ⟨(hδ hb).1, (hκ b (sb hb)).2⟩⟩

structure HChart (s : X ⟶ Sp ℂ) (ξ : Sp Ω ⟶ X) (W U : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T : Ω) {d : ℕ}
    (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) : Prop where
  chart : IsChart s B Y
  inU : ∀ b ∈ B, centre (Y b) ∈ U
  cpt : ∀ b ∈ B, genPt ξ ⤳ centre (Y b)
  dense : ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W
  hol : DifferentiableOn ℂ H B
  ne : ∀ b ∈ B, H b ≠ 0
  rel : ∀ b ∈ B, centre (Y b) ∈ W → ∀ r : ℂ, ValAt ξ (Y b) T r → F (Y b) = H b * r

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
