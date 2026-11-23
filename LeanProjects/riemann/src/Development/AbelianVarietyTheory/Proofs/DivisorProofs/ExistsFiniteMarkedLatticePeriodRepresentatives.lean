import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

variable {O : Type} [Ring O] {bar : O → O}

theorem isPeriod_comp_symm {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D D' : PLat O bar}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) :
    IsPeriod D' ρ (P.comp w.symm.toAddEquiv.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hr : (P.comp w.symm.toAddEquiv.toAddMonoidHom).range = P.range := by
    ext z
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [h1]
  · exact h2.comp w.symm.injective
  · rw [hr]; exact h3
  · have : Set.range (P.comp w.symm.toAddEquiv.toAddMonoidHom) = Set.range P := by
      rw [← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    rw [this]; exact h4
  · simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hEF, ← hw]
    simp

def unifClass {Λ : Type} {g : ℕ} (F : Fam ℂ O Λ g) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (y : Sp ℂ ⟶ F.X) : Set ((D' : PLat O bar) × (Λ → D'.La)) :=
  {p | C p.1 p.2 ∧ ∃ P e, UnifAt F (RingHom.id ℂ) ρ N p.1 p.2 P y e}

theorem unifClass_eq {Λ : Type} {g : ℕ} (F : Fam ℂ O Λ g) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) {N : ℕ}
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (hN : 0 < N) {y : Sp ℂ ⟶ F.X} {D₀ : PLat O bar}
    {t₀ : Λ → D₀.La} {P₀ : D₀.La →+ (Fin g → ℂ)} {e₀ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)}
    (hU : UnifAt F (RingHom.id ℂ) ρ N D₀ t₀ P₀ y e₀) :
    unifClass F ρ N C y = {p | C p.1 p.2 ∧ ∃ w, IsMarkedIsom N D₀ p.1 t₀ p.2 w} := by
  ext ⟨D', t'⟩
  constructor
  · rintro ⟨hC, P, e, hU'⟩
    obtain ⟨w, -, hw, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D₀ D' t₀ t' P₀ P y e₀ e hN hU hU'
    exact ⟨hC, w, hw⟩
  · rintro ⟨hC, w, hw⟩
    exact ⟨hC, P₀.comp w.symm.toAddEquiv.toAddMonoidHom, _,
      GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D₀ D' t₀ t' P₀ (P₀.comp w.symm.toAddEquiv.toAddMonoidHom) y e₀ w
        (LinearEquiv.refl ℂ _) hN hU hw (fun x => by simp) (isPeriod_comp_symm hU.2.1 w hw.1)⟩

theorem exists_finite_representatives : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → ∃ (n : ℕ) (Di : Fin n → PLat O bar) (t : ∀ i, Λ → (Di i).La), (∀ i, C (Di i) (t i) ∧ ∃ P, IsPeriod (Di i) ρ P) ∧ (∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w) ∧ ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hF
  have : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
  have hlft : LocallyOfFiniteType F.s := inferInstance

  have hloc : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ F.X)), IsOpen B →
      (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → ∀ b₀ ∈ B,
      ∀ᶠ b in nhds b₀, unifClass F ρ N C (y b) = unifClass F ρ N C (y b₀) := by
    intro B y hB hy hhol b₀ hb₀
    obtain ⟨D₀, t₀, P₀, e₀, -, hU₀⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨B', P, e, hB', hb₀', -, -, -, -, hU⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N D₀ t₀ d B y b₀ P₀ e₀ hN heta hlft hB hb₀ hy hhol hU₀
    filter_upwards [hB'.mem_nhds hb₀'] with b hb
    rw [unifClass_eq F ρ C hN (hU b hb), unifClass_eq F ρ C hN hU₀]
  have hfin := GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families
    GlobalTheory.SubfieldChart.exists_holomorphic_chart ℂ (RingHom.id ℂ) F.X F.s d _ (unifClass F ρ N C) hsm hqc hloc
  set T := unifClass F ρ N C '' {x | x ≫ F.s = spMap (RingHom.id ℂ)} with hT
  haveI := hfin.fintype
  let E := (Fintype.equivFin T).symm
  have hch : ∀ c : T, ∃ (p : (D' : PLat O bar) × (Λ → D'.La)) (y : Sp ℂ ⟶ F.X), unifClass F ρ N C y = c.1 ∧ p ∈ unifClass F ρ N C y := by
    rintro ⟨c, y, hy, rfl⟩
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    exact ⟨⟨D', t'⟩, y, rfl, hC, P, e, hU⟩
  choose p y hcls hmem using hch
  refine ⟨Fintype.card T, fun i => (p (E i)).1, fun i => (p (E i)).2, fun i => ?_, ?_, ?_⟩
  · obtain ⟨hC, P, e, hU⟩ := hmem (E i)
    exact ⟨hC, P, hU.2.1⟩
  · rintro D' t' hC ⟨P, hP⟩
    obtain ⟨y', e', hU'⟩ := hF.occ D' t' P hC hP
    let c : T := ⟨unifClass F ρ N C y', y', hU'.1, rfl⟩
    refine ⟨E.symm c, ?_⟩
    have h1 : p (E (E.symm c)) ∈ unifClass F ρ N C y' := by
      have := hmem (E (E.symm c))
      have h2 : ((E (E.symm c)) : Set ((D' : PLat O bar) × (Λ → D'.La))) = unifClass F ρ N C y' :=
        congrArg Subtype.val (E.apply_symm_apply c)
      rwa [hcls, h2] at this
    rw [unifClass_eq F ρ C hN hU'] at h1
    exact h1.2
  · intro i j w hw
    apply E.injective
    apply Subtype.ext
    obtain ⟨hCi, Pi, ei, hUi⟩ := hmem (E i)
    obtain ⟨hCj, Pj, ej, hUj⟩ := hmem (E j)
    have hj' : p (E j) ∈ unifClass F ρ N C (y (E i)) := by
      rw [unifClass_eq F ρ C hN hUi]
      exact ⟨hCj, w, hw⟩
    obtain ⟨-, Pj', ej', hUj'⟩ := hj'
    rw [← hcls, ← hcls, unifClass_eq F ρ C hN hUj', unifClass_eq F ρ C hN hUj]

end GlobalTheory.PELU
