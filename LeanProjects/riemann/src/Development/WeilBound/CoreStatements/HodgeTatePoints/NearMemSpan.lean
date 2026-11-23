import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm

noncomputable section

namespace PositivityTheory.HtPt.Mc

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem near_all {ι : Type} [Finite ι] (p : Cpt ξ) (P : ι → Cpt ξ → Prop)
    (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  choose U hU hP using h
  refine ⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, ?_, fun q hq i => hP i q ?_⟩
  · exact Set.mem_iInter.2 hU
  · exact Set.mem_iInter.1 hq i

theorem near_mem_span {n : ℕ} (g : Fin n → E) (p : Cpt ξ) (e : E)
    (h : e ∈ Submodule.span (regAt ξ p) (Set.range g)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range g) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  obtain ⟨U, hU, H⟩ := near_all p (fun i q => (c i : Ω) ∈ regAt ξ q)
    fun i => (regAt_unitAt_open X Ω ξ p (c i)).1 (c i).2
  exact ⟨U, hU, fun q hq => (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨c i, H q hq i⟩, hc⟩⟩

theorem near_span_eq {n m : ℕ} (g : Fin n → E) (b : Fin m → E) (p : Cpt ξ)
    (h : Submodule.span (regAt ξ p) (Set.range g) = Submodule.span (regAt ξ p) (Set.range b)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      Submodule.span (regAt ξ q) (Set.range g) = Submodule.span (regAt ξ q) (Set.range b) := by
  obtain ⟨U, hU, H⟩ := near_all p (fun i q => g i ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun i => near_mem_span b p _ (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨U', hU', H'⟩ := near_all p (fun i q => b i ∈ Submodule.span (regAt ξ q) (Set.range g))
    fun i => near_mem_span g p _ (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq => le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 (H q hq.1))
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 (H' q hq.2))

end

theorem frame_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsCohOn T → p ∈ T → L.IsFrameAt b p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q := by
  intro X Ω _ ξ E _ _ L T r b p hL hp hb
  obtain ⟨U, hU, n, g, hg⟩ := hL p hp
  obtain ⟨U', hU', H⟩ := near_span_eq g b p ((hg p hp hU).symm.trans hb.2)
  exact ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq hqU => ⟨hb.1, (hg q hq hqU.1).trans (H q hqU.2)⟩⟩

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem map_of_span {L : Lat ξ E} (φ : E →ₗ[Ω] E') {q : Cpt ξ} {ι : Type} {b : ι → E}
    (h : L q = Submodule.span (regAt ξ q) (Set.range b)) :
    L.map φ q = Submodule.span (regAt ξ q) (Set.range (φ ∘ b)) := by
  unfold Lat.map
  rw [h, Submodule.map_span, Set.range_comp]
  rfl

theorem coh_map {L : Lat ξ E} {T : Set (Cpt ξ)} (φ : E →ₗ[Ω] E') (h : L.IsCohOn T) : (L.map φ).IsCohOn T := by
  intro p hp
  obtain ⟨U, hU, n, g, hg⟩ := h p hp
  exact ⟨U, hU, n, φ ∘ g, fun q hq hqU => map_of_span φ (hg q hq hqU)⟩

theorem vb_of_coh {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {V : Submodule Ω E} (h : L.IsCohOn T)
    (hb : ∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) : L.IsVBOn T r V := by
  intro p hp
  obtain ⟨b, hV, hb⟩ := hb p hp
  obtain ⟨U, hU, H⟩ := frame_spread X Ω ξ E L T r b p h hp hb
  exact ⟨U, hU, b, hV, H⟩

theorem span_smul_fam {ι : Type} (b : ι → E) {a : Ω} (ha : a ≠ 0) :
    Submodule.span Ω (Set.range fun i => a • b i) = Submodule.span Ω (Set.range b) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have : b i = a⁻¹ • a • b i := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem li_smul_fam {ι : Type} {b : ι → E} (hb : LinearIndependent Ω b) {a : Ω} (ha : a ≠ 0) :
    LinearIndependent Ω fun i => a • b i :=
  hb.units_smul fun _ => Units.mk0 a ha

end

theorem coh_ops : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) := by
  intro X Ω _ ξ E _ _ E' _ _ L L' T
  refine ⟨fun r V h => Lat.IsCohOn.of_isVBOn h, fun φ h => coh_map φ h, fun h h' p hp => ?_,
    fun r V a ha h p hp => ?_, fun r V h hb => vb_of_coh h hb⟩
  · obtain ⟨U, hU, n, g, hg⟩ := h p hp
    obtain ⟨U', hU', n', g', hg'⟩ := h' p hp
    refine ⟨U ⊓ U', ⟨hU, hU'⟩, n + n', Fin.append g g', fun q hq hqU => ?_⟩
    have e : Set.range (Fin.append g g') = Set.range g ∪ Set.range g' := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        induction i using Fin.addCases with
        | left i => exact Or.inl ⟨i, by simp⟩
        | right i => exact Or.inr ⟨i, by simp⟩
      · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact ⟨Fin.castAdd n' i, by simp⟩
        · exact ⟨Fin.natAdd n i, by simp⟩
    rw [e, Submodule.span_union, ← hg q hq hqU.1, ← hg' q hq hqU.2]
  · obtain ⟨U, hU, b, hV, hb⟩ := h p hp
    refine ⟨U, hU, fun i => a • b i, (span_smul_fam b ha).trans hV, fun q hq hqU =>
      ⟨li_smul_fam (hb q hq hqU).1 ha, ?_⟩⟩
    exact map_of_span _ (hb q hq hqU).2

end PositivityTheory.HtPt.Mc
