import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticeSpread

theorem exists_common {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] [QuasiSober α]
    {O : Type*} [CommRing O] [IsDomain O] (f : α → PrimeSpectrum O) (hf : Continuous f) (C : Set α)
    (hC : IsClosed C) (h : ∀ x ∈ C, ∃ o : O, o ≠ 0 ∧ o ∈ (f x).asIdeal) :
    ∃ n : O, n ≠ 0 ∧ ∀ x ∈ C, n ∈ (f x).asIdeal := by
  classical
  obtain ⟨S, hS, hcl, hirr, hU⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  have key : ∀ Z ∈ S, ∃ o : O, o ≠ 0 ∧ ∀ x ∈ Z, o ∈ (f x).asIdeal := by
    intro Z hZ
    obtain ⟨η, hη⟩ := QuasiSober.sober (hirr Z hZ) (hcl Z hZ)
    obtain ⟨o, ho, hm⟩ := h η (by rw [hU]; exact ⟨Z, hZ, hη.mem⟩)
    refine ⟨o, ho, fun x hx => ?_⟩
    exact (PrimeSpectrum.le_iff_specializes _ _).2 ((hη.specializes hx).map hf) hm
  choose! o ho hm using key
  refine ⟨∏ Z ∈ hS.toFinset, o Z, Finset.prod_ne_zero_iff.2 fun Z hZ => ho Z (hS.mem_toFinset.1 hZ), ?_⟩
  intro x hx
  rw [hU] at hx
  obtain ⟨Z, hZ, hxZ⟩ := hx
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem o (hS.mem_toFinset.2 hZ)
  rw [hc]
  exact Ideal.mul_mem_right _ _ (hm Z hZ x hxZ)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isGenAt_iff (L : Lat ξ Ω) (b : Fin 1 → Ω) (q : Cpt ξ) (hb : L.IsFrameAt b q) (t : Ω) :
    L.IsGenAt q t ↔ unitAt ξ q (t / b 0) := by
  have h0 : b 0 ≠ 0 := hb.1.ne_zero 0
  have hr : Set.range b = {b 0} := Set.range_unique
  have hL : L q = Submodule.span (regAt ξ q) {b 0} := by rw [hb.2, hr]
  constructor
  · rintro ⟨ht, e⟩
    have e' := hL.symm.trans e
    refine ⟨div_ne_zero ht h0, ?_, ?_⟩
    · have : t ∈ Submodule.span (regAt ξ q) {b 0} := e' ▸ Submodule.mem_span_singleton_self t
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      have hr' : (r : Ω) * b 0 = t := hr
      rw [← hr', mul_div_cancel_right₀ _ h0]
      exact r.2
    · have : b 0 ∈ Submodule.span (regAt ξ q) {t} := e' ▸ Submodule.mem_span_singleton_self (b 0)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      have hr' : (r : Ω) * t = b 0 := hr
      rw [inv_div, ← hr', mul_div_cancel_right₀ _ ht]
      exact r.2
  · rintro ⟨h1, h2, h3⟩
    have ht : t ≠ 0 := fun h => h1 (by rw [h, zero_div])
    refine ⟨ht, hL.trans (le_antisymm ?_ ?_)⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨_, h3⟩, ?_⟩
      show (t / b 0)⁻¹ * t = b 0
      field_simp
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨_, h2⟩, ?_⟩
      show (t / b 0) * b 0 = t
      field_simp

end PositivityTheory.Xgn.LineLatticeSpread

open PositivityTheory.Xgn.LineLatticeSpread in
theorem PositivityTheory.Xgn.line_lattice_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t := by
  intro X Ω _ ξ O _ _ _ s _ _ _ hs _ hc L T n₀ t hn₀ hT hL hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := {}
  have hu : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal := fun p o =>
    (ConstReg.regular_const X Ω ξ O s hs p o).2 hc
  let W : Set X := ⋃ (U : X.Opens) (_ : ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q t), (U : Set X)
  have hW : IsOpen W := isOpen_iUnion fun U => isOpen_iUnion fun _ => U.isOpen
  obtain ⟨n, hn, H⟩ := exists_common (O := O) (fun x : X => s x) s.continuous (closure {genPt ξ} ∩ Wᶜ)
    (isClosed_closure.inter hW.isClosed_compl) (by
      rintro x ⟨hx, hxW⟩
      by_contra hcon
      let p : Cpt ξ := ⟨x, specializes_iff_mem_closure.2 hx⟩
      have hp : p ∈ genFibre O ξ := fun o ho => (hu p o).2 fun hm => hcon ⟨o, ho, hm⟩
      obtain ⟨U, hpU, b, -, hb⟩ := hL p (hT p (hp n₀ hn₀))
      have h1 := (isGenAt_iff L b p (hb p (hT p (hp n₀ hn₀)) hpU) t).1 (hgen p hp)
      obtain ⟨U₁, hp₁, H₁⟩ := (regAt_unitAt_open X Ω ξ p _).2 h1
      obtain ⟨U₂, hp₂, H₂⟩ := (regAt_unitAt_open X Ω ξ p _).2 (hp n₀ hn₀)
      refine hxW (Set.mem_iUnion₂.2 ⟨U ⊓ U₁ ⊓ U₂, ?_, ⟨⟨hpU, hp₁⟩, hp₂⟩⟩)
      rintro q ⟨⟨hq, hq₁⟩, hq₂⟩
      exact (isGenAt_iff L b q (hb q (hT q (H₂ q hq₂)) hq) t).2 (H₁ q hq₁))
  refine ⟨n, hn, fun p hp => ?_⟩
  have hpW : p.1 ∈ W := by
    by_contra hW'
    exact (hu p n).1 hp (H p.1 ⟨specializes_iff_mem_closure.1 p.2, hW'⟩)
  obtain ⟨U, hU, hpU⟩ := Set.mem_iUnion₂.1 hpW
  exact hU p hpU
