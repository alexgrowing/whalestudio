import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet

theorem finite_ringHom (k : Type) [CommRing k] [Module.Finite ℤ k] : Finite (k →+* ℂ) := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ k).FG)
  have hroot : ∀ a : k, ∃ S : Set ℂ, S.Finite ∧ ∀ σ : k →+* ℂ, σ a ∈ S := by
    intro a
    obtain ⟨P, hm, hP⟩ := (Algebra.IsIntegral.isIntegral a : IsIntegral ℤ a)
    refine ⟨{z | (P.map (Int.castRingHom ℂ)).IsRoot z}, ?_, fun σ => ?_⟩
    · exact Polynomial.finite_setOf_isRoot (hm.map _).ne_zero
    · have h : Polynomial.eval₂ (σ.comp (algebraMap ℤ k)) (σ a) P = 0 := by
        rw [← Polynomial.hom_eval₂, hP, map_zero]
      rw [Subsingleton.elim (σ.comp (algebraMap ℤ k)) (Int.castRingHom ℂ)] at h
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using h
  choose S hS hm using hroot
  have : ∀ i : s, Finite (S i) := fun i => (hS i).to_subtype
  refine Finite.of_injective (fun (σ : k →+* ℂ) (i : s) => (⟨σ i, hm i σ⟩ : S i)) fun σ₁ σ₂ h => ?_
  have hs' : ∀ i ∈ s, σ₁ i = σ₂ i := fun i hi => congrArg Subtype.val (congrFun h ⟨i, hi⟩)
  have hspan : ∀ x ∈ Submodule.span ℤ (s : Set k), σ₁ x = σ₂ x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => exact hs' x h
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx => simp [map_zsmul, hx]
  exact RingHom.ext fun x => hspan x (hs ▸ Submodule.mem_top)

variable {k : Type} [CommRing k] {X : Scheme.{0}}

theorem emb_apply (p : X ⟶ Sp k) {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} (y : CxPts t τ) (a : k) :
    emb p y a = ev t τ ⊤ (algX p ⊤ a) y :=
  (ev_algX (y := unsheet p y) mem_ptsIn_top a).symm

theorem range_sheet (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact emb_sheet t τ z
  · intro h
    have h' : emb p y = σ := h
    subst h'
    exact ⟨unsheet p y, rfl⟩

theorem isOpen_emb_eq [Finite (k →+* ℂ)] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    IsOpen {y : CxPts t τ | emb p y = σ} := by
  have hc (a : k) : Continuous fun y : CxPts t τ => emb p y a := by
    simp only [emb_apply]
    exact (Points.continuous_valR_top _).comp continuous_subtype_val
  have e : {y : CxPts t τ | emb p y = σ} =
      ⋂ σ' : {s : k →+* ℂ // s ≠ σ}, ⋃ a : k, {y | emb p y a ≠ σ'.1 a} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · rintro rfl σ'
      by_contra h
      push Not at h
      exact σ'.2 (RingHom.ext fun a => (h a).symm)
    · intro h
      by_contra he
      obtain ⟨a, ha⟩ := h ⟨_, he⟩
      exact ha rfl
  rw [e]
  exact isOpen_iInter_of_finite fun σ' => isOpen_iUnion fun a => isOpen_ne_fun (hc a) continuous_const

theorem isOpenEmbedding_and_range : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ), Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) ∧ Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  intro k _ _ X p t τ σ
  have := finite_ringHom k
  have hr := range_sheet p t τ σ
  refine ⟨⟨IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    IsEmbedding.subtypeVal, ?_⟩, hr⟩
  rw [hr]
  exact isOpen_emb_eq p t τ σ

end GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet
