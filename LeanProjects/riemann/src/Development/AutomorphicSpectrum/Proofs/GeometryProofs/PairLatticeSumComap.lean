import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeSum

section LinearAlgebra

open Submodule

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]

theorem range_append {α : Type} {r s : ℕ} (f : Fin r → α) (g : Fin s → α) :
    Set.range (Fin.append f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · exact Or.inl ⟨i, by simp⟩
    · exact Or.inr ⟨i, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd s i, by simp⟩
    · exact ⟨Fin.natAdd r i, by simp⟩

theorem linearIndependent_append {r s : ℕ} {f : Fin r → V} {g : Fin s → V} (hf : LinearIndependent Ω f)
    (hg : LinearIndependent Ω g) (hd : Disjoint (span Ω (Set.range f)) (span Ω (Set.range g))) :
    LinearIndependent Ω (Fin.append f g) := by
  have h := hf.sum_type hg hd
  have e : Fin.append f g = Sum.elim f g ∘ finSumFinEquiv.symm := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
  rw [e]
  exact h.comp _ finSumFinEquiv.symm.injective

theorem span_lift_eq_top {W : Submodule Ω V} {n : ℕ} {v : Fin n → V} {c : Fin n → W} (hc : ∀ k, (c k : V) = v k)
    (hv : span Ω (Set.range v) = W) : span Ω (Set.range c) = ⊤ := by
  apply Submodule.map_injective_of_injective W.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  have e : (W.subtype ∘ c) = v := funext hc
  rw [show (⇑W.subtype ∘ c) = v from e, hv]

theorem comap_sup_span (A : Subring Ω) {W : Submodule Ω V} {r s : ℕ} {f : Fin r → V} {g : Fin s → V}
    {c : Fin (r + s) → W} (hc : ∀ k, (c k : V) = Fin.append f g k) :
    (span A (Set.range f) ⊔ span A (Set.range g)).comap (W.subtype.restrictScalars A) =
      span A (Set.range c) := by
  have hinj : Function.Injective (W.subtype.restrictScalars A) := W.injective_subtype
  have e : span A (Set.range f) ⊔ span A (Set.range g) =
      (span A (Set.range c)).map (W.subtype.restrictScalars A) := by
    rw [Submodule.map_span, ← Set.range_comp, ← Submodule.span_union, ← range_append]
    congr 2
    exact funext fun k => (hc k).symm
  rw [e, Submodule.comap_map_eq_of_injective hinj]

end LinearAlgebra

end GlobalTheory.CompanionTheory.Ar.HodgeSum

theorem GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H), a ≠ b → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB (labelRk D a + labelRk D b) ⊤ := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 a b hab
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
    GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐 hβ
  have hdisj : Disjoint (𝔐.Vgen a) (𝔐.Vgen b) := hind.pairwiseDisjoint hab
  intro p _
  obtain ⟨Ua, hpa, f, hfs, hff⟩ := 𝔐.vb a p (Set.mem_univ _)
  obtain ⟨Ub, hpb, g, hgs, hgf⟩ := 𝔐.vb b p (Set.mem_univ _)
  have hfs' : Submodule.span Ω (Set.range f) = 𝔐.Vgen a := hfs
  have hgs' : Submodule.span Ω (Set.range g) = 𝔐.Vgen b := hgs
  have hspan : Submodule.span Ω (Set.range (Fin.append f g)) = 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
    rw [HodgeSum.range_append, Submodule.span_union, hfs', hgs']
  have hmem : ∀ k, Fin.append f g k ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := fun k => by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self k)
  have hli : LinearIndependent Ω (Fin.append f g) :=
    HodgeSum.linearIndependent_append (hff p (Set.mem_univ _) hpa).1 (hgf p (Set.mem_univ _) hpb).1
      (by rw [hfs', hgs']; exact hdisj)
  refine ⟨Ua ⊓ Ub, ⟨hpa, hpb⟩, fun k => ⟨Fin.append f g k, hmem k⟩,
    HodgeSum.span_lift_eq_top (fun _ => rfl) hspan, fun q _ hq => ⟨?_, ?_⟩⟩
  · exact LinearIndependent.of_comp (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype hli
  · have h1 : 𝔐.V a q = Submodule.span (regAt 𝔐.ξ q) (Set.range f) := (hff q (Set.mem_univ _) hq.1).2
    have h2 : 𝔐.V b q = Submodule.span (regAt 𝔐.ξ q) (Set.range g) := (hgf q (Set.mem_univ _) hq.2).2
    show (𝔐.V a q ⊔ 𝔐.V b q).comap ((𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype.restrictScalars (regAt 𝔐.ξ q)) = _
    rw [h1, h2]
    exact HodgeSum.comap_sup_span (regAt 𝔐.ξ q) fun _ => rfl
