import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory

theorem fibre_exists_finite_generizing {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z)
    (hq : Continuous q) (z : Z) :
    ∃ T : Set Y, T.Finite ∧ (∀ e ∈ T, q e = z) ∧ ∀ w, q w = z → ∃ e ∈ T, e ⤳ w := by
  have hfin : (irreducibleComponents (q ⁻¹' {z})).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have key : ∀ C : irreducibleComponents (q ⁻¹' {z}),
      ∃ e : Y, q e = z ∧ ∀ c ∈ C.1, e ⤳ (c : Y) := by
    intro C
    have hC : IsIrreducible C.1 := C.2.1
    have hCi : IsIrreducible (((↑) : q ⁻¹' {z} → Y) '' C.1) :=
      hC.image _ continuous_subtype_val.continuousOn
    have hgen := hCi.isGenericPoint_genericPoint_closure
    refine ⟨hCi.genericPoint, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hC.nonempty
      have hcz : q c = z := c.2
      have h1 : hCi.genericPoint ⤳ (c : Y) := hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
      have h2 : hCi.genericPoint ∈ closure (((↑) : q ⁻¹' {z} → Y) '' C.1) := hgen.mem
      have h3 : closure (((↑) : q ⁻¹' {z} → Y) '' C.1) ⊆ q ⁻¹' closure {z} :=
        (closure_mono (by rintro _ ⟨d, -, rfl⟩; exact d.2)).trans (hq.closure_preimage_subset _)
      have h4 : z ⤳ q hCi.genericPoint := specializes_iff_mem_closure.2 (h3 h2)
      have h5 : q hCi.genericPoint ⤳ z := by
        have := h1.map hq
        rwa [hcz] at this
      exact (h5.antisymm h4).eq
    · intro c hc
      exact hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
  choose f hf using key
  haveI : Finite (irreducibleComponents (q ⁻¹' {z})) := hfin.to_subtype
  refine ⟨Set.range f, Set.finite_range f, ?_, ?_⟩
  · rintro _ ⟨C, rfl⟩
    exact (hf C).1
  · intro w hw
    let w' : q ⁻¹' {z} := ⟨w, hw⟩
    refine ⟨f ⟨_, irreducibleComponent_mem_irreducibleComponents w'⟩, ⟨_, rfl⟩, ?_⟩
    exact (hf _).2 w' mem_irreducibleComponent

theorem fibre_const_of_specializes_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  intro Y Z _ _ _ _ _ q hq z hpc P hP a b ha hb hPa
  obtain ⟨T, hTf, hTz, hTs⟩ := fibre_exists_finite_generizing q hq z
  by_contra hPb
  have closed : ∀ R : Y → Prop, IsClosed (⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y)) :=
    fun R => (hTf.subset (fun _ h => h.1)).isClosed_biUnion (fun _ _ => isClosed_closure)
  have mem : ∀ (R : Y → Prop) (e w : Y), e ∈ T → R e → e ⤳ w →
      w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) := by
    intro R e w he hR hs
    exact Set.mem_biUnion ⟨he, hR⟩ (specializes_iff_mem_closure.1 hs)
  have mem' : ∀ (R : Y → Prop) (w : Y), w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) →
      ∃ e, e ∈ T ∧ R e ∧ e ⤳ w := by
    intro R w hw
    obtain ⟨e, ⟨he, hR⟩, hc⟩ := Set.mem_iUnion₂.1 hw
    exact ⟨e, he, hR, specializes_iff_mem_closure.2 hc⟩
  obtain ⟨w, hwS, hwt, hwt'⟩ := isPreconnected_closed_iff.1 hpc _ _ (closed P) (closed (fun e => ¬ P e))
    (by
      intro w hw
      obtain ⟨e, he, hs⟩ := hTs w hw
      by_cases h : P e
      · exact Or.inl (mem P e w he h hs)
      · exact Or.inr (mem _ e w he h hs))
    (by
      obtain ⟨e, he, hs⟩ := hTs a ha
      exact ⟨a, ha, mem P e a he ((hP e a (hTz e he) ha hs).2 hPa) hs⟩)
    (by
      obtain ⟨e, he, hs⟩ := hTs b hb
      exact ⟨b, hb, mem (fun e => ¬ P e) e b he (fun h => hPb ((hP e b (hTz e he) hb hs).1 h)) hs⟩)
  have hwz : q w = z := hwS
  obtain ⟨e₁, h₁, hP₁, hs₁⟩ := mem' P w hwt
  obtain ⟨e₂, h₂, hP₂, hs₂⟩ := mem' _ w hwt'
  exact hP₂ ((hP e₂ w (hTz e₂ h₂) hwz hs₂).2 ((hP e₁ w (hTz e₁ h₁) hwz hs₁).1 hP₁))

end GlobalTheory
