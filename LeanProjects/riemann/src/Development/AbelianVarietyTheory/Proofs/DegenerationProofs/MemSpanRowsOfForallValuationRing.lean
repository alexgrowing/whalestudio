import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_vecMul_inv {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {c : Matrix J J Ω} (hc : c.det ≠ 0) (v : J → Ω) :
    v ∈ Submodule.span S (Set.range c) ↔ ∀ j, Matrix.vecMul v c⁻¹ j ∈ S := by
  have hu : IsUnit c.det := isUnit_iff_ne_zero.2 hc
  have key : ∀ a : J → S, ∑ i, a i • c i = Matrix.vecMul (fun i => (a i : Ω)) c := fun a => by
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun S (v := fun i => c i)).trans ?_
  constructor
  · rintro ⟨a, rfl⟩ j
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (a j).2
  · intro h
    refine ⟨fun j => ⟨_, h j⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul v c⁻¹) c = v
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
  {J : Type} [Fintype J] [DecidableEq J]

theorem mem_span_rows_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {c : Matrix J J Ω} (hc : c.det ≠ 0) (x : M.Z) (v : J → Ω)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) → v ∈ Submodule.span (M.O ξ) (Set.range c)) :
    v ∈ Submodule.span (M.O x) (Set.range c) :=
  (mem_span_rows_iff_vecMul_inv _ hc v).2 fun j => M.mem_O_of_forall_valuationRing hn x _ fun ξ hξ hv =>
    (mem_span_rows_iff_vecMul_inv _ hc v).1 (h ξ hξ hv) j

theorem span_rows_eq_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {b c : Matrix J J Ω} (hb : b.det ≠ 0) (hc : c.det ≠ 0) (x : M.Z)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range b) = Submodule.span (M.O ξ) (Set.range c)) :
    Submodule.span (M.O x) (Set.range b) = Submodule.span (M.O x) (Set.range c) :=
  le_antisymm
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hc x v fun ξ hξ hr =>
      (h ξ hξ hr).le (Submodule.subset_span hv))
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hb x v fun ξ hξ hr =>
      (h ξ hξ hr).ge (Submodule.subset_span hv))

end RatModel

theorem exists_lat_of_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
      [JacobsonSpace M.Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (J : Type) [Fintype J] [DecidableEq J]
      (b : M.Z → Matrix J J Ω) (D : ∀ ξ : M.Z, Submodule (M.O ξ) (J → Ω)), (∀ z, (b z).det ≠ 0) →
      (∀ z, IsClosed ({z} : Set M.Z) → ∃ W : M.Z.Opens, z ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
        Submodule.span (M.O ξ) (Set.range (b z)) = D ξ) →
      ∃ EE : M.Lat J, (∀ z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) (Set.range (b z))) ∧
        ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
          (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
          ∀ x ∈ W, EE.E x = Submodule.span (M.O x) (Set.range c) := by
  intro o Ω _ _ _ M _ _ hn J _ _ b D hb h
  have hx : ∀ x : M.Z, ∃ (z : M.Z) (W : M.Z.Opens), x ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range (b z)) = D ξ := fun x => by
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set M.Z))
      ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    obtain ⟨W, hzW, hW⟩ := h z hzc
    exact ⟨z, W, (specializes_iff_mem_closure.2 hz).mem_open W.isOpen hzW, hW⟩
  choose g U hU hg using hx
  have main : ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
      (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
      ∀ x ∈ W, Submodule.span (M.O x) (Set.range (b (g x))) = Submodule.span (M.O x) (Set.range c) :=
    fun W c hc hW x hx => M.span_rows_eq_of_forall_valuationRing hn (hb _) hc x fun ξ hξ hr =>
      (hg x ξ (hξ.mem_open (U x).isOpen (hU x)) hr).trans (hW ξ (hξ.mem_open W.isOpen hx) hr)
  refine ⟨⟨fun x => Submodule.span (M.O x) (Set.range (b (g x))), fun x => ⟨U x, b (g x), hU x, hb _,
    main _ _ (hb _) fun ξ hξ hr => (hg x ξ hξ hr).symm⟩⟩, fun z hz => ?_, main⟩
  obtain ⟨W, hzW, hW⟩ := h z hz
  exact main W _ (hb z) (fun ξ hξ hr => (hW ξ hξ hr).symm) z hzW

end GlobalTheory.ZH
