import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfIntegralAtFibreGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isOpen_setOf_intAt {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) :
    IsOpen {x : X | IntAt L α s x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨j, W, hW, hx, hWa, hint⟩
  exact ⟨W, fun x' hx' => ⟨j, W, hW, hx', hWa, hint⟩, W.isOpen, hx⟩

theorem exists_fibre_generic {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyIrreducible f] (y : S) :
    ∃ ζ : X, f ζ = y ∧ ∀ z, f z = y → ζ ⤳ z := by
  refine ⟨f.fiberι y (genericPoint (f.fiber y)), ?_, ?_⟩
  · have : f.fiberι y (genericPoint (f.fiber y)) ∈ Set.range (f.fiberι y) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range (f.fiberι y) := by rw [Scheme.Hom.range_fiberι]; exact hz
    exact (genericPoint_specializes z').map (f.fiberι y).continuous

theorem exists_specializes_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R)
    (y : M.S) : ∃ y₀, y ⤳ y₀ ∧ M.π y₀ = closedPoint R := by
  haveI := M.proper
  have hc : IsClosed (M.π '' closure {y}) := M.π.isClosedMap _ isClosed_closure
  have hm : M.π y ∈ M.π '' closure {y} := ⟨y, subset_closure rfl, rfl⟩
  obtain ⟨y₀, hy₀, e⟩ := (IsLocalRing.specializes_closedPoint (M.π y)).mem_closed hc hm
  exact ⟨y₀, specializes_iff_mem_closure.2 hy₀, e⟩

end GlobalTheory.Mum

theorem GlobalTheory.Mum.intAt_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), (∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x) → ∀ x : G.left, IntAt L α s x := by
  intro R _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hcl x
  haveI := hsm; haveI := hgi
  by_contra hx
  obtain ⟨ζ, hζ, hζg⟩ := exists_fibre_generic G.hom (G.hom x)
  obtain ⟨y₀, hy₀, hy₀c⟩ := exists_specializes_closedPoint M (G.hom ζ)
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, G.hom g₀ = y₀ := by
    obtain ⟨g₀, hg₀, -⟩ := exists_fibre_generic G.hom y₀
    exact ⟨g₀, hg₀⟩
  obtain ⟨g, hg, hgg₀⟩ := Flat.generalizingMap G.hom (show G.hom ζ ⤳ G.hom g₀ from hg₀ ▸ hy₀)
  have hζg' : ζ ⤳ g := hζg g (hgg₀.trans hζ)
  have hnζ : ¬ IntAt L α s ζ := fun h => hx (GlobalTheory.T.integral_of_integral_at_fibre_generic_point R M G hsm hqc hgi L hL Y α t hpb k s x ζ hζ hζg h)
  have hclosed : IsClosed {z : G.left | ¬ IntAt L α s z} := (isOpen_setOf_intAt L α s).isClosed_compl
  have : ¬ IntAt L α s g₀ := (hζg'.trans hg).mem_closed hclosed hnζ
  exact this (hcl g₀ (by rw [hg₀, hy₀c]))
