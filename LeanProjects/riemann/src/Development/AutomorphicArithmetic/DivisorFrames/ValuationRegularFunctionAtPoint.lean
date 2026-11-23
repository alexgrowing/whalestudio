import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointClosureExtension
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

theorem UpperTheory.valuation_regular_function_at_point :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), spMap e.O.subtype ≫ yt = z ≫ V.j → ∀ g : V.X.functionField, RegAt (yt (IsLocalRing.closedPoint e.O)) g → RegAt (below (z ≫ V.j)) g ∧ e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1 ∧ (e.w (TrueGeo.valAt (z ≫ V.j) g) = 1 ↔ UnitAt (yt (IsLocalRing.closedPoint e.O)) g) := by
  intro F _ _ Y V v e z yt hy g hg
  obtain ⟨W₀, hW₀, s, hs⟩ := hg.exists_fnOf
  have ht : ⊤ ≤ yt ⁻¹ᵁ W₀ := GlobalTheory.HtGen.IntPt.top_le_of_closedPoint yt hW₀
  have hb : below (z ≫ V.j) ∈ W₀ := by
    change (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ W₀
    rw [← hy]
    exact ht trivial
  have ht' : ⊤ ≤ (z ≫ V.j) ⁻¹ᵁ W₀ := fun p _ => by
    change (z ≫ V.j) p ∈ W₀
    rw [← hy]
    exact ht (x := spMap e.O.subtype p) trivial
  have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (z ≫ V.j) yt
    (hy.trans (Category.comp_id _).symm) (U := W₀) (W := W₀) le_rfl ht' ht s
  have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE W₀ W₀ le_rfl).hom s = s := by
    have : (𝟙 V.X : V.X ⟶ V.X).appLE W₀ W₀ le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (V.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  refine ⟨hs ▸ regAt_fnOf hb _ s, ?_, ?_⟩
  · rw [← hs, OfModel.valAt_fnOf _ hb ht', hev]
    exact (e.mem_O _).1 (Subtype.property _)
  · rw [← hs, OfModel.valAt_fnOf _ hb ht', hev, unitAt_fnOf_iff hW₀, ← RegCrit.isUnit_eval_iff yt ht s]
    exact GlobalTheory.HtGen.IntPt.w_eq_one_iff e _
