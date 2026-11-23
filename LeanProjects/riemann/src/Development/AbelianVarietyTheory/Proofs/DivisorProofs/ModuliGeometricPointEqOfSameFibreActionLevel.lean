import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem moduli_point_eq_of_same_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (x x' : Sp K ⟶ Xo.X) (α α' : P.A.left ⟶ Xo.univ.t.G.left), x ≫ Xo.s = x' ≫ Xo.s → IsGrpPullback P.A Xo.univ.t.G x α → IsGrpPullback P.A Xo.univ.t.G x' α' → LBIso P.L (Xo.univ.t.PP.L.pull α) → LBIso P.L (Xo.univ.t.PP.L.pull α') → (∀ a, ∃ h : P.A ⟶ P.A, h.left ≫ α = α ≫ (Xo.univ.t.act.act a).left ∧ h.left ≫ α' = α' ≫ (Xo.univ.t.act.act a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.eta a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.eta a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.etaA a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.etaA a).left) → x = x' := by
  intro E _ _ _ H D l Xo K _ _ P x x' α α' hs hα hα' hL hL' hact hM hA
  choose act h₁ h₂ using hact
  have h : GlobalTheory.ArcUnique.IsFibre P.A act P.L Xo.univ.t x α := ⟨hα, h₁, hL⟩
  have h' : GlobalTheory.ArcUnique.IsFibre P.A act P.L Xo.univ.t x' α' := ⟨hα', h₂, hL'⟩
  obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ (Sp K) Xo.s
    (x ≫ Xo.s) x rfl rfl ((Category.comp_id _).symm.trans (congrArg ((x ≫ Xo.s) ≫ ·) (Spec.map_id _).symm)) Xo.univ
  obtain ⟨ρ, e₁, g, ha, hi⟩ := h.cancel P.isLB o'.t.PP.isLB (GlobalTheory.ArcUnique.isFibre_of_sabMap m.toSABMap)
    (Category.id_comp x)
  obtain ⟨f₁, f₂, f₃⟩ := h'.precomp P.isLB o'.t.PP.isLB g ha hi
  rw [Category.id_comp] at f₁
  have := o'.proper
  obtain ⟨m', hm'⟩ := exists_sabMap_of_lbIso E H _ _ Xo.univ.t o'.t x' (ρ ≫ α')
    ⟨inferInstance, fun s _ K _ _ t _ => inferInstance⟩ f₁ f₂ f₃
  have key : ∀ (y : 𝟙_ (Over (Sp K)) ⟶ o'.t.G) (w : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
      y.left ≫ m.toSABMap.φ = x ≫ w.left →
      (∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ w.left ∧ z.left ≫ α' = x' ≫ w.left) →
      y.left ≫ m'.φ = x' ≫ w.left := by
    rintro y w hy ⟨z, z₁, z₂⟩
    have e : y.left ≫ ρ = z.left := hα.1.hom_ext (by rw [Category.assoc, e₁, hy, z₁]) (by
      rw [Category.assoc, g.1.w, ← Category.assoc, Over.w, Over.w]
      exact Category.comp_id _)
    rw [hm', ← Category.assoc, e, z₂]
  exact (Xo.rep _ _ inferInstance o').unique ⟨rfl, ⟨m⟩⟩
    ⟨hs.symm, ⟨⟨m', fun a => key _ _ (m.eta a) (hM a), fun a => key _ _ (m.etaA a) (hA a)⟩⟩⟩

end GlobalTheory.UMin
