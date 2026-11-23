import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem isTen_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (t : IsTen C D h T) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), EllMap C' C f φ → ∃ t' : IsTen C' D h T', ∀ a, (t'.ten.tmul a).left ≫ m.φ = φ ≫ (t.ten.tmul a).left := by
  intro E _ _ _ H R _ ω C D h T t R' _ ω' C' f φ T' m hC
  obtain ⟨-, ⟨-, hφ, iC⟩, -, hact⟩ := hC
  have hφ' : Serre.IsLinearPullback C'.act C.act (spMap f) φ := ⟨hφ, hact⟩
  have hψ : Serre.IsLinearPullback (Serre.comapAct T'.t.act (algebraMap (OK H) (𝓞 E)))
      (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (spMap f) m.φ := ⟨m.cart, fun c => m.act _⟩
  have iT : LBIso (T.t.PP.L.pull m.φ) T'.t.PP.L :=
    LBIso.symm (show LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) from m.lin.imp fun _ h => h.1)
  have e := fun a => t.ten.baseChange_tmul hφ' hψ a
  refine ⟨⟨t.ten.baseChange hφ' hψ, fun s a => ?_, fun a b => ?_⟩, e⟩
  · refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine (e (s • a)).trans ?_
    rw [t.lin, Over.comp_left, Over.comp_left, Category.assoc, m.act s, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (T.t.act.act s).left) (e a).symm
  · exact lamEq_baseChange _ _ (spMap f) C.P.A C.P.A T.t.G C.P.A C'.P.A C'.P.A T'.t.G C'.P.A φ φ m.φ φ
      hφ.1.w hφ.1.w m.cart hφ T.t.PP.L C.P.L T'.t.PP.L C'.P.L T.t.PP.isLB C.P.isLB T'.t.PP.isLB C'.P.isLB iT iC
      _ _ _ _ _ _ _ _ (e a) (e b) (hact _) ((Category.id_comp _).trans (Category.comp_id _).symm) (t.lam a b)

end GlobalTheory.CM

end
