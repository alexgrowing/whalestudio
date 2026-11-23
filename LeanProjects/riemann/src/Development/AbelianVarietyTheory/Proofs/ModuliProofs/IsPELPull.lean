import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPull

theorem lbIso_pull {X Y Y' : Scheme.{0}} {A : LB Y} {L : LB X} {φ : Y ⟶ X} (H : LBIso A (L.pull φ)) (h : Y' ⟶ Y)
    {F : Y' ⟶ X} (e : F = h ≫ φ) : LBIso (A.pull h) (L.pull F) :=
  H.chartPull (chartPullPull A h h rfl)
    (chartPullSame L (fun _ : PUnit => F) (fun _ : PUnit => φ) (fun _ => 1) h fun _ => e)

theorem isPEL_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g k J a bas o _ b ρ S S' s s' f t t' τ hs ⟨ψ, hψ, hψL, hpt, hact⟩ ⟨φ, hφ, hφL, hφa, hgeom⟩
  obtain ⟨τ', ⟨m⟩⟩ : ∃ τ' : SAB H S', Nonempty (SABMap τ' τ f) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f τ
    exact ⟨_, ⟨m⟩⟩
  have hL : LBIso τ'.PP.L (τ.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : IsGrpPullback τ'.G t.A f (m.cm.F ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨τ', e, he, ?_, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · exact (hL.trans τ'.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (lbIso_pull hφL m.cm.F rfl)).trans
      τ'.PP.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) (lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (τ'.act.act (a j)).left ≫ m.cm.F = m.cm.F ≫ (τ.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom K (x ≫ f) β (by rw [Category.assoc, hs, hx])
    refine ⟨fun σ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c y => ?_)
      (fun n y y' c hc => ?_) I, hI, fun i => ?_⟩
    · rw [GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ,
        GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ]
      exact hdet σ
    · apply Over.OverMorphism.ext
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' τ.G τ'.G f m.cm.F τ.PP.L τ'.PP.L τ.PP.isLB τ'.PP.isLB m.cart hL
        (Over.mk x) n y y' _ _ _ rfl rfl).2 hc
    · apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = (x ≫ f) ≫ (t.pt i).left :=
          congrArg (fun z => z.left) (hA i)
        have h₂ := GlobalTheory.ObjPull.pushEquiv_symm_left m.cart (Over.mk x) (I.ev k (bas (Pi.single i 1)))
        show (((GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)).symm (I.ev k (bas (Pi.single i 1)))).left ≫ e.hom.left) ≫ ψ =
          (x ≫ (t'.pt i).left) ≫ ψ
        rw [Category.assoc, heF, Category.assoc, hpt]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ.hom.left) h₂).trans (h₁.trans (Category.assoc _ _ _)))
      · rw [Over.w, Over.w]

end GlobalTheory.PELPull
