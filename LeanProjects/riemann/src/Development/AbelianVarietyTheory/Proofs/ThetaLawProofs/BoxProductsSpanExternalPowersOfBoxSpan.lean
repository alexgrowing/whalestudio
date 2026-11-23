import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.PowSpan

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def ev (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_cst (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst p U c) = ev (r ≫ p) z c :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _))

theorem sum_mul_cons {T : Type} [CommRing T] {E₂ E : R →+* T} (h₂ : E₂ = E) {n N : ℕ}
    (G : Fin (n + 1) → Fin N → T) (q : Fin N → (Fin n → Fin N) → R) :
    ∑ k, (∑ I, E₂ (q k I) * ∏ d : Fin n, G d.succ (I d)) * G 0 k =
      ∑ I : Fin (n + 1) → Fin N, E (q (I 0) (Fin.tail I)) * ∏ d, G d (I d) := by
  subst h₂
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [show Fin.tail ((Fin.consEquiv fun _ => Fin N) (k, I)) = I from Fin.tail_cons _ _]
  ring

theorem span_ev (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (hL : L.IsLB)
    (hb : ∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))),
      ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  induction n with
  | zero =>
    intro s
    have hW : LB.wchart L (K := Fin 0) (fun c => (Out.powPr A c).left) Fin.elim0 = ⊤ :=
      top_le_iff.1 fun _ _ => Set.mem_iInter.2 fun k => k.elim0
    haveI : IsIso (Out.powObj A 0).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))
    obtain ⟨c, hc⟩ := (cst_bijective (Out.powObj A 0).hom hW).2 (s.f Fin.elim0)
    refine ⟨fun _ => c, fun Z r z J hJ => ?_⟩
    rw [sval_of s r z J Fin.elim0 (fun k => k.elim0), ← hc, Fintype.sum_unique, Fin.prod_univ_zero, _root_.mul_one]
    exact gs_cst _ r z _ (Set.mem_iInter.2 fun k => k.elim0) c
  | succ n ih =>
    intro s
    have hF : FormEq (K := Fin (n + 1)) (K' := Fin n ⊕ PUnit) (fun c => (Out.powPr A c).left) (fun _ => t)
        (Sum.elim (fun k => (snd A (Out.powObj A n)).left ≫ (Out.powPr A k).left)
          (fun _ => (fst A (Out.powObj A n)).left))
        (Sum.elim (fun _ => t) (fun _ => t)) := fun U _ h => by
      rw [Fin.prod_univ_succ, Fintype.prod_sum_type, mul_comm]
      exact congrArg₂ (· * ·) rfl (Fintype.prod_unique
        (fun _ : PUnit => h (fst A (Out.powObj A n)).left ^ t)).symm
    obtain ⟨v, hv⟩ := exists_sec hL hF s
    obtain ⟨a, ha⟩ := hb (Out.powObj A n) (Fin n) (fun c => (Out.powPr A c).left) (fun _ => t) v
    choose q hq using fun i => ih (a i)
    refine ⟨fun I => q (I 0) (Fin.tail I), fun Z r z J hJ => ?_⟩
    refine (hv Z r z J hJ).symm.trans ((ha Z r z J hJ).trans ?_)
    have e₂ : (r ≫ (snd A (Out.powObj A n)).left) ≫ (Out.powObj A n).hom =
        r ≫ (Out.powObj A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (snd A (Out.powObj A n))))
    refine (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (hq i Z _ z J hJ) rfl).trans ?_
    exact sum_mul_cons (congrArg (ev · z) e₂)
      (fun d j => gs (r ≫ (Out.powPr A d).left) z (L.U (J (r ≫ (Out.powPr A d).left)))
          ((b j).f (J (r ≫ (Out.powPr A d).left)))) q

theorem boxProducts_span_of_boxSpan : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), L.IsLB → (∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))), ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by
  intro R _ A L t N b hL hb n s
  obtain ⟨q, hq⟩ := span_ev A L t N b hL hb n s
  refine ⟨q, fun Z r z J hJ => (hq Z r z J hJ).trans (Finset.sum_congr rfl fun I _ => ?_)⟩
  rw [gs_cst _ r z ⊤ trivial]

end GlobalTheory.PowSpan
