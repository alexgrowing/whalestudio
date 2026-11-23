import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionLinCombFiberProductSeparatedStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.BoxSpan

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def ev (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_cst (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst p U c) = ev (r ≫ p) z c :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _))

theorem gs_sum {I : Type} (s : Finset I) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : I → Γ(Y, U)) :
    gs r z U (∑ i ∈ s, a i) = ∑ i ∈ s, gs r z U (a i) := by
  simp only [gs_eq r z U h, map_sum]

theorem exists_sec_pw (L : LB X) (t : ℤ) (a : LB.Sec (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => t))) :
    ∃ a' : LB.Sec (pw L t), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
      sval a r z J = gs r z (L.U (J r)) (a'.f (J r)) := by
  have hle : ∀ i, L.U i ≤ LB.wchart L (K := PUnit) (fun _ => 𝟙 X) (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  refine ⟨⟨fun i => rs X (hle i) (a.f fun _ => i), fun i j => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · have hy' : y ∈ L.U i ⊓ L.U j := hy
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (hle i) hy'.1 _)).trans
      ((sec_trans a (𝟙 X) y (hle i hy'.1) (hle j hy'.2)).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (hle j) hy'.2 _)).symm
    refine Eq.trans ?_ (gs_unit (𝟙 X) y (L.U i ⊓ L.U j) hy' (L.g i j ^ t)).symm
    rw [map_zpow]
    exact congrArg Units.val (Fintype.prod_unique (fun _ : PUnit => gm (𝟙 X ≫ 𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) ^ t))
  · rw [sval_of a r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact (gs_res r z (hle _) (hJ r) _).symm

theorem isProper_powObj {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A) :
    ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => (AbelianSchemeGerms.isAbelianScheme_powObj A h n).proper

theorem exists_coords (x : KeyIn R) {m N : ℕ} (b : Fin N → RR x m) (hb : IsBasis x b)
    (a : LB.Sec (LB.LinComb x.P.L (K := PUnit) (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)))) :
    ∃ c : Fin N → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) J, Good x.P.L z J →
      sval a r z J = ∑ k, ev (r ≫ x.P.A.hom) z (c k) * gs r z (x.P.L.U (J r)) ((b k).f (J r)) := by
  obtain ⟨a', ha⟩ := exists_sec_pw x.P.L m a
  obtain ⟨c, hc, -⟩ := hb a'
  refine ⟨c, fun Z r z J hJ => (ha Z r z J hJ).trans ((congrArg (gs r z _) (hc (J r))).trans
    ((gs_sum _ r z _ (hJ r) _).trans (Finset.sum_congr rfl fun k _ => ?_)))⟩
  exact (gs_mul r z _ (hJ r) _ _).trans (congrArg (· * _) (gs_cst _ r z _ (hJ r) _))

theorem sum_mul_sum_cons {T : Type} [CommRing T] {E₁ E₂ E : R →+* T} (h₁ : E₁ = E) (h₂ : E₂ = E) {n N k : ℕ}
    (G : Fin (n + 1) → Fin N → T) (c : Fin k → Fin N → R) (q : Fin k → (Fin n → Fin N) → R) :
    ∑ i, (∑ j, E₁ (c i j) * G 0 j) * ∑ I, E₂ (q i I) * ∏ d : Fin n, G d.succ (I d) =
      ∑ I : Fin (n + 1) → Fin N, E (∑ i, c i (I 0) * q i (Fin.tail I)) * ∏ d, G d (I d) := by
  subst h₁ h₂
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, map_sum, map_mul]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i _ => ?_
  rw [show Fin.tail ((Fin.consEquiv fun _ => Fin N) (j, I)) = I from Fin.tail_cons _ _]
  ring

theorem span_ev (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m) (hb : IsBasis x b) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))),
      ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj x.P.A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  induction n with
  | zero =>
    intro s
    have hW : LB.wchart x.P.L (K := Fin 0) (fun c => (Out.powPr x.P.A c).left) Fin.elim0 = ⊤ :=
      top_le_iff.1 fun _ _ => Set.mem_iInter.2 fun k => k.elim0
    haveI : IsIso (Out.powObj x.P.A 0).hom := inferInstanceAs (IsIso (𝟙 (Sp K)))
    obtain ⟨c, hc⟩ := (cst_bijective (Out.powObj x.P.A 0).hom hW).2 (s.f Fin.elim0)
    refine ⟨fun _ => c, fun Z r z J hJ => ?_⟩
    rw [sval_of s r z J Fin.elim0 (fun k => k.elim0), ← hc, Fintype.sum_unique, Fin.prod_univ_zero, _root_.mul_one]
    exact gs_cst _ r z _ (Set.mem_iInter.2 fun k => k.elim0) c
  | succ n ih =>
    intro s
    haveI := x.P.isAb.proper
    haveI := isProper_powObj x.P.A x.P.isAb n
    have hF : FormEq (K := Fin (n + 1)) (K' := PUnit ⊕ Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ))
        (Sum.elim (fun _ => (fst x.P.A (Out.powObj x.P.A n)).left ≫ 𝟙 x.P.A.left)
          (fun k => (snd x.P.A (Out.powObj x.P.A n)).left ≫ (Out.powPr x.P.A k).left))
        (Sum.elim (fun _ => (m : ℤ)) (fun _ => (m : ℤ))) := fun U _ h => by
      rw [Fin.prod_univ_succ, Fintype.prod_sum_type]
      exact congrArg₂ (· * ·) (Fintype.prod_unique
        (fun _ : PUnit => h ((fst x.P.A (Out.powObj x.P.A n)).left ≫ 𝟙 x.P.A.left) ^ (m : ℤ))).symm rfl
    obtain ⟨v, hv⟩ := exists_sec x.P.isLB hF s
    obtain ⟨k, a₁, a₂, ha⟩ := (GlobalTheory.T.section_lin_comb_fiber_product_separated K x.P.A.left x.P.L x.P.isLB x.P.A (Out.powObj x.P.A n) PUnit (Fin n)
      (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ))).1 v
    choose c hc using fun i => exists_coords x b hb (a₁ i)
    choose q hq using fun i => ih (a₂ i)
    refine ⟨fun I => ∑ i, c i (I 0) * q i (Fin.tail I), fun Z r z J hJ => ?_⟩
    refine (hv Z r z J hJ).symm.trans ((ha Z r z J hJ).trans ?_)
    have e₁ : (r ≫ (fst x.P.A (Out.powObj x.P.A n)).left) ≫ x.P.A.hom = r ≫ (Out.powObj x.P.A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (fst x.P.A (Out.powObj x.P.A n))))
    have e₂ : (r ≫ (snd x.P.A (Out.powObj x.P.A n)).left) ≫ (Out.powObj x.P.A n).hom =
        r ≫ (Out.powObj x.P.A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (snd x.P.A (Out.powObj x.P.A n))))
    refine (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (hc i Z _ z J hJ) (hq i Z _ z J hJ)).trans ?_
    exact sum_mul_sum_cons (congrArg (ev · z) e₁) (congrArg (ev · z) e₂)
      (fun d j => gs (r ≫ (Out.powPr x.P.A d).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A d).left)))
          ((b j).f (J (r ≫ (Out.powPr x.P.A d).left)))) c q

theorem boxProducts_span : ∀ (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m), IsBasis x b → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))), ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  intro K _ x m N b hb n s
  obtain ⟨q, hq⟩ := span_ev K x m N b hb n s
  refine ⟨q, fun Z r z J hJ => (hq Z r z J hJ).trans (Finset.sum_congr rfl fun I _ => ?_)⟩
  rw [gs_cst _ r z ⊤ trivial]

end GlobalTheory.BoxSpan
