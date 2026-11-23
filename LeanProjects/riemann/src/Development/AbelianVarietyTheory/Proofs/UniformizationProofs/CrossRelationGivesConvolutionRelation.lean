import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.MixedConv
open GlobalTheory.FieldBaseChange

section Base
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem prod_coord {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oε i =
      h (cP D T χ * p).left * (h (cP D T χ).left)⁻¹ * (h p.left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (1 : ℤ) * h (cP D _ χ).left ^ (-1 : ℤ) * h p.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_coord_inv {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oinvε i =
      (h (cP D T χ * p).left)⁻¹ * h (cP D T χ).left * h p.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h p.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_comp {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (χ : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ D.famφB χ i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (cP D T χ * ρ).left * (h (cP D T χ).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e₀ : ρ.left ≫ D.famφB χ 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ D.famφB χ 1 = (cP D T χ * ρ).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 D.P.A) (cP D _ χ)).trans
      (by rw [comp_cP, Category.comp_id, mul_comm]))
  have e₂ : ρ.left ≫ D.famφB χ 2 = (cP D T χ).left := congrArg (fun q => q.left) (comp_cP D ρ χ)
  have e₃ : ρ.left ≫ D.famφB χ 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

def cubB (a b : D.X) := LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
  (lift (cP D D.P.A a) (lift (cP D D.P.A b) (𝟙 D.P.A))).left

theorem cubB_isGen (a b : D.X) : (cubB D a b).IsGen := DVR.pullGen_isGen _ _ _ _ D.cub.isGen _

def mixφ (a : D.P.A ⟶ D.P.A) (α : D.X) : PUnit.{1} ⊕ Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  Sum.elim (fun _ => a.left) (D.famφB α)

def mixε (j j' : ℕ) : PUnit.{1} ⊕ Fin 4 → ℤ := Sum.elim (fun _ => (j : ℤ)) (DegPre.famε j')

theorem prod_mix {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (a : D.P.A ⟶ D.P.A) (α : D.X) (j j' : ℕ)
    {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (ρ.left ≫ mixφ D a α i) ^ mixε j j' i = h (ρ ≫ a).left ^ (j : ℤ) *
      (h ρ.left ^ ((j' : ℤ) - 1) * h (cP D T α * ρ).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left) :=
  prod_sum₂ (K := PUnit.{1}) (K' := Fin 4) (U := U) _ (Fintype.prod_unique _) (prod_comp D ρ α j' h)

theorem exists_mix (a : D.P.A ⟶ D.P.A) (j j' : ℕ) (χ χ' β α : D.X) (hα : χ' + β = α)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) χ') (D.Oφ a χ)) (Sum.elim Oε Oinvε))) (hu : u.IsGen)
    (f : D.SecB j χ) (f' : D.SecB j' β) : ∃ n : LB.Sec (LB.LinComb D.P.L (mixφ D a α) (mixε j j')),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → sval n r z J =
        sval f (r ≫ a.left) z J * sval f' r z J * (val u r z J * val (cubB D χ' β) r z J).val := by
  subst hα
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := mixφ D a (χ' + β)) (ε' := mixε j j') (fun U _ h => by
      have p₁ := prod_cub (cP D D.P.A χ') (cP D D.P.A β) (𝟙 D.P.A) h
      have p₂ := prod_comp D a χ j h
      have p₃ := prod_comp D (𝟙 _) β j' h
      have p₄ := prod_mix D (𝟙 _) a (χ' + β) j j' h
      have p₅ := prod_coord D (𝟙 _) χ' h
      have p₆ := prod_coord_inv D a χ h
      rw [DVR.cPoint_add] at p₄
      simp only [Over.id_left, Category.id_comp] at p₃ p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := (Fin 4 ⊕ Fin 4) ⊕ thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₂ p₃)
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₅ p₆) p₁)) (Eq.trans ?_ p₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.id_left]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec f a.left) f')
      (Geo.Tor.genSec (LB.mulGen D.P.L _ _ _ _ u (cubB D χ' β)) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (cubB_isGen D χ' β))))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  exact (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ) rfl))
    ((sval_genSec _ _ _ z hJ).trans (congrArg Units.val (val_mul hJ _ _ _)))))

end Base

section Level
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem expand_common (e k : ℕ) {N : Type} [Fintype N] (σ : N → H0 U.LG.L k)
    (f : N → ∀ α : D.toPre.X, D.toPre.SecB k α) (h : ∀ ν, U.ExpandsAt e k (σ ν) (f ν)) :
    ∃ S : Finset D.toPre.X, ∀ ν (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J),
      Good D.toPre.P.L z J → (∀ α ∉ S, sval (f ν α) (r ≫ pGl U e) z J = 0) ∧ ∀ J', Good U.LG.L z J' →
      (wv U e r z (J (r ≫ pGl U e)) (J' ((r ≫ fGl I G e) ≫ 𝟙 _)) ^ k).val * sval (σ ν) (r ≫ fGl I G e) z J' =
        ∑ α ∈ S, sval (f ν α) (r ≫ pGl U e) z J * (val (tG U e α) r z J).val := by
  classical
  choose S hS using fun ν => expandsAt_val U e k (σ ν) (f ν) (h ν)
  refine ⟨Finset.univ.biUnion S, fun ν Z r z J hJ => ⟨fun α hα => (hS ν Z r z J hJ).1 α fun hh =>
    hα (Finset.mem_biUnion.2 ⟨ν, Finset.mem_univ _, hh⟩), fun J' hJ' => ?_⟩⟩
  refine ((hS ν Z r z J hJ).2 _ (hJ' ((r ≫ fGl I G e) ≫ 𝟙 _))).trans (Finset.sum_subset
    (Finset.subset_biUnion_of_mem S (Finset.mem_univ ν)) fun α _ hα => ?_)
  rw [(hS ν Z r z J hJ).1 α hα, zero_mul]

theorem t_mul_val (e : ℕ) (a b : D.toPre.X) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left) (z : Z) {J}
    (hJ : Good D.toPre.P.L z J) : val (tG U e (a + b)) x z J * val (cubB D.toPre a b) (x ≫ pGl U e) z J =
      val (tG U e a) x z J * val (tG U e b) x z J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ ((U.gt e).t_mul a b) x).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  have e₁ : (U.gt e).pG ≫ lift (cP D.toPre _ a) (lift (cP D.toPre _ b) (𝟙 _)) =
      lift (cP D.toPre _ a) (lift (cP D.toPre _ b) (U.gt e).pG) := by
    rw [comp_lift, comp_lift, comp_cP, comp_cP, Category.comp_id]
  exact congrArg (fun q => val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε)
    D.toPre.cub.t q z J) ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (congrArg (fun q => q.left) e₁)))

variable {U} (E : EndU U)

theorem end_fGl (e : ℕ) : ((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e = fGl I G e ≫ E.aG.left :=
  pullback.lift_fst _ _ _

theorem end_pGl (e : ℕ) : ((Over.pullback (thick R I e)).map E.aG).left ≫ pGl U e = pGl U e ≫ E.aB.left := by
  have h₁ := congrArg (fun q => q.left) (E.q_lin e)
  have h₂ : ((Over.pullback (thick R I e)).map E.aB).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ E.aB.left :=
    pullback.lift_fst _ _ _
  show _ ≫ (U.gt e).q.left ≫ pullback.fst _ _ = ((U.gt e).q.left ≫ pullback.fst _ _) ≫ _
  rw [← Category.assoc]
  exact (congrArg (· ≫ pullback.fst _ _) h₁).trans ((Category.assoc _ _ _).trans
    ((congrArg ((U.gt e).q.left ≫ ·) h₂).trans (Category.assoc _ _ _).symm))

theorem level (j j' e : ℕ) {N : Type} [Fintype N] (ρ : N → R) (σ : N → H0 U.LG.L j) (σ' : N → H0 U.LG.L j')
    (f : N → ∀ α : D.toPre.X, D.toPre.SecB j α) (f' : N → ∀ α : D.toPre.X, D.toPre.SecB j' α)
    (hE : ∀ ν, U.ExpandsAt e j (σ ν) (f ν)) (hE' : ∀ ν, U.ExpandsAt e j' (σ' ν) (f' ν))
    (hrel : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J →
      ∑ ν, constVal (r ≫ G.hom) z (ρ ν) * (sval (σ ν) (r ≫ E.aG.left) z J * sval (σ' ν) r z J) = 0)
    (m : ∀ α, {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α} →
      LB.Sec (LB.LinComb D.toPre.P.L (mixφ D.toPre E.aB α) (mixε j j')))
    (hm : ∀ α p (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (m α p) r z J = ∑ ν, constVal (r ≫ D.toPre.P.A.hom) z (ρ ν) *
        (sval (f ν p.1.1) (r ≫ E.aB.left) z J * sval (f' ν p.1.2) r z J *
          (val (E.u p.1.1) r z J * val (cubB D.toPre (E.h p.1.1) p.1.2) r z J).val)) (α : D.toPre.X) :
    ∃ S : Finset {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α}, ∀ (Z : Scheme.{0})
      (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J →
      (∀ i ∉ S, sval (m α i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧
        ∑ i ∈ S, sval (m α i) (r ≫ (D.toPre.prBe I e).left) z J = 0 := by
  classical
  obtain ⟨S, hS⟩ := expand_common U e j σ f hE
  obtain ⟨S', hS'⟩ := expand_common U e j' σ' f' hE'
  let ae := ((Over.pullback (thick R I e)).map E.aG).left
  have hp : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left), (x ≫ ae) ≫ pGl U e = (x ≫ pGl U e) ≫ E.aB.left :=
    fun x => by rw [Category.assoc, Category.assoc, end_pGl E e]
  have hf : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left), (x ≫ ae) ≫ fGl I G e = (x ≫ fGl I G e) ≫ E.aG.left :=
    fun x => by rw [Category.assoc, Category.assoc, end_fGl E e]
  let d : ∀ α, SecOver D.toPre.P.A.hom (LB.LinComb D.toPre.P.L (mixφ D.toPre E.aB α) (mixε j j')) := fun α =>
    ∑ p ∈ (S ×ˢ S').subtype (fun p => E.h p.1 + p.2 = α), (m α p : SecOver D.toPre.P.A.hom _)
  have lift : ∀ n : LB.Sec (LB.LinComb D.toPre.P.L (mixφ D.toPre E.aB α) (mixε j j')),
      (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval n (x ≫ pGl U e) z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J),
        Good D.toPre.P.L z J → sval n (r ≫ (D.toPre.prBe I e).left) z J = 0 := fun n hn Z r z J hJ =>
    GlobalTheory.LiftTest.main R I D.toPre e G (U.gt e) D.toPre.P.A (𝟙 _) _ D.toPre.P.L D.toPre.P.isLB _ _ _ n
      (fun Z x r hr z J hJ => by
        obtain rfl : r = x ≫ pGl U e := (Category.comp_id r).symm.trans hr
        exact hn Z x z J hJ) Z _
      ⟨r ≫ pullback.snd _ _, by
        rw [Category.assoc, Category.assoc]; exact congrArg (r ≫ ·) pullback.condition.symm⟩ z J hJ
  refine ⟨(S ×ˢ S').subtype (fun p => E.h p.1 + p.2 = α), fun Z r z J hJ => ⟨fun i hi => ?_, ?_⟩⟩
  · refine lift _ (fun Z x z J hJ => ?_) Z r z J hJ
    rw [hm α i _ _ z J hJ]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [Finset.mem_subtype, Finset.mem_product, not_and_or] at hi
    rcases hi with hi | hi
    · rw [← hp, (hS ν Z (x ≫ ae) z J hJ).1 _ hi, zero_mul, zero_mul, mul_zero]
    · rw [(hS' ν Z x z J hJ).1 _ hi, mul_zero, zero_mul, mul_zero]
  · refine (sval_sum' (π := D.toPre.P.A.hom) hJ _ _ _).symm.trans (lift (d α) (fun Z x z J hJ => ?_) Z r z J hJ)
    refine GlobalTheory.sval_eq_zero_of_sum_mul_coord R I D.toPre e G (U.gt e) D.toPre.P.A (𝟙 _) _
      (mixφ D.toPre E.aB) (mixε j j') d (insert α ((S ×ˢ S').image fun p => E.h p.1 + p.2)) ?_ α
      (Finset.mem_insert_self _ _) Z x _ (Category.comp_id _) z J hJ
    intro Z x r hr z J hJ
    obtain rfl : r = x ≫ pGl U e := (Category.comp_id r).symm.trans hr
    obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' U.LG.isLB z
    let T : D.toPre.X × D.toPre.X → Z.presheaf.stalk z := fun p => ∑ ν, constVal ((x ≫ pGl U e) ≫ D.toPre.P.A.hom) z (ρ ν) *
      ((sval (f ν p.1) ((x ≫ ae) ≫ pGl U e) z J * (val (tG U e p.1) (x ≫ ae) z J).val) *
        (sval (f' ν p.2) (x ≫ pGl U e) z J * (val (tG U e p.2) x z J).val))
    have k₁ : ∀ β, sval (d β) (x ≫ pGl U e) z J * (val (tG U e β) x z J).val =
        ∑ p ∈ (S ×ˢ S').filter (fun p => E.h p.1 + p.2 = β), T p := fun β => by
      refine (congrArg (· * _) (sval_sum' (π := D.toPre.P.A.hom) hJ _ _ _)).trans ?_
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨⟨χ, δ⟩, rfl⟩ := p
      rw [hm _ _ _ _ z J hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have a₁ := congrArg Units.val (t_mul_val U e (E.h χ) δ x z hJ)
      have a₂ := congrArg Units.val (E.t_lin e χ Z x z J hJ)
      simp only [Units.val_mul] at a₁ a₂ ⊢
      rw [hp]
      erw [a₂]
      linear_combination (constVal ((x ≫ pGl U e) ≫ D.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U e) ≫ E.aB.left) z J * sval (f' ν δ) (x ≫ pGl U e) z J *
        (val (E.u χ) (x ≫ pGl U e) z J).val) * a₁
    refine (Finset.sum_congr rfl fun β _ => k₁ β).trans ((Finset.sum_fiberwise_of_maps_to (fun p hp =>
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)) T).trans ?_)
    have hc : (x ≫ pGl U e) ≫ D.toPre.P.A.hom = (x ≫ fGl I G e) ≫ G.hom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) ((Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm)
    have k₂ := hrel Z (x ≫ fGl I G e) z J' hJ'
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun ν _ => ?_) ((Finset.mul_sum _ _ _).symm.trans
      ((congrArg (((wv U e (x ≫ ae) z (J ((x ≫ ae) ≫ pGl U e)) (J' (((x ≫ ae) ≫ fGl I G e) ≫ 𝟙 _)) ^ j).val *
        (wv U e x z (J (x ≫ pGl U e)) (J' ((x ≫ fGl I G e) ≫ 𝟙 _)) ^ j').val) * ·) k₂).trans (mul_zero _)))
    rw [← Finset.mul_sum, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_mul_sum, ← (hS ν Z (x ≫ ae) z J hJ).2 J' hJ',
      ← (hS' ν Z x z J hJ).2 J' hJ', hc, ← hf]
    ring

end Level

section Eval
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

def IsCoefB (k : ℕ) (g : GtPtF D F) (w : Frm D F k g.b) (χ : D.X) (f : D.SecB k χ) (x : F) : Prop :=
  ∀ (z : (TF (R := R) F).left) (J), Good D.P.L z J →
    cst F z x * (rigV D (TF (R := R) F).hom z J).val ^ k =
      sval f g.b.left z J * (val (g.s χ) (𝟙 _) z J).val * (val w (𝟙 _) z J).val

theorem lift_prB (b : TF (R := R) F ⟶ D.P.A) :
    (lift (𝟙 (TF (R := R) F)) b).left ≫ (DegPre.prB D F).left = b.left :=
  congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) F)) b)

theorem exists_isCoefB {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (f : D.SecB k χ) :
    ∃ x, IsCoefB k g w χ f x := by
  obtain ⟨s, hs⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D F χ) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq])
    (H1.SectionArithmetic.pullSec f (DegPre.prB D F).left)
  obtain ⟨x, hx⟩ := CoefBasic.exists_isCoef g hw χ s
  refine ⟨x, fun z J hJ => (hx z J hJ).trans ?_⟩
  rw [hs _ _ z J hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, lift_prB]

theorem coef_of_secLin {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s : Fam D F k} {n : ℕ}
    {f : Fin n → D.SecB k χ} {c x : Fin n → F}
    (h : GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) (s.s χ) (D.famφB χ) (DegPre.famε k) f
      (DegPre.prB D F).left (fun i => scal (fst (TF (R := R) F) D.P.A).left (c i)))
    (hx : ∀ i, IsCoefB k g w χ (f i) (x i)) : coef s g w χ = ∑ i, c i * x i := by
  refine CoefBasic.coef_eq fun z J hJ => ?_
  rw [GlobalTheory.BoxExpansion.secLin_val h _ z hJ, CoefBasic.cst_eq, map_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₁ : gs (lift (𝟙 (TF (R := R) F)) g.b).left z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) =
      CoefBasic.cstH z (c i) := by
    refine (gs_scal _ _ z _).trans (Eq.trans ?_ (CoefBasic.cst_eq z _))
    rw [← Over.comp_left, lift_fst]; rfl
  have e₂ := hx i z J hJ
  rw [CoefBasic.cst_eq] at e₂
  rw [e₁, lift_prB, map_mul]
  linear_combination CoefBasic.cstH z (c i) * e₂

theorem exists_frame (a : D.P.A ⟶ D.P.A) (α : D.X) {j j' : ℕ} (g : GtPtF D F) {b' : TF (R := R) F ⟶ D.P.A}
    (hb : b' = g.b ≫ a) (w : Frm D F j b') (w' : Frm D F j' g.b) (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb D.P.L (fun i => g.b.left ≫ mixφ D a α i) (mixε j j')), τ.IsGen ∧
      ∀ z J, Good D.P.L z J → val τ (𝟙 _) z J = rigV D (TF (R := R) F).hom z J ^ (j + j') *
        (val (g.s α) (𝟙 _) z J * (val w (𝟙 _) z J * val w' (𝟙 _) z J))⁻¹ := by
  let ρ : LB.Gen (LB.LinComb D.P.L (fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D.P.A) (fun _ => 1)) :=
    LB.pullGen D.P.L (fun _ : PUnit.{1} => eSec D.P.A) (fun _ => 1) D.rig (TF (R := R) F).hom
  have hρ : ρ.IsGen := DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  obtain ⟨τ, hτ, hv⟩ := exists_gen D.P.isLB (φ' := fun i => g.b.left ≫ mixφ D a α i) (ε' := mixε j j')
    (fun U _ h => by
      have p₀ : ∏ i : PUnit.{1}, h ((fun _ : PUnit.{1} => (TF (R := R) F).hom ≫ eSec D.P.A) i) ^
          (((j + j' : ℕ) : ℤ) * (fun _ => (1 : ℤ)) i) = h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((j + j' : ℕ) : ℤ) := by
        rw [Fintype.prod_unique, _root_.mul_one]; rfl
      have p₁ := prod_gt g.b α h
      have p₂ := CoefBasic.prod_line j b' h
      have p₃ := CoefBasic.prod_line j' g.b h
      have p₄ := prod_mix D g.b a α j j' h
      have p₅ := prod_neg (fun i => h (Sum.elim (DegPre.gtφ D F g.b α)
        (Sum.elim (DegPre.lineφ D F b') (DegPre.lineφ D F g.b)) i))
        (Sum.elim DegPre.gtε (Sum.elim (DegPre.lineε j) (DegPre.lineε j')))
        (DVR.prod_sum₂ (U := U) _ p₁ (DVR.prod_sum₂ (U := U) _ p₂ p₃))
      refine Eq.trans (DVR.prod_sum₂ (U := U) _ p₀ p₅) (Eq.trans ?_ p₄.symm)
      rw [← hb]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ ρ (j + j')) (LB.invGen D.P.L _ _
      (LB.mulGen D.P.L _ _ _ _ (g.s α) (LB.mulGen D.P.L _ _ _ _ w w'))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ hρ _) (DVR.invGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) (DVR.mulGen_isGen _ _ _ _ _ _ _ hw hw'))))
  refine ⟨τ, hτ, fun z J hJ => (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ?_
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _)))))))⟩
  refine (map_pow _ _ _).trans (congrArg (· ^ (j + j')) ((val_pull hJ _ _ _).trans ?_))
  rw [Category.id_comp]; rfl

end Eval

section Core
variable {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]

theorem core (hL : LL) (hR : AdmBase R I) (j j' : ℕ) {N : Type} [Fintype N] (ρ : N → R) (σ : N → H0 U.LG.L j)
    (σ' : N → H0 U.LG.L j')
    (f : N → ∀ α : D.toPre.X, D.toPre.SecB j α) (f' : N → ∀ α : D.toPre.X, D.toPre.SecB j' α)
    (hE : ∀ ν e, U.ExpandsAt e j (σ ν) (f ν)) (hE' : ∀ ν e, U.ExpandsAt e j' (σ' ν) (f' ν))
    (hrel : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J →
      ∑ ν, constVal (r ≫ G.hom) z (ρ ν) * (sval (σ ν) (r ≫ E.aG.left) z J * sval (σ' ν) r z J) = 0)
    (g g' : GtPtF D.toPre F) (hg : E.Act g g') (w : Frm D.toPre F j g'.b) (w' : Frm D.toPre F j' g.b)
    (hw : w.IsGen) (hw' : w'.IsGen) (x x' : N → D.toPre.X → F)
    (hx : ∀ ν χ, IsCoefB j g' w χ (f ν χ) (x ν χ)) (hx' : ∀ ν χ, IsCoefB j' g w' χ (f' ν χ) (x' ν χ))
    (α : D.toPre.X) :
    SumF I F (fun p : {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α} =>
      ∑ ν, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν)) * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  choose n hn using fun (ν : N) (α : D.toPre.X) (p : {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α}) =>
    exists_mix D.toPre E.aB j j' p.1.1 (E.h p.1.1) p.1.2 α p.2 (E.u p.1.1) (E.u_norm p.1.1).1 (f ν p.1.1) (f' ν p.1.2)
  let m : ∀ α, {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α} →
      SecOver D.toPre.P.A.hom (LB.LinComb D.toPre.P.L (mixφ D.toPre E.aB α) (mixε j j')) := fun α p =>
    ∑ ν, ρ ν • (show SecOver D.toPre.P.A.hom _ from n ν α p)
  have hm : ∀ α p (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (m α p) r z J = ∑ ν, constVal (r ≫ D.toPre.P.A.hom) z (ρ ν) *
        (sval (f ν p.1.1) (r ≫ E.aB.left) z J * sval (f' ν p.1.2) r z J *
          (val (E.u p.1.1) r z J * val (cubB D.toPre (E.h p.1.1) p.1.2) r z J).val) := fun α p Z r z J hJ =>
    (sval_sum' (π := D.toPre.P.A.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
      (sval_smul' (π := D.toPre.P.A.hom) hJ _ _ _).trans (congrArg _ (hn ν α p Z r z J hJ)))
  obtain ⟨τ, hτ, hv⟩ := exists_frame E.aB α g hg.1 w w' hw hw'
  refine GlobalTheory.T.adicSum_sections_of_finite_sums_on_thickenings hL R I hR D F _ (mixφ D.toPre E.aB α) (mixε j j') _ (m α)
    (0 : SecOver D.toPre.P.A.hom _) (fun e => ?_) g.b τ hτ _ 0 fun z J hJ => ⟨fun p => ?_, ?_⟩
  · obtain ⟨S, hS⟩ := level E j j' e ρ σ σ' f f' (fun ν => hE ν e) (fun ν => hE' ν e) hrel m hm α
    exact ⟨S, fun Z r z J hJ => ⟨(hS Z r z J hJ).1,
      (sval_zero' (π := D.toPre.P.A.hom) hJ _).trans (hS Z r z J hJ).2.symm⟩⟩
  · obtain ⟨⟨χ, δ⟩, rfl⟩ := p
    rw [hm _ _ _ _ z J hJ, CoefBasic.cst_eq, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have c₁ : constVal (g.b.left ≫ D.toPre.P.A.hom) z (ρ ν) =
        CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν))) := by
      refine Eq.trans ?_ (CoefBasic.cst_eq z _)
      rw [Over.w g.b]
      refine (constVal_specMap (jFK (R := R) F) _ z _).trans ?_
      exact (congrArg (fun q => constVal q z _) (Category.id_comp _).symm).trans (constVal_specMap (𝟙 _) _ z _)
    have c₂ : val (cubB D.toPre (E.h χ) δ) g.b.left z J =
        th D.toPre z J (cP D.toPre _ (E.h χ)) (cP D.toPre _ δ) g.b := by
      refine (val_cub D.toPre.cub g.b hJ _ _ _).trans ?_
      rw [comp_cP, comp_cP, Category.comp_id]
    have c₃ := gt_mul (𝟙 (TF (R := R) F)) hJ g (E.h χ) δ
    have c₄ := hx ν χ z J hJ
    have c₅ := hx' ν δ z J hJ
    have c₆ : g.b.left ≫ E.aB.left = g'.b.left := (congrArg (fun q => q.left) hg.1).symm
    rw [Category.id_comp, Over.id_left] at c₃
    rw [hg.2 χ z J hJ, CoefBasic.cst_eq] at c₄
    rw [CoefBasic.cst_eq] at c₅
    rw [c₁, c₂, c₆, hv z J hJ, map_mul, map_mul, eq_comm, Units.val_mul, ← _root_.mul_assoc, Units.mul_inv_eq_iff_eq_mul]
    have c₇ := congrArg Units.val c₃
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c₄ c₅ c₇ ⊢
    have c₈ := congrArg₂ (· * ·) c₄ c₅
    linear_combination CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν))) * c₈ -
      CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν))) *
        sval (f ν χ) g'.b.left z J * sval (f' ν δ) g.b.left z J * (val (E.u χ) g.b.left z J).val *
        (val w (𝟙 _) z J).val * (val w' (𝟙 _) z J).val * c₇
  · rw [CoefBasic.cst_eq, map_zero, zero_mul]
    exact sval_zero' (π := D.toPre.P.A.hom) hJ _

end Core

section Alg

theorem exists_indep {R F : Type} [CommRing R] [IsDomain R] [Field F] [Algebra (FractionRing R) F] {N : Type}
    [Fintype N] (c : N → F) : ∃ (n : ℕ) (β : Fin n → F) (ρ : Fin n → N → R),
      (∀ a : Fin n → R, ∑ m, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (a m)) * β m = 0 →
        ∀ m, a m = 0) ∧
      ∀ ν, c ν = ∑ m, β m * algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ m ν)) := by
  let V := Submodule.span (FractionRing R) (Set.range c)
  have : FiniteDimensional (FractionRing R) V := FiniteDimensional.span_of_finite _ (Set.finite_range c)
  let b := Module.finBasis (FractionRing R) V
  let v : N → V := fun ν => ⟨c ν, Submodule.subset_span ⟨ν, rfl⟩⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Fin (Module.finrank (FractionRing R) V) × N => b.repr (v p.2) p.1)
  choose ρ hρ using hd
  have d₀ : algebraMap R (FractionRing R) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (nonZeroDivisors.ne_zero d.2)
  refine ⟨_, fun m => (algebraMap R (FractionRing R) d)⁻¹ • (b m : F), fun m ν => ρ (m, ν), fun a ha m => ?_,
    fun ν => ?_⟩
  · have li := Fintype.linearIndependent_iff.1 (b.linearIndependent.map' V.subtype V.ker_subtype)
      (fun m => algebraMap R (FractionRing R) (a m) * (algebraMap R (FractionRing R) d)⁻¹) (by
        refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) ha
        rw [mul_smul, Algebra.smul_def]; rfl) m
    exact IsFractionRing.injective R (FractionRing R)
      (((mul_eq_zero.1 li).resolve_right (inv_ne_zero d₀)).trans (map_zero _).symm)
  · have e := congrArg V.subtype (b.sum_repr (v ν))
    rw [map_sum] at e
    refine e.symm.trans (Finset.sum_congr rfl fun m _ => ?_)
    rw [hρ (m, ν), _root_.mul_comm, ← Algebra.smul_def, ← mul_smul, Algebra.smul_def (d : R), mul_right_comm,
      mul_inv_cancel₀ d₀, _root_.one_mul, map_smul]
    rfl

theorem sumF_comb {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix M : Type} (S : Finset M) (β : M → F) (x : M → Ix → F)
    (h : ∀ m, SumF I F (x m) 0) : SumF I F (fun i => ∑ m ∈ S, β m * x m i) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
    refine ⟨⊥, Submodule.fg_bot, Submodule.zero_mem _, fun i => ?_, fun n => ⟨∅, fun T _ => ?_⟩⟩
    · simp only [Finset.sum_empty]; exact Submodule.zero_mem _
    · simp only [Finset.sum_empty, Finset.sum_const_zero, sub_zero]; exact Submodule.zero_mem _
  | insert a S ha ih =>
    have := (GlobalTheory.AdicSum.sumF_calculus R I hR F Ix _ _ _ _).2.1 (h a) ih (β a)
    simpa only [Finset.sum_insert ha, mul_zero, add_zero] using this

theorem whisker_comm {C : Type*} [Category C] [CartesianMonoidalCategory C] (T : C) {X Y : C} (g : X ⟶ Y) (a : X ⟶ X)
    (b : Y ⟶ Y) (h : a ≫ g = g ≫ b) :
    T ◁ a ≫ lift (fst _ _) (snd _ _ ≫ g) = lift (fst _ _) (snd _ _ ≫ g) ≫ T ◁ b := by
  ext <;> simp [h]

end Alg

section Field
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem cross_at {a : A.A ⟶ A.A} {j j' : ℕ} {t₁ t₂ : SecA A F j} {t₁' t₂' : SecA A F j'} (h : Cross a t₁ t₂ t₁' t₂')
    {Z : Scheme.{0}} (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) {J} (hJ : Good A.L z J) :
    sA t₁ (r ≫ (TFK (R := R) F ◁ a).left) z J * sA t₂' r z J =
      sA t₂ (r ≫ (TFK (R := R) F ◁ a).left) z J * sA t₁' r z J := by
  let P : SecA A F j → SecA A F j' → _ := fun t t' => H1.SectionArithmetic.mulSec (L := A.L) (H1.SectionArithmetic.pullSec (L := A.L)
    (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (j : ℤ)) t (TFK (R := R) F ◁ a).left)
    (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (j' : ℤ)) t'
  have hP : ∀ t t' {Z : Scheme.{0}} (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) {J}, Good A.L z J →
      sval (P t t') r z J = sA t (r ≫ (TFK (R := R) F ◁ a).left) z J * sA t' r z J := fun t t' Z r z J hJ =>
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ) rfl)
  have e : P t₁ t₂' = P t₂ t₁' := sec_ext' A.isLB fun y J hJ => by
    rw [hP _ _ _ y hJ, hP _ _ _ y hJ, Category.id_comp]; exact h y J hJ
  rw [← hP _ _ r z hJ, ← hP _ _ r z hJ, e]

def endF (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (UnifPre.GF (G := G) F).left ⟶ (UnifPre.GF (G := G) F).left :=
  (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left

def strF (G : Over (Spec (CommRingCat.of R))) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (UnifPre.GF (G := G) F).left ⟶ Spec (CommRingCat.of F) :=
  (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left

theorem endF_str : endF E F ≫ strF G F = strF G F :=
  congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) ((Over.pullback (jK R)).map E.aG))

theorem endF_gFK : endF E F ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G) F ≫ E.aG.left := by
  have h₁ := congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) ((Over.pullback (jK R)).map E.aG))
  have h₂ : ((Over.pullback (jK R)).map E.aG).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ E.aG.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom (jK R)) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

theorem endF_genF : endF E F ≫ (U.genF F).left = (U.genF F).left ≫ (TFK (R := R) F ◁ E.aA).left :=
  congrArg (fun q => q.left) (whisker_comm (TFK (R := R) F) U.gen.hom _ _ E.ext)

abbrev Carried (w₀ : W0 U) (k : ℕ) (t : SecA A F k) (σ : U.SecGF F k) : Prop :=
  GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
    (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ

theorem cross_G {w₀ : W0 U} {j j' : ℕ} {t₁ t₂ : SecA A F j} {t₁' t₂' : SecA A F j'} {σ₁ σ₂ : U.SecGF F j}
    {σ₁' σ₂' : U.SecGF F j'} (h₁ : Carried w₀ j t₁ σ₁) (h₂ : Carried w₀ j t₂ σ₂) (h₁' : Carried w₀ j' t₁' σ₁')
    (h₂' : Carried w₀ j' t₂' σ₂') (h : Cross E.aA t₁ t₂ t₁' t₂') (y : (UnifPre.GF (G := G) F).left) {J}
    (hJ : Good U.LG.L y J) : sval σ₁ (endF E F) y J * sval σ₂' (𝟙 _) y J =
      sval σ₂ (endF E F) y J * sval σ₁' (𝟙 _) y J := by
  obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' A.isLB y
  have a₁ := GlobalTheory.BoxExpansion.isoRel_val h₁ (endF E F) y hJ' hJ
  have a₂ := GlobalTheory.BoxExpansion.isoRel_val h₂ (endF E F) y hJ' hJ
  have a₃ := GlobalTheory.BoxExpansion.isoRel_val h₁' (𝟙 _) y hJ' hJ
  have a₄ := GlobalTheory.BoxExpansion.isoRel_val h₂' (𝟙 _) y hJ' hJ
  have a₅ := cross_at h (U.genF F).left y hJ'
  rw [Category.comp_id, endF_genF] at a₁ a₂
  rw [Category.comp_id, Category.id_comp (U.genF F).left] at a₃ a₄
  rw [a₁, a₂, a₃, a₄]
  exact (_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg (_ * ·) a₅).trans (_root_.mul_mul_mul_comm _ _ _ _))

theorem val_secLin {k n : ℕ} {σ₀ : U.SecGF F k} {σ : Fin n → H0 U.LG.L k} {c : Fin n → F}
    (h : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)))
    (r : (UnifPre.GF (G := G) F).left ⟶ (UnifPre.GF (G := G) F).left) (hr : r ≫ strF G F = strF G F)
    (y : (UnifPre.GF (G := G) F).left) {J} (hJ : Good U.LG.L y J) :
    sval σ₀ r y J = ∑ i, GlobalTheory.BoxExpansion.constHomVal (strF G F) y (c i) *
      sval (σ i) (r ≫ UnifPre.gFK (G := G) F) y J :=
  (GlobalTheory.BoxExpansion.secLin_val h r y hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _)
    ((gs_scal (strF G F) r y _).trans ((congrArg (fun q => constVal q y (c i)) hr).trans
      (GlobalTheory.BoxExpansion.constVal_eq _ _ _))))

omit [GrpObj G] [IsCommMonObj G] in
theorem isPullback_GF : IsPullback (UnifPre.gFK (G := G) F) (strF G F) G.hom (Spec.map (CommRingCat.ofHom
    ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  exact (IsPullback.of_hasPullback (TFK (R := R) F).hom ((Over.pullback (jK R)).obj G).hom).flip.paste_horiz
    (IsPullback.of_hasPullback G.hom (jK R))

theorem coreF [CharZero R] [IsAlgClosed F] (hL : LL) (hR : AdmBase R I) (j j' : ℕ) {N : Type} [Fintype N] (c : N → F)
    (σ : N → H0 U.LG.L j) (σ' : N → H0 U.LG.L j')
    (f : N → ∀ α : D.toPre.X, D.toPre.SecB j α) (f' : N → ∀ α : D.toPre.X, D.toPre.SecB j' α)
    (hE : ∀ ν e, U.ExpandsAt e j (σ ν) (f ν)) (hE' : ∀ ν e, U.ExpandsAt e j' (σ' ν) (f' ν))
    (hrel : ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J →
      ∑ ν, GlobalTheory.BoxExpansion.constHomVal (strF G F) y (c ν) *
        (sval (σ ν) (UnifPre.gFK (G := G) F ≫ E.aG.left) y J * sval (σ' ν) (UnifPre.gFK (G := G) F) y J) = 0)
    (g g' : GtPtF D.toPre F) (hg : E.Act g g') (w : Frm D.toPre F j g'.b) (w' : Frm D.toPre F j' g.b)
    (hw : w.IsGen) (hw' : w'.IsGen) (x x' : N → D.toPre.X → F)
    (hx : ∀ ν χ, IsCoefB j g' w χ (f ν χ) (x ν χ)) (hx' : ∀ ν χ, IsCoefB j' g w' χ (f' ν χ) (x' ν χ))
    (α : D.toPre.X) :
    SumF I F (fun p : {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α} =>
      ∑ ν, c ν * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  obtain ⟨n, β, ρ, hβ, hc⟩ := exists_indep (R := R) c
  let d : Fin n → SecOver G.hom (LB.LinComb U.LG.L (Sum.elim (fun _ : Fin 1 => E.aG.left ≫ 𝟙 G.left)
      (fun _ : Fin 1 => 𝟙 G.left)) (Sum.elim (fun _ => (j : ℤ)) (fun _ => (j' : ℤ)))) := fun m =>
    ∑ ν, ρ m ν • (show SecOver G.hom _ from H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec (σ ν) E.aG.left) (σ' ν))
  have hd : ∀ m (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval (d m) r z J =
      ∑ ν, constVal (r ≫ G.hom) z (ρ m ν) * (sval (σ ν) (r ≫ E.aG.left) z J * sval (σ' ν) r z J) :=
    fun m Z r z J hJ => (sval_sum' (π := G.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
      (sval_smul' (π := G.hom) hJ _ _ _).trans (congrArg _ ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans
        (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ) rfl))))
  have := U.smooth
  have h₀ := GlobalTheory.T.sval_eq_zero_of_linearIndependent_comb R F _ _ _ _ G.hom (strF G F) _ isPullback_GF U.LG.L U.LG.isLB _ _ _ _ β hβ d
    (fun y J hJ => by
      refine Eq.trans ?_ (hrel y J hJ)
      simp only [hd _ _ _ y J hJ, hc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => ?_
      rw [(isPullback_GF (G := G) (F := F)).w, constVal_specMap, GlobalTheory.BoxExpansion.constVal_eq,
        GlobalTheory.BoxExpansion.constVal_eq, _root_.mul_assoc]
      rfl)
  have h₁ := sumF_comb hR Finset.univ β _ fun m => core E hL hR j j' (ρ m) σ σ' f f' hE hE'
    (fun Z r z J hJ => (hd m Z r z J hJ).symm.trans (h₀ m Z r z J hJ)) g g' hg w w' hw hw' x x' hx hx' α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp h₁
  simp only [hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => (_root_.mul_assoc _ _ _).symm

end Field

theorem sumF_conv_of_cross : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A F j) (t₁' t₂' : SecA A F j') s₁ s₂ s₁' s₂', U.ExpandsF F j w₀ t₁ s₁ → U.ExpandsF F j w₀ t₂ s₂ → U.ExpandsF F j' w₀ t₁' s₁' → U.ExpandsF F j' w₀ t₂' s₂' → Cross E.aA t₁ t₂ t₁' t₂' → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w : Frm D.toPre F j g'.b) (w' : Frm D.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  intro hL R _ _ _ I hR D A G _ _ _ U F _ _ _ E w₀ _ j j' _ _ t₁ t₂ t₁' t₂' s₁ s₂ s₁' s₂' H₁ H₂ H₁' H₂' hC g g' hg
    w w' hw hw' α
  obtain ⟨τ₁, r₁, n₁, c₁, σ₁, f₁, e₁, l₁, b₁⟩ := H₁
  obtain ⟨τ₂, r₂, n₂, c₂, σ₂, f₂, e₂, l₂, b₂⟩ := H₂
  obtain ⟨τ₁', r₁', n₁', c₁', σ₁', f₁', e₁', l₁', b₁'⟩ := H₁'
  obtain ⟨τ₂', r₂', n₂', c₂', σ₂', f₂', e₂', l₂', b₂'⟩ := H₂'
  choose x₁ hx₁ using fun i χ => exists_isCoefB g' hw χ (f₁ i χ)
  choose x₂ hx₂ using fun i χ => exists_isCoefB g' hw χ (f₂ i χ)
  choose x₁' hx₁' using fun i χ => exists_isCoefB g hw' χ (f₁' i χ)
  choose x₂' hx₂' using fun i χ => exists_isCoefB g hw' χ (f₂' i χ)
  have key := coreF E hL hR j j' (N := (Fin n₁ × Fin n₂') ⊕ (Fin n₂ × Fin n₁'))
    (Sum.elim (fun p => c₁ p.1 * c₂' p.2) (fun p => -(c₂ p.1 * c₁' p.2)))
    (Sum.elim (fun p => σ₁ p.1) (fun p => σ₂ p.1)) (Sum.elim (fun p => σ₂' p.2) (fun p => σ₁' p.2))
    (Sum.elim (fun p => f₁ p.1) (fun p => f₂ p.1)) (Sum.elim (fun p => f₂' p.2) (fun p => f₁' p.2))
    (by rintro (p | p); exacts [e₁ p.1, e₂ p.1]) (by rintro (p | p); exacts [e₂' p.2, e₁' p.2])
    (fun y J hJ => by
      have h := cross_G E r₁ r₂ r₁' r₂' hC y hJ
      rw [val_secLin l₁ _ (endF_str E) y hJ, val_secLin l₂ _ (endF_str E) y hJ,
        val_secLin l₁' _ (Category.id_comp _) y hJ, val_secLin l₂' _ (Category.id_comp _) y hJ, endF_gFK,
        Category.id_comp, Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero] at h
      refine Eq.trans ?_ h
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, map_neg, map_mul,
        neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
      exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
        (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _))
    g g' hg w w' hw hw' (Sum.elim (fun p => x₁ p.1) (fun p => x₂ p.1))
    (Sum.elim (fun p => x₂' p.2) (fun p => x₁' p.2))
    (by rintro (p | p); exacts [hx₁ p.1, hx₂ p.1]) (by rintro (p | p); exacts [hx₂' p.2, hx₁' p.2]) α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp key
  rw [coef_of_secLin (b₁ _) (fun i => hx₁ i _), coef_of_secLin (b₂ _) (fun i => hx₂ i _),
    coef_of_secLin (b₁' _) (fun i => hx₁' i _), coef_of_secLin (b₂' _) (fun i => hx₂' i _),
    Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
    (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)

end GlobalTheory.UT.MixedConv
end
