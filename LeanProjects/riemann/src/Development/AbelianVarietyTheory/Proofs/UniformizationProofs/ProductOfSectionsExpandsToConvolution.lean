import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSubSum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickeningsStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ProdConv
open GlobalTheory.FieldBaseChange

section Prod

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem prod_famB {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (α : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ D.famφB α i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (cP D T α * ρ).left * (h (cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e₀ : ρ.left ≫ D.famφB α 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ D.famφB α 1 = (cP D T α * ρ).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 _) (cP D _ α)).trans (by rw [comp_cP, Category.comp_id, mul_comm]))
  have e₂ : ρ.left ≫ D.famφB α 2 = (cP D T α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

def IsProd (r : R) {k l m : ℕ} {β ga α : D.X} (a : D.SecB k β) (b : D.SecB l ga) (c : D.SecB m α) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    sval c ρ.left z J = constVal T.hom z r *
      (sval a ρ.left z J * sval b ρ.left z J * (th D z J (cP D T β) (cP D T ga) ρ).val)

theorem exists_isProd (r : R) (k l : ℕ) {β ga α : D.X} (hα : β + ga = α) (f : D.SecB k β) (g : D.SecB l ga) :
    ∃ h : D.SecB (k + l) α, IsProd r f g h := by
  subst hα
  let a : D.P.A ⟶ D.P.A := cP D _ β
  let b : D.P.A ⟶ D.P.A := cP D _ ga
  have hu := pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift b (𝟙 D.P.A))).left
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := D.famφB (β + ga)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      have p₁ := prod_cub a b (𝟙 D.P.A) h
      have p₂ := prod_famB (𝟙 D.P.A) β k h
      have p₃ := prod_famB (𝟙 D.P.A) ga l h
      have p₄ := prod_famB (𝟙 D.P.A) (β + ga) (k + l) h
      rw [cPoint_add] at p₄
      simp only [Over.id_left, Category.id_comp] at p₁ p₂ p₃ p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₂ p₃) p₁) (Eq.trans ?_ p₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, b]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (Geo.Tor.genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift a (lift b (𝟙 D.P.A))).left) hu))
  refine ⟨(r • (show SecOver D.P.A.hom _ from t) : SecOver D.P.A.hom _), fun T ρ z J hJ => ?_⟩
  refine (sval_smul' hJ ρ.left r _).trans (congrArg₂ (· * ·) (by rw [Over.w]) ?_)
  refine (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val
      ((val_cub D.cub ρ hJ a b (𝟙 _)).trans ?_)))))
  rw [comp_cP, comp_cP, Category.comp_id]

variable {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem prod_mul_coord {e : ℕ} (g : GtCoord I D e G) {r : R} {k l m : ℕ} {β ga α : D.X}
    (hα : β + ga = α) {a : D.SecB k β} {b : D.SecB l ga} {c : D.SecB m α} (H : IsProd r a b c) {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval c (x ≫ g.pG.left) z J * (val (g.t α) x z J).val = constVal (x ≫ g.pG.left ≫ D.P.A.hom) z r *
      (sval a (x ≫ g.pG.left) z J * (val (g.t β) x z J).val *
        (sval b (x ≫ g.pG.left) z J * (val (g.t ga) x z J).val)) := by
  subst hα
  let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (x ≫ g.pG.left ≫ D.P.A.hom)
  let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (congrArg (x ≫ ·) (Over.w g.pG).symm)
  have h₁ := H FinalForm (xo ≫ g.pG) z J hJ
  have h₂ := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.t_mul β ga) x).trans (val_mul hJ _ _ _))
  have h₃ := val_cub D.cub xo (z := z) hJ (cP D _ β) (cP D _ ga) g.pG
  rw [comp_cP, comp_cP] at h₃
  have h₅ := congrArg Units.val ((congrArg (val (g.t (β + ga)) x z J * ·) h₃).symm.trans h₂)
  rw [Units.val_mul, Units.val_mul] at h₅
  refine (congrArg (· * (val (g.t (β + ga)) x z J).val) h₁).trans ?_
  rw [_root_.mul_mul_mul_comm, ← h₅]
  exact (_root_.mul_assoc _ _ _).trans (congrArg _ ((_root_.mul_assoc _ _ _).trans (congrArg _ (mul_comm _ _))))

end Prod

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem level (e : ℕ) {k l m : ℕ} (r : R) {σ : H0 U.LG.L k} {σ' : H0 U.LG.L l} {σ'' : H0 U.LG.L m} (hm : m = k + l)
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D.toPre.SecB l α} {f'' : ∀ α, D.toPre.SecB m α}
    (h : U.ExpandsAt e k σ f) (h' : U.ExpandsAt e l σ' f') (h'' : U.ExpandsAt e m σ'' f'')
    (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ G.left) (z : Z) (j), q z ∈ U.LG.L.U j →
      sv U m σ'' q z j = constVal (q ≫ G.hom) z r * (sv U k σ q z j * sv U l σ' q z j))
    (p : ∀ α (_ : D.toPre.X), D.toPre.SecB m α) (hp : ∀ α β, IsProd r (f β) (f' (α - β)) (p α β)) (α₀ : D.toPre.X) :
    ∃ S : Finset D.toPre.X, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J),
      Good D.toPre.P.L z J → (∀ i ∉ S, sval (p α₀ i) (x ≫ (D.toPre.prBe I e).left) z J = 0) ∧
        sval (f'' α₀) (x ≫ (D.toPre.prBe I e).left) z J =
          ∑ i ∈ S, sval (p α₀ i) (x ≫ (D.toPre.prBe I e).left) z J := by
  classical
  obtain ⟨s, hs⟩ := expandsAt_val U e k σ f h
  obtain ⟨s', hs'⟩ := expandsAt_val U e l σ' f' h'
  obtain ⟨s'', hs''⟩ := expandsAt_val U e m σ'' f'' h''
  have hπ : fGl I G e ≫ G.hom = pGl U e ≫ D.toPre.P.A.hom := (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      ∑ α ∈ s'', sval (f'' α) (x ≫ pGl U e) z J * (val (tG U e α) x z J).val =
        constVal (x ≫ pGl U e ≫ D.toPre.P.A.hom) z r *
        ((∑ α ∈ s, sval (f α) (x ≫ pGl U e) z J * (val (tG U e α) x z J).val) *
          ∑ α ∈ s', sval (f' α) (x ≫ pGl U e) z J * (val (tG U e α) x z J).val) := by
    intro Z x z J hJ
    obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (fGl I G e (x z))
    rw [← (hs Z x z J hJ).2 j hj, ← (hs' Z x z J hJ).2 j hj, ← (hs'' Z x z J hJ).2 j hj,
      hσ Z (x ≫ fGl I G e) z j hj, Category.assoc, hπ, hm, pow_add, Units.val_mul]
    ring
  choose d hd using fun α => ConvOfProd.exists_sub_sum (f'' α) (p α) s
  let S : Finset D.toPre.X := insert α₀ (s'' ∪ Finset.image₂ (· + ·) s s')
  have hd0 := GlobalTheory.sval_eq_zero_of_sum_mul_coord R I D.toPre e G (U.gt e) D.toPre.P.A (𝟙 _) (Fin 4)
    D.toPre.famφB (DegPre.famε m) d S (fun Z x ρ hr z J hJ => by
      obtain rfl : ρ = x ≫ pGl U e := (Category.comp_id ρ).symm.trans hr
      have c := ConvOfProd.sum_conv s s' S (fun β => sval (f β) (x ≫ pGl U e) z J * (val (tG U e β) x z J).val)
        (fun β => sval (f' β) (x ≫ pGl U e) z J * (val (tG U e β) x z J).val)
        (fun v hv => by rw [(hs' Z x z J hJ).1 v hv, zero_mul])
        (fun β hβ v hv => Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hβ hv)))
      have c' : ∑ α ∈ s'', sval (f'' α) (x ≫ pGl U e) z J * (val (tG U e α) x z J).val =
          ∑ α ∈ S, sval (f'' α) (x ≫ pGl U e) z J * (val (tG U e α) x z J).val :=
        Finset.sum_subset (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
          (fun a _ ha => by rw [(hs'' Z x z J hJ).1 a ha, zero_mul])
      have k₄ := key Z x z J hJ
      rw [← c, c', Finset.mul_sum] at k₄
      rw [← sub_eq_zero.2 k₄, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hd α Z _ z J hJ, sub_mul, Finset.sum_mul, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun β _ =>
        prod_mul_coord (U.gt e) (add_sub_cancel β α) (hp α β) x z J hJ)) α₀ (Finset.mem_insert_self _ _)
  refine ⟨s, fun Z x z J hJ => ?_⟩
  have hl : ∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
      ρ ≫ thick R I e = (x ≫ (D.toPre.prBe I e).left) ≫ D.toPre.P.A.hom :=
    ⟨x ≫ (thickObj R I e D.toPre.P.A).hom, by
      rw [Category.assoc, Category.assoc, Over.w (D.toPre.prBe I e)]; rfl⟩
  refine ⟨fun β hβ => ?_, ?_⟩
  · refine GlobalTheory.LiftTest.main R I D.toPre e G (U.gt e) D.toPre.P.A (𝟙 _) _ D.toPre.P.L D.toPre.P.isLB _ _ _ (p α₀ β)
      (fun Z x ρ hr z J hJ => ?_) Z _ hl z J hJ
    obtain rfl : ρ = x ≫ pGl U e := (Category.comp_id ρ).symm.trans hr
    have c := prod_mul_coord (U.gt e) (add_sub_cancel β α₀) (hp α₀ β) x z J hJ
    rw [(hs Z x z J hJ).1 β hβ, zero_mul, zero_mul, mul_zero] at c
    exact (Units.mul_left_eq_zero _).1 c
  · have c := GlobalTheory.LiftTest.main R I D.toPre e G (U.gt e) D.toPre.P.A (𝟙 _) _ D.toPre.P.L D.toPre.P.isLB _ _ _ (d α₀)
      hd0 Z _ hl z J hJ
    rw [hd α₀ Z _ z J hJ] at c
    exact sub_eq_zero.1 c

section Point

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

def IsTerm {D : DegPre R} {k : ℕ} (g : GtPtF D F) (w : Frm D F k g.b) {χ : D.X} (f : D.SecB k χ) (x : F) : Prop :=
  ∀ (z : (TF (R := R) F).left) (J), Good D.P.L z J →
    cst F z x * (rigV D (TF (R := R) F).hom z J).val ^ k =
      sval f g.b.left z J * (val (g.s χ) (𝟙 _) z J).val * (val w (𝟙 _) z J).val

theorem exists_frame {D : DegPre R} {m : ℕ} (g : GtPtF D F) {w : Frm D F m g.b} (hw : w.IsGen) (α : D.X) :
    ∃ τ : LB.Gen (LB.LinComb D.P.L (fun i => g.b.left ≫ D.famφB α i) (DegPre.famε m)), τ.IsGen ∧
      ∀ z J, Good D.P.L z J → val τ (𝟙 _) z J =
        rigV D (TF (R := R) F).hom z J ^ m * (val (g.s α) (𝟙 _) z J)⁻¹ * (val w (𝟙 _) z J)⁻¹ := by
  obtain ⟨τ, hτ, vτ⟩ := exists_gen D.P.isLB (φ' := fun i => g.b.left ≫ D.famφB α i) (ε' := DegPre.famε m)
    (fun U _ h => by
      have p₁ : ∏ i : PUnit, h ((TF (R := R) F).hom ≫ eSec D.P.A) ^ ((m : ℤ) * 1) =
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ (m : ℤ) := by
        rw [Fintype.prod_unique, _root_.mul_one]; rfl
      refine Eq.trans (prod_sum₂ (K := PUnit ⊕ Fin 4) (K' := Fin 2) (U := U) _
        (prod_sum₂ (K := PUnit) (K' := Fin 4) (U := U) _ p₁ (prod_neg _ _ (prod_gt g.b α h)))
        (prod_neg _ _ (CoefBasic.prod_line m g.b h))) (Eq.trans ?_ (prod_famB g.b α m h).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _
      (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (TF (R := R) F).hom) m)
      (LB.invGen D.P.L _ _ (g.s α))) (LB.invGen D.P.L _ _ w))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) _)
      (invGen_isGen _ _ _ _ (g.isGen α))) (invGen_isGen _ _ _ _ hw))
  refine ⟨τ, hτ, fun z J hJ => (vτ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((map_pow _ _ _).trans (congrArg (· ^ m)
      ((val_pull hJ _ _ _).trans ?_))) (val_inv _ _))) (val_inv _ _)))⟩
  rw [Category.id_comp]; rfl

omit [IsDomain R] in
theorem constVal_TF [IsDomain R] (z : (TF (R := R) F).left) (r : R) :
    constVal (TF (R := R) F).hom z r = cst F z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) := by
  refine (constVal_specMap (jFK (R := R) F) (algebraMap R (FractionRing R)) z r).trans ?_
  refine Eq.trans ?_ (constVal_specMap (𝟙 (Spec (CommRingCat.of F))) (algebraMap (FractionRing R) F) z _)
  rw [Category.id_comp]

theorem alg_term {S : Type} [CommRing S] {x f : S} {ρ a w : Sˣ} {m : ℕ} (h : x * ρ.val ^ m = f * a.val * w.val) :
    f = x * (ρ ^ m * a⁻¹ * w⁻¹).val := by
  refine (w * a).mul_left_inj.1 ?_
  rw [_root_.mul_assoc, ← Units.val_mul, ← _root_.mul_assoc (ρ ^ m * a⁻¹ * w⁻¹), inv_mul_cancel_right,
    inv_mul_cancel_right, Units.val_pow_eq_pow_val, h, Units.val_mul]
  ring

theorem alg_prod {S : Type} [CommRing S] (c : S) {x x' f f' : S} {ρ a a' a'' w w' θ : Sˣ} {k l : ℕ}
    (h : x * ρ.val ^ k = f * a.val * w.val) (h' : x' * ρ.val ^ l = f' * a'.val * w'.val) (b : a'' * θ = a * a') :
    c * (f * f' * θ.val) = c * (x * x') * (ρ ^ (k + l) * a''⁻¹ * (w * w')⁻¹).val := by
  refine alg_term ?_
  have b' := congrArg Units.val b
  rw [Units.val_mul, Units.val_mul] at b'
  rw [Units.val_mul, pow_add]
  linear_combination c * x' * ρ.val ^ l * h + c * (f * a.val * w.val) * h' - c * f * f' * w.val * w'.val * b'

theorem point [CharZero R] [IsAlgClosed F] (hL : LL) (hR : AdmBase R I) {k l m : ℕ} (r : R) {σ : H0 U.LG.L k}
    {σ' : H0 U.LG.L l} {σ'' : H0 U.LG.L m} (hm : m = k + l)
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D.toPre.SecB l α} {f'' : ∀ α, D.toPre.SecB m α}
    (h : ∀ e, U.ExpandsAt e k σ f) (h' : ∀ e, U.ExpandsAt e l σ' f') (h'' : ∀ e, U.ExpandsAt e m σ'' f'')
    (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ G.left) (z : Z) (j), q z ∈ U.LG.L.U j →
      sv U m σ'' q z j = constVal (q ≫ G.hom) z r * (sv U k σ q z j * sv U l σ' q z j))
    (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} {w' : Frm D.toPre F l g.b} {w'' : Frm D.toPre F m g.b}
    (hw : w''.IsGen) (hww : ∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J)
    {x x' : D.toPre.X → F} (hx : ∀ χ, IsTerm g w (f χ) (x χ)) (hx' : ∀ χ, IsTerm g w' (f' χ) (x' χ))
    (α : D.toPre.X) {x'' : F} (hx'' : IsTerm g w'' (f'' α) x'') :
    SumF I F (fun χ => algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) * (x χ * x' (α - χ))) x'' := by
  subst hm
  choose p hp using fun α β => exists_isProd r k l (add_sub_cancel β α) (f β) (f' (α - β))
  obtain ⟨τ, hτ, vτ⟩ := exists_frame g hw α
  refine GlobalTheory.T.adicSum_sections_of_finite_sums_on_thickenings hL R I hR D F (Fin 4) (D.toPre.famφB α) (DegPre.famε (k + l)) D.toPre.X (p α) (f'' α)
    (fun e => level U e r rfl (h e) (h' e) (h'' e) hσ p hp α) g.b τ hτ _ _ fun z J hJ => ⟨fun χ => ?_, ?_⟩
  · have b := gt_mul (𝟙 (TF (R := R) F)) hJ g χ (α - χ)
    rw [add_sub_cancel, Category.id_comp, Over.id_left] at b
    rw [hp α χ _ g.b z J hJ, vτ z J hJ, constVal_TF, hww z J hJ, CoefBasic.cst_eq z (_ * _), map_mul, map_mul,
      ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]
    exact alg_prod _ (hx χ z J hJ) (hx' (α - χ) z J hJ) b
  · rw [vτ z J hJ]
    exact alg_term (hx'' z J hJ)

end Point

theorem exists_powMul {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {q : Y ⟶ X} {k l m : ℕ} (hm : m = k + l)
    (a : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => (k : ℤ))))
    (b : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => (l : ℤ)))) :
    ∃ c : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => (m : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i), q (r z) ∈ L.U i → powVal c r z i = powVal a r z i * powVal b r z i := by
  obtain ⟨c, hc⟩ := exists_sec hL (K' := Fin 1) (φ' := fun _ => q) (ε' := fun _ => (m : ℤ)) (fun U _ h => by
    refine (prod_sum₂ (K := Fin 1) (K' := Fin 1) (U := U) _ (Fin.prod_univ_one _) (Fin.prod_univ_one _)).trans
      (Eq.trans ?_ (Fin.prod_univ_one _).symm)
    rw [hm, Nat.cast_add, zpow_add]; rfl) (H1.SectionArithmetic.mulSec a b)
  refine ⟨c, fun Z r z i hi => ?_⟩
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun _ : PUnit => r ≫ q) (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  obtain rfl : J (r ≫ q) = i := e PUnit.unit
  exact (hc Z r z J hJ).trans (H1.SectionArithmetic.sval_mulSec a b r z hJ)

theorem genericSec_injective (k : ℕ) : Function.Injective (genericSec U k) := by
  have := U.smooth
  have hd : IsDominant (jK R) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)
  have : IsSchemeTheoreticallyDominant (jK R) := .of_isDominant _
  intro a b e
  refine SecOver.ext _ _ fun j => Scheme.Hom.app_injective (pullback.fst G.hom (jK R)) _ (fn_ext fun y hy => ?_)
  have hy' := (wchart_eq (L := U.LG.L) (φ := fun _ : Fin 1 => 𝟙 G.left) (p := pullback.fst G.hom (jK R))
    (fun _ => (Category.comp_id _).symm) j).ge hy
  have v : ∀ s : IntSec U k, gs (𝟙 _) y _ (LB.Sec.f (genericSec U k s) j) =
      gs (𝟙 _) y _ (((pullback.fst G.hom (jK R)).app _).hom (LB.Sec.f s j)) := fun s =>
    (gs_pullFn _ _ _ (𝟙 _) y hy').trans (gs_pull (𝟙 _) _ y _ hy _).symm
  exact (v a).symm.trans ((congrArg (fun s : U.SecK k => gs (𝟙 _) y _ (LB.Sec.f s j)) e).trans (v b))

section Global

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem expandsG_of_fintype {κ : Type} [Fintype κ] (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) (c : κ → F)
    (x : κ → IntSec U k × ∀ α, IntTerm D k α) (hx : ∀ i, x i ∈ expansionPairs U k)
    (h₁ : v = ∑ i, c i • extendSec U F k (genericSec U k (x i).1))
    (h₂ : ∀ α, famProj D.toPre F k α s =
      ∑ i, c i • termPull D.toPre (FractionRing R) F k α (genericTerm D k α ((x i).2 α))) : U.ExpandsG F k v s := by
  let e := (Fintype.equivFin κ).symm
  refine (expandsG_iff U F k v s).2 ⟨_, fun i => c (e i), fun i => x (e i), fun i => hx _, h₁.trans ?_,
    fun α => (h₂ α).trans ?_⟩
  · exact (e.sum_comp fun i => c i • extendSec U F k (genericSec U k (x i).1)).symm
  · exact (e.sum_comp fun i => c i • termPull D.toPre (FractionRing R) F k α (genericTerm D k α ((x i).2 α))).symm

variable {F}

theorem sval_termPull {k : ℕ} {α : D.toPre.X} (f : IntTerm D k α) (b : TF (R := R) F ⟶ D.toPre.P.A)
    {z : (TF (R := R) F).left} {J} (hJ : Good D.toPre.P.L z J) :
    sval (termPull D.toPre (FractionRing R) F k α (genericTerm D k α f)) (lift (𝟙 (TF (R := R) F)) b).left z J =
      sval f b.left z J := by
  refine (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans (congrArg (fun q => sval f q z J) ?_))
  rw [← Over.comp_left, ← Over.comp_left, Category.assoc, famMap_snd, lift_snd]

theorem exists_isTerm {k : ℕ} (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} (hw : w.IsGen) {χ : D.toPre.X}
    (f : IntTerm D k χ) : ∃ x, IsTerm g w f x := by
  obtain ⟨x, hx⟩ := CoefBasic.exists_isCoef g hw χ (termPull D.toPre (FractionRing R) F k χ (genericTerm D k χ f))
  exact ⟨x, fun z J hJ => (hx z J hJ).trans (by rw [sval_termPull f g.b hJ])⟩

theorem coef_eq_sum {κ : Type} [Fintype κ] {k : ℕ} (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} {χ : D.toPre.X}
    {s : Fam D.toPre F k} {c x : κ → F} {f : κ → IntTerm D k χ} (hx : ∀ i, IsTerm g w (f i) (x i))
    (h : famProj D.toPre F k χ s = ∑ i, c i • termPull D.toPre (FractionRing R) F k χ (genericTerm D k χ (f i))) :
    coef s g w χ = ∑ i, c i * x i := by
  refine CoefBasic.coef_eq fun z J hJ => ?_
  have e : (lift (𝟙 (TF (R := R) F)) g.b).left ≫ famBase D.toPre F = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) g.b)
  have e₁ := (congrArg (fun q => sval q (lift (𝟙 (TF (R := R) F)) g.b).left z J) h).trans (sval_sum' hJ _ _ _)
  refine Eq.trans ?_ (congrArg (fun q => q * _ * _) e₁).symm
  rw [CoefBasic.cst_eq, map_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_smul' hJ, sval_termPull (f i) g.b hJ, e, map_mul, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, _root_.mul_assoc,
    hx i z J hJ, ← _root_.mul_assoc, ← _root_.mul_assoc]
  rfl

theorem powVal_comb {κ : Type} [Fintype κ] {k : ℕ} (c : κ → F) (σ : κ → IntSec U k) (y : (UnifPre.GF (G := G) F).left)
    {i : U.LG.L.ι} (hi : UnifPre.gFK (G := G) F y ∈ U.LG.L.U i) :
    powVal (∑ p, c p • extendSec U F k (genericSec U k (σ p)) : GroupSec U F k) (𝟙 _) y i =
      ∑ p, constVal (groupBase G F) y (c p) * powVal (σ p) (UnifPre.gFK (G := G) F) y i := by
  obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB y (fun _ : PUnit => UnifPre.gFK (G := G) F) (fun _ => i)
    (fun _ _ _ => rfl) (fun _ => hi)
  obtain rfl : J (UnifPre.gFK (G := G) F) = i := e PUnit.unit
  have e₁ := sval_sum' hJ (𝟙 _) Finset.univ (fun p => (c p • extendSec U F k (genericSec U k (σ p)) : GroupSec U F k))
  refine Eq.trans (congrArg (fun q => powVal _ (𝟙 _) y (J q)) (Category.id_comp _).symm)
    (e₁.trans (Finset.sum_congr rfl fun p _ => ?_))
  have e₂ : sval (extendSec U F k (genericSec U k (σ p))) (𝟙 _) y J = sval (σ p) (UnifPre.gFK (G := G) F) y J :=
    (sval_pullOver _ _ _ (𝟙 _) hJ).trans ((sval_pullOver _ _ (σ p) _ hJ).trans (by rw [Category.id_comp]))
  exact (sval_smul' hJ _ _ _).trans (congrArg₂ (· * ·) (by rw [Category.id_comp])
    (e₂.trans (congrArg (fun q => powVal (σ p) _ y (J q)) (Category.comp_id _))))

omit [IsDomain R] in
theorem sumF_zero [IsDomain R] {Ix : Type} : SumF I F (fun _ : Ix => (0 : F)) 0 := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  exact ⟨⊥, Submodule.fg_bot, zero_mem _, fun _ => zero_mem _, fun n => ⟨∅, fun T _ => by simp⟩⟩

theorem sumF_sum (hR : AdmBase R I) {κ Ix : Type} (S : Finset κ) (c : κ → F) {x : κ → Ix → F} {s : κ → F}
    (h : ∀ p, SumF I F (x p) (s p)) : SumF I F (fun i => ∑ p ∈ S, c p * x p i) (∑ p ∈ S, c p * s p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using sumF_zero
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (GlobalTheory.AdicSum.sumF_calculus R I hR F Ix _ _ _ _).2.1 (h a) ih (c a)

end Global

theorem main : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k k' k'' : ℕ), 1 ≤ k → 1 ≤ k' → k'' = k + k' → ∀ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F k'') s s' s'', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → U.ExpandsF F k'' w₀ t'' s'' → (∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J) → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) (w' : Frm D.toPre F k' g.b) (w'' : Frm D.toPre F k'' g.b), w.IsGen → w'.IsGen → w''.IsGen → (∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J) → ∀ α, SumF I F (fun χ => coef s g w χ * coef s' g w' (α - χ)) (coef s'' g w'' α) := by
  intro hL R _ _ _ I hR D A G _ _ _ U F _ _ _ w₀ hw₀ k k' k'' hk hk' hm t t' t'' s s' s'' h h' h'' ht g w w' w'' hw hw' hw''
    hww α
  have hG := hL.1.globalFns
  have hk'' : 1 ≤ k'' := by omega
  obtain ⟨v, a, b⟩ := h
  obtain ⟨v', a', b'⟩ := h'
  obtain ⟨v'', a'', b''⟩ := h''
  obtain ⟨n, c, x, hx, e₁, e₂⟩ := (expandsG_iff U.toUnifPre F k v s).1 b
  obtain ⟨n', c', x', hx', e₁', e₂'⟩ := (expandsG_iff U.toUnifPre F k' v' s').1 b'
  obtain ⟨u, hu⟩ := exists_powMul A.isLB (q := (snd (TFK (R := R) F) A.A).left) hm t t'
  obtain rfl : t'' = u := sec_ext' A.isLB fun y J hJ => (ht y J hJ).trans (hu _ (𝟙 _) y _ (hJ (𝟙 _ ≫ _))).symm
  choose τ hτ using fun p : Fin n × Fin n' => exists_powMul U.LG.isLB (q := 𝟙 G.left) hm (x p.1).1 (x' p.2).1
  choose Φ hΦ using fun p => ((U.expand k'' hk'').1 (genericSec U.toUnifPre k'' (τ p))).exists
  choose r hr y hy d₁ d₂ using fun p => (expands_iff U.toUnifPre k'' _ _).1 (hΦ p)
  have hr' : ∀ p, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)) ≠ 0 := fun p => by
    rw [map_ne_zero]; exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hr p)
  have hyτ : ∀ p, (y p).1 = r p • (show IntSec U.toUnifPre k'' from τ p) := fun p =>
    genericSec_injective U.toUnifPre k'' ((d₁ p).trans (map_smulₛₗ _ _ _).symm)
  have hv : v'' = (∑ p : Fin n × Fin n', (c p.1 * c' p.2) • extendSec U.toUnifPre F k'' (genericSec U.toUnifPre k'' (τ p)) :
      GroupSec U.toUnifPre F k'') := by
    refine powVal_ext U.LG.isLB fun z i hi => ?_
    obtain ⟨i₁, hi₁⟩ := exists_chart A.isLB
      (U.gen.hom.left ((snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left z))
    have m := (isoRelM_iff _ _ _ _ a.1 _ a.2.1 _ _).1 a _ (𝟙 _) z i i₁ hi hi₁
    have m' := (isoRelM_iff _ _ _ _ a'.1 _ a'.2.1 _ _).1 a' _ (𝟙 _) z i i₁ hi hi₁
    have m'' := (isoRelM_iff _ _ _ _ a''.1 _ a''.2.1 _ _).1 a'' _ (𝟙 _) z i i₁ hi hi₁
    have b₁ : (snd (TFK (R := R) F) A.A).left ((𝟙 _ ≫ (U.genF F).left) z) ∈ A.L.U i₁ :=
      (congrArg (fun q => q z ∈ A.L.U i₁) a.1).mpr hi₁
    have m₀ := hu _ _ z i₁ b₁
    rw [Category.comp_id] at m m' m''
    have w₁ := (congrArg (fun q => powVal q (𝟙 _) z i) e₁).trans (powVal_comb U.toUnifPre c (fun p => (x p).1) z hi)
    have w₂ := (congrArg (fun q => powVal q (𝟙 _) z i) e₁').trans (powVal_comb U.toUnifPre c' (fun p => (x' p).1) z hi)
    refine Eq.trans ?_ (powVal_comb U.toUnifPre _ τ z hi).symm
    have w₃ : powVal v'' (𝟙 _) z i = powVal v (𝟙 _) z i * powVal v' (𝟙 _) z i := by
      rw [m, m', m'', m₀, hm, Nat.cast_add, zpow_add, Units.val_mul]; ring
    rw [w₃, w₁, w₂, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have cm : constVal (groupBase G F) z (c p * c' q) = constVal (groupBase G F) z (c p) * constVal (groupBase G F) z (c' q) :=
      (congrArg (gs _ z ⊤) (map_mul _ _ _)).trans (gs_mul _ z ⊤ trivial _ _)
    rw [hτ (p, q) _ (UnifPre.gFK (G := G) F) z i hi, cm]
    ring
  have hs : ∀ β, famProj D.toPre F k'' β (∑ p : Fin n × Fin n', (c p.1 * c' p.2) • famPull D.toPre (FractionRing R) F hG k'' (Φ p)) =
      ∑ p : Fin n × Fin n', (c p.1 * c' p.2 * (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)))⁻¹) •
        termPull D.toPre (FractionRing R) F k'' β (genericTerm D k'' β ((y p).2 β)) := fun β => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [d₂, map_smulₛₗ, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' p)]; rfl
  have hE := expandsG_of_fintype U.toUnifPre F k'' v'' _ _ y hy (hv.trans (Finset.sum_congr (M := GroupSec U.toUnifPre F k'') rfl fun p _ => by
    rw [d₁, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' p)])) hs
  rw [← ((expandsG_bijective U.toUnifPre F hG hk'' (U.expand k'' hk'')).1 v'').unique b'' hE] at hs
  choose z hz using fun i χ => exists_isTerm g hw ((x i).2 χ)
  choose z' hz' using fun i χ => exists_isTerm g hw' ((x' i).2 χ)
  choose z'' hz'' using fun p => exists_isTerm g hw'' ((y p).2 α)
  have key := sumF_sum hR Finset.univ (fun p : Fin n × Fin n' =>
      c p.1 * c' p.2 * (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)))⁻¹)
    fun p => point U.toUnifPre hL hR (r p) hm (hx p.1) (hx' p.2) (hy p) (fun Z q z j hj => by
      rw [hyτ p]
      exact (powVal_smul _ _ q z hj).trans (congrArg _ (hτ p Z q z j hj))) g hw'' hww (hz p.1) (hz' p.2) α (hz'' p)
  rw [coef_eq_sum g hz'' (hs α)]
  convert key using 2 with χ
  rw [coef_eq_sum g (fun i => hz i χ) (e₂ χ), coef_eq_sum g (fun i => hz' i (α - χ)) (e₂' (α - χ)), Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have := hr' (p, q)
  field_simp

end GlobalTheory.UT.ProdConv
end
