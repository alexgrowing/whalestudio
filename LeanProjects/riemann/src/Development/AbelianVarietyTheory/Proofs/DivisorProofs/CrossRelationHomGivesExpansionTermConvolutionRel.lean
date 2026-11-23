import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionsCrossRelationOfHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.Mum.MixTwo

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

abbrev homF (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (UnifPre.GF (G := G₁) F).left ⟶ (UnifPre.GF (G := G₂) F).left :=
  (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left

theorem homF_str (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    homF a F ≫ MixedConv.strF G₂ F = MixedConv.strF G₁ F :=
  congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) ((Over.pullback (jK R)).map a))

theorem homF_gFK (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    homF a F ≫ UnifPre.gFK (G := G₂) F = UnifPre.gFK (G := G₁) F ≫ a.left := by
  have h₁ := congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) ((Over.pullback (jK R)).map a))
  have h₂ : ((Over.pullback (jK R)).map a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ a.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G₂.hom (jK R)) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

theorem val_secLin' {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {U : UnifPre I D A G} {F : Type} [Field F] [Algebra (FractionRing R) F] {k n : ℕ} {σ₀ : U.SecGF F k}
    {σ : Fin n → H0 U.LG.L k} {c : Fin n → F}
    (h : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)))
    {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of F)) (r : Y ⟶ (UnifPre.GF (G := G) F).left)
    (hr : r ≫ MixedConv.strF G F = q) (y : Y) {J} (hJ : Good U.LG.L y J) :
    sval σ₀ r y J = ∑ i, GlobalTheory.BoxExpansion.constHomVal q y (c i) *
      sval (σ i) (r ≫ UnifPre.gFK (G := G) F) y J :=
  (GlobalTheory.BoxExpansion.secLin_val h r y hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _)
    ((gs_scal (MixedConv.strF G F) r y _).trans ((congrArg (fun q => constVal q y (c i)) hr).trans
      (GlobalTheory.BoxExpansion.constVal_eq _ _ _))))

theorem coreF₂ [CharZero R] (hL : LL) (hR : AdmBase R I) {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
    {a : G₁ ⟶ G₂} {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {h : D₂.toPre.X →+ D₁.toPre.X} (hLin : Lin U₁ U₂ a b h)
    (hCo : Coord U₁ U₂ a b h) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ)
    {N : Type} [Fintype N] (c : N → F) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j')
    (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α)
    (hE : ∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) (hE' : ∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν))
    (hrel : ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ →
      ∑ ν, GlobalTheory.BoxExpansion.constHomVal (MixedConv.strF G₁ F) y (c ν) *
        (sval (σ ν) (UnifPre.gFK (G := G₁) F ≫ a.left) y J₂ * sval (σ' ν) (UnifPre.gFK (G := G₁) F) y J₁) = 0)
    (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F) (hg : Act D₁.toPre D₂.toPre b h g g')
    (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b) (hw : w.IsGen) (hw' : w'.IsGen)
    (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F)
    (hx : ∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) (hx' : ∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ))
    (α : D₁.toPre.X) :
    SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} =>
      ∑ ν, c ν * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  obtain ⟨n, β, ρ, hβ, hc⟩ := MixedConv.exists_indep (R := R) c
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  have P₁ := isPart_inl U₁.LG.L U₂.LG.L
  have P₂ := isPart_inr U₁.LG.L U₂.LG.L
  let d : Fin n → SecOver G₁.hom (LB.LinComb (join U₁.LG.L U₂.LG.L)
      (Sum.elim (fun _ : Fin 1 => (a.left ≫ 𝟙 G₂.left) ≫ coprod.inr) (fun _ : Fin 1 => 𝟙 G₁.left ≫ coprod.inl))
      (Sum.elim (fun _ => (j : ℤ)) (fun _ => (j' : ℤ)))) := fun m =>
    ∑ ν, ρ m ν • (show SecOver G₁.hom _ from
      H1.SectionArithmetic.mulSec (P₂.sec (H1.SectionArithmetic.pullSec (σ ν) a.left)) (P₁.sec (σ' ν)))
  have hd : ∀ m (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J), Good (join U₁.LG.L U₂.LG.L) z J →
      sval (d m) r z J = ∑ ν, constVal (r ≫ G₁.hom) z (ρ m ν) *
        (sval (σ ν) (r ≫ a.left) z (rr J) * sval (σ' ν) r z (rl J)) :=
    fun m Z r z J hJ => (sval_sum' (π := G₁.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
      (sval_smul' (π := G₁.hom) hJ _ _ _).trans (congrArg _ ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans
        (congrArg₂ (· * ·) ((P₂.sval_sec _ r z hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z (P₂.good hJ)))
          (P₁.sval_sec _ r z hJ)))))
  have := U₁.smooth
  have h₀ := GlobalTheory.T.sval_eq_zero_of_linearIndependent_comb R F _ _ _ _ G₁.hom (MixedConv.strF G₁ F) _ MixedConv.isPullback_GF
    (join U₁.LG.L U₂.LG.L) (join_isLB U₁.LG.isLB U₂.LG.isLB) _ _ _ _ β hβ d
    (fun y J hJ => by
      refine Eq.trans ?_ (hrel y (rl J) (rr J) (P₁.good hJ) (P₂.good hJ))
      simp only [hd _ _ _ y J hJ, hc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => ?_
      rw [(MixedConv.isPullback_GF (G := G₁) (F := F)).w, constVal_specMap, GlobalTheory.BoxExpansion.constVal_eq,
        GlobalTheory.BoxExpansion.constVal_eq, _root_.mul_assoc]
      rfl)
  have h₁ := MixedConv.sumF_comb hR Finset.univ β _ fun m => GlobalTheory.T.integralRelation_uniformisedHom_convolution_expansionTerms hL R I hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a b h hLin hCo F
    j j' N (ρ m) σ σ' f f' hE hE' (fun Z r z J₁ J₂ hJ₁ hJ₂ => by
      obtain ⟨J, hJ, rfl, rfl⟩ := exists_good_join U₁.LG.isLB U₂.LG.isLB hJ₁ hJ₂
      exact (hd m Z r z J hJ).symm.trans (h₀ m Z r z J hJ)) g g' hg w w' hw hw' x x' hx hx' α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp h₁
  simp only [hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => (_root_.mul_assoc _ _ _).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₁ : W0 U₁.toUnifPre) (w₂ : W0 U₂.toUnifPre), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') s₁ s₂ s₁' s₂', U₂.ExpandsF F j w₂ t₁ s₁ → U₂.ExpandsF F j w₂ t₂ s₂ → U₁.ExpandsF F j' w₁ t₁' s₁' → U₁.ExpandsF F j' w₁ t₂' s₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  intro R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ _ _ U₁ U₂ a c b h _ hG hLin hCo F _ _ _ w₁ w₂ hw₁ hw₂ j j' _ _
    t₁ t₂ t₁' t₂' s₁ s₂ s₁' s₂' H₁ H₂ H₁' H₂' hC g g' hg w w' hw hw' α
  obtain ⟨τ₁, r₁, n₁, c₁, σ₁, f₁, e₁, l₁, b₁⟩ := H₁
  obtain ⟨τ₂, r₂, n₂, c₂, σ₂, f₂, e₂, l₂, b₂⟩ := H₂
  obtain ⟨τ₁', r₁', n₁', c₁', σ₁', f₁', e₁', l₁', b₁'⟩ := H₁'
  obtain ⟨τ₂', r₂', n₂', c₂', σ₂', f₂', e₂', l₂', b₂'⟩ := H₂'
  choose x₁ hx₁ using fun i χ => MixedConv.exists_isCoefB g' hw χ (f₁ i χ)
  choose x₂ hx₂ using fun i χ => MixedConv.exists_isCoefB g' hw χ (f₂ i χ)
  choose x₁' hx₁' using fun i χ => MixedConv.exists_isCoefB g hw' χ (f₁' i χ)
  choose x₂' hx₂' using fun i χ => MixedConv.exists_isCoefB g hw' χ (f₂' i χ)
  have key := coreF₂ GlobalTheory.firstFiveLaws hR hLin hCo j j' (N := (Fin n₁ × Fin n₂') ⊕ (Fin n₂ × Fin n₁'))
    (Sum.elim (fun p => c₁ p.1 * c₂' p.2) (fun p => -(c₂ p.1 * c₁' p.2)))
    (Sum.elim (fun p => σ₁ p.1) (fun p => σ₂ p.1)) (Sum.elim (fun p => σ₂' p.2) (fun p => σ₁' p.2))
    (Sum.elim (fun p => f₁ p.1) (fun p => f₂ p.1)) (Sum.elim (fun p => f₂' p.2) (fun p => f₁' p.2))
    (by rintro (p | p); exacts [e₁ p.1, e₂ p.1]) (by rintro (p | p); exacts [e₂' p.2, e₁' p.2])
    (fun y J₁ J₂ hJ₁ hJ₂ => by
      have hh := GlobalTheory.T.carriedSections_crossRelation_of_hom R I D₁ D₂ A₁ A₂ G₁ G₂ U₁.toUnifPre U₂.toUnifPre a c hG F w₁ w₂ hw₁ hw₂ j j'
        t₁ t₂ t₁' t₂' τ₁ τ₂ τ₁' τ₂' r₁ r₂ r₁' r₂' hC y J₁ J₂ hJ₁ hJ₂
      rw [val_secLin' l₁ _ _ (homF_str a F) y hJ₂, val_secLin' l₂ _ _ (homF_str a F) y hJ₂,
        val_secLin' l₁' _ _ (Category.id_comp _) y hJ₁, val_secLin' l₂' _ _ (Category.id_comp _) y hJ₁, homF_gFK,
        Category.id_comp, Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero] at hh
      refine Eq.trans ?_ hh
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, map_neg, map_mul,
        neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
      exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
        (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _))
    g g' hg w w' hw hw' (Sum.elim (fun p => x₁ p.1) (fun p => x₂ p.1))
    (Sum.elim (fun p => x₂' p.2) (fun p => x₁' p.2))
    (by rintro (p | p); exacts [hx₁ p.1, hx₂ p.1]) (by rintro (p | p); exacts [hx₂' p.2, hx₁' p.2]) α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp key
  rw [MixedConv.coef_of_secLin (b₁ _) (fun i => hx₁ i _), MixedConv.coef_of_secLin (b₂ _) (fun i => hx₂ i _),
    MixedConv.coef_of_secLin (b₁' _) (fun i => hx₁' i _), MixedConv.coef_of_secLin (b₂' _) (fun i => hx₂' i _),
    Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
    (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)

end GlobalTheory.Mum.MixTwo
end
