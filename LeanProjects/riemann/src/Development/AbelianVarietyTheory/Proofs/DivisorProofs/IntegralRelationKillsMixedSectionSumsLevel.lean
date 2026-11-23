import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqZeroWeightIndependenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

set_option maxHeartbeats 1000000 in

theorem level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Over₀ U₁ U₂ a b → ∀ (u : ∀ χ, LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ)), (∀ χ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) = val ((U₁.gt e).t (h χ)) x z (rl J) * val (u χ) (x ≫ (U₁.gt e).pG.left) z J) → ∀ (j j' e : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} → LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j'))), (∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) * (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) * (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val)) → ∀ (α : D₁.toPre.X), ∃ S : Finset {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → (∀ i ∉ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0) ∧ ∑ i ∈ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hO u hu j j' e N _ ρ σ σ' f f' hE hE' hrel m hm α
  classical
  obtain ⟨S, hS⟩ := MixedConv.expand_common U₂ e j σ f hE
  obtain ⟨S', hS'⟩ := MixedConv.expand_common U₁ e j' σ' f' hE'
  have pl := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have pr := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  let ae := ((Over.pullback (thick R I e)).map a).left
  have hpe : ae ≫ pGl U₂ e = pGl U₁ e ≫ b.left := by
    have h₁ := congrArg (fun q => q.left) (hO e)
    have h₂ : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ b.left :=
      pullback.lift_fst _ _ _
    show _ ≫ (U₂.gt e).q.left ≫ pullback.fst _ _ = ((U₁.gt e).q.left ≫ pullback.fst _ _) ≫ _
    rw [← Category.assoc]
    exact (congrArg (· ≫ pullback.fst _ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg ((U₁.gt e).q.left ≫ ·) h₂).trans (Category.assoc _ _ _).symm))
  have hfe : ae ≫ fGl I G₂ e = fGl I G₁ e ≫ a.left := pullback.lift_fst _ _ _
  have hp : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ pGl U₂ e = (x ≫ pGl U₁ e) ≫ b.left :=
    fun x => by rw [Category.assoc, Category.assoc, hpe]
  have hf : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ fGl I G₂ e = (x ≫ fGl I G₁ e) ≫ a.left :=
    fun x => by rw [Category.assoc, Category.assoc, hfe]
  let d : ∀ α, SecOver D₁.toPre.P.A.hom
      (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) := fun α =>
    ∑ p ∈ (S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), (m α p : SecOver D₁.toPre.P.A.hom _)
  have lift : ∀ n : LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')),
      (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
        sval n (x ≫ pGl U₁ e) z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J),
        Good (JN D₁.toPre D₂.toPre) z J → sval n (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := fun n hn Z r z J hJ =>
    GlobalTheory.LiftTest.main R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) _ _ _ n
      (fun Z x r hr z J hJ => by
        obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
        exact hn Z x z J hJ) Z _
      ⟨r ≫ pullback.snd _ _, by
        rw [Category.assoc, Category.assoc]; exact congrArg (r ≫ ·) pullback.condition.symm⟩ z J hJ
  refine ⟨(S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), fun Z r z J hJ => ⟨fun i hi => ?_, ?_⟩⟩
  · refine lift _ (fun Z x z J hJ => ?_) Z r z J hJ
    rw [hm α i _ _ z J hJ]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [Finset.mem_subtype, Finset.mem_product, not_and_or] at hi
    rcases hi with hi | hi
    · rw [← hp, (hS ν Z (x ≫ ae) z (rr J) (pr.good hJ)).1 _ hi, zero_mul, zero_mul, mul_zero]
    · rw [(hS' ν Z x z (rl J) (pl.good hJ)).1 _ hi, mul_zero, zero_mul, mul_zero]
  · refine (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).symm.trans (lift (d α) (fun Z x z J hJ => ?_) Z r z J hJ)
    refine GlobalTheory.T.sectionValue_eq_zero_weightIndependence_level R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) coprod.inl Prod.fst pl _
      (mixφ D₁.toPre D₂.toPre b) (MixedConv.mixε j j') d (insert α ((S ×ˢ S').image fun p => h p.1 + p.2)) ?_ α
      (Finset.mem_insert_self _ _) Z x _ (Category.comp_id _) z J hJ
    intro Z x r hr z J hJ
    obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
    have hJl : Good D₁.toPre.P.L z (rl J) := pl.good hJ
    have hJr : Good D₂.toPre.P.L z (rr J) := pr.good hJ
    obtain ⟨J₁, hJ₁⟩ := CoefBasic.exists_good' U₁.LG.isLB z
    obtain ⟨J₂, hJ₂⟩ := CoefBasic.exists_good' U₂.LG.isLB z
    let T : D₂.toPre.X × D₁.toPre.X → Z.presheaf.stalk z := fun p =>
      ∑ ν, constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
      ((sval (f ν p.1) ((x ≫ ae) ≫ pGl U₂ e) z (rr J) * (val (tG U₂ e p.1) (x ≫ ae) z (rr J)).val) *
        (sval (f' ν p.2) (x ≫ pGl U₁ e) z (rl J) * (val (tG U₁ e p.2) x z (rl J)).val))
    have k₁ : ∀ β, sval (d β) (x ≫ pGl U₁ e) z J * (val ((U₁.gt e).t β) x z (rs coprod.inl Prod.fst J)).val =
        ∑ p ∈ (S ×ˢ S').filter (fun p => h p.1 + p.2 = β), T p := fun β => by
      refine (congrArg (· * _) (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _)).trans ?_
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨⟨χ, δ⟩, rfl⟩ := p
      rw [hm _ _ _ _ z J hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have a₁ := congrArg Units.val (MixedConv.t_mul_val U₁ e (h χ) δ x z hJl)
      have a₂ := congrArg Units.val (hu χ e Z x z J hJ)
      simp only [Units.val_mul] at a₁ a₂ ⊢
      rw [hp]
      linear_combination (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (u χ) (x ≫ pGl U₁ e) z J).val) * a₁ -
        (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (tG U₁ e δ) x z (rl J)).val) * a₂
    refine (Finset.sum_congr rfl fun β _ => k₁ β).trans ((Finset.sum_fiberwise_of_maps_to (fun p hp =>
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)) T).trans ?_)
    have hc : (x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom = (x ≫ fGl I G₁ e) ≫ G₁.hom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) ((Over.w (U₁.gt e).pG).trans (Over.w (fstG I e G₁)).symm)
    have k₂ := hrel Z (x ≫ fGl I G₁ e) z J₁ J₂ hJ₁ hJ₂
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun ν _ => ?_) ((Finset.mul_sum _ _ _).symm.trans
      ((congrArg (((wv U₂ e (x ≫ ae) z (rr J ((x ≫ ae) ≫ pGl U₂ e)) (J₂ (((x ≫ ae) ≫ fGl I G₂ e) ≫ 𝟙 _)) ^ j).val *
        (wv U₁ e x z (rl J (x ≫ pGl U₁ e)) (J₁ ((x ≫ fGl I G₁ e) ≫ 𝟙 _)) ^ j').val) * ·) k₂).trans (mul_zero _)))
    rw [← Finset.mul_sum, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_mul_sum, ← (hS ν Z (x ≫ ae) z (rr J) hJr).2 J₂ hJ₂,
      ← (hS' ν Z x z (rl J) hJl).2 J₁ hJ₁, hc, ← hf]
    ring

end GlobalTheory.Mum.Two.Mix
