import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section
namespace GlobalTheory.Poinc.Tors.OneOver

theorem exists_frm_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F 1 b) (hw : w.IsGen) (k : ℕ) :
    ∃ wk : Frm D F k b, wk.IsGen ∧ ∀ z J, Good D.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k := by
  obtain ⟨z₀⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' D.P.isLB z₀
  obtain ⟨wk, hwk, hv⟩ := GlobalTheory.TorusExt.exists_gen_val D.P.isLB (DegPre.lineφ D F b) (DegPre.lineε k) hJ₀
    (val w (𝟙 _) z₀ J₀ ^ k)
  refine ⟨wk, hwk, fun z J hJ => ?_⟩
  obtain rfl := CoefBasic.pt_eq z₀ z
  have a₁ := CoefBasic.val_tr hwk (𝟙 _) hJ hJ₀
  have a₂ := CoefBasic.val_tr hw (𝟙 _) hJ hJ₀
  simp only [Category.id_comp] at a₁ a₂
  rw [CoefBasic.prod_line k b (CoefBasic.trU D.P.L z₀ J J₀)] at a₁
  rw [CoefBasic.prod_line 1 b (CoefBasic.trU D.P.L z₀ J J₀)] at a₂
  refine a₁.trans ?_
  rw [hv, a₂]
  simp only [pow_one, mul_pow, inv_pow]

theorem sumF_scale {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hI : AdmBase R I) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} {x : Ix → F} {v v' c : F} (h : SumF I F x v)
    (h' : SumF I F (fun i => c * x i) v') : v' = c * v := by
  have hl := (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix x x v v).2.1 h h (c - 1)
  have e : (fun i => (c - 1) * x i + x i) = fun i => c * x i := funext fun i => by ring
  rw [e, show (c - 1) * v + v = c * v by ring] at hl
  exact (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix (fun i => c * x i) x v' (c * v)).1 h' hl

theorem eq_of_liesOver : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre F) (w w' : Frm D.toPre F 1 g.b) (x x' : TFK (R := R) F ⟶ A.A) (fr : FrAt x) (fr' : FrAt x'), w.IsGen → w'.IsGen → fr.IsGen → fr'.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g w' x' fr' → x = x' := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ w₀ hw₀ g w w' x x' fr fr' hw hw' hfr hfr' H H'
  obtain ⟨wk, hwk, hvk⟩ := exists_frm_pow w hw 4
  obtain ⟨wk', hwk', hvk'⟩ := exists_frm_pow w' hw' 4
  obtain ⟨c, hc, -, hcoef⟩ := ((CoefBasic.coef_basic R D.toPre F 4 g).2.2 wk hwk).2.2.1 wk' hwk'
  have key : ∀ (t : SecA A F 4) (v v' : F), ValAt t x fr v → ValAt t x' fr' v' → v' = c * v := by
    intro t v v' hv hv'
    obtain ⟨s, hs⟩ : ∃ s, U.toUnifPre.ExpandsF F 4 w₀ t s := by
      obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 4) (by norm_num) w₀ hw₀
      exact ⟨e t, (he t _).2 rfl⟩
    have h1 := H 4 (by norm_num) wk hvk hwk t s v hs hv
    have h2 := H' 4 (by norm_num) wk' hvk' hwk' t s v' hs hv'
    rw [show coef s g wk' = fun χ => c * coef s g wk χ from funext (hcoef s)] at h2
    exact sumF_scale hI h1 h2
  obtain ⟨M, s, hcov, haff⟩ := (hL.1.ample _ A 4 le_rfl).2 ⊤ (isAffineOpen_top _)
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.A.left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.A.left.topIso.inv, A.A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ v : SecA A F 4, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J),
      Good A.L z J → sA v r z J =
        sval (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd (TFK (R := R) F) A.A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec A.isLB (φ := fun _ : Fin 4 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => ((4 : ℕ) : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (TFK (R := R) F) A.A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (VVRank.sval_pullTo _ _ _ r z hJ)⟩
  choose v hv using sec
  choose a ha using fun j => GlobalTheory.OneBasis.exists_valAt A F hL.1 (v j) x hfr
  choose a' ha' using fun j => GlobalTheory.OneBasis.exists_valAt A F hL.1 (v j) x' hfr'
  have hrel : ∀ j, a' j = c * a j := fun j => key (v j) (a j) (a' j) (ha j) (ha' j)
  have hf : (x.left ≫ i') ≫ (A.A.hom ∣_ ⊤) = (x'.left ≫ i') ≫ (A.A.hom ∣_ ⊤) := by
    rw [← cancel_mono (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens).ι]
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
  have e : ∀ y : TFK (R := R) F ⟶ A.A,
      (ptSecT A.A y).left ≫ (snd (TFK (R := R) F) A.A).left ≫ i' = y.left ≫ i' := fun y => by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
  have key2 : x.left ≫ i' = x'.left ≫ i' := by
    refine AutUniq.hom_eq_of_sval (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s
      (A.A.hom ∣_ ⊤) _ _ hf hcov (fun i => (haff i).1) r hr hsurj fun z => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' A.isLB z
    obtain ⟨κ, hκ⟩ : ∃ κ : F →+* (TFK (R := R) F).left.presheaf.stalk z, ∀ b, cst (R := R) F z b = κ b :=
      ⟨CoefBasic.cstH (R := R) z, CoefBasic.cst_eq z⟩
    refine ⟨J, hJ, Units.map κ.toMonoidHom (Units.mk0 c hc) *
      val (powFrame A.A A.L x' fr' 4) (𝟙 _) z J * (val (powFrame A.A A.L x fr 4) (𝟙 _) z J)⁻¹, fun j => ?_⟩
    have p := (hv j _ (ptSecT A.A x).left z J hJ).symm.trans (ha j z J hJ)
    have q := (hv j _ (ptSecT A.A x').left z J hJ).symm.trans (ha' j z J hJ)
    rw [e] at p q
    rw [p, q, hrel j]
    have hinv := Units.inv_mul (val (powFrame A.A A.L x fr 4) (𝟙 _) z J)
    simp only [Units.val_mul, Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      hκ, map_mul, id] at hinv ⊢
    linear_combination (-(κ c * (val (powFrame A.A A.L x' fr' 4) (𝟙 _) z J).val * κ (a j))) * hinv
  have := congrArg (fun q => q ≫ (A.A.hom ⁻¹ᵁ ⊤).ι) key2
  simp only [Category.assoc, hi, Category.comp_id] at this
  exact Over.OverMorphism.ext this

end GlobalTheory.Poinc.Tors.OneOver
