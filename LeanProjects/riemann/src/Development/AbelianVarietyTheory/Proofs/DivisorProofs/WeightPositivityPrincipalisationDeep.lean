import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfGenericUniqueComplexPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatesOnSmoothOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPtMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompEmbEqOfFrBor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepCusp

section Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn exOf secZ)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.CompHt (genVal genPoint)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_of_ptY_eq {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (h : GenFrEx Xo c) (Z : Comp Xo c)
    {K : Type} [Field K] [Algebra c.F K] (φ φ' : Om Z →ₐ[c.F] K)
    (e : spMap φ.toRingHom ≫ X.ptY (genFr h Z) = spMap φ'.toRingHom ≫ X.ptY (genFr h Z)) : φ = φ' := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagMod.exists_frMap φ (genFr h Z)
  obtain ⟨y', hy'⟩ := GlobalTheory.FlagMod.exists_frMap φ' (genFr h Z)
  rw [X.ptY_frMap hy, X.ptY_frMap hy'] at e
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY y)
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) (X.lies_ptY y).1 k hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY y)
  obtain ⟨t', ht'⟩ := hQ.exists_frBor (e ▸ X.lies_ptY y')
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  exact eq_of_heq (GlobalTheory.Reg.GenericFlagInj.eq_of_frBor h Z Z φ φ' y y' _ hy hy' (g1 _ _ _ _ _ (g2 _ _ _ ht) ht')).2

theorem exists_val_cuspSec {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (h : GenFrEx Xo c) (w : Sp (Om Z) ⟶ Y₀ X Z)
    (hw : w ≫ inc₀ X Z = X.ptY (genFr h Z)) (hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z) (i : (L₀ X Z la).ι)
    (hi : ⊤ ≤ w ⁻¹ᵁ (L₀ X Z la).U i) :
    ∃ T : Om Z, T ≠ 0 ∧ ∀ g : Cusp Z U la, H0.val w i hU hi (cuspSec X Z U la g) = T * genVal Z g.1 := by
  have e₁ : w ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by rw [X.pt_inc]; exact hw
  have hO₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have hk₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) :=
    (le_iff_ptOf_mem _ _).2 (mem_pull.1 ((le_iff_ptOf_mem _ _).1 hi))
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
  have hQ₂ : X.F.ChartFr (i PUnit.unit) (w ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
  have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
  have v₅ : H0.val w i hU hi (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
      (w ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl w i hU hi hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  rw [v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem val_eq_stalk {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    H0.val x i hO hi f = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom (germ i (ptOf x) hy hj f) := by
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm

theorem gapGe_std (Dw : Datum H) : GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_std (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) :=
  map_nsmul (AddMonoidHom.mk' (fun a => cls (B a) (C.isLB a)) (cls_common_add C)) n a

theorem ratioField_eq_top (hP : Hypotheses₂) (hG : GlobalTheory.Published.GrothendieckDeformation) (hN : GlobalTheory.Published.NefNumerics)
    (hSi : GlobalTheory.Published.SiegelToroidalIntegral) (hCh : GlobalTheory.Published.ToroidalChartsForFan)
    (hLie : GlobalTheory.Published.SemiAbelianLieSeminegative) (hS : GlobalTheory.Published.PointSeparationPair) (TF : TorFlag Xo c)
    (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hF : FnAlgClosed Xo c) (hD : 1 ≤ dimFlag Dw)
    (hpq : 1 ≤ Dw.p + Dw.q) (la : AllWt.Weight Dw)
    (hg : GapGe (((dimFlag Dw + 2).choose 2 : ℕ) : ℤ) (la - FlagTan.kap Dw))
    (hv : vanBd TF.X Z la ≤ space TF.X Z U la) :
    GlobalTheory.DegVal.ratioField (genPoint Z (cuspOn U Z (wtOf Dw la 0))) = ⊤ := by
  set L := GlobalTheory.DegVal.ratioField (genPoint Z (cuspOn U Z (wtOf Dw la 0))) with hL
  haveI := c.fin
  haveI : Countable c.F := (Module.finBasis ℚ c.F).equivFun.injective.countable
  haveI : Countable (Om Z) := TwoPoint.countable_of_fg c.F (Om Z) ((FlagDim.fnFG_fnTrdeg E H Dw l Xo c).1 Z)
  refine eq_top_iff.2 fun a _ => by_contra fun ha => ?_
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap c.F L).injective
  obtain ⟨i₁, i₂, hi, hne⟩ := TwoPoint.exists_two_embeddings L (Om Z) a (by rintro ⟨b, rfl⟩; exact ha b.2)
  have hag : ∀ b ∈ L, i₁ b = i₂ b := fun b hb => RingHom.congr_fun hi ⟨b, hb⟩
  have hV := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  let M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw) := Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)
  haveI : IsAffineHom M.σ := inferInstanceAs (IsAffineHom (𝟙 (Y₀ TF.X Z)))
  have hconn : GeometricallyConnected M.str := by
    have e : M.str = str₀ TF.X Z := Category.id_comp (str₀ TF.X Z)
    rw [e]
    exact hV.2.2
  obtain ⟨ω⟩ := GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z M
    (fun K _ _ y => GlobalTheory.FlagTan.ksIso_psiSet hP hG E H Dw l Xo c K y hpq)
  obtain ⟨F, hFg⟩ := GlobalTheory.T.canonical_modification_weight_bound hP hG E H Dw l Xo c TF Z r U hF M ω (la - FlagTan.kap Dw) la (by abel) hv
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M h
  have hzo : ptOf z ∈ M.off := (le_iff_ptOf_mem _ _).1 hO
  have hη : M.σ (ptOf z) ∈ U₀ TF.X Z := M.off_eq.le hzo
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ TF.X Z := (le_iff_ptOf_mem _ _).2 hη
  have hB := LB.isLB_pull (isLB_L₀ TF.X Z (la - FlagTan.kap Dw)) M.σ
  obtain ⟨j, hj⟩ := exists_chart (isLB_tens M.K.isLB hB) (ptOf z)
  have hj' := (le_iff_ptOf_mem z _).2 hj
  obtain ⟨i, hi₀⟩ := exists_chart (isLB_L₀ TF.X Z la) (M.σ (ptOf z))
  have hi' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (L₀ TF.X Z la).U i := (le_iff_ptOf_mem _ _).2 hi₀
  obtain ⟨u, hu⟩ := hFg (ptOf z) hzo j hj i hi₀
  obtain ⟨T, hT, hTv⟩ := exists_val_cuspSec TF.X Z U la h (z ≫ M.σ) (by rw [Category.assoc]; exact hz) hU i hi'
  obtain ⟨T', hT', hval⟩ : ∃ T' : Om Z, T' ≠ 0 ∧ ∀ g, H0.val z j le_top hj' g = T' * genVal Z (F g).1 := by
    refine ⟨(Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) z).hom u.val * T,
      mul_ne_zero (u.isUnit.map _).ne_zero hT, fun g => ?_⟩
    rw [val_eq_stalk z j le_top hj' (memTop _) hj, hu, mul_assoc, ← hTv,
      val_eq_stalk (z ≫ M.σ) i hU hi' hη hi₀, Scheme.stalkClosedPointTo_comp]
    exact map_mul (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) z).hom _ _
  let σ : c.F →+* ℂ := i₁.comp (algebraMap c.F (Om Z))
  have hσ : i₂.comp (algebraMap c.F (Om Z)) = σ := RingHom.ext fun k => (hag _ (L.algebraMap_mem k)).symm
  let ι : Fin 2 → (Om Z →+* ℂ) := ![i₁, i₂]
  have hι : ∀ n, (ι n).comp (algebraMap c.F (Om Z)) = σ := Fin.forall_fin_two.2 ⟨rfl, hσ⟩
  have hstr : z ≫ M.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag M ≫ flagStr TF.X) = _
    rw [← Category.assoc, hz, ptY_str]
  have hzz : spMap (ι 0) ≫ z ≠ spMap (ι 1) ≫ z := fun e => by
    letI : Algebra c.F ℂ := σ.toAlgebra
    have := eq_of_ptY_eq TF.X h Z (K := ℂ) ⟨i₁, RingHom.congr_fun (hι 0)⟩ ⟨i₂, RingHom.congr_fun (hι 1)⟩ (by
      rw [← hz, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ toFlag M) e)
    exact hne (congrArg AlgHom.toRingHom this)
  set std : AllWt.Weight Dw := GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q)
  set m : ℕ := (dimFlag Dw + 2).choose 2
  have hstd : GapGe 1 std := gapGe_std Dw
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → letI := algebraΓOfHom M.str; IsNef c.F ((L₀ TF.X Z w).pull M.σ) :=
    fun w hw => TwoPoint.nef_pull hN _ M.str M.σ hV.2.1 M.proj _ (GlobalTheory.NefWt.isNef_L₀ hP hN hLie E H Dw l Xo c TF Z hF w hw)
  obtain ⟨mu, hmu0, m', hm', hA⟩ := ampleAt_regular hP hN hSi hCh E H Dw l Xo c TF Z hF std hstd _ hη
  have C := (common₀ TF.X Z).pull M.σ
  have e₁ := cls_common_add C (m' • std - mu) mu
  rw [sub_add_cancel] at e₁
  replace e₁ := (cls_nsmul C m' std).symm.trans e₁
  have e₂ := cls_common_add C (m • std) (la - FlagTan.kap Dw - m • std)
  rw [add_sub_cancel] at e₂
  replace e₂ := e₂.trans (congrArg (· + _) (cls_nsmul C m std))
  have hk : ∀ n, ⊤ ≤ (spMap (ι n) ≫ z) ⁻¹ᵁ (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)).U j :=
    fun n => (le_iff_ptOf_mem _ _).2 (by rw [ptOf_spMap_comp]; exact hj)
  have main := fun (a : Fin 2 → ℂ) (ha : ∀ n, a n ≠ 0) =>
    TwoPoint.separate_two (TwoPoint.separatesOnSmooth_of_pair hS) hN c.F σ M.X M.str (dimFlag Dw) M.proj hconn hD M.K
      _ _ _ _ _ _ _ _ _ _ m' m (nef std (hstd.mono zero_le_one)) (nef _ (gapGe_sub_std m _ hg)) (nef mu hmu0) le_rfl hm'
      e₁ e₂ (fun n => spMap (ι n) ≫ z) hzz
      (fun n => by rw [Category.assoc, hstr, spMap_comp_ring, hι])
      (fun n s => by
        have e : (spMap (ι n) ≫ z) s = ptOf z := congrArg z (Subsingleton.elim (α := PrimeSpectrum (Om Z)) _ _)
        rw [e]
        exact AmplePull.ampleAt_pull _ _ M.σ _ (isLB_L₀ TF.X Z _) _ hA)
      (fun _ => j) hk a ha
  have hvι : ∀ n g, H0.val (spMap (ι n) ≫ z) j le_top (hk n) g = ι n (T' * genVal Z (F g).1) := fun n g => by
    rw [← hval]
    exact GlobalTheory.CuspOnTor.val_spMap (ι n) z j le_top hj' le_top (hk n) g
  by_cases h0 : ∃ g₀, genVal Z (F g₀).1 ≠ 0
  · obtain ⟨g₀, hg₀⟩ := h0
    have hn : ∀ n, ι n (T' * genVal Z (F g₀).1) ≠ 0 := fun n => (map_ne_zero _).2 (mul_ne_zero hT' hg₀)
    refine main ![(i₁ (T' * genVal Z (F g₀).1))⁻¹, -(i₂ (T' * genVal Z (F g₀).1))⁻¹]
      (Fin.forall_fin_two.2 ⟨inv_ne_zero (hn 0), neg_ne_zero.2 (inv_ne_zero (hn 1))⟩) fun g => ?_
    have e := hag (genVal Z (F g).1 / genVal Z (F g₀).1) (IntermediateField.subset_adjoin _ _ ⟨F g, F g₀, rfl⟩)
    rw [← mul_div_mul_left _ _ hT', map_div₀, map_div₀] at e
    rw [Fin.sum_univ_two, hvι, hvι]
    show (i₁ _)⁻¹ * i₁ _ + -(i₂ _)⁻¹ * i₂ _ = 0
    rw [neg_mul, ← div_eq_inv_mul, ← div_eq_inv_mul, e, add_neg_cancel]
  · push_neg at h0
    refine main (fun _ => 1) (fun _ => one_ne_zero) fun g => ?_
    simp [hvι, h0]

end Geometry

theorem exists_fg_complexPoint (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [Countable K]
    (hfg : (⊤ : IntermediateField K Ω).FG) (L : IntermediateField K Ω) (hL : L = ⊤) :
    ∃ (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ L) ∧
      IntermediateField.adjoin K (A : Set Ω) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ,
        (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧
          ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) := by
  have : Countable Ω := TwoPoint.countable_of_fg _ _ hfg
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨i⟩ := TwoPoint.nonempty_ringHom_complex Ω
  obtain ⟨s, hs⟩ := hfg
  let A : Subalgebra K Ω := Algebra.adjoin K (s : Set Ω)
  exact ⟨i.comp (algebraMap _ _), A, A, ⟨s, rfl⟩, ⟨s, rfl⟩, le_rfl, fun b _ => hL ▸ IntermediateField.mem_top,
    eq_top_iff.2 (hs ▸ IntermediateField.adjoin.mono _ _ _ Algebra.subset_adjoin), fun b _ hb =>
    ⟨i.comp A.val.toRingHom, fun _ => rfl, fun _ => (map_ne_zero i).2 hb, fun y _ h => RingHom.ext fun a => h a a.2⟩⟩

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem gapGe_sub_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (hu : ∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      (((dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ u τ a - u τ b) :
    GlobalTheory.HSApp.GapGe (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) (u - FlagTan.kap Dw) := by
  intro τ k hk
  have h₁ := hu τ ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
  have h₂ := GlobalTheory.HSApp.gap_kap_le (Dw := Dw) τ hk
  have h₃ := GlobalTheory.CompHS.gap_eq (u τ) (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl
  have h₄ : (FlagTan.dimFlag Dw + 2).choose 2 ≤ (FlagTan.dimFlag Dw + 3) ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 2)
  have h₅ : (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) ≤ ((FlagTan.dimFlag Dw + 3) ^ 2 : ℕ) := by
    exact_mod_cast h₄
  rw [GlobalTheory.CompHS.dimFlag_eq] at h₁
  rw [Pi.sub_apply, GlobalTheory.HSApp.gap_sub]
  dsimp only at h₃
  push_cast at h₁ h₂ h₅ ⊢
  linarith

set_option maxHeartbeats 1000000 in

theorem cusp_separate_general_points : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → Hypotheses₂ → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (σ : Y.d.c₂.F →+* ℂ) (A B : Subalgebra Y.d.c₂.F (Om Z)), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ ratioField (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)))) ∧ IntermediateField.adjoin Y.d.c₂.F (A : Set (Om Z)) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : Y.d.c₂.F, x (algebraMap Y.d.c₂.F A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : Y.d.c₂.F, y (algebraMap Y.d.c₂.F A k) = σ k) → (∀ a : A, (a : Om Z) ∈ B → y a = x a) → y = x) := by
  intro hX hG hQ hSi hP _ _ D T _ j hp hq Y e o hY u hu Z
  have hf : 2 < Module.finrank ℚ D.host.E / 2 := by
    have := D.eight_le_f
    rw [D.host.finrank_E']
    omega
  have hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) := Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨TF⟩ := GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have htop := ratioField_eq_top hP hG hQ.nef hSi hX.ks.toroidalChartsForFan hX.lie hX.sep TF Z Y.U hY.geo hD (by omega) u (gapGe_sub_kap u hu)
    (GlobalTheory.HSApp.vanBd_le_space D T.toCore j Y e o hY hf Z TF u)
  have := Y.d.c₂.fin
  have : Countable Y.d.c₂.F := (Module.finBasis ℚ Y.d.c₂.F).equivFun.injective.countable
  exact exists_fg_complexPoint _ _ ((FlagDim.fnFG_fnTrdeg _ _ _ _ Y.d.Xo₂ Y.d.c₂).1 Z) _ htop

end GlobalTheory.SepCusp
