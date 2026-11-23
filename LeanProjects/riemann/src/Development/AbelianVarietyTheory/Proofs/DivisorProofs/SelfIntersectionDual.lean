import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnSeqShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyDivisorDimension
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue GlobalTheory.ArInt GlobalTheory.TwistTop

namespace GlobalTheory.DualHeight

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}

structure Anti (N L : HermLB p) (π : N.B.ι → L.B.ι) : Prop where
  le : ∀ c, N.B.U c ≤ L.B.U (π c)
  g : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) c c', r z ∈ N.B.U c → r z ∈ N.B.U c' →
    gm r z (N.B.U c ⊓ N.B.U c') (N.B.g c c') = (gm r z (L.B.U (π c) ⊓ L.B.U (π c')) (L.B.g (π c) (π c')))⁻¹
  φ : ∀ σ c, ∀ y ∈ ptsIn p σ (N.B.U c), (N.φ σ).φ c y = -(L.φ σ).φ (π c) y

theorem anti_dual (L : HermLB p) : Anti L L.dual id where
  le _ := le_rfl
  g Z r z c c' _ _ := (inv_inv _).symm.trans (congrArg (·⁻¹) (map_inv _ _).symm)
  φ σ c y _ := (neg_neg _).symm

variable {N L : HermLB p} {π : N.B.ι → L.B.ι}

theorem Anti.pull (h : Anti N L π) {q : Y ⟶ Sp k} (f : Y ⟶ X) (hf : f ≫ p = q) :
    Anti (N.pull f hf) (L.pull f hf) (fun c a => π (c a)) where
  le c y hy := mem_iInter.2 fun a => h.le _ (mem_iInter.1 hy a)
  g Z r z c c' hc hc' := (gm_pull_g _ f r z c c' hc hc').trans
    ((h.g Z (r ≫ f) z _ _ (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit)).trans
      (congrArg (·⁻¹) (gm_pull_g _ f r z (fun a => π (c a)) (fun a => π (c' a))
        (mem_iInter.2 fun a => h.le _ (mem_iInter.1 hc a))
        (mem_iInter.2 fun a => h.le _ (mem_iInter.1 hc' a))).symm))
  φ σ c y hy := ((N.φ σ).pull_φ f hf c y).trans ((h.φ σ _ _
    (mem_of_mem_linComb (m := fun _ => Points.PtsOver.map f hf _ y) (fun _ => rfl) hy PUnit.unit)).trans
      (congrArg (- ·) ((L.φ σ).pull_φ f hf (fun a => π (c a)) y).symm))

theorem Anti.pow (h : Anti N L π) (m : ℕ) : Anti (N.pow m) (L.pow m) (fun c a => π (c a)) where
  le c y hy := mem_iInter.2 fun a => h.le _ (mem_iInter.1 hy a)
  g Z r z c c' hc hc' := (gm_pow N m r z c c' hc hc').trans
    ((congrArg (· ^ m) (h.g Z r z _ _ (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit))).trans
      ((inv_pow _ _).trans (congrArg (·⁻¹) (gm_pow L m r z (fun a => π (c a)) (fun a => π (c' a))
        (mem_iInter.2 fun a => h.le _ (mem_iInter.1 hc a))
        (mem_iInter.2 fun a => h.le _ (mem_iInter.1 hc' a))).symm)))
  φ σ c y hy := ((N.φ σ).zpow_φ m c y).trans ((congrArg _ (h.φ σ _ _ (mem_pow_iff.1 hy))).trans
      ((mul_neg _ _).trans (congrArg (- ·) ((L.φ σ).zpow_φ m (fun a => π (c a)) y).symm)))

theorem Anti.chernDens (h : Anti N L π) {σ : k →+* ℂ} {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : c.chernDens (N.φ σ) y = (-1) ^ D * c.chernDens (L.φ σ) y := by
  have hi := mem_pick N.isLB y
  have hj := ptsIn_mono (h.le _) hi
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (L.B.U (π (pick N.isLB y))))
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (contDiffOn_chart (L.cInf σ _) c)
    (contDiffOn_chart (L.cInf σ _) c) (-2) (mem_over c.e hy hj)
  have e' : c.hess (N.φ σ) (pick N.isLB y) y = -c.hess (L.φ σ) (π (pick N.isLB y)) y := by
    refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) (e.trans ?_)
    · filter_upwards [(isOpen_over c.e (isOpen_ptsIn _)).mem_nhds (mem_over c.e hy hi)] with w hw
      rw [h.φ σ _ _ hw.2]
      simp only [Function.comp_apply]
      push_cast
      ring
    · rw [AlgChart.hess]
      simp only [Function.comp_apply]
      push_cast
      module
  rw [c.chernDens_eq (N.cInf σ) hy hi, c.chernDens_eq (L.cInf σ) hy hj, e', Matrix.det_neg, Fintype.card_fin]
  have : ((-1 : ℂ) ^ D) = (((-1 : ℝ) ^ D : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  ring

theorem Anti.chernPart (h : Anti N L π) (σ : k →+* ℂ) (D : ℕ) (ε : ℤˣ) :
    (N.φ σ).chernPart D ε = (L.φ σ).chernPart D (ε * (-1) ^ D) := by
  refine iSup_congr fun c => congrArg (Measure.map _) (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem c.e.open_target.measurableSet] with v hv
  simp only [Function.comp_apply]
  rw [h.chernDens c (c.e.map_target hv)]
  push_cast
  rw [mul_assoc]

theorem Anti.chernInt (h : Anti N L π) (σ : k →+* ℂ) (D : ℕ) (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (N.φ σ).chernInt D S f = (-1) ^ D * (L.φ σ).chernInt D S f := by
  simp only [Weight.chernInt, h.chernPart]
  rcases Nat.even_or_odd D with hD | hD
  · simp only [hD.neg_one_pow, mul_one, one_mul]
  · simp only [hD.neg_one_pow, mul_neg, neg_mul, mul_one, one_mul, neg_neg, neg_sub]

theorem Anti.chernIntegrableOn (h : Anti N L π) {σ : k →+* ℂ} {D : ℕ} {S : Set (CxPts p σ)} {f : CxPts p σ → ℝ}
    (H : (N.φ σ).ChernIntegrableOn D S f) : (L.φ σ).ChernIntegrableOn D S fun y => -f y := by
  simp only [Weight.ChernIntegrableOn, h.chernPart] at H
  rcases Nat.even_or_odd D with hD | hD
  · simp only [hD.neg_one_pow, mul_one] at H
    exact ⟨H.1.neg, H.2.neg⟩
  · simp only [hD.neg_one_pow, mul_neg, mul_one, neg_neg] at H
    exact ⟨H.2.neg, H.1.neg⟩

section Rat

variable [IsIntegral X] {r : L.B.ι → X.functionFieldˣ}

theorem Anti.isRatSec (h : Anti N L π) (hr : IsRatSec L.B r) : IsRatSec N.B fun c => (r (π c))⁻¹ :=
  fun c c' hc => by
  have h' : genericPoint X ∈ L.B.U (π c) ⊓ L.B.U (π c') := ⟨h.le _ hc.1, h.le _ hc.2⟩
  have e := congrArg Units.val (eq_inv_iff_mul_eq_one.1 (h.g X (𝟙 X) _ c c' hc.1 hc.2))
  rw [Units.val_mul, gm_val _ _ _ hc, gm_val _ _ _ h'] at e
  have e' : fnOf _ hc (N.B.g c c' : Γ(X, _)) * fnOf _ h' (L.B.g (π c) (π c') : Γ(X, _)) = 1 := e
  simp only [Units.val_inv_eq_inv_val]
  rw [hr _ _ h', mul_inv, eq_inv_of_mul_eq_one_left e']

theorem Anti.div (h : Anti N L π) (hr : IsRatSec L.B r) : N.div (h.isRatSec hr) = -L.div hr :=
  CartierDiv.ext_of_isEqn fun z =>
    have ⟨i, hi⟩ := exists_chart N.isLB z
    ⟨(r (π i))⁻¹, (presents_divOfRatSec _ (h.isRatSec hr)).isEqn i z hi,
      ((presents_divOfRatSec _ hr).isEqn _ z (h.le _ hi)).neg⟩

theorem mult_neg [IsLocallyNoetherian X] (D : CartierDiv X) (z : X) : (-D).mult z = -D.mult z := by
  have h₀ := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  have h₁ := CartierDiv.mult_add (-D) D z
  rw [add_zero] at h₀
  rw [neg_add_cancel] at h₁
  omega

theorem offSupp_neg (σ : k →+* ℂ) (D : CartierDiv X) : offSupp p σ (-D) = offSupp p σ D := by
  have key (E : CartierDiv X) (y : CxPts p σ) (hy : y ∈ offSupp p σ E) : y ∈ offSupp p σ (-E) :=
    mem_offSupp.2 fun h => h (by simpa using (not_not.1 (mem_offSupp.1 hy) : E.IsEqn _ 1).neg)
  exact Set.ext fun y => ⟨fun hy => by simpa using key _ y hy, key _ y⟩

theorem Anti.logNorm (h : Anti N L π) (hr : IsRatSec L.B r) {σ : k →+* ℂ} {y : CxPts p σ}
    (hy : y ∈ offSupp p σ (L.div hr)) : logNorm (N.φ σ) (fun c => (r (π c))⁻¹) y = -logNorm (L.φ σ) r y := by
  have hi := mem_pick N.isLB y
  have hj := ptsIn_mono (h.le _) hi
  have hu := hr.unitAt L.isLB hy hj
  have hu' := (h.isRatSec hr).unitAt N.isLB (by rw [← HermLB.div, h.div hr, offSupp_neg]; exact hy) hi
  have e := ratVal_mul (y := y) hu'.regAt hu.regAt
  have e₁ : ratVal (1 : X.functionField) y = 1 := by
    have := ratVal_mul (y := y) (unitAt_one _).regAt (unitAt_one _).regAt
    rw [one_mul] at this
    exact (mul_eq_left₀ (ratVal_ne_zero (unitAt_one _))).1 this.symm
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, e₁] at e
  rw [logNorm_eq (L.φ σ) hr hy hj, Cartier.logNorm, h.φ σ _ y hi, eq_inv_of_mul_eq_one_left e.symm, norm_inv,
    Real.log_inv]
  ring

end Rat

theorem topSelf_dual {D : ℕ} (hX : IsArithVar p D) (L : HermLB p) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (d : ℕ) (hd : topologicalKrullDim Z = d) :
    topSelfIntersection κ (L.dual.B.pull i) d = (-1) ^ d * topSelfIntersection κ (L.B.pull i) d := by
  have := hX.finite
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have hpr' : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have hp := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom κ Z)).2
    ⟨hpr', _, hH.pull_of_isClosedImmersion i⟩
  have HD := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := d)
    (by rw [QCoh.suppDim_structureModule, hd])
  have e := HD.interNum_of_cls_eq_zsmul (P := fun _ => L.B.pull i) (Q := fun _ => L.dual.B.pull i)
    (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull L.dual.isLB i) (fun _ => -1) fun _ => by
      have e₂ : cls L.dual.B L.dual.isLB = -cls L.B L.isLB := cls_dual L.isLB _
      rw [CechPic.cls_pull L.dual.isLB, CechPic.cls_pull L.isLB, e₂, map_neg, neg_one_zsmul]
  rw [topSelf_def, topSelf_def, e]
  simp

def cdim (x : X) : ℕ := ((topologicalKrullDim (closure {x} : Set X)).unbotD 0).toNat

theorem cdim_eq {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] {d : ℕ}
    (hd : topologicalKrullDim Z = d) : cdim (i (genericPoint Z)) = d := by
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [cdim, topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm, hd]
  rfl

theorem isArithHeight_dual {D : ℕ} (hX : IsArithVar p D) {f : X → ℝ} (H : L.IsArithHeight f) :
    L.dual.IsArithHeight fun x => (-1) ^ cdim x * f x where
  vertical Z i _ _ κ _ _ _ d hd := by
    rw [cdim_eq i hd, H.vertical Z i κ d hd, topSelf_dual hX L Z i κ d hd]
    push_cast
    ring
  point Z i _ _ _ hc hd r hr := by
    have h' := (anti_dual L).pull i rfl
    rw [cdim_eq i (d := 1) hd, H.point Z i hc hd _ (h'.isRatSec hr), HermLB.curveDeg, HermLB.curveDeg, h'.div hr,
      pow_one, neg_one_mul, neg_sub', ← finsum_neg_distrib, ← finsum_neg_distrib]
    refine congrArg₂ (· - ·) (finsum_congr fun z => ?_) (finsum_congr fun σ => ?_)
    · rw [mult_neg]
      push_cast
      ring
    · rw [← finsum_neg_distrib]
      refine finsum_congr fun y => neg_eq_iff_eq_neg.2 (h'.logNorm hr (mem_offSupp.2 ?_))
      rw [under_eq_genericPoint (hX.of_isClosedImmersion i hc hd) y]
      exact CartierDiv.genericPoint_notMem_supp _
  recursion Z i _ _ _ hc e he hd m r hr := by
    have h' := (anti_dual L).pull i rfl
    have h'' := h'.pow m
    have hZ := hX.of_isClosedImmersion i hc hd
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m _ (h''.isRatSec hr)
    unfold HermLB.ArchIntegrable at h₁
    unfold HermLB.archInt at h₂
    rw [h''.div hr] at h₁ h₂
    simp only [offSupp_neg] at h₁ h₂
    refine ⟨fun σ => (h'.chernIntegrableOn (h₁ σ)).congr (isOpen_offSupp _).measurableSet
      fun y hy => neg_eq_iff_eq_neg.2 (h''.logNorm hr hy), ?_⟩
    have hu : IsUnit ((-1 : ℝ) ^ (e + 1)) := isUnit_neg_one.pow _
    have hm {ι : Type} (g : ι → ℝ) : (-1 : ℝ) ^ (e + 1) * ∑ᶠ a, g a = ∑ᶠ a, (-1 : ℝ) ^ (e + 1) * g a :=
      mul_finsum _ _
    rw [cdim_eq i hd, mul_left_comm, h₂, mul_sub, hm, hm, HermLB.archInt]
    refine congrArg₂ (· - ·) (finsum_congr fun z => ?_) (finsum_congr fun σ => ?_)
    · rw [mult_neg]
      by_cases hz : (((L.dual.restr i).pow m).div hr).mult z = 0
      · simp [hz]
      obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      have hW := GlobalTheory.CodimOneDim.topologicalKrullDim_eq_of_coheight_eq_one k Z _ e hZ W j
        (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
      have e₁ : cdim (i (j (genericPoint W))) = e := cdim_eq (j ≫ i) hW
      rw [e₁]
      push_cast
      ring
    · rw [h'.chernInt, Weight.chernInt_congr (isOpen_offSupp _).measurableSet
        (g := fun y => (-1) * logNorm (((L.dual.restr i).pow m).φ σ) r y)
        fun y hy => (h''.logNorm hr hy).trans (neg_one_mul _).symm, Weight.chernInt_const_mul]
      have : (-1 : ℝ) ^ e * (-1) ^ e = 1 := by rw [← mul_pow]; simp
      linear_combination (((L.dual.restr i).φ σ).chernInt e (offSupp _ σ (((L.dual.restr i).pow m).div hr))
        (logNorm (((L.dual.restr i).pow m).φ σ) r)) * this

theorem isSelfInter_dual_of_isArithVar {D : ℕ} [IsIntegral X] (hX : IsArithVar p D) {x : ℝ} (h : L.IsSelfInter x) :
    L.dual.IsSelfInter ((-1) ^ (D + 1) * x) := by
  obtain ⟨f, H, rfl⟩ := h
  refine ⟨_, isArithHeight_dual hX H, ?_⟩
  have : cdim (genericPoint X) = D + 1 := cdim_eq (𝟙 X) hX.dim_eq
  simp only [this]

theorem isSelfInter_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (L : HermLB p)
    (x : ℝ), IsRegSurf p → L.IsSelfInter x → L.dual.IsSelfInter x := by
  intro k _ X p _ L x hX h
  simpa using isSelfInter_dual_of_isArithVar hX.toIsArithVar h

end GlobalTheory.DualHeight
