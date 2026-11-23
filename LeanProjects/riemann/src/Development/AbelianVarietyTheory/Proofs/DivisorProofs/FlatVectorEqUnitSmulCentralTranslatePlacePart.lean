import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSplittingCharacterUnitOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralUniformiserActsByDilationTameKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelVectorUnitMulDilatedFlat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepCentralActsByDilationUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqUnitMulCentralTranslateLiftVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsCentAtScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorIdempotentSumVacuumNormalisedSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelTypePlaceThetaVectorLatticeFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjHalfCosetRepsScalarDilationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHeisenbergTranslatesBaseVectorEqCardSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterConjHalfIdeleEqProdLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilatedFlatDatumIsSBHalfTameKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftDatumConjugateHalfFiniteFourierSumStatement
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.PartFlat

open GlobalTheory.BaseCmp GlobalTheory.OnCmp Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas

theorem idem_mul_of_subset {D : D7} {P Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) (h : P ⊆ Q) : idem Q * idem P = idem P := by
  have k : ∀ l ∈ Q, idemAt l * idem Q = idemAt l := fun l hl =>
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hQ.isIdemAt ha).1) (fun a ha b hb hab => hQ.mul_eq_zero ha hb hab) hl
  conv_lhs => rw [show idem P = ∑ PP ∈ P, idemAt PP from rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l hl => by rw [mul_comm, k l (h hl)]

theorem isHalf_mono {D : D7} {m n : ℕ} {a b : AE D} (hab : b * a = a) {u : Mx D m n} (hu : IsHalf a u) : IsHalf b u := by
  intro k l
  rw [← hu k l, ← mul_assoc, hab]

theorem suppAt_mono {D : D7} {V : HSp D} {a b : AE D} (hab : b * a = a) (ha : a * cA D a = 0) (hb : b * cA D b = 0)
    {g : GA D V} (hg : SuppAt a V g) : SuppAt b V g := by
  intro k l
  have hc : cA D b * cA D a = cA D a := by rw [← map_mul, hab]
  have h1 : b * cA D a = 0 := by rw [← hc, ← mul_assoc, hb, zero_mul]
  have h2 : cA D b * a = 0 := by rw [← hab, ← mul_assoc, mul_comm (cA D b), hb, zero_mul]
  have e : (b + cA D b) * (a + cA D a) = a + cA D a := by linear_combination hab + hc + h1 + h2
  rw [← hg k l, ← mul_assoc, e]

open GlobalTheory.ChiUnit GlobalTheory.DilChi in

theorem chi_unitOff_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (i : Fin D.R.m) (t : T0) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eQ : AE D) (heQ : IsIdemSum eQ Q) (ϖ : 𝓞 D.host.E)
    (hϖ0 : (ϖ : D.host.E) ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) (z : GA D (Vc D i))
    (hz : mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) +
      (1 - eQ - cA D eQ))) (x : (AE D)ˣ) (hx : IsDetAt (cA D eQ) (Vc D i) z x) :
    UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  have hchr := hK.chr
  have hfin := hK.fin
  have hpl := fun P (hP : P ∈ Q) => hK.pl P (hQ hP)
  generalize R.xi t = χ at hchr ⊢
  generalize R.xiH t = ξ at hchr hfin
  show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _
  have hlev := hC.lev
  have hs0 : star ((ϖ : 𝓞 D.host.E) : D.host.E) ≠ 0 := by simpa using hϖ0
  set u : D.host.Eˣ := Units.mk0 _ hs0 with hu
  have hxl : (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (((u ^ (Vc D i).rank : D.host.Eˣ)) : D.host.E) := by
    rw [detIdele_eq_locE D (Vc D i) Q eQ heQ _ z hz x hx, Units.val_pow_eq_pow_val]; rfl
  have hval : ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ →
      ((c x : Circle) : ℂ) = ∏ P ∈ Q, (((ψ.locK (conjPl P) u : ℂˣ) : ℂ)) ^ (Vc D i).rank := by
    intro c ψ hc
    rw [GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local D Q eQ heQ (u ^ (Vc D i).rank) x hxl c ψ hc]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
  have e : ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) =
      (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((χ x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹ := by
    simp only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [e, hval _ _ (hlev.mu0 i), hval _ _ hchr, hval _ _ hlev.eta]
  have hb : ∀ P ∈ Q, Formalism.L2.DIV.starO ϖ ∈ (conjPl P).asIdeal ∧ Formalism.L2.DIV.starO ϖ ∉ (conjPl P).asIdeal ^ 2 := fun P hP =>
    ⟨(conjO_mem_conjPl P ϖ).2 (hϖ P hP).1, conjO_not_mem_sq (hϖ P hP).2⟩
  have hNc : ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := fun P hP => (natCast_mem_conjPl P N).2 (hNQ P hP)
  have hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt (conjPl P) := fun P hP => by
    obtain ⟨⟨q, hq, hqc, -, hqg⟩, -⟩ := hpl P hP
    have hqm : (q : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
      rw [natCast_mem_conjPl, ← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)
    exact (R.C.isMu0 i).unr (conjPl P) fun k hk =>
      not_mem_of_prime_ne (conjPl P) (D.host.g_prime k) hq (hqg k) hqm hk
  have hcoe : (u : D.host.E) = ((Formalism.L2.DIV.starO ϖ : 𝓞 D.host.E) : D.host.E) := by rw [Formalism.L2.DIV.starO_coe]; rfl
  obtain ⟨nμ, -, hnμ⟩ := (R.C.isMu0 i).inf
  obtain ⟨n, hn, hnx⟩ := hfin
  refine unitOff_inv (unitOff_mul (unitOff_mul (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)
    (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)) (unitOff_inv (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)))
  · rw [locK_eq_val _ (hunr P hP) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ (conjPl P) _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr)
      (R.C.isMu0 i).tame (hunr P hP) (hNc P hP)
  · refine unitOff_of_pow_eq_one _ hn ?_
    have h := LR ξ n hnx (conjPl P) u
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  · rw [locK_eq_val _ (R.C.isEta.unr (conjPl P)) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ (conjPl P) _ R.C.isEta.inf
      (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy)
      (R.C.isEta.unr (conjPl P)) (hNc P hP)

theorem splitSet_tuple {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (i : Fin D.R.m) (t : T0) : SplitSet (R.Q t) := by
  obtain ⟨-, e, he, -⟩ := (kerDat_tuple (i := i) hC.lev hC.thP t).vec
  exact SplitSet.mono ⟨e, he⟩ (by convert Finset.subset_union_right)

theorem dil_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hQG : QGuard R) (i : Fin D.R.m) (t : T0) (hV : VStd D i) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ) (hN : N ≠ 0)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ) (heg : IsIdemSum eg R.Pg)
    (heQ : IsIdemSum eQ Q) (hfg : IsTypeVec R i eg fg) (ϖ : 𝓞 D.host.E)
    (hϖ0 : (ϖ : D.host.E) ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) (z : GA D (Vc D i))
    (hz : mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) +
      (1 - eQ - cA D eQ))) :
    SuppAt eQ (Vc D i) z ∧ ∃ κ : ℂ, UnitOff N κ ∧ ∀ Tm, IsModel R i eQ fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ,
      IsSBHalf eQ (lattice₂ R i) Ψ → R.ωP i t (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (dil i (ϖ : D.host.E)⁻¹ x)) := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  have hsp := splitSet_tuple hC i t
  have hsub : idem (R.Q t) * eQ = eQ := by rw [← idem_eq heQ]; exact idem_mul_of_subset hsp hQ
  have hsubc : cA D (idem (R.Q t)) * cA D eQ = cA D eQ := by rw [← map_mul, hsub]
  obtain ⟨hSV, hSW, hθ, hfix0⟩ := GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed D G Pl0 T0 A Ks R F hC hQG i hV _ _ _ _ _ _ hK ⟨t, subset_rfl⟩ eg
    (idem (R.Q t)) fg heg hsp.isIdemSum hfg
  have hfix : ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) →
      heisO R.ψ (Vc D i) (Wc D i) u fg = fg := fun u hu h =>
    hfix0 u hu (h.imp (isHalf_mono hsub) (isHalf_mono hsubc))
  have hW := hK.weil
  obtain ⟨hsupp, ⟨x, hx⟩, hpull, hsb, hlat⟩ :=
    GlobalTheory.T.scalarDilationElement_support_det_pullback D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  obtain ⟨Rr, hR1, hR2, hR3, hRc⟩ :=
    GlobalTheory.T.exists_conjHalf_cosetReps_scalarDilation D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  have hchi := chi_unitOff_part hC i t Q hQ N hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  refine ⟨hsupp, (((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ), unitOff_mul' hchi hRc, fun Tm hTm Ψ hΨ => ?_⟩
  have hom := GlobalTheory.T.weilOperator_idempotentSum_vacuum_normalised_sum D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z x hsupp hx Rr hR1 hR2 hR3
    fg hθ hfix
  have hsum := GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z hlat Rr hR1 hR2 hR3 fg Tm hTm
  have hvac : R.ωP i t (z, 1) fg = (((((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ)) •
      Tm (actPull (z, (1 : GA D (Wc D i))) (halfInd eQ (latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i)))) := by
    rw [hom, hsum, smul_smul]
    congr 1
    have hs : ((Rr.card : ℕ) : ℂ) = ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    rw [hs]
    simp only [splitFacO, map_one, mul_one, Circle.coe_mul, Circle.coe_inv]
    by_cases h0 : ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) = 0
    · rw [h0]; simp
    · field_simp
  have h := GlobalTheory.T.weilRep_apply_eq_smul_of_halfIndicator_base D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ fg hθ hfix Tm hTm (z, 1) _ hsb hvac
    Ψ hΨ
  rw [h, hpull Ψ hΨ.1]

theorem lift_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hG : QGuard R) (i : Fin D.R.m) (t : T0) (hV : VStd D i) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ) (hN : N ≠ 0)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ)
    (hq : IsIdemSum eQ Q) (ϖ : 𝓞 D.host.E) (hϖ0 : ϖ ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) :
    ∃ Gc : ℂ, UnitOff N Gc ∧ IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) ∧
      ∀ Tm, IsModel R i eQ fg Tm → ∀ φ, ThAt R i (cA D eQ) fg (adjDat R i Q (R.xiR t) (cA D eQ)) φ →
        φ = Tm (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  obtain ⟨Y, a, Gc, hU, hY, hΦ, hS⟩ := GlobalTheory.T.lift_datum_conjugate_half_finite_fourier_sum D G Pl0 T0 A Ks R F hC hG i hV (R.xiR t) Q ⟨t, hQ⟩
    (fun PP hP => kerDat_xiR_ne D G Pl0 T0 A Ks R F hC i _ _ _ _ _ _ hK PP (hQ hP)) N hN hNQ eQ hq ϖ hϖ0 hϖ
  refine ⟨Gc, hU, GlobalTheory.T.dilatedFlatDatum_isSBHalf_tameKernel D G Pl0 T0 A Ks R F hC hG i hV (R.xiR t) Q ⟨t, hQ⟩ eQ hq ϖ hϖ0 hϖ Gc, fun Tm hTm φ hθ => ?_⟩
  have h1 := GlobalTheory.DatumFourier.thetaAt_eq_sum (fun q : Y => q.1) (fun q : Y => a q.1) hθ
    (fun q => by rw [GlobalTheory.LatVac.cA_cA]; exact hY q.1 q.2)
    (fun s => by
      refine (hΦ s).trans ?_
      congr 1; exact (Finset.sum_coe_sort Y fun y => a y * R.ψ (symplO (Vc D i) (Wc D i) s y)).symm)
  have h2 : (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) =
      ∑ y ∈ Y, a y • fun s => halfInd eQ (lattice₂ R i) (s + y) := by
    funext s
    rw [← hS s, Finset.sum_apply]
    rfl
  have hvac : Tm (halfInd eQ (lattice₂ R i)) = fg := by simpa using hTm.vac
  rw [h1, h2, map_sum, ← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hTm.trans _ (GlobalTheory.isSBHalf_halfInd eQ (lattice₂ R i)) _ (hY q.1 q.2), hvac]

theorem flat_eq_unit_smul_om_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa : Finset (Pl D.host.E)), Sa ⊆ R.Q t → ∀ (eg ea : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt ea (Vc D i) z ∧ SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ ∀ h g, ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i Sa (R.xiR t) ea) h → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) g → h = c • R.ωP i t (z⁻¹, 1) g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV Sa hSa eg ea fg heg hea hfg
  obtain ⟨ϖ, hϖ0, hϖ⟩ := GlobalTheory.FlatLift.exists_unif D.host.E Sa
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, -, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i Sa ea hea (ϖ : D.host.E) hϖE
  have hN : GlobalTheory.TwistField.tupPrime R t ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
    exact GlobalTheory.TupDil.card_ne_zero PP
  have hNQ : ∀ PP ∈ Sa, ((GlobalTheory.TwistField.tupPrime R t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ GlobalTheory.TwistField.tupPrime R t :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) (hSa hPP))
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.TupDil.card_mem PP)
  obtain ⟨hsupp, κ, hκ, hact⟩ := dil_part hC hQG i t hV Sa hSa _ hN hNQ eg ea fg heg hea hfg ϖ hϖE hϖ z hzm
  obtain ⟨Gc, hG, hSB, hvP⟩ := lift_part hC hQG i t hV Sa hSa _ hN hNQ ea fg hea ϖ hϖ0 hϖ
  have hsp := splitSet_tuple hC i t
  have hsub : idem (R.Q t) * ea = ea := by rw [← idem_eq hea]; exact idem_mul_of_subset hsp hSa
  have hsi := GlobalTheory.SplitHecke.Stab.suppAt_inv hsupp
  refine ⟨z⁻¹, (κ * Gc)⁻¹, hsi, suppAt_mono hsub hea.2 hsp.isIdemSum.2 hsi, GlobalTheory.FlatLift.unitOff_inv_mul hκ hG,
    fun h g hh hg => ?_⟩
  obtain ⟨Tm, hTm⟩ := hh.1
  have hfT := hh.2 Tm hTm
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ.1 hG.1
  have hcomp : ∀ x : WO (Vc D i) (Wc D i), dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x) = x := by
    intro x
    ext a b
    simp only [dil, Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  rw [inv_inv, hvP Tm hTm g hg, hact Tm hTm _ hSB]
  simp only [hcomp]
  have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * flatDat R i Sa (R.xiR t) ea x) = Gc • flatDat R i Sa (R.xiR t) ea := rfl
  rw [hsm, map_smul, ← hfT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.PartFlat
