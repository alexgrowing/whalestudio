import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjConjNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PtHomInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

theorem sum_section {M Q : Type} [AddCommGroup M] [AddCommGroup Q] [Fintype Q] (π : M →+ Q) (Z : Q → M) (hZ : ∀ q, π (Z q) = q)
    (χ : M → ℂ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hker : ∀ x, π x = 0 → χ x = 1) {m : M} (hm : χ m ≠ 1) :
    ∑ q, χ (Z q) = 0 := by
  have h1 : ∀ q, χ (Z (q + π m)) = χ m * χ (Z q) := fun q => by
    have e : Z (q + π m) = (Z (q + π m) - (m + Z q)) + (m + Z q) := by abel
    rw [e, hadd, hker _ (by rw [map_sub, map_add, hZ, hZ]; abel), one_mul, hadd]
  have h2 : ∑ q, χ (Z q) = χ m * ∑ q, χ (Z q) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (π m)) (fun q => χ (Z q))]
    exact Finset.sum_congr rfl fun q _ => h1 q
  have h3 : (χ m - 1) * ∑ q, χ (Z q) = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hm)

variable {D : D7}

theorem pt_mem_iff {δ : ℂ} {a d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) (y : VC D a d) :
    y ∈ La D (tor0 D ⊤ δ) L L' ↔ ∃ z ∈ YYl D L L', GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d z = y := by
  constructor
  · intro hy
    have h : La D (tor0 D ⊤ δ) L L' ≤ (YYl D L L').toAddSubgroup.map (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d) := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨w, hw, A, hA, rfl⟩
      obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
      exact ⟨((c : D.host.K) : D.host.E) • A, (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) hA,
        GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
    exact h hy
  · rintro ⟨z, hz, rfl⟩
    exact AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, z, hz, rfl⟩

theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type} (s : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) : Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add ih

theorem reads_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1
      ((κ * ζ) • ((Real.sqrt ((Ideal.absNorm (D.host.conj • modul P c) : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • modul P c) d)) e0)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) := by
  intro D ψ θ S T a d hS hT δ hcc hset LS LT hLS hLT hSd hTd e P c he _ κ e0 vac he0 hread hvac Tm hTm
  subst hS hT
  have hc := hset.crv
  have hψ := hset.std
  have gS := hset.gS
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hne := conj_ne_bot P c
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ hc _ hne
    (by rw [conj_conj_smul]; exact isCoprime_conj he.1 c) S.rank T.rank
  have hN0 : 0 < Ideal.absNorm (D.host.conj • modul P c) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hne)
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacMove.sd_of_moves (GlobalTheory.NormSum.VacMove.moves_one D S.rank),
      GlobalTheory.SkewLatSD.skewLat_sd D _ T.rank hne, rfl⟩
  obtain ⟨-, -, hIm, -, -, -, hq⟩ := GlobalTheory.ThetaLine.theta_line D hG ⊤ δ hc S.rank T.rank _ kp
  have hrep := GlobalTheory.ThetaConj.repInd_of_thSp D _ _ _ (La0 D (tor0 D ⊤ δ) S.rank T.rank) _ e0 hq
    (fun x hx y hy => hIm _ (GlobalTheory.GalTheta.weilElement_smul_mem_thetaLattice D hG ⊤ δ _ _ x hx) y hy) he0
  have hmem0 := pt_mem_iff (δ := δ) (stdL D S.rank) (stdL D T.rank)
  have hmem2 := pt_mem_iff (δ := δ) (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)
  have hinj := GlobalTheory.ThetaLatticePoints.ptHom_injective D ⊤ (delta_ne_zero hc) S.rank T.rank
  have hkI := fun t ht htΛ hk => inId_of_kill hψ hcc gS hLS hLT hSd hTd he c (t := t) ht htΛ hk
  have hsm := fun z hz => smul_finRat_mem hψ hcc gS hLS hLT hSd hTd P c (z := z) hz
  have hhalf := fun z hz => heisO_eq_half hψ hcc gS hLS hLT hSd hTd he.1 c hvac (z := z) hz
  have hsk := fun z hz m hm => smul_skew_mem (conj_conj_ne_bot P c) (a := S.rank) (d := T.rank) (z := z) hz (m := m) hm
  rw [conj_conj_smul] at hsk
  set I := D.host.conj • modul P c with hI
  set p := GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ S.rank T.rank with hp
  set Y := YYl D (stdL D S.rank) (skewLat D I T.rank) with hY
  set A₁ := La0 D (tor0 D ⊤ δ) S.rank T.rank with hA₁
  set A₂ := La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D I T.rank) with hA₂
  haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofFinite _
  have hcard : Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) = Ideal.absNorm I ^ (S.rank * T.rank) := by
    rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  obtain ⟨m, hm, u, hmu⟩ := exists_add_two he c
  have hz : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, ∃ z ∈ Y, ((Quotient.out q : A₂) : VC D S.rank T.rank) - p (2 • z) ∈ A₁ := fun q => by
    obtain ⟨z, hz, ez⟩ := (hmem2 _).1 (Quotient.out q).2
    refine ⟨u • z, Y.smul_mem u hz, (hmem0 _).2 ⟨m • z, hsk z hz m hm, ?_⟩⟩
    rw [← ez, ← map_sub, two_nsmul, ← add_smul, ← mul_two, eq_sub_of_add_eq hmu, sub_smul, one_smul]
  choose z hzY hzq using hz
  have hp2 : ∀ w ∈ Y, p w ∈ A₂ := fun w hw => (hmem2 _).2 ⟨w, hw, rfl⟩
  let π : Y →+ A₂ ⧸ A₁.addSubgroupOf A₂ := (QuotientAddGroup.mk' _).comp
    ((p.comp Y.toAddSubgroup.subtype).codRestrict A₂ fun w => hp2 w w.2)
  have hπ : ∀ q, π ⟨2 • z q, nsmul_mem (hzY q) 2⟩ = q := fun q => by
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    refine QuotientAddGroup.eq.2 ?_
    rw [AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
    exact hzq q
  have hπ0 : ∀ w : Y, π w = 0 → GlobalTheory.VacUnique.finRat S T (-w.1) ∈ latO S T LS LT (fun _ => True) := fun w hw => by
    obtain ⟨w', hw', ew⟩ := (hmem0 (p w.1)).1
      ((QuotientAddGroup.eq_zero_iff (N := A₁.addSubgroupOf A₂) (⟨p w.1, hp2 w w.2⟩ : A₂)).1 hw)
    rw [finRat_mem_iff hψ hcc gS hLS hLT hSd hTd, ← hinj ew]
    exact neg_mem hw'
  have hn : ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hfun : cosetFn (cA D e) I (0 : WO S T) = ∑ q, ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ • fun t =>
      ψ (symplO S T t (e • GlobalTheory.VacUnique.finRat S T (2 • -z q))) * halfInd (cA D e) (latO S T LS LT fun _ => True) t := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp only [cosetFn, halfInd, Matrix.zero_apply, sub_zero]
    by_cases h1 : t ∈ latO S T LS LT (fun _ => True) ∧ IsHalf (cA D e) t
    · have e1 : ∀ y, symplO S T t (e • y) = symplO S T t y := fun y => by
        rw [← cA_cA e, ← GlobalTheory.PlaceModel.symplO_smul, (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 h1.2)]
      simp only [e1]
      rw [if_pos h1, mul_one]
      by_cases h2 : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j))
      · rw [if_pos ⟨h1.2, h2⟩, Finset.sum_congr rfl fun q _ =>
          kill_of_inId hψ hcc hLS hLT hSd hTd he h1.2 h2 (hsm _ (nsmul_mem (neg_mem (hzY q)) 2)),
          Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hn]
      · rw [if_neg fun h => h2 h.2]
        obtain ⟨w, hw, hw1⟩ : ∃ w ∈ Y, ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T w)) ≠ 1 := by
          by_contra h
          push_neg at h
          exact h2 (hkI t h1.2 h1.1 h)
        have h3 := sum_section π (fun q => ⟨2 • z q, nsmul_mem (hzY q) 2⟩) hπ
          (fun w => ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T (-w.1))))
          (fun x y => by
            rw [Submodule.coe_add, neg_add, map_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
          (fun x hx => GlobalTheory.LatVac.char_sympl_eq_one hψ hSd hTd h1.1 (hπ0 x hx)) (m := ⟨-w, neg_mem hw⟩)
          (by simpa only [neg_neg] using hw1)
        simp only [smul_neg]
        rw [h3, mul_zero]
    · rw [if_neg h1, mul_zero, mul_zero, if_neg fun h => h1 ⟨(half_mem_iff hcc hLS hLT hSd hTd he t h.1).2 fun i j => (h.2 i j).1, h.1⟩]
  have hv : Tm (halfInd (cA D e) (latO S T LS LT fun _ => True)) = vac := by simpa using hTm.vac
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he.1
  have hTmΦ : Tm (cosetFn (cA D e) I 0) = ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ •
      ∑ q, heisO ψ S T (finPt rfl rfl 1 (2 • z q)) vac := by
    rw [hfun, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) 1 (2 • z q) = GlobalTheory.VacUnique.finRat S T (2 • -z q) := by
      unfold finPt
      congr 1
      refine Matrix.ext fun i j => ?_
      simp
    rw [map_smul, hTm.modul _ (GlobalTheory.isSBHalf_halfInd _ _) _ (fun i j => by
      change cA D (cA D e) * (e * _) = e * _
      rw [cA_cA, ← mul_assoc, hee]), hv, hhalf _ (neg_mem (hzY q)), e1]
  have hR := (reads_sum Finset.univ _ _ fun q =>
    heisO_finPt_reads ψ θ S T rfl rfl ⊤ δ 1 hset _ _ hread (2 • z q)).smul ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹
  refine ⟨1, IsRootOne.one, ?_⟩
  rw [hTmΦ]
  convert hR using 1
  have hU : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, ∀ y, al D (tor0 D ⊤ δ) ((Quotient.out q : A₂) : VC D S.rank T.rank) *
      U D (tor0 D ⊤ δ) ((Quotient.out q : A₂) : VC D S.rank T.rank) e0 y =
        U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (2 • z q)) e0 y := fun q y => by
    have h1 := congrFun (hrep _ (Quotient.out q).2 _ (hp2 _ (nsmul_mem (hzY q) 2)) (hzq q)) y
    obtain ⟨k, hk⟩ := hq _ (hp2 _ (hzY q))
    have h2 : al D (tor0 D ⊤ δ) (p (2 • z q)) = 1 := by
      rw [GlobalTheory.ThetaConj.al_of_qH D _ _ (2 * (2 * k)) (by
        rw [map_nsmul, GlobalTheory.NormSum.Expand.qH_nsmul, hk]; push_cast; ring), zpow_mul]
      norm_num
    simp only [GlobalTheory.ThetaConj.aU, h2, one_mul] at h1
    exact h1
  have hs : ((Real.sqrt ((Ideal.absNorm I : ℝ) ^ (S.rank * T.rank)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℝ)) : ℂ))⁻¹ =
        ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ := by
    have h1 : (((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℝ)) = (Ideal.absNorm I : ℝ) ^ (S.rank * T.rank) := by
      push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, Iop, finsum_eq_sum_of_fintype, hidx, hU, Finset.sum_apply]
  rw [← hs]
  simp only [U, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

end GlobalTheory.SkewLevel

end
