import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsTwExtendPowMul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RelAmpleQProj

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out TopologicalSpace

variable {Y : Scheme.{0}} {L M G : LB Y}

def secPwOne (σ : G.Sec) : (pw G 1).Sec where
  f := σ.f
  compat i j := by
    have h := σ.compat i j
    rw [← zpow_one (G.g i j)] at h
    exact h

theorem exists_sec_tw_locus [CompactSpace Y] [QuasiSeparatedSpace Y] (hM : M.IsLB) (hG : G.IsLB) (σ : G.Sec)
    (V : Y.Opens) (hV : V = nonzeroLocus σ) (r : (M.pull V.ι).Sec) :
    ∃ (k : ℕ) (u : (tw M G (k : ℤ)).Sec), V.ι ⁻¹ᵁ nonzeroLocus u = nonzeroLocus r := by
  obtain ⟨s, ⟨hs, hr⟩, -⟩ := existsUnique_secOn_of_pull M V r
  obtain ⟨k, H⟩ := exists_tw_extend_pow_mul Y G M 1 (secPwOne σ) V 0 hG hM hV inferInstance inferInstance
    (SecOn.twZeroEquiv hM hG V (GlobalTheory.LB.mkSec s hs))
  rw [show (0 : ℤ) + k * 1 = k by ring] at H
  obtain ⟨a, ha⟩ := H
  refine ⟨k, SecOn.topEquiv _ a, ?_⟩
  ext z
  obtain ⟨p, hp⟩ := exists_chart hM (V.ι z)
  obtain ⟨l, hl⟩ := exists_chart hG (V.ι z)
  have hzV : V.ι z ∈ V := z.2
  have hz : V.ι z ∈ V ⊓ (M.U p ⊓ G.U l) := ⟨hzV, hp, hl⟩
  have hz' : V.ι z ∈ M.U p ⊓ G.U l := ⟨hp, hl⟩
  have hzp : z ∈ (M.pull V.ι).U (fun _ => p) := mem_pull.2 hp
  have e := congrArg (gs V.ι z _) (ha p l)
  rw [SecOn.twCoord_twZeroEquiv, gs_res _ z _ hz, gs_mul _ z _ hz, gs_pow _ z _ hz, gs_res _ z _ hz] at e
  have e₁ : gs V.ι z _ ((SecOn.topEquiv _ a).f (p, l)) = gs V.ι z _ (SecOn.twCoord a p l) :=
    gs_res V.ι z _ hz' _
  have e₂ : gs (𝟙 _) z _ (r.f fun _ => p) = gs V.ι z _ (s p) := by
    rw [← hr, gs_appLE V.ι _ _ _ (𝟙 _) z hzp, Category.id_comp]
  have hσ : IsUnit (gs V.ι z (V ⊓ (M.U p ⊓ G.U l)) (rs Y (inf_le_right.trans inf_le_right) (σ.f l))) := by
    rw [gs_res _ z _ hz]
    exact (mem_nonzeroLocus_iff_pull σ V.ι z hl).1 (hV.le hzV)
  refine (mem_nonzeroLocus_iff_pull (SecOn.topEquiv _ a) V.ι z (k := (p, l)) hz').trans
    (Iff.trans ?_ (mem_nonzeroLocus_iff_isUnit r hzp).symm)
  rw [e₂]
  refine (iff_of_eq (congrArg IsUnit (e₁.trans e))).trans ?_
  rw [IsUnit.mul_iff]
  exact and_iff_right (hσ.pow k)

theorem exists_sec_pow_tw {m k c e : ℕ} (he : 1 ≤ e) (h : c * m = k + e) (u : (tw (lbPow L m) G (k : ℤ)).Sec)
    (σ : G.Sec) : ∃ w : (lbPow (tw L G (c : ℤ)) m).Sec, nonzeroLocus w = nonzeroLocus u ⊓ nonzeroLocus σ := by
  have le : ∀ J : PUnit → L.ι × G.ι, powChart (tw L G (c : ℤ)) J ≤
      powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2 := fun J y hy =>
    ⟨mem_powChart.2 (mem_powChart.1 hy).1, (mem_powChart.1 hy).2⟩
  let F : ∀ J : PUnit → L.ι × G.ι, Γ(Y, powChart (tw L G (c : ℤ)) J) := fun J =>
    resG Y (le J) (show Γ(Y, powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2) from
      u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
      resG Y ((le J).trans inf_le_right) (σ.f (J PUnit.unit).2) ^ e
  have hF : ∀ (y : Y) (J : PUnit → L.ι × G.ι), y ∈ powChart (tw L G (c : ℤ)) J → gs (𝟙 Y) y _ (F J) =
      gs (𝟙 Y) y _ (u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
        gs (𝟙 Y) y _ (σ.f (J PUnit.unit).2) ^ e := fun y J hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨powSecOfGerm (L := tw L G (c : ℤ)) m F fun y J J' hJ hJ' => ?_, ?_⟩
  · have e₁ := gs_compat u (𝟙 Y) y (j := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
      (j' := (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2)) (le J hJ) (le J' hJ')
    have e₂ := TwistGen.gm_tw_g (lbPow L m) G k y (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2) (le J hJ) (le J' hJ')
    have e₃ := gm_lbPow_g (L := L) m (𝟙 Y) y (fun _ => (J PUnit.unit).1) (fun _ => (J' PUnit.unit).1)
      (le J hJ).1 (le J' hJ').1
    have e₄ := TwistGen.gm_tw_g L G c y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.1 hJ) (mem_powChart.1 hJ')
    have e₅ := gs_compat σ (𝟙 Y) y (le J hJ).2 (le J' hJ').2
    dsimp only at e₂
    rw [e₃] at e₂
    refine (hF y J hJ).trans (Eq.trans ?_ (congrArg₂ (fun a b => a ^ m * b) e₄ (hF y J' hJ')).symm)
    rw [e₅]
    refine (congrArg (· * _) (e₁.trans (congrArg (· * _) e₂))).trans ?_
    simp only [Units.val_pow_eq_pow_val]
    rw [mul_pow, mul_pow, ← pow_mul, h]
    ring
  · refine nonzeroLocus_pow_eq_of _ _ (fun y hy => ?_) fun y J hJ => ?_
    · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
      exact ⟨fun _ => (p.1 PUnit.unit, p.2), mem_powChart.2 ⟨mem_powChart.1 hp.1, hp.2⟩⟩
    · refine (iff_of_eq (congrArg IsUnit (hF y J hJ))).trans ?_
      rw [IsUnit.mul_iff, isUnit_pow_iff (by omega)]
      exact and_congr (mem_nonzeroLocus_iff_isUnit u (k := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
        (le J hJ)).symm (mem_nonzeroLocus_iff_isUnit σ (le J hJ).2).symm

theorem exists_isAmpleLB_tw [CompactSpace Y] [QuasiSeparatedSpace Y] (hL : L.IsLB) (hG : G.IsLB)
    (h : ∀ y : Y, ∃ (σ : G.Sec) (V : Y.Opens), V = nonzeroLocus σ ∧ y ∈ V ∧ IsAmpleLB (L.pull V.ι)) :
    ∃ c : ℕ, IsAmpleLB (tw L G (c : ℤ)) := by
  have loc : ∀ y : Y, ∃ (m k : ℕ) (u : (tw (lbPow L m) G (k : ℤ)).Sec) (σ : G.Sec), 1 ≤ m ∧
      y ∈ nonzeroLocus u ⊓ nonzeroLocus σ ∧ IsAffineOpen (nonzeroLocus u ⊓ nonzeroLocus σ) := fun y => by
    obtain ⟨σ, V, hV, hy, hA⟩ := h y
    obtain ⟨m, hm, τ, hτ, ha⟩ := hA.exists_affine ⟨y, hy⟩
    obtain ⟨r, hr⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL m) V.ι)
      (isLB_lbPow hA.isLB m) (lbIso_lbPow_pull hL V.ι m).symm τ
    obtain ⟨k, u, hu⟩ := exists_sec_tw_locus (isLB_lbPow hL m) hG σ V hV r
    have e := hu.trans hr
    refine ⟨m, k, u, σ, hm, ⟨e.ge hτ, hV.le hy⟩, ?_⟩
    have h₁ := ha.image_of_isOpenImmersion V.ι
    rwa [← e, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm, hV] at h₁
  choose m k u σ hm hy ha using loc
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun y => nonzeroLocus (u y) ⊓ nonzeroLocus (σ y)) hy
  refine ⟨T.sup k + 1, isLB_tw hL hG _, inferInstance, fun x => ?_⟩
  obtain ⟨y, hx⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ x))
  have h₁ : k y ≤ T.sup k := Finset.le_sup y.2
  have h₂ : T.sup k + 1 ≤ (T.sup k + 1) * m y := Nat.le_mul_of_pos_right _ (hm y)
  obtain ⟨w, hw⟩ := exists_sec_pow_tw (c := T.sup k + 1) (e := (T.sup k + 1) * m y - k y) (by omega) (by omega)
    (u y) (σ y)
  exact ⟨m y, hm y, w, hw.ge hx, hw ▸ ha y⟩

theorem isProper_morphismRestrict {S : Scheme.{0}} (A : Over S) {B : LB A.left} (h : RelAmple A B) {U : S.Opens}
    (hU : IsAffineOpen U) : IsProper (A.hom ∣_ U) := by
  obtain ⟨N, -, K, s, H⟩ := h U hU
  have h₁ := isProper_of_veryAmpleBy
    ((ProjSpace.veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom s).2 H)
  exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).1 h₁

theorem isProper_and_exists_isAmpleLB {S : Scheme.{0}} (A : Over S) {B : LB A.left} (hB : B.IsLB)
    (h : RelAmple A B) {H : LB S} (hH : IsAmpleLB H) : IsProper A.hom ∧ ∃ N : LB A.left, IsAmpleLB N := by
  obtain ⟨n, -, c, s, hs, ha⟩ := hH.exists_cover
  have hp : IsProper A.hom := IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) _ hs
    fun i => isProper_morphismRestrict A h (ha i)
  have := hH.compactSpace
  have := hH.quasiSeparatedSpace
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  obtain ⟨d, hd⟩ := exists_isAmpleLB_tw hB (LB.isLB_pull (isLB_lbPow hH.isLB n) A.hom) fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ (A.hom y)))
    exact ⟨secPull (s i) A.hom, _, (nonzeroLocus_secPull _ _).symm, hi, isAmpleLB_of_relAmple A hB h _ (ha i)⟩
  exact ⟨hp, _, hd⟩

theorem isQProjOver_of_relAmple : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  rintro K _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProj
