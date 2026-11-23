import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealIndicatorReadsNormPowMulIntertwinedVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.CosRead

open scoped TensorProduct nonZeroDivisors
open GlobalTheory.LatVac GlobalTheory.IopRead
open Formalism.L2.DIV (starO starO_coe)
open Formalism.MainNotions.TaylorLogMetric (U)
open Formalism.MainNotions.StandardLatticesGL3 (KLat)
open GlobalTheory.SkewIndex (skewEnt)
open GlobalTheory.ThetaLatticePoints (ptHom)

variable {D : D7}

private theorem one_mem_inverse_halfDifferent (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  have hb0 := bb_ne_zero D
  refine (show (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ D.host.AA0 from ?_) (FractionalIdeal.one_mem_one _)
  rw [Formalism.BasicNotions.Host.AA0, ← one_div, FractionalIdeal.le_div_iff_mul_le hb0, one_mul]
  exact FractionalIdeal.coeIdeal_le_one

private theorem mem_skewEnt {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {b : 𝓞 D.host.E} (hb : b ∈ 𝔪) :
    (b : D.host.E) ∈ skewEnt D 𝔪 := by
  have hn0 := GlobalTheory.SkewLatSelfDual.coe_ne_zero (GlobalTheory.SkewLatSelfDual.conj_smul_ne_bot h𝔪)
  have hle : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ skewEnt D 𝔪 := by
    rw [skewEnt, FractionalIdeal.le_div_iff_mul_le hn0]
    simpa using mul_le_mul' (le_refl (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))
      (FractionalIdeal.coeIdeal_le_one (I := D.host.conj • 𝔪))
  exact hle (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 D.host.E)⁰ hb)

private theorem mem_skewMat {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : IsIntE z) {c : 𝓞 D.host.E} (hc : c ∈ 𝔪) : (c : D.host.E) • z ∈ skewMat D 𝔪 a d := fun i j => by
  obtain ⟨b, hb⟩ := hz i j
  have h := FractionalIdeal.mul_mem_mul (one_mem_inverse_halfDifferent D) (mem_skewEnt h𝔪 (𝔪.mul_mem_right b hc))
  rw [one_mul] at h
  rw [Matrix.smul_apply, smul_eq_mul, hb]
  exact h

private theorem mem_stdMat {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E} (hz : IsIntE z) :
    z ∈ stdMat D a d := fun i j => by
  obtain ⟨b, hb⟩ := hz i j
  have h := Submodule.smul_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) b (one_mem_inverse_halfDifferent D)
  rw [Algebra.smul_def, mul_one] at h
  rw [hb]
  exact h

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {δ : ℂ}

private theorem cosInd_zero (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) (t : WO S T) :
    cosInd e 𝔪 rfl rfl 0 t = if IsHalf e t ∧ ∀ i j, toEAf D (t i j) ∈ idGrp 𝔪 then 1 else 0 := by
  simp only [cosInd, Matrix.zero_apply, RingHom.map_zero, mul_zero, sub_zero, inId_iff]

private theorem half_add {e : AE D} {u : WO S T} (hue : IsHalf e u) (t : WO S T) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [GlobalTheory.PlaceModel.isHalf_iff, GlobalTheory.PlaceModel.isHalf_iff]
  exact add_mem_cancel_right ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hue)

set_option maxHeartbeats 800000 in
private theorem sb_cosInd (hc : D.host.ccK = ⊤) (hS : S.gram = 1) {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) :
    IsSBHalf e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) (cosInd e 𝔪 rfl rfl 0) := by
  have h𝔪 := h.ne_bot
  have hn0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hnm := Ideal.absNorm_mem 𝔪
  generalize Ideal.absNorm 𝔪 = n at hn0 hnm
  have hsupp : ∀ t : WO S T, cosInd e 𝔪 rfl rfl 0 t ≠ 0 → IsHalf e t ∧ ∀ i j, toEAf D (t i j) ∈ idGrp 𝔪 := fun t ht => by
    by_contra hh
    exact ht (by rw [cosInd_zero, if_neg hh])
  refine ⟨fun t ht => (hsupp t ht).1, n, hn0, fun u hu hue t => ?_, fun t ht => nsmul_mem ?_ _⟩
  · have h1 : n • u ∈ latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
        (skewLat D 𝔪 T.rank : Set (Fin T.rank → D.host.E)) fun _ => True := by
      refine latO_induction (p := fun u => n • u ∈ latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
        (skewLat D 𝔪 T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) ?_ ?_ ?_ ?_ hu
      · intro α hα M hM
        have h2 : n • M ∈ latRat S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
            (skewLat D 𝔪 T.rank : Set (Fin T.rank → D.host.E)) := by
          refine (mem_latRat_iff hc hS (GlobalTheory.SkewLatSelfDual.mem_skewLat (𝔪 := 𝔪)) _).2 fun i j => ?_
          have h3 := (mem_latRat_iff hc hS mem_stdL M).1 hM i j
          rw [mul_one] at h3
          have h4 := FractionalIdeal.mul_mem_mul h3 (mem_skewEnt h𝔪 hnm)
          rw [Matrix.smul_apply, nsmul_eq_mul, mul_comm (n : D.host.E)]
          exact h4
        have h5 : finTens α (n • M) = n • finTens α M := by
          clear h2 hnm hn0
          induction n with
          | zero => rw [zero_nsmul, zero_nsmul, finTens_zero]
          | succ k ih => rw [succ_nsmul, succ_nsmul, finTens_add, ih]
        rw [← h5]
        exact finTens_mem_latO hα h2
      · rw [smul_zero]; exact zero_mem _
      · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
      · intro x hx; rw [smul_neg]; exact neg_mem hx
    have h6 : IsHalf e (n • u) :=
      (GlobalTheory.PlaceModel.isHalf_iff S T).2 (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hue) n)
    have h7 : ∀ i j, toEAf D ((t + n • u) i j) ∈ idGrp 𝔪 ↔ toEAf D (t i j) ∈ idGrp 𝔪 := fun i j => by
      have := inId_of_mem hc hS h h1 i j
      rw [h6 i j] at this
      rw [Matrix.add_apply, RingHom.map_add]
      exact add_mem_cancel_right this
    rw [cosInd_zero, cosInd_zero]
    simp only [half_add h6, h7]
  · obtain ⟨ht1, ht2⟩ := hsupp t ht
    have h0 : ∀ i j, infPart D (t i j) = 0 := fun i j => by
      obtain ⟨SS, c, he, -⟩ := h
      rw [← ht1 i j, RingHom.map_mul, (GlobalTheory.IdemSumIdeal.isIdemSum_props e SS c he).1, zero_mul]
    exact mem_of_inId hc hS mem_stdL FractionalIdeal.coeIdeal_le_one h0 ht2

set_option maxHeartbeats 1600000 in

private theorem fix_deep (hc : D.host.ccK = ⊤) (hs : Setup ψ θ S T ⊤ δ 1) {v : WO S T → ℂ}
    (hv : IsLatVac (heisO ψ S T) (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) v)
    {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm)
    {l : WO S T} (hl : l ∈ latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) :
    heisO ψ S T (2 • (Ideal.absNorm 𝔪 • l)) (Tm (cosInd e 𝔪 rfl rfl 0)) = Tm (cosInd e 𝔪 rfl rfl 0) := by
  have h𝔪 := h.ne_bot
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ hs.crv 𝔪 h𝔪 (coprime_conj h) S.rank T.rank
  have hB := GlobalTheory.SkewIndex.La_skew_eq_map D δ 𝔪 S.rank T.rank
  have hA := La0_eq (D := D) δ S.rank T.rank
  have hn : 0 < Ideal.absNorm 𝔪 ^ (S.rank * T.rank) :=
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)) _
  generalize La0 D (tor0 D ⊤ δ) S.rank T.rank = A at hidx hA
  generalize La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D 𝔪 T.rank) = B at hidx hB
  generalize Ideal.absNorm 𝔪 ^ (S.rank * T.rank) = N at hidx hn
  have hnm := Ideal.absNorm_mem 𝔪
  generalize Ideal.absNorm 𝔪 = n at hnm ⊢
  have hnc : (n : 𝓞 D.host.E) ∈ D.host.conj • 𝔪 := by
    have := starO_mem_conj hnm
    rwa [show starO (n : 𝓞 D.host.E) = n from map_natCast Formalism.L2.DIV.starOHom n] at this
  haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero (by
    change (A.addSubgroupOf B).index ≠ 0
    rw [hidx]; exact hn.ne')
  haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
  choose z hz hz' using fun q : B ⧸ A.addSubgroupOf B => hB.le (Quotient.out q : B).2
  have hee : cA D e * cA D e = cA D e := by
    obtain ⟨SS, c, he, -⟩ := h
    rw [← RingHom.map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hce : finPart D (cA D e) ∈ intAE D := by
    obtain ⟨SS, c, he, -⟩ := h
    rw [Formalism.IndefR.Fin.finPart_cA]
    exact Formalism.IndefR.Fin.cF_int (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.IdemSumIdeal.isIdemSum_props e SS c he).2.1)
  have hSB : IsSBHalf e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) (halfInd e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True)) := by
    refine ⟨fun t ht => ?_, 1, one_pos, fun u hu hue t => ?_, fun t ht => ?_⟩
    · by_contra hh
      exact ht (if_neg fun h' => hh h'.2)
    · simp only [one_smul, halfInd, add_mem_cancel_right hu, half_add hue]
    · rw [one_smul]
      by_contra hh
      exact ht (if_neg fun h' => hh h'.1)
  have hvac := hTm.vac
  rw [one_smul] at hvac
  have hT : ∑ q, heisO ψ S T (cA D e • finTens 1 (-z q)) v =
      (Fintype.card (B ⧸ A.addSubgroupOf B) : ℂ) • Tm (cosInd e 𝔪 rfl rfl 0) := by
    rw [← map_smul, show (Fintype.card (B ⧸ A.addSubgroupOf B) : ℂ) • cosInd e 𝔪 rfl rfl 0 =
      ∑ q, fun t => ψ (symplO S T t (cA D e • finTens 1 (-z q))) * halfInd e
        (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
          (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) t from
      funext fun t => by rw [Finset.sum_apply]; exact (sum_char hc hs h A B hA hB z hz hz' t).symm, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hTm.modul _ hSB _ fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee], hvac]
  have hq : ∀ q, GlobalTheory.PlaceModel.heisL S T ψ (2 • (n • l)) (heisO ψ S T (cA D e • finTens 1 (-z q)) v) =
      heisO ψ S T (cA D e • finTens 1 (-z q)) v := fun q => by
    have h1 := finTens_mem_std hc hs.gS (smul_mem_stdMat h𝔪 hnc (neg_mem (hz q)))
    rw [finTens_smul, show ((n : 𝓞 D.host.E) : D.host.E) = n from rfl, map_natCast, Nat.cast_smul_eq_nsmul] at h1
    have h2 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hce _ h1
    rw [smul_comm] at h2
    generalize cA D e • finTens 1 (-z q) = y at h2 ⊢
    have h3 := GlobalTheory.PlaceModel.heisL_comm S T ψ (2 • (n • l)) y v
    have h4 : ψ (symplO S T (2 • (n • l)) y) = 1 := by
      rw [smul_comm]
      exact ((GlobalTheory.PlaceModel.isBichar_symplO S T ψ).nsmul n _ _).trans
        (char_sympl_eq_one hs.std (sdC_std hs.gS) (sdC_std hs.gT) (nsmul_mem hl 2) h2)
    have h5 : GlobalTheory.PlaceModel.heisL S T ψ (2 • (n • l)) v = v := hv.1 _ (nsmul_mem hl n)
    rw [h4, h5, one_smul] at h3
    exact h3
  have h6 := congrArg (GlobalTheory.PlaceModel.heisL S T ψ (2 • (n • l))) hT
  rw [map_sum, map_smul, Finset.sum_congr rfl fun q _ => hq q, hT] at h6
  exact (smul_right_injective _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h6).symm

end GlobalTheory.CosRead

open GlobalTheory.CosRead GlobalTheory.LatVac GlobalTheory.IopRead in
set_option maxHeartbeats 1600000 in
theorem _root_.GlobalTheory.T.cosetIndicator_reads_as_translate_curveTheta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∀ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), Reads ψ θ hS hT ⊤ δ 1 G v → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm →
  Reads ψ θ hS hT ⊤ δ 1 (cosV δ 𝔪 0 G) (Tm (cosInd e 𝔪 hS hT 0)) →
  ∀ z : Matrix (Fin d) (Fin a) D.host.E, IsIntE z → Reads ψ θ hS hT ⊤ δ 1 (cosV δ 𝔪 z G) (Tm (cosInd e 𝔪 hS hT z)) := by
  intro D ψ θ S T a d hS hT δ hc hs v hv G hG hr e 𝔪 h Tm hTm h0 z hz
  subst hS hT
  have h𝔪 := h.ne_bot
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hfd := fun l hl => fix_deep hc hs hv.2.lat h hTm (l := l) hl
  have hn0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hnm := Ideal.absNorm_mem 𝔪
  obtain ⟨n, hn⟩ : ∃ n, n = Ideal.absNorm 𝔪 := ⟨_, rfl⟩
  rw [← hn] at hfd hn0 hnm
  obtain ⟨μ, s, hsi, hμ, hμ1, k, hk⟩ := exists_near_idem h (N := 2 * (2 * n)) (by positivity)
    (by push_cast; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hnm))
  have hmm : (μ : D.host.E) * D.host.conj μ = 4 * ((n * k : 𝓞 D.host.E) : D.host.E) := by
    have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hk
    simp only [map_mul, map_natCast] at this
    rw [← GlobalTheory.SkewLatSelfDual.star_eq_conj, ← Formalism.L2.DIV.starO_coe]
    change algebraMap (𝓞 D.host.E) D.host.E μ * algebraMap (𝓞 D.host.E) D.host.E (Formalism.L2.DIV.starO μ) =
      4 * algebraMap (𝓞 D.host.E) D.host.E _
    simp only [map_mul, map_natCast]
    rw [this]
    push_cast
    ring

  have k0 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) S.rank T.rank) :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D _) (GlobalTheory.NormSum.VacMove.moves_one D _)
  have kB := klat_skew δ h𝔪 S.rank T.rank
  have hH := (GlobalTheory.T.intertwinerUnitary_all D ⊤ δ hs.crv _ _ _ _ k0 kB G hG).2.1
  have htop : (⊤ : Ideal (𝓞 D.host.E)) ≠ ⊥ := top_ne_bot
  have hz1 : z ∈ skewMat D ⊤ S.rank T.rank := by
    simpa using mem_skewMat htop hz (c := 1) trivial
  have hcurve : cosV δ 𝔪 z G =
      Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ ((μ : D.host.E) • z)) (cosV δ 𝔪 0 G) := by
    have hfix := GlobalTheory.NormSum.VacMove.wd_fix h1 hs.crv kB hH (pt_mem δ (mem_skewMat h𝔪 hz hμ1))
    rw [cosV, cosV, GlobalTheory.NormSum.VacMove.pt_zero, GlobalTheory.NormSum.VacMove.wd_zero]
    generalize Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) S.rank T.rank)
      (La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D 𝔪 T.rank)) G = H at hfix ⊢
    have hW := wd_pt_mul hs.crv htop (smul_mem_skewMat μ hz1) (smul_mem_skewMat (1 - μ) hz1) H
    have hsum : (μ : D.host.E) • z + ((1 - μ : 𝓞 D.host.E) : D.host.E) • z = z := by
      rw [← add_smul, show ((1 - μ : 𝓞 D.host.E) : D.host.E) = 1 - (μ : D.host.E) from rfl, add_sub_cancel, one_smul]
    rw [hfix, hsum] at hW
    rw [← hW]
    funext y
    simp only [Wd, wdPh_eq_one hs.crv htop hz1 hmm, one_mul, Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hR := GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T rfl rfl ⊤ δ 1 hs _ _ h0 ((μ : D.host.E) • z)
  rw [hcurve]
  convert hR using 1

  obtain ⟨hee, hei⟩ : e * e = e ∧ finPart D e ∈ intAE D := by
    obtain ⟨SS, c, he, -⟩ := h
    exact ⟨GlobalTheory.PlaceDatum.idemSum_mul_self he,
      GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.IdemSumIdeal.isIdemSum_props e SS c he).2.1⟩
  have hhalf : IsHalf e (e • finTens 1 (-z) : WO S T) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  have hcos : cosInd e 𝔪 rfl rfl z = fun t : WO S T => cosInd e 𝔪 rfl rfl 0 (t + e • finTens 1 (-z)) := by
    funext t
    have h2 : ∀ i j, toEAf D ((t + e • finTens 1 (-z) : WO S T) i j) = toEAf D (t i j) - toEAf D e * eToEAf D (z i j) :=
      fun i j => by
        rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add, RingHom.map_mul, sub_eq_add_neg, ← mul_neg,
          ← RingHom.map_neg]
        rfl
    rw [cosInd_zero]
    simp only [cosInd, half_add hhalf, h2, inId_iff, Fin.cast_eq_self]
  rw [hcos, hTm.trans _ (sb_cosInd hc hs.gS h) _ hhalf, finPt_eq, ← smul_neg, finTens_smul]
  have hu := finTens_mem_std hc hs.gS (neg_mem (mem_stdMat hz))
  have hu0 : ∀ i j, infPart D (finTens 1 (-z) i j) = 0 := fun i j => infPart_pair _ _
  generalize finTens 1 (-z) = u at hu hu0 ⊢
  generalize Tm (cosInd e 𝔪 rfl rfl 0) = φ at hfd ⊢
  have hl := nsmul_mem (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hsi _ hu) 2
  have hx := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hei _ hu
  have h5 : incA D (μ : D.host.E) • u = e • u + 2 • (n • (2 • (s • u))) := by
    refine Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, RingHom.map_add, RingHom.map_mul, hu0,
        mul_zero, add_zero]
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, RingHom.map_add, RingHom.map_mul, hμ,
        map_natCast]
      push_cast
      ring
  have h6 := heisO_heisO ψ (e • u) (2 • (n • (2 • (s • u)))) φ
  rw [hfd _ hl, ← h5] at h6
  have h7 : ψ (symplOH S T (e • u) (2 • (n • (2 • (s • u))))) = 1 := by
    have h8 : ∀ x w : WO S T, symplOH S T x (2 • w) = symplO S T x w := fun x w => by
      rw [two_nsmul, symplOH, symplO_add_right, mul_add, ← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]
    rw [h8]
    exact char_sympl_eq_one hs.std (sdC_std hs.gS) (sdC_std hs.gT) hx (nsmul_mem hl n)
  rw [h6, h7, one_smul]
