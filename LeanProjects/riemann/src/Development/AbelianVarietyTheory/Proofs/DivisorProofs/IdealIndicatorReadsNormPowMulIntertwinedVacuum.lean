import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCOfSd

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

open scoped TensorProduct nonZeroDivisors
open GlobalTheory.LatVac
open Formalism.L2.DIV (starO starO_coe)
open Formalism.MainNotions.TaylorLogMetric (Hf qH U)
open Formalism.MainNotions.StandardLatticesGL3 (wdPh ee KLat)
open GlobalTheory.SkewIndex (skewEnt)
open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs (matIn)
open GlobalTheory.ThetaLatticePoints (ptHom)

noncomputable section

namespace GlobalTheory.IopRead

variable {D : D7}

abbrev skewMat (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) : AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) :=
  matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)

abbrev stdMat (D : D7) (a d : ℕ) : AddSubgroup (Matrix (Fin d) (Fin a) D.host.E) :=
  matIn D a d (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice in
theorem La0_eq (δ : ℂ) (a d : ℕ) : La0 D (tor0 D ⊤ δ) a d = (stdMat D a d).map (ptHom D ⊤ δ a d) := by
  have hcoef : coefLat D ⊤ = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [coefLat_eq, ext, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]
  rw [La0_eq_map, lat0, hcoef]

theorem smul_mem_skewMat {𝔪 : Ideal (𝓞 D.host.E)} {a d : ℕ} (c : 𝓞 D.host.E) {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : z ∈ skewMat D 𝔪 a d) : (c : D.host.E) • z ∈ skewMat D 𝔪 a d := fun i j =>
  Submodule.smul_mem _ c (hz i j)

theorem smul_mem_stdMat {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {c : 𝓞 D.host.E} (hc : c ∈ D.host.conj • 𝔪)
    {z : Matrix (Fin d) (Fin a) D.host.E} (hz : z ∈ skewMat D 𝔪 a d) : (c : D.host.E) • z ∈ stdMat D a d := fun i j => by
  have hn0 := GlobalTheory.SkewLatSelfDual.coe_ne_zero (GlobalTheory.SkewLatSelfDual.conj_smul_ne_bot h𝔪)
  have h2 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 D.host.E)⁰ (P := D.host.E) hc) (hz i j)
  rw [mul_left_comm, skewEnt, mul_div_cancel₀ _ hn0] at h2
  have h3 : D.host.AA0 * (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ D.host.AA0 := by
    simpa using mul_le_mul' (le_refl D.host.AA0) (FractionalIdeal.coeIdeal_le_one (I := 𝔪))
  exact h3 h2

theorem klat_skew (δ : ℂ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (a d : ℕ) :
    KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
  Or.inr ⟨_, _, GlobalTheory.NormSum.VacMove.sd_of_moves (GlobalTheory.NormSum.VacMove.moves_one D a),
    GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 d, rfl⟩

theorem pt_mem (δ : ℂ) {𝔪 : Ideal (𝓞 D.host.E)} {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : z ∈ skewMat D 𝔪 a d) : pt D (tor0 D ⊤ δ) δ z ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  rw [GlobalTheory.SkewIndex.La_skew_eq_map]
  exact ⟨z, hz, rfl⟩

theorem ee_int (m : ℤ) : ee (m : ℝ) = 1 := by
  rw [ee, ← Complex.exp_int_mul_two_pi_mul_I m]
  congr 1
  push_cast
  ring

theorem wd_pt_mul {δ : ℂ} (hc : Crv D ⊤ δ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ}
    {z y : Matrix (Fin d) (Fin a) D.host.E} (hz : z ∈ skewMat D 𝔪 a d) (hy : y ∈ skewMat D 𝔪 a d) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) F) =
      Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z + y)) F := by
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨w, -, hw⟩ := GlobalTheory.FinWeil.WdCocycle.wd_cocycle D h1 ⊤ δ hc
  obtain ⟨m, hm⟩ := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D h1 ⊤ δ hc a d _ (klat_skew δ h𝔪 a d)).2.2.1 _
    (pt_mem δ (smul_mem_skewMat w hz)) _ (pt_mem δ hy)
  have h2 := (hw a d ((w : D.host.E) • z) y).1
  rw [hm, ← Int.cast_neg, ee_int] at h2
  rw [(hw a d z y).2.2 F]
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  rw [← h2, one_smul]

theorem wdPh_eq_one {δ : ℂ} (hc : Crv D ⊤ δ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ}
    {z : Matrix (Fin d) (Fin a) D.host.E} (hz : z ∈ skewMat D 𝔪 a d) {m k : 𝓞 D.host.E}
    (hm : (m : D.host.E) * D.host.conj m = 4 * k) :
    wdPh D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ ((m : D.host.E) • z)) = 1 := by
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hq := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D h1 ⊤ δ hc a d _ (klat_skew δ h𝔪 a d)).2.2.2.2.2.2
  obtain ⟨n1, hn1⟩ := hq _ (pt_mem δ (smul_mem_skewMat (k + 1) hz))
  obtain ⟨n2, hn2⟩ := hq _ (pt_mem δ (smul_mem_skewMat k hz))
  obtain ⟨n3, hn3⟩ := hq _ (pt_mem δ hz)
  have hk : D.host.conj (k : D.host.E) = k := by
    have := congrArg D.host.conj hm
    rw [map_mul, map_mul, GlobalTheory.NormSum.VacMove.conj_conj, mul_comm, hm, map_ofNat] at this
    exact (mul_left_cancel₀ (by norm_num) this).symm
  have key : Hf D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ ((m : D.host.E) • z)) (pt D (tor0 D ⊤ δ) δ ((m : D.host.E) • z)) =
      2 * (Hf D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (((k + 1 : 𝓞 D.host.E) : D.host.E) • z))
        (pt D (tor0 D ⊤ δ) δ (((k + 1 : 𝓞 D.host.E) : D.host.E) • z)) -
      Hf D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ ((k : D.host.E) • z)) (pt D (tor0 D ⊤ δ) δ ((k : D.host.E) • z)) -
      Hf D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ z)) := by
    have hs : ∀ c : D.host.E, ∑ i, ∑ j, (c • z) i j * D.host.conj ((c • z) i j) =
        c * D.host.conj c * ∑ i, ∑ j, z i j * D.host.conj (z i j) := fun c => by
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hk1 : ((k + 1 : 𝓞 D.host.E) : D.host.E) = (k : D.host.E) + 1 := rfl
    simp only [GlobalTheory.FinWeil.WdCocycle.hf_pt, hs, hm, hk1, map_add D.host.conj, map_one, hk]
    generalize (∑ i, ∑ j, z i j * D.host.conj (z i j)) = c
    rw [← mul_sub, ← mul_sub, mul_left_comm (2 : ℂ), ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum (a := (2 : ℂ))]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [map_mul, map_add, map_one, map_ofNat]
    ring
  have h2 : qH D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ ((m : D.host.E) • z)) / 2 = ((n1 - n2 - n3 : ℤ) : ℝ) := by
    push_cast
    rw [← hn1, ← hn2, ← hn3, qH, qH, qH, qH, key]
    simp only [Complex.mul_re, Complex.sub_re, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [wdPh, h2, ee_int]

theorem char_sum {M V : Type} [AddCommGroup M] [AddCommGroup V] (p : M →+ V) (hp : Function.Injective p)
    (Y₀ : AddSubgroup M) (A B : AddSubgroup V) (hA : A ≤ Y₀.map p) [Fintype (B ⧸ A.addSubgroupOf B)]
    (z : B ⧸ A.addSubgroupOf B → M) (hz : ∀ q, p (z q) = ((Quotient.out q : B) : V)) (g : M → ℂ)
    (hg : ∀ x y, g (x + y) = g x * g y) (h0 : ∀ x ∈ Y₀, g x = 1) {z₀ : M} (hz₀ : p z₀ ∈ B) (hne : g z₀ ≠ 1) :
    ∑ q, g (z q) = 0 := by
  set q₀ : B ⧸ A.addSubgroupOf B := QuotientAddGroup.mk ⟨p z₀, hz₀⟩ with hq₀
  have h1 : ∀ q, g (z (q + q₀)) = g (z q) * g z₀ := fun q => by
    have h2 : (QuotientAddGroup.mk (Quotient.out q + ⟨p z₀, hz₀⟩) : B ⧸ A.addSubgroupOf B) =
        QuotientAddGroup.mk (Quotient.out (q + q₀)) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h2
    obtain ⟨y, hy, hye⟩ := hA h2
    have h3 : z (q + q₀) = z q + z₀ + y := by
      apply hp
      rw [map_add, map_add, hye, hz, hz]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
      abel
    rw [h3, hg, hg, h0 y hy, mul_one]
  have h4 : ∑ q, g (z q) = (∑ q, g (z q)) * g z₀ := by
    rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight q₀)]
    exact Finset.sum_congr rfl fun q _ => h1 q
  have h5 : (∑ q, g (z q)) * (1 - g z₀) = 0 := by linear_combination h4
  exact (mul_eq_zero.1 h5).resolve_right (sub_ne_zero.2 hne.symm)

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {δ : ℂ}

theorem finPt_eq (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) 1 z = finTens 1 (-z) := by
  refine Matrix.ext fun i j => ?_
  change pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-((1 : D.host.E)⁻¹ * z i j)) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(z i j))
  rw [inv_one, one_mul]

theorem finTens_smul {m n : ℕ} (c : D.host.E) (z : Matrix (Fin m) (Fin n) D.host.E) :
    finTens 1 (c • z) = incA D c • finTens 1 z := by
  refine Matrix.ext fun i j => ?_
  change _ = ((1 : AF D.host.F) ⊗ₜ[D.host.F] c) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem finTens_mem_std (hc : D.host.ccK = ⊤) (hS : S.gram = 1) {z : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hz : z ∈ stdMat D S.rank T.rank) : finTens 1 z ∈ latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True :=
  finTens_mem_latO (one_mem_intAf _) ((mem_latRat_iff hc hS mem_stdL z).2 fun i j => by rw [mul_one]; exact hz i j)

theorem sdC_std {V : HSp D} (hV : V.gram = 1) : IsSelfDualC V (stdL D V.rank) :=
  isSelfDualC_of_sd hV (GlobalTheory.NormSum.VacMove.sd_of_moves (GlobalTheory.NormSum.VacMove.moves_one D _))

set_option maxHeartbeats 1600000 in

theorem term_reads (hc : D.host.ccK = ⊤) (hs : Setup ψ θ S T ⊤ δ 1) {v : WO S T → ℂ}
    (hv : IsLatVac (heisO ψ S T) (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) v)
    {G : VC D S.rank T.rank → ℂ} (hG : G ∈ Th D (tor0 D ⊤ δ) (stdL D S.rank) (stdL D T.rank))
    (hr : Reads ψ θ rfl rfl ⊤ δ 1 G v) {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪)
    {z : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (hz : z ∈ skewMat D 𝔪 S.rank T.rank) :
    Reads ψ θ rfl rfl ⊤ δ 1 (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) G) (heisO ψ S T (cA D e • finTens 1 (-z)) v) := by
  have h𝔪 := h.ne_bot
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨n, hn⟩ : ∃ n, n = Ideal.absNorm 𝔪 := ⟨_, rfl⟩
  have hn0 : 0 < n := hn ▸ Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hnm : (n : 𝓞 D.host.E) ∈ 𝔪 := hn ▸ Ideal.absNorm_mem 𝔪
  have hnc : (n : 𝓞 D.host.E) ∈ D.host.conj • 𝔪 := by
    have := starO_mem_conj hnm
    rwa [show starO (n : 𝓞 D.host.E) = n from map_natCast Formalism.L2.DIV.starOHom n] at this
  obtain ⟨μ, s, hsi, hμ, hμ1, k, hk⟩ := exists_near_idem h (N := 2 * (2 * n * n)) (by positivity)
    (by push_cast; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hnm))
  have hm1 := starO_mem_conj hμ1
  rw [starO_one_sub] at hm1
  obtain ⟨m, hm⟩ : ∃ m, m = starO μ := ⟨_, rfl⟩
  rw [← hm] at hm1 hk
  have hmc : D.host.conj (m : D.host.E) = μ := by
    rw [hm, starO_coe, ← GlobalTheory.SkewLatSelfDual.star_eq_conj, star_star]
  have hmm : (m : D.host.E) * D.host.conj m = 4 * ((n * n * k : 𝓞 D.host.E) : D.host.E) := by
    have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hk
    simp only [map_mul, map_natCast] at this
    rw [hmc]
    change algebraMap (𝓞 D.host.E) D.host.E m * algebraMap (𝓞 D.host.E) D.host.E μ = 4 * algebraMap (𝓞 D.host.E) D.host.E _
    simp only [map_mul, map_natCast]
    rw [mul_comm, this]
    push_cast
    ring

  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) S.rank T.rank) :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D _) (GlobalTheory.NormSum.VacMove.moves_one D _)
  have hfix : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (((1 - m : 𝓞 D.host.E) : D.host.E) • z)) G = G :=
    GlobalTheory.NormSum.VacMove.wd_fix h1 hs.crv k0 hG (by rw [La0_eq]; exact ⟨_, smul_mem_stdMat h𝔪 hm1 hz, rfl⟩)
  have hW := wd_pt_mul hs.crv h𝔪 (smul_mem_skewMat m hz) (smul_mem_skewMat (1 - m) hz) G
  have hsum : (m : D.host.E) • z + ((1 - m : 𝓞 D.host.E) : D.host.E) • z = z := by
    rw [← add_smul, show ((1 - m : 𝓞 D.host.E) : D.host.E) = 1 - (m : D.host.E) from rfl, add_sub_cancel, one_smul]
  rw [hfix, hsum] at hW
  have hU : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ ((m : D.host.E) • z)) G =
      U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ ((m : D.host.E) • z)) G := by
    funext y
    rw [Wd, wdPh_eq_one hs.crv h𝔪 hz hmm, one_mul]
  have hR := GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T rfl rfl ⊤ δ 1 hs G v hr ((m : D.host.E) • z)
  rw [← hW, hU]
  convert hR using 1

  rw [finPt_eq, ← smul_neg, finTens_smul]
  have hnu : ∀ c : ℕ, (c * n) • finTens 1 (-z) ∈ latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True := fun c => by
    have := finTens_mem_std hc hs.gS (smul_mem_stdMat h𝔪 hnc (neg_mem hz))
    rw [finTens_smul, show ((n : 𝓞 D.host.E) : D.host.E) = n from rfl, map_natCast, Nat.cast_smul_eq_nsmul] at this
    rw [mul_smul]
    exact nsmul_mem this c
  have hu0 : ∀ i j, infPart D (finTens 1 (-z) i j) = 0 := fun i j => infPart_pair _ _
  generalize finTens 1 (-z) = u at hnu hu0 ⊢
  have hcs : finPart D (cA D s) ∈ intAE D := by
    rw [Formalism.IndefR.Fin.finPart_cA]; exact Formalism.IndefR.Fin.cF_int hsi
  have hce : finPart D (cA D e) ∈ intAE D := by
    obtain ⟨SS, c, he, -⟩ := h
    rw [Formalism.IndefR.Fin.finPart_cA]
    exact Formalism.IndefR.Fin.cF_int (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.IdemSumIdeal.isIdemSum_props e SS c he).2.1)
  have h4 : finPart D (incA D (m : D.host.E)) = finPart D (cA D e + ((2 * (2 * n * n) : ℕ) : AE D) * cA D s) := by
    rw [hm, starO_coe, ← GlobalTheory.DualPairCheck.cA_incA, Formalism.IndefR.Fin.finPart_cA, hμ, ← Formalism.IndefR.Fin.finPart_cA,
      RingHom.map_add (cA D), RingHom.map_mul (cA D), map_natCast (cA D)]
  have hl := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hcs _ (hnu 1)
  have hx := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hce _ (hnu 2)
  have h5 : incA D (m : D.host.E) • u = cA D e • u + 2 • ((2 * n) • (cA D s • ((1 * n) • u))) := by
    refine Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, RingHom.map_add, RingHom.map_mul, hu0,
        mul_zero, add_zero]
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, RingHom.map_add, RingHom.map_mul, h4,
        map_natCast]
      push_cast
      ring
  have h6 := heisO_heisO ψ (cA D e • u) (2 • ((2 * n) • (cA D s • ((1 * n) • u)))) v
  rw [hv.1 _ (nsmul_mem hl _), ← h5] at h6
  have h7 : ψ (symplOH S T (cA D e • u) (2 • ((2 * n) • (cA D s • ((1 * n) • u))))) = 1 := by
    have h8 : ∀ x w : WO S T, symplOH S T x (2 • w) = symplO S T x w := fun x w => by
      rw [two_nsmul, symplOH, symplO_add_right, mul_add, ← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]
    rw [h8]
    refine ((GlobalTheory.PlaceModel.isBichar_symplO S T ψ).nsmul (2 * n) _ _).symm.trans ?_
    rw [← smul_comm]
    exact char_sympl_eq_one hs.std (sdC_std hs.gS) (sdC_std hs.gT) hx hl
  rw [h6, h7, one_smul]

set_option maxHeartbeats 1600000 in

theorem sum_char (hc : D.host.ccK = ⊤) (hs : Setup ψ θ S T ⊤ δ 1) {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪)
    (A B : AddSubgroup (VC D S.rank T.rank)) (hA : A = (stdMat D S.rank T.rank).map (ptHom D ⊤ δ S.rank T.rank))
    (hB : B = (skewMat D 𝔪 S.rank T.rank).map (ptHom D ⊤ δ S.rank T.rank)) [Fintype (B ⧸ A.addSubgroupOf B)]
    (z : B ⧸ A.addSubgroupOf B → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hz : ∀ q, z q ∈ skewMat D 𝔪 S.rank T.rank)
    (hz' : ∀ q, ptHom D ⊤ δ S.rank T.rank (z q) = ((Quotient.out q : B) : VC D S.rank T.rank)) (t : WO S T) :
    ∑ q, ψ (symplO S T t (cA D e • finTens 1 (-z q))) * halfInd e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) t =
      (Fintype.card (B ⧸ A.addSubgroupOf B) : ℂ) * cosInd e 𝔪 rfl rfl 0 t := by
  have h𝔪 := h.ne_bot
  have hn0 := GlobalTheory.SkewLatSelfDual.coe_ne_zero (GlobalTheory.SkewLatSelfDual.conj_smul_ne_bot h𝔪)
  have hcos : cosInd e 𝔪 rfl rfl 0 t = if IsHalf e t ∧ ∀ i j, toEAf D (t i j) ∈ idGrp 𝔪 then 1 else 0 := by
    simp only [cosInd, Matrix.zero_apply, RingHom.map_zero, mul_zero, sub_zero, inId_iff]
  rw [hcos, ← Finset.sum_mul, halfInd]
  by_cases ht : IsHalf e t
  swap
  · rw [if_neg fun hh => ht hh.2, if_neg fun hh => ht hh.1, mul_zero, mul_zero]
  have h0 : ∀ i j, infPart D (t i j) = 0 := fun i j => by
    obtain ⟨SS, c, he, -⟩ := h
    rw [← ht i j, RingHom.map_mul, (GlobalTheory.IdemSumIdeal.isIdemSum_props e SS c he).1, zero_mul]
  have hsym : ∀ y, symplO S T t (cA D e • y) = symplO S T t y := fun y => by
    rw [← GlobalTheory.PlaceModel.symplO_smul, show e • t = t from Matrix.ext ht]
  simp only [hsym]
  have hsk := isSelfDualC_of_sd hs.gT (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 T.rank)
  have hrat := mem_latRat_iff (S := S) (T := T) hc hs.gS (GlobalTheory.SkewLatSelfDual.mem_skewLat (𝔪 := 𝔪))
  by_cases hI : ∀ i j, toEAf D (t i j) ∈ idGrp 𝔪
  · have h1 := mem_of_inId hc hs.gS mem_stdL FractionalIdeal.coeIdeal_le_one h0 hI
    have h2 := mem_of_inId hc hs.gS (GlobalTheory.SkewLatSelfDual.mem_skewLat (𝔪 := 𝔪)) (by
      rw [FractionalIdeal.le_div_iff_mul_le hn0]
      simpa using mul_le_mul' (le_refl (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))
        (FractionalIdeal.coeIdeal_le_one (I := D.host.conj • 𝔪))) h0 hI
    rw [if_pos ⟨h1, ht⟩, if_pos ⟨ht, hI⟩, Finset.sum_congr rfl fun q _ => char_sympl_eq_one hs.std (sdC_std hs.gS) hsk h2
      (finTens_mem_latO (one_mem_intAf _) ((hrat _).2 (neg_mem (hz q))))]
    simp
  · rw [if_neg (fun hh => hI hh.2 : ¬ (IsHalf e t ∧ ∀ i j, toEAf D (t i j) ∈ idGrp 𝔪)), mul_zero]
    split_ifs with h1
    swap
    · exact mul_zero _
    rw [mul_one]
    have h2 : ¬ ∀ ℓ ∈ latRat S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
        (skewLat D 𝔪 T.rank : Set (Fin T.rank → D.host.E)), ψ (symplO S T t (finTens 1 ℓ)) = 1 := fun hh =>
      hI fun i j => by
        have := inId_of_mem hc hs.gS h (mem_of_char_rat hs.std (sdC_std hs.gS) hsk h0 hh) i j
        rwa [ht i j] at this
    push Not at h2
    obtain ⟨ℓ, hℓ, hne⟩ := h2
    have hℓ' : ℓ ∈ skewMat D 𝔪 S.rank T.rank := (hrat _).1 hℓ
    refine char_sum (ptHom D ⊤ δ S.rank T.rank)
      (GlobalTheory.ThetaLatticePoints.ptHom_injective D ⊤ (GlobalTheory.NormExact.delta_ne_zero hs.crv) _ _) _ A B hA.le z hz'
      (fun x => ψ (symplO S T t (finTens 1 (-x)))) (fun x y => ?_) (fun x hx => ?_) (z₀ := -ℓ) ?_ (by rwa [neg_neg])
    · rw [neg_add, finTens_add, symplO_add_right, ψ.map_add_eq_mul]
    · exact char_sympl_eq_one hs.std (sdC_std hs.gS) (sdC_std hs.gT) h1.1 (finTens_mem_std hc hs.gS (neg_mem hx))
    · rw [hB]
      exact ⟨_, neg_mem hℓ', rfl⟩

theorem reads_sum {ι : Type} (s : Finset ι) {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} (G : ι → VC D a d → ℂ)
    (f : ι → WO S T → ℂ) {G₀ : VC D a d → ℂ} {f₀ : WO S T → ℂ} (h₀ : Reads ψ θ hS hT ⊤ δ 1 G₀ f₀)
    (h : ∀ i, Reads ψ θ hS hT ⊤ δ 1 (G i) (f i)) : Reads ψ θ hS hT ⊤ δ 1 (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using h₀.smul 0
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

set_option maxHeartbeats 1600000 in

theorem indicator_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∀ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), Reads ψ θ hS hT ⊤ δ 1 G v → ∀ (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm →
  Reads ψ θ hS hT ⊤ δ 1 (cosV δ 𝔪 0 G) (Tm (cosInd e 𝔪 hS hT 0)) := by
  intro D ψ θ S T a d hS hT δ hc hs v hv G hG hr e 𝔪 h Tm hTm
  subst hS hT
  have h𝔪 := h.ne_bot
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ hs.crv 𝔪 h𝔪 (coprime_conj h) S.rank T.rank
  have hB := GlobalTheory.SkewIndex.La_skew_eq_map D δ 𝔪 S.rank T.rank
  have hA := La0_eq (D := D) δ S.rank T.rank
  have hW := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D h1 ⊤ δ hs.crv _ _ _ (klat_skew δ h𝔪 S.rank T.rank)).2.1
  have hn : 0 < Ideal.absNorm 𝔪 ^ (S.rank * T.rank) :=
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)) _
  rw [cosV, GlobalTheory.NormSum.VacMove.pt_zero, GlobalTheory.NormSum.VacMove.wd_zero, ← Nat.cast_pow]
  generalize La0 D (tor0 D ⊤ δ) S.rank T.rank = A at hidx hA ⊢
  generalize La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D 𝔪 T.rank) = B at hidx hB hW ⊢
  generalize Ideal.absNorm 𝔪 ^ (S.rank * T.rank) = n at hidx hn ⊢
  haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero (by
    change (A.addSubgroupOf B).index ≠ 0
    rw [hidx]; exact hn.ne')
  haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
  have hcard : Fintype.card (B ⧸ A.addSubgroupOf B) = n := by rw [← hidx, AddSubgroup.index, Nat.card_eq_fintype_card]
  choose z hz hz' using fun q : B ⧸ A.addSubgroupOf B => hB.le (Quotient.out q : B).2
  have hee : cA D e * cA D e = cA D e := by
    obtain ⟨SS, c, he, -⟩ := h
    rw [← RingHom.map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hSB : IsSBHalf e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) (halfInd e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True)) := by
    refine ⟨fun t ht => ?_, 1, one_pos, fun u hu hue t => ?_, fun t ht => ?_⟩
    · by_contra hh
      exact ht (if_neg fun h' => hh h'.2)
    · have : IsHalf e (t + u) ↔ IsHalf e t := by
        rw [GlobalTheory.PlaceModel.isHalf_iff, GlobalTheory.PlaceModel.isHalf_iff]
        exact add_mem_cancel_right ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hue)
      simp only [one_smul, halfInd, add_mem_cancel_right hu, this]
    · rw [one_smul]
      by_contra hh
      exact ht (if_neg fun h' => hh h'.1)
  have hvac := hTm.vac
  rw [one_smul] at hvac
  have hsum := reads_sum Finset.univ _ _ hr fun q => term_reads hc hs hv.2.lat hG hr h (hz q)
  have hT : ∑ q, heisO ψ S T (cA D e • finTens 1 (-z q)) v = (n : ℂ) • Tm (cosInd e 𝔪 rfl rfl 0) := by
    rw [← map_smul, ← hcard, show (Fintype.card (B ⧸ A.addSubgroupOf B) : ℂ) • cosInd e 𝔪 rfl rfl 0 =
      ∑ q, fun t => ψ (symplO S T t (cA D e • finTens 1 (-z q))) * halfInd e
        (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
          (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) t from
      funext fun t => by rw [Finset.sum_apply]; exact (sum_char hc hs h A B hA hB z hz hz' t).symm, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hTm.modul _ hSB _ fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee], hvac]
  rw [hT] at hsum
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h2 := hsum.smul (n : ℂ)⁻¹
  rw [smul_smul, inv_mul_cancel₀ hn', one_smul] at h2
  convert h2 using 1
  funext y
  have hsq : ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n), Complex.ofReal_natCast]
  simp only [Iop, hidx, Pi.smul_apply, smul_eq_mul, finsum_eq_sum_of_fintype, Finset.sum_apply]
  rw [← mul_assoc, hsq]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← GlobalTheory.ThetaLatticePoints.ptHom_apply, hz', hW _ (Quotient.out q : B).2]

end GlobalTheory.IopRead
