import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverBridge

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

theorem galF_val {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (z : Fq l a) :
    Per.σF k (Fq.val l a z) = Fq.val l a z ^ l ^ s := by
  obtain ⟨z₀, ω, hω, hz, h⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hω' : k ω = ω ^ l ^ s := hk ω (by
    rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
  have hd : ¬ l ∣ l ^ a - 1 := fun h => hl.out.not_dvd_one
    ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne a))).1 h)
  have h2 : Per.σF k (Fq.val l a z₀) = Fq.val l a z₀ ^ l ^ s := by
    refine GlobalTheory.UnramIdem.tilt_pow (k := l ^ s) hd dvd_rfl hz fun n => ?_
    obtain ⟨y, y1, y2, y3⟩ := hz n
    refine ⟨Per.σO k y, ?_, by rw [← map_pow, y2, map_one], ?_⟩
    · rw [GlobalTheory.RingIface.sigO_coe l, ← map_pow, y1, GlobalTheory.RingBasics.σC_coe, hω']
    · exact GlobalTheory.AdicMaps.coeff_galois l k _ n y y3
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0, map_zero, map_zero, zero_pow (pow_pos hl.out.pos s).ne']
  · obtain ⟨j, rfl⟩ := h z h0
    rw [map_pow, map_pow, h2, ← pow_mul, ← pow_mul, mul_comm]

theorem galA_wA {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (w : Wq l a) :
    Per.σA k (wA l a w) = wA l a ((sigma l a ^ s) w) := by
  refine WittVector.ext fun n => ?_
  refine (GlobalTheory.RingIface.sigA_coeff l k _ n).trans ?_
  change Per.σF k (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ s) w).coeff n)
  rw [coeff_sigma_pow, map_pow, galF_val hk]

variable {e : ℕ} [NeZero e]

theorem isTiltOf_kummer (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) : IsTiltOf ζ e (ϖ.kummer k) := by
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  intro n
  refine ⟨ϖ.ratio k n, ?_, ?_, ϖ.coeff_kummer k n⟩
  · rw [PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, ϖ.seq_pow, hζ,
      mul_div_cancel_right₀ _ (ϖ.seq_ne_zero 0)]
    rfl
  · refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow,
      hfix _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩), div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)),
      map_one]
    rfl

theorem emb_sigma_pow {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O) (n : ℕ)
    (τ : ZMod a) (w : Wq l a) : emb t τ ((sigma l a ^ n) w) = emb t (τ - n) w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, emb_sigma]
    congr 1
    push_cast
    ring

theorem kummer_mem_resSub (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) (he : e + 1 = l ^ a) : ϖ.kummer k ∈ resSub l a := by
  rw [mem_resSub, ← he, pow_succ, GlobalTheory.MemLoc.IsTiltOf.pow_eq_one (isTiltOf_kummer ϖ hk hζ), one_mul]

theorem galA_ev (ϖ : PiSys l e) {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s)
    (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (x : (Wq l a)⟦X⟧) :
    Per.σA k (ϖ.ev a x) = ϖ.ev a (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) x)) := by
  refine RingHom.congr_fun (ringHom_ext_of_sep ((Per.σA k).comp (ϖ.ev a))
    ((ϖ.ev a).comp ((rescale (WittVector.teichmuller l z)).comp
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a)))) (fun w => ?_) ?_
    fun y hy => ϖ.sep_teich y fun n => ?_) x
  · simp only [RingHom.comp_apply, PiSys.ev_C, galA_wA hk, map_C]
    have : rescale (WittVector.teichmuller l z) (C ((sigma l a ^ s) w)) = C ((sigma l a ^ s) w) := by
      refine PowerSeries.ext fun m => ?_
      rw [coeff_rescale, coeff_C]
      split_ifs with h
      · rw [h, pow_zero, one_mul]
      · rw [mul_zero]
    rw [RingHom.coe_coe, this, PiSys.ev_C]
  · simp only [RingHom.comp_apply, PiSys.ev_X, map_X, rescale_X, map_mul, PiSys.ev_C, PiSys.gal_teich,
      PiSys.mu, wA_teich, hz, add_sub_cancel]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, PiSys.ev_X, PiSys.gal_teich, mul_pow]
    exact dvd_mul_left _ _

theorem thetaW_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    {ζ : ↥LL.1} (hζ : k (ϖ.seq 0) = (ζ : Om l) * ϖ.seq 0) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) :
    ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) = ζ := by
  refine Subtype.ext ((algebraMap (Om l) ℂ_[l]).injective ?_)
  have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
  simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller, hz] at h1
  exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq (isTiltOf_kummer ϖ hk hζ))

theorem toAc_rescale {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (γ : TameGal K l e a) (c : Wq l a)
    (hc : ∀ τ, algebraMap O K (emb t τ c) = γ.root τ) (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    (toAc t K (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x)) τ : K⟦X⟧) = ringAct γ (fun σ => (toAc t K x σ : K⟦X⟧)) τ := by
  refine PowerSeries.ext fun n => ?_
  rw [ringAct_apply, coeff_rescale, coeff_toAc, coeff_toAc, coeff_rescale, coeff_map, map_mul, map_pow,
    map_mul, map_pow, hc]
  congr 2
  rw [RingHom.coe_coe, emb_sigma_pow, ZMod.natCast_zmod_val]

theorem algebraMap_emb_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a)
    (hζ : k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0) (z : Fq l a)
    (hz : Fq.val l a z = ϖ.kummer k) (τ : ZMod a) :
    algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ (WittVector.teichmuller l z)) = γ.root τ := by
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) : ↥(OL LL)) : ↥LL.1) = _
  rw [sigma_pow_teich, map_pow, SubmonoidClass.coe_pow, thetaW_teich ϖ hk LL hζ z hz, TameGal.root, powL_apply]
  simp

theorem covers_of_root {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (γ : TameGal K l e a) {k : GQ l}
    (hunr : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k)
    (hroot : ∀ τ, algebraMap O K (emb t τ (WittVector.teichmuller l z)) = γ.root τ) : Covers K t ϖ k γ := by
  intro f f' hf'
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) f
  set o := Module.Free.chooseBasis ℤ_[l] O
  have hf : f' = ∑ j, o j • toAc t K (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) (x j))) := by
    funext τ
    refine Subtype.ext ?_
    rw [hf' τ]
    have h1 : (fun σ => (((∑ j, o j • toAc t K (x j)) σ : A O K) : K⟦X⟧)) =
        ∑ j, algebraMap O K (o j) • (fun σ => (toAc t K (x j) σ : K⟦X⟧)) := by
      funext σ
      simp [Finset.sum_apply, algebraMap_smul]
    rw [h1, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
    simp [algebraMap_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toAc_rescale t γ _ hroot]
  subst hf
  simp only [map_sum, map_smul, PiSys.iTot_toAc, galOA_tmul, galA_ev ϖ hunr z hz]

end GlobalTheory.BKGal.CoverBridge

open GlobalTheory.BKGal.CoverBridge in

theorem GlobalTheory.BKGal.covers_of_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a), ∀ k ∈ ϖ.GKinf,
    (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) →
    k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 → Covers ↥LL.1 (thetaW a LL) ϖ k γ := by
  intro l _ a e _ _ ϖ LL _ _ γ k hk hunr hζ
  have hmem := kummer_mem_resSub ϖ hk hζ (TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a))
  exact covers_of_root (thetaW a LL) ϖ γ hunr ⟨ϖ.kummer k, hmem⟩ rfl
    (algebraMap_emb_teich ϖ hk LL γ hζ ⟨ϖ.kummer k, hmem⟩ rfl)
