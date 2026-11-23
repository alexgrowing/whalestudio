import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SpecializesIff
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IsProjPrimeOfRelComps
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ResGAppLE
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.LeDimQuotientHorizontal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCharacterised

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsChowForm IsMultiHomog relComps localMult chowDegree reduceMod
  HermNorm ArchData fsLog cycleIntegral fundCycle chowHt divCycle vertTerm specFirst)

namespace ChowFormHeightComparison₂.CF.M

theorem bijective_comp (F : Type) [Field F] [NumberField F] :
    Function.Bijective fun σ : F →+* ℂ => σ.comp (algebraMap (𝓞 F) F) := by
  constructor
  · intro f g hfg
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) hfg
  · intro τ
    have hinj : Function.Injective τ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hne
      have h := Ideal.comap_ne_bot_of_integral_mem hne (show x ∈ RingHom.ker τ from hx)
        (NumberField.RingOfIntegers.isIntegral x)
      apply h
      rw [eq_bot_iff]
      intro n hn
      rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
      simp [hn]
    refine ⟨IsFractionRing.lift (K := F) hinj, RingHom.ext fun x => ?_⟩
    exact IsFractionRing.lift_algebraMap (K := F) hinj x

theorem finsum_emb {K : Type} [Field K] [NumberField K] (G : (𝓞 K →+* ℂ) → ℝ) :
    ∑ᶠ σ, G σ = ∑ σ : K →+* ℂ, G (σ.comp (algebraMap (𝓞 K) K)) := by
  rw [← finsum_eq_sum_of_fintype]
  exact (finsum_comp_equiv (f := G) (Equiv.ofBijective _ (bijective_comp K))).symm

theorem dualNorm_pos {m : ℕ} (h : HermNorm m) {y : Fin m → ℂ} (hy : y ≠ 0) : 0 < h.dualNorm y := by
  unfold HermNorm.dualNorm
  apply Real.sqrt_pos.mpr
  have hne : h.mat.transpose⁻¹.mulVec y ≠ 0 := by
    intro h0
    apply hy
    have := congrArg (h.mat.transpose.mulVec) h0
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hpos : 0 < ‖h.mat.transpose⁻¹.mulVec y i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => ‖h.mat.transpose⁻¹.mulVec y j‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i))

section

variable {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {m : ℕ} {p : Z ⟶ Sp R} {s : Fin m → B.Sec} {σ : R →+* ℂ}

theorem isComb_single (k : Fin m) : IsComb p s (Pi.single k 1) (s k) := by
  intro i
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem secVal_comb (hB : B.IsLB) {u : Fin m → R} {su : B.Sec} (hu : IsComb p s u su) (y : CxPts p σ) :
    secVal p σ su (pick hB y) y = ∑ k, σ (u k) * coords p σ hB s y k := by
  have hy := GlobalTheory.CxPts.mem_pick hB y
  rw [secVal_apply, hu (pick hB y)]
  simp only [coords]
  have key : ∀ t : Finset (Fin m), ev p σ (B.U (pick hB y))
      (∑ k ∈ t, algX p (B.U (pick hB y)) (u k) * (s k).f (pick hB y)) y =
      ∑ k ∈ t, σ (u k) * ev p σ (B.U (pick hB y)) ((s k).f (pick hB y)) y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have h0 := ev_add (p := p) (σ := σ) (U := B.U (pick hB y)) 0 0 y
      simpa using h0
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ev_mul, ev_algX hy, ih]
  exact key Finset.univ

theorem ptsIn_comb (hB : B.IsLB) {u : Fin m → R} {su : B.Sec} (hu : IsComb p s u su) :
    ptsIn p σ (nonzeroLocus su) = {y | ∑ k, σ (u k) * coords p σ hB s y k ≠ 0} := by
  ext y
  rw [Set.mem_setOf_eq, ← secVal_comb hB hu y]
  exact (secVal_ne_zero_iff su (mem_pick hB y)).symm

theorem log_nsq (φ : Weight p σ B) {h : HermNorm m} (hφ : IsFS φ s h) {u : Fin m → R} {su : B.Sec}
    (hu : IsComb p s u su) {y : CxPts p σ} (hy : y ∈ ptsIn p σ (nonzeroLocus su)) :
    Real.log (φ.nsq (secVal p σ su) y) / 2 = fsLog h (fun k => σ (u k)) (coords p σ φ.isLB s y) := by
  have hpk := mem_pick φ.isLB y
  have hsum : (∑ k, σ (u k) * coords p σ φ.isLB s y k) ≠ 0 := by
    have h1 := hy
    rw [ptsIn_comb φ.isLB hu] at h1
    exact h1
  have hc : coords p σ φ.isLB s y ≠ 0 := by
    intro h0
    apply hsum
    simp [h0]
  have hd := dualNorm_pos h hc
  have ha : 0 < ‖∑ k, σ (u k) * coords p σ φ.isLB s y k‖ := norm_pos_iff.mpr hsum
  have hφy := hφ (pick φ.isLB y) y hpk
  unfold Weight.nsq
  rw [secVal_comb φ.isLB hu y, hφy]
  unfold fsLog
  change Real.log (‖∑ k, σ (u k) * coords p σ φ.isLB s y k‖ ^ 2 *
    Real.exp (-Real.log (h.dualNorm (coords p σ φ.isLB s y) ^ 2))) / 2 = _
  rw [Real.log_div ha.ne' hd.ne', Real.exp_neg, Real.exp_log (pow_pos hd 2), ← div_eq_mul_inv,
    Real.log_div (pow_pos ha 2).ne' (pow_pos hd 2).ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem isFS_pull {φ : Weight p σ B} {h : HermNorm m} (hφ : IsFS φ s h) {Y : Scheme.{0}} (i : Y ⟶ Z) :
    IsFS (φ.pull i rfl) (fun k => GlobalTheory.secPull (s k) i) h := by
  intro J z hz
  have hm : ∀ w : CxPts (i ≫ p) σ, (PtsOver.map i rfl (spMap σ) w).1 = w.1 ≫ i := fun w => rfl
  have hz' := (GlobalTheory.Published.mem_ptsIn_pull hm).mp hz
  refine (Weight.pull_φ φ i rfl J z).trans ?_
  rw [hφ _ _ hz']
  refine congrArg (fun v => Real.log (h.dualNorm v ^ 2)) (funext fun k => ?_)
  dsimp only
  unfold GlobalTheory.secPull
  rw [chartSec_f]
  exact (ev_appLE_of_comp hm _ _ hz).symm

end

variable {K : Type} [Field K] [NumberField K] {m : ℕ} {X : Scheme.{0}} {p : X ⟶ Sp (𝓞 K)} {L : HermLB p}
  {s : Fin m → L.B.Sec} {D : ℕ} {H : ArchData K m} {h : X → ℝ}

local notation "φ" => (MvPolynomial.map (algebraMap (𝓞 K) K) : MvPolynomial (Fin m) (𝓞 K) →+* MvPolynomial (Fin m) K)
local notation "CC" => (C : 𝓞 K →+* MvPolynomial (Fin m) (𝓞 K))

theorem charZero_iff {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp (𝓞 K)} {B : LB Z} {s : Fin m → B.Sec} (hE : Emb q s) :
    CharZero Γ(Z, ⊤) ↔ (ptIdeal q s (genericPoint Z)).comap CC = ⊥ := by
  have hcov : genericPoint Z ∈ (⨆ i, B.U i) := by
    rw [hE.isLB.cover]
    trivial
  obtain ⟨i0, hi0⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have htop : genericPoint Z ∈ (⊤ : Z.Opens) := trivial
  have hcomp : (Z.evaluation ⊤ (genericPoint Z) htop).hom =
      (Z.residue (genericPoint Z)).hom.comp (Z.presheaf.germ ⊤ (genericPoint Z) htop).hom := rfl
  have hinj : Function.Injective (Z.evaluation ⊤ (genericPoint Z) htop).hom := by
    rw [hcomp]
    exact (RingHom.injective (Z.residue (genericPoint Z)).hom).comp
      (germ_injective_of_isIntegral Z (genericPoint Z) htop)
  rw [RingHom.charZero_iff hinj]
  have hmem : ∀ r : 𝓞 K, CC r ∈ ptIdeal q s (genericPoint Z) ↔
      ∀ i (h : genericPoint Z ∈ B.U i), (Z.evaluation (B.U i) _ h).hom (algX q (B.U i) r) = 0 := by
    intro r
    simp only [ptIdeal, Submodule.mem_iInf, RingHom.mem_ker, coneHom, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, Polynomial.C_eq_zero]
  constructor
  · intro hc
    haveI := hc
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, hmem] at hr
    have hr0 := hr i0 hi0
    by_contra hne
    have hker : r ∈ RingHom.ker ((Z.evaluation (B.U i0) _ hi0).hom.comp (algX q (B.U i0))) := hr0
    have h := Ideal.comap_ne_bot_of_integral_mem hne hker (NumberField.RingOfIntegers.isIntegral r)
    apply h
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  · intro hb
    refine charZero_of_inj_zero fun n hn => ?_
    have h1 : CC (n : 𝓞 K) ∈ ptIdeal q s (genericPoint Z) := by
      rw [hmem]
      intro i h
      rw [map_natCast, map_natCast]
      exact hn
    have h2 : (n : 𝓞 K) ∈ (ptIdeal q s (genericPoint Z)).comap CC := h1
    rw [hb, Ideal.mem_bot] at h2
    exact_mod_cast h2

theorem isClosed_of_coheight {Z : Scheme.{0}} (hd : topologicalKrullDim Z = 1) {z : Z} (hz : Order.coheight z = 1) :
    IsClosed ({z} : Set Z) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have hzw : z ⤳ w := specializes_iff_mem_closure.mpr hw
  have hle : w ≤ z := hzw
  by_cases hback : z ≤ w
  · have hwz : w ⤳ z := hback
    have he : z = w := (hzw.antisymm hwz).eq
    subst he
    exact Set.mem_singleton _
  · exfalso
    have hlt : w < z := lt_of_le_not_ge hle hback
    have h1 : Order.coheight z + 1 ≤ Order.coheight w := Order.coheight_add_one_le hlt
    have h2 : (Order.coheight w : WithBot ℕ∞) ≤ Order.krullDim Z := Order.coheight_le_krullDim w
    have h3 : Order.krullDim Z = 1 := by
      rw [← hd, topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
    rw [hz] at h1
    rw [h3] at h2
    have h4 : Order.coheight w ≤ 1 := by exact_mod_cast h2
    have h5 := h1.trans h4
    norm_num at h5

private theorem ev_chart_eq_gv_mul {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {p : Z ⟶ Sp R}
    {σ : R →+* ℂ} (t : B.Sec) {j j' : B.ι} {x : CxPts p σ} (hj : x ∈ ptsIn p σ (B.U j))
    (hj' : x ∈ ptsIn p σ (B.U j')) :
    ev p σ (B.U j) (t.f j) x = GlobalTheory.CxPts.gv p σ B j j' x * ev p σ (B.U j') (t.f j') x := by
  have hx : x ∈ ptsIn p σ (B.U j ⊓ B.U j') := mem_ptsIn_inf.mpr ⟨hj, hj'⟩
  have h1 := congrArg (fun g => ev p σ (B.U j ⊓ B.U j') g x) (t.compat j j')
  rw [ev_mul] at h1
  rw [← ev_res inf_le_left hx, ← ev_res inf_le_right hx]
  exact h1

private theorem dualNorm_smul' {m : ℕ} (h : HermNorm m) (c : ℂ) (v : Fin m → ℂ) :
    h.dualNorm (c • v) = ‖c‖ * h.dualNorm v := by
  unfold HermNorm.dualNorm
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)]

private theorem fsLog_smul_of_ne_zero {m : ℕ} (h : HermNorm m) (w : Fin m → ℂ) {c : ℂ} (hc : c ≠ 0)
    (v : Fin m → ℂ) : fsLog h w (c • v) = fsLog h w v := by
  unfold fsLog
  rw [dualNorm_smul']
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ j, w j * (c * v j)) = c * ∑ j, w j * v j by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring]
  rw [norm_mul, mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hc)]

theorem log_pull (hE : Emb p s) {σ : 𝓞 K →+* ℂ} {h₀ : HermNorm m} (hF : IsFS (L.φ σ) s h₀)
    {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] {u : Fin m → 𝓞 K} {su : L.B.Sec} (hu : IsComb p s u su)
    (y : CxPts (i ≫ p) σ) (hy : y ∈ ptsIn (i ≫ p) σ (nonzeroLocus (GlobalTheory.secPull su i))) :
    Real.log ((L.φ σ).nsq (secVal p σ su) (PtsOver.map i rfl _ y)) / 2 =
      fsLog h₀ (fun k => σ (u k)) (coords (i ≫ p) σ (LB.isLB_pull L.isLB i) (fun k => GlobalTheory.secPull (s k) i) y) := by
  set x := PtsOver.map i rfl (spMap σ) y with hxdef
  have hm : ∀ w : CxPts (i ≫ p) σ, (PtsOver.map i rfl (spMap σ) w).1 = w.1 ≫ i := fun w => rfl
  have hB' := LB.isLB_pull L.isLB i
  set J := pick hB' y with hJdef
  have hyJ : y ∈ ptsIn (i ≫ p) σ ((L.B.pull i).U J) := mem_pick hB' y
  have hxJ : x ∈ ptsIn p σ (L.B.U (J PUnit.unit)) := (GlobalTheory.Published.mem_ptsIn_pull hm).mp hyJ
  have hpullev : ∀ t : L.B.Sec, ev (i ≫ p) σ ((L.B.pull i).U J) ((GlobalTheory.secPull t i).f J) y =
      ev p σ (L.B.U (J PUnit.unit)) (t.f (J PUnit.unit)) x := by
    intro t
    unfold GlobalTheory.secPull
    rw [chartSec_f]
    exact ev_appLE_of_comp hm _ _ hyJ
  have hx : x ∈ ptsIn p σ (nonzeroLocus su) := by
    rw [← secVal_ne_zero_iff su hxJ, secVal_apply, ← hpullev su, ← secVal_apply]
    exact (secVal_ne_zero_iff _ hyJ).mpr hy
  rw [log_nsq (L.φ σ) hF hu hx]
  set j := pick (L.φ σ).isLB x with hjdef
  have hxj : x ∈ ptsIn p σ (L.B.U j) := mem_pick _ x
  have hcoord : coords p σ (L.φ σ).isLB s x = GlobalTheory.CxPts.gv p σ L.B j (J PUnit.unit) x •
      coords (i ≫ p) σ hB' (fun k => GlobalTheory.secPull (s k) i) y := by
    funext k
    simp only [coords, Pi.smul_apply, smul_eq_mul]
    rw [hpullev (s k)]
    exact ev_chart_eq_gv_mul (s k) hxj hxJ
  rw [hcoord, fsLog_smul_of_ne_zero]
  exact ev_ne_zero (mem_ptsIn_inf.mpr ⟨hxj, hxJ⟩) (Units.isUnit _)

theorem arch_pull (hA : StArch) (hX : IsArithVar p D) (hE : Emb p s)
    (hF : ∀ σ : K →+* ℂ, IsFS (L.φ (σ.comp (algebraMap (𝓞 K) K))) s (H.normAt σ))
    {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (hc : CharZero Γ(Z, ⊤))
    {e : ℕ} (hd : topologicalKrullDim Z = (e + 1 : ℕ)) {I : Ideal (MvPolynomial (Fin m) K)}
    (hg : I = (ptIdeal p s (i (genericPoint Z))).map φ) (hf : ∃ f, IsChowForm I (e + 1) f) (hI : IsProjPrime I)
    {u : Fin m → 𝓞 K} {su : L.B.Sec} (hu : IsComb p s u su)
    (hn : GroundTheory.Heights₂.Heights.linForm (fun j => (u j : K)) ∉ I) (σ : K →+* ℂ) :
    ((L.restr i).φ (σ.comp (algebraMap (𝓞 K) K))).chernInt e (ptsIn (i ≫ p) _ (nonzeroLocus (GlobalTheory.secPull su i)))
      (fun y => Real.log ((L.φ _).nsq (secVal p _ su) (PtsOver.map i rfl _ y)) / 2) =
      cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e (fsLog (H.normAt σ) fun j => σ (u j)) ∧
    (e = 0 → (∀ y : CxPts (i ≫ p) (σ.comp (algebraMap (𝓞 K) K)), y ∈ ptsIn (i ≫ p) _ (nonzeroLocus (GlobalTheory.secPull su i))) →
      ∑ᶠ y : CxPts (i ≫ p) (σ.comp (algebraMap (𝓞 K) K)),
        Real.log ((L.φ _).nsq (secVal p _ su) (PtsOver.map i rfl _ y)) / 2 =
      cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e (fsLog (H.normAt σ) fun j => σ (u j))) := by
  obtain ⟨hE', hpt, hcomb⟩ := stPull (𝓞 K) X Z p L.B m s i hE
  have hX' : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc hd
  have hgen : genIdeal (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) = I := by
    rw [hg, genIdeal, hpt]
  have hu' := hcomb u su hu
  have hF' : IsFS ((L.restr i).φ (σ.comp (algebraMap (𝓞 K) K))) (fun k => GlobalTheory.secPull (s k) i) (H.normAt σ) :=
    isFS_pull (hF σ) i
  have hf' : ∃ f, IsChowForm (genIdeal (i ≫ p) (fun k => GlobalTheory.secPull (s k) i)) (e + 1) f := by
    rw [hgen]; exact hf
  have hI' : IsProjPrime (genIdeal (i ≫ p) (fun k => GlobalTheory.secPull (s k) i)) := by
    rw [hgen]; exact hI
  have hn' : GroundTheory.Heights₂.Heights.linForm (fun j => (u j : K)) ∉ genIdeal (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) := by
    rw [hgen]; exact hn
  obtain ⟨k1, k2⟩ := hA K Z (i ≫ p) (L.restr i).B m (fun k => GlobalTheory.secPull (s k) i) e hE' hX' hf' hI' σ
    ((L.restr i).φ (σ.comp (algebraMap (𝓞 K) K))) (H.normAt σ) ((L.restr i).cInf _) hF' (fun j => (u j : K)) hn'
  have hm : ∀ w : CxPts (i ≫ p) (σ.comp (algebraMap (𝓞 K) K)),
      (PtsOver.map i rfl (spMap (σ.comp (algebraMap (𝓞 K) K))) w).1 = w.1 ≫ i := fun w => rfl
  have hset := ptsIn_comb (σ := σ.comp (algebraMap (𝓞 K) K)) (LB.isLB_pull L.isLB i) hu'
  have hfun : (fun y : CxPts (i ≫ p) (σ.comp (algebraMap (𝓞 K) K)) =>
      Real.log ((L.φ _).nsq (secVal p _ su) (PtsOver.map i rfl _ y)) / 2) =
      fun y => fsLog (H.normAt σ) (fun k => σ (u k))
        (coords (i ≫ p) _ (LB.isLB_pull L.isLB i) (fun k => GlobalTheory.secPull (s k) i) y) := by
    funext y
    by_cases hy : y ∈ ptsIn (i ≫ p) (σ.comp (algebraMap (𝓞 K) K)) (nonzeroLocus (GlobalTheory.secPull su i))
    · exact log_pull hE (hF σ) i hu y hy
    · have hy1 := hy
      rw [hset] at hy1
      simp only [Set.mem_setOf_eq, not_not] at hy1
      have hy2 : PtsOver.map i rfl (spMap (σ.comp (algebraMap (𝓞 K) K))) y ∉
          ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (nonzeroLocus su) := by
        rw [← mem_ptsIn_preimage hm, ← GlobalTheory.Cartier.nonzeroLocus_secPull]
        exact hy
      have h0 : secVal p (σ.comp (algebraMap (𝓞 K) K)) su
          (pick (L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB (PtsOver.map i rfl (spMap (σ.comp (algebraMap (𝓞 K) K))) y))
          (PtsOver.map i rfl (spMap (σ.comp (algebraMap (𝓞 K) K))) y) = 0 := by
        by_contra hne
        exact hy2 ((secVal_ne_zero_iff su (mem_pick _ _)).mp hne)
      have hl : Real.log ((L.φ (σ.comp (algebraMap (𝓞 K) K))).nsq (secVal p _ su)
          (PtsOver.map i rfl (spMap (σ.comp (algebraMap (𝓞 K) K))) y)) = 0 := by
        unfold Weight.nsq
        rw [h0]
        simp
      rw [hl, fsLog]
      simp only [zero_div]
      rw [show (∑ k, σ (u k) * coords (i ≫ p) (σ.comp (algebraMap (𝓞 K) K)) (LB.isLB_pull L.isLB i)
          (fun k => GlobalTheory.secPull (s k) i) y k) = 0 from hy1]
      simp
  refine ⟨?_, fun he _ => ?_⟩
  · rw [hfun, hset, ← hgen]
    exact k1
  · rw [hfun, ← hgen]
    exact k2 he

theorem step (hA : StArch) (hX : IsArithVar p D) (hE : Emb p s)
    (hF : ∀ σ : K →+* ℂ, IsFS (L.φ (σ.comp (algebraMap (𝓞 K) K))) s (H.normAt σ)) (hh : L.IsArithHeight h)
    {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤))
    {e : ℕ} (hd : topologicalKrullDim Z = (e + 1 : ℕ)) {I : Ideal (MvPolynomial (Fin m) K)}
    (hg : I = (ptIdeal p s (i (genericPoint Z))).map φ) (hf : ∃ f, IsChowForm I (e + 1) f) (hI : IsProjPrime I)
    {u : Fin m → 𝓞 K} {su : L.B.Sec} (hu : IsComb p s u su)
    (hn : GroundTheory.Heights₂.Heights.linForm (fun j => (u j : K)) ∉ I)
    (hη : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull su i)) :
    h (i (genericPoint Z)) = ∑ᶠ z, ((divOfSec (L.restr i).isLB _ hη).mult z : ℝ) * h (i z) -
      ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
        (fsLog (H.normAt σ) fun j => σ (u j)) := by
  obtain rfl | he := Nat.eq_zero_or_pos e
  · have hd1 : topologicalKrullDim Z = 1 := by simpa using hd
    have hXZ : IsArithVar (i ≫ p) 0 := GlobalTheory.IsArithVar.of_isClosedImmersion hX i hc hd
    have hall : ∀ (σ : 𝓞 K →+* ℂ) (y : CxPts (i ≫ p) σ),
        y ∈ ptsIn (i ≫ p) σ (nonzeroLocus (GlobalTheory.secPull su i)) := by
      intro σ y
      have hy := GlobalTheory.TwistTop.under_eq_genericPoint hXZ y
      rw [GlobalTheory.CxPts.mem_ptsIn]
      simp only [GlobalTheory.Cartier.under] at hy
      rw [hy]
      exact hη
    have hhZ := GlobalTheory.HermLB.IsArithHeight.restrict hX hh i rfl
    rw [GlobalTheory.HermLB.IsArithHeight.point hh Z i hc hd1 _ (GlobalTheory.Cartier.isRatSec_ratOfSec _ hη),
      GlobalTheory.HermLB.curveDeg_sec i su hη hall, finsum_emb]
    congr 1
    · refine finsum_congr fun z => ?_
      by_cases hm : (divOfSec (L.restr i).isLB (GlobalTheory.secPull su i) hη).mult z = 0
      · rw [hm]
        simp
      · have hz1 := GlobalTheory.Cartier.CartierDiv.coheight_eq_one_of_mult_ne_zero hm
        have hcl := isClosed_of_coheight hd1 hz1
        have hfin := hXZ.finite_residueField hcl
        have hpt := hhZ.closedPoint hcl
        simp only at hpt
        rw [hpt]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      exact (arch_pull hA hX hE hF i hc hd hg hf hI hu hn σ).2 rfl (hall _)
  · obtain ⟨_, hrec⟩ := GlobalTheory.HermLB.IsArithHeight.recursion_sec i su hη hh hc he hd
    rw [hrec, finsum_emb]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact (arch_pull hA hX hE hF i hc hd hg hf hI hu hn σ).1

theorem height_vertical (hV : StVert) (hX : IsArithVar p D) (hE : Emb p s) (hh : L.IsArithHeight h)
    {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] {e : ℕ} (hd : topologicalKrullDim Z = e)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (ptIdeal p s (i (genericPoint Z))).comap CC = v.asIdeal) :
    h (i (genericPoint Z)) = chowDegree (reduceMod v (ptIdeal p s (i (genericPoint Z)))) (e + 1) *
      Real.log (Ideal.absNorm v.asIdeal) := by
  obtain ⟨hE', hpt, -⟩ := stPull (𝓞 K) X Z p L.B m s i hE
  have hproj : IsProjOver (i ≫ p) := GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion i hX.isProjOver
  have hv' : (ptIdeal (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) (genericPoint Z)).comap CC = v.asIdeal := by
    rw [hpt]
    exact hv
  obtain ⟨x, hx⟩ := hV K Z (i ≫ p) (L.B.pull i) m (fun k => GlobalTheory.secPull (s k) i) v e hproj hE' hv' hd
  rw [hpt] at hx
  letI := x
  have hbij := Ideal.bijective_algebraMap_quotient_residueField v.asIdeal
  have hcard : Nat.card v.asIdeal.ResidueField = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  haveI : Finite v.asIdeal.ResidueField := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    intro h0
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  rw [hh.vertical Z i v.asIdeal.ResidueField e hd, hx, hcard]
  push_cast
  rfl

private theorem exists_isMultiHomog_of_isChowForm_dvd {F : Type} [Field F] {k n δ : ℕ} {f g : MvPolynomial (Fin k × Fin n) F}
    {I : Ideal (MvPolynomial (Fin n) F)} (hg : IsChowForm I k g) (hf : IsMultiHomog δ f) (hf0 : f ≠ 0)
    (hdvd : g ∣ f) : ∃ a, IsMultiHomog a g := by
  classical
  have hgrp := GroundTheory.Heights₂.Heights.isWeightedHomogeneous_inGroup_of_dvd hf hf0 hdvd
  choose a ha using hgrp
  have hw : ∀ (d : Fin k × Fin n →₀ ℕ) (i : Fin k),
      Finsupp.weight (GroundTheory.Heights₂.Heights.groupWeight k n) d i =
        Finsupp.weight (GroundTheory.Heights₂.Heights.inGroup i) d := by
    intro d i
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      GroundTheory.Heights₂.Heights.groupWeight, GroundTheory.Heights₂.Heights.inGroup, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x.1 = i
    · simp [hx]
    · simp [hx, Ne.symm hx]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨0, fun d _ => funext fun i => i.elim0⟩
  · refine ⟨a ⟨0, hk⟩, fun d hd => funext fun i => ?_⟩
    rw [hw d i, ha i hd]
    exact GroundTheory.Heights₂.Heights.IsChowForm.degrees_eq hg ha i ⟨0, hk⟩

private theorem core_lemma (hV : StVert) (hA : StArch) (hR : GroundTheory.Heights₂.Heights.ChowHeightRecursion.Statement)
    (hS : GroundTheory.Heights₂.Heights.ChowFormSection.Statement) (hMul : GroundTheory.Heights₂.Heights.ChowHeightMul.Statement)
    (hPt : GroundTheory.Heights₂.Heights.ProjPrimeHasPoint.Statement) (hX : IsArithVar p D) (hE : Emb p s)
    (hF : ∀ σ : K →+* ℂ, IsFS (L.φ (σ.comp (algebraMap (𝓞 K) K))) s (H.normAt σ)) (hh : L.IsArithHeight h) (e : ℕ)
    (ih : ∀ e', e = e' + 1 → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
      (ptIdeal p s (i (genericPoint Z))).comap CC = ⊥ → topologicalKrullDim Z = (e' + 1 : ℕ) →
      ∀ (δ : ℕ) (f : MvPolynomial (Fin (e' + 1) × Fin m) K),
      IsChowForm ((ptIdeal p s (i (genericPoint Z))).map φ) (e' + 1) f → IsMultiHomog δ f →
      h (i (genericPoint Z)) = (Module.finrank ℚ K : ℝ) * chowHt H (e' + 1) δ f)
    (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hc0 : (ptIdeal p s (i (genericPoint Z))).comap CC = ⊥) (hd : topologicalKrullDim Z = (e + 1 : ℕ))
    (δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin m) K)
    (hf : IsChowForm ((ptIdeal p s (i (genericPoint Z))).map φ) (e + 1) f) (hδ : IsMultiHomog δ f) :
    h (i (genericPoint Z)) = (Module.finrank ℚ K : ℝ) * chowHt H (e + 1) δ f := by
  classical
  obtain ⟨hE', hpt', hcomb'⟩ := stPull (𝓞 K) X Z p L.B m s i hE
  have hQpt : ptIdeal (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) (genericPoint Z) =
      ptIdeal p s (i (genericPoint Z)) := hpt' _
  have hc : CharZero Γ(Z, ⊤) := (charZero_iff hE').mpr (by rw [hQpt]; exact hc0)
  have hXZ : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc hd
  haveI : IsLocallyNoetherian Z := hXZ.isLocallyNoetherian
  have hQproj : IsProjPrime (ptIdeal p s (i (genericPoint Z))) := ChowFormHeightComparison₂.CF.P.isProjPrime hE _
  have hIproj : IsProjPrime ((ptIdeal p s (i (genericPoint Z))).map φ) := isProjPrime_map hQproj hc0
  obtain ⟨j, hj⟩ := ChowFormHeightComparison₂.CF.P.exists_mem hE (i (genericPoint Z))
  have hu : IsComb p s (Pi.single j 1) (s j) := isComb_single j
  have hnQ : GroundTheory.Heights₂.Heights.linForm (Pi.single j 1 : Fin m → 𝓞 K) ∉ ptIdeal p s (i (genericPoint Z)) :=
    (ChowFormHeightComparison₂.CF.P.mem_iff hE hu _).mp hj
  have hn : GroundTheory.Heights₂.Heights.linForm (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K)) ∉
      (ptIdeal p s (i (genericPoint Z))).map φ := by
    intro hmem
    apply hnQ
    rw [← map_linForm] at hmem
    have hmem' := Ideal.mem_comap.mpr hmem
    rwa [comap_map hQproj.isPrime hc0] at hmem'
  have hu' := hcomb' _ _ hu
  have hη : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull (s j) i) := by
    rw [ChowFormHeightComparison₂.CF.P.mem_iff hE' hu' (genericPoint Z), hQpt]
    exact hnQ
  have hstep := step hA hX hE hF hh i hc hd rfl ⟨f, hf⟩ hIproj hu hn hη
  have hrec := hR K m e δ H _ f _ hIproj hf hδ hn
  obtain ⟨hdiv1, hdiv2⟩ := stDiv (𝓞 K) Z (i ≫ p) (L.B.pull i) m (fun k => GlobalTheory.secPull (s k) i) hE'
    (Pi.single j 1) (GlobalTheory.secPull (s j) i) hu' hη
  have hmult : ∀ z : Z, (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z ≠ 0 ↔
      ptIdeal p s (i z) ∈ relComps (ptIdeal p s (i (genericPoint Z)) ⊔
        Ideal.span {GroundTheory.Heights₂.Heights.linForm (Pi.single j 1 : Fin m → 𝓞 K)}) := by
    intro z
    have h1 := hdiv1 z
    rw [hpt', hpt'] at h1
    exact h1
  have hmu : ∀ z : Z, (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z ≠ 0 →
      (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z =
        (localMult (ptIdeal p s (i (genericPoint Z)) ⊔
          Ideal.span {GroundTheory.Heights₂.Heights.linForm (Pi.single j 1 : Fin m → 𝓞 K)}) (ptIdeal p s (i z)) : ℤ) := by
    intro z hz
    have h1 := hdiv2 z hz
    rw [hpt', hpt'] at h1
    exact h1
  have hPtinj : Function.Injective (fun z : Z => ptIdeal p s (i z)) := by
    intro a b hab
    apply ChowFormHeightComparison₂.CF.P.injective hE'
    simp only [hpt']
    exact hab
  have hrelfin : (relComps (ptIdeal p s (i (genericPoint Z)) ⊔
      Ideal.span {GroundTheory.Heights₂.Heights.linForm (Pi.single j 1 : Fin m → 𝓞 K)})).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset (fun W hW => hW.1)
  have hSfin : {z : Z | (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z ≠ 0}.Finite :=
    (hrelfin.preimage hPtinj.injOn).subset (fun z hz => (hmult z).mp hz)
  have hmemS : ∀ z, z ∈ hSfin.toFinset ↔ (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z ≠ 0 :=
    fun z => by simp
  have hrel : ∀ W, W ∈ relComps (ptIdeal p s (i (genericPoint Z)) ⊔
      Ideal.span {GroundTheory.Heights₂.Heights.linForm (Pi.single j 1 : Fin m → 𝓞 K)}) ↔
      ∃ z ∈ hSfin.toFinset, ptIdeal p s (i z) = W := by
    intro W
    constructor
    · intro hW
      have hWproj : IsProjPrime W := isProjPrime_of_relComps
        (GroundTheory.Heights₂.Heights.isHomogIdeal_sup_span_linForm hQproj.isHomog _) hW
      have hle : ptIdeal (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) (genericPoint Z) ≤ W := by
        rw [hQpt]
        exact le_trans le_sup_left hW.1.1.2
      obtain ⟨z, hz⟩ := ChowFormHeightComparison₂.CF.P.exists_pt hE' W hWproj hle
      rw [hpt'] at hz
      exact ⟨z, (hmemS z).mpr ((hmult z).mpr (hz ▸ hW)), hz⟩
    · rintro ⟨z, hz, rfl⟩
      exact (hmult z).mp ((hmemS z).mp hz)
  have hμ : ∀ z ∈ hSfin.toFinset, (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z =
      (localMult (ptIdeal p s (i (genericPoint Z)) ⊔
        Ideal.span {GroundTheory.Heights₂.Heights.linForm (Pi.single j 1 : Fin m → 𝓞 K)}) (ptIdeal p s (i z)) : ℤ) :=
    fun z hz => hmu z ((hmemS z).mp hz)
  have hμne : ∀ z ∈ hSfin.toFinset, (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z ≠ 0 :=
    fun z hz => (hmemS z).mp hz
  have hsub : ∀ z ∈ hSfin.toFinset, ∃ (Zz : Scheme.{0}) (jz : Zz ⟶ Z) (_ : IsClosedImmersion jz)
      (_ : IsIntegral Zz), jz (genericPoint Zz) = z ∧ topologicalKrullDim Zz = e := by
    intro z hz
    obtain ⟨Zz, jz, hjz, hZz, hgen⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
    refine ⟨Zz, jz, hjz, hZz, hgen, ?_⟩
    exact stDim (𝓞 K) Z (i ≫ p) e hXZ Zz jz
      (by rw [hgen]; exact GlobalTheory.Cartier.CartierDiv.coheight_eq_one_of_mult_ne_zero ((hmemS z).mp hz))
  have hvg : ∀ z ∈ hSfin.toFinset, ∀ v : HeightOneSpectrum (𝓞 K), (ptIdeal p s (i z)).comap CC = v.asIdeal →
      h (i z) = chowDegree (reduceMod v (ptIdeal p s (i z))) (e + 1) * Real.log (Ideal.absNorm v.asIdeal) := by
    intro z hz v hv
    obtain ⟨Zz, jz, hjz, hZz, hgen, hdz⟩ := hsub z hz
    haveI := hjz
    haveI := hZz
    have hv' : (ptIdeal p s ((jz ≫ i) (genericPoint Zz))).comap CC = v.asIdeal := by
      show (ptIdeal p s (i (jz (genericPoint Zz)))).comap CC = v.asIdeal
      rw [hgen]
      exact hv
    have hfin : h (i (jz (genericPoint Zz))) = chowDegree (reduceMod v (ptIdeal p s (i (jz (genericPoint Zz)))))
        (e + 1) * Real.log (Ideal.absNorm v.asIdeal) := height_vertical hV hX hE hh (jz ≫ i) hdz v hv'
    rw [hgen] at hfin
    exact hfin
  have hvert := vertTerm_eq (S := hSfin.toFinset) (Pt := fun z => ptIdeal p s (i z))
    (μ := fun z => (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z)
    hQproj.isPrime hc0 hPtinj hrel hμ (e + 1) (fun z => h (i z)) hvg
  have hdc := divCycle_eq (S := hSfin.toFinset) (Pt := fun z => ptIdeal p s (i z))
    (μ := fun z => (divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z) hPtinj hrel hμ hμne
  obtain ⟨c, hcne, g, hg, hspec⟩ := hS K m e ((ptIdeal p s (i (genericPoint Z))).map φ) f _ hIproj hf hn
  have hCc : (MvPolynomial.C c : MvPolynomial (Fin e × Fin m) K) ≠ 0 := by simpa using hcne
  have hspec0 : specFirst f (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K)) ≠ 0 := by
    rw [hspec]
    exact mul_ne_zero hCc (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hfs : ∑ᶠ z, ((divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z : ℝ) * h (i z) =
      ∑ z ∈ hSfin.toFinset, ((divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z : ℝ) * h (i z) := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    rw [Function.mem_support] at hz
    rw [Finset.mem_coe, hmemS]
    intro h0
    apply hz
    rw [h0]
    simp
  rw [← Finset.sum_filter_add_sum_filter_not hSfin.toFinset (fun z => (ptIdeal p s (i z)).comap CC = ⊥)] at hfs
  have hd0 : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hhor : ∑ z ∈ hSfin.toFinset with (ptIdeal p s (i z)).comap CC = ⊥,
      ((divOfSec (L.restr i).isLB (GlobalTheory.secPull (s j) i) hη).mult z : ℝ) * h (i z) =
      (Module.finrank ℚ K : ℝ) * chowHt H e δ (specFirst f (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))) := by
    by_cases he : e = 0
    · subst he
      have hempty : hSfin.toFinset.filter (fun z => (ptIdeal p s (i z)).comap CC = ⊥) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro z hz hzc
        have hW := hdc.1 z hz hzc
        exact GroundTheory.Heights₂.Heights.not_isChowForm_zero hPt
          (isProjPrime_map (ChowFormHeightComparison₂.CF.P.isProjPrime hE _) hzc) _ (hg _ hW)
      rw [hempty, Finset.sum_empty]
      have hsupp : (divCycle ((ptIdeal p s (i (genericPoint Z))).map φ)
          (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))).support = ∅ := by
        have h1 := hdc.2 (fun _ => 1)
        rw [hempty, Finset.sum_empty] at h1
        simp only [mul_one] at h1
        rw [Finset.eq_empty_iff_forall_notMem]
        intro W hW
        have hpos := (Finset.sum_eq_zero_iff_of_nonneg (fun W _ => Nat.cast_nonneg _)).mp h1 W hW
        rw [Nat.cast_eq_zero] at hpos
        exact (Finsupp.mem_support_iff.mp hW) hpos
      rw [hspec, hsupp, Finset.prod_empty, mul_one,
        GroundTheory.Heights₂.Heights.chowHt_zero_groups_eq_zero H δ hCc, mul_zero]
    · obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
      have hdeg : ∀ W ∈ (divCycle ((ptIdeal p s (i (genericPoint Z))).map φ)
          (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))).support, ∃ a, IsMultiHomog a (g W) := by
        intro W hW
        refine exists_isMultiHomog_of_isChowForm_dvd (hg W hW) (hδ.specFirst _) hspec0 ?_
        rw [hspec]
        exact Dvd.dvd.mul_left ((dvd_pow_self (g W) (Finsupp.mem_support_iff.mp hW)).trans
          (Finset.dvd_prod_of_mem (fun W => g W ^ (divCycle ((ptIdeal p s (i (genericPoint Z))).map φ)
            (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))) W) hW)) _
      choose! δW hδW using hdeg
      have hIH : ∀ z ∈ hSfin.toFinset, (ptIdeal p s (i z)).comap CC = ⊥ →
          h (i z) = (Module.finrank ℚ K : ℝ) * chowHt H (e' + 1) (δW ((ptIdeal p s (i z)).map φ))
            (g ((ptIdeal p s (i z)).map φ)) := by
        intro z hz hzc
        obtain ⟨Zz, jz, hjz, hZz, hgen, hdz⟩ := hsub z hz
        haveI := hjz
        haveI := hZz
        have hW := hdc.1 z hz hzc
        have key : h (i (jz (genericPoint Zz))) = (Module.finrank ℚ K : ℝ) * chowHt H (e' + 1)
            (δW ((ptIdeal p s (i z)).map φ)) (g ((ptIdeal p s (i z)).map φ)) :=
          ih e' rfl Zz (jz ≫ i)
            (by show (ptIdeal p s (i (jz (genericPoint Zz)))).comap CC = ⊥; rw [hgen]; exact hzc) hdz
            (δW ((ptIdeal p s (i z)).map φ)) (g ((ptIdeal p s (i z)).map φ))
            (by show IsChowForm ((ptIdeal p s (i (jz (genericPoint Zz)))).map φ) (e' + 1) _
                rw [hgen]; exact hg _ hW) (hδW _ hW)
        rw [hgen] at key
        exact key
      have hprodH : IsMultiHomog (∑ W ∈ (divCycle ((ptIdeal p s (i (genericPoint Z))).map φ)
          (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))).support,
            (divCycle ((ptIdeal p s (i (genericPoint Z))).map φ)
              (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))) W * δW W)
          (MvPolynomial.C c * ∏ W ∈ (divCycle ((ptIdeal p s (i (genericPoint Z))).map φ)
            (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))).support,
              g W ^ (divCycle ((ptIdeal p s (i (genericPoint Z))).map φ)
                (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))) W) := by
        have h1 := (MvPolynomial.isWeightedHomogeneous_C (GroundTheory.Heights₂.Heights.groupWeight (e' + 1) m) c).mul
          (MvPolynomial.IsWeightedHomogeneous.prod _ _ _ (fun W hW => (hδW W hW).pow
            ((divCycle ((ptIdeal p s (i (genericPoint Z))).map φ)
              (fun k => ((Pi.single j 1 : Fin m → 𝓞 K) k : K))) W)))
        unfold IsMultiHomog
        convert h1 using 1
        funext x
        simp [Finset.sum_apply]
      have hδeq := MvPolynomial.IsWeightedHomogeneous.inj_right hspec0 (hδ.specFirst _)
        (by rw [hspec]; exact hprodH)
      rw [Finset.sum_congr rfl (fun z hz => by rw [hIH z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2])]
      rw [← hdc.2 (fun W => (Module.finrank ℚ K : ℝ) * chowHt H (e' + 1) (δW W) (g W))]
      rw [congrFun hδeq 0, hspec, GroundTheory.Heights₂.Heights.chowHt_C_mul_prod hMul H _ _ δW g
        (fun W hW => (hg W hW).1) hcne, Finset.mul_sum]
      refine Finset.sum_congr rfl fun W _ => ?_
      push_cast
      ring
  rw [hstep, hfs, hrec, hhor]
  simp only [ne_eq] at hvert
  rw [← hvert]
  field_simp
  ring

open Classical in
theorem core (hV : StVert) (hA : StArch) (hR : GroundTheory.Heights₂.Heights.ChowHeightRecursion.Statement)
    (hS : GroundTheory.Heights₂.Heights.ChowFormSection.Statement) (hMul : GroundTheory.Heights₂.Heights.ChowHeightMul.Statement)
    (hPt : GroundTheory.Heights₂.Heights.ProjPrimeHasPoint.Statement) (hX : IsArithVar p D) (hE : Emb p s)
    (hF : ∀ σ : K →+* ℂ, IsFS (L.φ (σ.comp (algebraMap (𝓞 K) K))) s (H.normAt σ)) (hh : L.IsArithHeight h) (e : ℕ) :
    ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
      (ptIdeal p s (i (genericPoint Z))).comap CC = ⊥ → topologicalKrullDim Z = (e + 1 : ℕ) →
      ∀ (δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin m) K),
      IsChowForm ((ptIdeal p s (i (genericPoint Z))).map φ) (e + 1) f → IsMultiHomog δ f →
      h (i (genericPoint Z)) = (Module.finrank ℚ K : ℝ) * chowHt H (e + 1) δ f := by
  induction e with
  | zero =>
    intro Z i _ _ hc0 hd δ f hf hδ
    exact core_lemma hV hA hR hS hMul hPt hX hE hF hh 0
      (fun e' he => absurd he (Nat.succ_ne_zero e').symm) Z i hc0 hd δ f hf hδ
  | succ e ih =>
    intro Z i _ _ hc0 hd δ f hf hδ
    refine core_lemma hV hA hR hS hMul hPt hX hE hF hh (e + 1) (fun e' he => ?_) Z i hc0 hd δ f hf hδ
    obtain rfl : e = e' := Nat.succ.inj he
    intro Z' i' _ _ hc' hd' δ' f' hf' hδ'
    exact ih Z' i' hc' hd' δ' f' hf' hδ'

end ChowFormHeightComparison₂.CF.M

namespace ChowFormHeightComparison₂.CF

theorem stMain_of (hV : StVert) (hA : StArch) (hR : GroundTheory.Heights₂.Heights.ChowHeightRecursion.Statement)
    (hS : GroundTheory.Heights₂.Heights.ChowFormSection.Statement) (hMul : GroundTheory.Heights₂.Heights.ChowHeightMul.Statement)
    (hPt : GroundTheory.Heights₂.Heights.ProjPrimeHasPoint.Statement) : StMain := by
  rintro K _ _ m H e Z _ p L s hX hE hF δ f hf hδ a ⟨h, hh, rfl⟩
  exact M.core hV hA hR hS hMul hPt hX hE hF hh e Z (𝟙 Z) ((M.charZero_iff hE).1 hX.charZero) hX.dim_eq δ f hf hδ

end ChowFormHeightComparison₂.CF
