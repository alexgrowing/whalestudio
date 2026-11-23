import Formalism.LocalToGlobal.GlobalTheory.Places
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLo
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
import Formalism.LogFactorialBounds.LogFactorialProofs.PrimeSum
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedSlopeExcessDecomposition

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Places

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.HN Formalism.LFunctionChainParameters

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem exists_prod_notMem (S : Finset (HeightOneSpectrum (𝓞 K))) (k : HeightOneSpectrum (𝓞 K) → ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    ∃ t : 𝓞 K, t ∈ ∏ w ∈ S, w.asIdeal ^ k w ∧ t ∉ v.asIdeal := by
  by_contra hcon
  push Not at hcon
  have hle : ∏ w ∈ S, w.asIdeal ^ k w ≤ v.asIdeal := fun t ht => hcon t ht
  obtain ⟨w, hw, hwv⟩ := (Ideal.IsPrime.prod_le v.isPrime).1 hle
  have h1 : w.asIdeal ≤ v.asIdeal := Ideal.IsPrime.le_of_pow_le (hP := v.isPrime) hwv
  have h2 : w.asIdeal = v.asIdeal := w.isMaximal.eq_of_le v.isPrime.ne_top h1
  exact hv ((HeightOneSpectrum.ext h2) ▸ hw)

theorem le_prod_smul (M N : Submodule (𝓞 K) V) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (k : HeightOneSpectrum (𝓞 K) → ℕ) (h : ∀ v ∈ S, DV.LocLe v (k v) N M) (h0 : ∀ v, v ∉ S → DV.LocLe v 0 N M) :
    N ≤ (∏ v ∈ S, v.asIdeal ^ k v) • M := by
  classical
  intro x hx
  refine Lnk.mem_of_locally _ x (fun v => ?_)
  obtain ⟨t, ht, htv⟩ := exists_prod_notMem (S.erase v) k v (Finset.notMem_erase v S)
  by_cases hv : v ∈ S
  · obtain ⟨s, hs, hsx⟩ := h v hv x hx
    refine ⟨t * s, fun hm => (v.isPrime.mem_or_mem hm).elim htv hs, ?_⟩
    rw [← Finset.mul_prod_erase S _ hv, mul_comm (v.asIdeal ^ k v), Submodule.mul_smul, mul_smul]
    exact Submodule.smul_mem_smul ht hsx
  · obtain ⟨s, hs, hsx⟩ := Lnk.locLe_zero (h0 v hv) x hx
    refine ⟨t * s, fun hm => (v.isPrime.mem_or_mem hm).elim htv hs, ?_⟩
    rw [Finset.erase_eq_of_notMem hv] at ht
    rw [mul_smul]
    exact Submodule.smul_mem_smul ht hsx

end General

section Slopes

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

def toFinPl (v : HeightOneSpectrum (𝓞 K)) : slopeLatticeData.FinPl K := ⟨v.asIdeal, v.isMaximal⟩

theorem lenLoc_eq_lenAt (v : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) :
    DV.lenLoc v N M = slopeLatticeData.lenAt (toFinPl v) M N := rfl

theorem mu_index_sum (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    {M N : Submodule (𝓞 K) V} (hM : M.FG) (hNM : N ≤ M) (hN0 : N ≠ ⊥) (hrk : rkK N = rkK M) :
    (∀ v, DV.lenLoc v N M ≠ ⊤) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 K)), (∀ v, v ∉ S → DV.lenLoc v N M = 0) →
      muDef b X N = muDef b X M - (∑ v ∈ S, 2 * lw K v * ((DV.lenLoc v N M).toNat : ℝ)) / (rkK M : ℝ) := by
  classical
  have hidx := slopeLatticeData.relIndex_ne_zero b X hX hM hNM hrk
  obtain ⟨k, hk, hc⟩ := slopeLatticeData.index_finsupp M N hidx
  have hlen : ∀ v, DV.lenLoc v N M = (k (toFinPl v) : ℕ∞) := fun v => hk (toFinPl v)
  refine ⟨fun v => by rw [hlen]; exact ENat.natCast_ne_top _, fun S hS => ?_⟩
  have hinj : Set.InjOn (toFinPl (K := K)) S := fun a _ c _ hac =>
    HeightOneSpectrum.ext (congrArg Subtype.val hac)
  have hne : ∀ w : slopeLatticeData.FinPl K, ((Ideal.absNorm w.1 : ℕ) : ℝ) ≠ 0 := fun w => by
    exact_mod_cast fun h => slopeLatticeData.finPl_ne_bot w (Ideal.absNorm_eq_zero_iff.1 h)
  have hsub : k.support ⊆ S.image toFinPl := by
    intro w hw
    rw [Finset.mem_image]
    refine ⟨⟨w.1, w.2.isPrime, slopeLatticeData.finPl_ne_bot w⟩, ?_, rfl⟩
    by_contra hv
    have h1 := hS _ hv
    rw [hlen] at h1
    have h2 : k w = 0 := by exact_mod_cast h1
    exact (Finsupp.mem_support_iff.1 hw) h2
  have hsum : Real.log ((k.prod fun w j => Ideal.absNorm w.1 ^ j : ℕ) : ℝ) =
      ∑ v ∈ S, (k (toFinPl v) : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    unfold Finsupp.prod
    rw [Nat.cast_prod, Real.log_prod (fun w _ => by push_cast; exact pow_ne_zero _ (hne w))]
    have e := Finset.sum_image (f := fun w : slopeLatticeData.FinPl K => (k w : ℝ) * Real.log (Ideal.absNorm w.1 : ℝ)) hinj
    refine Eq.trans ?_ e
    refine (Finset.sum_subset hsub (fun w _ hw => ?_)).trans (Finset.sum_congr rfl fun w _ => ?_)
    · rw [Finsupp.notMem_support_iff.1 hw]; simp
    · rw [Nat.cast_pow, Real.log_pow]
  rw [slopeLatticeData.muDef_index b X hX hM hNM hN0 hrk, hc, hsum]
  congr 1
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  rw [← div_div]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hlen, ENat.toNat_natCast]
  unfold lw
  ring

end Slopes

section Record

variable {D : D7} {L : SizeData₂ D}

theorem nuLat_span (hc : Lnk.NuCommens D L) (u : D.what₂.Word) :
    Submodule.span D.what₂.LL (L.NuLat u : Set (D.div.Nu u).V) = ⊤ := by
  obtain ⟨-, c, hc0, hcM⟩ := hc u
  rw [eq_top_iff, ← Lnk.mramSpan D u, Submodule.span_le]
  intro y hy
  have e : y = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL c)⁻¹ • (c • y) := by
    rw [Lnk.int_smul c y, smul_smul, inv_mul_cancel₀ (Lnk.algMap_ne hc0), one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hcM y hy))

theorem rk_nuLat (hc : Lnk.NuCommens D L) (u : D.what₂.Word) : rkK (L.NuLat u) = rkK (DV.MramL D u) := by
  unfold rkK
  rw [nuLat_span hc u, Lnk.mramSpan D u]

theorem rk_nu (hN' : DV.NprimeDef D L) (hc : Lnk.NuCommens D L) (u : D.what₂.Word) :
    (D.div.Nu u).rank = rkK (DV.MramL D u) := by
  unfold HLat.rank rkK
  rw [(Lnk.nuFull_of hN' hc u).2, Lnk.mramSpan D u]

theorem mu_eq (hN' : DV.NprimeDef D L) (hNu : DV.NuDef D L) (hc : Lnk.NuCommens D L) (u : D.what₂.Word)
    (hle : L.NuLat u ≤ DV.MramL D u) (hr : 0 < (D.div.Nu u).rank)
    (hoff : ∀ w, w ∉ L.supp → DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = 0 ∨ L.lenMN u w = 0) :
    (D.div.Nu u).mu = (LocalQuadraticParts.MuH D u).mu + ∑ w ∈ L.supp, 2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ) -
      (∑ w ∈ L.supp, 2 * SizeData₂.lwP w * ((L.lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ))) /
        ((D.div.Nu u).rank : ℝ) := by
  have hfull := Lnk.nuFull_of hN' hc
  have hX := D.div_good.2 u
  have h1 := J.mu_diff D L hN' u hX (hfull u).1 (J.ne_bot_of_rank_pos _ hr)
  have hrk := rk_nuLat hc u
  have hrk' := rk_nu hN' hc u
  have hN0 : L.NuLat u ≠ ⊥ := slopeLatticeData.ne_bot_of_rkK_pos (by rw [hrk, ← hrk']; exact hr)
  obtain ⟨hfin, h2⟩ := mu_index_sum (D.div.Nu u).b (D.div.Nu u).X hX (D.MramL_fg u) hle hN0 hrk
  have h3 := h2 (L.supp.map D.plEq.toEmbedding) (fun v hv => by
    have hw : D.plEq.symm v ∉ L.supp := fun hm => hv (Finset.mem_map.2 ⟨_, hm, by simp⟩)
    have hz : DV.lenLoc (D.plEq (D.plEq.symm v)) (L.NuLat u) (DV.MramL D u) = 0 := by
      rcases hoff _ hw with h0 | h0
      · exact h0
      · obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 (hfin (D.plEq (D.plEq.symm v)))
        have h5 := hNu.2.2 u _ l hl.symm
        rw [h0] at h5
        have h6 : l = 0 := by
          have : (l : ℝ) = 0 := by rw [h5]; simp
          exact_mod_cast this
        rw [← hl, h6]; rfl
    rwa [Equiv.apply_symm_apply] at hz)
  rw [Finset.sum_map] at h3
  have h4 : ∀ w ∈ L.supp, 2 * lw D.what₂.LL (D.plEq.toEmbedding w) *
      ((DV.lenLoc (D.plEq.toEmbedding w) (L.NuLat u) (DV.MramL D u)).toNat : ℝ) =
      2 * SizeData₂.lwP w * ((L.lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ)) := by
    intro w _
    obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 (hfin (D.plEq w))
    have h5 := hNu.2.2 u w l hl.symm
    show 2 * SizeData₂.lwP w * ((DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u)).toNat : ℝ) = _
    rw [← hl, ENat.toNat_natCast, h5]
  rw [Finset.sum_congr rfl h4] at h3
  have h1' : (L.NuH u).mu = muDef (D.div.Nu u).b (D.div.Nu u).X (L.NuLat u) := rfl
  have h6 : (LocalQuadraticParts.MuH D u).mu = muDef (D.div.Nu u).b (D.div.Nu u).X (DV.MramL D u) := rfl
  rw [h1', h3] at h1
  rw [h6, hrk']
  linarith

theorem muMax_le (hN' : DV.NprimeDef D L) (hc : Lnk.NuCommens D L) (u : D.what₂.Word)
    (hr : 0 < (D.div.Nu u).rank) (k : D.what₂.places.Pl → ℕ)
    (hloc : ∀ w ∈ L.supp, DV.LocLe (D.plEq w) (k w) (L.NuLat u) (DV.MramL D u))
    (hloc0 : ∀ w, w ∉ L.supp → DV.LocLe (D.plEq w) 0 (L.NuLat u) (DV.MramL D u)) :
    (D.div.Nu u).muMax ≤ (LocalQuadraticParts.MuH D u).muMax +
      ∑ w ∈ L.supp, 2 * SizeData₂.lwP w * ((⌊DV.ur D w (L.sg u w)⌋ : ℝ) - (k w : ℝ)) := by
  have hX := D.div_good.2 u
  have hrk' := rk_nu hN' hc u
  have hM0 : DV.MramL D u ≠ ⊥ := slopeLatticeData.ne_bot_of_rkK_pos (by rw [← hrk']; exact hr)
  set Jd : Ideal (𝓞 D.what₂.LL) := ∏ w ∈ L.supp, (D.plEq w).asIdeal ^ k w with hJd
  have hJ0 : Jd ≠ ⊥ := by
    rw [hJd, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro w _
    exact pow_ne_zero _ (D.plEq w).ne_bot
  have hle : L.NuLat u ≤ Jd • DV.MramL D u := by
    have h := le_prod_smul (DV.MramL D u) (L.NuLat u) (L.supp.map D.plEq.toEmbedding) (fun v => k (D.plEq.symm v))
      (fun v hv => by
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
        have := hloc w hw
        simpa using this)
      (fun v hv => by
        have hw : D.plEq.symm v ∉ L.supp := fun hm => hv (Finset.mem_map.2 ⟨_, hm, by simp⟩)
        have := hloc0 _ hw
        rwa [Equiv.apply_symm_apply] at this)
    rw [Finset.prod_map] at h
    simpa [hJd] using h
  have hI0 : DV.Iu D L u * (Jd : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ≠ 0 :=
    mul_ne_zero (J.Iu_ne_zero D L u) (FractionalIdeal.coeIdeal_ne_zero.2 hJ0)
  have hNL : (D.div.Nu u).L = Formalism.HermitianLatticesTheory.idealSmul
      ((DV.Iu D L u : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) : Submodule (𝓞 D.what₂.LL) D.what₂.LL)
      (L.NuLat u) := hN' u
  have hle2 : (D.div.Nu u).L ≤ Formalism.HermitianLatticesTheory.idealSmul
      ((DV.Iu D L u * (Jd : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) : Submodule (𝓞 D.what₂.LL) D.what₂.LL)
      (DV.MramL D u) := by
    rw [hNL, FractionalIdeal.coe_mul, slopeLatticeData.idealSmul_mul, slopeLatticeData.idealSmul_coeIdeal]
    exact slopeLatticeData.idealSmul_mono_right _ hle
  have h1 := slopeLatticeData.muMaxDef_mono (D.div.Nu u).b (D.div.Nu u).X hX (slopeLatticeData.idealSmul_fg _ (D.MramL_fg u)) hle2
    (J.ne_bot_of_rank_pos _ hr)
  have h2 := slopeLatticeData.muMaxDef_fractional_le (D.div.Nu u).b (D.div.Nu u).X hX (D.MramL_fg u) hM0 hI0
  have hJn : Real.log ((FractionalIdeal.absNorm
      (Jd : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) : ℚ) : ℝ) =
      ∑ w ∈ L.supp, (k w : ℝ) * Real.log (Ideal.absNorm (D.plEq w).asIdeal : ℝ) := by
    rw [FractionalIdeal.coeIdeal_absNorm, hJd, map_prod]
    push_cast
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [map_pow, Nat.cast_pow, Real.log_pow]
    · intro w _
      rw [map_pow, Nat.cast_pow]
      apply pow_ne_zero
      have : Ideal.absNorm (D.plEq w).asIdeal ≠ 0 := fun h => (D.plEq w).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast this
  rw [map_mul, Rat.cast_mul, Real.log_mul (slopeLatticeData.absNorm_pos (J.Iu_ne_zero D L u)).ne'
    (slopeLatticeData.absNorm_pos (FractionalIdeal.coeIdeal_ne_zero.2 hJ0)).ne', J.log_absNorm_Iu, hJn] at h2
  have h3 : ∑ w ∈ L.supp, 2 * SizeData₂.lwP w * ((⌊DV.ur D w (L.sg u w)⌋ : ℝ) - (k w : ℝ)) =
      -(2 * (-∑ w ∈ L.supp, (⌊DV.ur D w (L.sg u w)⌋ : ℝ) * Real.log (Ideal.absNorm (D.plEq w).asIdeal : ℝ) +
        ∑ w ∈ L.supp, (k w : ℝ) * Real.log (Ideal.absNorm (D.plEq w).asIdeal : ℝ)) /
        (Module.finrank ℚ D.what₂.LL : ℝ)) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold SizeData₂.lwP lw
    ring
  have h4 : (D.div.Nu u).muMax = muMaxDef (D.div.Nu u).b (D.div.Nu u).X (D.div.Nu u).L := rfl
  have h5 : (LocalQuadraticParts.MuH D u).muMax = muMaxDef (D.div.Nu u).b (D.div.Nu u).X (DV.MramL D u) := rfl
  rw [h3, h4, h5]
  linarith

end Record

section AtT

variable {D : D7} {L : SizeData₂ D}

theorem nlam_eq_sram (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : (D.fm u).seenP w = false) :
    LT.Nlam D u w = LT.Sram D u w := by
  have hV : LT.VVT D u w = ∅ := by unfold LT.VVT; simp [h]
  have hE : LT.expT D u w = 0 := by unfold LT.expT; rw [hV]; simp
  have hU : LT.Uprod D u 0 w = 1 := by unfold LT.Uprod; rw [hV, Finset.toList_empty]; rfl
  ext y
  unfold LT.Nlam
  rw [hE, hU, one_pow, zpow_zero, one_smul]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have e : (D.fm u).emb 0 y = (D.fm u).emb 0 x := hxy
    rw [(D.fm u).emb_inj 0 e]; exact hx
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem lenLoc_atT_zero (hAtT : NuAtTDef D L) {X : ErrX D} {K : G.Consts} {c : ErrC} (hE : L.EDef X K c)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = (D.mem u).A.T) (hs : w ∉ L.supp) :
    DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = 0 := by
  have hm : 1 ∈ SizeData₂.lifts D := Finset.mem_Icc.2 ⟨le_rfl, by have := D.R.two_le_m; omega⟩
  have h1 := hE u 1 hm w
  rw [L.E_supp u 1 w hs] at h1
  unfold Eval at h1
  simp only [if_pos hw] at h1
  have hseen : (D.fm u).seenP w = false := by
    by_contra hcon
    have ht : (D.fm u).seenP w = true := by simpa using hcon
    unfold EatT at h1
    rw [if_pos ht] at h1
    have hf : (0 : ℝ) < (D.R.f : ℝ) := by
      have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
      exact_mod_cast this
    have hN : (0 : ℝ) < G.Nm D := by
      unfold G.Nm
      exact_mod_cast D.R.N_pos D.R.m
    have h2 : (0 : ℝ) ≤ 2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℝ)) := by positivity
    have h3 : (0 : ℝ) ≤ ((topsOf D.host D.eTau).card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4 := by positivity
    have h4 := mul_pos hf hN
    linarith
  rw [D.lenLoc_atT hAtT u w hw, nlam_eq_sram D u w hseen, Submodule.comap_subtype_self]
  exact Module.length_eq_zero_iff.2 (Submodule.Quotient.subsingleton_iff.2 rfl)

end AtT

section Assemble

variable {D : D7} {L : SizeData₂ D}

theorem lE_nonneg (w : D.what₂.places.Pl) : 0 ≤ Lnk.lE w :=
  mul_nonneg (J.logWeight_nonneg w) (Nat.cast_nonneg _)

open Classical in

theorem places_at_of (C26 CMu C : ℝ) (hC26 : C26 ≤ C) (hCMu : CMu ≤ C)
    (hN' : DV.NprimeDef D L) (hNu : DV.NuDef D L) (hc : Lnk.NuCommens D L)
    (hrank : ∀ u, 0 < (D.div.Nu u).rank)
    (h26 : LocalQuadraticParts.adm26 L C26) (hMu : NprimeMuR L CMu)
    (hG1 : ∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
      DV.LocLe (D.plEq w) ⌊DV.ur D w (L.tau w)⌋₊ (L.NuLat u) (DV.MramL D u) ∧
      (L.lenMN u w : ℝ) ≤ (D.duS u : ℝ) * (L.tau w + L.io w))
    (htauN : ∀ w, ∃ n : ℕ, L.tau w = n) (hio : ∀ w, 0 ≤ L.io w)
    (htauT : ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → L.tau w = 0)
    (hoff : ∀ u w, w ∉ L.supp → DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) = 0 ∨ L.lenMN u w = 0)
    (hTa : ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) ≤ L.sc.b ^ 2)
    (hT2 : ∀ u, (2 : ℝ) < (D.mem u).A.T)
    (hT4 : ∀ u, 2 * (D.R.f : ℝ) / ((D.mem u).A.T : ℝ) ≤ 1 / 2)
    (hT1 : ∀ u, 4 * (D.R.f : ℝ) / ((D.mem u).A.T : ℝ) * L.sc.b ^ 2 +
      (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ≤ 1) :
    Lnk.Places_at L C := by
  intro u
  obtain ⟨c1, c2, c3, c4, c5⟩ := h26 u
  have hfull := Lnk.nuFull_of hN' hc
  have hdu0 : (D.div.Nu u).rank = (D.mem u).A.du := hfull.rank u
  have hdu : ((D.div.Nu u).rank : ℝ) = ((D.mem u).A.du : ℝ) := by rw [hdu0]
  have hr := hrank u
  have hduP : (0 : ℝ) < ((D.div.Nu u).rank : ℝ) := by exact_mod_cast hr
  have hdM : (0 : ℝ) < (D.duS u : ℝ) := by
    rcases Nat.eq_zero_or_pos (D.duS u) with h0 | h0
    · exfalso
      rw [hdu, c1, h0] at hduP
      simp at hduP
    · exact_mod_cast h0
  have hform : ((D.div.Nu u).rank : ℝ) = (D.duS u : ℝ) * (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := by
    rw [hdu, c1]; ring
  obtain ⟨d1, d2, d3, d4⟩ := UnitWeightPartition.deficit_bounds D.R.f ((D.mem u).A.T : ℝ) (D.duS u : ℝ)
    ((D.div.Nu u).rank : ℝ) hdM (hT2 u) hform
  have hAtT : Lnk.NuAtT D L := fun u' w hw => (h26 u').2.2.2.1 w hw
  have hle := Lnk.nu_le_mram hNu hAtT u
  have he : ∀ w, (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := fun w => by
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hmu := mu_eq hN' hNu hc u hle hr (hoff u)
  have hk : ∀ w, ((⌊DV.ur D w (L.tau w)⌋₊ : ℕ) : ℝ) = (D.what₂.places.ramIdx w : ℝ) * L.tau w := by
    intro w
    obtain ⟨n, hn⟩ := htauN w
    unfold DV.ur
    rw [hn]
    have e : ((D.what₂.places.ramIdx w : ℝ) * (n : ℝ)) = ((D.what₂.places.ramIdx w * n : ℕ) : ℝ) := by push_cast; ring
    rw [e, Nat.floor_natCast]
  have hmax := muMax_le hN' hc u hr (fun w => ⌊DV.ur D w (L.tau w)⌋₊)
    (fun w _ => by
      by_cases hw : D.what₂.places.resChar w = (D.mem u).A.T
      · have e : ⌊DV.ur D w (L.tau w)⌋₊ = 0 := by rw [htauT u w hw]; simp [DV.ur]
        rw [e]; exact c4 w hw
      · exact (hG1 u w hw).1)
    (fun w _ => by
      by_cases hw : D.what₂.places.resChar w = (D.mem u).A.T
      · exact c4 w hw
      · exact hNu.1 u w hw)
  have htau0 : ∀ w, 0 ≤ L.tau w := fun w => by
    obtain ⟨n, hn⟩ := htauN w
    rw [hn]; exact Nat.cast_nonneg _
  have hdiff := J.mu_diff D L hN' u (D.div_good.2 u) (hfull u).1 (J.ne_bot_of_rank_pos _ hr)
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  have ha : 0 < L.sc.a := mul_pos hx0 (Real.exp_pos _)
  have hb' : 0 < L.sc.b' := div_pos ha (Real.exp_pos _)
  refine ⟨fun w => (⌊DV.ur D w (L.sg u w)⌋ : ℝ) / (D.what₂.places.ramIdx w : ℝ),
    1 - ((D.div.Nu u).rank : ℝ) / (D.duS u : ℝ), (LocalQuadraticParts.MuH D u).mu, (LocalQuadraticParts.MuH D u).muMax,
    ∑ w ∈ Lnk.suppT L u, 2 * Lnk.lE w * (L.lenMN u w : ℝ) / ((D.div.Nu u).rank : ℝ),
    ∑ w ∈ L.supp, 2 * Lnk.lE w * (L.sg u w - (⌊DV.ur D w (L.sg u w)⌋ : ℝ) / (D.what₂.places.ramIdx w : ℝ)),
    ∑ w ∈ Lnk.suppT L u, 2 * Lnk.lE w * (L.lenMN u w : ℝ) / ((D.div.Nu u).rank : ℝ),
    ∑ w ∈ L.supp, 2 * Lnk.lE w * (L.sg u w - (⌊DV.ur D w (L.sg u w)⌋ : ℝ) / (D.what₂.places.ramIdx w : ℝ)),
    ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun w _ => lE_nonneg w, hdM, d2, d3, d1, Finset.filter_subset _ _,
      fun w hw => htauT u w (Finset.mem_filter.1 hw).2, fun w _ => hio w, ?_, le_refl _, le_refl _, ?_⟩
    · intro w hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_sdiff.mp hw
      exact (hG1 u w (fun h => hw2 (Finset.mem_filter.mpr ⟨hw1, h⟩))).2
    · rw [hmu]
      unfold UnitWeightPartition.Sg UnitWeightPartition.BeSum UnitWeightPartition.be
      rw [Finset.sum_div, add_sub_assoc, add_sub_assoc, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      have h1 := (he w).ne'
      have h2 := hduP.ne'
      unfold Lnk.lE
      field_simp
      ring
  · refine ⟨c2, d4, hT4 u, fun w _ => htau0 w, ?_, hT1 u, ?_, le_refl _, le_refl _⟩
    · refine le_trans (le_of_eq ?_) hTa
      unfold UnitWeightPartition.Ta
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      unfold SizeData₂.sz Lnk.lE
      ring
    · unfold UnitWeightPartition.IO Lnk.IOsum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      unfold Lnk.lE
      ring
  · refine ⟨fun w _ => lE_nonneg w, fun w _ => ?_, ?_, c3⟩
    · show (⌊DV.ur D w (L.sg u w)⌋ : ℝ) / (D.what₂.places.ramIdx w : ℝ) ≤ L.sg u w
      rw [div_le_iff₀ (he w), mul_comm]
      exact Int.floor_le _
    · refine le_trans hmax (le_of_eq ?_)
      congr 1
      unfold UnitWeightPartition.Sg
      refine Finset.sum_congr rfl fun w _ => ?_
      have h1 := (he w).ne'
      rw [hk w]
      unfold Lnk.lE
      field_simp
  · have h1 := c5 (Lnk.suppT L u) (fun w hw => (Finset.mem_filter.1 hw).2)
    have h2 : ∑ w ∈ Lnk.suppT L u, 2 * Lnk.lE w * (L.lenMN u w : ℝ) / ((D.div.Nu u).rank : ℝ) =
        (∑ w ∈ Lnk.suppT L u, SizeData₂.sz w (L.lenMN u w)) / ((D.mem u).A.du : ℝ) := by
      rw [Finset.sum_div, hdu]
      refine Finset.sum_congr rfl fun w _ => ?_
      unfold SizeData₂.sz Lnk.lE
      ring
    rw [h2]
    refine le_trans h1 ?_
    unfold LocalQuadraticParts.nTT
    have h3 : 0 ≤ (D.host.TT.card : ℝ) * (D.R.m * ((L.sc.a / D.R.k + L.sc.b') * Real.log ((D.mem u).A.T : ℝ))) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
        (add_nonneg (div_nonneg ha.le (Nat.cast_nonneg _)) hb'.le) (Real.log_natCast_nonneg _)))
    have h4 := mul_le_mul_of_nonneg_right hC26 h3
    simp only [mul_assoc] at h4 ⊢
    exact h4
  · have hX : 0 ≤ L.sc.X'' D.R.n := by
      unfold Scale.X'' Scale.w''
      exact div_nonneg ha.le (div_nonneg hb'.le (mul_nonneg hx0.le (Nat.cast_nonneg _)))
    have h1 := hMu u
    rw [hdiff] at h1
    have h2 : ∑ w ∈ L.supp, 2 * Lnk.lE w * (L.sg u w - (⌊DV.ur D w (L.sg u w)⌋ : ℝ) / (D.what₂.places.ramIdx w : ℝ)) =
        -(∑ w ∈ L.supp, 2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ) - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      have h3 := (he w).ne'
      unfold SizeData₂.sz Lnk.lE
      field_simp
      ring
    rw [h2]
    exact le_trans (neg_le_abs _) (le_trans h1 (mul_le_mul_of_nonneg_right hCMu hX))

end Assemble

section Sizes

theorem mertens (y : ℝ) (hy : 1 ≤ y) :
    ∑ p ∈ (Finset.range ⌈y⌉₊).filter Nat.Prime, Real.log p / p ≤ 2 * Real.log y := by
  have hy0 : 0 < y := by linarith
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hN1 : 1 ≤ ⌈y⌉₊ := Nat.one_le_ceil_iff.2 hy0
  obtain ⟨n, hn⟩ : ∃ n, ⌈y⌉₊ = n + 1 := ⟨⌈y⌉₊ - 1, by omega⟩
  have hny : (n : ℝ) < y := by
    have h := Nat.ceil_lt_add_one hy0.le
    rw [hn] at h
    push_cast at h
    linarith
  rcases le_or_gt 4 y with h4 | h4
  · have hn1 : 1 ≤ n := by
      have h := Nat.le_ceil y
      rw [hn] at h
      push_cast at h
      have : (2 : ℝ) < n := by linarith
      have : 2 < n := by exact_mod_cast this
      omega
    have h := Formalism.LogFactorialBounds.sum_primesLE_log_div_le n hn1
    have e : (Finset.range ⌈y⌉₊).filter Nat.Prime = Nat.primesLE n := by rw [hn]; rfl
    rw [e]
    have h1 : Real.log n ≤ Real.log y := Real.log_le_log (by exact_mod_cast hn1) hny.le
    have h2 : Real.log 4 ≤ Real.log y := Real.log_le_log (by norm_num) h4
    linarith
  · have hn3 : n ≤ 3 := by
      have : (n : ℝ) < 4 := by linarith
      have : n < 4 := by exact_mod_cast this
      omega
    rw [hn, Finset.sum_filter]
    have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    interval_cases n
    · simp [Nat.not_prime_zero]; exact hlog0
    · simp [Finset.sum_range_succ, Nat.not_prime_zero, Nat.not_prime_one]; exact hlog0
    · have h1 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by exact_mod_cast hny.le)
      simp [Finset.sum_range_succ, Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]
      linarith
    · have h1 : Real.log 3 ≤ Real.log y := Real.log_le_log (by norm_num) (by exact_mod_cast hny.le)
      have h2 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
      simp [Finset.sum_range_succ, Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two, Nat.prime_three]
      linarith

theorem size_alt (f b T : ℝ) (hf : 0 ≤ f) (hb : 16 * f ≤ b) (hb4 : 4 ≤ b) (hT : b ^ 3 ≤ T) :
    2 < T ∧ 2 * f / T ≤ 1 / 2 ∧ 4 * f / T * b ^ 2 + f * Real.log (T - 1) / (T - 2) ≤ 1 := by
  have hb0 : 0 < b := by linarith
  have hb2 : b ^ 2 ≤ T := by nlinarith [sq_nonneg b]
  have hbT : b ≤ T := by nlinarith
  have hT0 : 0 < T := by linarith
  have hT4 : 4 ≤ T := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [div_le_iff₀ hT0]; linarith
  · have h1 : 4 * f / T * b ^ 2 ≤ 1 / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hT0]
      have : 4 * f * b ^ 2 ≤ 1 / 4 * b ^ 3 := by
        have : 4 * f * b ^ 2 = (16 * f) * (b ^ 2 / 4) := by ring
        rw [this]
        have h2 := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ b ^ 2 / 4)
        nlinarith
      linarith
    have hs : b ≤ Real.sqrt T := Real.le_sqrt_of_sq_le hb2
    have hs0 : 0 < Real.sqrt T := by linarith
    have hlog : Real.log (T - 1) ≤ 2 * Real.sqrt T := by
      have h3 : Real.log (T - 1) ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
      have h4 : Real.log T = 2 * Real.log (Real.sqrt T) := by
        rw [Real.log_sqrt hT0.le]; ring
      have h5 := Real.log_le_sub_one_of_pos hs0
      linarith
    have h2 : f * Real.log (T - 1) / (T - 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by linarith)]
      have h6 : f * Real.log (T - 1) ≤ f * (2 * Real.sqrt T) := mul_le_mul_of_nonneg_left hlog hf
      have h7 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
      have h8 : 16 * f * Real.sqrt T ≤ Real.sqrt T * Real.sqrt T :=
        mul_le_mul_of_nonneg_right (le_trans hb hs) hs0.le
      nlinarith
    linarith

end Sizes

section Family

theorem exists_tau_eq_natCast {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p : ℕ) :
    ∃ n : ℕ, G.tauP X K a b p = n := by
  classical
  unfold G.tauP
  split_ifs
  · exact ⟨0, by simp⟩
  · exact ⟨X.ep p + ∑ t0 ∈ G.VV X K a b p, D.R.m * (⌈G.tv X K a b p t0⌉₊ + G.Dp K L p + 1), by push_cast; rfl⟩

theorem VV_empty_of_ge {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p : ℕ)
    (h : L.sc.X' ≤ (p : ℝ)) : G.VV X K a b p = ∅ := by
  by_contra hne
  exact absurd (G.TopChoiceBounds.bt_cand X K a b p hne).2.1 (not_lt.2 h)

theorem tau_eq_zero_of_le {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p : ℕ)
    (h : L.sc.X' ≤ (p : ℝ)) : G.tauP X K a b p = 0 := by
  unfold G.tauP
  rw [if_pos (VV_empty_of_ge X K a b p h)]

theorem sizes_at {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx5 : 5 ≤ L.sc.x) (hb9 : L.sc.x ^ 9 ≤ L.sc.b) :
    (D.R.f : ℝ) ≤ 2 * L.sc.x ^ 3 ∧ (D.R.m : ℝ) ≤ 2 * L.sc.x ^ 3 ∧ (D.host.TT.card : ℝ) ≤ 2 * L.sc.x ^ 3 ∧
    0 ≤ Real.log L.sc.X' ∧ Real.log L.sc.X' ≤ L.sc.x ∧ L.sc.X' ≤ L.sc.b ∧ L.sc.X' ≤ L.sc.X'' D.R.n ∧
    16 * (D.R.f : ℝ) ≤ L.sc.b ∧ 4 ≤ L.sc.b := by
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by
    refine le_trans S.1.2 ?_
    rw [← Real.rpow_natCast L.sc.x 3]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    unfold szTh
    push_cast
    linarith
  have hn0 : 0 < D.R.n := J.n_pos D.R
  have hn1 : (1 : ℝ) ≤ (D.R.n : ℝ) := by exact_mod_cast hn0
  have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by unfold Ranks.f; push_cast; ring
  have hm : (D.R.m : ℝ) ≤ (D.R.f : ℝ) := by
    have : D.R.m ≤ D.R.f := by unfold Ranks.f Ranks.n; exact D.R.m_le_f
    exact_mod_cast this
  have hd1 : L.sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hTT : (D.host.TT.card : ℝ) ≤ 2 * (D.R.n : ℝ) := by
    refine le_trans S.2.2.2.2.2.2.2.1.2 ?_
    unfold szNst
    have : 2 * (D.R.n : ℝ) * L.sc.delta1 ≤ 2 * (D.R.n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hd1 (by positivity)
    linarith
  have hlX : Real.log L.sc.X' = L.sc.x ^ (L.sc.eps / 3) := by unfold Scale.X'; rw [Real.log_exp]
  have hx3 : (1 : ℝ) ≤ L.sc.x ^ 3 := one_le_pow₀ hx1
  have hx6 : (32 : ℝ) ≤ L.sc.x ^ 6 := by
    have h2 : (5 : ℝ) ^ 6 ≤ L.sc.x ^ 6 := pow_le_pow_left₀ (by norm_num) hx5 6
    have h3 : (32 : ℝ) ≤ (5 : ℝ) ^ 6 := by norm_num
    linarith
  have h9 : L.sc.x ^ 9 = L.sc.x ^ 6 * L.sc.x ^ 3 := by ring
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlX]; exact Real.rpow_nonneg hx0.le _
  · rw [hlX]; exact J.scale_rpow_le_self_of_le_one L.sc (by linarith)
  · unfold Scale.X' Scale.b Scale.L
    exact Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  · rw [J.Xpp_eq L.sc D.R.n hn0]
    have hX0 : 0 < L.sc.X' := Real.exp_pos _
    have : (1 : ℝ) ≤ L.sc.x * D.R.n := by nlinarith
    nlinarith
  · have : 32 * L.sc.x ^ 3 ≤ L.sc.x ^ 6 * L.sc.x ^ 3 := mul_le_mul_of_nonneg_right hx6 (by linarith)
    linarith
  · have : 32 * 1 ≤ L.sc.x ^ 6 * L.sc.x ^ 3 := mul_le_mul hx6 hx3 (by norm_num) (by linarith)
    linarith

theorem ta_le {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx5 : 5 ≤ L.sc.x) (hb9 : L.sc.x ^ 9 ≤ L.sc.b) (C δ : ℝ)
    (hC : 4 * |C| + 1 ≤ L.sc.x) (hδ : δ ≤ 1) (h : CornerGLContinuity.WeightSumBound D L C (L.sc.b ^ δ)) :
    ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) ≤ L.sc.b ^ 2 := by
  obtain ⟨-, s2, s3, s4, s5, -, -, -, s9⟩ := sizes_at L S hx5 hb9
  have hx0 : 0 < L.sc.x := by linarith
  have hb0 : 0 < L.sc.b := by linarith
  have hb1 : 1 ≤ L.sc.b := by linarith
  refine le_trans h ?_
  have h1 : L.sc.b ^ δ ≤ L.sc.b := by
    calc L.sc.b ^ δ ≤ L.sc.b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 hδ
      _ = L.sc.b := Real.rpow_one _
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have hx3 : 0 ≤ 2 * L.sc.x ^ 3 := by positivity
  have hP : (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X' ≤
      (2 * L.sc.x ^ 3) * (2 * L.sc.x ^ 3) * (L.sc.x * L.sc.b) * L.sc.x := by
    rw [ha]
    have a1 : (D.R.m : ℝ) * (D.host.TT.card : ℝ) ≤ (2 * L.sc.x ^ 3) * (2 * L.sc.x ^ 3) :=
      mul_le_mul s2 s3 (Nat.cast_nonneg _) hx3
    have a2 : (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.x * L.sc.b) ≤
        (2 * L.sc.x ^ 3) * (2 * L.sc.x ^ 3) * (L.sc.x * L.sc.b) :=
      mul_le_mul_of_nonneg_right a1 (by positivity)
    exact mul_le_mul a2 s5 s4 (by positivity)
  have hP0 : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X' := by
    rw [ha]
    exact mul_nonneg (by positivity) s4
  have h2 : C * D.R.m * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X' ≤
      |C| * ((2 * L.sc.x ^ 3) * (2 * L.sc.x ^ 3) * (L.sc.x * L.sc.b) * L.sc.x) := by
    calc C * D.R.m * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X'
        = C * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X') := by ring
      _ ≤ |C| * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * Real.log L.sc.X') :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hP0
      _ ≤ _ := mul_le_mul_of_nonneg_left hP (abs_nonneg C)
  have hx8 : (1 : ℝ) ≤ L.sc.x ^ 8 := one_le_pow₀ (by linarith)
  have h3 : (4 * |C| + 1) * L.sc.x ^ 8 ≤ L.sc.x ^ 9 := by
    have : L.sc.x ^ 9 = L.sc.x * L.sc.x ^ 8 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hC (by linarith)
  have h4 : 4 * |C| * L.sc.x ^ 8 + 1 ≤ L.sc.b := by nlinarith [abs_nonneg C]
  have h5 : (4 * |C| * L.sc.x ^ 8 + 1) * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right h4 hb0.le
  have h6 : |C| * ((2 * L.sc.x ^ 3) * (2 * L.sc.x ^ 3) * (L.sc.x * L.sc.b) * L.sc.x) =
      4 * |C| * L.sc.x ^ 8 * L.sc.b := by ring
  rw [h6] at h2
  nlinarith

end Family

section Main

theorem placesF_of : PlaceConditionsFamily := by
  intro eps Fm crystallineComparison h10 tSet hTu hRank lG lMu
  have heps := Lnk.fam_eps_pos Fm
  have hDl : J.DlSize Fm :=
    ⟨Fm.x1 + 1, fun x hx i => (Fm.sizes x (by linarith) i).2.2.2.2.2.2.1.2.2.2.2.2.1⟩
  have h26 : LocalQuadraticParts.LevelTFamily Fm := by
    obtain ⟨a0, h10'⟩ := h10
    obtain ⟨a1, hS⟩ := tSet
    refine J.family_levelPrime_summary_closed Fm crystallineComparison hTu hDl ⟨max (max a0 a1) (Fm.x1 + 1), fun x hx i => ?_⟩
    have e0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have e1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have e2 : Fm.x1 < x := by have := le_trans (le_max_right (max a0 a1) (Fm.x1 + 1)) hx; linarith
    exact ⟨fun u => (h10' x e0 i u (hS x e1 e2 i u)).2.1, fun u => (h10' x e0 i u (hS x e1 e2 i u)).2.2.2.2.1⟩
  obtain ⟨xNC, hNC⟩ := Lnk.nuCommensF_of Fm crystallineComparison h10 tSet
  obtain ⟨CT, xT, δ, hδ, hTa⟩ := G.TopChoiceBounds.tau_sum_family_of_mertens Fm (fun _ _ => mertens)
  obtain ⟨C26, x26, h26⟩ := h26
  obtain ⟨CMu, xMu, hMu⟩ := lMu
  obtain ⟨CG, xG, δG, -, hG⟩ := lG
  obtain ⟨xR, hRank⟩ := hRank
  obtain ⟨xU, hTu⟩ := hTu
  obtain ⟨xE, hE⟩ := Lnk.ev_pow_le_exp 1 eps 9 one_pos heps
  obtain ⟨xM, hM⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 6
  obtain ⟨xD, hD⟩ : ∃ xD : ℝ, ∀ x ≥ xD, δ x ≤ 1 :=
    Filter.eventually_atTop.1 (hδ.eventually (Iic_mem_nhds zero_lt_one))
  refine ⟨max (max C26 CMu) 4,
    |xNC| + |xT| + |x26| + |xMu| + |xG| + |xR| + |xU| + |xE| + |xM| + |xD| + |Fm.x1| + 4 * |CT| + 5,
    le_max_right _ _, fun x hx i => ?_⟩
  have n1 := abs_nonneg xNC
  have n2 := abs_nonneg xT
  have n3 := abs_nonneg x26
  have n4 := abs_nonneg xMu
  have n5 := abs_nonneg xG
  have n6 := abs_nonneg xR
  have n7 := abs_nonneg xU
  have n8 := abs_nonneg xE
  have n9 := abs_nonneg xM
  have n10 := abs_nonneg xD
  have n11 := abs_nonneg Fm.x1
  have n12 := abs_nonneg CT
  have e1 : x ≥ xNC := by linarith [le_abs_self xNC]
  have e2 : x ≥ xT := by linarith [le_abs_self xT]
  have e3 : x ≥ x26 := by linarith [le_abs_self x26]
  have e4 : x ≥ xMu := by linarith [le_abs_self xMu]
  have e5 : x ≥ xG := by linarith [le_abs_self xG]
  have e6 : x ≥ xR := by linarith [le_abs_self xR]
  have e7 : x ≥ xU := by linarith [le_abs_self xU]
  have e8 : x ≥ xE := by linarith [le_abs_self xE]
  have e9 : xM ≤ x := by linarith [le_abs_self xM]
  have e10 : x ≥ xD := by linarith [le_abs_self xD]
  have hx1 : Fm.x1 < x := by linarith [le_abs_self Fm.x1]
  have hx5 : 5 ≤ x := by linarith
  have hxC : 4 * |CT| + 1 ≤ x := by linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have S := Fm.sizes x hx1 i
  have hb9 : (Fm.L x i).sc.x ^ 9 ≤ (Fm.L x i).sc.b := by
    have h := hE x e8 (by linarith)
    rw [one_mul] at h
    unfold Scale.b Scale.L
    rw [hsx, hse, ← Real.rpow_natCast x 9]
    exact_mod_cast h
  have hx5' : 5 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx5
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := sizes_at (Fm.L x i) S hx5' hb9
  have hb1 : 1 ≤ (Fm.L x i).sc.b := by linarith
  have hm6 : (6 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) S (by linarith)).1
    rw [hsx] at z1
    exact le_trans (hM x e9) z1
  have hTb : ∀ u, (Fm.L x i).sc.b ^ 3 ≤ (((Fm.D x i).mem u).A.T : ℝ) := by
    intro u
    refine le_trans ?_ ((hTu x e7 i).1 u)
    rw [← Real.rpow_natCast (Fm.L x i).sc.b 3]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    push_cast
    linarith
  have hXT : ∀ u, (Fm.L x i).sc.X' ≤ (((Fm.D x i).mem u).A.T : ℝ) := by
    intro u
    have h3 : (Fm.L x i).sc.b ≤ (Fm.L x i).sc.b ^ 3 := by
      have : (Fm.L x i).sc.b ^ 3 = (Fm.L x i).sc.b * (Fm.L x i).sc.b ^ 2 := by ring
      rw [this]
      have h2 : (1 : ℝ) ≤ (Fm.L x i).sc.b ^ 2 := one_le_pow₀ hb1
      nlinarith
    linarith [hTb u]
  have hsz := fun u => size_alt ((Fm.D x i).R.f : ℝ) (Fm.L x i).sc.b (((Fm.D x i).mem u).A.T : ℝ)
    (Nat.cast_nonneg _) s8 s9 (hTb u)
  have hfill := Fm.fills x hx1 i
  refine ⟨Lnk.IOsum_nonneg (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Fm.ex x hx1 i).kapI_def
    (fun w => (hfill w).2.2.2.2.2.1), ?_⟩
  refine places_at_of C26 CMu _ (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _)) (Fm.nprimeDef x hx1 i) (Fm.nuDef x hx1 i) (hNC x e1 i)
    (hRank x e6 i) (h26 x e3 i) (hMu x e4 i)
    (fun u w hw => ⟨((hG x e5 i).1 u w hw).1, ((hG x e5 i).1 u w hw).2.1⟩)
    (fun w => by rw [(hfill w).2.2.2.2.1]; exact exists_tau_eq_natCast _ _ _ _ _)
    (fun w => by
      rw [(hfill w).2.2.2.2.2.1]
      exact Lnk.ioP_nonneg (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Fm.ex x hx1 i).kapI_def _ _ _)
    (fun u w hw => by
      rw [(hfill w).2.2.2.2.1, hw]
      exact tau_eq_zero_of_le _ _ _ _ _ (hXT u))
    (fun u w hs => ?_)
    (ta_le (Fm.L x i) S hx5' hb9 CT (δ x) (by rw [hsx]; exact hxC) (hD x e10) (hTa x e2 i))
    (fun u => (hsz u).1) (fun u => (hsz u).2.1) (fun u => (hsz u).2.2)
  by_cases hw : (Fm.D x i).what₂.places.resChar w = ((Fm.D x i).mem u).A.T
  · exact Or.inl (lenLoc_atT_zero (Fm.ex x hx1 i).lat.atT (Fm.ex x hx1 i).err.edef u w hw hs)
  · refine Or.inr (Fm.lats0 x hx1 i w u (VV_empty_of_ge _ _ _ _ _ ?_) hw)
    have h1 : ¬ ((((Fm.D x i).what₂.places.resChar w : ℕ) : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) :=
      fun h => hs (Fm.supp_sat x hx1 i w h)
    linarith [not_le.1 h1]

theorem slope_lemma_division_form : SlopeBoundOfMuRank := by
  intro eps Fm crystallineComparison h10 tSet hTu hRank lG lMu
  obtain ⟨C, x0, -, h⟩ := Lnk.slopesNF_of Fm (placesF_of Fm crystallineComparison h10 tSet hTu hRank lG lMu)
  exact ⟨C, x0, fun x hx i _ u => h x hx i u⟩

end Main

section Link

theorem dlSize (eps : ℝ) (Fm : FamP eps) : J.DlSize Fm :=
  ⟨Fm.x1 + 1, fun x hx i => (Fm.sizes x (by linarith) i).2.2.2.2.2.2.1.2.2.2.2.2.1⟩

theorem settingF_of : LevelPrimeSettingFamily := by
  intro eps Fm hT
  obtain ⟨Cn, hN⟩ := J.numsL_wtsL_fam Fm hT (dlSize eps Fm)
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hT⟩ := hT
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  refine ⟨max (max x0 x1) (max x3 4), fun x hx hx1 i u => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : x ≥ x1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e4 : 4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hm : 4 ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x hx1 i) (by rw [hsx]; exact e4)).1
    rw [hsx] at z1
    have : (4 : ℝ) ≤ (Fm.D x i).R.m := le_trans (h3 x e3) z1
    exact_mod_cast this
  exact J.levelPrime_setting_of_sizes le_rfl (hN x e0 i).1 (hN x e0 i).2 (hT x e1 i).1 hm u

theorem slope_lemma_link_form : SlopeLemmaLinkForm := by
  intro eps Fm Cabs CH C0 crystallineComparison hC0 h10 hTu hCh hIn
  have tSet := settingF_of Fm hTu
  have hNF : NuFullF Fm := Lnk.nuFullF_of Fm (Lnk.nuCommensF_of Fm crystallineComparison h10 tSet)
  exact slope_lemma_division_form Fm crystallineComparison h10 tSet hTu (muRank_of_chosen Fm crystallineComparison hC0 hCh hNF h10 tSet) hIn.1 hIn.2.2.2.2

end Link

end Formalism.L2.GlobalTheoryTheory.Places

end

example {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (crystallineComparison : ℝ) (a : Formalism.MainNotions.product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (b : Formalism.MainNotions.GlobalTheoryTheory.SettingEventually Fm) (c : Formalism.MainNotions.TuSize Fm)
    (d : Formalism.MainNotions.J.MuRank Fm) : Formalism.MainNotions.LinkG Fm → Formalism.MainNotions.LinkMu Fm → Formalism.MainNotions.Lnk.PlacesF Fm :=
  Formalism.L2.GlobalTheoryTheory.Places.placesF_of Fm crystallineComparison a b c d

example {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cabs CH C0 crystallineComparison : ℝ) (h : 0 < C0) (a : Formalism.MainNotions.product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (c : Formalism.MainNotions.TuSize Fm) :
    Formalism.MainNotions.ChosenE Fm C0 CH → Formalism.MainNotions.GlobalTheoremInputs Fm Cabs CH C0 → Formalism.MainNotions.LocalQuadraticParts.SlopeLemmaFamily Fm :=
  Formalism.L2.GlobalTheoryTheory.Places.slope_lemma_link_form Fm Cabs CH C0 crystallineComparison h a c
