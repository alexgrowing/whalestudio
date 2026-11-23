import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.EtaValues

section General

variable {L : Type} [Field L] [NumberField L]

def hv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ℂ :=
  ((χ.val v : ℂˣ) : ℂ) * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ))⁻¹ : ℝ) : ℂ)

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 v.ne_bot)

theorem hv_ne_zero (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : hv χ v ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (absNorm_pos v)).ne'))

theorem valTw_eq (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : χ.valTw (1 / 2) v = hv χ v := by
  unfold HChar.valTw hv
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.ofReal_natCast, Complex.ofReal_neg]

open Classical in

def cnt (a : 𝓞 L) (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 L))).factors

theorem intValuation_eq {a : 𝓞 L} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 L)) :
    v.intValuation a = WithZero.exp (-(cnt a v : ℤ)) := by
  rw [HeightOneSpectrum.intValuation_if_neg _ ha]
  rfl

theorem ordF_eq {a : 𝓞 L} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 L)) : ordF v (GlobalTheory.Mem.ValAlg.uOf a ha) = cnt a v := by
  show -WithZero.log (v.valuation L (algebraMap (𝓞 L) L a)) = _
  rw [HeightOneSpectrum.valuation_of_algebraMap, intValuation_eq ha]
  simp

theorem cnt_eq_zero {a : 𝓞 L} (ha : a ≠ 0) {v : HeightOneSpectrum (𝓞 L)} (h : a ∉ v.asIdeal) : cnt a v = 0 := by
  have h1 := intValuation_eq ha v
  rw [HeightOneSpectrum.intValuation_eq_one_iff.2 h, ← WithZero.exp_zero, WithZero.exp_inj] at h1
  omega

theorem prod_hv (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hinf : χ.HasInf φ fun _ => 1) {a : 𝓞 L} (ha : a ≠ 0) (U : Finset (HeightOneSpectrum (𝓞 L)))
    (hU : ∀ v, a ∈ v.asIdeal → v ∈ U) :
    ∏ v ∈ U, hv χ v ^ cnt a v = (∏ i, φ i (algebraMap (𝓞 L) L a))⁻¹ := by
  classical
  have h0 : ∀ v, v ∉ U → cnt a v = 0 := fun v h => cnt_eq_zero ha (mt (hU v) h)
  have hp := GlobalTheory.TypeValues.productRule χ ∅ (fun v _ => hu v) (GlobalTheory.Mem.ValAlg.uOf a ha)
  have e1 : ∀ v, (∏ᶠ (_ : v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 L)))), χ.val v ^ ordF v (GlobalTheory.Mem.ValAlg.uOf a ha)) =
      χ.val v ^ cnt a v := fun v => by
    rw [finprod_eq_if, if_pos (Finset.notMem_empty v), ordF_eq, zpow_natCast]
  simp_rw [e1] at hp
  rw [Finset.prod_empty, mul_one, finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun v hv' => by
    by_contra h
    exact hv' (by simp only [h0 v h, pow_zero]))] at hp
  have hp' := congrArg (Units.val : ℂˣ → ℂ) hp
  rw [Units.val_mul, hinf, Units.val_one, Units.coe_prod] at hp'
  have hf := Ideal.finprod_heightOneSpectrum_factorization (I := Ideal.span {a}) (by simpa using ha)
  rw [finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun v hv' => by
    by_contra h
    refine hv' ?_
    show v.asIdeal ^ cnt a v = 1
    rw [h0 v h, pow_zero])] at hf
  have hN := GlobalTheory.Mem.ValAlg.absNorm_eq hL φ hφ a
  rw [← hf, map_prod, Nat.cast_prod] at hN
  have hN' : ∏ v ∈ U, Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) ^ cnt a v = ∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖ := by
    refine (pow_left_inj₀ (Finset.prod_nonneg fun _ _ => by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      two_ne_zero).1 ?_
    rw [← hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
    show _ = ((Ideal.absNorm (v.asIdeal ^ cnt a v) : ℕ) : ℝ)
    rw [map_pow, Nat.cast_pow]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← hp']
  unfold hv
  simp_rw [mul_pow, Finset.prod_mul_distrib, zpow_one, Finset.prod_div_distrib, Units.val_pow_eq_pow_val,
    ← Complex.ofReal_pow, ← Complex.ofReal_prod, inv_pow, Finset.prod_inv_distrib, hN', Complex.ofReal_inv]
  show _ = (∏ i, φ i (algebraMap (𝓞 L) L a)) / ((∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖ : ℝ) : ℂ) * _
  ring

theorem hv_mem (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hinf : χ.HasInf φ fun _ => 1) (M : Subfield ℂ) (hM : ∀ i x, φ i x ∈ M) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v, v ∉ S → hv χ v ∈ M) (P : HeightOneSpectrum (𝓞 L)) : hv χ P ∈ M := by
  classical
  by_cases hP : P ∈ S
  swap
  · exact hS P hP
  obtain ⟨b, hb1, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
    have := Ideal.pow_succ_lt_pow P.ne_bot 1 (P := P.asIdeal)
    rw [pow_one] at this
    exact SetLike.exists_of_lt this
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => 2)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have haP := ha P hP
  rw [if_pos rfl] at haP
  have ha2 : a ∉ P.asIdeal ^ 2 := fun h => hb2 (by simpa using (P.asIdeal ^ 2).sub_mem h haP)
  have ha1 : a ∈ P.asIdeal := by simpa using P.asIdeal.add_mem (Ideal.pow_le_self two_ne_zero haP) hb1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
  have hc : cnt a P = 1 := by
    have h1 := intValuation_eq ha0 P
    rw [GlobalTheory.TypeValues.intValuation_eq_of_mem ha1 ha2, WithZero.exp_inj] at h1
    omega
  have hfin : {v : HeightOneSpectrum (𝓞 L) | v.asIdeal ∣ Ideal.span {a}}.Finite :=
    Ideal.finite_factors (by simpa using ha0)
  have hU : ∀ v, a ∈ v.asIdeal ↔ v ∈ hfin.toFinset := fun v => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h := prod_hv hL φ hφ χ hu hinf ha0 hfin.toFinset fun v => (hU v).1
  rw [← Finset.mul_prod_erase _ _ ((hU P).1 ha1), hc, pow_one] at h
  rw [eq_div_of_mul_eq (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hv_ne_zero χ v)) h]
  refine div_mem (inv_mem (prod_mem fun i _ => hM i _)) (prod_mem fun v hv' => pow_mem (hS v fun hvS => ?_) _)
  obtain ⟨hvP, hva⟩ := Finset.mem_erase.1 hv'
  have h1 := ha v hvS
  rw [if_neg hvP] at h1
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  simpa using v.asIdeal.sub_mem ((hU v).2 hva) (Ideal.pow_le_self two_ne_zero h1)

theorem hv_mem_of_inert {F : Type} [Field F] [NumberField F] [Algebra F L] (χ : HChar L) (hr : χ.ResEta F)
    {v : HeightOneSpectrum (𝓞 L)} (hu : χ.UnrAt v) (ho : ∀ k : Fˣ, ordF v (upF F k) = ordF (v.under (𝓞 F)) k)
    (h1 : ((v.under (𝓞 F)).asIdeal.primesOver (𝓞 L)).ncard = 1)
    (hN : Ideal.absNorm v.asIdeal = Ideal.absNorm (v.under (𝓞 F)).asIdeal ^ 2) (M : Subfield ℂ) : hv χ v ∈ M := by
  have hab : aboveF (L := L) F (v.under (𝓞 F)) = {v} := by
    obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.1 h1
    have key : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v.under (𝓞 F) → w.asIdeal = Q := fun w hw => by
      have : w.asIdeal ∈ (v.under (𝓞 F)).asIdeal.primesOver (𝓞 L) := ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩
      rwa [hQ] at this
    ext P
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact ⟨fun h => HeightOneSpectrum.ext ((key P h).trans (key v rfl).symm), fun h => by rw [h]; rfl⟩
  have hval : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k : Kˣ),
      IsUnifAt w (atFin w k) ↔ ordF w k = 1 := by
    intro K _ _ w k
    have h : Valued.v ((atFin w k : (w.adicCompletion K)ˣ) : w.adicCompletion K) = w.valuation K (k : K) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : K)
    have h0 : w.valuation K (k : K) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
    unfold IsUnifAt ordF
    rw [h, ← WithZero.exp_log h0, WithZero.exp_inj, WithZero.log_exp]
    omega
  have hk := (hval _ _).1 (unif_spec (v.under (𝓞 F)))
  have h := hr.1 (v.under (𝓞 F)) (unif (v.under (𝓞 F)))
  rw [HChar.resFin, etaFin, hab, Finset.prod_singleton, MonoidHom.comp_apply, if_pos (Finset.card_singleton _), hk, zpow_one] at h
  have h2 : χ.val v = -1 := (χ.val_eq hu _ ((hval _ _).2 ((ho _).trans hk))).symm.trans h
  unfold hv
  rw [h2, hN, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_natCast, Units.val_neg,
    Units.val_one]
  exact mul_mem (neg_mem (one_mem _)) (inv_mem (natCast_mem _ _))

end General

end GlobalTheory.EtaValues

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.EtaValues

open Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hv_mem_host (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : Formalism.L2.Host.IsEtaT D.host χ) (T : Finset (Pl D.host.E))
    (hT : ∀ v, Bridge.SplitOff v (T : Set (Pl D.host.E)) → hv χ v ∈ D.what₂.embLL.fieldRange) (P : Pl D.host.E) :
    hv χ P ∈ D.what₂.embLL.fieldRange := by
  classical
  obtain ⟨c, -, hcm, ho, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  refine hv_mem hcm.cplx _ hcm.bij χ hχ.unr hχ.inf D.what₂.embLL.fieldRange (fun g x => ⟨D.embE (D.host.sigmaOf g x),
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)⟩) (T ∪ T.image conjPrime₂) (fun v hv' => ?_) P
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) v.asIdeal = v.asIdeal
  · have hm : v.asIdeal ∈ (v.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E) := ⟨v.isPrime, ⟨rfl⟩⟩
    rcases GlobalTheory.EtaEulerProduct.inert_or_split (σ := D.sp.cm.sig)
      ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩ (fun _ => rfl)
      D.sp.cm.cmUnram (v.under (𝓞 D.host.F)) with ⟨-, h1, h2⟩ | ⟨-, -, h2⟩
    · exact hv_mem_of_inert χ hχ.res (hχ.unr v) (ho v) h1 (h2 _ hm).2 _
    · exact absurd hc (h2 _ hm).1
  · exact hT v ⟨hc, fun h => hv' (Finset.mem_union_left _ h), fun w hw h => hv' (Finset.mem_union_right _ (Finset.mem_image.2
      ⟨w, hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)),
        GlobalTheory.RationalValues.conjP_conjP]⟩))⟩

theorem splitOff_mono {D : D7} {v : Pl D.host.E} {S S' : Set (Pl D.host.E)} (h : Bridge.SplitOff v S) (hS : S' ⊆ S) :
    Bridge.SplitOff v S' :=
  ⟨h.1, fun h' => h.2.1 (hS h'), fun w hw => h.2.2 w (hS hw)⟩

theorem etaVals : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), EtaVals R := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ P e he x hx
  have htie := hR.fam.tie
  obtain ⟨_, _, _, hT⟩ := htie
  have hok := hT.ok A.μ0
  have h := hv_mem_host D R.C.eta R.C.isEta (R.Sb ∪ R.Q A.μ0) (fun v hs => by
    rw [Finset.coe_union] at hs
    obtain ⟨Q, rfl⟩ := hR.fam.pl_onto v (splitOff_mono hs Set.subset_union_left)
    exact ⟨_, (hR.fam.etaVal Q ((hok Q).2 hs)).trans (valTw_eq _ _)⟩) P
  obtain ⟨y, hy⟩ := h
  refine ⟨y, hy.trans ?_⟩
  rw [hR.lev.eta.2 P e he _ x hx]
  rfl

end GlobalTheory.EtaValues

end
