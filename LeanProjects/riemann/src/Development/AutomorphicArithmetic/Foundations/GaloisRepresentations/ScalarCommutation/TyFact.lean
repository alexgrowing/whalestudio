import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPrimeMem

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
variable {x : E} {U : Submodule ℂ (UA E n → ℂ)} {w₀ : Plc E} {Up : Plc E → Prop}

private theorem cont_comp (w : Plc E) : Continuous (comp w : GUf E n → GL (Fin n) (w.adicCompletion E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp
    (continuous_fst.comp continuous_subtype_val)

private theorem th_eq (F : Frame S) (g : GUf E n) : F.th g = UpperTheory.Gal.CertificateRingHomMap.th g :=
  Subtype.ext (Prod.ext (Units.ext ((F.th_mat g).trans (UpperTheory.Gal.CertificateRingHomMap.invT_val _).symm)) (F.th_sim g))

private theorem pr_loc_one {F : Frame S} {w u : Spl E p} {L : Loc S.G.GAf (GLw n w.1)} {L' : Loc S.G.GAf (GLw n u.1)}
    (hf : IsFac F w L) (hf' : IsFac F u L') (h : GlobalTheory.Cong.Apart w.1 u.1) (y : GLw n u.1) : L.pr (L'.loc y) = 1 := by
  rw [hf'.2, hf.1, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart u.2.1 h]

private theorem fac_apart {F : Frame S} {w u : Spl E p} {L : Loc S.G.GAf (GLw n w.1)} {L' : Loc S.G.GAf (GLw n u.1)}
    (hf : IsFac F w L) (hf' : IsFac F u L') (h : GlobalTheory.Cong.Apart w.1 u.1) : L.Apart L' :=
  ⟨pr_loc_one hf hf' h, pr_loc_one hf' hf (Ne.symm h)⟩

private theorem exists_prime_mem (w : Plc E) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 E) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk68.exists_prime_mem w

private theorem val_lt_one {w : Plc E} {q : ℕ} (hq : (q : 𝓞 E) ∈ w.asIdeal) : Valued.v (q : w.adicCompletion E) < 1 := by
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (q : 𝓞 E)).2 hq
  have e : ((q : ℕ) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E (q : 𝓞 E)) := by
    rw [map_natCast, map_natCast]
  rw [e]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt h

private theorem mul_mem_of_dvd {w : Plc E} {a b : ℕ} (h : a ∣ b) {y : w.adicCompletion E}
    (hy : (a : w.adicCompletion E) * y ∈ w.adicCompletionIntegers E) : (b : w.adicCompletion E) * y ∈ w.adicCompletionIntegers E := by
  obtain ⟨d, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm (a : w.adicCompletion E), mul_assoc]
  exact mul_mem (natCast_mem _ d) hy

private theorem exists_pow {T : Type} [TopologicalSpace T] {w : Plc E} {q : ℕ} (hq : (q : 𝓞 E) ∈ w.asIdeal) {C : Set T}
    (hC : IsCompact C) {f : T → w.adicCompletion E} (hf : Continuous f) :
    ∃ m : ℕ, ∀ t ∈ C, ((q ^ m : ℕ) : w.adicCompletion E) * f t ∈ w.adicCompletionIntegers E := by
  have ho : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := Valued.isOpen_valuationSubring _
  obtain ⟨m, hm⟩ := hC.elim_directed_cover
    (fun m : ℕ => {t | ((q ^ m : ℕ) : w.adicCompletion E) * f t ∈ w.adicCompletionIntegers E})
    (fun m => ho.preimage (continuous_const.mul hf)) (fun t _ => by
      rw [Set.mem_iUnion]
      by_cases h0 : Valued.v (f t) = 0
      · refine ⟨0, ?_⟩
        show Valued.v (_ * f t) ≤ 1
        rw [map_mul, h0, mul_zero]
        exact zero_le_one
      · obtain ⟨m, hm⟩ := exists_pow_lt₀ (val_lt_one hq) (Units.mk0 _ h0)⁻¹
        refine ⟨m, ?_⟩
        show Valued.v (_ * f t) ≤ 1
        rw [map_mul, Nat.cast_pow, map_pow]
        rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
        calc _ ≤ (Valued.v (f t))⁻¹ * Valued.v (f t) := mul_le_mul' hm.le le_rfl
          _ = 1 := inv_mul_cancel₀ h0)
    (Monotone.directed_le fun a b hab t ht => mul_mem_of_dvd (pow_dvd_pow q hab) ht)
  exact ⟨m, fun t ht => hm ht⟩

private theorem bound_at (F : Frame S) {C : Set (GUf E n)} (hC : IsCompact C) (w : Plc E) :
    ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ ((p : 𝓞 E) ∉ w.asIdeal → ∀ t ∈ C, ∀ i k,
      (c : w.adicCompletion E) * F.cmp w (UpperTheory.Gal.CertificateRingHomMap.th t) i k ∈ w.adicCompletionIntegers E) := by
  by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
  · exact ⟨1, one_pos, Nat.coprime_one_left p, fun h => absurd hp h⟩
  obtain ⟨q, hq, hqw⟩ := exists_prime_mem w
  have hne : q ≠ p := fun e => hp (e ▸ hqw)
  have hc : Continuous fun t : GUf E n => F.cmp w (UpperTheory.Gal.CertificateRingHomMap.th t) := by
    simp only [Frame.cmp, UpperTheory.Gal.CertificateRingHomMap.comp_th]
    exact Units.continuous_val.comp
      ((continuous_const.mul ((GlobalTheory.SplitPts.continuous_invT _).comp (cont_comp w))).mul continuous_const)
  choose m hm using fun i k : Fin n => exists_pow hqw hC (hc.matrix_elem i k)
  refine ⟨q ^ ∑ i, ∑ k, m i k, pow_pos hq.pos _, ((Nat.coprime_primes hq Fact.out).2 hne).pow_left _, fun _ t ht i k => ?_⟩
  refine mul_mem_of_dvd (pow_dvd_pow q ?_) (hm i k t ht)
  exact (Finset.single_le_sum (f := fun k => m i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)).trans
    (Finset.single_le_sum (f := fun i => ∑ k, m i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

private theorem bound (F : Frame S) (V : Vec x U w₀ Up) :
    ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ ∀ g : GUf E n, F.th g ∈ lev V.S V.Kw → ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k,
      (c : w.adicCompletion E) * F.cmp w g i k ∈ w.adicCompletionIntegers E := by
  choose c h0 h1 h2 using fun w => bound_at F V.cpt w
  have hfin : {w | ¬ F.a w ∈ GlobalTheory.LFun.KGL w n}.Finite := Filter.eventually_cofinite.1 F.a_cof
  let B : Finset (Plc E) := hfin.toFinset ∪ V.S ∪ V.S.image cj
  refine ⟨∏ w ∈ B, c w, Finset.prod_pos fun w _ => h0 w, Nat.Coprime.prod_left fun w _ => h1 w, fun g hg w hw i k => ?_⟩
  rw [th_eq] at hg
  by_cases hB : w ∈ B
  · have := h2 w hw _ hg i k
    rw [UpperTheory.Gal.CertificateRingHomMap.th_th] at this
    exact mul_mem_of_dvd (Finset.dvd_prod_of_mem _ hB) this
  · simp only [B, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not, Finset.mem_image] at hB
    obtain ⟨⟨ha, hS⟩, hc⟩ := hB
    have hg' := (UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 (UpperTheory.Gal.CertificateRingHomMap.th_mem_lev.1 hg)).2.2 w hS
      fun h => hc ⟨_, h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm w⟩
    have hm := ((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w _).1 (mul_mem (mul_mem ha hg') (inv_mem ha))).1 i k
    exact mul_mem (natCast_mem _ _) hm

private theorem loc_mem {F : Frame S} {V : Vec x U w₀ Up} {W : Finset (Spl E p)} {N : ℕ}
    {L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)} {hw : IsSplitAt w₀ ∧ (p : 𝓞 E) ∉ w₀.asIdeal} {Ty : TyLev S.G.GAf (GLw n w₀)}
    (h : TyOK F V W N L hw Ty) (w : Spl E p) (h1 : w.1 ∉ V.S) (h2 : cj w.1 ∉ V.S) {y : GLw n w.1} (hy : y ∈ GlobalTheory.LFun.KGL w.1 n)
    (hI : ∀ u ∈ W, (L u).pr ((L w).loc y) ∈ Iw n u.1) : (L w).loc y ∈ Ty.K := by
  refine (h.K_iff _).2 ⟨⟨UpperTheory.Gal.CertificateRingHomMap.loc w.2.1 y, ((h.fac w).2 y).symm, ?_⟩, hI⟩
  rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.th_mem_lev]
  exact (UpperTheory.Gal.CertificateRingHomMap.pLocMem_of UpperTheory.Gal.CertificateRingHomMap.pIntConj_of UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n V.S _ w.1 w.2.1 h2 y).2 h1 hy

private theorem iw_le (w : Plc E) : Iw n w ≤ GlobalTheory.LFun.KGL w n := by
  intro y hy
  have := GlobalTheory.SmGL.iwahori_le_KO _ _ hy
  rwa [GlobalTheory.SmGL.SphCompletion.KO_completion] at this

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.tyFact :
    UpperTheory.Gal.Spc.TyFact := by
  intro E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ _ r W aux N _ _ L hw Ty h
  refine ⟨fun w hwW => ?_, fun w h1 h2 h3 => ⟨⟨fun y hy => ?_, fun g hg => ?_⟩, ?_⟩, ?_⟩
  · haveI : Fact r.Prime := ⟨aux.prime⟩
    have hoff : ∀ u ∈ V.S, GlobalTheory.Cong.Apart w.1 u := fun u hu =>
      apart_of_not_mem (p := r) (aux.off u hu) (aux.half.above w hwW)
    obtain ⟨-, hap, -⟩ := UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n w.1 w.2.1
    have h1 : w.1 ∉ V.S := fun e => hoff _ e rfl
    have h2 : cj w.1 ∉ V.S := fun e => ((hap _).1 (Ne.symm (hoff _ e))).2 rfl
    refine ⟨⟨fun y hy => loc_mem h w h1 h2 (iw_le _ hy) fun u hu => ?_, fun g hg => ((h.K_iff g).1 hg).2 w hwW⟩, ?_,
      fun w' hw' hne => fac_apart (h.fac w) (h.fac w') (aux.half.apart w hwW w' hw' hne)⟩
    · by_cases e : u = w
      · subst e
        rw [Loc.pr_loc]
        exact hy
      · rw [pr_loc_one (h.fac u) (h.fac w) (aux.half.apart u hu w hwW e)]
        exact one_mem _
    · rw [h.L_eq]
      exact fac_apart (h.fac ⟨w₀, hw⟩) (h.fac w) (Ne.symm (hoff _ V.shape.mem))
  · refine loc_mem h w h1 h2 hy fun u hu => ?_
    rw [pr_loc_one (h.fac u) (h.fac w) (Ne.symm (h3 u hu))]
    exact one_mem _
  · obtain ⟨⟨k, rfl, hk⟩, -⟩ := (h.K_iff g).1 hg
    rw [th_eq, UpperTheory.Gal.CertificateRingHomMap.th_mem_lev] at hk
    rw [(h.fac w).1]
    exact (UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 hk).2.2 w.1 h1 h2
  · obtain ⟨-, hap, -, -, hcc, -⟩ := UpperTheory.Gal.CertificateRingHomMap.pLocComm_of E n w₀ hw.1
    rw [h.L_eq]
    refine fac_apart (h.fac ⟨w₀, hw⟩) (h.fac w) (Ne.symm ((hap w.1).2 ⟨fun e => h1 ?_, fun e => h2 ?_⟩))
    · rw [e]
      exact V.shape.mem
    · rw [e, hcc]
      exact V.shape.mem
  · obtain ⟨c, h0, h1, h2⟩ := bound F V
    refine ⟨c, h0, h1, fun k hk => ?_⟩
    obtain ⟨⟨g, rfl, hg⟩, -⟩ := (h.K_iff k).1 hk
    exact (nsmul_integ_iff F g c).2 (h2 g hg)
