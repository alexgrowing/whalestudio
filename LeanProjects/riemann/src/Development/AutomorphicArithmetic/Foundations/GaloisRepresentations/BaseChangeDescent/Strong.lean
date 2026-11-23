import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigidAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.BcBackOffTOfSat
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnramifiedAtOfIsSplitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.LFun GlobalTheory.PRep Formalism.UG
open GlobalTheory.GalOfCusp PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange UpperTheory.V.Z.Tf

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Desc

def WeakAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU σ w) ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, IsSplitAt w → ∃ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B

theorem weakAll_of (hR : SR.SplitRigid) (hN : GlobalTraceComparison.PartNorm) (hU : GOne.UnitOf) (hRun : GlobalTraceComparison.RunTh) : WeakAll := by
  intro E _ _ _ hE n hn π hreg hd hsat
  rcases hRun E hE n hn π hreg hd hsat with h | ⟨D, h1, h2, -, h4⟩
  · exact h
  refine absurd (hR E hE n hn (CG.mk π) (hU E n hn π hd) (Fin D.c) D.N D.P D.pos (fun i => ?_) (h4.mono fun w hw hs => ?_)) h1
  · obtain ⟨P, e, -, hu⟩ := hN E n hn π hd D h2 h4 i
    rw [← e]
    exact (CG.isUnitary_mk P).2 hu
  · obtain ⟨B, ⟨b, hb, rfl⟩, hB⟩ := hw hs
    exact ⟨b, hb, hB⟩

theorem len_one {q d : ℕ} (hq : 1 < q) (hd : 1 ≤ d) (z : ℂ)
    (h : ∀ k : Fin d, (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖z * (q : ℂ) ^ (((d : ℂ) - 1) / 2 - (k : ℕ))‖ ∧
      ‖z * (q : ℂ) ^ (((d : ℂ) - 1) / 2 - (k : ℕ))‖ < (q : ℝ) ^ (1 / 2 : ℝ)) : d = 1 := by
  by_contra hne
  have hq0 : 0 < q := by omega
  have hq1 : (0 : ℝ) < q := by exact_mod_cast hq0
  have h0 := (h ⟨0, by omega⟩).2
  have h1 := (h ⟨1, by omega⟩).1
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq0] at h0 h1
  have e0 : (((d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)).re = ((d : ℝ) - 1) / 2 := by simp
  have e1 : (((d : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)).re = ((d : ℝ) - 1) / 2 - 1 := by simp
  simp only at h0 h1
  rw [e0] at h0
  rw [e1, Real.rpow_sub hq1, Real.rpow_one, ← mul_div_assoc, lt_div_iff₀ hq1] at h1
  have e2 : (q : ℝ) ^ (-(1 / 2) : ℝ) * q = (q : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hq1.ne']
    norm_num
  linarith

theorem match_of (hB : BcSpeh) (h1 : CompUnique) (h3 : OneFactor) (hJ : GlobalTheory.Published.JacquetShalikaBound)
    (hM : GlobalTheory.Published.CuspidalMultiplicityOne) (hR : SR.SplitRigid) (hT : GOne.Thin)
    {E : Type} [Field E] [NumberField E] [IsCMField E] (hE : GlobalTheory.BCT.Unr E) {n : ℕ} (hn : 1 ≤ n) (π : CuspSub E n)
    (hu : (CG.mk π).IsUnitary) (U : Submodule ℂ (UA E n → ℂ)) (hU : IsAutRepU U)
    (hun : ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU U w)
    (hae : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, IsSplitAt w →
      ∃ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B) :
    GlobalTheory.Cong.Match U π := by
  obtain ⟨c, a, d, h, P, ρ, m, σ, hP, hsp, hsplit⟩ := hB E hE n hn U hU
  have key : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, IsSplitAt w → ∃ (B : Multiset ℂˣ) (S : Fin c → Multiset ℂˣ),
      (CG.mk π).HasSat w B ∧ (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧
      ∑ i, ∑ k : Fin (d i), (S i).map (fun z : ℂˣ => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
        B.map (fun z : ℂˣ => (z : ℂ)) := hae.mono fun w hw hs => by
    obtain ⟨τ, B, t1, t2, t3⟩ := hw hs
    obtain ⟨e⟩ := h1 E n U hU w hs τ
      { V := _, ρ := locProd h w (σ · w), smooth := isSmooth_parInd _ _, irred := (hsplit w hs).1 } t1 (hsplit w hs)
    obtain ⟨S, s1, s2⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hP.pos i).2)
      (fun i => (hsp i w).2.2) B (GlobalTheory.BaseChangeBridge.hasSatGL_of_equiv e.toLinearEquiv
        (fun g x => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x) t2)
    exact ⟨B, S, t3, fun i => (GlobalTheory.BcSpehCompare.hasSat_iff (hP.loc i w) _).2 (s1 i), by
      simpa only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def] using s2⟩
  have hd : ∀ i, d i = 1 := fun i => by
    obtain ⟨w, hs, hw⟩ := (hT E).2.exists_notMem_finite (eventually_cofinite.1 key)
    obtain ⟨B, S, b1, b2, b3⟩ := not_not.1 hw hs
    obtain ⟨z, hz⟩ : ∃ z, z ∈ S i := Multiset.card_pos_iff_exists_mem.mp (by rw [(b2 i).card]; exact (hP.pos i).1)
    have hq : 1 < Ideal.absNorm w.asIdeal := by
      have a0 : Ideal.absNorm w.asIdeal ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
      have a1 : Ideal.absNorm w.asIdeal ≠ 1 := fun e => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 e)
      omega
    refine len_one hq (hP.pos i).2 (z : ℂ) fun k => ?_
    have hm : (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ)) ∈ B.map (fun z : ℂˣ => (z : ℂ)) := by
      rw [← b3]
      exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Multiset.mem_sum.2 ⟨k, Finset.mem_univ _, Multiset.mem_map_of_mem _ hz⟩⟩
    obtain ⟨α, hα, e⟩ := Multiset.mem_map.1 hm
    rw [← e]
    exact hJ E n _ hu w B b1 α hα
  obtain rfl : d = fun _ => 1 := funext hd
  obtain ⟨j, hj⟩ := hR E hE n hn (CG.mk π) hu (Fin c) a (fun i => CG.mk (P i)) (fun i => (hP.pos i).1)
    (fun i => GlobalTheory.CuspRep.CsdUnitary.isUnitary_of_isCsd E _ (CG.mk (P i)) (hP.csd i)) (key.mono fun w hw hs => by
      obtain ⟨B, S, b1, b2, b3⟩ := hw hs
      refine ⟨S, b2, ?_⟩
      have e : ∑ i, S i = B := by
        apply Multiset.map_injective (f := fun z : ℂˣ => (z : ℂ)) Units.val_injective
        rw [← b3]
        exact (map_sum (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ)) S Finset.univ).trans (by simp)
      rwa [e])
  have haj : a j = n := congrArg Sigma.fst hj
  have hone : ∀ i, i = j := fun i => by
    by_contra hij
    have h2 : 1 * a i + 1 * a j ≤ ∑ k, 1 * a k := by
      rw [← Finset.sum_pair (f := fun k => 1 * a k) hij]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := (hP.pos i).1
    have h' : ∑ k, 1 * a k = n := h
    omega
  obtain rfl : c = 1 := by
    have := Fintype.card_eq_one_iff.2 ⟨j, hone⟩
    simpa using this
  obtain rfl : j = 0 := Subsingleton.elim _ _
  obtain rfl : a = fun _ => n := funext fun i => by rw [hone i, haj]
  have hπ : P 0 = π := CuspSub.ext (hM E n _ _ (eq_of_heq (Sigma.mk.inj hj).2))
  subst hπ
  refine ⟨hU, hun, fun w hw σ' hσ' => ?_, fun τ' lam hl => ?_⟩
  · obtain ⟨e₁⟩ := h3 E w n h (ρ 0 w) (σ · w) (hsp 0 w).2.2
    obtain ⟨e₂⟩ := LocUniq.isLocComp_unique (P 0) w _ _ (hP.loc 0 w) hσ'
    exact GlobalTheory.BaseChangeBridge.isCompAlong_of_equiv (e₁.trans e₂).toLinearEquiv
      (fun g x => LinearMap.congr_fun ((e₁.trans e₂).toIntertwiningMap.isIntertwining' g) x) σ'.irred (hsplit w hw)
  · have hw := hP.weight τ' lam hl
    rw [Fin.sum_univ_one] at hw
    rw [← hw, show spehInf 1 (m 0 τ') = m 0 τ' by simp [spehInf]]
    exact CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hP.inf 0 τ')

theorem desc_of (hB : BcSpeh) (h1 : CompUnique) (h3 : OneFactor) (hJ : GlobalTheory.Published.JacquetShalikaBound)
    (hM : GlobalTheory.Published.CuspidalMultiplicityOne) (hR : SR.SplitRigid) (hT : GOne.Thin) (hU : GOne.UnitOf) (hW : WeakAll) :
    GlobalTheory.Cong.Desc := by
  intro E _ _ _ l a _ ha π ⟨hreg, hpol, hg, _⟩
  have hE : GlobalTheory.BCT.Unr E := fun w => by
    by_cases hs : IsSplitAt w
    · exact GlobalTheory.SplitUnram.isUnramifiedAt_of_isSplitAt E w hs
    · exact (hg.2.2 w hs).2.1
  have hd : GlobalTheory.ContraPair.DualIsConj π := by
    have := hpol.dual
    rwa [map_pow, compNorm_quadChar, one_pow, GlobalTheory.ContraPair.dualIsConjBy_one] at this
  obtain ⟨U, u1, u2, u3⟩ := hW E hE a ha π hreg hd fun w hw => (hg.2.2 w hw).2.2
  exact ⟨U, match_of hB h1 h3 hJ hM hR hT hE ha π (hU E a ha π hd) U u1 u2 u3⟩

end UpperTheory.Gal.Desc
