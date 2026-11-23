import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CondNu
variable {D : D7}
open GlobalTheory.Mem.Col2.SplitChar in

theorem vl_le_of_mem_hatId {I : Ideal (𝓞 D.host.E)} {PP : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (hI : I ≤ PP.asIdeal ^ n) {x : AE D} (hx : x ∈ hatId D I) : vl D PP x ≤ WithZero.exp (-(n : ℤ)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    rw [map_mul, vl_inc]
    refine (mul_le_of_le_one_right' (vl_le hs PP)).trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem PP b n).2 (hI hb)
  | zero => simp
  | add a b _ _ ha hb => exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  | neg a _ ha => rwa [Valuation.map_neg]

theorem sgA_mem_hatId {I : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D I) : sgA D x ∈ hatId D (D.host.conj • I) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s,
      GlobalTheory.NormSum.UnramHecke.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.sgA_inc]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem conj_mul_conj (D : D7) : D.host.conj * D.host.conj = 1 :=
  AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z

theorem conj_smul_le (𝔪 : Ideal (𝓞 D.host.E)) : D.host.conj • (𝔪 * D.host.conj • 𝔪) ≤ 𝔪 := by
  have e : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by rw [smul_smul, conj_mul_conj, one_smul]
  calc D.host.conj • (𝔪 * D.host.conj • 𝔪) ≤ D.host.conj • D.host.conj • 𝔪 :=
        Ideal.map_mono (Ideal.mul_le_inf.trans inf_le_right)
    _ = 𝔪 := e

open GlobalTheory.Mem.Col2.SplitChar in

theorem vl_sub_le {T : Type} {L : LevCh D T} (P : Places L) {u : (AE D)ˣ}
    (hu : (u : AE D) - 1 ∈ hatId D (condE P * D.host.conj • condE P)) {PP : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : PP.under (𝓞 D.host.F) ∈ P.S0) :
    vl D PP ((u : AE D) - 1) ≤ WithZero.exp (-(condExp P (PP.under (𝓞 D.host.F)) : ℤ)) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  set v := PP.under (𝓞 D.host.F) with hvdef
  have hw : (P.w v).under (𝓞 D.host.F) = v := P.under_w hv
  have hle : condE P ≤ (P.w v).asIdeal ^ condExp P v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (P.w v) PP).1 (by rw [hw]) with e | h
  · rw [e]
    exact vl_le_of_mem_hatId ((Ideal.mul_le_inf.trans inf_le_left).trans (e ▸ hle)) hu
  · have e : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
    rw [e] at h
    rw [← GlobalTheory.NormSum.UnramHecke.sgA_sgA D ((u : AE D) - 1), vl_sgA h]
    exact vl_le_of_mem_hatId ((conj_smul_le _).trans hle) (sgA_mem_hatId hu)

open GlobalTheory.Mem.Col2.SplitChar Formalism.L2.Host in

theorem nuH_inv_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (u : (AE D)ˣ), IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → (nuH G μ₀ i j)⁻¹.1 (finIdl D u) = 1 := by
  intro D T L sc μ₀ hL G i j u hu hc
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j)⁻¹.2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  have hsub : Valued.v ((x : PP.adicCompletion D.host.E) - 1) = vl D PP ((u : AE D) - 1) := by
    rw [hx, vl_sub_one]
  have hμ : (L.C.mu0 j).loc PP x = 1 := by
    by_cases hg : ∃ k, OverP D.host (D.host.g k) PP
    · obtain ⟨k, hk⟩ := hg
      have hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0 := by
        refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
        have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
          change _ ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl this
        · exact Or.inr (Or.inl this)
      refine (L.C.isMu0 j).tame PP x hunit ?_
      rw [hsub]
      refine (vl_sub_le G.pl hc hS).trans ?_
      have : 1 ≤ condExp G.pl (PP.under (𝓞 D.host.F)) := by unfold condExp; split_ifs <;> omega
      exact WithZero.exp_le_exp.2 (by omega)
    · push_neg at hg
      exact (L.C.isMu0 j).unr PP hg x hunit
  have hχ : (G.ch.chiH (D.R.m - i)).loc PP x = 1 := by
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
    by_cases hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0
    · have hb := vl_sub_le G.pl hc hS
      rw [← hsub] at hb
      rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1'
      · rw [condExp, if_pos h0] at hb
        exact (G.ch.lev0 _ h1 h2 PP h0).1 x hunit (by simpa using hb)
      · have hne : PP.under (𝓞 D.host.F) ≠ G.pl.v0 := fun e => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ h1')
        rw [condExp, if_neg hne] at hb
        exact (G.ch.lev1 _ h1 h2 PP h1').1 x hunit (by simpa using hb)
    · exact G.ch.unr _ h1 h2 PP hS x hunit
  show ((nuH G μ₀ i j).loc PP x)⁻¹ = 1
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv, HChar.loc_mul, HChar.loc_inv, hμ, hχ]
  simp
end GlobalTheory.BotPairSmall.CondNu

end
