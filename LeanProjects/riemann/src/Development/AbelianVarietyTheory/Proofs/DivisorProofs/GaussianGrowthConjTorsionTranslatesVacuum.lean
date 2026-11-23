import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint

namespace GlobalTheory.ConjGrowth

section SlopeTestRemainingChoices

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ConjJet
open scoped BigOperators

theorem fnConj_sum (D : D7) {N N' n : ℕ} (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (c : Fin n → M)
    (F : Fin n → VC D N N' → ℂ) (hF : ∀ i, Differentiable ℂ (F i)) (hM : ∀ i, CoefIn D (F i) M)
    (hd : ∀ i, Differentiable ℂ (fnConj D M ρ (F i))) (h0 : ∀ i, fnConj D M ρ (F i) ≠ 0) :
    fnConj D M ρ (fun z => ∑ i, (c i : ℂ) * F i z) = fun z => ∑ i, ρ (c i) * fnConj D M ρ (F i) z := by
  funext z
  have ht : ∀ α, TaylorLogMetric.taylor D (fun z => ∑ i, (c i : ℂ) * F i z) α =
      ((∑ i, c i * ⟨_, hM i α⟩ : M) : ℂ) := by
    intro α
    rw [GlobalTheory.ConjSeries.taylor_eq_coeff, taylorDir_sum _ _ fun i _ =>
      GlobalTheory.ProdThetaConj.an0 ((hF i).const_mul (c i : ℂ)), map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← GlobalTheory.ConjSeries.taylor_eq_coeff, GlobalTheory.ProdThetaConj.taylor_const_mul (hF i)]
  have hcj : ∀ x : M, cj M ρ x = ρ x := fun x => by simp [cj, TaylorLogMetric.liftM]
  have hs : HasSum (fun α => ∑ i, ρ (c i) * (TaylorLogMetric.taylor D (fnConj D M ρ (F i)) α * mono D α z))
      (∑ i, ρ (c i) * fnConj D M ρ (F i) z) :=
    hasSum_sum fun i _ => (GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' _ (hd i) z).mul_left _
  rw [← hs.tsum_eq]
  refine tsum_congr fun α => ?_
  change cj M ρ _ * _ = _
  rw [ht, hcj, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(GlobalTheory.ConjSeries.taylor_fnConj D N N' M ρ (F i) (hd i) (h0 i)).1 α, map_mul, mul_assoc, ← hcj ⟨_, hM i α⟩]

theorem vBar_vBar (D : D7) {N N' : ℕ} (z : VC D N N') : vBar D (vBar D z) = z := by
  funext τ i j
  simp [vBar]

theorem cBar_cBar (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : cBar D (cBar D G) = G := by
  funext z
  simp [cBar, vBar_vBar]

def Facts (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E))
    (G : VC D a d → ℂ) (ρ : Qbar →ₐ[ℚ] ℂ) : Prop :=
  0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧ fnConj D Qbar ρ G ≠ 0 ∧
    (∀ y, LaQ D (tor0 D cc δ) L L' y → ∃ y', fnConj D Qbar ρ (U D (tor0 D cc δ) y G) =
      U D (torConj D (tor0 D cc δ) Qbar ρ) y' (fnConj D Qbar ρ G)) ∧
    ∀ x z, ‖U D (torConj D (tor0 D cc δ) Qbar ρ) x (fnConj D Qbar ρ G) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
        normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
          (fnConj D Qbar ρ G) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ)))

theorem facts_fix (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) :
    Facts D cc δ L L' G ρ := by
  have hGT := vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (hI.t0Ex cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := hI.curve cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hI.perm Qbar ρ hρ hdata.1
  refine ⟨by rw [hΛ]; exact area_pos D hI.g1 cc' δ' hc', ?_, fun y hy => ?_, fun x z => ?_⟩
  · intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hI.g1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  · obtain ⟨m, hm, hmy⟩ := id hy
    obtain ⟨y', hy', -⟩ := hI.galEx cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
      (by omega)
    have hgal := (hI.gal cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
      hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
      (by rw [comb_one]; exact hAU y hy)).1
    rw [comb_one] at hgal
    exact ⟨y', hgal⟩
  · have := sup_perm D hI.g1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh x z
    rw [Hf_re, ← mul_div_assoc] at this
    exact this

theorem facts_all (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (ρ : Qbar →ₐ[ℚ] ℂ) :
    Facts D cc δ L L' G ρ := by
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, -⟩ := hI.alg cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hfix | hfix, htor, hbar⟩ := hI.bar cc δ hc Qbar ρ hdata
  · exact facts_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG ρ hfix
  obtain ⟨k1, k2, k3, k4⟩ := facts_fix D hI cc δ t0 hc ht a d L L' h1 h2 hev G hG _ hfix
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
  rw [U_zero] at hn2
  have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
      (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
    congrArg Tor.abelian₂ htor
  rw [hL, area_conj] at k1 k4
  rw [(hbar a d L L' G).1] at k2 k3 k4
  rw [htor] at k3 k4
  rw [hn2] at k4
  have hU := (hbar a d L L' (fnConj D Qbar ρ G)).2.1
  refine ⟨k1, fun h => k2 ?_, fun y hy => ?_, fun x z => ?_⟩
  · rw [h]
    funext z
    simp [cBar]
  · obtain ⟨y', hy'⟩ := k3 y hy
    refine ⟨vBar D y', ?_⟩
    rw [(hbar a d L L' _).1, ← vBar_vBar D y', ← hU] at hy'
    have := congrArg (cBar D) hy'
    rwa [cBar_cBar, cBar_cBar] at this
  · have := k4 (vBar D x) (vBar D z)
    rw [← hU] at this
    simpa only [cBar, vBar_vBar, vBar, RCLike.norm_conj, Complex.conj_conj] using this

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem conj_growth : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
  ∀ (a b : ℕ) (e0 : VC D a b → ℂ), Even (a * b) → oddE0 D cc δ t0 a b e0 →
  ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
  ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), 0 < k →
  (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) →
  ∀ (ρ : Qbar →ₐ[ℚ] ℂ) (t' : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t' →
    0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧
    CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) Qbar ∧
    Differentiable ℂ (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) ∧
    ∀ z, ‖fnConj D Qbar ρ (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) *
        nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t') ^ (fF D * a * b) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  intro D hI cc δ t0 hc ht a b e0 hev he Ls Lt h1 h2 κ hκ k n r s hk hs hr ρ t' ht'
  have hsd : ∀ N, SD D (stdL D N) := fun N => by
    obtain ⟨Lt, h, h1, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    exact h1 ▸ (h 1).2
  have hG := GlobalTheory.VacuumMove.isVacuum_thetaIntertwiner_selfDual D hI cc δ t0 hc ht a b _ _ Ls Lt (hsd a) (hsd b) h1 h2 e0 he.2.2.2.1
  change ThetaVectorUpToUnits D (tor0 D cc δ) t0 Ls Lt
    (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) at hG
  generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0 = G at hG ⊢
  have hGT := GlobalTheory.ConjJet.vacuum_mem_thetaSpace_pair D hI cc δ t0 hc ht a b Ls Lt h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 cc δ hc
  obtain ⟨hA, hAU, hAC, -⟩ := hI.alg cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := hI.conj cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨hN, -⟩ := hI.nrm cc δ hc t0 ht a b Ls Lt h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨k1, k2, k3, k4⟩ := facts_all D hI cc δ t0 hc ht a b Ls Lt h1 h2 hev G hG ρ
  rw [hN] at k4
  obtain ⟨hκ1, hκ2⟩ := hκ
  have hq : ∀ i, LaQ D (tor0 D cc δ) Ls Lt (s i) := fun i => ⟨k, hk, hs i⟩
  choose y hy using fun i => k3 (s i) (hq i)
  have he' : (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i) G z) =
      fun z => ∑ i, ((⟨κ, hκ1⟩ * r i : Qbar) : ℂ) * U D (tor0 D cc δ) (s i) G z := by
    funext z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    rfl
  have hd : ∀ i, Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G)) := fun i => by
    rw [hy]; exact GlobalTheory.ConjJet.U_diff D _ _ _ hTh.1
  rw [he', fnConj_sum D Qbar ρ _ _ (fun i => GlobalTheory.ConjJet.U_diff D _ _ _ hGT.1) (fun i => hAU _ (hq i)) hd
    (fun i => by rw [hy]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ k2)]
  refine ⟨k1, hAC n _ s (fun i => (⟨κ, hκ1⟩ * r i : Qbar).2) hq,
    Differentiable.fun_sum fun i _ => (hd i).const_mul _, fun z => ?_⟩
  have hb := fun i => k4 (y i) z
  have h0 := (sq_nonneg _).trans (k4 0 z)
  generalize (3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) * _ * _ : ℝ) = B at hb h0 ⊢
  have hb' : ∀ i, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G) z‖ ≤ √B := fun i => by
    rw [hy]; exact Real.le_sqrt_of_sq_le (hb i)
  rw [← Real.le_sqrt (norm_nonneg _) h0]
  calc _ ≤ ∑ i, ‖ρ (r i)‖ * √B := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        have h3 : ‖ρ ⟨κ, hκ1⟩‖ = 1 := hκ2 ρ.toRingHom
        rw [norm_mul, map_mul, norm_mul, h3, one_mul]
        exact mul_le_mul_of_nonneg_left (hb' i) (norm_nonneg _)
    _ ≤ 1 * √B := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hr ρ.toRingHom) (Real.sqrt_nonneg _)
    _ = √B := one_mul _

end GlobalTheory.ConjGrowth
