import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmOneNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstJetOperatorNormCauchyBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatWDualWtOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumns
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaJetMapWeightedTableScale
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BlockShape

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

namespace GlobalTheory.KerConjRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Jets

open Formalism.L2.Ker

theorem jetOp_transport {K M : Type} [Field K] [Field M] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (n : ι → ℕ) (hJ : JetInVV ℂ lam lam' n) (i : K →+* M) (e ψ : M →+* ℂ) (J : (DVar ι a b →₀ ℕ) → M)
    (u : VV K lam) (w : VV K lam')
    (h : jetOp lam lam' (fun m => e (J m)) n (GlobalTheory.CoefModel.mapVV (e.comp i) lam u) = GlobalTheory.CoefModel.mapVV (e.comp i) lam' w) :
    GlobalTheory.CoefModel.mapVV (ψ.comp i) lam' w = jetOp lam lam' (fun m => ψ (J m)) n (GlobalTheory.CoefModel.mapVV (ψ.comp i) lam u) := by
  have key : ∀ φ : M →+* ℂ, ((jetOp lam lam' (fun m => φ (J m)) n (GlobalTheory.CoefModel.mapVV (φ.comp i) lam u) : VV ℂ lam') :
      Pol ℂ ι b) = MvPolynomial.map φ (jetMap J n (MvPolynomial.map i u.1)) := fun φ => by
    rw [GlobalTheory.JetPoint.coe_jetOp _ _ _ _ _ (hJ _ _ (GlobalTheory.CoefModel.mapVV (φ.comp i) lam u).2), Shape.map_jetMap,
      GlobalTheory.CoefModel.mapVV_coe, MvPolynomial.map_map]
    rfl
  have h1 := congrArg Subtype.val h
  rw [key, GlobalTheory.CoefModel.mapVV_coe, ← MvPolynomial.map_map] at h1
  have h2 := MvPolynomial.map_injective e e.injective h1
  apply Subtype.ext
  rw [key, GlobalTheory.CoefModel.mapVV_coe, ← MvPolynomial.map_map, h2]

theorem applyAt0_monomial (D : D7) {N N' : ℕ} (m : GL3Theta.Idx D N N' →₀ ℕ) (H : VC D N N' → ℂ) :
    GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D H m := by
  classical
  rw [GL3Theta.applyAt0, MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl, one_mul]

def trL (D : D7) (a b : ℕ) : VC D a b →ₗ[ℂ] VC D b a where
  toFun z := fun τ i j => z τ j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def trI (D : D7) (a b : ℕ) : D.what₂.Tau × Fin b × Fin a ↪ D.what₂.Tau × Fin a × Fin b :=
  ⟨fun k => (k.1, k.2.2, k.2.1), by
    rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
    simp only [Prod.mk.injEq] at h
    simp [h]⟩

theorem applyAt0_tr (D : D7) {a b : ℕ} {H : VC D b a → ℂ} (hH : Differentiable ℂ H) (m : GL3Theta.Idx D a b →₀ ℕ) :
    GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => H (trL D a b z)) =
      GL3Theta.applyAt0 D (MvPolynomial.monomial (m.mapDomain fun k => (k.1, k.2.2, k.2.1)) 1) H := by
  have han : AnalyticAt ℂ H 0 := GlobalTheory.ProdThetaConj.an0 hH
  have e : (m.mapDomain fun k => (k.1, k.2.2, k.2.1)) = Finsupp.embDomain (trI D a b) m := by
    rw [Finsupp.embDomain_eq_mapDomain]; rfl
  rw [applyAt0_monomial, applyAt0_monomial, e, Finsupp.prod_embDomain, GlobalTheory.ConjSeries.taylor_eq_coeff,
    GlobalTheory.ConjSeries.taylor_eq_coeff, ← GlobalTheory.ConjRestrict.coeff_taylorDir_embDomain _ _ han]
  have h := taylorDir_comp_clm (LinearMap.toContinuousLinearMap (trL D a b)) (coordV D) han
  have hc : ∀ k, trL D a b (coordV D k) = coordV D (trI D a b k) := fun k => by
    funext τ i j
    simp only [trL, trI, coordV, LinearMap.coe_mk, AddHom.coe_mk, Function.Embedding.coeFn_mk]
    congr 1
    exact propext (by tauto)
  simp only [LinearMap.coe_toContinuousLinearMap', hc] at h
  rw [h]

end Jets

theorem taylor_fnConj_comb (D : D7) (hI : GlobalTheory.NormSum.Inp D) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (hc : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a b : ℕ) (e0 : VC D a b → ℂ) (hev : Even (a * b)) (he : oddE0 D cc δ t0 a b e0)
    (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h1 : SD D Ls)
    (h2 : SD D Lt) (κ : ℂ) (hκ1 : κ ∈ Qbar) (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b) (hk : 0 < k)
    (hs : ∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) (ρ : Qbar →ₐ[ℚ] ℂ) (α : Mono D a b) :
    TaylorLogMetric.taylor D (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) α =
    StandardLatticesGL3.cj Qbar ρ (TaylorLogMetric.taylor D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) α) := by
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
  obtain ⟨-, k2, k3, -⟩ := GlobalTheory.ConjGrowth.facts_all D hI cc δ t0 hc ht a b Ls Lt h1 h2 hev G hG ρ
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
  have h0 : ∀ i, fnConj D Qbar ρ (U D (tor0 D cc δ) (s i) G) ≠ 0 := fun i => by
    rw [hy]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ k2
  have hF : ∀ i, Differentiable ℂ (U D (tor0 D cc δ) (s i) G) := fun i => GlobalTheory.ConjJet.U_diff D _ _ _ hGT.1
  have hsum : ∀ (c : Fin n → ℂ) (F : Fin n → VC D a b → ℂ), (∀ i, Differentiable ℂ (F i)) →
      TaylorLogMetric.taylor D (fun z => ∑ i, c i * F i z) α = ∑ i, c i * TaylorLogMetric.taylor D (F i) α := fun c F hF => by
    rw [GlobalTheory.ConjSeries.taylor_eq_coeff, taylorDir_sum _ _ fun i _ =>
      GlobalTheory.ProdThetaConj.an0 ((hF i).const_mul (c i : ℂ)), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← GlobalTheory.ConjSeries.taylor_eq_coeff, GlobalTheory.ProdThetaConj.taylor_const_mul (hF i)]
  have hcj : ∀ x : Qbar, StandardLatticesGL3.cj Qbar ρ x = ρ x := fun x => by simp [StandardLatticesGL3.cj, TaylorLogMetric.liftM]
  rw [he', GlobalTheory.ConjGrowth.fnConj_sum D Qbar ρ _ _ hF (fun i => hAU _ (hq i)) hd h0, hsum _ _ hd, hsum _ _ hF]
  have e : (∑ i, ((⟨κ, hκ1⟩ * r i : Qbar) : ℂ) * TaylorLogMetric.taylor D (U D (tor0 D cc δ) (s i) G) α) =
      ((∑ i, (⟨κ, hκ1⟩ * r i) * ⟨_, hAU _ (hq i) α⟩ : Qbar) : ℂ) := by
    push_cast; rfl
  rw [e, hcj, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(GlobalTheory.ConjSeries.taylor_fnConj D a b Qbar ρ _ (hd i) (h0 i)).1 α, map_mul ρ _ ⟨_, hAU _ (hq i) α⟩,
    ← hcj ⟨_, hAU _ (hq i) α⟩]

open GlobalTheory.SignedHC in

theorem abs_entry_le {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i : ℕ) (τ : D.what₂.Tau) :
    ∀ x ∈ entries (parV D 1 i D.R.m τ), |(x : ℝ)| ≤ 14 * large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, hbe, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hsg : sLen D < gap D 1 := sLen_lt_gap D 1
  have hg1 : (1 : ℝ) ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ gap D 1)
  have hsg' : (sLen D : ℝ) + 1 ≤ (gap D 1 : ℝ) := by exact_mod_cast hsg
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hgb : (gap D 1 : ℝ) ≤ large₂.sc.b := by nlinarith
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hScb : large₂.Sc ≤ large₂.sc.b := by nlinarith

  have hv : ∀ j, 0 ≤ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ∧ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ≤ large₂.Sc :=
    GlobalTheory.GridWtBound.extend_bounds 2 _ _ hSc.le fun l => large₂.cloud_v τ l
  have hbl : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).b l : ℚ) : ℝ) ∧ (((D.hc τ).b l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : (D.hc τ).b l ≤ (D.hc τ).e l := by linarith
    have h5 : (((D.hc τ).b l : ℚ) : ℝ) ≤ (((D.hc τ).e l : ℚ) : ℝ) := by exact_mod_cast h4
    exact ⟨by exact_mod_cast h1.le, h5.trans h2⟩
  have hel : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : 0 ≤ (D.hc τ).e l := by linarith
    exact ⟨by exact_mod_cast h4, h2⟩
  have hb := GlobalTheory.GridWtBound.extend_bounds 1 _ _ (by linarith) hbl
  have he := GlobalTheory.GridWtBound.extend_bounds 1 _ _ (by linarith) hel
  have htb : (D.R.t : ℝ) ≤ 8 * large₂.sc.b := by
    obtain ⟨h1, h2⟩ := hbe τ ⟨0, by have := D.R.two_le_m; omega⟩
    have h3 := (D.hc τ).gap_be ⟨0, by have := D.R.two_le_m; omega⟩
    have h3' := (Rat.cast_le (K := ℝ)).2 h3
    push_cast at h3'
    have h1' : (0 : ℝ) < (((D.hc τ).b ⟨0, by have := D.R.two_le_m; omega⟩ : ℚ) : ℝ) := by exact_mod_cast h1
    linarith

  have hcen : ∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ ((cen D 1 τ j : ℤ) : ℝ) ∧ ((cen D 1 τ j : ℤ) : ℝ) ≤ large₂.sc.b := by
    intro j hj1 hj2
    have e := GridData.mid_eq (GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0) hj1
    have hv2 := hv 2
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hj2' : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hj2
    have hmid : 0 ≤ (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ∧
        (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ≤ large₂.sc.b := by
      rw [e]
      simp only [GridData.a, GridData.ofHCParam]
      push_cast
      constructor <;> nlinarith
    unfold cen
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 (by exact_mod_cast hmid.1), le_trans ?_ hmid.2⟩
    exact_mod_cast Int.floor_le _
  intro x hx
  obtain ⟨sg, hsg⟩ := mem_entries.1 hx
  simp only [parV, shift, Finset.mem_image] at hsg
  obtain ⟨⟨y, sy⟩, hy, hxy⟩ := hsg
  have hx' := (congrArg Prod.fst hxy).symm
  simp only at hx'
  simp only [GridData.parD, Finset.mem_union, plus, Finset.mem_image, Finset.mem_biUnion, GridData.cloud,
    GridData.blockM, GridData.blockC, mem_block, Finset.mem_Icc, Prod.mk.injEq] at hy
  have hyb : |(y : ℝ)| ≤ 13 * large₂.sc.b := by
    rcases hy with ((⟨a0, ⟨j, -, hj⟩, hay, -⟩ | ⟨j, -, hj, -⟩) | ⟨a0, ⟨j, -, a, ha, hae⟩, hay, -⟩) |
      ⟨a0, ⟨j, ⟨hj1, hj2⟩, a, ha, hae⟩, hay, -⟩
    · have h : 0 ≤ (((num D 1 τ).v j : ℤ) : ℝ) ∧ (((num D 1 τ).v j : ℤ) : ℝ) ≤ large₂.Sc := hv j
      rw [← hay, ← hj]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have h : 0 ≤ (((num D 1 τ).b j : ℤ) : ℝ) ∧ (((num D 1 τ).b j : ℤ) : ℝ) ≤ 4 * large₂.sc.b := hb j
      rw [← hj]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have h : 0 ≤ (((num D 1 τ).e j : ℤ) : ℝ) ∧ (((num D 1 τ).e j : ℤ) : ℝ) ≤ 4 * large₂.sc.b := he j
      have ht : ((num D 1 τ).t : ℝ) ≤ 8 * large₂.sc.b := htb
      have ha' : (a : ℝ) + 1 ≤ ((num D 1 τ).t : ℝ) := by exact_mod_cast ha
      have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
      rw [← hay, hae]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have hj1' : 1 ≤ j := by
        have : (num D 1 τ).m = D.R.m := rfl
        omega
      have h : 0 ≤ (((num D 1 τ).cen j : ℤ) : ℝ) ∧ (((num D 1 τ).cen j : ℤ) : ℝ) ≤ large₂.sc.b := hcen j hj1' hj2
      have hs : ((num D 1 τ).s : ℝ) + 1 ≤ (gap D 1 : ℝ) := hsg'
      have ha' : (a : ℝ) + 1 ≤ ((num D 1 τ).s : ℝ) := by exact_mod_cast ha
      have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
      rw [← hay, hae]; push_cast
      rw [abs_le]; constructor <;> linarith
  have hsh : |(((if Odd (i + D.R.m) then -(1 / 2) else 0 : ℚ)) : ℝ)| ≤ 1 / 2 := by
    split_ifs <;> norm_num
  rw [hx']
  push_cast
  calc |(y : ℝ) + (((if Odd (i + D.R.m) then -(1 / 2) else 0 : ℚ)) : ℝ)|
      ≤ |(y : ℝ)| + |(((if Odd (i + D.R.m) then -(1 / 2) else 0 : ℚ)) : ℝ)| := abs_add_le _ _
    _ ≤ 14 * large₂.sc.b := by linarith

theorem pow_le_exp_posLog (x : ℝ) (g : ℕ) : x ^ g ≤ Real.exp (g * Real.posLog x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases g with _ | g
    · simp
    · rw [zero_pow (Nat.succ_ne_zero g)]; exact (Real.exp_pos _).le
  · calc x ^ g ≤ |x ^ g| := le_abs_self _
      _ = |x| ^ g := abs_pow x g
      _ = Real.exp (g * Real.log |x|) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos (abs_pos.2 hx) g)]
      _ ≤ Real.exp (g * Real.posLog x) := by
          gcongr
          rw [Real.log_abs]; unfold Real.posLog; exact le_max_right _ _

theorem max_pow_le_exp_posLog (A : ℝ) (hA : 0 < A) (d : ℕ) :
    max 1 A⁻¹ ^ d ≤ Real.exp (d * Real.posLog A⁻¹) := by
  have h1 : max 1 A⁻¹ ≤ Real.exp (Real.posLog A⁻¹) := by
    refine max_le ?_ ?_
    · exact Real.one_le_exp (by unfold Real.posLog; exact le_max_left _ _)
    · calc A⁻¹ = Real.exp (Real.log A⁻¹) := (Real.exp_log (inv_pos.2 hA)).symm
        _ ≤ Real.exp (Real.posLog A⁻¹) := by gcongr; unfold Real.posLog; exact le_max_right _ _
  calc max 1 A⁻¹ ^ d ≤ Real.exp (Real.posLog A⁻¹) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = Real.exp (d * Real.posLog A⁻¹) := (Real.exp_nat_mul _ d).symm

theorem size_bound (K f N b rd Kx W1 W2 a bb c : ℝ) (g : ℕ) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hcf : c ≤ f) (hb3 : 3 ≤ b) (hN1 : 1 ≤ N) (hNb : N ≤ b)
    (hf1 : 1 ≤ f) (hfb : f ≤ b) (hrd0 : 0 ≤ rd) (hrd : rd ≤ b) (ha0 : 0 ≤ a) (haN : a ≤ N) (hbb0 : 0 ≤ bb)
    (hbN : bb ≤ N) (hW1 : W1 ≤ f * N * (8 * b)) (hW2 : W2 ≤ f * N * (8 * b)) (hW10 : 0 ≤ W1) (hW20 : 0 ≤ W2)
    (hg : (g : ℝ) = f * a * bb) (hKx : 0 < Kx)
    (hlogKx : Real.log Kx ≤ K * (W1 + W2 + c * (a + bb) ^ 2 + 1) * Real.log (2 + W1 + W2 + a + bb + c)) :
    Real.log (3 * (2 * (g : ℝ) * rd + 1) ^ g * Kx) ≤ (6 + 126 * K) * f * N * b * Real.log b ∧
      (g : ℝ) ≤ f * N * b := by
  have hb0 : 0 < b := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hlogb : 1 ≤ Real.log b := by
    have : Real.exp 1 ≤ b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hfN1 : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf1 hN1
  have hfNb : 1 ≤ f * N * b := by nlinarith
  have hab : a * bb ≤ N * N := mul_le_mul haN hbN hbb0 hN0
  have hfNN : f * a * bb ≤ f * N * N := by
    have := mul_le_mul_of_nonneg_left hab hf0
    linarith
  have hNN : f * N * N ≤ f * N * b := mul_le_mul_of_nonneg_left hNb (by positivity)
  have hgG : (g : ℝ) ≤ f * N * b := by rw [hg]; linarith
  have hfNb3 : f * N * b ≤ b ^ 3 := by
    have h1 := mul_le_mul hfb hNb hN0 hb0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hb0.le
    calc f * N * b ≤ b * b * b := h2
      _ = _ := by ring
  have hg3 : (g : ℝ) ≤ b ^ 3 := hgG.trans hfNb3
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hrdpos : 0 < 2 * (g : ℝ) * rd + 1 := by have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith
  have hq : 2 * (g : ℝ) * rd + 1 ≤ 3 * b ^ 4 := by
    have h1 := mul_le_mul hg3 hrd hrd0 (by positivity)
    have h2 : (1 : ℝ) ≤ b ^ 4 := one_le_pow₀ (by linarith)
    have h3 : b ^ 3 * b = b ^ 4 := by ring
    linarith
  have hl3 : Real.log 3 ≤ Real.log b := Real.log_le_log (by norm_num) hb3
  have hlq : Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * Real.log b := by
    calc _ ≤ Real.log (3 * b ^ 4) := Real.log_le_log hrdpos hq
      _ = Real.log 3 + 4 * Real.log b := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by linarith
  have hlq0 : 0 ≤ Real.log (2 * (g : ℝ) * rd + 1) := Real.log_nonneg (by
    have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith)
  have hY0 : 0 ≤ f * N * b * Real.log b := by positivity
  have hgl : (g : ℝ) * Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * (f * N * b * Real.log b) := by
    have := mul_le_mul hgG hlq hlq0 (by positivity); linarith
  have hKb : Real.log Kx ≤ 126 * K * (f * N * b * Real.log b) := by
    have hsq : (a + bb) ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hab2 : c * (a + bb) ^ 2 ≤ 4 * (f * N * b) := by
      have := mul_le_mul hcf hsq (by positivity) hf0
      have e : f * (2 * N) ^ 2 = 4 * (f * N * N) := by ring
      linarith
    have hQ1 : W1 + W2 + c * (a + bb) ^ 2 + 1 ≤ 21 * (f * N * b) := by linarith
    have hQ1' : 0 ≤ W1 + W2 + c * (a + bb) ^ 2 + 1 := by positivity
    have hArg0 : 0 < 2 + W1 + W2 + a + bb + c := by linarith
    have hb27 : (27 : ℝ) ≤ b ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hb3 3; norm_num at this; linarith
    have hbb3 : b ≤ b ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have hArg : 2 + W1 + W2 + a + bb + c ≤ 27 * b ^ 3 := by linarith
    have hQ2 : Real.log (2 + W1 + W2 + a + bb + c) ≤ 6 * Real.log b := by
      calc _ ≤ Real.log (27 * b ^ 3) := Real.log_le_log hArg0 hArg
        _ = 3 * Real.log 3 + 3 * Real.log b := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
              show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
        _ ≤ _ := by linarith
    have hQ20 : 0 ≤ Real.log (2 + W1 + W2 + a + bb + c) := Real.log_nonneg (by linarith)
    have := mul_le_mul (mul_le_mul_of_nonneg_left hQ1 hK0) hQ2 hQ20 (by positivity)
    refine hlogKx.trans (this.trans (le_of_eq ?_))
    ring
  refine ⟨?_, hgG⟩
  rw [Real.log_mul (by positivity) hKx.ne', Real.log_mul (by norm_num) (pow_pos hrdpos g).ne', Real.log_pow]
  have hlY : Real.log b ≤ f * N * b * Real.log b := le_mul_of_one_le_left (by linarith) hfNb
  have e : (6 + 126 * K) * f * N * b * Real.log b =
      f * N * b * Real.log b + 5 * (f * N * b * Real.log b) + 126 * K * (f * N * b * Real.log b) := by ring
  rw [e]; linarith

theorem rowSizes : BigC fun {D} _ _ _ _ _ _ _ _ _ _ _ _ ch _ b =>
    ∀ i τ a, ((wt ch.G (.grid i D.R.m) τ).natW a : ℝ) ≤ 29 * b := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch _ i τ a
  have hc : ch.sc.cGap = 1 := by
    have h : ch.sc = { cGap := 1, cDep := CF, b := large₂.sc.b } := hch
    rw [h]
  have hb1 := GlobalTheory.GridWtBound.one_le_b large₂ hS.size
  have key : ∀ x ∈ GlobalTheory.SignedHC.entries (Node.par D ch.sc.cGap (.grid i D.R.m) τ), |(x : ℝ)| ≤ 14 * large₂.sc.b := by
    rw [hc]; exact abs_entry_le large₂ hS.size i τ
  have hw := GlobalTheory.GridWtBound.natW_dual_wtOf_le _ _ (14 * large₂.sc.b) (by linarith) key a
  calc (((wt ch.G (.grid i D.R.m) τ).natW a : ℕ) : ℝ)
      = (((wtOf _ (GlobalTheory.SignedHC.entries (Node.par D ch.sc.cGap (.grid i D.R.m) τ))).dual.natW a : ℕ) : ℝ) := rfl
    _ ≤ 2 * (14 * large₂.sc.b) + 1 := hw
    _ ≤ 29 * large₂.sc.b := by linarith

theorem even_rank_mul {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    Even ((G.V (.grid (i + 1) D.R.m)).rank * (G.V (.grid i D.R.m)).rank) := by
  have h : ∀ j, j ≤ D.R.m → (G.V (.grid j D.R.m)).rank = D.R.r + D.R.m * D.R.t + j * sLen D := by
    rintro (_ | j) hj
    · have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
      rw [e, D.sp.X'_rank, zero_mul, add_zero]
      rfl
    · rw [(G.isV (X := .grid (j + 1) D.R.m) ⟨hj, le_rfl⟩ (by simp)).rank]
      rfl
  rw [h _ hi, h i (by omega), add_mul i, one_mul, ← add_assoc]
  generalize D.R.r + D.R.m * D.R.t + i * sLen D = x
  have hs := odd_sLen D
  rcases Nat.even_or_odd x with hx | hx
  · exact hx.mul_left _
  · exact (hx.add_odd hs).mul_right _

def barQ : Qbar →+* Qbar :=
  ((starRingEnd ℂ).comp (algebraMap Qbar ℂ)).codRestrict _ fun x =>
    mem_algebraicClosure_iff.2 (IsAlgebraic.algHom (starRingEnd ℂ).toRatAlgHom (mem_algebraicClosure_iff.1 x.2))

def embQ (D : D7) : D.what₂.LL →+* Qbar :=
  D.what₂.embLL.codRestrict _ fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom)

section Row

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem kkMap_eq {t : T} {p : GlobalTheory.ChiGrid.Pair T} (hp : DefPair D.R.m p) (d : FinDatum ch.G t p) (x : FinPt ch.G p.small)
    (y : FinPt ch.G p.big) (J : (Formalism.L2.Ker.DVar D.what₂.Tau (ch.G.V p.small).rank (ch.G.V p.big).rank →₀ ℕ) → ℂ)
    (hJ : ∀ mon, jetTab ch.W ch.S.N.frC p (ch.S.Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _) mon =
      ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * J mon)) :
    ch.S.Z.kkMap 1 d x y = Formalism.L2.Ker.jetOp _ _ (fun m => opp p (J m)) (nuEnd ch.G p) := by
  have hW := wtOK_of_defPair ch.G p hp
  set Z := ch.S.Z
  set c : D.what₂.Tau → ℂ := fun τ => opp p (period Z.δ τ) with hc
  have hf : ∀ k, (fvar ch.G p k).1 = k.1 := fun k => by cases p <;> rfl
  have hJf : jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _) =
      fun m => (Z.c0 p : ℂ) * ((m.prod fun k e => c k.1 ^ e) * opp p (J m)) := by
    funext m
    rw [hJ m, map_mul]
    congr 2
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), map_finsuppProd]
    simp only [map_pow, hf, hc]
  have hop : Formalism.L2.Ker.jetOp (wt ch.G p.small) (wt ch.G p.big)
      (jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _)) (nuEnd ch.G p) =
        ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) • Formalism.L2.Ker.jetOp _ _ (fun m => opp p (J m)) (nuEnd ch.G p) := by
    refine LinearMap.ext fun P => ?_
    rw [hJf, LinearMap.smul_apply]
    simp only [Formalism.L2.Ker.jetOp, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [GlobalTheory.JetScale.jetMap_weight_scale, GlobalTheory.blockAct_diag_mem_VV _ _ _ (hW.2 _ P.1 P.2), smul_smul, map_smul]
    rfl
  have e : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) = 1 := by
    simp only [Normal.scal, Pi.one_apply, hc]
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← mul_pow, ← map_mul, one_div, inv_mul_cancel₀ (Z.period_ne_zero _ τ), map_one, one_pow]
  rw [Normal.kkMap, fockComp, hop, smul_smul, e, one_smul]

theorem row_jets (hI : GlobalTheory.NormSum.Inp D) (hDict : DictAt ch) {Φ β d} (hocc : Occurs ch.S.toGridChoice A.μ0 Φ β d)
    (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m)))
    (hf : ∀ u, ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) (σ : D.what₂.LL →+* ℂ) {ρ} (hρ : ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ)
    (L : AddSubgroup ℂ) (hL : L = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ))
    (g : ℕ) (hg : g = fF D * (ch.G.V (.grid (i + 1) D.R.m)).rank * (ch.G.V (.grid i D.R.m)).rank) :
    ∃ H : VC D (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid (i + 1) D.R.m)).rank → ℂ, 0 < area L ∧ Differentiable ℂ H ∧
      (∀ z, ‖H z‖ ^ 2 ≤ 3 * (2 * (g : ℝ) * D.host.rdE + 1) ^ g * nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ)) ^ g *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area L)) ∧
      ∀ u, GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ (f u) =
        Formalism.L2.Ker.jetOp (wt ch.G (.grid i D.R.m)) (wt ch.G (.grid (i + 1) D.R.m))
          (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H) (nuEnd ch.G (.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))
          (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) := by
  obtain ⟨-, τ, ⟨hk, ⟨e, -, h1, -⟩, h3⟩, hd⟩ := hocc
  have hp : DefPair D.R.m (.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) := ⟨i.2, rfl⟩
  have hW := wtOK_of_defPair ch.G _ hp
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, -, hr, -, hJ⟩ := hDict A.μ0 _ hp _ (d.2 i) hk ((h3 d hd).2 i)
    ((h1 d hd).2 i).2.2 ((h1 d hd).2 i).1 (ch.S.ptRow c i) (ch.S.ptRow c (i + 1))
  have hkk := kkMap_eq ch hp (d.2 i) _ _ _ hJ
  haveI := fld_finiteDimensional D hI _ _ ch.S.Z.crv ch.S.Z.pt0
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.ArchNorm.exists_extension _ ρ
  have hlam : lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) = L := by
    rw [hL]
    unfold lamConj
    rw [hρ' _ (IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))),
      hρ' _ (IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp)))]
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 _ _ ch.S.Z.crv
  obtain ⟨t', ht'⟩ := (hI.t0Ex _ _ ch.S.Z.crv).2 Qbar ρ' hdata.2.1 hdata.2.2
  have htc : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)) (tc D ch.S.Z.δ ch.S.Z.t0 ρ) := by
    rw [hlam, hL] at ht' ⊢
    unfold tc; rw [dif_pos ⟨t', ht'⟩]; exact Exists.choose_spec _
  have hev := even_rank_mul ch.G i i.2
  obtain ⟨harea, hcoef, hdiff, hgr⟩ := GlobalTheory.ConjGrowth.conj_growth D hI _ _ _ ch.S.Z.crv ch.S.Z.pt0 _ _ _ hev
    (ch.S.Z.e0_is _ hp) Ls Lt hLs hLt κ hκ _ n r s hk hs hr ρ' _ htc
  have htay := taylor_fnConj_comb D hI _ _ _ ch.S.Z.crv ch.S.Z.pt0 _ _ _ hev
    (ch.S.Z.e0_is _ hp) Ls Lt hLs hLt κ hκ.1 _ n r s hk hs ρ'
  rw [hlam, ← hg] at hgr
  rw [hlam] at harea
  revert hkk hcoef hdiff hgr htay
  generalize (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) _ z) = FF
  intro hkk hcoef hdiff hgr htay
  refine ⟨fun z => fnConj D Qbar ρ' FF (trL D _ _ z), harea,
    hdiff.comp (LinearMap.toContinuousLinearMap (trL D _ _)).differentiable, fun z => ?_, fun u => ?_⟩
  · refine (hgr _).trans (le_of_eq ?_)
    congr 4
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_comm
  let J : (Formalism.L2.Ker.DVar D.what₂.Tau (ch.G.V (.grid i D.R.m)).rank (ch.G.V (.grid (i + 1) D.R.m)).rank →₀ ℕ) → Qbar :=
    fun m => (((m.mapDomain fun k => (k.1, k.2.2, k.2.1)).prod fun _ n => n.factorial : ℕ) : Qbar) *
      ⟨_, hcoef (m.mapDomain fun k => (k.1, k.2.2, k.2.1))⟩
  have e1 : ((algebraMap Qbar ℂ).comp barQ).comp (barQ.comp (embQ D)) = D.what₂.embLL :=
    RingHom.ext fun x => Complex.conj_conj _
  have e2 : (ρ' : Qbar →+* ℂ).comp (barQ.comp (embQ D)) = σ.comp (starRingEnd D.what₂.LL) := RingHom.ext fun x => by
    have h1 := hρ' _ (embLL_mem D ch.S.Z.δ ch.S.Z.t0 (starRingEnd _ x))
    unfold TaylorLogMetric.liftM at h1
    rw [dif_pos (embLL_mem D ch.S.Z.δ ch.S.Z.t0 (starRingEnd _ x)), hρ,
      dif_pos (show D.what₂.embLL (starRingEnd _ x) ∈ Qbar from (embQ D (starRingEnd _ x)).2)] at h1
    refine Eq.trans (congrArg ρ' (Subtype.ext ?_)) h1
    exact (D.starLL_cx x).symm
  have key := jetOp_transport _ _ _ hW.2 (barQ.comp (embQ D)) ((algebraMap Qbar ℂ).comp barQ) (ρ' : Qbar →+* ℂ) J u (f u) (by
    rw [e1, ← hf u, hkk]
    congr 2
    funext m
    rw [applyAt0_monomial]
    change starRingEnd ℂ (J m : ℂ) = starRingEnd ℂ _
    congr 1
    simp only [J, Finsupp.prod]
    push_cast
    rfl)
  rw [e2] at key
  refine key.trans ?_
  congr 2
  funext m
  rw [applyAt0_tr D hdiff, applyAt0_monomial, htay]
  simp only [J, Finsupp.prod, map_mul, map_natCast, StandardLatticesGL3.cj, TaylorLogMetric.liftM, dif_pos (hcoef _)]
  push_cast
  rfl

end Row

theorem conjRowK : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 →
    BigC fun _ ch C b => ConjRowAt ch C b C1 := by
  intro _ hInp hDict _ C1 hC1
  obtain ⟨K, hK0, hFock⟩ := GlobalTheory.FockJetBound.jetOp_norm_le
  obtain ⟨CF0, h⟩ := BigC.and (BigC.and hDict rowSizes) GlobalTheory.KerConjMean.TopSizes.sizesK
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨max C0 (24 * (6 + 126 * K) + 36 * C1), fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨⟨hA, hwt⟩, hb3, hN1, hNb, hf1, hfb, hcard, hrd0, hrd, -⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  have hCb : 24 * (6 + 126 * K) + 36 * C1 ≤ C := (le_max_right _ _).trans hC
  have hlogb : 1 ≤ Real.log large₂.sc.b := by
    have : Real.exp 1 ≤ large₂.sc.b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hlog4 : Real.log (4 * large₂.sc.b) ≤ 3 * Real.log large₂.sc.b := by
    calc _ ≤ Real.log (large₂.sc.b ^ 3) := Real.log_le_log (by linarith) (by nlinarith [mul_le_mul hb3 hb3 (by norm_num) (by linarith)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hN1' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN1
  have hf1' : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf1
  have hb0 : 0 ≤ large₂.sc.b := by linarith
  have hX : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine ⟨12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b, 32 * D.R.f * bigN D * large₂.sc.b,
    4 * D.R.f * bigN D * large₂.sc.b, by positivity, by positivity, by positivity, ?_, ?_⟩
  · have hsig : 0 ≤ sig ch.G :=
      Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hC0 : 0 ≤ C := by linarith
    have h2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
    have h3 := mul_le_mul_of_nonneg_right hCb hX
    unfold aOne
    nlinarith
  · intro Φ β d hocc c j fm hfm σ ρ hρ u B hu
    obtain ⟨L, hL⟩ : ∃ L, L = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) := ⟨_, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g, g = fF D * (ch.G.V (.grid (j + 1) D.R.m)).rank * (ch.G.V (.grid j D.R.m)).rank := ⟨_, rfl⟩
    obtain ⟨H, harea, hdiff, hgr, hfeq⟩ := row_jets ch (hInp D) hA hocc c j fm hfm σ hρ L hL g hg
    have hp : DefPair D.R.m (.chi j D.R.m : GlobalTheory.ChiGrid.Pair T) := ⟨j.2, rfl⟩
    obtain ⟨hpos, Kx, hKx, hlogKx, hop⟩ := hFock D _ _ (wt ch.G (.grid j D.R.m)) (wt ch.G (.grid (j + 1) D.R.m)) _
      (wtOK_of_defPair ch.G _ hp).2
    have eA : hArea D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (area L)⁻¹ := by
      unfold hArea; rw [hL]
    have eT : hTh D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ))) := by
      unfold hTh; rw [hL]
    set X := nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ)) with hXdef
    set a := (ch.G.V (.grid j D.R.m)).rank with ha
    set bb := (ch.G.V (.grid ((j : ℕ) + 1) D.R.m)).rank with hbb
    set P := 3 * (2 * ((g : ℕ) : ℝ) * D.host.rdE + 1) ^ g with hP
    set deg := ∑ τ, ∑ i, (wt ch.G (.grid ((j : ℕ) + 1) D.R.m) τ).natW i with hdeg
    have hS : 0 ≤ P * X ^ g := by
      have h0 := hgr 0
      have : (∑ τ, ∑ i, ∑ j, ‖(0 : VC D a bb) τ i j‖ ^ 2) = 0 := by simp
      rw [this, mul_zero, zero_div, Real.exp_zero, mul_one] at h0
      exact le_trans (sq_nonneg _) h0
    have hop' := hop _ (P * X ^ g) _ harea hS hdiff hgr (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u)
    have hM0 : 0 ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg :=
      mul_nonneg (mul_nonneg hS hKx.le) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hrdpos : 0 < 2 * ((g : ℕ) : ℝ) * D.host.rdE + 1 := by
      have := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg g)) hrd0; linarith
    have hPpos : 0 < P := by rw [hP]; exact mul_pos (by norm_num) (pow_pos hrdpos g)
    have hrk : ∀ jj : ℕ, jj ≤ D.R.m → ((ch.G.V (.grid jj D.R.m)).rank : ℝ) ≤ bigN D := fun jj hjj => by
      exact_mod_cast GlobalTheory.DefRank.rank_le_bigN ch.G (.grid jj D.R.m) ⟨hjj, rfl⟩
    have hW : ∀ jj : ℕ, jj ≤ D.R.m → (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) * (8 * (4 * large₂.sc.b)) := by
      intro jj hjj
      calc (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) ≤
            ∑ τ : D.what₂.Tau, ∑ i : Fin (ch.G.V (.grid jj D.R.m)).rank, (8 * (4 * large₂.sc.b)) :=
            Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => (hwt jj τ i).trans (by linarith)
        _ = (Fintype.card D.what₂.Tau : ℝ) * (((ch.G.V (.grid jj D.R.m)).rank : ℝ) * (8 * (4 * large₂.sc.b))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (D.R.f : ℝ) * ((bigN D : ℝ) * (8 * (4 * large₂.sc.b))) := by
            have h1 : (Fintype.card D.what₂.Tau : ℝ) ≤ D.R.f := by exact_mod_cast hcard
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right (hrk jj hjj) (by positivity)) (by positivity) (by positivity)
        _ = _ := by ring
    have hW0 : ∀ jj : ℕ, 0 ≤ (∑ τ, ∑ i, ((wt ch.G (.grid jj D.R.m) τ).natW i : ℝ)) := fun jj =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have haN : (a : ℝ) ≤ bigN D := hrk j j.2.le
    have hbN : (bb : ℝ) ≤ bigN D := hrk _ (Nat.succ_le_of_lt j.2)
    have hgc : (g : ℝ) = (D.R.f : ℝ) * a * bb := by rw [hg, mul_right_comm]; push_cast; rfl
    obtain ⟨hc0, hgG⟩ := size_bound K D.R.f (bigN D) (4 * large₂.sc.b) D.host.rdE Kx _ _ a bb (Fintype.card D.what₂.Tau) g hK0
      (Nat.cast_nonneg _) (by exact_mod_cast hcard) (by linarith) hN1' (by linarith) hf1' (by linarith)
      hrd0 (by linarith) (Nat.cast_nonneg _) haN (Nat.cast_nonneg _) hbN (hW j j.2.le) (hW _ (Nat.succ_le_of_lt j.2))
      (hW0 _) (hW0 _) hgc hKx hlogKx
    have hc : Real.log (P * Kx) ≤ 12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b := by
      rw [hP]
      refine hc0.trans ((mul_le_mul_of_nonneg_left hlog4 (by positivity)).trans (le_of_eq ?_))
      ring
    have hdN : (deg : ℝ) ≤ 32 * D.R.f * bigN D * large₂.sc.b := by
      have e : (deg : ℝ) = ∑ τ, ∑ i, ((wt ch.G (.grid ((j : ℕ) + 1) D.R.m) τ).natW i : ℝ) := by rw [hdeg]; push_cast; rfl
      rw [e]; refine (hW _ (Nat.succ_le_of_lt j.2)).trans (le_of_eq ?_); ring
    have hpA : 0 ≤ Real.posLog (area L)⁻¹ := Real.posLog_nonneg
    have hpX : 0 ≤ Real.posLog X := Real.posLog_nonneg
    have hMexp : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤ Real.exp (12 * (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b *
        Real.log large₂.sc.b + 32 * D.R.f * bigN D * large₂.sc.b * hArea D ch.S.Z.δ ch.S.Z.t0 ρ +
        4 * D.R.f * bigN D * large₂.sc.b * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      have hXg := pow_le_exp_posLog X g
      have hMd := max_pow_le_exp_posLog (area L) harea deg
      have step1 : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤
          (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) := by
        have := mul_le_mul hXg hMd (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.exp_pos _).le
        calc P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg = (P * Kx) * (X ^ g * max 1 (area L)⁻¹ ^ deg) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (mul_nonneg hPpos.le hKx.le)
      refine step1.trans ?_
      have eq : (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) =
          Real.exp (Real.log (P * Kx) + g * Real.posLog X + deg * Real.posLog (area L)⁻¹) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (mul_pos hPpos hKx)]; ring
      rw [eq, Real.exp_le_exp, eA, eT]
      linarith [mul_le_mul_of_nonneg_right hgG hpX, mul_le_mul_of_nonneg_right hdN hpA]
    rw [hfeq u]
    calc _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg *
          nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) := hop'
      _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * B := mul_le_mul_of_nonneg_left hu hM0
      _ ≤ _ := mul_le_mul_of_nonneg_right hMexp (le_trans (hpos _) hu)

end GlobalTheory.KerConjRow

end
