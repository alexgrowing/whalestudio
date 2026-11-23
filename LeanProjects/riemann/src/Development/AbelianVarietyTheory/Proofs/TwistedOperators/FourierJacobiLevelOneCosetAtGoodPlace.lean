import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitAny
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.OneCosetFJ

open GlobalTheory.FinPl (Pl colMul)
open GlobalTheory.FinPl.SuppShift

variable {D : D7}

theorem flagN_mem_Rgrp {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) {n : GA D W}
    (hn : n ∈ flagN d) : n ∈ Rgrp W (xLast d z) := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D W W₀ σ d).1 n).1 hn
  have hm : mt W (d.levi u * (d.nB b * d.nC c)) ⬝ d.j0 = d.j0 + d.jX ⬝ (u.1 ⬝ b) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
      ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc]
  refine (GlobalTheory.Unf.FB.snocCols_uni_iff (AE D) W.rank σ d.jX (d.j0 *ᵥ ratV z) (mt W _)).2
    ⟨u, hu, (u.1 ⬝ b) *ᵥ ratV z, ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  · rw [Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem embA_mem_Rgrp {W W₀ A L : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) (o : OrthDec W₀ A L) (ζ : Fin L.rank → D.host.E)
    (h : GA D A) : d.emb0 (o.emb (h, 1)) ∈ Rgrp W (xLast d (vecB o ζ)) := by
  refine (GlobalTheory.Unf.FB.snocCols_uni_iff (AE D) W.rank σ d.jX (d.j0 *ᵥ ratV (vecB o ζ)) (mt W _)).2
    ⟨1, one_mem _, 0, ?_, ?_⟩
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]
  · rw [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec,
      vecB, GlobalTheory.Unf.FB.ratV_mulVec_rat]
    change d.j0 *ᵥ (mt W₀ (o.emb (h, 1)) *ᵥ (o.jB *ᵥ ratV ζ)) = d.j0 *ᵥ (o.jB *ᵥ ratV ζ)
    congr 1
    rw [Matrix.mulVec_mulVec, o.emb_jB, mt_one, Matrix.mul_one]

theorem wittDec_embedding_preserves_latticeStabilizer {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) {L : Lat W} {L₀ : Lat W₀} {v : Pl D} (hm : MonoAt d L L₀ v)
    {κ : GA D W₀} (hκ : InK W₀ L₀ (· = v) κ) : InK W L (· = v) (d.emb0 κ) := by
  have key : ∀ {k : GA D W₀}, InK W₀ L₀ (· = v) k → ∀ y ∈ latV W L (· = v), mt W (d.emb0 k) *ᵥ y ∈ latV W L (· = v) := by
    intro k hk y hy
    obtain ⟨hX, hY, h0⟩ := (hm y).1 hy
    refine (hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]; exact hX i
    · rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]; exact hY i
    · rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding, ← Matrix.mulVec_mulVec]
      exact (hk.2 _ (GlobalTheory.FinPl.FrameLat.latV_supp h0)).1 h0
  refine ⟨GlobalTheory.IwaPlace.wittCoreEmbedding_preserves_supportedUnitarySubgroup d hκ.1, fun y _ => ⟨key hκ y, fun hy => ?_⟩⟩
  have h := key (GlobalTheory.AscFin.inK_inv hκ) _ hy
  rwa [Matrix.mulVec_mulVec, map_inv, mt_inv_mul, Matrix.one_mulVec] at h

theorem inK_maps {W : HSp D} {L : Lat W} {P : Pl D → Prop} {κ : GA D W} (hκ : InK W L P κ) (y : Fin W.rank → AE D)
    (hy : y ∈ latV W L P) : mt W κ *ᵥ y ∈ latV W L P := (hκ.2 _ (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy

section General

variable {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ} {dW : HypDec W W₀ σ}
  {p : Pieces V₀ W W₀ ρ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W} {LW₀ : Lat W₀}
  {v : Pl D}

set_option maxHeartbeats 1600000 in

theorem col_of_pt (hG : GoodAt dV dW x ψ LV LV₀ LW LW₀ v) (hS : StdAt dV dW p LV LW v) {r g κ : GA D W}
    (hr : r ∈ Rgrp W x) (hκ : InK W LW (· = v) κ) (hC : Cond dW p x y ψ (· = v) (r * g * κ))
    (q : Mx D W.rank W.rank) (hq : ∀ z ∈ latV W LW (· = v), q *ᵥ z ∈ latV W LW (· = v)) (i : Fin ρ)
    (hi : ∀ j < i, ∀ k, (q ⬝ (mt W g⁻¹ ⬝ x)) k j = 0) (c : AE D) (hc : colMul dV.jX i c ∈ latV V LV (· = v)) :
    colMul (q ⬝ (mt W g⁻¹ ⬝ x)) i c ∈ latA W LW (· = v) := by
  obtain ⟨u, a, ha, hoff⟩ := hC.pt
  obtain ⟨b, hab, hb⟩ := hS.a' a ha
  obtain ⟨u', hu', hru⟩ := inv_mem hr
  have hc' := idAt_of_colMul dV hc
  have hb' : colMul b i c ∈ latA W LW (· = v) := by
    have h := GlobalTheory.FinPl.LatMem.latO_maps hG.sdV hb hc
    have e : (dV.extX W b) *ᵥ colMul dV.jX i c = colMul b i c := by
      rw [mulVec_colMul, HypDec.extX_apply, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one]
    exact e ▸ h
  have h1 : colMul (mt W (r * g * κ)⁻¹ ⬝ (x ⬝ u.1.1)) i c ∈ latA W LW (· = v) := by
    convert add_mem ((hG.cols i c hc').1 hc) hb' using 1
    funext k
    have e1 := GlobalTheory.DisjComb.mul_eq_zero_of_off (hoff k i) hc'
    have e2 := GlobalTheory.DisjComb.mul_eq_zero_of_off (hab k i) hc'
    simp only [Matrix.sub_apply] at e1 e2
    simp only [colMul, Pi.add_apply]
    linear_combination e1 + e2
  have h2 := mulVec_latA q hq (mulVec_latA (mt W κ) (inK_maps hκ) h1)
  rw [mulVec_colMul, mulVec_colMul] at h2
  have e : q ⬝ (mt W κ ⬝ (mt W (r * g * κ)⁻¹ ⬝ (x ⬝ u.1.1))) = q ⬝ (mt W g⁻¹ ⬝ x) ⬝ (u' * u.1).1 := by
    rw [← Matrix.mul_assoc (mt W κ), ← mt_mul, show κ * (r * g * κ)⁻¹ = g⁻¹ * r⁻¹ by group, mt_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (mt W r⁻¹), hru, Units.val_mul]
    simp only [Matrix.mul_assoc]
  have hw := mem_UX.1 (mul_mem hu' u.2)
  rw [e] at h2
  convert h2 using 1
  funext k
  rw [colMul, colMul, Matrix.mul_apply (M := q ⬝ (mt W g⁻¹ ⬝ x)), Finset.sum_eq_single i, (hw i i).2, mul_one]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hi j h k, zero_mul]
    · rw [(hw j i).1 h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem psi_of_shift (hG : GoodAt dV dW x ψ LV LV₀ LW LW₀ v) (hS : StdAt dV dW p LV LW v) {r g κ : GA D W}
    (hr : r ∈ Rgrp W x) (hκ : InK W LW (· = v) κ) (hC : Cond dW p x y ψ (· = v) (r * g * κ))
    (i j : Fin ρ) (hij : j.1 = i.1 + 1) (s : AE D) (hs : s ∈ idAt D (· = v))
    (hu : dV.extX W (mt W g⁻¹ ⬝ x ⬝ (Matrix.single i j s : Mx D ρ ρ)) ∈ latO V W (LV : Set _) (LW : Set _) (· = v)) :
    psiE ψ s = 1 := by
  obtain ⟨u, hu', hru⟩ := hr
  have hU := mem_UX.1 hu'
  have hE : MxAt (· = v) (Matrix.single i j s : Mx D ρ ρ) := fun k l => by
    rw [Matrix.single_apply]
    split_ifs
    · exact hs
    · exact zero_mem _
  have hN : MxAt (· = v) (u.1 ⬝ (Matrix.single i j s : Mx D ρ ρ)) := mxAt_mul_left _ hE
  have e : mt W (r * g * κ)⁻¹ ⬝ (x ⬝ (u.1 ⬝ (Matrix.single i j s : Mx D ρ ρ))) =
      mt W κ⁻¹ ⬝ (mt W g⁻¹ ⬝ x ⬝ (Matrix.single i j s : Mx D ρ ρ)) := by
    rw [← Matrix.mul_assoc x, ← hru, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul,
      show (r * g * κ)⁻¹ * r = κ⁻¹ * g⁻¹ by group, mt_mul]
    simp only [Matrix.mul_assoc]
  have h1 := hC.shift _ hN (fun k l hkl => by
      by_cases hl : l = j
      · subst hl
        rw [Matrix.mul_single_apply_same, (hU k i).1 (by rw [Fin.le_def] at hkl; rw [Fin.lt_def]; omega), zero_mul]
      · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]) (by
      refine (hS.a _ (mxAt_mul_left _ (mxAt_mul_left _ hN))).2 ?_
      have h := sandwich_latO hG.sdV hG.sdW (mt W κ⁻¹) (inK_maps (GlobalTheory.AscFin.inK_inv hκ)) 1
        (fun z hz => by rwa [Matrix.one_mulVec]) hu
      rw [e]
      convert h using 1
      simp only [HypDec.extX_apply, Matrix.mul_assoc, Matrix.mul_one])
  have e2 : upSum (u.1 ⬝ (Matrix.single i j s : Mx D ρ ρ)) = s := by
    unfold upSum
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j, if_pos hij, Matrix.mul_single_apply_same, (hU i i).2, one_mul]
    · intro l _ hl; rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro k _ hk
      refine Finset.sum_eq_zero fun l _ => ?_
      split_ifs with hl
      · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ fun h => hk (Fin.ext (by subst h; omega))]
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  rwa [e2] at h1

end General

set_option maxHeartbeats 1600000 in

theorem parts {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {σ : ℕ} {dV : HypDec V V₀ (σ + 1)} {dW : HypDec W W₀ σ}
    {p : Pieces V₀ W W₀ (σ + 1) σ} {z : Fin W₀.rank → D.host.E} {y : Mx D V₀.rank σ} {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    {LW₀ : Lat W₀} {v : Pl D} (hA : GoodAt dV dW (xLast dW z) ψ LV LV₀ LW LW₀ v) (hS : StdAt dV dW p LV LW v)
    {t : GL (Fin σ) (AE D)} (ht : ∀ i j, i ≠ j → t.1 i j = 0) (htG : dW.levi t ∈ grpAt W (· = v)) (γ : GA D W₀)
    {r κ : GA D W} (hr : r ∈ Rgrp W (xLast dW z)) (hκ : InK W LW (· = v) κ)
    (hC : Cond dW p (xLast dW z) y ψ (· = v) (r * (dW.levi t * dW.emb0 γ) * κ)) :
    InK W LW (· = v) (dW.levi t) ∧ ∀ a : AE D, a • ratV z ∈ latA W₀ LW₀ (· = v) →
      mt W₀ γ⁻¹ *ᵥ (a • ratV z) ∈ latA W₀ LW₀ (· = v) := by
  set g := dW.levi t * dW.emb0 γ with hg
  have hgX : mt W g⁻¹ ⬝ dW.jX = dW.jX ⬝ (t⁻¹).1 := by
    rw [hg, _root_.mul_inv_rev, ← map_inv, ← map_inv, mt_mul, Matrix.mul_assoc, dW.levi_jX, cancel₂ (dW.wittDecomp_anisotropicEmbedding_inclX _)]
  have hg0 : mt W g⁻¹ ⬝ dW.j0 = dW.j0 ⬝ mt W₀ γ⁻¹ := by
    rw [hg, _root_.mul_inv_rev, ← map_inv, ← map_inv, mt_mul, Matrix.mul_assoc, dW.wittDecomp_levi_inclAnisotropic, dW.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  have hD := col_of_pt hA hS hr hκ hC
  have hti := inv_diag ht
  refine ⟨inK_levi dW hA.monoW ht htG (fun i => ?_) fun i => ?_, fun c hc => ?_⟩
  · refine int_of_stable dV hA.sdV hA.monoV i.castSucc (levi_entry dW htG i) ?_
    refine stable_of_prim dV hA.sdV hA.monoV hA.prim i.castSucc i.succ (by simp) fun s' hs' hr' => ?_
    refine psi_of_shift hA hS hr hκ hC i.castSucc i.succ (by simp) _ (Ideal.mul_mem_left _ _ hs') ?_
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ LV LW hA.sdV hA.sdW (· = v) _).2
      ⟨mxAt_mul_right (mxAt_mul_left _ fun k l => ?_) _, fun y hy => ?_⟩
    · rw [Matrix.single_apply]
      split_ifs
      · exact Ideal.mul_mem_left _ _ hs'
      · exact zero_mem _
    · change (mt W g⁻¹ ⬝ xLast dW z ⬝ (Matrix.single i.castSucc i.succ (t.1 i i * s') : Mx D (σ + 1) (σ + 1)) ⬝
        dV.pX) *ᵥ y ∈ _
      rw [← Matrix.mulVec_mulVec, single_mulVec']
      have h1 := hr' _ (((hA.monoV y).1 hy).1 i.succ)
      have h2 := (hA.cols _ _ (idAt_of_colMul dV h1)).1 h1
      convert h2 using 1
      funext k
      rw [colMul, colMul, mul_xLast_castSucc, hgX, mul_diag _ hti, xLast_castSucc]
      linear_combination (s' * (dV.pX *ᵥ y) i.succ * dW.jX k i) * inv_diag_mul ht i
  · refine int_of_stable dV hA.sdV hA.monoV i.castSucc (levi_entry dW (by rw [map_inv]; exact inv_mem htG) i)
      fun c hc => ?_
    have hcol : ∀ k (j : Fin σ), (dW.jX ⬝ (Matrix.single i i 1 : Mx D σ σ) ⬝ dW.pX ⬝ (mt W g⁻¹ ⬝ xLast dW z)) k
        j.castSucc = dW.jX k i * (t⁻¹).1 i j := fun k j => by
      rw [← Matrix.mul_assoc, mul_xLast_castSucc, Matrix.mul_assoc, hgX, Matrix.mul_assoc, cancel₂ dW.pX_jX,
        Matrix.one_mul, Matrix.mul_apply, Finset.sum_eq_single i, Matrix.mul_single_apply_same, mul_one]
      · intro l _ hl; rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h1 := hD (dW.jX ⬝ (Matrix.single i i 1 : Mx D σ σ) ⬝ dW.pX)
      (fun y hy => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hA.monoW y).1 hy).1 i) i.castSucc
      (fun j hj k => by
        obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hj)
        rw [hcol, hti i j (Fin.castSucc_lt_castSucc_iff.1 hj).ne', mul_zero]) c hc
    refine (hA.cols _ _ (Ideal.mul_mem_left _ _ (idAt_of_colMul dV hc))).2 ?_
    convert h1 using 1
    funext k
    rw [colMul, colMul, hcol, xLast_castSucc]
    ring
  · have hε : (eps v * c) • ratV z = c • ratV z := by
      rw [mul_smul]
      funext k
      exact eps_mul (latA_supp hc k)
    have h0 : colMul (xLast dW z) (Fin.last σ) (eps v * c) ∈ latA W LW (· = v) := by
      have h := GlobalTheory.FinPl.VacFlat.wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace dW hA.monoW hc
      rw [← hε, Matrix.mulVec_smul] at h
      convert h using 1
      funext k
      rw [colMul, xLast_last]
      rfl
    have h1 := hD (dW.j0 ⬝ dW.p0)
      (fun y hy => by
        rw [← Matrix.mulVec_mulVec]
        exact GlobalTheory.FinPl.VacFlat.wittCoreInclusion_mem_latticeCompletionAtPlace dW hA.monoW ((hA.monoW y).1 hy).2.2) (Fin.last σ)
      (fun j hj k => by
        obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj.ne
        rw [← Matrix.mul_assoc, mul_xLast_castSucc, Matrix.mul_assoc, hgX, Matrix.mul_assoc, cancel₂ dW.p0_jX,
          Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]) _
      ((hA.cols _ _ (Ideal.mul_mem_right _ _ (eps_idAt v))).2 h0)
    have h2 := mulVec_latA dW.p0 (fun y hy => ((hA.monoW y).1 hy).2.2) h1
    rw [mulVec_colMul] at h2
    rw [← hε, Matrix.mulVec_smul]
    convert h2 using 1
    funext k
    rw [colMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_xLast_last, Matrix.mul_assoc, hg0, cancel₂ dW.p0_j0,
      Matrix.one_mul, cancel₂ dW.p0_j0, Matrix.one_mul]
    rfl

theorem oneCoset_good : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ A L : HSp D) (σ : ℕ) (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (o : OrthDec W₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (p : Pieces V₀ W W₀ (σ + 1) σ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (LA : Lat A) (LL : Lat L) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xLast dW (vecB o ζ)) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → IsSelfDualC A LA → IsSelfDualC L LL → OrthAt o LW₀ LA LL v → ∀ h ∈ grpAt W (· = v), Cond dW p (xLast dW (vecB o ζ)) 0 ψ (· = v) h → CosetAt W (Rgrp W (xLast dW (vecB o ζ))) LW v h := by
  intro D ψ _ V V₀ W W₀ A L σ dV dW o ζ hζ p LV LV₀ LW LW₀ LA LL v hG hS hA hL hO h hh hC
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    GlobalTheory.IwaPlace.iwasawa_at_place D W W₀ σ dW LW LW₀ v (GlobalTheory.FinPl.TamePlaces.tame D v) hG.sdW hG.sdW₀ hG.monoW h hh
  have hn := flagN_mem_Rgrp dW (vecB o ζ) hnN
  rw [mul_assoc n] at hC
  obtain ⟨hK, hz⟩ := parts hG hS ht htG γ hn hκ hC
  obtain ⟨a, ha, k, hk, rfl⟩ := GlobalTheory.AscFin.OrbitAny.orbitAny D W₀ A L o ζ hζ LW₀ LA LL v hG.sdW₀ hA hL hO γ hγ hz
  refine ⟨n * dW.emb0 (o.emb (a, 1)), mul_mem hn (embA_mem_Rgrp dW o ζ a),
    mul_mem hnG (GlobalTheory.IwaPlace.wittCoreEmbedding_preserves_supportedUnitarySubgroup dW (GlobalTheory.FinPl.SplitOrbit.emb_mem_grpAt o ha)),
    dW.emb0 k * dW.levi t * κ, GlobalTheory.AscFin.inK_mul (GlobalTheory.AscFin.inK_mul (wittDec_embedding_preserves_latticeStabilizer dW hG.monoW hk) hK) hκ, ?_⟩
  rw [mul_assoc n (dW.levi t), ← dW.wittHyperbolic_anisotropic_commute_levi _ t, map_mul]
  simp only [mul_assoc]

end GlobalTheory.AscFin.OneCosetFJ

end
