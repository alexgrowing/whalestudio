import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
import Formalism.LocalToGlobal.InertKernelTheory.K2OfAgreements
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove

noncomputable section

namespace GlobalTheory.FormsSharpTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.KerInert.K2

theorem natW_antitone {n : ℕ} (l : DomWeight n) : Antitone l.natW := by
  intro a b h
  simp only [DomWeight.natW]
  exact Int.toNat_le_toNat (by have := l.anti h; omega)

theorem ratSpan_le_wtPol (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) :
    ∀ P ∈ RatSpan D lam, P ∈ WtPol ℂ (fun τ r => (lam τ).natW r) := by
  intro P hP
  have hle : RatSpan D lam ≤ (WtPol ℂ (fun τ r => (lam τ).natW r)).toAddSubgroup := by
    unfold RatSpan
    rw [AddSubgroup.closure_le]
    rintro p ⟨r, f, hf, rfl⟩
    show _ ∈ WtPol ℂ _
    apply Submodule.smul_mem
    apply GlobalTheory.KerWt.VV_le_WtPol lam
    unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
    apply Submodule.subset_span
    refine ⟨fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ), fun τ => ?_, rfl⟩
    have h1 : MvPolynomial.map (Int.castRingHom ℂ) (f τ) ∈ delSq ℂ n (lam τ) := by
      rw [← GlobalTheory.Published.span_map_delSq ℤ ℂ (Int.castRingHom ℂ) n (lam τ)]
      exact Submodule.subset_span ⟨f τ, hf τ, rfl⟩
    exact Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ (natW_antitone (lam τ)) h1
  exact hle hP

theorem eval_colSub {ι : Type} [Fintype ι] {a : ℕ} (β x : ι → Matrix (Fin a) (Fin a) ℂ) (p : Formalism.L2.DIV.Pol ℂ ι a) :
    MvPolynomial.eval (fun k : ι × Fin a × Fin a => x k.1 k.2.1 k.2.2) (colSub β p) =
      MvPolynomial.eval (fun k : ι × Fin a × Fin a => (x k.1 * β k.1) k.2.1 k.2.2) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, colSub, MvPolynomial.aeval_X, MvPolynomial.eval_X, Matrix.mul_apply]
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [mul_comm]

theorem zpow_mul_pow_toNat {x : ℂ} (hx : x ≠ 0) (s : ℤ) : x ^ s * x ^ (-s).toNat = x ^ s.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  omega

theorem isVLam_of_wtPol {ι : Type} [Fintype ι] {a : ℕ} {Y : Type} (fr g : Y → ι → Matrix (Fin a) (Fin a) ℂ)
    (B : ι → Matrix (Fin a) (Fin a) ℂ) (hB : ∀ τ, (B τ).det ≠ 0) (hg : ∀ y τ, (g y τ).det ≠ 0)
    (hfr : ∀ y τ, fr y τ = B τ * g y τ) (ν : ι → Fin a → ℕ) (s : ι → ℤ) (P : Formalism.L2.DIV.Pol ℂ ι a)
    (hP : P ∈ WtPol ℂ ν) :
    IsVLam fr (fun τ r => (ν τ r : ℤ) + s τ)
      (fun y => (∏ τ, (g y τ).det ^ s τ) * MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y x.1 x.2.1 x.2.2) P) := by
  have hBu : ∀ τ, IsUnit (B τ).det := fun τ => isUnit_iff_ne_zero.2 (hB τ)
  have hg' : ∀ y τ, g y τ = (B τ)⁻¹ * fr y τ := by
    intro y τ
    rw [hfr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hBu τ), Matrix.one_mul]
  refine ⟨?_, ?_⟩
  ·
    let sub : Formalism.L2.DIV.Pol ℂ ι a →ₐ[ℂ] Formalism.L2.DIV.Pol ℂ ι a :=
      MvPolynomial.aeval fun v => ∑ c, MvPolynomial.C ((B v.1)⁻¹ v.2.1 c) * MvPolynomial.X (v.1, c, v.2.2)
    have hsub : ∀ y (p : Formalism.L2.DIV.Pol ℂ ι a), MvPolynomial.eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (sub p) =
        MvPolynomial.eval (fun k : ι × Fin a × Fin a => g y k.1 k.2.1 k.2.2) p := by
      intro y p
      induction p using MvPolynomial.induction_on with
      | C c => simp [sub]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p v hp =>
        simp only [map_mul, hp, sub, MvPolynomial.aeval_X, MvPolynomial.eval_X, hg', Matrix.mul_apply, map_sum]
        simp
    have hdet : ∀ y τ, MvPolynomial.eval (fun k : ι × Fin a × Fin a => g y k.1 k.2.1 k.2.2) (frDet ℂ a τ) = (g y τ).det := by
      intro y τ
      unfold frDet
      rw [RingHom.map_det]
      congr 1
      ext i k
      simp
    refine ⟨MvPolynomial.C (∏ τ, (B τ).det ^ (-s τ).toNat) * (∏ τ, sub (frDet ℂ a τ) ^ (s τ).toNat) * sub P,
      fun τ => (-s τ).toNat, fun y => ?_⟩
    simp only [frPolyG, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_prod, map_pow, MvPolynomial.eval_C, hsub, hdet]
    have e2 : ∀ τ, (g y τ).det ^ s τ * (g y τ).det ^ (-s τ).toNat = (g y τ).det ^ (s τ).toNat :=
      fun τ => zpow_mul_pow_toNat (hg y τ) (s τ)
    simp only [hfr, Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]
    rw [← Finset.prod_congr rfl fun τ _ => e2 τ, Finset.prod_mul_distrib]
    ring
  ·
    intro y y₂ β hβ hy
    have hgy : ∀ τ, g y₂ τ = g y τ * β τ := by
      intro τ
      have h := hy τ
      rw [hfr, hfr, Matrix.mul_assoc] at h
      have h2 := congrArg (fun M => (B τ)⁻¹ * M) h
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hBu τ), Matrix.one_mul] at h2
      exact h2
    have hdβ : ∀ τ, (β τ).det = ∏ r, β τ r r := fun τ =>
      Matrix.det_of_upperTriangular (fun r s h => (hβ τ).1 r s h)
    have hev : MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y₂ x.1 x.2.1 x.2.2) P =
        (∏ τ, ∏ r, β τ r r ^ ν τ r) * MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y x.1 x.2.1 x.2.2) P := by
      have := eval_colSub β (g y) P
      rw [hP β hβ, MvPolynomial.smul_eval] at this
      simp only [hgy]
      rw [← this]
    have hne : ∀ τ r, β τ r r ≠ 0 := fun τ r => (hβ τ).2 r
    have e3 : ∀ τ r, β τ r r ^ ((ν τ r : ℤ) + s τ) = β τ r r ^ ν τ r * β τ r r ^ s τ := by
      intro τ r
      rw [zpow_add₀ (hne τ r), zpow_natCast]
    dsimp only
    rw [hev]
    simp only [hgy, Matrix.det_mul, hdβ, mul_zpow, e3, Finset.prod_mul_distrib, ← Finset.prod_zpow]
    ring

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset in

theorem sharpWt_rat (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) :
    ((((nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ : ℤ)) : ℚ) =
        ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
  have h1 := (GlobalTheory.KerWt.nu_t_identity D u j hj τ r).1
  have h2 := (D.chTw u μ).sSharp_eq j hj τ
  have h3 := (Tw.fm u μ).lam_eq j hj.le τ r
  have h2' : (((D.chTw u μ).sSharp j τ : ℤ) : ℝ) =
      (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) + ((j : ℝ) + 1) * ((D.R.t : ℝ) + 1)) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h2
    simp only [sExp', Ranks.N] at this
    push_cast at this
    exact this
  have he : ∀ (k : ℕ) (hk : k < D.R.m), k = j → (D.hc τ).e ⟨k, hk⟩ = (D.hcW u τ).e ⟨j, hj⟩ := by
    rintro k hk rfl; rw [D.hcW_e]
  apply Rat.cast_injective (α := ℝ)
  have hw : ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℝ) = (((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  push_cast
  rw [h1, h2', hw, h3]
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dif_pos (show 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m by omega), he _ _ (by omega)]
  simp only [Ranks.N]
  by_cases hr : r.1 < D.R.k
  · rw [dif_pos hr, dif_pos hr]
    simp only [hcToWeightQ, rhoVec]
    push_cast
    ring
  · have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by
      have := D.R.blk_lt hj.le r hr
      omega
    rw [dif_neg hr, dif_neg hr, dif_pos hb]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hrk : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + (D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1) := by omega
      exact_mod_cast this
    simp only [wG]
    push_cast
    rw [hrk]
    ring

theorem nuT_sub_sSharp (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) :
    (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ = (lamTG (Tw.fm u μ) j τ).w r := by
  have h := sharpWt_rat D Tw u μ j hj τ r
  set z : ℤ := (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ with hz
  set w : ℤ := ((Tw.fm u μ).lam j τ).w r with hw
  show z = ((Tw.fm u μ).lam j τ).w r - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)
  rw [← hw]
  generalize hn : j * (D.R.t + 1) = n
  have h2 : (2 * (w - z) : ℚ) = (n : ℚ) := by
    rw [← hn]; push_cast; rw [h]; ring
  have h3 : 2 * (w - z) = (n : ℤ) := by exact_mod_cast h2
  omega

theorem natW_add_shift {N : ℕ} (l : DomWeight N) (c : ℤ) (r : Fin N) :
    ((l.natW r : ℕ) : ℤ) + (shW l c).detShift = (shW l c).w r := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) r.2
  have hle : l.w ⟨N - 1, by omega⟩ ≤ l.w r := l.anti (show r ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
  simp only [DomWeight.natW, DomWeight.detShift, shW, dif_pos hN]
  rw [Int.toNat_of_nonneg (by omega)]
  ring

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem formsSharpAt_of_valTied (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    {T : ℕ} {bad : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F))}
    {eY : (D.chTw u μ).Y j ≃ Fr D j hj.le} {okW : D.what₂.places.Pl → Prop} {Ch : Type} {chOf : (D.chTw u μ).cls j → Ch}
    {lat : (D.chTw u μ).cls j → Submodule (NumberField.RingOfIntegers D.host.E) (Fin (D.R.N j) → D.host.E)}
    {K : ∀ β : Ch, LevelChart D T bad j hj.le (fun c : {c // chOf c = β} => (D.chTw u μ).stab j c.1) (fun c => lat c.1)}
    (hV : ValuationCompatibleChart (ex.tw.fm u μ) eY okW chOf K) (crd : GL (Fin (D.R.N j)) D.host.E)
    (hfrm : ∀ y τ, (t.O u μ).frm j y τ = atInf (embT D) crd.1 τ * (eY y).1 τ) :
    ∀ x, ∃ Q, SharpQ t ex.tw u μ j x Q := by
  intro x
  have hx := (hV.rat ((ex.tw.fm u μ).emb j x)).1 ⟨x, rfl⟩
  choose P hP hE using hx.2
  have hB : ∀ τ, (atInf (embT D) crd.1 τ).det ≠ 0 := by
    intro τ
    show ((crd : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ)).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Matrix.isUnits_det_units crd).ne_zero
  have hg : ∀ y τ, ((eY y).1 τ).det ≠ 0 := fun y τ => ((eY y).2 τ).ne_zero
  have key : ∀ c, IsVLam ((t.O u μ).frm j) (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ)
      ((ex.tw.fm u μ).emb j x c) := by
    intro c
    have h1 := isVLam_of_wtPol ((t.O u μ).frm j) (fun y => (eY y).1) (fun τ => atInf (embT D) crd.1 τ) hB hg hfrm
      (fun τ r => ((ex.tw.fm u μ).lam j τ).natW r) (shiftOf (lamTG (ex.tw.fm u μ) j)) (P c)
      (ratSpan_le_wtPol D _ (P c) (hP c))
    have hw : (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ) =
        (fun τ r => ((((ex.tw.fm u μ).lam j τ).natW r : ℕ) : ℤ) + shiftOf (lamTG (ex.tw.fm u μ) j) τ) := by
      funext τ r
      rw [nuT_sub_sSharp D ex.tw u μ j hj τ r]
      exact (natW_add_shift _ _ r).symm
    have hf : (ex.tw.fm u μ).emb j x c = fun y => (∏ τ, ((eY y).1 τ).det ^ shiftOf (lamTG (ex.tw.fm u μ) j) τ) *
        MvPolynomial.eval (fun k : D.what₂.Tau × Fin (D.R.N j) × Fin (D.R.N j) => (eY y).1 k.1 k.2.1 k.2.2) (P c) := by
      funext y
      rw [hE c y]
      simp [fnOf]
    rw [hw, hf]
    exact h1
  have := fun c => forms_sharp_description Formalism.L2.KerInert.SharpPolyP.sharp_polynomial_frames D u (D.chTw u μ) (t.O u μ) j hj.le
    (nuT D u j) _ (key c)
  choose Q hQ hQE using this
  exact ⟨Q, hQ, hQE⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem formsSharpAt_of_pins (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ)
    (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (hP : GlobalTheory.TwU.AdPins A dtU)
    (okW : ℕ → D.what₂.places.Pl → Prop)
    (hV : ∀ j (hj : j < D.R.m), ValuationCompatibleChart (ex.tw.fm u μ) (St j hj.le).eY (okW j) (St j hj.le).chOf (St j hj.le).K) :
    ∀ j, j < D.R.m → ∀ x, ∃ Q, SharpQ t ex.tw u μ j x Q :=
  fun j hj => formsSharpAt_of_valTied t u μ j hj (hV j hj) (A.crd j hj.le) (hP.frm j hj.le)

end GlobalTheory.FormsSharpTie
