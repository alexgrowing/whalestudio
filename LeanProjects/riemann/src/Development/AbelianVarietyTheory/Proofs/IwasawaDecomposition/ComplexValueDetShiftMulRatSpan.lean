import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerValRat

theorem lamTG_add_sSharp {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (lamTG M i τ).w r + (D.chTw u μ).sSharp i τ = (nuT D u i τ r : ℤ) := by
  obtain ⟨a, ha⟩ := D.R.t_odd
  have hc : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) = (i : ℝ) * ((a : ℝ) + 1) := by
    rw [ha, show i * (2 * a + 1 + 1) = 2 * (i * (a + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * a + 1 := by rw [ha]; push_cast; ring
  have h1 := congrArg (Rat.cast : ℚ → ℝ) (M.lam_eq i hi.le τ r)
  have h2 := congrArg (Rat.cast : ℚ → ℝ) ((D.chTw u μ).sSharp_eq i hi τ)
  have h3 := GlobalTheory.PdvKm.nuT_real u i hi τ r
  have he := D.hcW_e u τ
  suffices key : (((lamTG M i τ).w r : ℤ) : ℝ) + (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((nuT D u i τ r : ℕ) : ℝ) by
    exact_mod_cast key
  rw [h3]
  have e0 : (lamTG M i τ).w r = (M.lam i τ).w r - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) := rfl
  have hl : (((lamTG M i τ).w r : ℤ) : ℝ) = ((((M.lam i τ).w r : ℤ) : ℚ) : ℝ) - (i : ℝ) * ((a : ℝ) + 1) := by
    rw [e0, Int.cast_sub, Int.cast_natCast, hc, Rat.cast_intCast]
  have hs : (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((((D.chTw u μ).sSharp i τ : ℤ) : ℚ) : ℝ) := by rw [Rat.cast_intCast]
  rw [hl, hs, h1, h2]
  have hw : DV.wSz D (i + 1) τ = (((D.hcW u τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dif_pos ⟨by omega, by omega⟩, he]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar sExp' Ranks.N
  by_cases hk : r.1 < D.R.k
  · rw [dif_pos hk, dif_pos hk]
    unfold hcToWeightQ rhoVec
    push_cast
    rw [ht]
    ring
  · rw [dif_neg hk, dif_neg hk]
    have hr := r.2
    unfold Ranks.N at hr
    have hb : (r.1 - D.R.k) / (D.R.t + 1) < i := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact Nat.sub_lt_left_of_lt_add (by omega) hr
    have hbm : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by omega
    rw [dif_pos hbm]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hr' : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + ((D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1)) := by omega
      conv_lhs => rw [this]
      push_cast; ring
    unfold wG
    push_cast
    rw [hr', ht]
    ring

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem detShift_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    (lamTG M i τ).detShift = (nuT D u i τ (lastI D i) : ℤ) - (D.chTw u μ).sSharp i τ := by
  have h := lamTG_add_sSharp M μ i hi τ (lastI D i)
  unfold DomWeight.detShift
  rw [dif_pos (N_pos D i)]
  show (lamTG M i τ).w (lastI D i) = _
  omega

open GlobalTheory.PdvKm in
theorem natW_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (M.lam i τ).natW r = nuT D u i τ r - nuT D u i τ (lastI D i) := by
  have h0 : (M.lam i τ).natW r = (lamTG M i τ).natW r := by
    show _ = (Formalism.L2.Forms.shW (M.lam i τ) _).natW r
    rw [Formalism.L2.Forms.natW_shW]
  rw [h0]
  have h1 := lamTG_add_sSharp M D.what₂.mu0 i hi τ r
  have h2 := detShift_lamTG M D.what₂.mu0 i hi τ
  have hle : nuT D u i τ (lastI D i) ≤ nuT D u i τ r :=
    antitone_kernelChain_nuT D u i τ hi (show r ≤ lastI D i by rw [Fin.le_def]; simp only [lastI]; omega)
  unfold DomWeight.natW
  rw [h2]
  omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem evC_ratSpan_gen {D : D7} (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {A : ColumnsAtT D.R (D.chTw u μ)} {P : PeriodMap D.R (D.chTw u μ)}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) A P)
    (i : ℕ) (hi : i < D.R.m) (eY : (D.chTw u μ).Y i ≃ Fr D i hi.le)
    (hfrm : ∀ y, (O u μ).frm i y = (eY y).1) (v : ValQ O u μ i) :
    ∃ Q ∈ Formalism.L2.Forms.RatSpan D (M.lam i), ∀ z, evC O u μ i v z =
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) := by
  have hne : ∀ (z : (D.chTw u μ).Y i) τ, ((eY z).1 τ).det ≠ 0 := fun z τ => by
    rw [← hfrm z, ← (O u μ).frm_de i hi.le z τ]; exact (D.chTw u μ).de_ne i z τ
  have hev : ∀ z, evC O u μ i v z = (∏ τ, (((eY z).1 τ).det) ^ (-(twB D u μ i τ))) *
      MvPolynomial.eval₂ D.what₂.embLL (fun k => (eY z).1 k.1 k.2.1 k.2.2)
        (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) := by
    intro z
    rw [evC_sec]
    show (∏ τ, ((D.chTw u μ).de i z τ) ^ (-(twB D u μ i τ))) *
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i z) = _
    simp only [(O u μ).frm_de i hi.le z, hfrm z, evFr_map]
  have hfn : ∀ (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) z,
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) =
        (∏ τ, ((eY z).1 τ).det ^ (lamTG M i τ).detShift) * MvPolynomial.eval (fun x => (eY z).1 x.1 x.2.1 x.2.2) Q := by
    intro Q z
    show (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) τ * (eY z).1 τ).det ^ _) *
      MvPolynomial.eval (fun x => ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) x.1 * (eY z).1 x.1) x.2.1 x.2.2) Q = _
    simp only [Pi.one_apply, one_mul]
    rfl

  haveI hLL : Infinite D.what₂.LL := Infinite.of_injective (fun n : ℕ => (n : D.what₂.LL)) (fun a b h => by
    have := congrArg D.what₂.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hmem : (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) ∈ polV D u i := (secC O u μ i v).2
  rcases i with _ | j
  · have h0 : 0 < D.R.m := hi
    have hk : ∀ τ r, nuT D u 0 τ (lastI D 0) ≤ nuT D u 0 τ r := fun τ r =>
      antitone_kernelChain_nuT D u 0 τ h0 (show r ≤ lastI D 0 by rw [Fin.le_def]; simp only [lastI]; omega)
    obtain ⟨P0, hP0, hQe⟩ := frameWeightPolyDivByDet_proof D.what₂.LL D.what₂.Tau (D.R.N 0) (nuT D u 0) (fun τ => nuT D u 0 τ (lastI D 0)) hk _ hmem
    refine ⟨MvPolynomial.map D.what₂.embLL P0, GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam 0) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam 0 τ).natW r) = fun τ r => nuT D u 0 τ r - nuT D u 0 τ (lastI D 0) :=
        funext fun τ => funext fun r => natW_lamTG M 0 h0 τ r
      rw [e]; exact hP0
    · have hd : ∀ τ, MvPolynomial.eval₂ D.what₂.embLL (fun k : GL3Theta.FrV D (D.R.N 0) => (eY z).1 k.1 k.2.1 k.2.2)
          (frDet D.what₂.LL (D.R.N 0) τ) = ((eY z).1 τ).det := by
        intro τ
        rw [← MvPolynomial.eval_map, Formalism.L2.Ker.map_frDet, Formalism.L2.Ker.eval_frDet]
        rfl
      rw [hev, hfn, hQe, MvPolynomial.eval_map, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod]
      simp only [MvPolynomial.eval₂_pow, hd]
      have hs : ∀ τ, (lamTG M 0 τ).detShift = ((nuT D u 0 τ (lastI D 0) : ℕ) : ℤ) - twB D u μ 0 τ :=
        fun τ => detShift_lamTG M μ 0 h0 τ
      simp only [hs]
      rw [prod_zpow_split _ (hne z) _ (fun τ => nuT D u 0 τ (lastI D 0))]
      ring
  · have hj : j < D.R.m := by omega
    refine ⟨MvPolynomial.map D.what₂.embLL (secC O u μ (j + 1) v : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) D.what₂.LL),
      GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam (j + 1)) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam (j + 1) τ).natW r) = extNu (D.R.N (j + 1)) (nuT D u j) := by
        funext τ r
        rw [natW_lamTG M (j + 1) hi τ r, ← natW_succ (antitone_kernelChain_nuT D) u j hj τ r]
        have h1 := clause1 (antitone_kernelChain_nuT D) u (j + 1) hi τ r
        have h2 : nn D u (j + 1) τ = nuT D u (j + 1) τ (lastI D (j + 1)) := by unfold nn; rw [if_pos hi]
        omega
      rw [e]; exact hmem
    · rw [hev, hfn, MvPolynomial.eval_map]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      rw [detShift_lamTG M μ (j + 1) hi τ]
      have h1 := last_real u μ j hi τ
      show -((D.chTw u μ).sDiv j τ) = _
      have h2 : ((nuT D u (j + 1) τ (lastI D (j + 1)) : ℕ) : ℤ) = (D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ := by
        exact_mod_cast h1
      omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

theorem evC_ratSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ v : ValQ O u μ i, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, evC O u μ i v z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z) := by
  intro B X I hOk hPins l Z Y O hQ hS u μ i hi eY hId v
  exact evC_ratSpan_gen O u μ (I.fm l u μ) i hi eY (fun y => (hS.frm u μ i y).trans (hId y).symm) v

end GlobalTheory.KerValRat
