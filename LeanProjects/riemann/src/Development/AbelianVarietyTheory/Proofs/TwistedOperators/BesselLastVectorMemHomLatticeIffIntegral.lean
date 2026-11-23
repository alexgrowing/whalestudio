import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.RowShape.LastBF

open GlobalTheory.GoodPos GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mem_completedHomLattice_iff_selfDual_source {S T : HSp D} {LS : Lat S} (LT : Lat T) (hS : IsSelfDualC S LS) (P : Pl D → Prop) (u : WO S T) :
    u ∈ latO S T (LS : Set _) (LT : Set _) P ↔
      MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  refine ⟨fun hu => ⟨latO_mxAt hu, fun y hy => latO_maps hS hu hy⟩, fun ⟨hP, hmap⟩ => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := exists_dualBasis S hS
  let yv : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)
  have hyv : ∀ i, yv i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨indP D.host.F P, indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hu : u = ∑ i, rowMul S T (s' i) (u *ᵥ yv i) := by
    ext k j
    simp only [Matrix.sum_apply, rowMul, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, yv]
    simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← TensorProduct.tmul_sum, hdual]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; exact (mul_indP (hP k j)).symm
    · intro l _ hl; rw [if_neg hl, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hu]
  exact sum_mem fun i _ => rowMul_mem (hs' i) (hmap _ (hyv i))

theorem last_of_line {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} (LW : Lat W)
    (hM : IsSelfDualC V₀ M) {x : Pl D} {m : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hW : ∀ t ∈ idAt D (· = x), colMul d.jY r t ∈ latA W LW (· = x) ↔
      incA D D.host.xi0 * cA D (m : AE D) * t ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [mem_completedHomLattice_iff_selfDual_source LW hM, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hW _ (Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.LocSD.hermAt_mem_idAt (hsd.1 y hy) _)),
    ← herm_conj V₀ y (((m : AE D) * a) • ratV z), int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1]
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D m * GlobalTheory.IwaPlace.hermAt V₀ y (a • ratV z)) * e3

theorem const_mem_latPi {S : HSp D} (i₀ : Fin S.rank) (I : FI D) (v : Pl D) (s : AE D) :
    (fun _ => s) ∈ latV S (latPi S I) (· = v) ↔ s ∈ idV I v := by
  constructor
  · intro hy
    have key : ∀ y ∈ latV S (latPi S I) (· = v), y i₀ ∈ idV I v := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, a, rfl, z, hz, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨α, hα, h0, z i₀, mem_latPi.1 hz i₀, by simp only [one_mul]⟩
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | neg a _ ha => exact neg_mem ha
    exact key _ hy
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, z, hz, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, fun _ => z, mem_latPi.2 fun _ => hz,
        funext fun i => by rw [one_mul]⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha

theorem AA_mul_rowId (j τ : ℕ) (hj : j + 2 * (τ + 1) + 2 = D.R.m) (p : Fin (D.R.m - 1 - (j + 1))) (hp : p.1 = τ + 1) :
    D.host.AA * rowId D (j + 1) p = FractionalIdeal.spanSingleton _ (star (D.host.xi0 ^ τ)) * lineId D j := by
  have hodd : Odd (j + 1) := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - τ - 2, by omega⟩
  unfold rowId tiltSc lineId stairId
  rw [if_pos hodd, if_neg (by omega), show D.R.m - 1 - (j + 1) - 1 - p.1 = τ by omega,
    show D.R.m - 1 - (j + 1) - p.1 = τ + 1 by omega, show (D.R.m - 2 - j) / 2 = τ + 1 by omega, hp,
    pow_succ D.host.AA (τ + 1)]
  ring

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem last_rowN (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) (hσ : 0 < σ) :
    ∀ a ∈ idAt D (· = v),
    (rowJac G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (G.V (.grid D.R.m (j + 1)))
        (coreL G j : Set _) (rowN G (j + 1) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  obtain ⟨τ, rfl⟩ : ∃ τ, σ = τ + 1 := ⟨σ - 1, by omega⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hL : IsSelfDualC _ (lineL D j) :=
    isSelfDualC_latPi (GlobalTheory.RowShape.nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (G.Λ (.top j)) :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  have hM : IsSelfDualC _ (coreL G j) := GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL
  have ho : OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (coreL G j) (G.Λ (.top j)) (lineL D j) v := GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v (lineId D j) (lineId_ne_zero D j)
  have hx : D.host.xi0 ^ (τ + 1) ≠ 0 := pow_ne_zero _ hξ
  have hm0 : g * (D.host.xi0 ^ (τ + 1))⁻¹ ≠ 0 := mul_ne_zero hg (inv_ne_zero hx)
  have hline : ∀ a ∈ idAt D (· = v),
      a • ratV (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ∈
        latV (GlobalTheory.SeeSaw.Model.nLine D) (lineL D j) (· = v) ↔
      (((inU _ hm0)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = v) := fun a ha => by
    refine (const_mem_latPi (S := GlobalTheory.SeeSaw.Model.nLine D) (0 : Fin 1) (lineId D j) v
      (a * incA D (D.host.xi0 ^ (τ + 1)))).trans ?_
    rw [hgen, and_iff_left (Ideal.mul_mem_right _ _ ha), inU_inv, mul_inv, inv_inv, RingHom.map_mul, mul_assoc, mul_comm a]
  have hU := line_norm (GlobalTheory.SeeSaw.Model.isLineVec_nLine hx) hL hline
  have hN : star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ⬝ᵥ
      (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => D.host.xi0 ^ (τ + 1)) =
      -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) := by
    rw [GlobalTheory.RowShape.nLine_gram, neg_mulVec, one_mulVec, dotProduct_neg]
    exact congrArg Neg.neg (Fin.sum_univ_one (fun _ : Fin 1 => star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)))
  rw [hN] at hU
  refine last_of_line _ _ _ hM (m := inU _ hm0) (Fin.last τ) rfl (fun t ht => ?_)
    (fun a ha => (orth_line _ ho _ a).symm.trans (hline a ha))
  have hc : colMul (rowJac G (j + 1) (by omega) (τ + 1) (by omega)).jY (Fin.last τ) t =
      fun k => t * incA D ((G.rowDec (j + 1) (by omega)).a k
        (Fin.castLE (by omega : τ + 1 ≤ D.R.m - 1 - (j + 1)) (Fin.last τ)).rev) := by
    funext k
    rfl
  have hs : star (D.host.xi0 ^ τ) ≠ 0 := star_ne_zero.2 (pow_ne_zero _ hξ)
  rw [hc, rowN, dif_pos (by omega), (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2,
    AA_mul_rowId j τ hj _ (by simp only [Fin.val_rev, Fin.val_castLE, Fin.val_last]; omega),
    idV_spanSingleton_mul_iff D v _ _ hs t, and_iff_left ht, hgen, and_iff_left (Ideal.mul_mem_left _ _ ht),
    hU _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ht)), inU_val]
  have e : g * (D.host.xi0 ^ (τ + 1))⁻¹ * -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) *
      (g⁻¹ * (star (D.host.xi0 ^ τ))⁻¹) = D.host.xi0 := by
    rw [pow_succ D.host.xi0 τ, star_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    have := pow_ne_zero τ hξ
    field_simp
  have e' := congrArg (incA D) e
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul (incA D) g⁻¹] at e'
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D (incA D (g * (D.host.xi0 ^ (τ + 1))⁻¹)) * t) * e'

end GlobalTheory.RowShape.LastBF

theorem GlobalTheory.RowShape.big_last_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj v hσ =>
    GlobalTheory.RowShape.LastBF.last_rowN ch.G j σ hj v hσ⟩⟩

end
