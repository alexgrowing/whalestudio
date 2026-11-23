import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfAnnihilatorMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastPrimSplit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q, q.pr_sec]

theorem mem_intAt_iff_pr (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  have he := (GlobalTheory.FinPl.FrameLat.e_mem_intAt q).2
  constructor
  · rintro ⟨-, h⟩
    constructor
    · rw [q.int_iff, q.sec_pr, RingHom.map_mul]
      exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he h
    · rw [q.int_iff, q.sec_pr, RingHom.map_mul]
      exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he ((GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 h)
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    rw [q.int_iff, q.sec_pr] at h1 h2
    rw [← GlobalTheory.FinPl.FrameLat.cA_int_iff, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj] at h2
    rw [← (GlobalTheory.FinPl.FrameLat.idem_iff q a).1 ha, add_mul, RingHom.map_add]
    exact add_mem h1 h2

theorem incAdj_yZero_apply {ρ : ℕ} (hρ : 0 < ρ) {S T T₀ : HSp D} (d : HypDec T T₀ ρ) (z : Fin S.rank → D.host.E)
    (a : AE D) (i : Fin T.rank) (l : Fin S.rank) :
    d.incAdj S (a • yZero S ρ z) i l =
      cA D a * incA D (D.host.xi0⁻¹ * d.e' i ⟨ρ - 1, by omega⟩ * (star z ᵥ* S.gram) l) := by
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp
  simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, Matrix.vecMul, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell, map_sum]
  rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [if_true, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  change incA D (d.e' i _) * (-incA D _ * (cA D a * -incA D (star (z m)) * incA D (S.gram m l))) =
    cA D a * (incA D _ * incA D (d.e' i _) * (incA D (star (z m)) * incA D (S.gram m l)))
  ring

theorem map_row {E : Type} [Field E] (f : E →+* k) {m n : Type} [Fintype m] (w : m → E) (M : Matrix m n E) (j : n) :
    ∑ l, f (w l) * f (M l j) = f ((w ᵥ* M) j) := by
  simp only [Matrix.vecMul, dotProduct, map_sum, RingHom.map_mul]

theorem row_core (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k)
    (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) :
    (fun l => q.pr (incA D ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l))) ᵥ* F₀.β =
      Pi.single (Sum.inr ()) (sc * (ofSplit q).hz B) := by
  set f := q.pr.comp (incA D) with hf
  funext t
  rcases t with t | ⟨⟨⟩⟩
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have h0 : (fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* B.o.iA.map f = 0 := by
      funext j
      refine (map_row f _ B.o.iA j).trans ?_
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, B.o.orth,
        Matrix.vecMul_zero, Pi.zero_apply, Pi.zero_apply, map_zero]
    have h1 : ((fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* (B.o.iA.map f * FA.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * F₀.β l (Sum.inl t) =
      ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * (B.o.iA.map f * FA.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.1 l t]
    rfl
  · rw [Pi.single_eq_same]
    have h0 : (star (vecB B.o B.ζ) ᵥ* B.V₀.gram) ⬝ᵥ vecB B.o B.ζ = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, B.o.isoB]
    change ∑ l, f _ * F₀.β l (Sum.inr ()) = sc * f (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)
    rw [← h0, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.2 l, RingHom.map_mul, mul_left_comm]
    rfl

theorem row_jac (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (hρ : 0 < ρ) (J : JacLev D ρ) {n' : Type} [Fintype n'] [DecidableEq n']
    (sc hh : k) (FW₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (2 * ρ)))
    (hFW : (ofSplit q).IsJacFrame J sc hh FW₀ FW) :
    (fun l => q.pr (incA D ((J.d.e'ᴴ * J.W.gram) ⟨ρ - 1, by omega⟩ l))) ᵥ* FW.β =
      Pi.single (Sum.inr ⟨ρ - 1, by omega⟩) (sc * (ofSplit q).xi) := by
  set f := q.pr.comp (incA D) with hf
  set i₀ : Fin ρ := ⟨ρ - 1, by omega⟩ with hi₀
  have hcol : ∀ {m : ℕ} (M : Matrix (Fin J.W.rank) (Fin m) D.host.E) (j : Fin m),
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * f (M l j) = f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun M j => by
    rw [Matrix.mul_apply (M := J.d.e'ᴴ * J.W.gram), map_sum]
    simp only [RingHom.map_mul]
  funext t
  rcases t with t | t
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have hz : J.d.e'ᴴ * J.W.gram * J.d.i₀ = 0 := by
      have := congrArg Matrix.conjTranspose J.d.i₀e'
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have h0 : (fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* J.d.i₀.map f = 0 := by
      funext j
      refine (hcol J.d.i₀ j).trans ?_
      rw [hz, Matrix.zero_apply, map_zero, Pi.zero_apply]
    have h1 : ((fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* (J.d.i₀.map f * FW₀.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inl t) =
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * (J.d.i₀.map f * FW₀.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hFW.2.1 l t]
    rfl
  · change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = _
    have hmul : ∀ (c : k) (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ),
        (∀ r, FW.β r (Sum.inr t) = c * f (M r j)) →
        ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = c * f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun c M j h => by
      rw [← hcol, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [h, mul_left_comm]
    by_cases ht : t.val < ρ
    · rw [hmul _ _ _ (hFW.2.2.1 ⟨t.val, ht⟩ t rfl), J.d.e'e]
      by_cases h2 : t.val = ρ - 1
      · have h3 : t = ⟨ρ - 1, by omega⟩ := Fin.ext h2
        have h4 : (⟨t.val, ht⟩ : Fin ρ) = i₀ := Fin.ext h2
        have h5 : ρ - (i₀ : ℕ) = 1 := by change ρ - (ρ - 1) = 1; omega
        rw [h4, Matrix.one_apply_eq, map_one, mul_one, h5, pow_one, h3, Pi.single_eq_same]
      · rw [Matrix.one_apply_ne fun h => h2 (congrArg Fin.val h).symm, map_zero, mul_zero,
          Pi.single_eq_of_ne fun h => h2 (congrArg Fin.val (Sum.inr_injective h))]
    · have h6 := t.2
      rw [hmul _ _ _ (hFW.2.2.2 ⟨2 * ρ - 1 - t.val, by omega⟩ t (by change t.val + (2 * ρ - 1 - t.val) + 1 = _; omega)),
        J.d.e'e', Matrix.zero_apply, map_zero, mul_zero, Pi.single_eq_of_ne fun h => ht (by
          have h7 : t.val = ρ - 1 := congrArg Fin.val (Sum.inr_injective h)
          omega)]

end GlobalTheory.LastPrimSplit

end
