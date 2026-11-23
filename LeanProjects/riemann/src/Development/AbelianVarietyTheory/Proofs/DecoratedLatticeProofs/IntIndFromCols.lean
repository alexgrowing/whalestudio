import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HatMemSBAndHatOmCol
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.LastTwoSteps
open GlobalTheory.StepData GlobalTheory.SymChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intInd_mem_SB (a b : Type) [Fintype a] [Fintype b] :
    Set.indicator {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) ∈ SB (Matrix a b k) := by
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : T2Space (Matrix a b k) := inferInstanceAs (T2Space (a → b → k))
  have e : {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} =
      Set.pi Set.univ fun _ : a => Set.pi Set.univ fun _ : b => (𝒪[k] : Set k) := by
    ext x; exact ⟨fun h r _ q _ => h r q, fun h r q => h r trivial q trivial⟩
  have hK : IsCompact {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have ho : IsOpen {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} := by
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have := GlobalTheory.FinPl.Comm.ite_mem_SB hK ho
  convert this using 1
  funext x
  by_cases h : ∀ r q, x r q ∈ 𝒪[k] <;> simp [Set.indicator_apply, h]

variable [MeasurableSpace k] [BorelSpace k]

theorem hat_const_mul {n : Type} [Fintype n] (ψ : AddChar k Circle) (ν : Measure k) (ε : k) (c : ℂ)
    (f : (n → k) → ℂ) (η : n → k) : hat ψ ν ε (fun y => c * f y) η = c * hat ψ ν ε f η := by
  simp only [hat, mul_assoc]
  rw [integral_const_mul]

open Classical in

theorem hat_int {n : Type} [Fintype n] [DecidableEq n] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k}
    (hν : IsUnitVol ν) {ε : k} (hε : valuation k ε = 1) (η : n → k) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0)) η = if ∀ i, η i ∈ 𝒪[k] then 1 else 0 := by
  classical
  have := hν.1
  have := secondCountable k
  split_ifs with hη
  · have hε' : ε ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, hε]
    rw [GlobalTheory.StepData.Model.hat_coset hψ hν hε' 0 hη]
    simp
  · have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
        cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0) (x + z) =
        cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0) x := fun z hz x => by
      have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
        (Submodule.Quotient.eq _).2 (by simpa using hz)
      simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
    refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
      (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
    · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

section Entries
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]

theorem psi_mem_SB (T : Chain k s X Z) (hT : T.Regular) (y : X (s + 1) → k) :
    (fun x₀ => T.Psi 1 x₀ y) ∈ SB (Matrix (X (s + 1)) (X s) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := X (s + 1)) (n' := X s)
  refine GlobalTheory.FinPl.Comm.comp_mem_SB (om_mem_SB (T.mu (s + 1)) 1 1 (hT.1 s 0 rfl))
    (p := fun x₀ => withCol x₀ y) (s := fun x => x.toBlocks₁₁) ?_ ?_ fun x => rfl
  · unfold withCol; fun_prop
  · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))

variable [MeasurableSpace k] [BorelSpace k]

theorem xiTop_mem_SB (T : Chain k s X Z) (hT : T.Regular) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) {ε : k} (hε : valuation k ε = 1) (yb : (X (s + 1) → k) ⧸ box (X (s + 1)) (1 : kˣ)) :
    T.xiTop (box _ (1 : kˣ)) ψ ν ε yb ∈ SB (Matrix (Z ⊕ Unit) (X (s + 1)) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z ⊕ Unit) (n' := X (s + 1))
  have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol k ψ ν ε hψ hν hε (X (s + 1)) 1 1 _ (cosetInd_mem_SB 1 yb)).1
  refine GlobalTheory.FinPl.Comm.prod_mem_SB hT.2.1 hh
    (p := fun x : Matrix (Z ⊕ Unit) (X (s + 1)) k => fromCols x.toRows₁ (0 : Matrix Z (Fin 0) k))
    (r := fun x => x (Sum.inr ()))
    (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
      · exact j.elim0
  · exact continuous_apply _
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases i with i | i
      · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
      · exact (continuous_apply j).comp continuous_snd
  · intro x; ext (i | i) j <;> rfl

end Entries

section Ones
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [Fintype c]

open Classical in

theorem cosetInd_zero (y : a → k) :
    cosetInd (box a (1 : kˣ)) (Submodule.Quotient.mk 0) y = if ∀ i, y i ∈ 𝒪[k] then 1 else 0 := by
  have hy : (Submodule.Quotient.mk y : (a → k) ⧸ box a (1 : kˣ)) = Submodule.Quotient.mk 0 ↔ ∀ i, y i ∈ 𝒪[k] := by
    simp [Submodule.Quotient.eq, mem_box, Valuation.mem_integer_iff]
  unfold cosetInd
  by_cases h : ∀ i, y i ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {y : a → k | Submodule.Quotient.mk y = Submodule.Quotient.mk 0}) (a := y)
      (hy.2 h), if_pos h]
  · rw [Set.indicator_of_notMem (s := {y : a → k | Submodule.Quotient.mk y = Submodule.Quotient.mk 0}) (a := y)
      (mt hy.1 h), if_neg h]

open Classical in

theorem intInd_fromCols (q : Matrix a b k) (y : a → k) :
    Set.indicator {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ))
        (fromCols q (Matrix.of fun r _ => y r)) =
      Set.indicator {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q *
        cosetInd (box a (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
  have hf : (∀ r c, fromCols q (Matrix.of fun r (_ : Unit) => y r) r c ∈ 𝒪[k]) ↔
      (∀ r c, q r c ∈ 𝒪[k]) ∧ ∀ i, y i ∈ 𝒪[k] := by
    constructor
    · intro h
      exact ⟨fun r c => by simpa using h r (Sum.inl c), fun r => by simpa using h r (Sum.inr ())⟩
    · rintro ⟨hq, hy⟩ r (c | c)
      · simpa using hq r c
      · simpa using hy r
  rw [cosetInd_zero]
  by_cases h : ∀ r c, fromCols q (Matrix.of fun r (_ : Unit) => y r) r c ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]}) (a := _) h,
      Set.indicator_of_mem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) (hf.1 h).1, if_pos (hf.1 h).2,
      mul_one]
  · rw [Set.indicator_of_notMem (s := {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]}) (a := _) h]
    by_cases hq : ∀ r c, q r c ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) hq,
        if_neg fun h2 => h (hf.2 ⟨hq, h2⟩), mul_zero]
    · rw [Set.indicator_of_notMem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) hq, zero_mul]

open Classical in

theorem intInd_rows (q : Matrix (c ⊕ Unit) a k) :
    Set.indicator {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q =
      Set.indicator {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q.toRows₁ *
        if ∀ i, q (Sum.inr ()) i ∈ 𝒪[k] then 1 else 0 := by
  have hr : (∀ r c, q r c ∈ 𝒪[k]) ↔ (∀ r c, q.toRows₁ r c ∈ 𝒪[k]) ∧ ∀ i, q (Sum.inr ()) i ∈ 𝒪[k] := by
    constructor
    · intro h
      exact ⟨fun r c => h (Sum.inl r) c, fun i => h (Sum.inr ()) i⟩
    · rintro ⟨hr, hη⟩ (r | r) c
      · exact hr r c
      · exact hη c
  by_cases h : ∀ r c, q r c ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) h,
      Set.indicator_of_mem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) (hr.1 h).1,
      if_pos (hr.1 h).2, mul_one]
  · rw [Set.indicator_of_notMem (s := {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) h]
    by_cases h1 : ∀ r c, q.toRows₁ r c ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) h1,
        if_neg fun h2 => h (hr.2 ⟨h1, h2⟩), mul_zero]
    · rw [Set.indicator_of_notMem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) h1, zero_mul]

end Ones

theorem gLast : ∀ (D : D7), LastLoc D → GlobalTheory.SymChain.AtMostOne → GLast D := by
  classical
  intro D hLL hAMO k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hstd hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz
    FA F₀ FS FT FX hcore hFX c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hΦ₁ hΦ₂ hO₁ hO₂
  have := hν.1
  obtain ⟨-, -, h1, h2, -⟩ := hAMO k ν hν s κ S t
  obtain ⟨Λ, hΛ, hK⟩ := hLL k p ν hν.1 ψ hstd S.ψ hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz _ _ _ FA F₀ FS FT FX
    hcore hFX T₁ T₂ hT₁ hT₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Φ₁ Φ₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁ O₂
  have hreg : (S.T t).Regular := Chain.ofType_regular _ _ _ _ _
  have hv1 : valuation k (-1 : k) = 1 := by simp
  let Ξ₁ : SB (Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) := ⟨_, psi_mem_SB _ hreg (S.y0 t)⟩
  let Ξ₂ : SB (Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) :=
    ⟨_, xiTop_mem_SB _ hreg S.cond hν hv1 (Submodule.Quotient.mk (S.y0 t))⟩
  let O₁' : SB (Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) := ⟨_, intInd_mem_SB _ _⟩
  let O₂' : SB (Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) := ⟨_, intInd_mem_SB _ _⟩
  have hcp : ∀ x₀ y, (S.T t).Psi 1 x₀ y =
      (S.T t).Psi 1 x₀ (S.y0 t) * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk (S.y0 t)) y := fun x₀ y => by
    by_cases hy : y - S.y0 t ∈ box _ (1 : kˣ)
    · rw [h2 x₀ y hy, cosetInd, Set.indicator_of_mem, mul_one]
      exact (Submodule.Quotient.eq _).2 hy
    · rw [cosetInd, Set.indicator_of_notMem, mul_zero]
      · exact not_not.1 (mt (h1 x₀ y) hy)
      · exact fun h => hy ((Submodule.Quotient.eq _).1 h)
  have hprod : ∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2 := fun q => by
    rw [hΞ q, hΦ₂]
    have e : (fun y => Φ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        (S.T t).Psi 1 q.1 (S.y0 t) * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk (S.y0 t)) y := by
      funext y
      rw [hΦ₁, ← hcp]
      rfl
    rw [e, hat_const_mul]
    show _ = (S.T t).Psi 1 q.1 (S.y0 t) * ((S.T t).PhiTop (fromCols q.2.toRows₁ 0) * _)
    ring
  have hone : ∀ q, Ξ'.1 q = O₁'.1 q.1 * O₂'.1 q.2 := fun q => by
    rw [hΞ' q, hO₂]
    have e : (fun y => O₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k | ∀ r q, x r q ∈ 𝒪[k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
      funext y
      rw [hO₁]
      exact intInd_fromCols q.1 y
    rw [e, hat_const_mul, hat_int S.cond hν hv1]
    simp only [O₁', O₂']
    rw [intInd_rows q.2]
    ring
  have key := (GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension D k p ψ _ _ _).1 B.A W X FA FS FX Λ c₁ c₂ Ξ₁ O₁' Ξ₂ O₂' Ξ Ξ' hΛ hc₁ hc₂ rfl rfl hprod hone
  have e1 := funext hΞK
  have e2 := funext hΞ'K
  rw [e1, e2]
  exact key

end GlobalTheory.LastTwoSteps
