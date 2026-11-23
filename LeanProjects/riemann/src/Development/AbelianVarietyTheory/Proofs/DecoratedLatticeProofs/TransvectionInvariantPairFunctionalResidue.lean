import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

theorem latPair_hasVal_residue_of_transvections : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 2 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → ∃ ε : 𝓀[k], ε ≠ 0 ∧ ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]), P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * ε) := by
  intro k _ _ _ _ n _ _ i P c _hcard hc hlat hcl
  classical
  set e : n → (n → k) := fun b => c • (Pi.single b (1:k) : n → k) with he_def
  have hcoef : ∀ b j, c⁻¹ * e b j = (Pi.single b (1:k) : n → k) j := by
    intro b j
    by_cases h : j = b
    · subst h; simp [he_def, hc]
    · simp [he_def, Pi.single_apply, h]
  have hmem : ∀ b, e b ∈ P.lat := fun b => (hlat _).2 (fun j => by
    rw [hcoef]
    by_cases h : j = b
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_apply, h, if_false]; exact zero_mem _)
  let v : n → 𝓀[k] := fun b => P.fn ⟨e b, hmem b⟩
  have hv : ∀ b, P.HasVal (e b) (v b) := fun b => P.hasVal_fn ⟨e b, hmem b⟩
  have hzero : ∀ a, a ≠ i → v a = 0 := by
    intro a ha
    have h1 := hcl (e i) (v i) (hv i) a i 1 ha (Or.inl ha)
    have h2 : e i + Pi.single a (((1:𝒪[k]) : k) * e i i) = e i + e a := by
      congr 1
      funext j
      by_cases h : j = a
      · subst h; simp [he_def]
      · simp [he_def, Pi.single_apply, h]
    rw [h2] at h1
    have h3 := h1.sub (hv i)
    rw [add_sub_cancel_left, sub_self] at h3
    exact (hv a).unique h3
  have hsum : ∀ (s : n → 𝒪[k]) (S : Finset n),
      P.HasVal (∑ b ∈ S, s b • e b) (∑ b ∈ S, IsLocalRing.residue 𝒪[k] (s b) * v b) := by
    intro s S
    induction S using Finset.induction_on with
    | empty => simpa using (hv i).sub (hv i)
    | insert b S hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      exact ((hv b).smul (s b)).add ih
  have hval : ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]),
      P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * v i) := by
    intro x hx
    let s : n → 𝒪[k] := fun b => ⟨c⁻¹ * x b, hx b⟩
    have hx' : (∑ b, s b • e b) = x := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · change ((s j : 𝒪[k]) : k) * (c * (Pi.single j (1:k) : n → k) j) = x j
        simp only [s, Pi.single_eq_same, mul_one]
        field_simp
      · intro b _ hb
        change ((s b : 𝒪[k]) : k) * (c * (Pi.single b (1:k) : n → k) j) = 0
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    have := hsum s Finset.univ
    rw [hx', Finset.sum_eq_single i (fun b _ hb => by rw [hzero b hb, mul_zero]) (by simp)] at this
    exact this
  refine ⟨v i, ?_, hval⟩
  intro h0
  apply P.fn_ne
  refine LinearMap.ext fun y => ?_
  have := hval y ((hlat y).1 y.2)
  rw [h0, mul_zero] at this
  exact (P.hasVal_fn y).unique this

end GlobalTheory
