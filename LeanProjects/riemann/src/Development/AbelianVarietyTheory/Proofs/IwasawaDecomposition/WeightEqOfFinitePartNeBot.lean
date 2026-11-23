import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversalStatement

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem isIrreducible_sqRep (n : ℕ) (mu : DomWeight n) : (GlobalTheory.Branching.sqRep ℂ n mu).IsIrreducible := by
  have hU := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  obtain ⟨hn, hs⟩ := (CuspRep.isIrreducible_iff _).1 hU
  exact (CuspRep.isIrreducible_iff _).2 ⟨hn, fun S hS => hs S fun u => hS _⟩

theorem rhoK_tenMul {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (u : ∀ τ, nablaSq ℂ n (lam τ)) :
    Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam u) =
      GlobalTheory.CoefIrred.tenMul lam fun τ => GlobalTheory.Branching.sqRep ℂ n (lam τ) (g τ) (u τ) := by
  apply Subtype.ext
  rw [Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cAll_of_mem_embU {v u : InfinitePlace E} (huv : u ≠ v) {x : UA E n} (hx : x ∈ embU n v.embedding) :
    cAll x u = 1 := by
  have h := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h
  have h2 := h u.embedding
  rw [Subgroup.mem_iInf] at h2
  exact h2 (by simpa using huv)

theorem embU_le_infU (τ : E →+* ℂ) : embU n τ ≤ infU E n := inf_le_left

theorem rep_tenMul_update [DecidableEq (InfinitePlace E)] (W : Wt E n) (v : InfinitePlace E) (x : infU E n)
    (hx : x.1 ∈ embU n v.embedding) (e : ∀ u, nablaSq ℂ n (W u)) (a : nablaSq ℂ n (W v)) :
    W.rep x (GlobalTheory.CoefIrred.tenMul W (Function.update e v a)) =
      GlobalTheory.CoefIrred.tenMul W (Function.update e v (GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding x.1) a)) := by
  change Formalism.L2.DIV.rhoK W (cAll x.1) _ = _
  rw [rhoK_tenMul]
  congr 1
  funext u
  by_cases h : u = v
  · subst h
    simp only [Function.update_self]
    rfl
  · simp only [Function.update_of_ne h, cAll_of_mem_embU h hx, map_one, Module.End.one_apply]

theorem hasWeightAt_of_finPart (π : AutSub E n) (W : Wt E n) {f : algForms W} (hf : f ∈ π.finPart W) (hf0 : f ≠ 0)
    (v : InfinitePlace E) : HasWeightAt π.V v.embedding (W v) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, f.1 (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n W (UA E n → ℂ) 0).unique (y₁ := f.1) (y₂ := 0)
      (fun u => hc u) (fun u => rfl)
    exact hf0 (Subtype.ext h1)
  refine ⟨isIrreducible_sqRep n (W v), f.1 ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun a => ?_,
    fun x a => ?_⟩
  · have := LinearMap.congr_fun h0 (e v)
    simpa [MultilinearMap.toLinearMap] using this
  · exact AutSub.mem_finPart.1 hf _
  · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
    have h2 := f.2.2 ⟨x.1, hx⟩ (GlobalTheory.CoefIrred.tenMul W (Function.update e v a))
    rw [rep_tenMul_update W v ⟨x.1, hx⟩ x.2] at h2
    exact h2

end GlobalTheory.DefU

end
