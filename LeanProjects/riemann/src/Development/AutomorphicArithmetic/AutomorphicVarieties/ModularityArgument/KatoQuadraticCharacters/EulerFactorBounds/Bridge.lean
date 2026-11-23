import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.GalAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ValCast
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OrbitSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

private theorem cgr_solve {K : Type} [Field K] {m : ℕ} {f a b c d : Kˣ} (h : Cgr m f (a * b)) (h' : Cgr m f (c * d)) :
    Cgr m b (c * d / a) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  refine ⟨k' / k, ?_⟩
  rw [div_pow, div_mul_div_comm, ← hk', hk, eq_div_iff_mul_eq', mul_assoc, mul_left_comm]

theorem sBridge : SBridge := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy u hu z β hβ hz A _ _ π
  obtain ⟨eqv, hadd, -, hsum, -, -, hgal, -, -, hmul, -⟩ := sApi Ω ε X l n
  obtain ⟨-, iadd, -, -, isum, -⟩ := sInvApi Ω ε X l N w n
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcyc := (sSlD Ω ε X N hN).2.2.2.2.2.2.2 M
  have cmul : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM M (s * t) = cycM M s * cycM M t := fun s t => (hcyc s).2.1 t
  have crep : ∀ t, cycM M (repM M t : Ω ≃ₐ[ℚ] Ω) = t := (hcyc 1).2.2.1
  have cfix : ∀ s : Ω ≃ₐ[ℚ] Ω, s ∈ fixMu Ω M ↔ cycM M s = 1 := fun s => (hcyc s).2.2.2.1
  have hM := sXiMul Ω ε X l n N M₀ M w g hL x y hxy
  have hT := sXiTw Ω ε X l n N M₀ M w g hL x y
  have hI := sXiInv Ω ε X l n N M₀ M w g hL hW x y hxy
  let B : (ZMod M)ˣ → X.Fn l := fun t =>
    Xi X l n N M₀ M w g x y (fun z => z = t) (u (repM M t)) + X.galB l (repM M t) β
  have hB : ∀ t, InvM X l N w n (B t) := fun t =>
    (iadd _ _ (hI _ _ (hu.eqv _)) (sGalAct Ω ε X l N w n hN _ β hβ).1).1
  have key : ∀ (s : Ω ≃ₐ[ℚ] Ω) (t : (ZMod M)ˣ), CgF X l n (shB X l M z s t)
      (Xi X l n N M₀ M w g x y (fun z => z = t) (u s) + (X.galB l s (B (t * (cycM M s)⁻¹)) - B t)) := by
    intro s t
    unfold shB
    simp only [B]
    generalize hτ : (repM M t : Ω ≃ₐ[ℚ] Ω) = τ
    generalize hτ' : (repM M (t * (cycM M s)⁻¹) : Ω ≃ₐ[ℚ] Ω) = τ'
    have c1 : cycM M τ = t := hτ ▸ crep _
    have c2 : cycM M τ' = t * (cycM M s)⁻¹ := hτ' ▸ crep _
    generalize hσ : τ⁻¹ * s * τ' = σ
    have e : τ * σ = s * τ' := by rw [← hσ]; group
    have hfix : σ ∈ fixMu Ω M := by
      rw [cfix]
      have h := congrArg (cycM M) e
      rw [cmul, cmul, c1, c2, mul_comm (cycM M s), inv_mul_cancel_right] at h
      exact mul_eq_left.1 h
    have h1 := hgal τ _ _ (hz σ hfix)
    rw [map_add, map_sub, ← hmul, e, hmul] at h1
    have h2 := hT (fun z => z = t) (u σ) τ
    have p2 : (fun z : (ZMod M)ˣ => z * cycM M τ = t) = fun z => z = 1 := by
      funext z
      rw [c1, mul_eq_right]
    rw [p2] at h2
    have h3 := (hM (fun z => z = t)).1 (tw X (l ^ n) M₀ τ (u σ)) (u s) (tw X (l ^ n) M₀ s (u τ')) (u τ)
      fun x y h => cgr_solve (hu.coc τ σ x y h) (e ▸ hu.coc s τ' x y h)
    have h4 := hT (fun z => z = t) (u τ') s
    have p4 : (fun z : (ZMod M)ˣ => z * cycM M s = t) = fun z => z = t * (cycM M s)⁻¹ := by
      funext z
      rw [eq_mul_inv_iff_mul_eq]
    rw [p4] at h4
    have h5 := eqv.trans (eqv.symm h2) (eqv.trans h3 (hadd _ _ _ _ (eqv.refl _) (hadd _ _ _ _ h4 (eqv.refl _)).2).1)
    have h6 := eqv.trans h1 (hadd _ _ _ _ h5 (eqv.refl _)).1
    convert h6 using 1
    rw [map_add]
    abel
  refine ⟨fun t => ∑ v ∈ Finset.univ.filter (fun v => π v = t), B v, fun t => isum _ _ _ fun v _ => hB v, fun s t => ?_⟩
  have h := hsum _ (Finset.univ.filter (fun v => π v = t)) _ _ fun v _ => key s v
  have r : ∑ v ∈ Finset.univ.filter (fun v => π v = t * (π (cycM M s))⁻¹), B v =
      ∑ v ∈ Finset.univ.filter (fun v => π v = t), B (v * (cycM M s)⁻¹) := by
    symm
    refine Finset.sum_equiv (Equiv.mulRight (cycM M s)⁻¹) (fun v => ?_) fun v _ => rfl
    simp
  beta_reduce
  rw [r, (hM (fun _ => True)).2.2.2 (u s) A π t, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact h

end UpperTheory.V.Z.Kato.Nb

end
