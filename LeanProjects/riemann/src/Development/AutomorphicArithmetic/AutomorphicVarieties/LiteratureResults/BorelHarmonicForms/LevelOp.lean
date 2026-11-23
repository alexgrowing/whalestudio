import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AvgProj
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem op_comm {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (k : GL (Fin a) (Af E)) (o : Op E a) (ho : ∀ k', o ≠ .fin k') : Commute (π.op o) (π.finPart k) := by
  have h : act o * act (.fin k) = act (.fin k) * act o := by
    cases o with
    | fin k' => exact (ho k' rfl).elim
    | cpt u =>
      change rt E a _ * rt E a _ = rt E a _ * rt E a _
      rw [← map_mul, ← map_mul]
      exact congrArg _ (infGL_comm _ _)
    | lie X => exact lie_rt_fin X k
  exact LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h x.1)

theorem UpperTheory.V.Lit.Bor.levelOp :
    UpperTheory.V.Lit.Bor.LevelOp := by
  intro E _ _ _ a U hU π hF φ hφ
  obtain ⟨p, hp1, hp2, hp3⟩ := UpperTheory.V.Lit.Bor.avgProj _ _ π.finPart U hU π.isSmooth_finPart
  have hc : ∀ (o : Op E a), (∀ k', o ≠ .fin k') → ∀ g, Commute (p * π.finPart g) (π.op o) := fun o ho g =>
    ((hp3 _ fun u _ => op_comm π u o ho).mul_right (op_comm π g o ho)).symm
  by_contra hne
  have hφ0 : ∀ g, (p * π.finPart g) φ = 0 := fun g => by
    by_contra h
    exact hne ⟨p * π.finPart g, h, fun k => hc _ (fun _ h => by cases h) g, fun ψ u hu => hp1 _ u hu⟩
  set N : Submodule ℂ π.V := ⨅ g, LinearMap.ker (p * π.finPart g) with hN
  have hm : ∀ x, x ∈ N ↔ ∀ g, (p * π.finPart g) x = 0 := fun x => by simp only [hN, Submodule.mem_iInf, LinearMap.mem_ker]
  have hs : ∀ o, ∀ x ∈ N, π.op o x ∈ N := fun o x hx => by
    rw [hm] at hx ⊢
    intro g
    by_cases ho : ∀ k', o ≠ .fin k'
    · have := LinearMap.congr_fun (hc o ho g).eq x
      rw [Module.End.mul_apply, Module.End.mul_apply (π.op o), hx g, map_zero] at this
      exact this
    · push Not at ho
      obtain ⟨k, rfl⟩ := ho
      have := hx (g * k)
      rw [map_mul] at this
      exact this
  rcases π.irred (N.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hs o x hx, rfl⟩) with e | e
  · have : φ.1 ∈ N.map π.V.subtype := ⟨φ, (hm φ).2 hφ0, rfl⟩
    rw [e, Submodule.mem_bot] at this
    exact hφ (Subtype.ext this)
  · obtain ⟨v, hv0, hv⟩ := hF
    have : v.1 ∈ N.map π.V.subtype := by rw [e]; exact v.2
    obtain ⟨w, hw, hwv⟩ := this
    obtain rfl : w = v := Subtype.ext hwv
    have h1 := (hm w).1 hw 1
    rw [map_one, mul_one, hp2 w hv] at h1
    exact hv0 h1
