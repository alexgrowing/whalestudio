import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar

open scoped TensorProduct

namespace GlobalTheory.EvaluationSum

open GlobalTheory.SeriesTie

theorem evK_eq_sum {D : Formalism.BasicNotions.D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Γ Pl0 I0 (List Nat) T (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D))]
    {Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks}
    {cG : MulEquiv (Formalism.L2.DIV.G0 (Formalism.IndefR.Links.LevCh.Pg (Formalism.IndefR.Links.RealDat.toLevCh (Formalism.IndefR.Links.RealDat3.toRealDat Rl))) (Formalism.BasicNotions.Ranks.r (Formalism.BasicNotions.D7.R D))) (Formalism.BasicNotions.G0g (Formalism.BasicNotions.D7.nd D))}
    {S : Formalism.IndefR.NX.RatDat (Formalism.BasicNotions.D7.ntw D)} (YS : Formalism.IndefR.NX.NExpRealS Rl cG S)
    (v₀ : (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) → (σ : RingHom (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Complex) → Formalism.IndefR.Mult.DSModel.Vec (Formalism.IndefR.Links.RealDat.MW (Formalism.IndefR.Links.RealDat3.toRealDat Rl) j σ))
    {ρ : GlobalTheory.SeriesTie.Setup (Formalism.BasicNotions.D7.ntw D)} (hρ : GlobalTheory.SeriesTie.Setup.Good ρ)
    (i : Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool)
    (t : TensorProduct (Formalism.IndefR.NX.RatDat.Ks S) (Formalism.IndefR.NX.KB S i b) (Formalism.IndefR.NX.FmK S ((j : ℕ) + 1))) :
    ∃ (n : ℕ) (a : Fin n → Formalism.IndefR.NX.KB S i b) (x : Fin n → Formalism.IndefR.NX.FmK S ((j : ℕ) + 1)),
      GlobalTheory.SeriesTie.evK YS v₀ hρ i j b t =
        ∑ k : Fin n, GlobalTheory.SeriesTie.Setup.e ρ i b (a k) • GlobalTheory.SeriesTie.evW YS v₀ j (x k).val := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a f => exact ⟨1, fun _ => a, fun _ => f, by simp [evK_tmul]⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨n₁, a₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, a₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ + n₂, Fin.append a₁ a₂, Fin.append x₁ x₂, ?_⟩
    rw [map_add, e₁, e₂, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.EvaluationSum
