import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def LamEig2 : Prop := ThLin → ThOp → ChiStab → ThP →
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (ev : Letter → Qbar l), Std A N w j →
    (∃ k : ℕ, ∀ T, GlobalTheory.KZ.admitted N l T → ‖ev T‖ ≤ (l : ℝ) ^ k) → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l,
    (∀ T, GlobalTheory.KZ.admitted N l T → ∀ b ∈ X.B N l w,
      FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] X.op N l T b) =
        ev T • FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) →
    ∀ lam₀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam₀ →
    (∀ a, lam a = lam₀ (FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) P a)) →
    ∃ c₂ : ℕ, ∀ n, c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N w χ b →
      Cg (n - c₂) (lam (th X A N j n (X.op N l T b))) (ev T * lam (th X A N j n b))

def AqBd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ), Nf e S A W → KillsMu l χ →
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) → ∃ k : ℕ, ∀ q : ℕ, q.Prime → ‖ι.symm (g.a q)‖ ≤ (l : ℝ) ^ k

def AdmOf2 : Prop := AdmTop → NewformPartOfTowerModule → AdmRho → JEx → RhoFrob → Unif → FormP → FinP → CoefUb → ThLin → ThOp → ChiStab → ThP → LamEig2 →
  ChiQuad → AqBd → AdmFR

theorem lamEig2 : LamEig2 := by
  intro hLin hOp hStab hP l _ Ω _ _ _ ε X A N w j χ ev hS hev P hPm hEig lam₀ lam hfin hlam
  obtain ⟨k', hev⟩ := hev
  obtain ⟨c, hc⟩ := hP hOp hStab l Ω ε X A N w j χ hS P hPm
  obtain ⟨k, hk⟩ := hfin.exists_loss
  refine ⟨c + k' + k, fun n hn T b hT hb => ?_⟩
  obtain ⟨Θ, hΘ⟩ := hLin l Ω ε X A N w j hS n
  have hTb := hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb
  have h1 := hc n (by omega) Θ hΘ _ hTb
  have h2 := hc n (by omega) Θ hΘ _ hb
  rw [hEig T hT b hb.1, map_smul] at h1
  rw [hlam, hlam, ← smul_eq_mul, ← map_smul, ← Nat.sub_sub, ← Nat.sub_sub]
  refine hk (n - c - k') (by omega) _ _ fun i => ?_
  have h3 := cg_mul_left (k := k') (by omega) (hev T hT) (h2 i)
  have h4 := cg_mono (Nat.sub_le (n - c) k') (h1 i)
  simp only [Pi.smul_apply, smul_eq_mul] at h4 ⊢
  unfold Cg at h3 h4 ⊢
  rw [← norm_neg, neg_sub] at h3
  rw [← sub_add_sub_cancel _ (ev T * Θ (FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) i)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h4 h3)

end UpperTheory.V.Z.Kato.Joint

end
