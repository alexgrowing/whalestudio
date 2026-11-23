import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMirabolicKernelEqZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedActionSmoothStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMirDer.NonZero

section Alg

variable {k : Type} [Field k]

theorem mir_zero_eq_one (g : Mir k 0) : g = 1 := by
  have h := (mem_Mir_iff k (g : GL (Fin 1) k)).1 g.2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
  have hj : j = Fin.last 0 := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
  subst hi
  subst hj
  have := congrFun h (Fin.last 0)
  simpa [eLast] using this

end Alg

theorem twKer_eq_bot_of_forall_eq_one {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (hN : ∀ n : N, n = 1) :
    twKer ρ N θ = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  rw [hN n]
  simp

theorem nontrivial_quot_of_not_mem {V : Type} [AddCommGroup V] [Module ℂ V] (p : Submodule ℂ V) (v : V)
    (hv : v ∉ p) : Nontrivial (V ⧸ p) :=
  nontrivial_of_ne (Submodule.Quotient.mk v) 0 (by rwa [Ne, Submodule.Quotient.mk_eq_zero])

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmb (n : ℕ) : Continuous (glEmb k n) := by
  apply Continuous.units_map
  show Continuous (glEmbMat k n)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases <;> simp [glEmbMat] <;>
      first | exact continuous_const | exact (continuous_apply _).comp (continuous_apply _) | fun_prop
  | cast i => induction j using Fin.lastCases <;> simp [glEmbMat] <;>
      first | exact continuous_const | exact (continuous_apply _).comp (continuous_apply _) | fun_prop

theorem continuous_levi_comp_subtype (m : ℕ) : Continuous ((levi k (m + 1)).comp (Mir k m).subtype) :=
  continuous_induced_rng.2 ((continuous_glEmb (m + 1)).comp continuous_subtype_val)

end Top

theorem exists_derivative_nontrivial (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ : ψ ≠ 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k m) V),
      IsSmooth τ → Nontrivial V → ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ τ _ hV
    refine ⟨0, le_rfl, ?_⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply nontrivial_quot_of_not_mem _ v
    rw [twKer_eq_bot_of_forall_eq_one τ _ _ (fun n => Subtype.ext (mir_zero_eq_one _))]
    exact hv
  | succ m ih =>
    intro V _ _ τ hτ hV
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    by_cases h1 : v ∈ twKer τ (MirUin k (m + 1)) 1
    · have hex : ∃ g : GL (Fin (m + 1)) k,
          τ (levi k (m + 1) g) v ∉ twKer τ (MirUin k (m + 1)) (mirChar k ψ m) := by
        by_contra hcon
        push_neg at hcon
        exact hv (GlobalTheory.T.smooth_mirabolic_kernel_eq_zero k ψ hψc hψ m V τ hτ v h1 hcon)
      obtain ⟨g, hg⟩ := hex
      haveI := nontrivial_quot_of_not_mem _ _ hg
      have hs : IsSmooth (phiMinus k ψ τ) :=
        GlobalTheory.T.twisted_action_smooth τ hτ _ _ _ (continuous_levi_comp_subtype m) (levi_stab ψ m)
      obtain ⟨n, hn, hnt⟩ := ih _ (phiMinus k ψ τ) hs inferInstance
      obtain ⟨e⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ m n hn V τ
      exact ⟨n, hn.trans (Nat.le_succ m), e.injective.nontrivial⟩
    · refine ⟨m + 1, le_rfl, ?_⟩
      apply nontrivial_quot_of_not_mem _ v
      rwa [← GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ (m + 1) V τ]

end GlobalTheory.CompanionTheory.BZMirDer.NonZero

end
