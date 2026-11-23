import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDegreeKEquivariantStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LowKMultOne

theorem map_eq_zero_of_disjoint : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ S : R.Pi →ₗ[ℂ] R.Pi, KEqOn B G.M om R.p (lowPartInf B G.M R.p) S → ∀ N : Submodule ℂ R.Pi,
        (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
          Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N) →
        lowPartInf B G.M R.p ⊓ N = ⊥ → (∀ x ∈ lowPartInf B G.M R.p, S x ∈ N) → ∀ x ∈ lowPartInf B G.M R.p, S x = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM S hS N _hN hVN hSN
  let U : ℕ → Submodule ℂ R.Pi := fun k => (fockDeg G.M B.ψ B.emb k).map R.p
  have hUmono : Monotone U := fun i j h => Submodule.map_mono (fockDeg_mono _ _ _ h)
  have htop : ⨆ k, U k = ⊤ := by
    show ⨆ k, (fockDeg G.M B.ψ B.emb k).map R.p = ⊤
    rw [← Submodule.map_iSup, ← pol_eq_iSup_fockDeg]
    exact hM.real.quot.onto
  have hfin : FiniteDimensional ℂ (lowPartInf B G.M R.p) :=
    GlobalTheory.T.lowPart_finite_dimensional hKP F E σ B a a' G X om om' R Rf hM
  have hfg : ((lowPartInf B G.M R.p).map S).FG :=
    (Module.Finite.iff_fg.1 hfin).map S
  obtain ⟨Y, ⟨m, rfl⟩, hm⟩ := (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le (Submodule ℂ R.Pi) _).1
    ((Submodule.fg_iff_compact _).1 hfg) (Set.range U) (Set.range_nonempty U)
    hUmono.directed_le.directedOn_range (by rw [sSup_range, htop]; exact le_top)
  have hstep := GlobalTheory.T.low_degree_K_equivariant hKP F E σ B a a' G X om om' R Rf hM
  have key : ∀ j : ℕ, (∀ x ∈ lowPartInf B G.M R.p, S x ∈ U (lowDegInf B G.M R.p + j)) →
      ∀ x ∈ lowPartInf B G.M R.p, S x ∈ U (lowDegInf B G.M R.p) := by
    intro j
    induction j with
    | zero => exact fun h => h
    | succ j ih => exact fun h => ih (hstep _ (Nat.le_add_right _ _) S hS h)
  have hV : ∀ x ∈ lowPartInf B G.M R.p, S x ∈ lowPartInf B G.M R.p := by
    have hm' : ∀ x ∈ lowPartInf B G.M R.p, S x ∈ U m := fun x hx => hm ⟨x, hx, rfl⟩
    rcases le_total m (lowDegInf B G.M R.p) with h | h
    · exact fun x hx => hUmono h (hm' x hx)
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h
      rw [hj] at hm'
      exact key j hm'
  intro x hx
  have : S x ∈ lowPartInf B G.M R.p ⊓ N := ⟨hV x hx, hSN x hx⟩
  rw [hVN] at this
  exact (Submodule.mem_bot ℂ).1 this

end GlobalTheory.LowKMultOne
