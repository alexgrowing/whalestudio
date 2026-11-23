import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAwayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorMemSpanLocalHeisenbergTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelOntoLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceModelOnto

variable {D : D7}

theorem isSBHalf_zero {m n : ℕ} (a : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf a Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem isSBHalf_smul {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf a Λ Φ) : IsSBHalf a Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (hne t ht), k, hk,
    fun u hu hu' t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hu' t], fun t ht => h3 t (hne t ht)⟩

theorem isSBHalf_add {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf a Λ Φ) (h' : IsSBHalf a Λ Ψ) : IsSBHalf a Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have hne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf a u → IsHalf a (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (hh _ _ hu') t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (hh _ _ hu') t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem placeModel_onto_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (a : AE D), IsSplitIdem D a → a + cA D a = idem D (.inl v) → (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧ ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → (∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ)) ∧ ∀ x, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x := by
  first
  | exact @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | (apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local ..)

end GlobalTheory.PlaceModelOnto

end
