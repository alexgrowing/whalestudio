import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSpanGenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootTiltLatticeBoundStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frames_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ eT eM : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame (rhoTA D) eT ∧ IsFrame D.ρM eM ∧ ∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], eT (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := inferInstance
  set d := Module.finrank ℤ_[p] Λ with hd
  have dpos : 0 < d := Module.finrank_pos
  obtain ⟨N', x, y, hN', hx, hy⟩ :=
    GlobalTheory.T.exists_span_rhoM_rhoT_mulVec_eq_top p C v O hv ε hε Λ h D d (Module.finBasis ℤ_[p] Λ)
  have hNN : N' = N := by
    have : d * N' = d * N := by rw [mul_comm, ← hN', hh]
    exact Nat.eq_of_mul_eq_mul_left dpos this
  subst hNN
  have hh' : h = N' * d := hN'

  have sM := (GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D).1
  obtain ⟨eM, heM, -⟩ := GlobalTheory.T.ainf_frame_span_generation p O Λ N' d h (Module.finBasis ℤ_[p] Λ) D.ρM x sM hh' hx

  let ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O) :=
    (RingHom.mapMatrix (ofPadic p O)).comp D.ρT.toRingHom
  have hρ : ∀ l, ρ l = rhoTA D l := fun l => rfl
  have sT : ∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
    intro c
    rw [hρ, rhoTA, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext1 i j
    by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply, Matrix.one_apply]
  let L : (Fin h → ℤ_[p]) →ₗ[ℤ_[p]] (Fin h → Ainf p O) :=
    (Algebra.linearMap ℤ_[p] (Ainf p O)).compLeft (Fin h)
  have hL : ∀ w j, L w j = ofPadic p O (w j) := fun w j => rfl
  have hLmul : ∀ (l : Λ) (w : Fin h → ℤ_[p]), L (D.ρT l *ᵥ w) = ρ l *ᵥ (fun j => ofPadic p O (w j)) := by
    intro l w; funext j
    rw [hL, hρ, rhoTA, RingHom.map_mulVec]
    rfl
  have hxT : Submodule.span (Ainf p O) (Set.range fun ij : Fin N' × Fin d =>
      ρ (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ (fun j => ofPadic p O (y ij.1 j))) = ⊤ := by
    set S := Set.range fun ij : Fin N' × Fin d =>
      ρ (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ (fun j => ofPadic p O (y ij.1 j))
    have hle : Submodule.span ℤ_[p] (Set.range fun ij : Fin N' × Fin d =>
        D.ρT (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ y ij.1) ≤
        ((Submodule.span (Ainf p O) S).restrictScalars ℤ_[p]).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨ij, rfl⟩
      show L _ ∈ Submodule.span (Ainf p O) S
      rw [hLmul]
      exact Submodule.subset_span ⟨ij, rfl⟩
    rw [eq_top_iff, ← (Pi.basisFun (Ainf p O) (Fin h)).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hk := hle (hy ▸ Submodule.mem_top : Pi.single k (1 : ℤ_[p]) ∈ _)
    have e1 : L (Pi.single k 1) = Pi.basisFun (Ainf p O) (Fin h) k := by
      funext j
      rw [hL, Pi.basisFun_apply]
      by_cases hkj : j = k
      · subst hkj; simp
      · simp [Pi.single_apply, hkj]
    rw [← e1]
    exact hk
  obtain ⟨eT, heT, heT1⟩ := GlobalTheory.T.ainf_frame_span_generation p O Λ N' d h (Module.finBasis ℤ_[p] Λ) ρ
    (fun i j => ofPadic p O (y i j)) sT hh' hxT
  refine ⟨eT, eM, heT, heM, fun i l => ⟨D.ρT l *ᵥ y i, ?_⟩⟩
  rw [heT1, ← hLmul]
  rfl

end GlobalTheory.DetInv
