import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.MapInfChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.ExistsAlgRepQdetEqSmulOneOfIsReg
import Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.WindowLinearEntryEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.WindowBoundReduction.WindowIntegerGapBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.ExistsScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.WeylC UpperTheory.V.Af

namespace UpperTheory.V.Cj.R

private theorem ex_pad {d D : ℕ} (h : d ∣ D) :
    Nonempty (Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ) := by
  obtain ⟨k, rfl⟩ := h
  let b : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ :=
    AlgHom.mk' ((Matrix.blockDiagonalRingHom (Fin d) (Fin k) ℂ).comp (Pi.constRingHom (Fin k) _))
      fun c A => Matrix.blockDiagonal_smul c fun _ : Fin k => A
  exact ⟨(Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv).toAlgHom.comp b⟩

private theorem ex_tens {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (P : (E →+* ℂ) → Weyl.Pre a)
    (hP : ∀ τ, 0 < (P τ).d) (ν : (E →+* ℂ) → Fin a → ℂ) (hν : ∀ τ, (P τ).HasWt (ν τ)) (N : ℕ) :
    ∃ Ξ : AlgRep E a, ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = (∏ k : Fin a, (u - N - (k : ℂ) + ν τ k)) • 1 := by
  classical
  let D := ∏ τ, (P τ).d
  have hD : 0 < D := Finset.prod_pos fun τ _ => hP τ
  let φ := fun τ => (ex_pad (Finset.dvd_prod_of_mem (fun τ => (P τ).d) (Finset.mem_univ τ))).some
  let F : (E →+* ℂ) → GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ := fun τ => (φ τ).toMonoidHom.comp (fac (P τ) N τ)
  have hF := fun τ => UpperTheory.window_linear_entry_estimate E a _ D (φ τ).toLinearMap _ (isReg_fac (P τ) N τ)
  have hreg : ∀ τ, IsReg (F τ) := fun τ => (hF τ).1
  have hder : ∀ t τ i j, eOf (F t) τ i j = φ t (eOf (fac (P t) N t) τ i j) := fun t => (hF t).2
  let r := Matrix.reindexAlgEquiv ℂ ℂ
    (Fintype.equivFinOfCardEq (by simp) : ((E →+* ℂ) → Fin D) ≃ Fin (D ^ Fintype.card (E →+* ℂ)))
  refine UpperTheory.exists_algRep_qdet_eq_smul_one_of_isReg E a _ (pow_pos hD _) ((r.toAlgHom.toMonoidHom.comp piK).comp (MonoidHom.pi F))
    (fun i j => isReg_piK hreg _ _) _ fun τ u => ?_
  have h1 : eOf ((r.toAlgHom.toMonoidHom.comp piK).comp (MonoidHom.pi F)) τ = fun i j =>
      ((r.toAlgHom.comp (intersection_update_fsHerm_neg_one τ)).comp (φ τ)) ((P τ).E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0)) := by
    funext i j
    change r (eOf (fun y => piK fun t => F t y) τ i j) = _
    rw [eOf_piK hreg (fun t => map_one _), Finset.sum_eq_single τ (fun t _ ht => by
      rw [hder, eOf_fac, if_neg ht, map_zero, map_zero]) (by simp), hder, eOf_fac, if_pos rfl]
    rfl
  rw [h1, ← map_qdet, qdet_shift, hν, map_smul, map_one]
  simp only [sub_eq_add_neg]

theorem exAlgRep : ExAlgRep := by
  intro E _ _ _ a m hm
  choose N₀ hN using fun τ => UpperTheory.window_integer_gap_bound a (m τ) (hm τ)
  choose ν h1 h2 using fun τ => hN τ (∑ t, N₀ t) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  choose P h3 h4 h5 using fun τ => Weyl.existsScalar a (ν τ) (h1 τ) (∑ k, ν τ k)
    fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨Ξ, h⟩ := ex_tens P h3 _ h5 (∑ t, N₀ t)
  refine ⟨Ξ, fun τ => (algInfChar_iff _ _ _).2 ⟨by rw [Multiset.card_map, (hm τ).1], fun u => ?_⟩⟩
  rw [h, h2]

theorem exAlgRepCusp : ExAlgRepCusp := by
  intro E _ _ _ a π hπ
  have h := fun τ => ParLaws.hasInfChar_infChar (CG.mk π) τ
  obtain ⟨Ξ, hΞ⟩ := exAlgRep E a (CG.mk π).infChar fun τ => ⟨(h τ).1, hπ τ⟩
  exact ⟨Ξ, fun τ => ⟨_, h τ, hΞ τ⟩⟩

end UpperTheory.V.Cj.R
