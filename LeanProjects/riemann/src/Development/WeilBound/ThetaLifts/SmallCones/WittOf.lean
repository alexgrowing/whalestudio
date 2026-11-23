import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.IsFrPlane
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr

theorem sig_val {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ}
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) (u : Fin r ⊕ Fin s → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (A *ᵥ u) =
      ((∑ i, Complex.normSq (u (Sum.inl i)) - ∑ i, Complex.normSq (u (Sum.inr i)) : ℝ) : ℂ) := by
  have e : star (A *ᵥ u) = A.map star *ᵥ star u := funext fun i => RingHom.map_mulVec (starRingEnd ℂ) A u i
  rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
  simp [Matrix.fromBlocks_mulVec, dotProduct, Matrix.neg_mulVec, Complex.mul_conj, sub_eq_add_neg]

theorem aniso {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) {x : Fin n → ℂ}
    (hx : x ⬝ᵥ M *ᵥ star x = 0) : x = 0 := by
  obtain ⟨hn, A, hA⟩ := h
  obtain ⟨A', -, h1⟩ := PositivityTheory.ThKG.Tow.Pln.frame_inv hn hA
  have e : x = A *ᵥ (A' *ᵥ x) := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  generalize A' *ᵥ x = u at e
  rw [e, sig_val hA, Complex.ofReal_eq_zero] at hx
  have : u = 0 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_sub, neg_eq_zero] at hx
      ext (i | i)
      · exact i.elim0
      · exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 hx i (Finset.mem_univ _))
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at hx
      ext (i | i)
      · exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 hx i (Finset.mem_univ _))
      · exact i.elim0
  rw [e, this, Matrix.mulVec_zero]

theorem witt_of : Witt := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  refine ⟨fun h0 x hx => ?_, fun n₁ H h1 h2 => ?_⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have e := congrArg (B.emb w).1 hx
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hB.cm.2.2.2, map_zero] at e
    have := aniso (hX.sig w) h0 (x := fun i => (B.emb w).1 (x i)) e
    exact funext fun i => (B.emb w).1.injective ((congrFun this i).trans (map_zero _).symm)
  · obtain ⟨c, hc, hσ⟩ := PositivityTheory.ThKF.exists_scale hB.cm (-1)
    have f : ∀ x, form σ X.J x x = 0 → form σ (c • X.J) x x = 0 := fun x hx => by
      rw [form, Matrix.smul_mulVec, dotProduct_smul]
      exact smul_eq_zero_of_right _ hx
    have key := fun x : IsoV σ X => PositivityTheory.ThKEnd.Grp.wittVec F E σ hB.cm n (c • X.J)
      (fun i j => by simp [hσ, hX.herm])
      (by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc) (det_ne (Or.inl hX))) x.1 H.x x.2.1 h1 (f _ x.2.2) (f _ h2)
    choose g g1 g2 using key
    have g3 : ∀ x, (g x).1ᵀ * X.J * (g x).1.map σ = X.J := fun x => smul_right_injective _ hc (by
      have := g1 x
      rwa [Matrix.mul_smul, Matrix.smul_mul] at this)
    have key : ∀ x, ∃ p : UA σ X.J, mat p = incM F (g x).1 := fun x =>
      PositivityTheory.ThKG.Tow.Levi.exists_UA (g' := incM F (g x)⁻¹.1)
        (by rw [← PositivityTheory.ThKEnd.Grp.incM_mul, Units.mul_inv, PositivityTheory.ThKEnd.Grp.incM_one])
        (by
          conv_rhs => rw [← g3 x]
          rw [PositivityTheory.ThKEnd.Grp.incM_mul, PositivityTheory.ThKEnd.Grp.incM_mul, PositivityTheory.ThKEnd.Grp.incM_conj]
          rfl)
    choose γ hγ using key
    exact ⟨γ, fun x => ⟨mem_ratU.2 ⟨_, hγ x⟩, by rw [hγ, PositivityTheory.ThKEnd.Grp.incM_mulVec, g2]⟩⟩

end PositivityTheory.ThKCT

end
