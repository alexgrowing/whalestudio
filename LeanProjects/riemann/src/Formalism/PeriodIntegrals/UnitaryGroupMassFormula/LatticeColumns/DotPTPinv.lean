import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsAdaptedColumn

noncomputable section

namespace PIW.MassDataColumns

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl
  MassDataIdxFrA MassDataIdxAdA MassDataIdxSteps Formalism.FourierDecayAlt.S3
open scoped Matrix TensorProduct

variable {D : D7}

section B

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (IdxD D) (FpX X p))

theorem cV_crd (s : IdxD D) :
    ((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ cV X u p θ s =
      crd1 X p θ P (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) := rfl

theorem yV_crd (i : Fin D.R.k) :
    ((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ yV X hb u p θ i =
      crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) := rfl

theorem dot_PT_Pinv (a w : IdxD D → FpX X p) :
    ((P : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *ᵥ a) ⬝ᵥ
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ w) = a ⬝ᵥ w := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.vecMul_one]

theorem aV_dot (s : IdxD D) (w : IdxD D → FpX X p) :
    aV X u p θ s ⬝ᵥ w = crd2 X p θ P (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ⬝ᵥ
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ w) := by
  unfold crd2 aV
  exact (dot_PT_Pinv X p P _ _).symm

theorem ay_gen (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) (i : Fin D.R.k)
    (V : Fin X.B.I.n → TpX X p) (v0 : Formalism.L2.SG.HidaSetting.VA X.B.I)
    (hw : adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0 ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hd : V - adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0 ∈ gLam X p)
    (h0 : ∃ z : OvA X p, crd2 X p θ P (PI.FinKW.vecV X.B.I p.1 v0) ⬝ᵥ
      crd1 X p θ P (PI.FinKW.vecV X.B.I p.1 (X.bw i)) = ((gOf p : ℕ) : FpX X p) * (z : FpX X p)) :
    InG X p (crd2 X p θ P V ⬝ᵥ crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i))) := by
  have hyi : ∀ j, crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) j ∈ OvA X p :=
    fun j => ((latCrd_of X p θ P hL _).1 (adq_ref_lat X hb u p (wI i))).1 j
  have h1 := adq_dotG X p (a := crd2 X p θ P V)
    (a' := crd2 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 v0))
    (b := crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)))
    (b' := crd1 X p θ P (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)))
    (fun j => ((latCrd_of X p θ P hL _).1 hw).2 j) hyi
    (secondCoords_congruent_mod X p θ P hL _ _ hd) (fun j => by rw [sub_self]; exact inG_zero)
  rw [adq_pairM X hb u p θ P hθ] at h1
  obtain ⟨z, hz⟩ := h0
  rw [hz] at h1
  have h3 := inG_add h1 (inG_g_mul (X := X) (p := p) z)
  rwa [sub_add_cancel] at h3

theorem ay_inG (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) (s : IdxD D) (hs : ¬ IsW s)
    (i : Fin D.R.k) : InG X p (aV X u p θ s ⬝ᵥ yV X hb u p θ i) := by
  rw [aV_dot X u p θ P, yV_crd X hb u p θ P]
  rcases s with a | ((j | v) | c)
  · exact ay_gen X hb u p θ P hθ hL i _ (X.e0 a) (adq_ref_lat X hb u p (Sum.inl a)) (adq_e_cong X hb u p a)
      (fin_dir X p θ P hθ hL _ _ ((X.weightVectorsIntegral i).2.2 a).1)
  · exact absurd ⟨j, rfl⟩ hs
  · exact ay_gen X hb u p θ P hθ hL i _ X.z0 (adq_ref_lat X hb u p zI) (adq_z_cong X hb u p)
      (fin_dir X p θ P hθ hL _ _ (X.weightVectorsIntegral i).1)
  · exact ay_gen X hb u p θ P hθ hL i _ (X.f0 (Fin.rev c)) (adq_refR_lat X hb u p (Sum.inl (Fin.rev c)))
      (adq_f_cong X hb u p (Fin.rev c)) (fin_dir X p θ P hθ hL _ _ ((X.weightVectorsIntegral i).2.2 (Fin.rev c)).2.1)

theorem adaptIn_ay (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p P)) :
    ∃ o : IdxD D → Fin D.R.k → FpX X p,
      (∀ s i, ¬ IsW s → aV X u p θ s ⬝ᵥ yV X hb u p θ i = ((gOf p : ℕ) : FpX X p) * o s i) ∧
      (∀ s i, o s i ∈ p.1.adicCompletionIntegers X.B.I.F) := by
  have h : ∀ (s : IdxD D) (i : Fin D.R.k), ∃ y : OvA X p,
      ¬ IsW s → aV X u p θ s ⬝ᵥ yV X hb u p θ i = ((gOf p : ℕ) : FpX X p) * (y : FpX X p) := by
    intro s i
    by_cases hs : IsW s
    · exact ⟨0, fun h => absurd hs h⟩
    · obtain ⟨y, hy⟩ := ay_inG X hb u p θ P hθ hL s hs i
      exact ⟨y, fun _ => hy⟩
  choose o ho using h
  exact ⟨fun s i => (o s i : FpX X p), ho, fun s i => (o s i).2⟩

end B

end PIW.MassDataColumns
