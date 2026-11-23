import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.DotPTPinv

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

def vT : IdxD D → Fin X.B.I.n → TpX X p
  | Sum.inr (Sum.inl (Sum.inl i)) => adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)
  | Sum.inl a => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inl a))
  | Sum.inr (Sum.inl (Sum.inr v)) => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inr (Sum.inl (Sum.inr v))))
  | Sum.inr (Sum.inr c) => ratV (F := X.B.I.F) (FpX X p) (vecAt (k := D.R.k) (frameOf X u) (Sum.inr (Sum.inr c)))

def mT : Matrix (IdxD D) (IdxD D) (FpX X p) := fun j t => crd1 X p θ P (vT X hb u p t) j

theorem mC_eq :
    ((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      ofCols (colv (cV X u p θ) (yV X hb u p θ)) = mT X hb u p θ P := by
  ext j t
  have e : (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      ofCols (colv (cV X u p θ) (yV X hb u p θ))) j t =
      (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ
        colv (cV X u p θ) (yV X hb u p θ) t) j := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, ofCols]
  rw [e]
  rcases t with a | ((i | v) | c) <;> rfl

theorem vT_cong (t : IdxD D) : vT X hb u p t - adqRef X hb u p t ∈ gLam X p := by
  rcases t with a | ((i | v) | c)
  · exact adq_e_cong X hb u p a
  · show adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i) -
      adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i) ∈ gLam X p
    rw [sub_self]
    exact zero_mem _
  · exact adq_z_cong X hb u p
  · exact adq_f_cong X hb u p (Fin.rev c)

theorem vT_cong1 (hL : LatBasis X p θ (reindex₂ X p P)) (t j : IdxD D) :
    InG X p (crd1 X p θ P (vT X hb u p t) j - crd1 X p θ P (adqRef X hb u p t) j) :=
  firstCoords_congruent_mod X p θ P hL _ _ (vT_cong X hb u p t) j

theorem vT_int (hL : LatBasis X p θ (reindex₂ X p P)) (t j : IdxD D) :
    crd1 X p θ P (vT X hb u p t) j ∈ OvA X p := by
  have h := (OvA X p).add_mem _ _ (adq_inG_int X p (vT_cong1 X hb u p θ P hL t j))
    (((latCrd_of X p θ P hL _).1 (adq_ref_lat X hb u p t)).1 j)
  rwa [sub_add_cancel] at h

theorem vT_RC (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p P))
    (s t : IdxD D) : ∃ z : OvA X p, (adqR X hb u p θ P * mT X hb u p θ P) s t =
      (1 : Matrix (IdxD D) (IdxD D) (FpX X p)) s t + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  have e1 : (adqR X hb u p θ P * mT X hb u p θ P) s t =
      sgnV X p s * (crd2 X p θ P (adqRefR X hb u p s) ⬝ᵥ crd1 X p θ P (vT X hb u p t)) := by
    simp only [Matrix.mul_apply, adqR, mT, dotProduct, Finset.mul_sum, mul_assoc]
  have hD := adq_dotG X p (a := crd2 X p θ P (adqRefR X hb u p s)) (a' := crd2 X p θ P (adqRefR X hb u p s))
    (b := crd1 X p θ P (vT X hb u p t)) (b' := crd1 X p θ P (adqRef X hb u p t))
    (fun j => ((latCrd_of X p θ P hL _).1 (adq_refR_lat X hb u p s)).2 j)
    (fun j => vT_int X hb u p θ P hL t j) (fun j => by rw [sub_self]; exact inG_zero)
    (fun j => vT_cong1 X hb u p θ P hL t j)
  rw [adq_pairM X hb u p θ P hθ] at hD
  obtain ⟨y, hy⟩ := inG_mul_int _ (sgnV_int X p s) hD
  obtain ⟨z, hz⟩ := rc_cong X p θ P hθ hε hL s t
  refine ⟨y + z, ?_⟩
  rw [e1]
  push_cast
  linear_combination hy + hz

theorem adaptIn_det (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p P)) :
    IntO (p.1.adicCompletionIntegers X.B.I.F).toSubring
        (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))) ∧
      ∃ uu : FpX X p, uu ∈ p.1.adicCompletionIntegers X.B.I.F ∧
        (((P⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))).det * uu = 1 := by
  rw [mC_eq X hb u p θ P]
  choose N hN using fun s t => vT_RC X hb u p θ P hθ hε hL s t
  have hgc : ((gA X p : OvA X p) : FpX X p) = ((gOf p : ℕ) : FpX X p) := by simp [gA]
  have hRC : adqR X hb u p θ P * mT X hb u p θ P =
      1 + ((gA X p : OvA X p) : FpX X p) • Matrix.of (fun s t => ((N s t : OvA X p) : FpX X p)) := by
    ext s t
    rw [hN s t, hgc]
    simp
  obtain ⟨c, hc⟩ := exists_gl_of_left_inv (OvA X p) (gA X p) (PIW.MassDataColumns.gOf_nonunit X p)
    (mT X hb u p θ P) (adqR X hb u p θ P) _
    (fun i t => vT_int X hb u p θ P hL t i)
    (fun s i => (OvA X p).mul_mem _ _ (sgnV_int X p s)
      (((latCrd_of X p θ P hL _).1 (adq_refR_lat X hb u p s)).2 i))
    (fun s t => (N s t).2) hRC
  refine ⟨fun i t => vT_int X hb u p θ P hL t i,
    ((((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p) : FpX X p),
    (((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p).2, ?_⟩
  have hdet : (mT X hb u p θ P).det = (((c : Matrix (IdxD D) (IdxD D) (OvA X p)).det : OvA X p) : FpX X p) := by
    rw [← hc]
    exact (RingHom.map_det (OvA X p).subtype (c : Matrix (IdxD D) (IdxD D) (OvA X p))).symm
  have hu : (c : Matrix (IdxD D) (IdxD D) (OvA X p)).det *
      ((c⁻¹ : GL (IdxD D) (OvA X p)) : Matrix (IdxD D) (IdxD D) (OvA X p)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [hdet]
  have := congrArg (fun x : OvA X p => (x : FpX X p)) hu
  simpa using this

end B

end PIW.MassDataColumns
