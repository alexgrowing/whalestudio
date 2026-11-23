import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsProjectionOrth

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA PIW.MassDataColumns
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_congruent_mod (hL : LatBasis X p θ (reindex₂ X p Q)) (v w : Fin X.B.I.n → TpX X p) (hd : v - w ∈ gLam X p)
    (i : IdxD D) : InG X p (crd1 X p θ Q v i - crd1 X p θ Q w i) := by
  obtain ⟨y, hy⟩ := adq_gLam1 (X := X) (p := p) (θ := θ) (Q := Q) hL (v - w) hd i
  refine ⟨y, ?_⟩
  rw [← hy]
  simp only [crd1, map_sub, Pi.sub_comp, Matrix.mulVec_sub, Pi.sub_apply]

theorem secondCoords_congruent_mod (hL : LatBasis X p θ (reindex₂ X p Q)) (v w : Fin X.B.I.n → TpX X p) (hd : v - w ∈ gLam X p)
    (i : IdxD D) : InG X p (crd2 X p θ Q v i - crd2 X p θ Q w i) := by
  obtain ⟨y, hy⟩ := adq_gLam2 (X := X) (p := p) (θ := θ) (Q := Q) hL (v - w) hd i
  refine ⟨y, ?_⟩
  rw [← hy]
  simp only [crd2, map_sub, Pi.sub_comp, Matrix.mulVec_sub, Pi.sub_apply]

abbrev adqRef (t : IdxD D) : Fin X.B.I.n → TpX X p := adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (colV X t)

abbrev adqRefR (s : IdxD D) : Fin X.B.I.n → TpX X p := adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (rowV X s)

theorem adq_ref_lat (t : IdxD D) :
    adqRef X hb u p t ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  adq_lat (X := X) (hb := hb) (u := u) (p := p) _ (colV_lat (X := X) (p := p) t)

theorem adq_refR_lat (s : IdxD D) :
    adqRefR X hb u p s ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  adq_lat (X := X) (hb := hb) (u := u) (p := p) _ (rowV_lat (X := X) (p := p) s)

include hb u in
theorem adq_F_lat (a : Fin D.R.rS) :
    adqF X p a ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h := colV_lat (X := X) (p := p) (Sum.inr (Sum.inr (Fin.rev a)))
  simp only [colV, Fin.rev_rev] at h
  exact adq_lat_of (X := X) (p := p) _ _ (adq_lat (X := X) (hb := hb) (u := u) (p := p) _ h)
    (adq_f_cong (X := X) (hb := hb) (u := u) (p := p) a)

include hb in
theorem adq_Z_lat :
    adqZ X u p ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  adq_lat_of (X := X) (p := p) _ _
    (adq_lat (X := X) (hb := hb) (u := u) (p := p) _ (colV_lat (X := X) (p := p) zI))
    (adq_z_cong (X := X) (hb := hb) (u := u) (p := p))

include hb in

theorem adq_tau (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q)) :
    ∃ o : OvA X p, adqTau X u p θ Q = -1 + ((gOf p : ℕ) : FpX X p) * (o : FpX X p) := by
  have hw := adq_ref_lat X hb u p zI
  have hz := adq_Z_lat X hb u p
  have hd := adq_z_cong X hb u p
  obtain ⟨y, hy⟩ := adq_dotG X p (a := crd2 X p θ Q (adqZ X u p)) (a' := crd2 X p θ Q (adqRef X hb u p zI))
    (b := crd1 X p θ Q (adqZ X u p)) (b' := crd1 X p θ Q (adqRef X hb u p zI))
    (fun i => ((latCrd_of X p θ Q hL _).1 hw).2 i) (fun i => ((latCrd_of X p θ Q hL _).1 hz).1 i)
    (secondCoords_congruent_mod X p θ Q hL _ _ hd) (firstCoords_congruent_mod X p θ Q hL _ _ hd)
  rw [adq_pairM X hb u p θ Q hθ] at hy
  obtain ⟨z, hz'⟩ := cong_dir X p θ Q hθ hL X.z0 X.z0 (-1) (by rw [sub_neg_eq_add]; exact X.formsAtZero.1)
  have h1 : (θ (PI.FinKW.psiV X.B.I p.1 (-1))).1 = -1 := by simp
  rw [h1] at hz'
  refine ⟨y + z, ?_⟩
  have e : adqTau X u p θ Q = crd2 X p θ Q (adqZ X u p) ⬝ᵥ crd1 X p θ Q (adqZ X u p) := rfl
  have e2 : crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X zI)) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X zI)) =
      crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) := rfl
  rw [e2, hz'] at hy
  rw [e]
  push_cast
  linear_combination hy

include hb in

theorem adq_tau_inv (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q)) :
    (adqTau X u p θ Q)⁻¹ ∈ OvA X p ∧ adqTau X u p θ Q ≠ 0 := by
  obtain ⟨o, ho⟩ := adq_tau X hb u p θ Q hθ hL
  have hg : ((gOf p : ℕ) : OvA X p) * o ∈ IsLocalRing.maximalIdeal (OvA X p) :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (gOf_nonunit X p))
  have hu1 : IsUnit (1 - ((gOf p : ℕ) : OvA X p) * o) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((IsLocalRing.mem_maximalIdeal _).mp hg)
  have hu : IsUnit (-1 + ((gOf p : ℕ) : OvA X p) * o) := by
    have := hu1.neg
    rwa [neg_sub, sub_eq_neg_add] at this
  obtain ⟨w, hw⟩ := hu
  have hτ : adqTau X u p θ Q = ((w : OvA X p) : FpX X p) := by
    rw [hw, ho]
    push_cast
    rfl
  have e : ((w : OvA X p) : FpX X p) * ((↑w⁻¹ : OvA X p) : FpX X p) = 1 :=
    congrArg Subtype.val w.mul_inv
  refine ⟨?_, ?_⟩
  · rw [hτ, inv_eq_of_mul_eq_one_right e]
    exact (↑w⁻¹ : OvA X p).2
  · rw [hτ]
    intro h0
    exact w.ne_zero (Subtype.ext h0)

def adqCol : IdxD D → IdxD D → FpX X p
  | Sum.inl a => crd1 X p θ Q (adqE X p a)
  | Sum.inr (Sum.inl (Sum.inl i)) =>
      adqProj X u p θ Q (crd1 X p θ Q (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)))
  | Sum.inr (Sum.inl (Sum.inr _)) => crd1 X p θ Q (adqZ X u p)
  | Sum.inr (Sum.inr c) => crd1 X p θ Q (adqF X p (Fin.rev c))

theorem adq_col_cong (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q)) (t s : IdxD D) :
    InG X p (adqCol X hb u p θ Q t s - crd1 X p θ Q (adqRef X hb u p t) s) := by
  rcases t with a | ((i | v) | c)
  · exact firstCoords_congruent_mod X p θ Q hL _ _ (adq_e_cong X hb u p a) s
  · set y := crd1 X p θ Q (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) with hy
    have hyi : ∀ j, y j ∈ OvA X p := fun j => ((latCrd_of X p θ Q hL _).1 (adq_ref_lat X hb u p (MassDataIdxStIm.wI i))).1 j
    have hca : ∀ a, InG X p (crd2 X p θ Q (adqE X p a) ⬝ᵥ y) := by
      intro a
      have h1 := adq_dotG X p (a := crd2 X p θ Q (adqE X p a)) (a' := crd2 X p θ Q (adqRef X hb u p (Sum.inl a)))
        (b := y) (b' := y) (fun j => ((latCrd_of X p θ Q hL _).1 (adq_ref_lat X hb u p _)).2 j) hyi
        (secondCoords_congruent_mod X p θ Q hL _ _ (adq_e_cong X hb u p a)) (fun j => by rw [sub_self]; exact inG_zero)
      have h2 : crd2 X p θ Q (adqRef X hb u p (Sum.inl a)) ⬝ᵥ y =
          crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.e0 a)) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw i)) :=
        adq_pairM X hb u p θ Q hθ _ _
      obtain ⟨z, hz⟩ := fin_dir X p θ Q hθ hL _ _ ((X.weightVectorsIntegral i).2.2 a).1
      rw [h2, hz] at h1
      have h3 := inG_add h1 (inG_g_mul (X := X) (p := p) z)
      rwa [sub_add_cancel] at h3
    have hcz : InG X p (crd2 X p θ Q (adqZ X u p) ⬝ᵥ y) := by
      have h1 := adq_dotG X p (a := crd2 X p θ Q (adqZ X u p)) (a' := crd2 X p θ Q (adqRef X hb u p zI))
        (b := y) (b' := y) (fun j => ((latCrd_of X p θ Q hL _).1 (adq_ref_lat X hb u p _)).2 j) hyi
        (secondCoords_congruent_mod X p θ Q hL _ _ (adq_z_cong X hb u p)) (fun j => by rw [sub_self]; exact inG_zero)
      have h2 : crd2 X p θ Q (adqRef X hb u p zI) ⬝ᵥ y =
          crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw i)) :=
        adq_pairM X hb u p θ Q hθ _ _
      obtain ⟨z, hz⟩ := fin_dir X p θ Q hθ hL _ _ (X.weightVectorsIntegral i).1
      rw [h2, hz] at h1
      have h3 := inG_add h1 (inG_g_mul (X := X) (p := p) z)
      rwa [sub_add_cancel] at h3
    have hti := (adq_tau_inv X hb u p θ Q hθ hL).1
    have e : adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inl i))) s -
        crd1 X p θ Q (adqRef X hb u p (Sum.inr (Sum.inl (Sum.inl i)))) s =
        0 - (∑ a, (crd2 X p θ Q (adqE X p a) ⬝ᵥ y) * crd1 X p θ Q (adqF X p a) s +
          (crd1 X p θ Q (adqZ X u p) s * (adqTau X u p θ Q)⁻¹) * (crd2 X p θ Q (adqZ X u p) ⬝ᵥ y)) := by
      show adqProj X u p θ Q y s - y s = _
      simp only [adqProj, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    refine inG_sub inG_zero (inG_add (inG_sum _ _ fun a _ => ?_) (inG_mul_int _ ?_ hcz))
    · rw [mul_comm]
      exact inG_mul_int _ (((latCrd_of X p θ Q hL _).1 (adq_F_lat X hb u p a)).1 s) (hca a)
    · exact (OvA X p).mul_mem _ _ (((latCrd_of X p θ Q hL _).1 (adq_Z_lat X hb u p)).1 s) hti
  · exact firstCoords_congruent_mod X p θ Q hL _ _ (adq_z_cong X hb u p) s
  · exact firstCoords_congruent_mod X p θ Q hL _ _ (adq_f_cong X hb u p (Fin.rev c)) s

theorem adq_col_int (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q)) (t s : IdxD D) :
    adqCol X hb u p θ Q t s ∈ OvA X p := by
  have h1 := adq_inG_int (X := X) (p := p) (adq_col_cong X hb u p θ Q hθ hL t s)
  have h2 := ((latCrd_of (X := X) (p := p) (θ := θ) (Q := Q) hL _).mp (adq_ref_lat X hb u p t)).1 s
  have h3 := add_mem h1 h2
  rwa [sub_add_cancel] at h3

def adqC : Matrix (IdxD D) (IdxD D) (FpX X p) := fun i t => adqCol X hb u p θ Q t i

def adqR : Matrix (IdxD D) (IdxD D) (FpX X p) :=
  fun s i => sgnV X p s * crd2 X p θ Q (adqRefR X hb u p s) i

theorem adq_RC (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p Q))
    (s t : IdxD D) : ∃ z : OvA X p, (adqR X hb u p θ Q * adqC X hb u p θ Q) s t =
      (1 : Matrix (IdxD D) (IdxD D) (FpX X p)) s t + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  have e1 : (adqR X hb u p θ Q * adqC X hb u p θ Q) s t =
      sgnV X p s * (crd2 X p θ Q (adqRefR X hb u p s) ⬝ᵥ adqCol X hb u p θ Q t) := by
    simp only [Matrix.mul_apply, adqR, adqC, dotProduct, Finset.mul_sum, mul_assoc]
  have hD := adq_dotG X p (a := crd2 X p θ Q (adqRefR X hb u p s)) (a' := crd2 X p θ Q (adqRefR X hb u p s))
    (b := adqCol X hb u p θ Q t) (b' := crd1 X p θ Q (adqRef X hb u p t))
    (fun j => ((latCrd_of X p θ Q hL _).1 (adq_refR_lat X hb u p s)).2 j)
    (fun j => adq_col_int X hb u p θ Q hθ hL t j) (fun j => by rw [sub_self]; exact inG_zero)
    (fun j => adq_col_cong X hb u p θ Q hθ hL t j)
  rw [adq_pairM X hb u p θ Q hθ] at hD
  obtain ⟨y, hy⟩ := inG_mul_int _ (sgnV_int X p s) hD
  obtain ⟨z, hz⟩ := rc_cong X p θ Q hθ hε hL s t
  refine ⟨y + z, ?_⟩
  rw [e1]
  push_cast
  linear_combination hy + hz

theorem adq_gl (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p Q)) :
    ∃ c : GL (IdxD D) (OvA X p),
      ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) = adqC X hb u p θ Q := by
  choose N hN using fun s t => adq_RC X hb u p θ Q hθ hε hL s t
  have hgc : ((gA X p : OvA X p) : FpX X p) = ((gOf p : ℕ) : FpX X p) := by simp [gA]
  have hRC : adqR X hb u p θ Q * adqC X hb u p θ Q =
      1 + ((gA X p : OvA X p) : FpX X p) • Matrix.of (fun s t => ((N s t : OvA X p) : FpX X p)) := by
    ext s t
    rw [hN s t, hgc]
    simp
  obtain ⟨c, hc⟩ := exists_gl_of_left_inv (OvA X p) (gA X p) (PIW.MassDataColumns.gOf_nonunit X p)
    (adqC X hb u p θ Q) (adqR X hb u p θ Q) _
    (fun i t => adq_col_int X hb u p θ Q hθ hL t i)
    (fun s i => (OvA X p).mul_mem _ _ (sgnV_int X p s) (((latCrd_of X p θ Q hL _).1 (adq_refR_lat X hb u p s)).2 i))
    (fun s t => (N s t).2) hRC
  exact ⟨c, by rw [glK_val]; exact hc⟩

end Loc

end MassDataIdxSteps
