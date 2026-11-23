import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PsiVIteOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem colV_lat (t : IdxD D) :
    PI.FinKW.vecV X.B.I p.1 (colV X t) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h := X.vectorsInLattice
  have key : ∀ A ∈ X.B.I.Lf, PI.FinKW.vecV X.B.I p.1 A ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    fun A hA => PI.FinKW.LocTo.mem_local_lattice_iff X.B.I A hA p.1
  rcases t with a | ((i | _) | c)
  · exact key _ (h.1 a).1
  · exact key _ (h.2.2 i).1
  · exact key _ h.2.1
  · exact key _ (h.1 _).2

theorem rowV_lat (s : IdxD D) :
    PI.FinKW.vecV X.B.I p.1 (rowV X s) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h := X.vectorsInLattice
  have key : ∀ A ∈ X.B.I.Lf, PI.FinKW.vecV X.B.I p.1 A ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    fun A hA => PI.FinKW.LocTo.mem_local_lattice_iff X.B.I A hA p.1
  rcases s with a | ((i | _) | c)
  · exact key _ (h.1 a).2
  · exact key _ (h.2.2 i).2
  · exact key _ h.2.1
  · exact key _ (h.1 _).1

theorem sgnV_int (s : IdxD D) : sgnV X p s ∈ OvA X p := by
  unfold sgnV
  split
  · exact neg_mem (one_mem _)
  · exact one_mem _

theorem sgnV_sq (s : IdxD D) : sgnV X p s * sgnV X p s = 1 := by
  unfold sgnV
  split <;> norm_num

def matC : Matrix (IdxD D) (IdxD D) (FpX X p) := fun i t => crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X t)) i

def matR : Matrix (IdxD D) (IdxD D) (FpX X p) :=
  fun s i => sgnV X p s * crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (rowV X s)) i

theorem matR_mul_matC (s t : IdxD D) :
    (matR X p θ Q * matC X p θ Q) s t = sgnV X p s * (crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (rowV X s)) ⬝ᵥ
      crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X t))) := by
  simp only [Matrix.mul_apply, matR, matC, dotProduct, Finset.mul_sum, mul_assoc]

private theorem isUnit_of_mul_eq_one_add_smul_maximalIdeal {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A]
    [IsLocalRing A] (g : A) (hg : g ∈ IsLocalRing.maximalIdeal A) (R C Z : Matrix ι ι A)
    (h : R * C = 1 + g • Z) : IsUnit C := by
  have hm : (R * C).map (IsLocalRing.residue A) = 1 := by
    rw [h]
    ext i j
    have h0 : IsLocalRing.residue A g = 0 := (IsLocalRing.residue_eq_zero_iff g).mpr hg
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, h0,
      zero_mul, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : IsUnit (R * C).det := by
    apply IsUnit.of_map (IsLocalRing.residue A)
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_one]
    exact isUnit_one
  rw [Matrix.det_mul] at h1
  exact (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_of_mul_isUnit_right h1)

set_option maxHeartbeats 800000 in

theorem adapt_of_eps (hθ : IsSplitEquiv X p θ) (hε : θ (epsP X p) = (1, 0)) (hL : LatBasis X p θ (reindex₂ X p Q)) :
    ∃ Q' : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q') ∧ AdaptA X p θ Q' := by
  classical
  have hgA : ((gA X p : OvA X p) : FpX X p) = ((gOf p : ℕ) : FpX X p) := map_natCast (OvA X p).subtype _
  have hT : Formalism.L2.SG.TypedSets.IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) p.1 := by
    have h := p.2
    unfold Formalism.L2.SG.TypedSets.typSet at h
    split_ifs at h with hf
    · exact hf.mem_toFinset.mp h
    · simp at h
  unfold Formalism.L2.SG.TypedSets.IsTyped at hT
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    unfold Formalism.L2.SG.TypedSets.gOf
    split_ifs with h0
    · exact h0
    · exact hT.resolve_left h0
  have hlt : Valued.v ((gOf p : ℕ) : FpX X p) < 1 := by
    have h2 : ((gOf p : ℕ) : FpX X p) = (((gOf p : ℕ) : X.B.I.F) : FpX X p) := by
      first
        | exact (map_natCast (algebraMap X.B.I.F (FpX X p)) _).symm
        | exact (map_natCast (IsDedekindDomain.HeightOneSpectrum.coeRingHom p.1) _).symm
        | (norm_cast; done)
        | (simp; done)
    rw [h2, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      ← map_natCast (algebraMap (𝓞 X.B.I.F) X.B.I.F),
      IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  have hg : (gA X p : OvA X p) ∈ IsLocalRing.maximalIdeal (OvA X p) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have hv1 : Valued.v (((u⁻¹ : (OvA X p)ˣ) : OvA X p) : FpX X p) ≤ 1 := ((u⁻¹ : (OvA X p)ˣ) : OvA X p).2
    have hmul : ((gOf p : ℕ) : FpX X p) * (((u⁻¹ : (OvA X p)ˣ) : OvA X p) : FpX X p) = 1 := by
      rw [← hgA, ← hu]
      exact congrArg Subtype.val u.mul_inv
    have h3 := congrArg Valued.v hmul
    rw [map_mul, map_one] at h3
    have h4 := (mul_le_of_le_one_right' hv1).trans_lt hlt
    rw [h3] at h4
    exact lt_irrefl _ h4
  have hC : ∀ i t, matC X p θ Q i t ∈ OvA X p := fun i t =>
    ((latCrd_of (X := X) (p := p) (θ := θ) (Q := Q) hL _).mp (colV_lat X p t)).1 i
  have hR : ∀ s i, matR X p θ Q s i ∈ OvA X p := fun s i =>
    mul_mem (sgnV_int X p s) (((latCrd_of (X := X) (p := p) (θ := θ) (Q := Q) hL _).mp (rowV_lat X p s)).2 i)
  choose zf hz using fun s t => rc_cong (X := X) (p := p) (θ := θ) (Q := Q) hθ hε hL s t
  let Ci : Matrix (IdxD D) (IdxD D) (OvA X p) := fun i t => ⟨matC X p θ Q i t, hC i t⟩
  let Ri : Matrix (IdxD D) (IdxD D) (OvA X p) := fun s i => ⟨matR X p θ Q s i, hR s i⟩
  let Zi : Matrix (IdxD D) (IdxD D) (OvA X p) := fun s t => zf s t
  have eR : Ri.map (OvA X p).subtype = matR X p θ Q := by ext; rfl
  have eC : Ci.map (OvA X p).subtype = matC X p θ Q := by ext; rfl
  have hRC : Ri * Ci = 1 + (gA X p) • Zi := by
    apply Matrix.map_injective (f := (OvA X p).subtype) (fun a b hab => Subtype.ext hab)
    show (Ri * Ci).map (OvA X p).subtype = (1 + gA X p • Zi).map (OvA X p).subtype
    rw [Matrix.map_mul, eR, eC]
    have hgA' : (OvA X p).subtype (gA X p) = ((gOf p : ℕ) : FpX X p) := hgA
    refine Matrix.ext fun s t => ?_
    rw [(matR_mul_matC X p θ Q s t).trans (hz s t)]
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      Matrix.one_apply, hgA']
    split_ifs <;> simp [Zi]
  have hU : IsUnit Ci := isUnit_of_mul_eq_one_add_smul_maximalIdeal (gA X p) hg Ri Ci Zi hRC
  let c : GL (IdxD D) (OvA X p) := hU.unit
  have hcC : ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) =
      matC X p θ Q := eC
  have hcol : ∀ t, crd1 X p θ (Q * glK (OvA X p) c) (PI.FinKW.vecV X.B.I p.1 (colV X t)) = Pi.single t 1 := by
    intro t
    rw [firstCoords_mul_GL (X := X) (p := p) (θ := θ) (Q := Q)]
    have e : crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (colV X t)) =
        ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ Pi.single t 1 := by
      rw [hcC]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, matC]
    rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hrow : ∀ s t, crd2 X p θ (Q * glK (OvA X p) c) (PI.FinKW.vecV X.B.I p.1 (rowV X s)) t =
      sgnV X p s * ((1 : Matrix (IdxD D) (IdxD D) (FpX X p)) s t + ((gOf p : ℕ) : FpX X p) * (zf s t : FpX X p)) := by
    intro s t
    rw [secondCoords_mul_GL (X := X) (p := p) (θ := θ) (Q := Q), hcC, ← hz s t, ← mul_assoc, sgnV_sq X p s, one_mul]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, matC]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨Q * glK (OvA X p) c, latBasis_mulGL (X := X) (p := p) (θ := θ) (Q := Q) hL c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨0, fun _ => zero_mem _, by rw [show X.e0 a = colV X (Sum.inl a) from rfl, hcol]; simp⟩
  · exact ⟨0, fun _ => zero_mem _, by
      rw [show X.z0 = colV X zI from rfl, hcol]; simp⟩
  · intro i
    exact ⟨0, fun _ => zero_mem _, by
      rw [show X.bw i = colV X (wI i) from rfl, hcol]; simp⟩
  · intro a
    have hs : X.e0 a = rowV X (Sum.inr (Sum.inr (Fin.rev a)) : IdxD D) := by simp [rowV]
    refine ⟨fun t => zf (Sum.inr (Sum.inr (Fin.rev a))) t, fun t => (zf _ t).2, ?_⟩
    funext t
    rw [hs, hrow]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hgA, Matrix.one_apply, Pi.single_apply, sgnV]
    by_cases h : (Sum.inr (Sum.inr (Fin.rev a)) : IdxD D) = t
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  · have hs : X.z0 = rowV X zI := rfl
    refine ⟨fun t => -(zf zI t : FpX X p), fun t => neg_mem (zf zI t).2, ?_⟩
    funext t
    rw [hs, hrow]
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hgA, Matrix.one_apply, Pi.single_apply]
    have : sgnV X p zI = -1 := rfl
    rw [this]
    by_cases h : zI = t
    · subst h; simp; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  · intro i
    exact PIW.MassDataColumns.secondProj_weight_vector_zero (X := X) (p := p) (θ := θ) hε i

theorem adaptA_holds : ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q := by
  obtain ⟨θ, hθ, hε⟩ := exists_split_eps X p
  obtain ⟨Q, hQ⟩ := exists_GL_latBasis_of_isSplitEquiv X p θ hθ
  obtain ⟨Q', h1, h2⟩ := adapt_of_eps X p θ Q hθ hε hQ
  exact ⟨θ, hθ, Q', h1, h2⟩

end Loc

end MassDataIdxSteps
