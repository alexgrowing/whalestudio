import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddedGroupMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section cont

variable {k p ρ : ℕ}

theorem psi_contM {r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Continuous (fun g : B.Mat k r => psi k r z c g) := by
  have hl : Continuous fun g : B.Mat k r => ell k r z g := Formalism.FourierDecayAlt.P.B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

theorem lowW_cont (σ : Equiv.Perm (Fin p)) : Continuous (fun v : U.LW σ → ℂ => U.lowW σ v) := by
  unfold U.lowW
  refine continuous_const.add ?_
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem lhOf_cont (σ : Equiv.Perm (Fin p)) : Continuous (fun v : U.LW σ → ℂ => lhOf σ v) := by
  unfold lhOf
  exact (continuous_const.matrix_mul (lowW_cont σ)).matrix_mul continuous_const

theorem subS_cont : Continuous (fun M : Matrix (Fin p) (Fin p) ℂ => U.subS M) := by
  unfold U.subS
  refine continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const

theorem supS_cont : Continuous (fun M : Matrix (Fin p) (Fin p) ℂ => U.supS M) := by
  unfold U.supS
  refine continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const

theorem cornerA_cont {s : ℕ} : Continuous (fun a : Fin s → Fin p → ℂ => U.cornerA a) := by
  unfold U.cornerA
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const

theorem cornerB_cont {s : ℕ} : Continuous (fun b : Fin p → Fin s → ℂ => U.cornerB b) := by
  unfold U.cornerB
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const

theorem psiStar_cont (σ : Equiv.Perm (Fin p)) (z0 z0' : Fin (2 * (p + ρ) + k + 1) → ℂ) :
    Continuous (fun ξ : U.Xi k p 0 ρ σ => U.psiStar k ρ σ z0 z0' ξ) := by
  unfold U.psiStar U.psiH
  have hR := Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) (p + 0) ρ
  refine ((psi_contM z0 cStd).comp (hR.comp (continuous_fst.comp continuous_fst))).mul
    (continuous_star.comp ((psi_contM z0' cStd).comp (hR.comp (continuous_snd.comp continuous_fst)))) |>.mul ?_
  refine (Formalism.FourierDecayAlt.P.G7.continuous_psi _).comp ?_
  refine ((?_ : Continuous _).add ?_).add ?_ |>.add ?_
  · exact subS_cont.comp ((continuous_const.matrix_mul ((lowW_cont σ).comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd)))).matrix_mul continuous_const)
  · exact supS_cont.comp (Formalism.FourierDecayAlt.P.Dx2.SplitM.continuous_upper.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  · exact cornerA_cont.comp (continuous_fst.comp (continuous_fst.comp continuous_snd))
  · exact cornerB_cont.comp (continuous_snd.comp (continuous_fst.comp continuous_snd))

end cont

section gaxi

variable {k p ρ : ℕ}

theorem zjH_eq (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : U.XiH p 0 σ) (Z : G.Mat 0) :
    U.ZjH σ d η Z = lhOf σ η.2.1 * U.hMat σ d * G.upper η.2.2 := by
  rw [lower_corner_hermitian_zero, (head_hermitian_eq p σ d η.2.1 η.2.2).1]

theorem zjH_cont (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (Z : G.Mat 0) :
    Continuous (fun η : U.XiH p 0 σ => U.ZjH σ d η Z) := by
  simp only [zjH_eq]
  exact ((lhOf_cont σ).comp (continuous_fst.comp continuous_snd)).matrix_mul continuous_const |>.matrix_mul
    (Formalism.FourierDecayAlt.P.Dx2.SplitM.continuous_upper.comp (continuous_snd.comp continuous_snd))

theorem zjH_det (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : U.XiH p 0 σ) (Z : G.Mat 0) :
    (U.ZjH σ d η Z).det = (U.hMat σ d).det := by
  rw [Formalism.FourierDecayAlt.P.level_determinant_z, detM_zero, mul_one]

theorem zjH_inv_cont (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (Z : G.Mat 0) :
    Continuous (fun η : U.XiH p 0 σ => (U.ZjH σ d η Z)ᴴ⁻¹) := by
  have e : (fun η : U.XiH p 0 σ => (U.ZjH σ d η Z)ᴴ⁻¹) =
      fun η => Ring.inverse (star (U.hMat σ d).det) • ((U.ZjH σ d η Z)ᴴ).adjugate := by
    funext η
    rw [Matrix.inv_def, Matrix.det_conjTranspose, zjH_det]
  rw [e]
  exact Continuous.const_smul (c := Ring.inverse (star (U.hMat σ d).det)) ((zjH_cont σ d Z).matrix_conjTranspose.matrix_adjugate)

theorem mMap_cont {X : Type*} [TopologicalSpace X] {f fi : X → Matrix (Fin p) (Fin p) ℂ} {γ : X → B.Mat k ρ}
    (hf : Continuous f) (hfi : Continuous fi) (he : ∀ x, fi x = (f x)ᴴ⁻¹) (hγ : Continuous γ) :
    Continuous (fun x => U.mMap k p ρ (f x) (γ x)) := by
  have e : (fun x => U.mMap k p ρ (f x) (γ x)) =
      fun x => U.blk3 0 0 (fi x * G.wMat p) 0 (γ x) 0 (G.wMat p * f x) 0 0 := by
    funext x; rw [he]; rfl
  rw [e]
  exact Formalism.FourierDecayAlt.P.Dx2.SplitF.continuous_block3_matrix continuous_const continuous_const (hfi.matrix_mul continuous_const)
    continuous_const hγ continuous_const (continuous_const.matrix_mul hf) continuous_const continuous_const

theorem gaXi_cont2 (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (Z : G.Mat 0) :
    Continuous (fun q : U.Xi k p 0 ρ σ × B.Mat k ρ => U.gaXi k ρ σ d q.1 Z q.2) := by
  have hR := Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) (p + 0) ρ
  have e : (fun q : U.Xi k p 0 ρ σ × B.Mat k ρ => U.gaXi k ρ σ d q.1 Z q.2) =
      fun q => U.Rn k (p + 0) ρ (-q.1.1.1) * U.mMap k (p + 0) ρ (U.ZjH σ d q.1.2 Z) q.2 * U.Rn k (p + 0) ρ q.1.1.2 := by
    funext q
    rw [U.gaXi, Formalism.FourierDecayAlt.P.PBM.rn_inv]
  rw [e]
  refine ((hR.comp (continuous_neg.comp (continuous_fst.comp (continuous_fst.comp continuous_fst)))).matrix_mul ?_).matrix_mul
    (hR.comp (continuous_snd.comp (continuous_fst.comp continuous_fst)))
  exact mMap_cont ((zjH_cont σ d Z).comp (continuous_snd.comp continuous_fst))
    ((zjH_inv_cont σ d Z).comp (continuous_snd.comp continuous_fst)) (fun _ => rfl) continuous_snd

theorem gaXi_dom (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0)
    {γ : B.Mat k ρ} (hγ : γ ∈ B.GV k ρ) :
    U.gaXi k ρ σ d ξ Z γ ∈ {x : B.Mat k (p + 0 + ρ) | x ∈ B.GV k (p + 0 + ρ) ∧ U.DjU k (p + 0) ρ x ≠ 0} := by
  refine ⟨Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ Z
    (by rw [detM_zero]; exact one_ne_zero) hγ, ?_⟩
  rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, detM_zero, mul_one]
  exact Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

end gaxi

section m4

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gaXi_contξ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (Z : G.Mat 0) (γ : B.Mat k ρ) :
    Continuous (fun ξ : U.Xi k p 0 ρ σ => U.gaXi k ρ σ d ξ Z γ) := by
  have h0 := gaXi_cont2 (k := k) (ρ := ρ) σ d Z
  have hc : Continuous (fun ξ : U.Xi k p 0 ρ σ => (ξ, γ)) := by fun_prop
  exact Continuous.comp (g := fun q : U.Xi k p 0 ρ σ × B.Mat k ρ => U.gaXi k ρ σ d q.1 Z q.2)
    (f := fun ξ : U.Xi k p 0 ρ σ => (ξ, γ)) h0 hc

theorem slice_int_cont' (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0})
    (z0 z0' : Fin (2 * (p + ρ) + k + 1) → ℂ) (Z : G.Mat 0) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) :
    Continuous (fun ξ : U.Xi k p 0 ρ σ => U.psiStar k ρ σ z0 z0' ξ • H (U.gaXi k ρ σ d ξ Z γ)) := by
  have h2 : Continuous (fun ξ : U.Xi k p 0 ρ σ => H (U.gaXi k ρ σ d ξ Z γ)) :=
    ContinuousOn.comp_continuous hHc (gaXi_contξ σ d Z γ) (fun ξ => gaXi_dom σ d hd ξ Z hγ)
  exact (psiStar_cont σ z0 z0').smul h2

theorem slice_int_cont (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0})
    (z0 z0' : Fin (2 * (p + ρ) + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) :
    Continuous (fun ξ : U.Xi k p 0 ρ σ => U.psiStar k ρ σ z0 z0' ξ • H (U.gaXi k ρ σ d ξ (fun a => a.elim0) γ)) :=
  slice_int_cont' σ d hd H hHc z0 z0' _ γ hγ

end m4

section m12

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem sgs_GV {Bs : B.RealPlaceData k ρ Wp Wq} {P : B.SS k ρ} (hP : Bs.inSS P) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) :
    B.sgs P g ∈ B.GV k ρ := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k ρ
  unfold B.sgs
  refine hG.mul_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.mul_mem _ ?_ _ ?_) _ hg) _ ?_) _ ?_
  · exact hG.inv_mem _ (Formalism.FourierDecayAlt.P.B6.UWset_sub k ρ _ hP.1)
  · exact hG.inv_mem _ (Formalism.FourierDecayAlt.P.B6.Nset_sub k ρ hP.2.1)
  · exact Formalism.FourierDecayAlt.P.B6.Nset_sub k ρ hP.2.2.2
  · exact Formalism.FourierDecayAlt.P.B6.UWset_sub k ρ _ hP.2.2.1

theorem isClosed_inSS (Bs : B.RealPlaceData k ρ Wp Wq) : IsClosed {P : B.SS k ρ | Bs.inSS P} := by
  have hWc := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bs.z).closed
  have hWc' := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bs.z').closed
  have hNc := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).closed
  have e : {P : B.SS k ρ | Bs.inSS P} = (fun p : B.SS k ρ => (p.1.1 : B.Mat k ρ)) ⁻¹' (UWset k ρ Bs.z) ∩
      ((fun p : B.SS k ρ => (p.1.2 : B.Mat k ρ)) ⁻¹' (Nset k ρ) ∩
        ((fun p : B.SS k ρ => (p.2.1 : B.Mat k ρ)) ⁻¹' (UWset k ρ Bs.z') ∩
          (fun p : B.SS k ρ => (p.2.2 : B.Mat k ρ)) ⁻¹' (Nset k ρ))) := by
    ext p; rfl
  rw [e]
  exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
    ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))

theorem sgs_contOn (Bs : B.RealPlaceData k ρ Wp Wq) (g : B.Mat k ρ) :
    ContinuousOn (fun P : B.SS k ρ => B.sgs P g) {P | Bs.inSS P} := by
  have hinv1 : ContinuousOn (fun p : B.SS k ρ => (Matrix.of p.1.1 : B.Mat k ρ)⁻¹) {P | Bs.inSS P} :=
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k ρ).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k ρ => (Matrix.of p.1.2 : B.Mat k ρ)⁻¹) {P | Bs.inSS P} :=
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k ρ).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hc4 : ContinuousOn (fun p : B.SS k ρ => (Matrix.of p.2.2 : B.Mat k ρ)) {P | Bs.inSS P} :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k ρ => (Matrix.of p.2.1 : B.Mat k ρ)) {P | Bs.inSS P} :=
    (continuous_snd.fst).continuousOn
  exact (((hinv1.mul hinv2).mul continuousOn_const).mul hc4).mul hc5

theorem continuous_xi₂ (Bs : B.RealPlaceData k ρ Wp Wq) : Continuous (fun P : B.SS k ρ => JF.xiP Bs P) := by
  unfold JF.xiP
  exact ((psi_contM Bs.z cStd).comp continuous_fst.snd).mul
    (continuous_star.comp ((psi_contM Bs.z' cStd).comp continuous_snd.snd))

theorem fl_aesm (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0})
    (g : B.Mat k ρ) (hg : g ∈ B.GV k ρ) :
    AEStronglyMeasurable (FL Bj (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') σ d H g)
      (Bj.μSS.prod (U.muXi k p 0 ρ σ)) := by
  set S : Set (B.SS k ρ × U.Xi k p 0 ρ σ) := {q | Bj.inSS q.1} with hSdef
  have hS : IsClosed S := (isClosed_inSS Bj).preimage continuous_fst
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have hae : ∀ᵐ q ∂(Bj.μSS.prod (U.muXi k p 0 ρ σ)), q ∈ S :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS Bj)
  have hsgs : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => B.sgs q.1 g) S :=
    (sgs_contOn Bj g).comp continuous_fst.continuousOn (fun q hq => hq)
  have hpair : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => (q.2, B.sgs q.1 g)) S :=
    continuous_snd.continuousOn.prodMk hsgs
  have hga : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => U.gaXi k ρ σ d q.2 (fun a => a.elim0) (B.sgs q.1 g)) S :=
    ContinuousOn.comp (g := fun r : U.Xi k p 0 ρ σ × B.Mat k ρ => U.gaXi k ρ σ d r.1 (fun a => a.elim0) r.2)
      (f := fun q : B.SS k ρ × U.Xi k p 0 ρ σ => (q.2, B.sgs q.1 g))
      (gaXi_cont2 σ d _).continuousOn hpair (Set.mapsTo_univ _ _)
  have hH : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ =>
      H (U.gaXi k ρ σ d q.2 (fun a => a.elim0) (B.sgs q.1 g))) S :=
    ContinuousOn.comp (g := H) (f := fun q : B.SS k ρ × U.Xi k p 0 ρ σ =>
      U.gaXi k ρ σ d q.2 (fun a => a.elim0) (B.sgs q.1 g)) hHc hga
      (fun q hq => gaXi_dom σ d hd q.2 _ (sgs_GV hq hg))
  have hps : Continuous (fun q : B.SS k ρ × U.Xi k p 0 ρ σ =>
      U.psiStar k ρ σ (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') q.2) :=
    (psiStar_cont σ _ _).comp continuous_snd
  have hc1' : Continuous (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => q.1.1.1) := continuous_fst.fst.fst
  have hc3' : Continuous (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => q.1.2.1) := continuous_fst.snd.fst
  have hc1 : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => (Matrix.of q.1.1.1 : B.Mat k ρ)) S :=
    hc1'.continuousOn
  have hc3 : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => (Matrix.of q.1.2.1 : B.Mat k ρ)) S :=
    hc3'.continuousOn
  have hπ : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => Bj.π (Matrix.of q.1.1.1)) S :=
    ContinuousOn.comp (g := Bj.π) (f := fun q : B.SS k ρ × U.Xi k p 0 ρ σ => (Matrix.of q.1.1.1 : B.Mat k ρ))
      Bj.π_cont hc1 (fun q hq => hq.1)
  have hinv3 : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => (Matrix.of q.1.2.1 : B.Mat k ρ)⁻¹) S :=
    ContinuousOn.comp (g := fun g : B.Mat k ρ => g⁻¹)
      (f := fun q : B.SS k ρ × U.Xi k p 0 ρ σ => (Matrix.of q.1.2.1 : B.Mat k ρ))
      (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k ρ) hc3 (fun q hq => hq.2.2.1.1)
  have hπ' : ContinuousOn (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => Bj.π' (Matrix.of q.1.2.1 : B.Mat k ρ)⁻¹) S :=
    Bj.π'_cont.comp hinv3 (fun q hq => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hq.2.2.1)
  have hxi : Continuous (fun q : B.SS k ρ × U.Xi k p 0 ρ σ => JF.xiP Bj q.1) := (continuous_xi₂ Bj).comp continuous_fst
  have hcont : ContinuousOn (FL Bj (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') σ d H g) S := by
    unfold FL
    exact hxi.continuousOn.smul (hπ.clm_comp ((hps.continuousOn.smul hH).clm_comp hπ'))
  have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
  have : BorelSpace (B.SS k ρ) := Prod.borelSpace
  have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ × U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) := Prod.borelSpace
  have : BorelSpace ((U.LW σ → ℂ) × (G.UT p → ℂ)) := Prod.borelSpace
  have : BorelSpace (U.XiH p 0 σ) := Prod.borelSpace
  have : BorelSpace (U.Xi k p 0 ρ σ) := Prod.borelSpace
  have : BorelSpace (B.SS k ρ × U.Xi k p 0 ρ σ) := Prod.borelSpace
  have h1 := hcont.aestronglyMeasurable (μ := Bj.μSS.prod (U.muXi k p 0 ρ σ)) hS.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

end m12

section m2

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def xiOf (σ : Equiv.Perm (Fin p)) (q : XL k p ρ σ × XR k p ρ) : U.Xi k p 0 ρ σ :=
  ((q.1.2.1, q.2.2.1), (q.1.2.2.1, (q.1.2.2.2, q.2.2.2)))

def ssOf (σ : Equiv.Perm (Fin p)) (q : XL k p ρ σ × XR k p ρ) : B.SS k ρ := (q.1.1, q.2.1)

theorem xiOf_cont (σ : Equiv.Perm (Fin p)) : Continuous (xiOf (k := k) (ρ := ρ) σ) := by
  unfold xiOf; fun_prop

theorem ssOf_cont (σ : Equiv.Perm (Fin p)) : Continuous (ssOf (k := k) (ρ := ρ) σ) := by
  unfold ssOf; fun_prop

theorem NR_cont : Continuous (fun y : XR k p ρ => NR y) := by
  unfold NR
  have h1 : Continuous (fun y : XR k p ρ => U.embG k p ρ (Matrix.of y.1.2)) :=
    (Formalism.FourierDecayAlt.P.Dx2.SplitF.embg_cont (k := k) p ρ).comp continuous_fst.snd
  have h2 : Continuous (fun y : XR k p ρ => U.muP k p ρ (G.upper y.2.2)) :=
    (Formalism.FourierDecayAlt.P.Dx2.SplitF.mup_cont (k := k) p ρ).comp continuous_snd.snd
  have h3 : Continuous (fun y : XR k p ρ => U.Rn k p ρ (rcAct (Matrix.of y.1.1) y.2.1)) :=
    (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont (k := k) p ρ).comp
      (Continuous.comp (g := fun r : Mt k ρ × U.RC k p ρ => rcAct (Matrix.of r.1) r.2)
        (f := fun y : XR k p ρ => (y.1.1, y.2.1)) rcAct_cont (by fun_prop))
  exact (h1.matrix_mul h2).matrix_mul h3

theorem aestronglyMeasurable_germ_integrand (hGS : GaXiSplit) (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hz' : B0.z' = liftVec k p ρ Bj.z') (hπ' : ∀ y, Bj.π' y = B0.π' (U.embG k p ρ y))
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0})
    (g : B.Mat k ρ) (hg : g ∈ B.GV k ρ) :
    AEStronglyMeasurable (fun q : XL k p ρ σ × XR k p ρ =>
      KrI B0 H (sxL Bj σ q.1 * U.mMap k p ρ (U.hMat σ d) g) (PsiR q.2)) ((muL Bj σ).prod (muR Bj)) := by
  set S : Set (XL k p ρ σ × XR k p ρ) := {q | Bj.inSS (ssOf σ q)} with hSdef
  have hS : IsClosed S := (isClosed_inSS Bj).preimage (ssOf_cont σ)
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have hae : ∀ᵐ q ∂((muL Bj σ).prod (muR Bj)), q ∈ S := by
    have a1 : ∀ᵐ x : XL k p ρ σ ∂(muL Bj σ), (Matrix.of x.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z ∧
        (Matrix.of x.1.2 : B.Mat k ρ) ∈ QuantumDeterminants.Nset k ρ := by
      have b : ∀ᵐ y : Mt k ρ × Mt k ρ ∂(Bj.μW.prod Bj.μN), (Matrix.of y.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z ∧
          (Matrix.of y.2 : B.Mat k ρ) ∈ QuantumDeterminants.Nset k ρ :=
        (Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarW)).and
          (Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarN))
      exact (Measure.quasiMeasurePreserving_fst (μ := Bj.μW.prod Bj.μN)
        (ν := (U.muRC k p ρ).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
          (volume : Measure (U.LW σ → ℂ))))).ae b
    have a2 : ∀ᵐ y : XR k p ρ ∂(muR Bj), (Matrix.of y.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z' ∧
        (Matrix.of y.1.2 : B.Mat k ρ) ∈ QuantumDeterminants.Nset k ρ := by
      have b : ∀ᵐ y : Mt k ρ × Mt k ρ ∂(Bj.μW'.prod Bj.μN), (Matrix.of y.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z' ∧
          (Matrix.of y.2 : B.Mat k ρ) ∈ QuantumDeterminants.Nset k ρ :=
        (Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarW')).and
          (Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bj.haarN))
      exact (Measure.quasiMeasurePreserving_fst (μ := Bj.μW'.prod Bj.μN)
        (ν := (U.muRC k p ρ).prod (volume : Measure (G.UT p → ℂ)))).ae b
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae a1, Measure.quasiMeasurePreserving_snd.ae a2] with q h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩

  set A : XL k p ρ σ × XR k p ρ → B.Mat k (p + ρ) := fun q =>
    U.gaXi k ρ σ d (xiOf σ q) (fun a => a.elim0) (B.sgs (ssOf σ q) g) with hAdef
  have hsgs : ContinuousOn (fun q : XL k p ρ σ × XR k p ρ => B.sgs (ssOf σ q) g) S :=
    (sgs_contOn Bj g).comp (ssOf_cont σ).continuousOn (fun q hq => hq)
  have hpair : ContinuousOn (fun q : XL k p ρ σ × XR k p ρ => (xiOf σ q, B.sgs (ssOf σ q) g)) S :=
    (xiOf_cont σ).continuousOn.prodMk hsgs
  have hA : ContinuousOn A S :=
    ContinuousOn.comp (g := fun r : U.Xi k p 0 ρ σ × B.Mat k ρ => U.gaXi k ρ σ d r.1 (fun a => a.elim0) r.2)
      (f := fun q : XL k p ρ σ × XR k p ρ => (xiOf σ q, B.sgs (ssOf σ q) g))
      (gaXi_cont2 σ d _).continuousOn hpair (Set.mapsTo_univ _ _)
  have hHA : ContinuousOn (fun q => H (A q)) S :=
    ContinuousOn.comp (g := H) (f := A) hHc hA (fun q hq => gaXi_dom σ d hd (xiOf σ q) _ (sgs_GV hq hg))
  have hc3' : Continuous (fun q : XL k p ρ σ × XR k p ρ => q.2.1.1) := continuous_snd.fst.fst
  have hc3 : ContinuousOn (fun q : XL k p ρ σ × XR k p ρ => (Matrix.of q.2.1.1 : B.Mat k ρ)) S :=
    hc3'.continuousOn
  have hinv3 : ContinuousOn (fun q : XL k p ρ σ × XR k p ρ => (Matrix.of q.2.1.1 : B.Mat k ρ)⁻¹) S :=
    ContinuousOn.comp (g := fun g : B.Mat k ρ => g⁻¹)
      (f := fun q : XL k p ρ σ × XR k p ρ => (Matrix.of q.2.1.1 : B.Mat k ρ))
      (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k ρ) hc3 (fun q hq => hq.2.2.1.1)
  have hπ : ContinuousOn (fun q : XL k p ρ σ × XR k p ρ => Bj.π' (Matrix.of q.2.1.1 : B.Mat k ρ)⁻¹) S :=
    ContinuousOn.comp (g := Bj.π') (f := fun q : XL k p ρ σ × XR k p ρ => (Matrix.of q.2.1.1 : B.Mat k ρ)⁻¹)
      Bj.π'_cont hinv3 (fun q hq => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hq.2.2.1)
  have hps : Continuous (fun q : XL k p ρ σ × XR k p ρ => star (psi k (p + ρ) B0.z' cStd (NR q.2))) :=
    continuous_star.comp ((psi_contM B0.z' cStd).comp (NR_cont.comp continuous_snd))
  have hnice : ContinuousOn (fun q : XL k p ρ σ × XR k p ρ =>
      star (psi k (p + ρ) B0.z' cStd (NR q.2)) • (H (A q)).comp (Bj.π' (Matrix.of q.2.1.1 : B.Mat k ρ)⁻¹)) S :=
    hps.continuousOn.smul (hHA.clm_comp hπ)
  have heq : ∀ q ∈ S, KrI B0 H (sxL Bj σ q.1 * U.mMap k p ρ (U.hMat σ d) g) (PsiR q.2) =
      star (psi k (p + ρ) B0.z' cStd (NR q.2)) • (H (A q)).comp (Bj.π' (Matrix.of q.2.1.1 : B.Mat k ρ)⁻¹) := by
    intro q hq
    obtain ⟨hh, hν, hh', hν'⟩ := hq
    have uh : IsUnit (Matrix.of q.1.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z).unit _ hh
    have uν : IsUnit (Matrix.of q.1.1.2 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).unit _ hν
    have uh' : IsUnit (Matrix.of q.2.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z').unit _ hh'
    have hH' : (Matrix.of q.2.1.1 : B.Mat k ρ)ᴴ * Hpk k ρ * Matrix.of q.2.1.1 = Hpk k ρ := hh'.1
    have hpt : sxL Bj σ q.1 * U.mMap k p ρ (U.hMat σ d) g * Matrix.of (PsiR q.2).2 * Matrix.of (PsiR q.2).1 = A q := by
      have := hGS k p ρ σ d (xiOf σ q) (fun a => a.elim0) (Matrix.of q.1.1.1) (Matrix.of q.1.1.2)
        (Matrix.of q.2.1.1) (Matrix.of q.2.1.2) g uh uν hH'
      show _ = U.gaXi k ρ σ d (xiOf σ q) (fun a => a.elim0) (B.sgs (ssOf σ q) g)
      rw [show B.sgs (ssOf σ q) g = (Matrix.of q.1.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of q.1.1.2 : B.Mat k ρ)⁻¹ * g *
        Matrix.of q.2.1.2 * Matrix.of q.2.1.1 from rfl]
      symm
      convert this using 1
      simp only [sxL, if_pos (show GoodL Bj σ q.1 from ⟨hh, hν⟩), PsiR, NR, of_levMt, Equiv.apply_symm_apply]
      rfl
    have hpi : B0.π' (Matrix.of (PsiR q.2).1)⁻¹ = Bj.π' (Matrix.of q.2.1.1 : B.Mat k ρ)⁻¹ := by
      simp only [PsiR, of_levMt]
      rw [← Formalism.FourierDecayAlt.P.LeftFubiniLemmas.embG_inv uh', hπ']
    have hN : Matrix.of (PsiR q.2).2 = NR q.2 := by simp only [PsiR, Equiv.apply_symm_apply]
    unfold KrI
    rw [hpt, hpi, hN]
  have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
  have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
  have : BorelSpace ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) := Prod.borelSpace
  have : BorelSpace (((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ)) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ × (((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ))) := Prod.borelSpace
  have : BorelSpace (XL k p ρ σ) := Prod.borelSpace
  have : BorelSpace (U.RC k p ρ × (G.UT p → ℂ)) := Prod.borelSpace
  have : BorelSpace (XR k p ρ) := Prod.borelSpace
  have : BorelSpace (XL k p ρ σ × XR k p ρ) := Prod.borelSpace
  have h1 := (hnice.congr heq).aestronglyMeasurable (μ := (muL Bj σ).prod (muR Bj)) hS.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

end m2

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
