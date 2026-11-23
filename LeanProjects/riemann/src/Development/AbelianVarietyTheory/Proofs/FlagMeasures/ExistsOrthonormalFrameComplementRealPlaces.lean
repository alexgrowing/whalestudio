import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameComplementChangeOfBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.CFrame

theorem hJ_rv_gen (I : AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hPi : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hJv : I.J.map (I.φ v) = ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ := by
    rw [← I.P_spec v]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hPi, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hPi, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold hJ rv
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hJv]
  simp only [dotProduct, mulVec, Pi.star_apply, Matrix.map_apply, Formalism.UG.hform, map_sum, map_mul,
    starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [I.cm.cmUnram.2.1]
  simp only [RCLike.star_def]
  ring

theorem hform_cols {A : Type} [CommRing A] {n ι : Type} [Fintype n] [Fintype ι] (σ : A →+* A)
    (J : Matrix n n A) (Q : Matrix n ι A) (α β : ι) :
    Formalism.UG.hform σ J (fun i => Q i α) (fun i => Q i β) = ((Q.map σ)ᵀ * J * Q) α β := by
  simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

variable {D : D7} (X : HidaSetting D)

theorem hJ_crd' (v : InfinitePlace X.B.I.F) (a b : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd a)) (rv X.B.I v (X.crd b)) = X.B.I.φ v (X.ιE.symm ((VS D).hT a b)) := by
  rw [hJ_rv_gen, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X a b, RingEquiv.symm_apply_apply]

theorem card_eq : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  rw [X.n_eq]
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

end GlobalTheory.St.CFrame

namespace GlobalTheory.St.CFrame

variable {D : D7} (X : HidaSetting D)

theorem gram_blocks (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hw : WittX X u wt) :
    (∀ v a b, hJ (X.B.I.ε v) (rvV X v (qFr wt a)) (rvV X v (qFr wt b)) =
        X.B.I.φ v (X.ιE.symm (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) a b))) ∧
    (∀ v c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (rvV X v (qFr wt a)) = 0 ∧
        hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (rvV X v (qFr wt a)) = 0) ∧
    (∀ v a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rvV X v (qFr wt a)) = 0) ∧
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hz, _, hblk⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hent : ∀ α β, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (fun i => Q i α) (fun i => Q i β) =
      Matrix.fromBlocks ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm) 0 0 G' α β := by
    intro α β
    rw [hform_cols, hblk]
  have colq : ∀ j, (fun i => Q i (Sum.inl j)) = X.crd (qFr wt j) := fun j => funext fun i => hq j i
  have cole : ∀ a, (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := fun a => funext fun i => he a i
  have colf : ∀ a, (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := fun a => funext fun i => hf a i
  have colz : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hz i
  refine ⟨fun v a b => ?_, fun v c a => ⟨?_, ?_⟩, fun v a => ?_, ?_⟩
  · have h := hent (Sum.inl a) (Sum.inl b)
    rw [colq, colq] at h
    rw [rvV, rvV, hJ_rv_gen, h]
    rfl
  · have h := hent (Sum.inr (Sum.inl c)) (Sum.inl a)
    rw [cole, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · have h := hent (Sum.inr (Sum.inr (Sum.inl c))) (Sum.inl a)
    rw [colf, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · have h := hent (Sum.inr (Sum.inr (Sum.inr ()))) (Sum.inl a)
    rw [colz, colq] at h
    rw [rvV, hJ_rv_gen, h]
    simp
  · intro h0
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.2 X.B.I.J_det
    have e1 : (Q.map (starRingEnd X.B.I.E))ᵀ * (Qi.map (starRingEnd X.B.I.E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hinv : ((Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q) *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J X.B.I.J⁻¹,
        Matrix.mul_nonsing_inv _ hJu, Matrix.one_mul, e1]
    rw [hblk] at hinv
    have hd := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one] at hd
    have hA : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det = 0 := by
      rw [show ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).det =
          X.ιE.symm.toRingHom (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).det from
          (RingHom.map_det X.ιE.symm.toRingHom _).symm, h0, map_zero]
    rw [hA, zero_mul, zero_mul] at hd
    exact zero_ne_one hd

end GlobalTheory.St.CFrame

namespace GlobalTheory.St.CFrame

theorem frame_of_type : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ o : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), (∀ τ, (o.1 τ)ᴴ * Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) τ * o.1 τ = 1) ∧ ∀ s ∈ Hinf X u, ∃ m : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ, ∀ τ, m τ ∈ Matrix.unitaryGroup (Fin (D.R.N 0)) ℂ ∧ (m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm) = matW X.B.I (X.wfr u (X.pl.symm τ)) (X.pl.symm τ) s ∧ sTil X wt s τ = o.1 τ * m τ * (o.1 τ)⁻¹ := by
  intro D X u wt hw
  obtain ⟨hqq, hqef, hqz, hdet⟩ := gram_blocks X u wt hw
  have hgQ : ∀ v, gramQ X wt v = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (Formalism.L2.Forms.embT D (X.pl v)) := by
    intro v
    ext a b
    simp only [gramQ, Matrix.of_apply, Matrix.map_apply]
    rw [hqq, X.φ_eq, RingEquiv.apply_symm_apply]
    rfl
  have hGu : ∀ v, IsUnit (gramQ X wt v).det := by
    intro v
    rw [hgQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hdet)
  have hJm : ∀ v, IsUnit (Formalism.REAL.Jm (X.B.I.ε v)).det :=
    fun v => Matrix.isUnit_det_of_left_inverse (Formalism.REAL.Jm_mul_self _)
  have key := fun v => GlobalTheory.frame_complement_change_of_basis X.B.I.n D.R.rS D.R.k (D.R.N 0) D.R.N_zero.symm (Formalism.REAL.Jm (X.B.I.ε v))
    (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v)
    (fun a => rvV X v (qFr wt a)) (card_eq X) (Formalism.REAL.Jm_conjTranspose _) (hJm v)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.eX a) (X.eX b)).trans ?_
      rw [X.ee]; simp)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.fY a) (X.fY b)).trans ?_
      rw [X.ff]; simp)
    (fun a b => by
      show hJ (X.B.I.ε v) _ _ = _
      refine (hJ_crd' X v (X.eX a) (X.fY b)).trans ?_
      rw [X.ef]; split_ifs <;> simp)
    (fun a => ⟨by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.eX a) (X.zu u)).trans ?_
      rw [(X.zu_orth u a).1]; simp, by
      show hJ (X.B.I.ε v) _ _ = 0
      refine (hJ_crd' X v (X.fY a) (X.zu u)).trans ?_
      rw [(X.zu_orth u a).2]; simp⟩)
    (by
      show hJ (X.B.I.ε v) _ _ ≠ 0
      refine (hJ_crd' X v (X.zu u) (X.zu u)).trans_ne ?_
      rw [X.zu_norm]
      have hT : (((D.mem u).A.T : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
      simpa using hT)
    (X.wfr_on u v) (X.wfr_perp u v)
    (fun a => ⟨fun c => ⟨(hqef v c a).1, (hqef v c a).2⟩, hqz v a⟩)
    (gramQ X wt v) (fun a b => rfl) (hGu v)
  choose oo hoo using key
  refine ⟨⟨fun τ => oo (X.pl.symm τ), fun τ => (hoo _).1⟩, fun τ => ?_, fun s hs => ?_⟩
  · have h := (hoo (X.pl.symm τ)).2.1
    rw [hgQ, Equiv.apply_symm_apply] at h
    exact h
  · have hfix : ∀ v, ∀ x ∈ fixSet X u, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v x := hs
    have hm := fun τ => (hoo (X.pl.symm τ)).2.2 (uMat (s (X.pl.symm τ))) (s (X.pl.symm τ)).2
      (fun a => ⟨hfix _ _ (Or.inl (Or.inl ⟨a, rfl⟩)), hfix _ _ (Or.inl (Or.inr ⟨a, rfl⟩))⟩)
      (hfix _ _ (Or.inr rfl))
    choose m hmU hmW hmT using hm
    exact ⟨m, fun τ => ⟨hmU τ, hmW τ, hmT τ⟩⟩

end GlobalTheory.St.CFrame
