import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousGrpHom
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NegDefStab

theorem jpq_zero_left (n : ℕ) : Formalism.UG.Jpq 0 n = -1 := by
  ext i j
  rcases i with i | i
  · exact i.elim0
  · rcases j with j | j
    · exact j.elim0
    · simp [Formalism.UG.Jpq, Matrix.one_apply]

theorem unitary_of_negative_definite {n m : ℕ} (e : Fin m ≃ Fin 0 ⊕ Fin n) (A : Matrix (Fin 0 ⊕ Fin n) (Fin m) ℂ)
    (Jt X : Matrix (Fin m) (Fin m) ℂ) (hJ : IsUnit Jt.det)
    (hA : A.conjTranspose * Formalism.UG.Jpq 0 n * A = Jt)
    (hX : X.conjTranspose * Jt * X = Jt) : ∃ b : Formalism.BasicNotions.UpqT 0 n, Formalism.BasicNotions.UpqT.mat b * A = A * X := by
  rw [jpq_zero_left, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul] at hA
  have hA' : A.conjTranspose * A = -Jt := by rw [← hA, neg_neg]
  have hJ' : IsUnit (-Jt).det := by
    rw [Matrix.det_neg]; exact ((isUnit_one.neg).pow _).mul hJ
  have hX' : X.conjTranspose * (-Jt) * X = -Jt := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hX]
  let L : Matrix (Fin m) (Fin 0 ⊕ Fin n) ℂ := (-Jt)⁻¹ * A.conjTranspose
  have hLA : L * A = 1 := by
    simp only [L, Matrix.mul_assoc, hA']
    exact Matrix.nonsing_inv_mul _ hJ'
  have hAL : A * L = 1 := (Matrix.mul_eq_one_comm_of_equiv (A := A) (B := L) e.symm).mpr hLA
  let bm : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ := A * X * L
  have hbb : bm.conjTranspose * bm = 1 := by
    have : bm.conjTranspose * bm = L.conjTranspose * (X.conjTranspose * (A.conjTranspose * A) * X) * L := by
      simp only [bm, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hA', hX', ← hA']
    rw [show L.conjTranspose * (A.conjTranspose * A) * L = (A * L).conjTranspose * (A * L) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [hAL, Matrix.conjTranspose_one, Matrix.one_mul]
  have hbb' : bm * bm.conjTranspose = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (A := bm.conjTranspose) (B := bm) (Equiv.refl _)).mp hbb
  let g : GL (Fin 0 ⊕ Fin n) ℂ := ⟨bm, bm.conjTranspose, hbb', hbb⟩
  have hg : g ∈ Formalism.UG.Upq 0 n := by
    show Formalism.UG.cT (starRingEnd ℂ) bm * Formalism.UG.Jpq 0 n * bm = Formalism.UG.Jpq 0 n
    have e' : Formalism.UG.cT (starRingEnd ℂ) bm = bm.conjTranspose := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [e', jpq_zero_left, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hbb]
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq 0 n), ?_⟩
  show bm * A = A * X
  simp only [bm, Matrix.mul_assoc, hLA, Matrix.mul_one]

open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin in

theorem measure_SFin_negDef : ∀ (D : D7) (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) →
    ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram), IsVolMeas D W 0 n μ →
    μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) = 1 := by
  intro D W n hW hsig μ hμ
  obtain ⟨θ, hθ⟩ := hμ.2.1
  obtain ⟨A, hA⟩ := (hμ.2.2 θ hθ).1
  have h := (hμ.2.2 θ hθ).2 A hA (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  have hp : D.cd.cd 0 n Set.univ = 1 := GlobalTheory.CompactDualSwap.cd_zero_univ D.cd n
  simp only [hp, Finset.prod_const_one] at h
  convert h using 2
  ext g
  constructor
  · intro hg
    refine ⟨hg, fun ρ => ?_⟩
    have h0 := hW (embOf D ρ)
    rw [hsig] at h0
    obtain ⟨e, P', hP⟩ := h0
    have hJ : IsUnit (W.gram.map (embOf D ρ)).det := by
      have hd := congrArg Matrix.det hP
      rw [jpq_zero_left, Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self] at hd
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      rw [h0, mul_zero, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hd
      exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hd.symm
    obtain ⟨b, hb⟩ := unitary_of_negative_definite e (A ρ) _ _ hJ (hA ρ)
      (infMat_unitary D.sp.cm.sig (fun _ => rfl) (fun x => (D.sp.cm.fixed _).mpr ⟨x, rfl⟩) (embOf D ρ)
        (D.sp.cm.cmUnram.2.1 _) (θ ρ) (hθ ρ) W.gram g)
    exact ⟨b, Set.mem_univ _, hb⟩
  · intro hg; exact hg.1

end GlobalTheory.NegDefStab
