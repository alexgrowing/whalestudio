import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeas

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

section vec

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def gd (p : KB.Pl P Wp Wq) (d : Fin (P.r + 1) → ℂ) : B.Mat P.k P.r :=
  bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))

def wq (p : KB.Pl P Wp Wq) (d : Fin (P.r + 1) → ℂ) : Fin (2 * P.r + P.k + 1) → ℂ :=
  D.prW P.k P.r p.T.base.z (D.cofR p.T.base (gd p d))

theorem vDecomp (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (d : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) (hG : 0 < TBB.Gp p (TBB.bigPt P.r d)) :
    ∃ hA ∈ UWset P.k P.r p.T.base.z, ∃ hB ∈ UWset P.k P.r p.T.base.z', ∃ l : ℂ,
      p.V F (TBB.bigPt P.r d) = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base hA hB (B.JF p.T.base F (gd p d)) ∧
      hA *ᵥ wq p d = l • (p.m₀ *ᵥ p.ν') ∧ l ≠ 0 := by
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt d hd
  have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  have hV : p.V F (TBB.bigPt P.r d) = D.orbJ p.T.base h'.choose
      (D.muR p.T.base h'.choose (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d))) F := by
    show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d) = _
    unfold D.vecV
    rw [dif_pos ⟨hl, hG'⟩, dif_pos h']
  obtain ⟨hγ, hZγ, hDγ⟩ := h'.choose_spec
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ d hG'
  have hc : ∀ a : Fin P.r, d a.castSucc ≠ 0 := fun a => hd _
  have hsec := p.T.base.sec.2 _ hζ
  have hγ' : gd p d ∈ B.GV P.k P.r := bigCellMem P.k P.r _ _ hc hsec.1
  have hZγ' : Zhat P.k P.r p.T.base.z p.T.base.z' (gd p d) = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) :=
    Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base d hζ
  have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  have hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (gd p d) := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ']; exact hG'
  obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z'
    ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩
    _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'
  have hlaw := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (Formalism.FourierDecayAlt.P.PBJ.bigPt d) hl hγ hZγ hpos hhA hnA hfA hhB hnB
    hfB F
  have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
    Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
  rw [hw] at hmono
  obtain ⟨a, ha, hpr⟩ := hDγ.1
  have hdet : (Zhat P.k P.r p.T.base.z p.T.base.z' h'.choose).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.determinant_nonzero P.k P.r p.T.base.z p.T.base.z' (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base)
      (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) _ hpos
  refine ⟨hA, hhA, hB, hhB, (a : ℂ) * (Zhat P.k P.r p.T.base.z p.T.base.z' h'.choose).det, ?_, ?_,
    mul_ne_zero (by exact_mod_cast ha.ne') hdet⟩
  · rw [hV, ← hlaw]
    show _ = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base hA hB (B.JF p.T.base F (gd p d))
    rw [← hγs, hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F]
  · have hZ1 := Formalism.FourierDecayAlt.P.Dx2.VV.zhat_conj p.T.base hhA hnA hfA hhB hnB hfB h'.choose
    have hcof := Formalism.FourierDecayAlt.P.Dx2.VV.cofR_conj p.T.base (sA := hA * nA)
      (Formalism.FourierDecayAlt.P.Dx2.VV.mul_fix hhB hfB) hZ1
    have hzz : herm (Hpk P.k P.r) p.T.base.z p.T.base.z ≠ 0 := by
      rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]
      have := p.T.base.T_pos
      intro h
      have h2 := congrArg Complex.re h
      simp at h2; linarith
    have hsinv := Formalism.FourierDecayAlt.P.Dx2.VV.prW_sinv p.T.base.z_mem hzz hhA hnA
      (Formalism.FourierDecayAlt.P.Dx2.VV.cofR_free p.T.base h'.choose)
    unfold wq
    rw [hγs, hcof, hsinv, hpr, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1),
      Matrix.one_mulVec]

end vec

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
