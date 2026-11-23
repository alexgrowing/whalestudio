import Formalism.HermitianCurvature.StatementKB
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WittOrthonormalBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.FormalDegreeBessel.FinalBF

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

open Formalism.FourierDecayAlt.P.PBJ

section pts

theorem bigPt_eq_map {n : ℕ} (d : Fin n → ℂ) : bigPt d = (List.ofFn d).map fun c => (1, c) := by
  rw [bigPt, List.map_ofFn]
  rfl

theorem ptPartner_ones (l : List ℂ) (a : ℕ) : D.ptPartner (l.map fun c => (1, c)) a = a := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih =>
    simp only [List.map_cons, D.ptPartner, ih]
    split_ifs with h <;> omega

theorem ptPerm_bigPt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) : D.ptPerm (bigPt d) = 1 := by
  unfold D.ptPerm
  split_ifs with h
  · ext i
    have hp : ∀ a : ℕ, D.ptPartner (bigPt d) a = a := fun a => by
      rw [bigPt_eq_map]
      exact ptPartner_ones _ _
    simp only [Equiv.ofBijective_apply, Equiv.Perm.coe_one, id_eq, D.ptPartnerF]
    split_ifs
    · exact hp i
    · rfl
  · rfl

theorem cast_perm_eq_one {n m : ℕ} (e : n = m) (σ : Equiv.Perm (Fin n)) (hσ : σ = 1) :
    (e ▸ σ : Equiv.Perm (Fin m)) = 1 := by
  subst e
  exact hσ

theorem hMat_one {n : ℕ} (d : Fin n → ℂ) : U.hMat (1 : Equiv.Perm (Fin n)) d = Matrix.diagonal d := by
  have hw : U.wP (1 : Equiv.Perm (Fin n)) = 1 := by
    ext a b
    by_cases hab : a = b <;> simp [U.wP, Matrix.one_apply, hab]
  simp only [U.hMat, hw, one_mul]

private lemma ptEntry_map_one_eq_ite_getD (l : List ℂ) (a b : ℕ) :
    D.ptEntry (l.map fun c => (1, c)) a b = if a = b then l.getD a 0 else 0 := by
  induction l generalizing a b with
  | nil => simp [D.ptEntry]
  | cons c l ih =>
    rcases a with _ | a <;> rcases b with _ | b <;> simp [D.ptEntry, ih]

private lemma list_ofFn_getD_of_lt {n : ℕ} (d : Fin n → ℂ) (i : ℕ) (hi : i < n) :
    (List.ofFn d).getD i 0 = d ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private lemma ptMatN_bigPt_eq_diagonal' {n : ℕ} (d : Fin n → ℂ) : D.ptMatN (bigPt d) n = Matrix.diagonal d := by
  ext a b
  simp only [D.ptMatN, bigPt_eq_map, ptEntry_map_one_eq_ite_getD, Matrix.diagonal_apply, Fin.ext_iff]
  split_ifs with h
  · exact list_ofFn_getD_of_lt d a a.isLt
  · rfl

theorem ptMatN_bigPt_head {r : ℕ} (d : Fin (r + 1) → ℂ) :
    D.ptMatN (bigPt d) r = Matrix.diagonal fun a : Fin r => d a.castSucc := by
  ext a b
  simp only [D.ptMatN, bigPt_eq_map, ptEntry_map_one_eq_ite_getD, Matrix.diagonal_apply, Fin.ext_iff]
  split_ifs with h
  · exact list_ofFn_getD_of_lt d a (by omega)
  · rfl

theorem zeta_big {r : ℕ} (TT : ℝ) (d : Fin (r + 1) → ℂ) (h : 0 < D.ptG TT r (bigPt d)) :
    TT < Complex.normSq (d (Fin.last r)) := by
  have h1 := h
  simp only [D.ptG, ptMatN_bigPt_eq_diagonal', ptMatN_bigPt_head, Matrix.det_diagonal, Fin.prod_univ_castSucc,
    map_mul] at h1
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (Complex.normSq_nonneg (∏ a : Fin r, d a.castSucc))]

end pts

section orb

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem zhat_bigCell_pt (Bs : B.RealPlaceData k r Wp Wq) (d : Fin (r + 1) → ℂ)
    (hζ : Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (d (Fin.last r))) :
    Zhat k r Bs.z Bs.z' (bigCell k r (fun i => d i.castSucc) (Bs.μsec (d (Fin.last r)))) =
      D.ptMatN (bigPt d) (r + 1) := by
  rw [ptMatN_bigPt_eq_diagonal', bigCellZhat k r _ _ _ _ Bs.z_mem Bs.z'_mem,
    Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ Bs.z_mem Bs.z'_mem, (Bs.sec.2 _ hζ).2]
  congr 1
  funext a
  split_ifs with h
  · rfl
  · have ha := a.isLt
    have hl : a = Fin.last r := Fin.ext (by rw [Fin.val_last]; omega)
    rw [hl]

theorem orbJ_one_zero (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    (hpos : 0 < Gf k r S.z S.z' γ) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r S.z S.z' γ = C2.monoP 1 d) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hJ : B.JF S F γ = 0) : D.orbJ S γ (D.muR S γ 1) F = 0 := by
  have : IsEmpty (C2.Lstidx (1 : Equiv.Perm (Fin (r + 1)))) := ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1, h2⟩ := q
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, id] at h2
    exact absurd h1 (not_lt.2 h2.le)⟩
  have hone : D.rhoOfU S γ 1 = 1 := by
    unfold D.rhoOfU
    split_ifs with hex
    · have h1mem : (1 : B.Mat k r) ∈ C6.Rset γ := by
        refine ⟨WeylGroupFacts.mem_n_one, ?_⟩
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ)]
        exact WeylGroupFacts.mem_n_one
      exact Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj S hγ hpos hd hZ hex.choose_spec.1 h1mem
        (hex.choose_spec.2.trans (Formalism.FourierDecayAlt.P.Dx2.Rad.uMap_one S.z ⟨S.z_mem, S.T_pos⟩).symm)
    · rfl
  have hlow : C2.lowOf (fun q : C2.Lstidx (1 : Equiv.Perm (Fin (r + 1))) => q.1) isEmptyElim = 1 := by
    unfold C2.lowOf
    ext i j
    simp
  have hR : D.muR S γ 1 = Measure.dirac (Matrix.of.symm (1 : B.Mat k r)) := by
    unfold D.muR
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty _ isEmptyElim, Measure.map_dirac' Subsingleton.measurable,
      hlow, Matrix.conjTranspose_one, hone]
  have hact : ∀ p, C6.actR γ 1 p = p := by
    intro p
    unfold C6.actR
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ), Matrix.one_mul,
      Matrix.one_mul]
    rfl
  have hθ : ∀ θ, D.IsNormCut S γ (D.muR S γ 1) θ → ∀ p, S.inSS p → θ p = 1 := by
    intro θ hθ p hp
    have h := hθ.2.2 p hp
    rw [hR, integral_dirac] at h
    simpa [hact] using h
  unfold D.orbJ
  split_ifs with hex
  · have h1 := hθ _ hex.choose_spec.1
    calc ∫ p, hex.choose p • D.orbIntegrand S γ F p ∂S.μSS = ∫ p, D.orbIntegrand S γ F p ∂S.μSS := by
          refine integral_congr_ae ?_
          filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS S] with p hp
          rw [h1 p hp, one_smul]
      _ = B.Jtau S (1, 1) F γ := rfl
      _ = B.JF S F γ := Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq S F γ
      _ = 0 := hJ
  · rfl

end orb

section jf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jf_bigCell_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hR : Top.IsRadOf P Bs 0 F) (c : Fin P.r → ℂ) (hc : ∀ a, c a ≠ 0) (ζ : ℂ)
    (hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ) :
    B.JF Bs F (bigCell P.k P.r c (Bs.μsec ζ)) = 0 := by
  have hsec := Bs.sec.2 ζ hζ
  have hμ : Bs.μsec ζ ∈ UH (Hb P.k) := hsec.1
  have hg : B2.embWb P.k P.r (Bs.μsec ζ) ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mem_UWb hμ)
  have e : herm (Hpk P.k P.r) (bigCell P.k P.r c (Bs.μsec ζ) *ᵥ Bs.z') Bs.z =
      Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (B2.embWb P.k P.r (Bs.μsec ζ)) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z'_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hz : Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (B2.embWb P.k P.r (Bs.μsec ζ)) = ζ := by
    rw [← e, Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ Bs.z_mem Bs.z'_mem, hsec.2]
  have hdom : ((c, B2.embWb P.k P.r (Bs.μsec ζ)) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈
      Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, by unfold Q.GGl; rw [hz]; linarith⟩
  have h0 := hR _ hdom
  have hz0 : ((0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
      (B2.embWb P.k P.r (Bs.μsec ζ)) = 0 := rfl
  rw [hz0] at h0
  unfold Q.resG at h0
  rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization P.k P.r c _).1] at h0
  rcases smul_eq_zero.1 h0.symm with h | h
  · exfalso
    rw [Complex.ofReal_eq_zero, Finset.prod_eq_zero_iff] at h
    obtain ⟨a, -, ha⟩ := h
    split_ifs at ha
    · exact pow_ne_zero _ (norm_ne_zero_iff.2 (hc a)) ha
    · exact one_ne_zero ha
  · exact h

end jf

theorem bigCellVan : PBJ.BigCellVan := by
  intro Wp Wq _ _ _ _ _ _ P p F _ hR d hd
  show D.vecV p.T.base p.ν' p.m₀ F (bigPt d) = 0
  unfold D.vecV
  split_ifs with h h'
  · obtain ⟨hγ, hZγ, -⟩ := h'.choose_spec
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r)) :=
      zeta_big _ d h.2
    have hc : ∀ a : Fin P.r, d a.castSucc ≠ 0 := fun a => hd _
    have hsec := p.T.base.sec.2 _ hζ
    have hγ' : bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r))) ∈ B.GV P.k P.r :=
      bigCellMem P.k P.r _ _ hc hsec.1
    have hZγ' := zhat_bigCell_pt p.T.base d hζ
    have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (bigPt d) _ h.1 hZγ]; exact h.2
    have hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z'
        (bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))) := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (bigPt d) _ h.1 hZγ']; exact h.2
    obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z'
      ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩
      _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)
    obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs
    obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'
    have hlaw := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (bigPt d) h.1 hγ hZγ hpos hhA hnA hfA hhB hnB hfB F
    rw [← hγs] at hlaw
    rw [← hlaw]
    have hw : (h.1.2 ▸ D.ptPerm (bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      cast_perm_eq_one _ _ (ptPerm_bigPt d hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (bigPt d) (P.r + 1) h.1.2 h.1.1
    rw [hw] at hmono
    rw [hw, orbJ_one_zero p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F
      (jf_bigCell_zero P p.T.base F hR _ hc _ hζ), map_zero]
  · rfl
  · rfl

end Formalism.FourierDecayAlt.P.PBM

namespace Formalism.FourierDecayAlt.P

theorem vector_vanishes_big_cell : PBJ.BigCellVan := PBM.bigCellVan

end Formalism.FourierDecayAlt.P
