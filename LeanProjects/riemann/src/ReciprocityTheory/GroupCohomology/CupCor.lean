import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.HomogExistsStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ContractNthCastAddCastSucc
import ReciprocityTheory.GroupCohomology.HomogIso
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
import ReciprocityTheory.GroupCohomology.ResNormalHolds
import ReciprocityTheory.GroupCohomology.CupCorB

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

set_option maxHeartbeats 800000 in

theorem cupCor_holds : CupCorStatement.{u} := by
  unfold CupCorStatement
  intro R _ G _ _ _ M N P U _ b bU cup cupU corM corP hU hβ hcup hcupU hcorM hcorP p q x y
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have ha' : (M.resSub U).coch.d p a = 0 := LinearMap.mem_ker.mp ha
  have hc' : N.coch.d q c = 0 := LinearMap.mem_ker.mp hc
  obtain ⟨eM, hMh, hM1, -⟩ := homogIso_holds.{u} R U (M.resSub U)
  obtain ⟨eN, hNh, hN1, -⟩ := homogIso_holds.{u} R G N
  obtain ⟨eP, hPh, hP1, -⟩ := homogIso_holds.{u} R G P

  have hAM : (eM p a).1 = CCA.homz (M.resSub U).rho p a.1 := funext fun z => hM1 p a z
  have hAmemU : CCA.homz (M.resSub U).rho p a.1 ∈ hcoch (M.resSub U) U p := by
    rw [← hAM]; exact (eM p a).2
  have hA : (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      ∈ hcoch (M.resSub U) G p :=
    CCA.retr_pull_mem (U := U) (hU := hU) (n := p) (F := CCA.homz (M.resSub U).rho p a.1)
      (hF := hAmemU)
  have hA0 : hd p (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) = 0 := by
    have h := hMh p a
    rw [ha', map_zero] at h
    funext z
    have h2 := congrFun h (fun i => retr U (z i))
    rw [← hAM]
    exact h2.symm

  have hFcE : (eN q c).1 = CCA.homz N.rho q c.1 := funext fun z => hN1 q c z
  have hFcN : CCA.homz N.rho q c.1 ∈ hcoch N G q := by
    rw [← hFcE]; exact (eN q c).2
  have hFc0 : hd q (CCA.homz N.rho q c.1) = 0 := by
    have h := hNh q c
    rw [hc', map_zero] at h
    rw [← hFcE]
    exact h.symm
  obtain ⟨FcA, hFcA⟩ : ∃ F : (HomogeneousCochainIso.hcx (N.resSub U) G).X q, F.1 = CCA.homz N.rho q c.1 :=
    ⟨⟨CCA.homz N.rho q c.1, CCA.res_mem (U := U) (n := q) (F := CCA.homz N.rho q c.1) (hF := hFcN)⟩,
      rfl⟩

  have hcont : Continuous (fun g : G => ((retr U g : U) : G)) :=
    continuous_subtype_val.comp (CCA.continuous_retr (U := U) hU)
  have hequiv : ∀ (v : U) (g : G), ((retr U (v • g) : U) : G) = v • ((retr U g : U) : G) := by
    intro v g
    show ((retr U ((v : G) * g) : U) : G) = (v : G) * ((retr U g : U) : G)
    rw [CCA.retr_mul, Subgroup.coe_mul]
  have hpr := prism_holds.{u} R U (N.resSub U) G G (HomogeneousCochainIso.hcx (N.resSub U) G)
    (HomogeneousCochainIso.hcx (N.resSub U) G) (fun n => LinearEquiv.refl R _) (fun n => LinearEquiv.refl R _)
    (fun n F => rfl) (fun n F => rfl)
  obtain ⟨φ, hφ⟩ := hpr.1 (fun g => ((retr U g : U) : G)) hcont hequiv
  have huq := hpr.2 (fun g => ((retr U g : U) : G)) id φ (Cx.Hom.id _) hcont continuous_id hequiv
    (fun _ _ => rfl) hφ (fun _ _ _ => rfl) q
  have h0 : (HomogeneousCochainIso.hcx (N.resSub U) G).d q FcA = 0 := by
    apply Subtype.ext
    show hd q FcA.1 = 0
    rw [hFcA]; exact hFc0
  have h1 : (HomogeneousCochainIso.hcx (N.resSub U) G).d q (φ.f q FcA) = 0 := by
    rw [← φ.comm, h0, map_zero]
  have hcls : (HomogeneousCochainIso.hcx (N.resSub U) G).cls q (φ.f q FcA) h1 =
      (HomogeneousCochainIso.hcx (N.resSub U) G).cls q FcA h0 :=
    congrArg (fun t => t ((HomogeneousCochainIso.hcx (N.resSub U) G).cls q FcA h0)) huq
  have hB : φ.f q FcA - FcA ∈ (HomogeneousCochainIso.hcx (N.resSub U) G).B q :=
    (Submodule.Quotient.eq (((HomogeneousCochainIso.hcx (N.resSub U) G).B q).comap
      ((HomogeneousCochainIso.hcx (N.resSub U) G).Z q).subtype)).mp hcls
  have hFr' : (φ.f q FcA).1 = fun z => CCA.homz N.rho q c.1 (fun i => ((retr U (z i) : U) : G)) := by
    funext z
    exact (hφ q FcA z).trans (congrFun hFcA _)

  have hrc : (N.resSub U).coch.d q ((Pair.res N U.subtype continuous_subtype_val).hom.f q c) = 0 := by
    rw [← (Pair.res N U.subtype continuous_subtype_val).hom.comm, hc', map_zero]
  obtain ⟨z1, hz1, hz1e, hz1c⟩ := hcupU p q a _ ha' hrc
  have hca : M.coch.d p (corM.f p a) = 0 := by rw [← corM.comm, ha', map_zero]
  obtain ⟨z2, hz2, hz2e, hz2c⟩ := hcup p q (corM.f p a) c hca hc'
  have hzz : P.coch.d (p + q) (corP.f (p + q) z1) = 0 := by rw [← corP.comm, hz1, map_zero]
  have hmem1 : CCA.hcup b.β p q (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) (φ.f q FcA).1
      ∈ hcoch (P.resSub U) G (p + q) := by
    have h := CCA.hcup_mem (b := bU) (p := p) (q := q) (hF := hA) (hF' := (φ.f q FcA).2)
    rw [hβ] at h; exact h
  have hmem2 : CCA.hcup b.β p q (fun z : Fin (p + 1) → G =>
      CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) (CCA.homz N.rho q c.1)
      ∈ hcoch (P.resSub U) G (p + q) := by
    have h := CCA.hcup_mem (b := bU) (p := p) (q := q) (hF := hA)
      (hF' := CCA.res_mem (U := U) (n := q) (F := CCA.homz N.rho q c.1) (hF := hFcN))
    rw [hβ] at h; exact h

  have hD1 : (eP (p + q) (corP.f (p + q) z1)).1 = CCA.normF P U (p + q) (CCA.hcup b.β p q
      (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      (φ.f q FcA).1) := by
    refine CCA.homog_eq (e := eP) (h1 := hP1) (n := p + q) (f := corP.f (p + q) z1)
      (hF := CCA.normF_mem (M := P) (U := U) (n := p + q) (hF := hmem1)) (hf := fun g => ?_)
    rw [hcorP (p + q) z1, hz1e, hFr']
    exact CCA.cor_cup_eq (b := b) (bU := bU) (hb := hβ) (p := p) (q := q) (f := a.1) (f' := c.1)
      (g := g)
  have hD2 : (eP (p + q) z2).1 = CCA.normF P U (p + q) (CCA.hcup b.β p q
      (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
      (CCA.homz N.rho q c.1)) := by
    refine CCA.homog_eq (e := eP) (h1 := hP1) (n := p + q) (f := z2)
      (hF := CCA.normF_mem (M := P) (U := U) (n := p + q) (hF := hmem2)) (hf := fun g => ?_)
    rw [hz2e, hcorM p a]
    exact CCA.cup_cor_eq (U := U) (b := b) (p := p) (q := q) (f := a.1) (f' := c.1) (g := g)

  have key : P.coch.cls (p + q) (corP.f (p + q) z1) hzz = P.coch.cls (p + q) z2 hz2 := by
    apply (Submodule.Quotient.eq (p := _)).mpr
    show corP.f (p + q) z1 - z2 ∈ P.coch.B (p + q)
    cases q with
    | zero =>
      have hz : φ.f 0 FcA = FcA := sub_eq_zero.mp ((Submodule.mem_bot (R := R)).mp hB)
      have hD : corP.f (p + 0) z1 - z2 = 0 := by
        apply (eP (p + 0)).injective
        apply Subtype.ext
        rw [map_sub, map_zero, Submodule.coe_sub, Submodule.coe_zero, hD1, hD2, hz, hFcA, sub_self]
      rw [hD]; exact Submodule.zero_mem _
    | succ q' =>
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hB
      have hwv : hd q' w.1 = (φ.f (q' + 1) FcA).1 - FcA.1 := congrArg Subtype.val hw
      rw [hFcA] at hwv
      have hh := CCA.hd_hcup b.β p q' _ w.1 hA0
      have hWmem : ((-1 : ℤ) ^ p • CCA.normF P U (p + q') (CCA.hcup b.β p q'
          (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1))
          ∈ hcoch P G (p + q') := by
        refine zsmul_mem (CCA.normF_mem (M := P) (U := U) (n := p + q') (hF := ?_)) _
        have h := CCA.hcup_mem (b := bU) (p := p) (q := q') (hF := hA) (hF' := w.2)
        rw [hβ] at h; exact h
      show corP.f (p + (q' + 1)) z1 - z2 ∈ LinearMap.range (P.coch.d (p + q'))
      refine LinearMap.mem_range.mpr ⟨(eP (p + q')).symm ⟨_, hWmem⟩, ?_⟩
      apply (eP (p + (q' + 1))).injective
      apply Subtype.ext
      refine (hPh (p + q') _).trans ?_
      rw [LinearEquiv.apply_symm_apply, map_sub, Submodule.coe_sub, hD1, hD2]
      exact calc hd (p + q') ((-1 : ℤ) ^ p • CCA.normF P U (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1))
          = (-1 : ℤ) ^ p • hd (p + q') (CCA.normF P U (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1)) :=
            CCA.hd_zsmul _ _ _
        _ = (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) (hd (p + q') (CCA.hcup b.β p q'
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) w.1)) :=
            congrArg (fun F => (-1 : ℤ) ^ p • F) (CCA.normF_hd (M := P) (U := U) (n := p + q') _).symm
        _ = (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) ((-1 : ℤ) ^ p • CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (hd q' w.1)) :=
            congrArg (fun F => (-1 : ℤ) ^ p • CCA.normF P U (p + q' + 1) F) hh
        _ = CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (hd q' w.1)) := by
            rw [CCA.normF_zsmul, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
        _ = CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
            (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
            (Sub.sub (α := (Fin (q' + 1 + 1) → G) → N.V) (φ.f (q' + 1) FcA).1
              (CCA.homz N.rho (q' + 1) c.1))) :=
            congrArg (fun F => CCA.normF P U (p + q' + 1) (CCA.hcup b.β p (q' + 1)
              (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i))) F)) hwv
        _ = _ := (congrArg (CCA.normF P U (p + q' + 1)) (CCA.hcup_sub_right b.β p (q' + 1)
              (fun z : Fin (p + 1) → G => CCA.homz (M.resSub U).rho p a.1 (fun i => retr U (z i)))
              (φ.f (q' + 1) FcA).1 (CCA.homz N.rho (q' + 1) c.1))).trans
            (CCA.normF_sub (M := P) (U := U) (n := p + q' + 1) _ _)
  have L : cupU p q ((M.resSub U).coch.cls p a ha')
      ((Pair.res N U.subtype continuous_subtype_val).hom.H q (N.coch.cls q c hc')) =
      (P.resSub U).coch.cls (p + q) z1 hz1 := hz1c
  have Rr : cup p q (corM.H p ((M.resSub U).coch.cls p a ha')) (N.coch.cls q c hc') =
      P.coch.cls (p + q) z2 hz2 := hz2c
  exact (congrArg (corP.H (p + q)) L).trans (key.trans Rr.symm)

end ReciprocityTheory.Coh
