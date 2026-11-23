import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KernelOfEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FibreCounting

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

theorem smul_cov (r χ χ' b : ℂ) (hχ : ‖χ‖ = 1) (O O' : V' →L[ℂ] V) (U : V' →L[ℂ] V') (hO : O' = b • O.comp U) :
    r • (χ' • O') = (χ' * b * χ⁻¹) • (r • (χ • O)).comp U := by
  have hχ0 : χ ≠ 0 := by intro h; rw [h, norm_zero] at hχ; exact zero_ne_one hχ
  rw [hO]
  simp only [ContinuousLinearMap.smul_comp, smul_smul]
  congr 1
  field_simp

theorem norm_cov (χ χ' b : ℂ) (hχ : ‖χ‖ = 1) (hχ' : ‖χ'‖ = 1) (hb : ‖b‖ = 1) : ‖χ' * b * χ⁻¹‖ = 1 := by
  rw [norm_mul, norm_mul, norm_inv, hχ, hχ', hb]; norm_num

end Gen

section Amp

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

set_option maxHeartbeats 400000 in

theorem oot_cov (hR : RatPt) (hC : ChiTrivialC) {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) :
    ∃ (b : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖b‖ = 1 ∧ OOt s' = b • (OOt s).comp (cl U) := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  obtain ⟨hl, n, hn, ν, hν, c, hc, hg, hfix, he⟩ := fib_dec h
  have hm : s.lam' = s'.lam' := lam'_eq h
  obtain ⟨xn, hxn⟩ := hR D X n (nlam_isom hn)
  obtain ⟨xν, hxν⟩ := hR D X ν (nlam_isom hν)
  obtain ⟨xc, hxc⟩ := hR D X c hc
  have hpt : s'.pt = xn * s.pt * xν * xc :=
    ratLink_unique X s'.rep.2.1
      (ratLink_congr (ratLink_mul X (ratLink_mul X (ratLink_mul X hxn s.rep.2.1) hxν) hxc) he.symm)
  have hIA : IsAutLam (VS D) s.lam' c := ⟨hc, gmap_congr hg hm.symm⟩
  have hset : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν) :=
    (roset_congr hl.symm hm.symm he).trans (roset_c _ hIA hfix)
  have hconj : ∀ y, y ∈ ROinf s ↔ xn.1 * y * xn.1⁻¹ ∈ ROinf s' := fun y =>
    (roset_conj X hn hν hxn y).trans (Set.ext_iff.1 hset.symm _)
  have hex : (∃ Ω, IsSFund X.B.I (ROinf s) Ω) ↔ (∃ Ω, IsSFund X.B.I (ROinf s') Ω) := by
    constructor
    · rintro ⟨Ω, hΩ⟩
      refine ⟨_, isSF_image_mul xn.1 (fun y => ?_) hΩ⟩
      have e : xn.1 * (xn.1⁻¹ * y * xn.1) * xn.1⁻¹ = y := by group
      rw [hconj, e]
    · rintro ⟨Ω, hΩ⟩
      refine ⟨_, isSF_image_mul xn.1⁻¹ (fun y => ?_) hΩ⟩
      rw [inv_inv]
      exact hconj y
  by_cases hE : ∃ Ω, IsSFund X.B.I (ROinf s') Ω
  · have hE0 := hex.2 hE
    have hΩp : IsSFund X.B.I (ROinf s) (FundOf s) := by
      unfold FundOf; rw [dif_pos hE0]; exact hE0.choose_spec
    have hΩq : IsSFund X.B.I (ROinf s') (FundOf s') := by
      unfold FundOf; rw [dif_pos hE]; exact hE.choose_spec
    have key := oo_rel nLamNinf_holds hC Y s.mem s.mem' s.rep hn hν hxn hxν hΩp (isSFund_congr hset hΩq)
    have hsinv : xc.1⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' (sinf_of_fix hxc hfix)
    have hB : ∀ x, X.Wu u' (xc.1⁻¹ * x) =
        X.psiInfU u' xc.1⁻¹ • (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv) (X.Wu u' x) :=
      fun x => (X.Wu_spec u').1 _ hsinv x
    have e1 : OOt s' = conj (X.psiInfU u' xc.1⁻¹) •
        (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') (xn * s.pt * xν).1).comp
          ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv :
            X.Vpi u' →L[ℂ] X.Vpi u') := by
      unfold OOt
      rw [hpt, Prod.fst_mul]
      exact OO_right _ _ _ _ _ xc.1 _ _ hB
    refine ⟨conj (X.psiInfU u' xc.1⁻¹) * (X.psiInfU u xn.1 * X.psiInfU u' xν.1),
      (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm, ?_, ?_⟩
    · rw [norm_mul, RCLike.norm_conj, norm_mul, psiInfU_norm, psiInfU_norm, psiInfU_norm]; norm_num
    · have key' : OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') (xn * s.pt * xν).1 =
          (X.psiInfU u xn.1 * X.psiInfU u' xν.1) • OOt s := key
      rw [e1, key']
      have hU : ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv :
          X.Vpi u' →L[ℂ] X.Vpi u') = cl (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm := by
        ext x; rfl
      rw [hU, ContinuousLinearMap.smul_comp, smul_smul]
  · have hE0 : ¬ ∃ Ω, IsSFund X.B.I (ROinf s) Ω := fun h0 => hE (hex.1 h0)
    have h1 : OOt s' = 0 := by
      unfold OOt FundOf; rw [dif_neg hE]; exact OO_empty _ _ _ _
    have h2 : OOt s = 0 := by
      unfold OOt FundOf; rw [dif_neg hE0]; exact OO_empty _ _ _ _
    refine ⟨1, LinearIsometryEquiv.refl ℂ _, norm_one, ?_⟩
    rw [h1, h2]
    simp

theorem ampCov_of (hR : RatPt) (hC : ChiTrivialC) (Y : Full X) : AmpCov Y := by
  intro u u' t s s'
  have h : s.1.toTerm = s'.1.toTerm := s.2.trans s'.2.symm
  obtain ⟨b, U, hb, hO⟩ := oot_cov hR hC h
  unfold amp ampN
  refine ⟨_, U, ?_, smul_cov _ _ _ b (norm_chiN _) (OOt s.1) (OOt s'.1) (cl U) hO⟩
  exact norm_cov _ _ b (norm_chiN _) (norm_chiN _) hb

end Amp

end Formalism.L2.SG.Pf.KernelOfEmbedding
