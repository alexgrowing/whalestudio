import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.StFull
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.SphLocProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.UnramB
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitSph
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfIsCompAlongSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT

noncomputable section

open NumberField IsDedekindDomain Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in

theorem sc_hasSatGL_of_isSubquotient {w : HeightOneSpectrum (𝓞 E)} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (hρs : IsSmooth ρ)
    (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (hsub : GlobalTheory.SmGL.IsSubquotient σ ρ)
    (hsph : GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w n)) (B : Multiset ℂˣ)
    (hsat : ∀ f ∈ fixed ρ (GlobalTheory.LFun.KGL w n), f ≠ 0 → GlobalTheory.LFun.IsSatVecGL w ρ f B) :
    GlobalTheory.LFun.HasSatGL w σ B := by
  obtain ⟨S, q, hq⟩ := hsub
  obtain ⟨-, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  have hSs : IsSmooth S.toRepresentation := fun y => by
    refine (congrArg IsOpen ?_).mpr (hρs y.1)
    ext g
    exact Subtype.ext_iff
  refine ⟨hsph, fun x hx hx0 => ?_⟩
  have hx' : x ∈ (fixed S.toRepresentation (GlobalTheory.LFun.KGL w n)).map q.toLinearMap := by
    rw [GlobalTheory.LocGL.map_fixed_of_surjective hSs hKc (f := q) hq]
    exact hx
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 hx'
  have hu0 : u ≠ 0 := fun e => hx0 (by rw [← hux, e, map_zero])
  have huK : u.1 ∈ fixed ρ (GlobalTheory.LFun.KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu k hk)
  have hu1 : GlobalTheory.LFun.IsSatVecGL w ρ u.1 B := hsat _ huK fun e => hu0 (Subtype.ext e)
  have hu2 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := ρ) S.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective hu1
  have hu3 : GlobalTheory.LFun.IsSatVecGL w σ (q.toLinearMap u) B :=
    hu2.map (ρ' := σ) q.toLinearMap (fun g y => Representation.IntertwiningMap.isIntertwining _ _ q g y)
      (by rw [hux]; exact hx0)
  rw [hux] at hu3
  exact hu3

theorem sc_satVec (X : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (h : X.Sat w B) :
    ∀ f ∈ fixed (locProd X.h w (X.σ · w)) (GlobalTheory.LFun.KGL w n), f ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w (locProd X.h w (X.σ · w)) f B := by
  obtain ⟨b, hb, rfl⟩ := h
  intro f hf hf0
  obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd X.h (π := fun i => (X.σ i w).ρ)
    (fun i => (X.σ i w).smooth) (fun i => (X.σ i w).irred) hf hf0
  have e : S = b := funext fun a => (hS a).unique (hb a).2
  rw [← e]
  exact hfS

theorem sc_cLoc_conj (x : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    cLoc u x = GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n (cLoc (GlobalTheory.ThetaSatake.cw u) x) := by
  have h : ((GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)
      (cLoc (GlobalTheory.ThetaSatake.cw u) x)).val)ᵀ * (cLoc u x).val = 1 := GlobalTheory.SplitPts.comp_eq x u
  generalize hM : GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)
      (cLoc (GlobalTheory.ThetaSatake.cw u) x) = M at h
  have h1 : ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ * (M.val)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h2 : (cLoc u x).val = ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ := by
    calc (cLoc u x).val = ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ * ((M.val)ᵀ * (cLoc u x).val) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = _ := by rw [h, Matrix.mul_one]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h2, GlobalTheory.LFun.ConjPlace.invT_val, Matrix.transpose_apply, ← hM, ← map_inv]
  rfl

theorem splitConj : SplitConj := by
  intro E _ _ _ n π hπ D w u hw hwu hu hDw hDu B B' hB hB'
  obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hw
  have huw : u ≠ w := hwu.2.resolve_right (not_not.2 hw)
  have hu' : u = conjSrc (GlobalTheory.SplitPts.conjE E) w := (hover u hwu.1).resolve_left huw
  have hw' : w = GlobalTheory.ThetaSatake.cw u := by
    rw [hu']
    exact (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w).symm
  clear hu' hover
  subst hw'
  obtain ⟨P, hPsub, hPc⟩ := hDw
  obtain ⟨P', hP'sub, hP'c⟩ := hDu
  have hPsat : GlobalTheory.LFun.HasSatGL (GlobalTheory.ThetaSatake.cw u) P.ρ B :=
    sc_hasSatGL_of_isSubquotient (locProd D.h _ (D.σ · _)) (GlobalTheory.SmGL.isSmooth_parInd _ _) P.ρ hPsub
      (GlobalTheory.PfBCI.split_spherical hπ hw P hPc hu) B (sc_satVec D _ B hB)
  have hq : Formalism.UG.qV E u = Formalism.UG.qV E (GlobalTheory.ThetaSatake.cw u) := (GlobalTheory.ThetaSatake.absNorm_cw u).symm
  have hQsat : GlobalTheory.LFun.HasSatGL u
      (P.ρ.comp (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.toMonoidHom) (B.map (·⁻¹)) :=
    GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc u) (conjLoc_spec _ u).2.2 hq (LinearEquiv.refl ℂ P.V)
      (fun g x => by
        show P.ρ ((GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm
          (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n g)) x = P.ρ g x
        rw [MulEquiv.symm_apply_apply]) hPsat
  have hloc : locU n u = locU n (GlobalTheory.ThetaSatake.cw u) := by
    simp only [locU, hwu.1]
  have hQc : IsCompAlong π (locU n u) ((cLoc u).comp (locU n u).subtype)
      (P.ρ.comp (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.toMonoidHom) := by
    obtain ⟨hirr, f, hf0, hfm, hf⟩ := hPc
    refine ⟨GlobalTheory.PfBCI.SplitSph.isIrreducible_comp_surj P.ρ _
      (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.surjective hirr, f, hf0, hfm, fun x v => ?_⟩
    have hx : (x : UA E n) ∈ locU n (GlobalTheory.ThetaSatake.cw u) := hloc ▸ x.2
    have e := hf ⟨x, hx⟩ v
    show f (P.ρ ((GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm (cLoc u (x : UA E n))) v) =
      RU E n (x : UA E n) (f v)
    rw [sc_cLoc_conj (x : UA E n) u, MulEquiv.symm_apply_apply]
    exact e
  have hsu : IsSplitAt u := ⟨GlobalTheory.ThetaSatake.cw u, Ne.symm huw, hwu.1.symm⟩
  have hP'inv : GlobalTheory.LFun.HasSatGL u P'.ρ (B.map (·⁻¹)) :=
    GlobalTheory.SplitSatake.hasSatGL_of_isCompAlong_split E n π hπ u hsu _ _ _ P'.ρ hQc hP'c _ hQsat
  have hP'B' : GlobalTheory.LFun.HasSatGL u P'.ρ B' :=
    sc_hasSatGL_of_isSubquotient (locProd D.h u (D.σ · u)) (GlobalTheory.SmGL.isSmooth_parInd _ _) P'.ρ hP'sub hP'inv.1 B'
      (sc_satVec D u B' hB')
  exact hP'B'.unique hP'inv

end PositivityTheory.Rg.BcB.F.Rig

end
