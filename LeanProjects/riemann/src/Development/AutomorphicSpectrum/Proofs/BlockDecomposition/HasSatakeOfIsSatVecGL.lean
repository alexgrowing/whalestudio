import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParameters

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatComp

open GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}

theorem hasSatake_of_isSatVecGL (hπ : IsIrrSmooth π) {x : V} (α : Fin n → ℂˣ)
    (hx : IsSatVecGL w π x (Finset.univ.val.map α)) : GlobalTheory.SmGL.HasSatake π α := by
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at h1
  obtain ⟨ho, hc⟩ := isOpen_isCompact_KGL w n
  obtain ⟨y, hy, hy0, ht⟩ := exists_fixed_of_fun _ _ ho (Final.GLintComm E w n) hφ0 ((isSphericalGL_iff α φ).1 hφ)
  have hq : IsSubquot π (psGL (w.adicCompletion E) α) :=
    GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues _ _ _ π _ _ hc (Final.GLintComm E w n) hπ (LeviDatum.nInd_isSmooth _ _) x hx.2.1
      hx.1 y hy hy0 fun f hf => by
        obtain ⟨c, e1, e2⟩ := exists_eigenvalue_GL hx (isSatVecGL_of_isSpherical hφ hφ0) f hf
        exact ⟨c, e1, ht f hf c e2⟩
  have hs : IsSpherical π (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n)) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact (Submodule.ne_bot_iff _).2 ⟨x, hx.2.1, hx.1⟩
  exact ⟨hπ.2, hs, (GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff _ _ π α).1 hq⟩

end GlobalTheory.CompanionTheory.SatComp

open GlobalTheory.CompanionTheory.SatComp in

theorem GlobalTheory.CompanionTheory.SatComp.satComp : SatComp := by
  intro E _ _ _ n π w τ τ' B hs hB hπ hτ'
  obtain ⟨α, rfl, h'⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π ((CG.hasSat_mk π w B).1 hπ) hτ'
  obtain ⟨x, hx⟩ := hB.exists_vec
  have h := hasSatake_of_isSatVecGL ⟨τ.smooth, τ.irred⟩ α hx
  exact GlobalTheory.SmGL.SphUniq.equiv_of_parInd _ _ h.1 h'.1 h.2.2 h'.2.2 h.2.1 h'.2.1

end
