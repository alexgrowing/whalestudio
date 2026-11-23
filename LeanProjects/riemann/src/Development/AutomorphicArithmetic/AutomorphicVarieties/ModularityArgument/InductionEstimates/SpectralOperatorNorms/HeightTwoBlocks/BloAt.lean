import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.bloAt :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (S : Set (BW.Pl E)) (r : ℕ) (b : Blo S r) (V : Submodule ℂ (LL (mu1 E r))),
      IsSummand (mu1 E r) V → ((cuspToL2 (mu1 E r) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E r)) : LL (mu1 E r)) ∈ V →
      At (mu1 E r) S V (fun τ => Finset.univ.val.map (b.Λ τ)) fun w => (b.sat w).map fun x : ℂˣ => (x : ℂ) := by
  intro E _ _ _ S r b V hV hf
  obtain ⟨π, hπ, -⟩ := Dp.exCusp E r (mu1 E r) V hV
  have hc : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ AutomorphicForm.centralCuspForms E r := fun s x => by
    have := b.cen (Real.log s.1) x
    unfold zt at this
    simpa only [Real.exp_log s.2] using this
  have hm : b.f ∈ π.V := by
    have : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ UpperTheory.V.Cm.carrier π := by
      rw [hπ.carrier_eq]; exact ⟨hc, hf⟩
    exact this
  refine ⟨fun τ => ?_, fun w hw => ?_⟩
  · obtain ⟨m, h1, -⟩ := Dp.sInfEx E r (mu1 E r) V hV τ
    have h2 : GlobalTheory.UnitaryBC.HasInfCharGL π.V τ m := (Dp.sInfIff E r (mu1 E r) π V hπ τ m).1 h1
    have hs : Submodule.span ℂ {b.f} ≠ ⊥ := by simpa using b.ne
    have e : m = Finset.univ.val.map (b.Λ τ) := by
      refine GlobalTheory.BcSpehProof.hasInfCharGL_unique hs (τ := τ) ⟨h2.1, fun u φ hφ => h2.2 u φ ?_⟩ ⟨by simp, fun u φ hφ => ?_⟩
      · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hm) hφ
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        rw [map_smul, b.inf, smul_comm, Multiset.map_map]
        rfl
    rw [e] at h1
    exact h1
  · have h0 := b.isSat w hw
    have hx : (⟨b.f, hm⟩ : π.V) ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w r) :=
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 h0.2.1 k hk)
    have hne : (⟨b.f, hm⟩ : π.V) ≠ 0 := fun e => b.ne (congrArg Subtype.val e)
    obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨_, hx, hne⟩)
    have h1 : GlobalTheory.LFun.IsSatVecGL w (BW.rw r w) b.f B := (hB.2 _ hx hne).map π.V.subtype (fun _ _ => rfl) b.ne
    have e := h1.unique h0
    subst e
    exact (Dp.sSatIff E r (mu1 E r) π V hπ w _).2 ⟨_, rfl, hB⟩
