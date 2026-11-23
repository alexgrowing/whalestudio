import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardLocalisationWeilDatumInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CayleyRuleOfBiInvariantVacuumCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMatrixCoefficientSourceInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegmentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlaceStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem eq_of_inert_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hin : IsInertAt F E v w)
    (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v) : w' = w := by
  have hle : w.asIdeal ≤ w'.asIdeal := by
    rw [← hin, Ideal.map_le_iff_le_comap, ← h', HeightOneSpectrum.under_asIdeal]
  exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle)).symm

set_option maxHeartbeats 2000000 in

theorem std_cayley_of_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ CayleyRule (qV D.host.F v) T.rank ρ (ω.comp (MonoidHom.inl _ _)) s ∧ CayleyRule (qV D.host.F v) S.rank ρ (ω.comp (MonoidHom.inr _ _)) s := by
  intro D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hU heS heT f hf hf0
  obtain ⟨δ, ψ', M, ρ, ω, s, hstd, hsf, hω, hth, hρ⟩ :=
    GlobalTheory.T.exists_standardLocalisation_weilDatum_inertPlace D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hU heS heT f hf hf0
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne S T
  have hψ := hW.std
  have hthf : IsThetaFunO ψ S T f := hf.1
  let l : M →ₗ[ℂ] ℂ :=
    { toFun := fun m => Lift.pet μ 𝓕 (m : WO S T → ℂ) f
      map_add' := fun m m' => by
        show GlobalTheory.Ker.ipO μ 𝓕 ((m + m' : M) : WO S T → ℂ) f = GlobalTheory.Ker.ipO μ 𝓕 _ f + GlobalTheory.Ker.ipO μ 𝓕 _ f
        rw [Submodule.coe_add]
        exact GlobalTheory.Size.ipO_add_left hψ hμ.1 hμ.2.1 (hth m) (hth m') hthf
      map_smul' := fun a m => by
        show GlobalTheory.Ker.ipO μ 𝓕 ((a • m : M) : WO S T → ℂ) f = a * GlobalTheory.Ker.ipO μ 𝓕 _ f
        rw [Submodule.coe_smul]
        exact GlobalTheory.Size.ipO_smul_left μ 𝓕 a _ _ }
  have hl : ∀ m : M, l m = Lift.pet μ 𝓕 (m : WO S T → ℂ) f := fun _ => rfl
  have hls : l s ≠ 0 := by
    rw [hl, hsf]
    exact fun h0 => hf0 ((GlobalTheory.Size.ipO_self_eq_zero_iff hψ hμ.1 hμ.2.1 hthf).1 h0)
  have hinv : ∀ u ∈ intMat (w.adicCompletion D.host.E) (Fin T.rank) (Fin S.rank), ∀ m : M, l (ρ u m) = l m := by
    intro u hu m
    obtain ⟨u0, hu0⟩ := hρ u
    have hfix : heisO ψ S T u0 f = f := by
      have e := hu0 s
      rw [hstd.fixes u hu, hsf] at e
      exact e.symm
    rw [hl, hl, hu0 m]
    conv_lhs => rw [← hfix]
    exact GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 (hth m) hthf u0
  have hcay := GlobalTheory.T.cayleyRule_of_biInvariantVacuumCoefficient _ ϖ c (qV D.host.F v) δ ψ' S.rank T.rank M ρ ω s hstd l hls hinv
  obtain ⟨φ1, hk1, hc1⟩ := GlobalTheory.T.vacuum_matrixCoefficient_source_inert_place_alt D ψ S T χS χT om hW μ 𝓕 hμ v w h hin hS hT c ϖ eS hU heS
  have hunr : ∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w' :=
    fun w' h' => by
      rw [eq_of_inert_under hin w' h']
      exact ⟨hS, hT⟩
  obtain ⟨φ2, hk2, hc2⟩ := GlobalTheory.T.weilMatrixCoefficient_vacua_unramifiedPlace D ψ S T χS χT om hW μ 𝓕 hμ v hunr
  have hval := (GlobalTheory.T.heckeChar_value_inert_place_and_segment D χS S.rank hW.hecS hW.resS v w h hin hS).1
  have hk2' := (hk2 w h).2 hin c ϖ eT hU heT
  rw [hval] at hk2'
  refine ⟨δ, ψ', M, ρ, ω, s, hstd, hsf, hω, hcay.1 φ1 hk1 fun g => ?_, hcay.2 (φ2 ∘ eT.symm) hk2' fun g => ?_⟩
  · exact (congrArg (fun x => Lift.pet μ 𝓕 x f) ((hω g 1 s).trans (by rw [map_one eT.symm, map_one (embV T v), hsf]))).trans
      ((hc1 g f f hf hf).trans (by rw [hl, hsf]))
  · exact (congrArg (fun x => Lift.pet μ 𝓕 x f) ((hω 1 g s).trans (by rw [map_one eS.symm, map_one (embV S v), hsf]))).trans
      ((hc2 (eT.symm g) f f hf hf).trans (by rw [hl, hsf]; rfl))

end GlobalTheory.ChainOnto

end
