import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensColPhiOneCharIndSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceSourceConstantProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombinStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAllStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFactsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem SmallPl.exists_card_withLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] :
    ∃ N : ℕ, 0 < N ∧ ∀ Q : Pair k n, (withLat Q.lat).card = N := by
  by_cases h : Nonempty (Pair k n)
  · obtain ⟨Q₀⟩ := h
    refine ⟨(withLat Q₀.lat).card, Finset.card_pos.2 ⟨Q₀, mem_withLat.2 rfl⟩, fun Q => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
    refine Finset.card_nbij' (fun P => g⁻¹ • P) (fun P => g • P) ?_ ?_ ?_ ?_
    · intro P hP
      have hP' : P.lat = g • Q₀.lat := mem_withLat.1 hP
      refine Finset.mem_coe.2 (mem_withLat.2 ?_)
      rw [Pair.smul_lat, hP', inv_smul_smul]
    · intro P hP
      have hP' : P.lat = Q₀.lat := mem_withLat.1 hP
      refine Finset.mem_coe.2 (mem_withLat.2 ?_)
      rw [Pair.smul_lat, Pair.smul_lat, hP']
    · intro P _
      exact smul_inv_smul g P
    · intro P _
      exact inv_smul_smul g P
  · exact ⟨1, one_pos, fun Q => (h ⟨Q⟩).elim⟩

theorem SmallPl.liftA_contAut {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V₀ A L S : HSp D} (o : OrthDec V₀ A L)
    (hA : CoCpt A) {χV χW : (AE D)ˣ →* Circle} {om : Om V₀ S} (hW : IsWeilDatumO ψ V₀ S χV χW om) (vA : Vol A)
    {φ : GA D A → ℂ} (hφ : IsContAut A φ) {Ξ : WO V₀ S → ℂ} (hΞ : IsThetaFunO ψ V₀ S Ξ) :
    IsContAut S fun h => liftA o om vA φ Ξ h 0 := by
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hlift : (fun h => liftA o om vA φ Ξ h 0) = fun h =>
      ∫ h₀ in vA.𝓕, φ h₀ * om (o.emb (h₀, 1), h) Ξ 0 ∂vA.μ := by
    funext h
    simp only [liftA]
    congr 1
    funext h₀
    rw [show ((0 : WO A S), (0 : WO L S)) = 0 from rfl, map_zero]
  rw [hlift]
  have jc := GlobalTheory.Unf.jointCont_all D ψ V₀ S χV χW om hW Ξ hΞ
  have hK₂c : Continuous (Function.uncurry fun (x : GA D A) (h : GA D S) => φ x * om (o.emb (x, 1), h) Ξ 0) := by
    have hmap : Continuous fun z : GA D A × GA D S => ((o.emb (z.1, 1), z.2), (0 : WO V₀ S)) :=
      ((o.continuous_emb.comp (continuous_fst.prodMk continuous_const)).prodMk continuous_snd).prodMk
        continuous_const
    exact (hφ.2.comp continuous_fst).mul (jc.comp hmap)
  have hK₂a : ∀ γ ∈ GQ A, ∀ (x : GA D A) (h : GA D S),
      φ (γ * x) * om (o.emb (γ * x, 1), h) Ξ 0 = φ x * om (o.emb (x, 1), h) Ξ 0 := by
    intro γ hγ x h
    have e : o.emb (γ * x, 1) = o.emb (γ, 1) * o.emb (x, 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    have hq := GlobalTheory.Unf.om_rat_mul D ψ V₀ S _ _ om hW Ξ hΞ (o.emb (γ, 1))
      (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (o.emb (x, 1)) h 0
    rw [one_mul] at hq
    rw [hφ.1 γ hγ x, e, hq, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨fun γ hγ h => ?_,
    (GlobalTheory.CocompactParam.continuous_integral_param D A hA vA (GA D S) _ hK₂c hK₂a).2.1⟩
  dsimp only
  congr 1
  funext x
  have hq := GlobalTheory.Unf.om_rat_mul D ψ V₀ S _ _ om hW Ξ hΞ 1 (one_mem _) γ hγ (o.emb (x, 1)) h 0
  rw [one_mul] at hq
  rw [hq, Matrix.mul_zero, Matrix.zero_mul]

theorem SmallPl.integral_sum_translates {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hS : CoCpt S)
    {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hW : IsWeilDatumO ψ S T χS χT om) (vS : Vol S) {Φ₂ : WO S T → ℂ}
    (hθ : IsThetaFunO ψ S T Φ₂) {ι : Type} (s : Finset ι) (b : ι → GA D S) (hfix : ∀ i ∈ s, om (b i, 1) Φ₂ = Φ₂)
    {G : GA D S → ℂ} (hG : IsContAut S G) (c : ℂ) (h' : GA D T) :
    (∫ h in vS.𝓕, om (h, h') Φ₂ 0 * (c * ∑ i ∈ s, G (h * b i)) ∂vS.μ) =
      c * s.card * ∫ h in vS.𝓕, om (h, h') Φ₂ 0 * G h ∂vS.μ := by
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hHc : Continuous fun h => om (h, h') Φ₂ 0 :=
    (hW.om_cont Φ₂ hθ 0).comp (continuous_id.prodMk continuous_const)
  have hHa : ∀ γ ∈ GQ S, ∀ h, om (γ * h, h') Φ₂ 0 = om (h, h') Φ₂ 0 := by
    intro γ hγ h
    have hq := GlobalTheory.Unf.om_rat_mul D ψ S T _ _ om hW Φ₂ hθ γ hγ 1 (one_mem _) h h' 0
    rw [one_mul] at hq
    rw [hq, Matrix.mul_zero, Matrix.zero_mul]
  have hHb : ∀ i ∈ s, ∀ h, om (h * b i, h') Φ₂ 0 = om (h, h') Φ₂ 0 := by
    intro i hi h
    have : ((h * b i, h') : GA D S × GA D T) = (h, h') * (b i, 1) := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [this, map_mul, Module.End.mul_apply, hfix i hi]
  obtain ⟨K, hK⟩ : ∃ K : GA D S → ℂ, K = fun h => om (h, h') Φ₂ 0 * G h := ⟨_, rfl⟩
  have hKc : Continuous K := hK ▸ hHc.mul hG.2
  have hKa : ∀ γ ∈ GQ S, ∀ h, K (γ * h) = K h := fun γ hγ h => by
    rw [hK]
    dsimp only
    rw [hHa γ hγ h, hG.1 γ hγ h]
  have hint : ∀ i ∈ s, IntegrableOn (fun h => c * K (h * b i)) vS.𝓕 vS.μ := by
    intro i _
    refine (GlobalTheory.CocompactParam.continuous_integral_param D S hS vS Unit (fun h _ => c * K (h * b i)) ?_ ?_).1 ()
    · exact (continuous_const.mul (hKc.comp (continuous_mul_right _))).comp continuous_fst
    · intro γ hγ h _
      rw [mul_assoc γ h, hKa γ hγ]
  calc (∫ h in vS.𝓕, om (h, h') Φ₂ 0 * (c * ∑ i ∈ s, G (h * b i)) ∂vS.μ)
      = ∫ h in vS.𝓕, ∑ i ∈ s, c * K (h * b i) ∂vS.μ := by
        refine integral_congr_ae (ae_of_all _ fun h => ?_)
        dsimp only
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hK]
        dsimp only
        rw [hHb i hi h]
        ring
    _ = ∑ i ∈ s, c * ∫ h in vS.𝓕, K h ∂vS.μ := by
        rw [integral_finset_sum _ hint]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S vS.μ vS.𝓕 vS.haar vS.fund K hKa]
    _ = _ := by
        rw [hK, Finset.sum_const, nsmul_eq_mul]
        ring

theorem smallOne : ∀ D : D7, SmallOne D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ hχ
  obtain ⟨r₀, e, hr₀, hsrc⟩ := GlobalTheory.T.gluedPlaceSourceConstant_proof D k p n n' q χ hχ
  obtain ⟨N, hN0, hN⟩ := SmallPl.exists_card_withLat k n
  refine ⟨r₀ * N, e, mul_pos hr₀ (Nat.cast_pos.2 hN0), ?_⟩
  intro ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hW₁ hWT hV hW hχS hχT vA vS vT α α₀ β hsum P Q s L₁ L₂ L₂' L₃
    f₁ Ξ Ξ' Φ₂ hΞ hΞ' hsd₂ hsd₃ hlat hvac φ₀ hφ₀ F hF
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  obtain ⟨χr, hχr⟩ : ∃ χr, χr = resChar χ hχ q := ⟨_, rfl⟩
  rw [← hχr] at hΞ' hsrc ⊢
  have hob := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hW₁.std V₀ S α₀ β L₁ L₂ hΞ.1 hΞ.2.1 f₁ hΞ.2.2.1
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  obtain ⟨Ξ'', hΞ'', -⟩ := hob.1 (tensCol (phiOne P (s • Q)) (charInd χr (s • Q)))
    (hsb.1 _ _ (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _) (hsb.2.2 _ _))
  have hram := (GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k p n' q χ hχ χr hχr s A α P).2.1 φ hφ
  have hram1 := ((GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k p n' q χ hχ χr hχr 1 A α P).2.1 φ hφ).1
  rw [map_one, Module.End.one_apply] at hram1

  have hmove : liftA o om₁ vA (FFStar q χr φ P) Ξ'' = liftA o om₁ vA (sOp α P q χr s (φ P)) Ξ' := by
    obtain ⟨lS, hlS, hθ⟩ := GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift D k p n n' ψ V₀ A L S o ζ hζ hA vA χV χW om₁ hW₁ α α₀ β hsum
    obtain ⟨θ, hθv, hθe⟩ := hθ L₁ L₂ f₁ hΞ.1 hΞ.2.1 hΞ.2.2.1
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P (s • P)
    have hgs : g ∈ latStab P.lat := by
      change g • P.lat = P.lat
      rw [← Pair.smul_lat, hg, Pair.dia_lat]
    have h1 := hθe g ⟨FFStar q χr φ P, hram1.2.2 P⟩ _ hΞ''.2.2.2.1
    have b2 : (fun x => tensCol (phiOne P (s • Q)) (charInd χr (s • Q)) (x * (SrcGl.blk g).val)) =
        tensCol (phiOne P Q) (charInd χr (s • Q)) := by
      funext x
      rw [SrcGl.tensCol_mul_blk]
      congr 1
      funext x₀
      rw [← SrcGl.phiOne_smul_left, hg, phiOne_dia]
    rw [b2, hθv _ _ _ hΞ', hθv _ _ _ hΞ'', GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' P.lat inferInstance g hgs lS (hlS hW), Units.val_one,
      inv_one, one_smul, SrcGl.caRep_apply] at h1
    rw [hram.2, dia_apply, ← hg, hram1.1 g P]
    exact h1.symm

  obtain ⟨lS, lT, -, hlT, -, -, hlin⟩ := GlobalTheory.T.linearModel_splitPlace_characterEquivariance D k p q ψ V₀ S χV χW om₁ hW₁
  choose gs hgs using fun Q' : Pair k n => MulAction.exists_smul_eq (GL n k) (s • Q) Q'
  have hstab : ∀ Q' ∈ withLat Q.lat, gs Q' • Q.lat = Q.lat := fun Q' hQ' => by
    rw [← Pair.dia_lat s Q, ← Pair.smul_lat, hgs, mem_withLat.1 hQ', Pair.dia_lat]
  have hfix : ∀ Q' ∈ withLat Q.lat, omT (β.gl (gs Q'), 1) Φ₂ = Φ₂ := by
    intro Q' hQ'
    obtain ⟨-, -, -, hfr, -, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β
    obtain ⟨Λ', -, hΛ', hK⟩ := hfr L₂' hsd₂
    have hΛQ : Λ' = Q.lat := Submodule.ext fun x => (hΛ' x).trans (hlat x).symm
    have hk1 : InK S L₂' (· = p.v) (β.gl (gs Q')) := (hK _).2 (hΛQ ▸ hstab Q' hQ')
    have hk2 : InK T L₃ (· = p.v) 1 := ⟨one_mem _, fun y _ => by simp [Formalism.L2.Theta.mt]⟩
    exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT omT hWT L₂' L₃ hsd₂ hsd₃ (· = p.v)
      (fun v hv => by subst hv; exact ⟨GlobalTheory.T.isTameFinitePlaceHermitian_all D _, hχS, hχT⟩) Φ₂ hvac _ _ hk1 hk2
  have hOver : ∀ Q' ∈ withLat Q.lat, Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q') (charInd χr Q'))
      (om₁ (1, β.gl (gs Q')) Ξ'') := by
    intro Q' hQ'
    have h0 := hlin n (n' ⊕ Fin 1) α₀ β L₁ L₂ f₁ _ Ξ'' hΞ'' 1 (gs Q')
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n Q.lat inferInstance (gs Q') (hstab Q' hQ') lT (hlT hV)] at h0
    convert h0 using 1
    · funext x
      simp only [map_one, Units.val_one, one_mul, Matrix.mul_one]
      rw [tensCol_phiOne_charInd_smul, hgs]
    · rw [map_one]
  have hfun := hsrc ψ V₀ A L S o ζ hζ hA vA χV χW om₁ hW₁ hV hW α α₀ β hsum P Q.lat L₁ L₂ f₁ Ξ
    (fun Q' => om₁ (1, β.gl (gs Q')) Ξ'') hΞ hOver φ hφ
  have hterm : ∀ (f : GA D A → ℂ) b h,
      liftA o om₁ vA f (om₁ (1, b) Ξ'') h 0 = liftA o om₁ vA f Ξ'' (h * b) 0 := by
    intro f b h
    simp only [liftA]
    congr 1
    funext h₀
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hG := SmallPl.liftA_contAut o hA hW₁ vA (hram1.2.2 P) (hob.2.1 _ _ hΞ'').1
  simp only [smallPair]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun h' => ?_)
  dsimp only
  have key := SmallPl.integral_sum_translates hS hWT vS hvac.1 (withLat Q.lat) (fun Q' => β.gl (gs Q')) hfix hG
    ((r₀ : ℂ) * chrPow χW (p.idele q.unit) e) h'
  rw [hfun, ← hmove]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hterm]
  rw [key, hN]
  push_cast
  ring

end GlobalTheory.FinPl
