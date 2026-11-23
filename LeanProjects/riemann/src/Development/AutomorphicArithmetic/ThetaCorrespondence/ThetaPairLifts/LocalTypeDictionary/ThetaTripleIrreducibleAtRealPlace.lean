import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaImageEqSpanDarboux
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleMapsEquivariantOnFiniteVectors
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleMapsLieEquivariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteSubspaceKStableIffLieStable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ILiescalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactorStatement

section
noncomputable section
namespace GlobalTheory.TripleAssembly.Irred
section Linear
end Linear
section Darboux
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem theta_triple_irreducible_at_real_place (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    Module.rank ℂ (G.M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 ∧
    (∀ γ ∈ Lines σ G.W, ∃ δ : Module.End ℂ (SInf F (Fin a × Fin (a + a'))), ∀ f ∈ G.M.Pol B.ψ B.emb,
      δ f ∈ G.M.Pol B.ψ B.emb ∧ ∀ f₁ : SInf F (Fin a × Fin (a + a')),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ↔ f₁ = δ f) ∧
    ∃ (r s : ℕ) (C : InfinitePlace F → Matrix (Fin (a + a')) (Ix r s) ℂ),
      (∀ w, IsFrame (Complex.I • G.W.J.map (B.emb w).1) (C w)) ∧
      ∀ S : Set (Multiplicative ℝ →* UA σ G.W.J),
        (∀ w, ∀ Z ∈ upq r s, ∃ γ ∈ S, γ ∈ Lines σ G.W ∧ IsGen B.emb C γ (Function.update (fun _ => 0) w Z)) →
        ∀ N : Submodule ℂ (SInf F (Fin a × Fin (a + a'))),
        (∀ γ ∈ S, γ ∈ Lines σ G.W → ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
          ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → f ∈ N → f₁ ∈ N) →
        ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
          ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → f ∈ N → f₁ ∈ N := by
  obtain ⟨hb, hg, hc, hw, hw'⟩ := h
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := _root_.GlobalTheory.RealLift.Main.lieSecond_of_lieScalar_of_vacLine hP i_derex hfe hvl (_root_.GlobalTheory.RealLift.Main.i_liescalar_alt hP i_derex hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ.1)
  have hmem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  have act : ∀ γ ∈ Lines σ G.W, ∀ Y, IsGen B.emb C γ Y → ∀ T (f₁ : SInf F (Fin a × Fin (a + a'))),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) f₁ ↔
        f₁ = Φ (sumPl (fun w => fockAct2 _ _ _ _ (Y w) + ((B.mβ w : ℂ) / 2 * (Y w).trace) • 1) T) := by
    intro γ hγ Y hY T f₁
    have h1 := (i_actslaws F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) (hW2 γ hγ Y hY T)
    exact ⟨fun k => ((i_actslaws F _ (Φ T) _ f₁).2.2.1 _ h1 k).symm, fun k => k ▸ h1⟩
  have gen := i_genex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1
  refine ⟨?_, fun γ hγ => ?_, _, _, C, hC, fun S hS N hN γ hγ f hf f₁ h1 hfN => ?_⟩
  · rw [← hr]
    refine (rank_range_le Φ).trans ?_
    rw [← (Basis.piTensorProduct fun _ : InfinitePlace F => MvPolynomial.basisMonomials _ ℂ).mk_eq_rank'']
    exact Cardinal.mk_le_aleph0
  · obtain ⟨Y, -, hY⟩ := gen γ hγ
    refine ⟨Φ ∘ₗ sumPl (fun w => fockAct2 _ _ _ _ (Y w) + ((B.mβ w : ℂ) / 2 * (Y w).trace) • 1) ∘ₗ Ψ, fun f hf => ?_⟩
    obtain ⟨T, rfl⟩ := pol_eq B G.M Φ hr hf
    have e : Ψ (Φ T) = T := LinearMap.congr_fun hΨ T
    refine ⟨hmem _, fun f₁ => ?_⟩
    rw [act γ hγ Y hY T f₁, LinearMap.comp_apply, LinearMap.comp_apply, e]
  · obtain ⟨Y, hYu, hY⟩ := gen γ hγ
    obtain ⟨T, rfl⟩ := pol_eq B G.M Φ hr hf
    rw [(act γ hγ Y hY T f₁).1 h1, sumPl, LinearMap.sum_apply, map_sum]
    refine N.sum_mem fun w _ => ?_
    obtain ⟨γ', hγS, hγ', hgen⟩ := hS w (Y w) (hYu w)
    refine hN γ' hγS hγ' _ (hmem T) _ ((act γ' hγ' _ hgen T _).2 ?_) hfN
    congr 2
    unfold sumPl
    rw [Finset.sum_eq_single w]
    · simp
    · intro w' _ k
      simp [Function.update_of_ne k, atPl_zero]
    · simp
end Darboux
section MatrixPart
open scoped Matrix
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealLift.OneParam
end MatrixPart
section Reading
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {D : D7}
end Reading
section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 2000000 in
theorem theta_triple_piT_irreducible : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        IsIrred X (ModuleCat.of ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf)) (GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf)) (GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf)) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  have iA := (_root_.GlobalTheory.T.theta_image_eq_span_darboux hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm).1
  have eqf := (_root_.GlobalTheory.T.theta_triple_maps_equivariant hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm).1
  have eql := (_root_.GlobalTheory.T.theta_triple_lift_lie_equivariant hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm).1
  have hT := hm.triple
  have hg := hT.geo
  have hM := hg.hM
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hT.base.std
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have dV : Γ.V.J.det ≠ 0 := Onto.det_ne_of_hasSig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV.sig w₀)
  have dW : Γ.W.J.det ≠ 0 := Onto.det_ne_of_hasSig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have gA : (sgn true W).gram.det ≠ 0 := Formalism.L2.Theta.gram_det_ne _
  have hξ : D.host.xi0 ≠ 0 := by
    intro h0
    have hlt := hg.lt
    haveI : Nonempty (Fin (W.rank + W₁.rank)) := ⟨⟨0, by omega⟩⟩
    rw [h.JX, h0, zero_smul] at dW
    exact dW (Matrix.det_zero)
  have hone : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW 1 = 1 := by
    apply Subtype.ext; simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]
  have hstdφ : ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
      (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
      ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 := fun φ hφ => by
    filter_upwards [hφ, hM.std] with v a b using a.trans b
  obtain ⟨T, hTh, hinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Γ.M ψ (sgn true W).gram e (hψ' ▸ hM) hstd dV dW gA
  have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Γ.M Bs.ψ Bs.emb hM
  have K : ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
      GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ algF ψ θ true A B ∧
      mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
        R.p f ⊗ₜ GlobalTheory.SmallThetaModules.pureT (vacIm Γ Rf) (fun v => Rf.p v (φ v)) := by
    intro f hf φ hφ hv
    have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ darbAlg Γ.M Bs.ψ Bs.emb := Submodule.subset_span ⟨f, φ, hf, hφ, hv, rfl⟩
    refine ⟨by rw [← iA T hTh, ← hTh _ (hS hmem)]; exact Submodule.mem_map_of_mem hmem, ?_⟩
    have H : ∃ q : (Matrix (Fin X.rank) (Fin W.rank) (AE D) → ℂ) →ₗ[ℂ] PiT R Γ Rf, ∀ Ψ ∈ darbAlg Γ.M Bs.ψ Bs.emb,
        q (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) = liftPure Γ.M R.p Rf.p (vacIm Γ Rf) Ψ := by
      obtain ⟨q, hq⟩ := Onto.exists_factor T _ (fun x hx => hinj x (hS hx)) (liftPure Γ.M R.p Rf.p (vacIm Γ Rf))
      exact ⟨q, fun Ψ hΨ => by rw [← hTh Ψ (hS hΨ)]; exact hq Ψ hΨ⟩
    have H' := GlobalTheory.T.weil_model_projection_factorisation _ _ _ Γ.M Bs.ψ hM _ R.p _ Rf.p (vacIm Γ Rf) (Filter.Eventually.of_forall fun _ => rfl)
    have e1 : mapA ψ e Bs Γ R Rf = H.choose := dif_pos H
    have e2 : liftPure Γ.M R.p Rf.p (vacIm Γ Rf) = H'.choose := dif_pos H'
    rw [e1]
    refine (H.choose_spec _ hmem).trans ?_
    rw [e2]
    exact H'.choose_spec f φ hφ hv
  have ext := end_ext _ R.p hm.real.quot.onto (fun v => GlobalTheory.WeilM.SB _) Rf.p hm.fin.onto Γ.M.vac (fun v => (hM.vac v).1)
  have hfin0 : {v | vacIm Γ Rf v = 0}.Finite := Xc.T.finite_toSet.subset fun v hv => by
    by_contra k
    exact (hm.fin.sph v k).2 hv
  obtain ⟨hrank, hδ, r, s, C, hC, hred⟩ := _root_.GlobalTheory.TripleAssembly.Irred.theta_triple_irreducible_at_real_place hP hT
  haveI := hm.real.nontriv
  refine ⟨nontrivial_tensor _ hfin0 hm.fin.nontriv R.Pi, fun N hNf hNl => ?_⟩
  have h1V : ∀ v, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.V (GlobalTheory.AdelicU.evFin D.host.F v) := fun v u _ => by
    show u • ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J).1.1 - 1) = 0
    rw [show (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have exF : ∀ v, ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v), ∀ φ ∈ GlobalTheory.WeilM.SB _,
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB _, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, g)) φ φ₁ :=
    fun v g hg φ hφ => GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.Inhab.pairV hT) v (1, g) (h1V v) hg φ hφ
  let Sv : ∀ v, Set (Module.End ℂ (Rf.Pi v)) := fun v => {a | ∃ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W
    (GlobalTheory.AdelicU.evFin D.host.F v), ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, (φ₁ ∈ GlobalTheory.WeilM.SB _ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, g)) φ φ₁) → Rf.p v φ₁ = a (Rf.p v φ)}
  have irrv : ∀ v, ∀ Q : Submodule ℂ (Rf.Pi v), (∀ a ∈ Sv v, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
    intro v Q hQ
    refine hm.fin.irred v Q fun g hg φ hφ φ₁ hφ₁ hact hx => ?_
    obtain ⟨a, ha⟩ := exists_descend _ (Rf.p v) (hm.fin.onto v) (fun φ φ₁ => φ₁ ∈ GlobalTheory.WeilM.SB _ ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, g)) φ φ₁) (exF v g hg)
      (fun f hf f' hf' k k' hk hk' a b => ⟨add_mem (Submodule.smul_mem _ a hk.1) (Submodule.smul_mem _ b hk'.1),
        GlobalTheory.ThK.LocalOps.acts_lin v _ (exF v g hg) hf hf' hk.2 hk'.2 a b⟩)
      (fun f hf k hk h0 => by
        rw [hm.fin.equiv v g hg f hf 0 (zero_mem _) k hk.1 0 (zero_mem _) hk.2 (fun r _ => by
          have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin D.host.F v) 0 r = 0 := by
            funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
          rw [e, map_zero]) (by rw [h0, map_zero]), map_zero])
    rw [ha φ hφ φ₁ ⟨hφ₁, hact⟩]
    exact hQ a ⟨g, hg, ha⟩ _ hx
  choose Op hOp using fun v (a : Module.End ℂ (Rf.Pi v)) =>
    exists_rtensOp (vacIm Γ Rf) (Function.update (fun i => (1 : Module.End ℂ (Rf.Pi i))) v a)
  have hOp' : ∀ v (a : Module.End ℂ (Rf.Pi v)) ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr (vacIm Γ Rf) ξ →
      Op v a (GlobalTheory.SmallThetaModules.pureT _ ξ) = GlobalTheory.SmallThetaModules.pureT _ (Function.update ξ v (a (ξ v))) := by
    intro v a ξ hξ
    rw [hOp v a ξ hξ]
    congr 1
    funext i
    by_cases c : i = v
    · subst c; simp
    · simp [Function.update_of_ne c]
  have rkv : ∀ v, Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := fun v => by
    rw [← rank_top ℂ (Rf.Pi v), ← hm.fin.onto v]
    exact (rank_map_le _ _).trans (GlobalTheory.T.rank_schwartzBruhat_adicCompletion_pi_le_aleph0 _ _ v)
  have irrF := GlobalTheory.T.restrictedTensorProduct_irreducible_countable_dimension Rf.Pi (vacIm Γ Rf) hfin0 rkv hm.fin.nontriv Sv irrv Op fun v a _ => hOp' v a
  have rkR : Module.rank ℂ R.Pi ≤ Cardinal.aleph0 := by
    rw [← rank_top ℂ R.Pi, ← hm.real.quot.onto]
    exact (rank_map_le _ _).trans hrank
  refine GlobalTheory.T.tensor_irreducible_of_countable_dimension_irreducible R.Pi _ {b | ∀ x ∈ N, LinearMap.rTensor _ b x ∈ N} {c | ∃ v, ∃ a ∈ Sv v, c = Op v a} rkR
    inferInstance (fun Q hQ => ?_) (fun Q hQ => irrF Q fun v a ha => hQ _ ⟨v, a, ha, rfl⟩) N (fun b hb => hb) ?_
  ·
    have hlie := hred {γ | ∃ τ, ∃ Y ∈ lieAt X τ, ∀ t : ℝ, γ (Multiplicative.ofAdd t) =
        GlobalTheory.TripleRead.toUX X e h.JX (oneP θ X τ Y t)}
      (fun w Z hZ => exists_line_at θ hθ X e Γ.W h.JX hξ Bs.emb (fun w => (h.cart w).imp fun _ k => k.1) C hC w Z hZ)
      (Q.comap R.p) (by
        rintro γ ⟨τ, Y, hY, hγt⟩ hγ f hf f₁ hact hfQ
        obtain ⟨δ, hδ⟩ := hδ γ hγ
        obtain ⟨b, hb⟩ := exists_descend _ R.p hm.real.quot.onto (fun f g => g = δ f) (fun f _ => ⟨_, rfl⟩)
          (fun f _ f' _ k k' hk hk' a b => by rw [hk, hk', map_add, map_smul, map_smul])
          (fun f hf k hk h0 => by
            rw [hm.real.lie γ hγ f hf 0 (zero_mem _) k 0 (((hδ f hf).2 k).2 hk) (fun r _ x => by
              have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F
                  (Fin W₁.rank × Fin (W.rank + W₁.rank)))) r = 0 := by
                funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
              simp only [e, map_zero]
              exact hasDerivAt_const _ _) (by rw [h0, map_zero]), map_zero])
        have hop : opLie θ ωA (algF ψ θ true A B) (mapA ψ e Bs Γ R Rf) τ Y = LinearMap.rTensor _ b := by
          refine ext _ _ fun f hf φ hφ hv => ?_
          obtain ⟨m1, k1⟩ := K f hf φ hφ hv
          obtain ⟨m2, k2⟩ := K _ (hδ f hf).1 φ hφ hv
          refine (congrArg _ k1.symm).trans ((eql τ Y hY _ m1 _ m2 fun z => ?_).symm.trans ?_)
          · have hd := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M Bs.ψ _ _ om hT.base.cm hT.base.std hM hT.weil γ hγ 1 (fun _ => f) (fun _ => δ f) (fun _ => φ)
              (fun _ => ⟨hφ, hv⟩) (fun _ => ((hδ f hf).2 _).2 rfl) (GlobalTheory.TripleRead.ptO (sgn true W).gram e z)
            rw [Fin.sum_univ_one, Fin.sum_univ_one, hψ'] at hd
            refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
            have h3 := congrFun (tA _ (GlobalTheory.TensUniq.pure_mem_schA f φ hφ (hstdφ φ hv)) 1 (oneP θ X τ Y t)) z
            rw [hone, ← hγt t] at h3
            exact h3.symm
          · rw [k2, hb f hf _ rfl]
            rfl
        show R.p f₁ ∈ Q
        rw [hb f hf f₁ (((hδ f hf).2 f₁).1 hact)]
        refine hQ b (fun x hx => ?_) _ hfQ
        rw [← hop]
        exact hNl τ Y hY x hx)
    exact hm.real.irred Q hlie (_root_.GlobalTheory.T.kFinite_subspace_kStable_iff_lie_stable hP Bs Γ Xc om om' R Rf hm Q hlie)
  ·
    rintro _ ⟨v, a, ⟨k, hk, ha⟩, rfl⟩ x hx
    obtain ⟨g, rfl⟩ := toUX_surj X e h.JX hξ k
    have hgf := mem_GfC_of_at X e Γ.W h.JX v g hk
    have hop : opFin ωA (algF ψ θ true A B) (mapA ψ e Bs Γ R Rf) g = LinearMap.lTensor _ (Op v a) := by
      refine ext _ _ fun f hf φ hφ hv => ?_
      obtain ⟨m1, k1⟩ := K f hf φ hφ hv
      obtain ⟨φ₁, hφ₁, hact⟩ := exF v _ hk (φ v) (hφ v)
      have hsch := GlobalTheory.TensUniq.pure_mem_schA f φ hφ (hstdφ φ hv)
      have hφ' : ∀ w, Function.update φ v φ₁ w ∈ GlobalTheory.WeilM.SB _ := fun w => by
        by_cases c : w = v
        · subst c; rw [Function.update_self]; exact hφ₁
        · rw [Function.update_of_ne c]; exact hφ w
      have hv' : ∀ᶠ w in Filter.cofinite, Function.update φ v φ₁ w = Γ.M.vac w := by
        filter_upwards [hv, Filter.eventually_cofinite_ne v] with w c c'
        rw [Function.update_of_ne c', c]
      have hpure : om (1, GlobalTheory.TripleRead.toUX X e h.JX g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁) := by
        obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ (hstdφ φ hv)
        have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin D.host.F v) (φ v) ρ := by
          rw [hρt, Function.update_eq_self]
        rw [e1, hact ρ ⟨hρ, e1 ▸ hsch⟩, hρt]
      have h3 := tA _ hsch 1 g
      rw [hone, hpure] at h3
      have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr (vacIm Γ Rf) fun w => Rf.p w (φ w) :=
        (Filter.eventually_cofinite.1 hv).subset fun w hw c => hw (congrArg (Rf.p w) c)
      refine (congrArg _ k1.symm).trans ((eqf g hgf _ m1).symm.trans ?_)
      rw [← h3, (K f hf _ hφ' hv').2]
      refine Eq.trans ?_ (LinearMap.lTensor_tmul _ _ _ _).symm
      refine congrArg _ (Eq.trans ?_ (hOp' v a _ hr).symm)
      congr 1
      funext w
      by_cases c : w = v
      · subst c
        rw [Function.update_self, Function.update_self]
        exact ha _ (hφ w) _ ⟨hφ₁, hact⟩
      · rw [Function.update_of_ne c, Function.update_of_ne c]
    rw [← hop]
    exact hNf g hgf x hx
end Main
end GlobalTheory.TripleAssembly.Irred
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_triple_lift_irreducible : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        IsIrred X (ModuleCat.of ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf)) (GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf)) (GlobalTheory.TripleAssembly.opLie θ ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf)) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.Irred.theta_triple_piT_irreducible | exact _root_.GlobalTheory.TripleAssembly.Irred.theta_triple_piT_irreducible | (intros; apply _root_.GlobalTheory.TripleAssembly.Irred.theta_triple_piT_irreducible <;> assumption)
end
