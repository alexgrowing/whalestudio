import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicModelInvariantSub
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFockMapFirstOrderOfRealLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicModelInvariantSubStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg
theorem polynomial_vector_kFinite (fockFirst : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb,
    ∃ P : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ P ∧ P ≤ Γ.M.Pol Bs.ψ Bs.emb ∧
      f ∈ P ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ g ∈ P, ∃ g₁ ∈ P,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) (⇑g) (⇑g₁) := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT f hf
  classical
  obtain ⟨A, Φ, c, hA, hAθ, hr, hact⟩ := fockFirst hPr F E σ Bs a a' Γ Xc om om' hT
  have hb := hT.base
  have hwp : GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.WeilM.adeleClass F) Bs.ψ (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) Γ.M.co Xc.β (Xc.β / Xc.α) om := hT.weil
  have hadm := fun g => (hwp.isUSplitting).adm g
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨D, hD⟩ := exists_tensDeg T
  haveI : FiniteDimensional ℂ (tensDeg F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) D) :=
    LinearMap.finiteDimensional_range _
  refine ⟨(tensDeg F _ _ _ _ D).map Φ, inferInstance, hr ▸ LinearMap.map_le_range, ⟨T, hD, rfl⟩, ?_⟩
  rintro k hk _ ⟨T', hT', rfl⟩
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ (Fin a) _ _ Bs.emb
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) 1 A Γ.V.θ hb.cm hA hAθ k hk.1 hk.2
  let L := GlobalTheory.RealLift.sumPl (fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
    (c w * (Yg w).trace) • (1 : Module.End ℂ _))
  have hloc : GlobalTheory.RealLift.LocFin L := GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w v => by
    obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights _ _ _ _).1 v
    exact ⟨W, hW, hv, fun y hy => W.add_mem (hs (Yg w) (hKC w) y hy) (W.smul_mem _ hy)⟩
  obtain ⟨U, hexp, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin a × Fin (a + a')) _ Φ L ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  let Lw : ∀ w : InfinitePlace F, Module.End ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
      (c w * (Yg w).trace) • (1 : Module.End ℂ _)
  let Nw : ∀ w : InfinitePlace F, Submodule ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun _ => MvPolynomial.restrictTotalDegree _ ℂ D
  have hN : ∀ i, ∀ z ∈ Nw i, Lw i z ∈ Nw i := by
    intro i z hz
    simp only [Lw, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.add_mem _ (GlobalTheory.FockPolGK.kStable1 _ _ _ _ D (Yg i) (hKC i) z hz) (Submodule.smul_mem _ _ hz)
  have hLst : ∀ y ∈ tensDeg F _ _ _ _ D, L y ∈ tensDeg F _ _ _ _ D := by
    intro y hy
    change GlobalTheory.RealLift.sumPl Lw y ∈ _
    rw [GlobalTheory.RealLift.sumPl, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun w _ => GlobalTheory.RealLift.atPl_mem_range_map Lw Nw hN w y hy
  refine ⟨Φ (U T'), ⟨U T', exp_stable hexp _ hLst T' hT', rfl⟩, ?_⟩
  have h1 := hSA T'
  rw [MonoidHom.comp_apply, hγ1] at h1
  exact (GlobalTheory.RealLift.actsLaws F _ (Φ T') (Φ (U T')) (Φ (U T'))).2.1 _ (map_zero _) h1
theorem derivation_algebra_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT ΦD hΦ
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hT
  have hstdM := hPair.good.std
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hx
    obtain ⟨P, hPfin, hPle, hfP, hPst⟩ := _root_.GlobalTheory.SquareAgree.KFinAlg.polynomial_vector_kFinite _root_.GlobalTheory.T.real_lift_exists_fock_map hPr F E σ Bs a a' Γ Xc om om' hT f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v |
          ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hcof, hstdM] with v h1 h2
      rw [h1, h2]
    refine ⟨P.map (pureL φ), inferInstance, ?_, ⟨f, hfP, rfl⟩, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, φ, hPle hg, hSB, hcof, rfl⟩
    · rintro k hk _ ⟨g, hg, rfl⟩
      obtain ⟨g₁, hg₁, hA⟩ := hPst k hk g hg
      have key : om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ :=
        hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ hSB hstd)
      exact ⟨g₁, hg₁, key.symm⟩
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, Submodule.zero_mem _, fun k _ x hx => by
      rw [Submodule.mem_bot] at hx; subst hx; rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h1, l1, m1, s1⟩ := hx
    obtain ⟨U₂, h2, l2, m2, s2⟩ := hy
    refine ⟨U₁ ⊔ U₂, inferInstance, sup_le l1 l2, Submodule.add_mem_sup m1 m2, fun k hk z hz => ?_⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add]
    exact Submodule.add_mem_sup (s1 k hk y₁ hy₁) (s2 k hk y₂ hy₂)
  | smul c x _ hx =>
    obtain ⟨U, h, l, m, s⟩ := hx
    exact ⟨U, h, l, U.smul_mem c m, s⟩
end GlobalTheory.SquareAgree.KFinAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_algebra_closed_under_derivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  first | exact @_root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | exact _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | (intros; apply _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite <;> assumption)
end
