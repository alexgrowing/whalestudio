import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingIntegralIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjLinearFunctionalSphericalVectorIndicator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingIntegralIdentityStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RegSo
theorem regular_subspace_vacuum_at : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (P : GL (Fin a') (Fv F v)) (Λ : Submodule 𝒪[Fv F v] (Fin (a + a') → Fv F v)) (c : ℂ),
      G.M'.IsLinBar B.ψ t 1 1 ι ∧
      ∀ Y, ι (G.M'.vac v) Y = c * (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t
  haveI := hT.geo.hV'.lat
  haveI := hT.geo.hW.lat
  obtain ⟨b', hb'⟩ := exists_isSplitBasis t G.V'.L hT.base.cm
  obtain ⟨c, hc⟩ := exists_isSplitBasis t G.W.L hT.base.cm
  obtain ⟨b₁, -, ι', hι', hvac'⟩ :=
    _root_.GlobalTheory.T.splitPlace_sphericalVector_indicator_value hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.ThKConst.isPair_small hT) v t b' c hb' hc
  let Q : GL (Fin a') (Fv F v) := Matrix.GeneralLinearGroup.mkOfDetNeZero b₁.valᵀ (by
    rw [Matrix.det_transpose]; exact b₁.isUnit.map Matrix.detMonoidHom |>.ne_zero)
  let Λ : Submodule 𝒪[Fv F v] (Fin (a + a') → Fv F v) :=
    { carrier := {x | ∀ j, (x ᵥ* c.val) j ∈ 𝒪[Fv F v]}
      add_mem' := fun {x y} hx hy j => by rw [Matrix.add_vecMul]; exact add_mem (hx j) (hy j)
      zero_mem' := fun j => by rw [Matrix.zero_vecMul]; exact zero_mem _
      smul_mem' := fun s x hx j => by
        rw [show s • x = (s : Fv F v) • x from rfl, Matrix.smul_vecMul]
        exact mul_mem s.2 (hx j) }
  refine ⟨_, Q, Λ, 1, isLinBar_one G.M' B.ψ t b₁ Q rfl c ι' hι', fun Y => ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
  rw [hvac', one_mul]
  have key : mulHomeo Q c Y ∈ {Y : Matrix (Fin a') (Fin (a + a')) (Fv F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} ↔
      Q.val * Y ∈ (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F v))) := by
    rw [mulHomeo_apply]
    show (∀ i j, (Q.val * Y * c.val) i j ∈ v.adicCompletionIntegers F) ↔ ∀ i j, ((Q.val * Y).row i ᵥ* c.val) j ∈ 𝒪[Fv F v]
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    rfl
  by_cases h : Q.val * Y ∈ (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F v)))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key.2 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (key.1 h'))]
theorem exists_combination_mem_regular_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
      (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, Xc.Good v → ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁ ∧ k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) ∧
        GlobalTheory.FunObj.zdeg z ≠ 0 ∧ ∀ i, ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
          Φ₀D ∈ Γ.M'.So Bs.ψ t := by
  intro hP D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD n Ψ hΨ
  classical
  choose ΦD hΦD hD using fun i => hO.algB (Ψ i) (hΨ i)
  choose m f φ hsum hSB hvac using fun i => decAlg Γ.M' Bs.ψ Bs.emb (ΦD i) (hΦD i)
  have hfin : Set.Finite (⋃ i, ⋃ k, {v | ¬ φ i k v = Γ.M'.vac v}) :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (hvac i k)
  refine ⟨hfin.toFinset, fun v hv hg t => ?_⟩
  have h0 : ∀ i k, φ i k v = Γ.M'.vac v := fun i k => by
    by_contra h
    exact hv (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, h⟩⟩))
  have hTD' := isTriple_goodPlace hTD v t hg
  obtain ⟨K, hK⟩ := homAt W₁ Γ hO.JW₁ hTD.base.cm hTD.geo.hV'.herm v t
  let K' : GL (Fin W₁.rank) (Fv D.host.F v) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (K g)
      map_one' := by simp only [map_one]; exact GlobalTheory.LocWeilAct.conjU_one' _ _ _
      map_mul' := fun g g' => by simp only [map_mul]; exact GlobalTheory.LocWeilAct.conjU_mul' _ _ _ _ _ }
  obtain ⟨ν', α', hν', hact⟩ := actAt { Bs with v₁ := v, τ₁ := t } Γ Xc om om' hTD' K' (fun g => (hK g).2.2)
  obtain ⟨ι, Pm, Λ, c, hι, hvι⟩ := _root_.GlobalTheory.RegSo.regular_subspace_vacuum_at hP _ _ D.sp.cm.sig { Bs with v₁ := v, τ₁ := t } _ _ Γ Xc om om' hTD' v t
  obtain ⟨z, hzs, hzd, hz⟩ := combAt { Bs with v₁ := v, τ₁ := t } Γ hTD.geo.hM' hTD.geo.lt om'
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁) K ν' α' hν' ι hι (hact ι hι) (Γ.M'.vac v) Pm Λ c hvι
  refine ⟨z, fun k hk => ?_, hzd, fun i => ⟨(z.sum fun k c => c • om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ k, 1) (ΦD i)),
    datumComb D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD (ΦD i) (Ψ i) (hD i) z, ?_⟩⟩
  · obtain ⟨g, rfl⟩ := hzs k hk
    exact ⟨(hK g).1, (hK g).2.1⟩
  · rw [hsum i]
    exact hz (f i) (φ i) (hSB i) (hvac i) (h0 i)
end GlobalTheory.RegSo
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_form_mem_regular_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
      (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, Xc.Good v → ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁ ∧ k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) ∧
        GlobalTheory.FunObj.zdeg z ≠ 0 ∧ ∀ i, ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
          Φ₀D ∈ Γ.M'.So Bs.ψ t := by
  first | exact @_root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace | exact _root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace | (intros; apply _root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace <;> assumption)
end
