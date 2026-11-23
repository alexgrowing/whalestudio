import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.EdgesRouteSmall
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Inj

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def IsDat (B : Base F E) (Γ : Geo σ a a') (T : Finset (Pl F)) (f : SInf F (Fin a × Fin (a + a')))
    (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) : Prop :=
  f ∈ Γ.M.Pol B.ψ B.emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ v = Γ.M.vac v

abbrev PiT (R : RealMaps F a a') (Rf : FinMaps F a a') (T : Finset (Pl F)) : Type :=
  R.Pi ⊗[ℂ] PiTensorProduct ℂ fun v : T => Rf.Pi v

def img (R : RealMaps F a a') (Rf : FinMaps F a a') (T : Finset (Pl F)) (f : SInf F (Fin a × Fin (a + a')))
    (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) : PiT R Rf T :=
  R.p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ v)

theorem pure_arch {n d : ℕ} (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    ∃ r : (Fin n × Fin d → AF F) → ℂ, (∀ x z, At (evI F) z → r (x + z) = r x) ∧
      ∀ f : SInf F (Fin n × Fin d), pure f φ = tens (evI F) f r := by
  refine ⟨fun x => ∏ᶠ v, φ v fun i => evFin F v (x i), fun x z hz => ?_, fun f => rfl⟩
  have h2 : ∀ i, (z i).2 = 0 := fun i => by
    let u : AF F := (0, 1)
    have h0 : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h : u * z i = 0 := congrFun (hz u h0) i
    have h' : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    simpa using h'
  have e : ∀ (v : Pl F) i, evFin F v ((x + z) i) = evFin F v (x i) := fun v i => by
    have h3 : evFin F v (z i) = 0 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F (z i)) = 0
      have : sndA F (z i) = 0 := h2 i
      rw [this, map_zero]
    rw [Pi.add_apply, map_add, h3, add_zero]
  simp only [e]

section Model
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)

theorem std_of_cof (hM : M.IsGood ψ) {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
  (h2.and hM.std).mono fun _ h => h.1.trans h.2

theorem pure_eq_pureA (hM : M.IsGood ψ) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∃ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∀ f : SInf F (Fin n × Fin d), pure f φ = pureA F f g :=
  ⟨_, ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ h1 (std_of_cof M ψ hM h2),
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 (std_of_cof M ψ hM h2)⟩, fun _ => rfl⟩

theorem pure_at (hM : M.IsGood ψ) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) (f : SInf F (Fin n × Fin d)) (v : Pl F) :
    ∃ r : (Fin n × Fin d → AF F) → ℂ, (∀ x z, At (evFin F v) z → r (x + z) = r x) ∧
      ∀ φ₂ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ w, w ≠ v → φ₂ w = φ w) →
        pure f φ₂ = tens (evFin F v) (φ₂ v) r := by
  classical
  obtain ⟨r, hr, e⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ (std_of_cof M ψ hM h2)
  refine ⟨r, hr, fun φ₂ h => ?_⟩
  have : φ₂ = Function.update φ v (φ₂ v) := by
    funext w
    by_cases hw : w = v
    · subst hw
      simp
    · rw [Function.update_of_ne hw, h w hw]
  rw [e (φ₂ v), ← this]
end Model

variable {B : Base F E} {Γ : Geo σ a a'} {X : Chars F E} {om : Rep σ Γ.V Γ.W} {om' : Rep σ Γ.V' Γ.W}

theorem om_schA (ht : IsTriple B Γ X om om') (p : UA σ Γ.V.J × UA σ Γ.W.J)
    {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} (hΦ : Φ ∈ schA F _) : om p Φ ∈ schA F _ :=
  (ht.weil.isUSplitting).pres p Φ hΦ

theorem theta_add (ht : IsTriple B Γ X om om') {Φ Ψ : (Fin a × Fin (a + a') → AF F) → ℂ} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _)
    (g : UA σ Γ.V.J) (h : UA σ Γ.W.J) : theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, map_add]
  exact thetaSum_add F (om_schA ht _ hΦ) (om_schA ht _ hΨ)

theorem theta_smul (c : ℂ) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (g : UA σ Γ.V.J) (h : UA σ Γ.W.J) :
    theta om (c • Φ) g h = c * theta om Φ g h := by
  simp only [theta, map_smul]
  exact thetaSum_smul F c _

theorem I_sum (hK : ThetaIntegralsAgree) (ht : IsTriple B Γ X om om') {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (Φ : ι → (Fin a × Fin (a + a') → AF F) → ℂ) (hΦ : ∀ i ∈ s, Φ i ∈ schA F _) :
    Γ.M.I om (∑ i ∈ s, c i • Φ i) = ∑ i ∈ s, c i • Γ.M.I om (Φ i) := by
  classical
  have hconv := (hK.1 F E σ B a a' Γ X om om' ht).1.1
  induction s using Finset.induction_on with
  | empty =>
    funext h
    simp [Model.I, theta, thetaSum]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, Φ j ∈ schA F _ := fun j hj => hΦ j (Finset.mem_insert_of_mem hj)
    have h1 : c i • Φ i ∈ schA F _ := Submodule.smul_mem _ _ (hΦ i (Finset.mem_insert_self _ _))
    have h2 : ∑ j ∈ s, c j • Φ j ∈ schA F _ := Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hs j hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih hs]
    funext h
    simp only [Model.I, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : ∀ g, theta om (c i • Φ i + ∑ j ∈ s, c j • Φ j) g h = c i * theta om (Φ i) g h + theta om (∑ j ∈ s, c j • Φ j) g h :=
      fun g => by rw [theta_add ht h1 h2, theta_smul]
    simp only [e]
    rw [integral_add ((hconv _ (hΦ i (Finset.mem_insert_self _ _)) h).const_mul _) (hconv _ h2 h), integral_const_mul]

variable {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem IsDat.cof {T : Finset (Pl F)} {f : SInf F (Fin a × Fin (a + a'))}
    {φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ} (h : IsDat B Γ T f φ) :
    ∀ᶠ v in cofinite, φ v = Γ.M.vac v :=
  Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
    by_contra h'
    exact hv (h.2.2 v h'))

theorem vanish (hK : ThetaIntegralsAgree) (hm : IsMatched B Γ X om om' R Rf) {T : Finset (Pl F)} (hT : X.T ⊆ T)
    {ι : Type} (s : Finset ι) (f : ι → SInf F (Fin a × Fin (a + a'))) (φ : ι → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ)
    (hd : ∀ i ∈ s, IsDat B Γ T (f i) (φ i)) (h0 : ∑ i ∈ s, img R Rf T (f i) (φ i) = 0) :
    Γ.M.I om (∑ i ∈ s, pure (f i) (φ i)) = 0 := by
  classical
  obtain ⟨-, ⟨c, hc, -⟩, -⟩ := ((hK.1 F E σ B a a' Γ X om om' hm.triple).2 R Rf hm).1
  have hM := hm.triple.geo.hM
  let e := s.equivFin
  let f' : Fin s.card → SInf F (Fin a × Fin (a + a')) := fun k => f (e.symm k).1
  let φ' : Fin s.card → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun k => φ (e.symm k).1
  have hd' : ∀ k, IsDat B Γ T (f' k) (φ' k) := fun k => hd _ (e.symm k).2
  choose g hg hgp using fun k => pure_eq_pureA Γ.M B.ψ hM (φ' k) (hd' k).2.1 (IsDat.cof (hd' k))
  have es : ∀ {M' : Type} [AddCommMonoid M'] (u : ι → M'), ∑ k, u (e.symm k).1 = ∑ i ∈ s, u i := fun u => by
    rw [← Finset.sum_coe_sort s u]
    exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
  have hΦ : ∑ i ∈ s, pure (f i) (φ i) = ∑ k, pureA F (f' k) (g k) := by
    rw [← es fun i => pure (f i) (φ i)]
    exact Finset.sum_congr rfl fun k _ => hgp k (f' k)
  have hmatch : Match B Γ X R Rf (∑ i ∈ s, pure (f i) (φ i)) 0 := by
    refine ⟨Submodule.zero_mem _, s.card, 0, g, f', fun _ => f', Fin.elim0, Fin.elim0, fun _ => Fin.elim0,
      fun i => ⟨hg i, tendsto_const_nhds⟩, fun j => j.elim0, hΦ, by simp, fun k => ⟨by simp, ?_⟩⟩
    refine ⟨T, hT, s.card, 0, f', φ', Fin.elim0, Fin.elim0, hd', fun j => j.elim0,
      Finset.sum_congr rfl fun k _ => (hgp k (f' k)).symm, by simp, ?_⟩
    have := es fun i => img R Rf T (f i) (φ i)
    rw [h0] at this
    simpa [img] using this
  funext h
  rw [hc _ _ hmatch h]
  simp [Model.I, theta, thetaSum]

theorem exists_ext {ι : Type} [DecidableEq ι] {X : ι → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (T T₁ : Finset ι) (hT : T ⊆ T₁) (s : ∀ i, X i) :
    ∃ e : (PiTensorProduct ℂ fun v : T => X v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T₁ => X v,
      ∀ u : ∀ i, X i, (∀ i ∉ T, u i = s i) →
        e (PiTensorProduct.tprod ℂ fun v : T => u v) = PiTensorProduct.tprod ℂ fun v : T₁ => u v := by
  let ext : (∀ v : T, X v) → ∀ v : T₁, X v := fun w v => if h : (v : ι) ∈ T then w ⟨v, h⟩ else s v
  have hupd : ∀ (inst : DecidableEq T) (w : ∀ v : T, X v) (i : T) (z : X i),
      ext (@Function.update _ _ inst w i z) = Function.update (ext w) ⟨i.1, hT i.2⟩ z := by
    intro inst w i z
    funext v
    by_cases hv : v = ⟨i.1, hT i.2⟩
    · subst hv
      simp [ext]
    · rw [Function.update_of_ne hv]
      by_cases h : (v : ι) ∈ T
      · have hne : (⟨v, h⟩ : T) ≠ i := fun e => hv (Subtype.ext (show (v : ι) = i.1 by rw [← e]))
        simp only [ext, dif_pos h]
        rw [Function.update_of_ne hne]
      · simp only [ext, dif_neg h]
  let m : MultilinearMap ℂ (fun v : T => X v) (PiTensorProduct ℂ fun v : T₁ => X v) :=
    { toFun := fun w => PiTensorProduct.tprod ℂ (ext w)
      map_update_add' := fun {inst} w i x y => by
        simp only [hupd inst]
        exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun {inst} w i c x => by
        simp only [hupd inst]
        exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }
  refine ⟨PiTensorProduct.lift m, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ (ext fun v : T => u v) = _
  congr 1
  funext v
  by_cases h : (v : ι) ∈ T
  · simp [ext, h]
  · simp only [ext, dif_neg h]
    exact (hu _ h).symm

end GlobalTheory.CompanionTheory.Ar.RT.Inj

end
