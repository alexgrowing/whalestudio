import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F]

theorem isOp_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp ψ s S S') (ht : IsOp ψ t T T') : IsOp ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') where
  pres φ h := ht.pres _ (hs.pres φ h)
  pres' φ h := hs.pres' _ (ht.pres' φ h)
  left φ h := by simp only [LinearMap.comp_apply]; rw [ht.left _ (hs.pres φ h), hs.left φ h]
  right φ h := by simp only [LinearMap.comp_apply]; rw [hs.right _ (ht.pres' φ h), ht.right φ h]
  adm l hl := by rw [← LinearMap.comp_assoc]; exact hs.adm _ (ht.adm l hl)
  adm' l hl := by rw [← LinearMap.comp_assoc]; exact ht.adm' _ (hs.adm' l hl)
  Heisenberg₂ w φ h := by
    simp only [LinearMap.comp_apply, Function.comp_apply]
    rw [hs.Heisenberg₂ w φ h, ht.Heisenberg₂ _ _ (hs.pres φ h)]
  theta := by
    obtain ⟨c₁, hc₁, e₁⟩ := hs.theta
    obtain ⟨c₂, hc₂, e₂⟩ := ht.theta
    exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun φ h => by
      simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩
  norm μ μ'' hμ hμ'' := by
    letI : MeasurableSpace (κ' → AF F) := borel _
    haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
    haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
    obtain ⟨c₁, h1, h1', e₁⟩ := hs.norm μ Measure.addHaar hμ inferInstance
    obtain ⟨c₂, h2, h2', e₂⟩ := ht.norm Measure.addHaar μ'' inferInstance hμ''
    exact ⟨c₂ * c₁, mul_ne_zero h2 h1, ENNReal.mul_ne_top h2' h1', fun φ h => by
      simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩

theorem dblAct_comp {κ κ' κ'' : Type} (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) :
    dblAct (t ∘ s) = dblAct t ∘ dblAct s := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem isOp2_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp2 ψ s S S') (ht : IsOp2 ψ t T T') : IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  obtain ⟨hs1, Sd, Sd', hsd, hsb⟩ := hs
  obtain ⟨ht1, Td, Td', htd, htb⟩ := ht
  have hc : ∀ {ι : Type} [Fintype ι], ∀ φ ∈ schA F ι, star φ ∈ schA F ι := fun φ h => GlobalTheory.ConjSch.conj_mem_schA φ h
  refine ⟨isOp_comp hs1 ht1, Td ∘ₗ Sd, Sd' ∘ₗ Td', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · rw [dblAct_comp]; exact isOp_comp hsd htd
  · simp only [LinearMap.comp_apply]
    rw [hsb φ₁ h₁ φ₂ h₂, htb _ (hs1.pres _ h₁) _ (hc _ (hs1.pres _ (hc _ h₂))), star_star]

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

def addRe {X : Type} [TopologicalSpace X] [AddCommGroup X] (e : κ' ≃ κ) : (κ' → X) ≃ₜ+ (κ → X) where
  toFun x := x ∘ e.symm
  invFun y := y ∘ e
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

def reix {R : Type} (e : κ' ≃ κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : κ' → R => x ∘ e.symm)

theorem reix_apply {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e.symm) := rfl

theorem reix_symm_reix {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) : reix e.symm (reix e φ) = φ := by
  funext x; simp only [reix_apply, Equiv.symm_symm]; congr 1; funext i; simp

def linRe (e : κ' ≃ κ) : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e.symm).toContinuousLinearEquiv

theorem sb_reix (e : κ' ≃ κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y : κ' → FiniteAdeleRing (𝓞 F) F => g (y ∘ e.symm)) ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) :=
  ⟨hg.1.comp_continuous (addRe e).continuous, hg.2.comp_homeomorph (addRe e).toHomeomorph⟩

theorem reix_pureA (e : κ' ≃ κ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    reix e (pureA F f g) = pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e) f)
      (fun y => g (y ∘ e.symm)) := by
  funext x
  rfl

theorem reix_mem_schA (e : κ' ≃ κ) {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have hle : schA F κ ≤ (schA F κ').comap (reix e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, _, sb_reix e hg, reix_pureA e f g⟩
  exact hle h

theorem reix_adm (e : κ' ≃ κ) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ reix e ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl _ (sb_reix e hg)
  exact ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e)), fun f => by
    rw [LinearMap.comp_apply, reix_pureA]; exact hT _⟩

theorem reix_theta (e : κ' ≃ κ) (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AF F) (ξ i)))

theorem reix_heis (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    reix e (schr ψ w φ) = schr ψ (w.1 ∘ e, w.2 ∘ e) (reix e φ) := by
  have hd : ∀ u v : κ → AF F, (u ∘ e) ⬝ᵥ (v ∘ e) = u ⬝ᵥ v := fun u v => by
    simp only [dotProduct, Function.comp_apply]; exact Equiv.sum_comp e (fun i => u i * v i)
  funext x
  simp only [reix_apply, schr]
  have h1 : (x ∘ e.symm) ⬝ᵥ w.2 = x ⬝ᵥ (w.2 ∘ e) := by
    rw [← hd]; congr 1; funext i; simp
  have h2 : x ∘ e.symm + w.1 = (x + w.1 ∘ e) ∘ e.symm := by funext i; simp
  rw [h1, h2, hd]

theorem reix_norm (e : κ' ≃ κ) (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (hμ' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : (κ → AF F) → ℂ,
      ∫⁻ x, ‖reix e φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  letI : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  haveI := hμ'
  let L : (κ' → AF F) ≃ₜ+ (κ → AF F) := addRe e
  haveI : (μ'.map L).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ' L
  have heq := Measure.isAddLeftInvariant_eq_smul (μ'.map L) μ
  refine ⟨(Measure.addHaarScalarFactor (μ'.map L) μ : ℝ≥0∞),
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top,
    fun φ => ?_⟩
  have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) L.toHomeomorph.toMeasurableEquiv (μ := μ')
  have hL : (⇑L.toHomeomorph.toMeasurableEquiv : (κ' → AF F) → (κ → AF F)) = ⇑L := rfl
  rw [hL, heq, lintegral_smul_measure] at hm
  rw [ENNReal.smul_def, smul_eq_mul] at hm
  exact hm.symm

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem isOp_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) where
  pres _ h := reix_mem_schA e h
  pres' _ h := reix_mem_schA e.symm h
  left φ _ := reix_symm_reix e φ
  right φ _ := by simpa using reix_symm_reix e.symm φ
  adm _ hl := reix_adm e hl
  adm' _ hl := reix_adm e.symm hl
  Heisenberg₂ w φ _ := reix_heis ψ e w φ
  theta := ⟨1, one_ne_zero, fun φ _ => by rw [reix_theta, one_mul]⟩
  norm μ μ' hμ hμ' := by
    obtain ⟨c, h0, h1, h⟩ := reix_norm e μ μ' hμ hμ'
    exact ⟨c, h0, h1, fun φ _ => h φ⟩

theorem dblAct_reix (e : κ' ≃ κ) :
    dblAct (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) =
      fun w => (w.1 ∘ Equiv.sumCongr e e, w.2 ∘ Equiv.sumCongr e e) := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

theorem isOp2_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp2 ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  refine ⟨isOp_reix ψ e, reix (Equiv.sumCongr e e), reix (Equiv.sumCongr e e).symm, ?_, fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_reix]; exact isOp_reix ψ _
  · funext x
    simp only [reix_apply, boxFun, Pi.star_apply, star_star]
    congr 2 <;> funext i <;> simp

theorem realised_comp_reix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' :=
  fun _ _ _ ψ _ => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hs ht => isOp2_comp hs ht, fun _ _ _ _ e => ⟨_, _, isOp2_reix ψ e⟩⟩

end GlobalTheory.TowU.RealComp

end
