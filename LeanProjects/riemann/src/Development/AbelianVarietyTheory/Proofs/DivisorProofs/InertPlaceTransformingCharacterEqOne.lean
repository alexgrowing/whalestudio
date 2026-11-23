import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTestStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersAgreeInertUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalIntegralHeisenbergTranslateIntegralIndicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDiagonalIntegralMemSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDiagonalIntegralExtendsLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralInjectiveSubspaceCompactOpenConstNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIntegralInvariantHeisenbergFirstVarsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianColumnsLinearParametrisationFinitePlacStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilOperatorDiagonalIntegralHeisenbergPoiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalarInertPlaceInvertibleShiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentBlockUnipotentIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirstStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertLagChar

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

def boxL {k κ κ' : Type} [CommRing k] (φ₂ : (κ' → k) → ℂ) : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → k) → ℂ) where
  toFun φ := boxFun φ φ₂
  map_add' a b := by funext x; simp [boxFun, add_mul]
  map_smul' a b := by funext x; simp [boxFun, mul_assoc]

variable {F : Type} [Field F] [NumberField F]

theorem one_sub_smul_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {u : M} (hu : At (evFin F v) u) :
    (1 - liftV v (1 : Fv F v)) • u = 0 := hu _ (by rw [map_sub, map_one, evFin_liftV, sub_self])

theorem smul_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {u : M} (hu : At (evFin F v) u) :
    liftV v (1 : Fv F v) • u = u := by
  have h := one_sub_smul_of_at hu
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

theorem at_of_one_sub_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {u : M}
    (h : (1 - liftV v (1 : Fv F v)) • u = 0) : At (evFin F v) u := fun t ht => by
  have h1 : t * (1 - liftV v (1 : Fv F v)) = t := by
    have h2 := at_liftV v (1 : Fv F v) t ht
    rw [smul_eq_mul] at h2
    rw [mul_sub, mul_one, h2, sub_zero]
  rw [← h1, mul_smul, h, smul_zero]

def Scales {κ : Type} [Fintype κ] (v : Pl F) (Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (a : ℂ) : Prop :=
  ∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T Φ Φ₁ ∧ Λ Φ₁ = a * Λ Φ

theorem Scales.mul {κ : Type} [Fintype κ] {v : Pl F} {Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ}
    {T T' : Module.End ℂ ((κ → AF F) → ℂ)} {a a' : ℂ} (h : Scales v Λ T a) (h' : Scales v Λ T' a')
    (hp : ∀ Φ ∈ schA F κ, T' Φ ∈ schA F κ) : Scales v Λ (T * T') (a * a') := by
  intro Φ hΦ
  obtain ⟨Φ₁, hΦ₁, hA₁, e₁⟩ := h' Φ hΦ
  obtain ⟨Φ₂, hΦ₂, hA₂, e₂⟩ := h Φ₁ hΦ₁
  refine ⟨Φ₂, hΦ₂, fun r hr => ?_, by rw [e₂, e₁, mul_assoc]⟩
  have hr1 : Rest (evFin F v) Φ₁ r := ⟨hr.1, by rw [← hA₁ r hr]; exact hp _ hr.2⟩
  show T (T' _) = _
  rw [hA₁ r hr, hA₂ r hr1]

theorem Scales.unique {κ : Type} [Fintype κ] {v : Pl F} {Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ}
    {T : Module.End ℂ ((κ → AF F) → ℂ)} {a a' : ℂ} (h : Scales v Λ T a) (h' : Scales v Λ T a')
    {Φ : (κ → Fv F v) → ℂ} (hΦ : Φ ∈ SB (κ → Fv F v)) (h0 : Λ Φ ≠ 0) : a = a' := by
  obtain ⟨Φ₁, -, hA₁, e₁⟩ := h Φ hΦ
  obtain ⟨Φ₂, -, hA₂, e₂⟩ := h' Φ hΦ
  have e : Φ₁ = Φ₂ := GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v Φ Φ₁ Φ₂ hΦ fun r hr => (hA₁ r hr).symm.trans (hA₂ r hr)
  rw [e, e₂] at e₁
  exact (mul_right_cancel₀ h0 e₁).symm

theorem scales_one {κ : Type} [Fintype κ] (v : Pl F) (Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Scales v Λ 1 1 :=
  fun Φ hΦ => ⟨Φ, hΦ, fun _ _ => rfl, (one_mul _).symm⟩

theorem scales_of_box {κ : Type} [Fintype κ] {v : Pl F} (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (T : Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (a : ℂ)
    (hex : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∃ Φ₁ ∈ SB (κ ⊕ κ → Fv F v), Acts (evFin F v) T Φ Φ₁)
    (r : (κ ⊕ κ → AF F) → ℂ) (hr0 : r 0 ≠ 0) (hr : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Rest (evFin F v) Φ r)
    (hbox : ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), ∀ Φ₁, Acts (evFin F v) T (boxFun φ₁ φ₂) Φ₁ →
      Λ Φ₁ = a * Λ (boxFun φ₁ φ₂)) : Scales v Λ T a := by
  let S : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → Fv F v) → ℂ) :=
    { toFun := fun f t => (r 0)⁻¹ * T (tens (evFin F v) f r) (fun i => liftV v (t i))
      map_add' := fun f f' => by
        have e : tens (evFin F v) (f + f') r = tens (evFin F v) f r + tens (evFin F v) f' r := by
          funext x; simp [tens, add_mul]
        funext t; simp only [e, map_add, Pi.add_apply]; ring
      map_smul' := fun c f => by
        have e : tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := by
          funext x; simp [tens, mul_assoc]
        funext t; simp only [e, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hS : ∀ f ∈ SB (κ ⊕ κ → Fv F v), ∀ f₁, Acts (evFin F v) T f f₁ → f₁ = S f := by
    intro f hf f₁ hA
    funext t
    show f₁ t = (r 0)⁻¹ * T (tens (evFin F v) f r) (fun i => liftV v (t i))
    rw [hA r (hr f hf)]
    have hat : At (evFin F v) (fun i => liftV v (t i)) := by
      intro u hu; funext i; exact at_liftV v _ u hu
    have h1 : r (fun i => liftV v (t i)) = r 0 := by
      simpa using (hr f hf).1 0 _ hat
    simp only [tens, h1, evFin_liftV]
    field_simp
  have key := GlobalTheory.T.linearForm_eq_zero_of_kills_productSchwartzBruhat F v κ κ ψ hψ hψ1 (Λ ∘ₗ S - a • Λ) (fun φ₁ h₁ φ₂ h₂ => by
    obtain ⟨Φ₁, -, hA⟩ := hex _ (box_mem_SB h₁ h₂)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply]
    rw [← hS _ (box_mem_SB h₁ h₂) Φ₁ hA, hbox φ₁ h₁ φ₂ h₂ Φ₁ hA, sub_self])
  intro Φ hΦ
  obtain ⟨Φ₁, hΦ₁, hA⟩ := hex Φ hΦ
  refine ⟨Φ₁, hΦ₁, hA, ?_⟩
  have h := key Φ hΦ
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at h
  rw [hS Φ hΦ Φ₁ hA]
  exact sub_eq_zero.1 h

theorem char_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    (∃ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), l φ ≠ 0) →
    ∀ c : UA σ G.V'.J → ℂ, (∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = c g * l φ) →
    ∀ g ∈ UAt σ G.V' (evFin F v), c g = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hv m C hC l hl hne c hc g hg
  obtain ⟨h2, -, hunr⟩ := hT.base.inert v w hin
  have hψc : Continuous (psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v
  have hψ1 : psiAt B.ψ v ≠ 1 := by
    obtain ⟨t, ht⟩ := GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hT.base.std v
    intro h; exact ht (by rw [h]; rfl)
  have hJ : IsUnit G.V'.J.det := GlobalTheory.isUnit_det_of_isHerm F E σ B a' G.V' _ _ hT.geo.hV'
  obtain ⟨-, ⟨d', hd', hBw⟩, -⟩ := hT.weil'
  obtain ⟨-, dd, omd, hdd, ⟨-, hspl, hsieg⟩, hres⟩ := hBw
  obtain ⟨L, hL, hinv, r₀, hr₀, c₀, hc₀, μ, hμ, hLφ, -⟩ := GlobalTheory.T.exists_admitted_diagonal_integral_linearForm F E σ a a' G B.ψ d' dd hdd v
  obtain ⟨hdm, N, j, ζ, hj, hζ, hζs, hT'⟩ := GlobalTheory.T.lagrangianColumns_linear_parametrisation_finitePlace F E σ a' (a + a') G.V' G.W G.M' v m C hC
  obtain ⟨ν, hν⟩ : ∃ ν : @Measure (Fin N → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν := by
    letI : MeasurableSpace (Fin N → Fv F v) := borel _
    haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
    exact ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨φ₀, hφ₀, c₁, hc₁, U, hUo, hUc, hU0, hU⟩ := GlobalTheory.T.diagonal_integral_heisenberg_translate_integral_indicator F v _ B.ψ hunr h2 μ hμ
  have hSB := GlobalTheory.T.heisenbergDiagonalIntegral_mem_schwartzBruhat F v _ _ hψc hψ1 μ hμ _ (box_mem_SB hφ₀ hφ₀) c₁ hc₁ U hUo hUc hU0 hU
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.lagrangian_diagonal_integral_extends_linearForm F v _ _ hψc μ hμ N ν hν j hj hSB
  have hΛ0 : Λ (boxFun φ₀ φ₀) ≠ 0 := by
    rw [hΛ _ (box_mem_SB hφ₀ hφ₀), lagInt]
    simp only [hU]
    exact GlobalTheory.T.integral_injectiveSubspace_compactOpen_const_ne_zero F v _ N ν hν j hj c₁ hc₁ U hUo hUc hU0
  have hlag : ∀ y, ζ y * Cᵀ ∈ lagAt v C := fun y =>
    ⟨fun t ht => by rw [← Matrix.smul_mul, (hζ y).1 t ht, Matrix.zero_mul], ζ y, rfl⟩
  have hiso : ∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2 := by
    intro y y'
    have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hC (-1) _ _ (hlag y) (hlag y')
    rw [G.M'.co.form] at h0
    have h1 := congrArg (evFin F v) h0
    rw [← sub_eq_zero, ← (hζ y).2, ← (hζ y').2]
    simpa [locCo, dotProduct, map_sum, map_mul, map_sub] using h1

  have hHeis : ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v), HeisInv G.M' B.ψ v C (Λ ∘ₗ boxL φ₂) := by
    rintro φ₂ hφ₂ u ⟨hu, z, hz⟩ φ hφ φ₁ hφ₁ hA
    obtain ⟨y, hy⟩ := hζs (liftV v (1 : Fv F v) • z) (fun t ht => by
      rw [smul_smul, ← smul_eq_mul, at_liftV v _ t ht, zero_smul])
    have hu' : u = ζ y * Cᵀ := by rw [hy, Matrix.smul_mul, ← hz, smul_of_at hu]
    have hA' := GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v u hu φ
    have e : φ₁ = _ := GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => (hA r hr).symm.trans (hA' r hr)
    show Λ (boxFun φ₁ φ₂) = Λ (boxFun φ φ₂)
    rw [hΛ _ (box_mem_SB hφ₁ hφ₂), hΛ _ (box_mem_SB hφ hφ₂), e, hu', (hζ y).2]
    exact GlobalTheory.T.isotropicIntegral_invariant_heisenberg_first_vars F v _ _ μ hμ N ν hν j hiso y φ φ₂
  obtain ⟨φt, hφt, hline⟩ := GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test F E σ a' (a + a') G.V' G.W G.M' B.ψ v hunr m C hC
  have hlt : l φt ≠ 0 := fun h => by
    obtain ⟨f, hf, hne⟩ := hne; exact hne (hline l hl h f hf)
  have hprop : ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Λ (boxFun φ φ₂) = Λ (boxFun φt φ₂) / l φt * l φ := by
    intro φ₂ hφ₂ φ hφ
    have hl' : HeisInv G.M' B.ψ v C (Λ ∘ₗ boxL φ₂ - (Λ (boxFun φt φ₂) / l φt) • l) := by
      intro u hu f hf f₁ hf₁ hA'
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hHeis φ₂ hφ₂ u hu f hf f₁ hf₁ hA', hl u hu f hf f₁ hf₁ hA']
    have h0 : (Λ ∘ₗ boxL φ₂ - (Λ (boxFun φt φ₂) / l φt) • l) φt = 0 := by
      show Λ (boxFun φt φ₂) - (Λ (boxFun φt φ₂) / l φt) * l φt = 0
      rw [div_mul_cancel₀ _ hlt, sub_self]
    exact sub_eq_zero.1 (hline _ hl' h0 φ hφ)
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))) v

  have hdiag : ∀ k ∈ UAt σ G.V' (evFin F v), ∀ kd : UG (cA σ) (dbl (incM F G.V'.J)),
      (kd.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
      Scales v Λ (omd kd) (c k) := by
    intro k hk kd hkd
    have hAt : At (evFin F v) ((kd.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
      intro u hu
      have hk1 : u • (mat k - 1) = 0 := hk u hu
      have e : Matrix.fromBlocks (mat k) 0 0 (1 : Matrix (Fin a') (Fin a') (AE F E)) - 1 =
          Matrix.fromBlocks (mat k - 1) 0 0 0 := by
        rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
        simp [sub_eq_add_neg]
      rw [hkd, e, Matrix.fromBlocks_smul]
      simp [hk1]
    refine scales_of_box _ hψc hψ1 Λ (omd kd) (c k) (GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v kd hAt) R hR0 hR ?_
    intro φ₁ h₁ φ₂ h₂ Φ₁ hA
    obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v k hk
    rw [GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first F v _ _ (om' (k, 1)) (omd kd) (fun Φ₁ h₁ Φ₂ h₂ => hres k kd hkd Φ₁ h₁ Φ₂ h₂) φ₁ h₁ φ₂ h₂ _ Φ₁ (hS φ₁ h₁).2 hA,
      hprop φ₂ h₂ _ (hS φ₁ h₁).1, hprop φ₂ h₂ φ₁ h₁, hc k hk φ₁ h₁ _ (hS φ₁ h₁).1 (hS φ₁ h₁).2]
    ring

  have hpar : ∀ (p : UG (cA σ) (dbl (incM F G.V'.J))) (t : GL (Fin a') (AE F E)),
      At (evFin F v) ((p.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) →
      (p.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) * diagCols (Fin a') = diagCols (Fin a') * t.val →
      Scales v Λ (omd p) 1 := by
    intro p t hp hpt Φ hΦ
    obtain ⟨Φ₁, hΦ₁, hA⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v p hp Φ hΦ
    refine ⟨Φ₁, hΦ₁, hA, ?_⟩
    obtain ⟨hdt, hnt, s, hs, hns⟩ := GlobalTheory.T.siegelParabolic_leviInverse_quotient_det_norm F E σ hT.base.cm a' G.V'.J hJ.ne_zero v p t hp hpt
    obtain ⟨T, hTζ, hTd⟩ := hT' s
    have hpt' := GlobalTheory.T.doubledWeilOperator_diagonalIntegral_heisenberg_point F E σ a' (a + a') G.V' G.W G.M' B.ψ hT.base.std.1 v m C hC d' hd' dd hdd omd hspl.toIsSplitting
      L hinv r₀ hr₀ c₀ hc₀ μ hLφ p _ (hsieg L hL hinv p t hpt) Φ hΦ Φ₁ hΦ₁ hA
    have hχ : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1 := by
      rw [MonoidHom.div_apply, GlobalTheory.InertChars.beta_eq_alpha_of_inert F E σ B a a' G X om om' hT v w hin hv
        (Matrix.GeneralLinearGroup.det t) hdt, div_self']
    set u : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t) with hu
    have hmod : (((adeleClass F).modu u : NNReal) : ℝ) =
        GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := GlobalTheory.T.distribHaarChar_supportedIdele_eq_localAbsValue F v u hnt
    have hdT : Matrix.GeneralLinearGroup.det T = (Units.map (evFin F v : AF F →* Fv F v) u) ^ m := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hTd, ← GlobalTheory.T.finitePlaceComponent_adeleNorm_eq_localNorm, hns, Units.val_pow_eq_pow_val]
      rfl
    have hpow : ∀ (x : (Fv F v)ˣ) (k : ℕ), GlobalTheory.SplitWeil.nabs (Fv F v) (x ^ k) = GlobalTheory.SplitWeil.nabs (Fv F v) x ^ k := by
      intro x k
      induction k with
      | zero => rw [pow_zero, pow_zero, GlobalTheory.SplitWeil.nabs_one]
      | succ k ih => rw [pow_succ, pow_succ, GlobalTheory.SplitWeil.nabs_mul, ih]
    have hexp : ((Fintype.card (Fin (a + a')) : ℝ) / 2) = (m : ℝ) := by
      rw [Fintype.card_fin, hdm]; push_cast; ring
    rw [hχ, hmod, hexp, Real.rpow_natCast, ← hpow, ← hdT, Circle.coe_one, one_mul] at hpt'
    rw [hΛ _ hΦ₁, hΛ _ hΦ, one_mul, lagInt, lagInt, ← GlobalTheory.T.normalizedAbsDet_mul_integral_comp_mulVec_finitePlace F v N ν hν T (fun y => diagW (psiAt B.ψ v) μ Φ (j y)),
      ← integral_const_mul]
    refine congrArg _ (funext fun y => ?_)
    rw [← (hζ y).2, hpt' _ (hζ y).1, ← hs, ← hTζ, (hζ _).2]

  obtain ⟨k, hk, α, β, hα, hβ, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unitaryScalar_inertPlace_invertible_shifts F E σ B hT.base v w hin a' G.V'.J g
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) g
  obtain ⟨kd, hkd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) k
  have hJA : IsUnit (incM F G.V'.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.map _
  have hee : liftV v (1 : Fv F v) * liftV v (1 : Fv F v) = liftV v (1 : Fv F v) := smul_of_at (at_liftV v 1)
  obtain ⟨p₁, p₂, t₁, t₂, hp₁, hp₂, ht₁, ht₂, hdec⟩ := GlobalTheory.T.idempotent_block_unipotent_identity (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) hJA _ hee g k
    (one_sub_smul_of_at hg) (one_sub_smul_of_at hk) α β (smul_of_at hα) (smul_of_at hβ) e1 e2 e3 e4 gd kd hgd hkd
  have hkk : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
  have hki : k⁻¹ ∈ UAt σ G.V' (evFin F v) := fun u hu => by
    have e : mat k⁻¹ - 1 = -((mat k - 1) * mat k⁻¹) := by rw [Matrix.sub_mul, hkk, Matrix.one_mul, neg_sub]
    rw [e, smul_neg, ← Matrix.smul_mul, hk u hu, Matrix.zero_mul, neg_zero]
  have hkdi : ((kd⁻¹).1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) = Matrix.fromBlocks (mat k⁻¹) 0 0 1 := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hkd, Matrix.fromBlocks_multiply]
    have : (k.1.1 : Matrix (Fin a') (Fin a') (AE F E)) * mat k⁻¹ = 1 := hkk
    simp [this, Matrix.fromBlocks_one]
  have s1 := hdiag k hk kd hkd
  have s2 := hdiag k⁻¹ hki kd⁻¹ hkdi
  have q1 := hpar p₁ t₁ (at_of_one_sub_smul hp₁) ht₁
  have q2 := hpar p₂ t₂ (at_of_one_sub_smul hp₂) ht₂
  have hb := box_mem_SB hφ₀ hφ₀
  have f1 : c k * c k⁻¹ = 1 := by
    have h := s1.mul s2 (hspl.pres _)
    rw [← map_mul, mul_inv_cancel, map_one] at h
    exact h.unique (scales_one v Λ) hb hΛ0
  have h := ((s1.mul q1 (hspl.pres _)).mul s2 (hspl.pres _)).mul q2 (hspl.pres _)
  rw [← map_mul, ← map_mul, ← map_mul, ← hdec, mul_one, mul_one, f1] at h
  exact (hdiag g hg gd hgd).unique h hb hΛ0

end GlobalTheory.InertLagChar
end
