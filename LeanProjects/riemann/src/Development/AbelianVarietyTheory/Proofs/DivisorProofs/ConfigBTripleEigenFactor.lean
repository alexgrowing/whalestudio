import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariantAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentsSchwartzMembershipStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseBTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleConfigRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleConfigGlobalIdentity
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeBNZ

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tens_add' {R κ : Type} (ev : AF F → R) (x y : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (x + y) r = tens ev x r + tens ev y r := by
  funext t; simp [tens, add_mul]

theorem tens_smul' {R κ : Type} (ev : AF F → R) (c : ℂ) (x : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (c • x) r = c • tens ev x r := by
  funext t; simp [tens, mul_assoc]

theorem pure_add' {κ : Type} [Fintype κ] (x y : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (x + y) φ = pure x φ + pure y φ := by
  funext t; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul' {κ : Type} [Fintype κ] (c : ℂ) (x : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (c • x) φ = c • pure x φ := by
  funext t; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem I_smul' {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (om : Rep σ Y W) (c : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ W.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  unfold Model.I theta
  rw [← integral_const_mul]
  congr 1
  funext g
  rw [map_smul]
  unfold thetaSum
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

end H

theorem nonzero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    (∃ Φ₁' ∈ PolData B G₁.M' ⊓ G₁.M'.So B.ψ B.τ₁, G₁.M'.I om₁' Φ₁' ≠ 0) →
    ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ (h : UA σ G.W.J) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi (W₁ := G₁.W) H' 1 h₁ m ∧
      G₁.M'.I om₁' (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ')) h₁ ≠ 0 := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' K μK μ hKs hμK hμ hex
  obtain ⟨Φ₁, hΦ₁, hI₁⟩ := hex
  obtain ⟨h₁, hh₁⟩ := Function.ne_iff.1 hI₁
  obtain ⟨ei, ev, hei, hev, hloc⟩ := he'.loc
  have hlin := GlobalTheory.T.theta_lift_linear_combination hK F E σ B a b G₁ X om₁ om₁' hT₁
  have hinv := GlobalTheory.T.thetaLift_I_smul_left_eq hK F E σ B a b G₁ X om₁ om₁' hT₁
  have hstd₁ := hT₁.geo.hM'.std

  have hpure : ∃ (f₁ : SInf F (Fin b × Fin (a + b))) (φ₁ : ∀ v : Pl F, (Fin b × Fin (a + b) → Fv F v) → ℂ),
      (∀ v, φ₁ v ∈ SB (Fin b × Fin (a + b) → Fv F v)) ∧ (∀ᶠ v in cofinite, φ₁ v = G₁.M'.vac v) ∧
      φ₁ B.v₁ ∈ G₁.M'.SoLoc B.ψ B.τ₁ ∧ G₁.M'.I om₁' (pure f₁ φ₁) h₁ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hh₁
    have key : ∀ Φ ∈ G₁.M'.So B.ψ B.τ₁, G₁.M'.I om₁' Φ h₁ = 0 := by
      intro Φ hΦ
      induction hΦ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, φ, h1, h2, h3, rfl⟩ := hx
        exact hcon f φ h1 h2 h3
      | zero => simpa using I_smul' G₁.M' om₁' 0 0 h₁
      | add x y hx hy ihx ihy =>
        have := hlin x hx y hy 1 h₁
        rw [one_smul, one_mul] at this
        rw [this, ihx, ihy, add_zero]
      | smul c x hx ihx => rw [I_smul', ihx, mul_zero]
    exact key Φ₁ (Submodule.mem_inf.1 hΦ₁).2
  obtain ⟨f₁, φ₁, hφ₁SB, hφ₁vac, hφ₁v, hne₁⟩ := hpure
  have hfinφ₁ := Filter.eventually_cofinite.1 hφ₁vac
  let T : Finset (Pl F) := X.T ∪ {B.v₁} ∪ hfinφ₁.toFinset
  have hXT : X.T ⊆ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hv₁T : B.v₁ ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hoff : ∀ v, v ∉ T → φ₁ v = G₁.M'.vac v := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))

  obtain ⟨K', -, -, hK'1, hK'c, -, -⟩ := GlobalTheory.T.theta_stabilizer_exists hK.base F E σ B (b + 2) G.V' _ _ hT.base hT.geo.hV'
  have hKeq : K = K' := by
    ext g
    rw [hKs g, hK'1 g]
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := hKeq ▸ hK'c
  choose μKv hμKv using fun v : Pl F => (existsUnique_isNormK hKc (evFin F v)).exists
  choose μv hμv using fun v : Pl F => (existsUnique_isNormE E v).exists
  obtain ⟨μKi, hμKi⟩ := (existsUnique_isNormK hKc (evI F)).exists
  obtain ⟨μi, hμi⟩ := exists_haar_idelesAt E (evI F)
  let cF : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) → (Fin b × Fin (a + b) → Fv F v) → ℂ :=
    fun v φ => coneFin B G.M' om' v (ev v) K (μKv v) (μv v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ
  let cur : (∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) → Finset (Pl F) →
      ∀ v : Pl F, (Fin b × Fin (a + b) → Fv F v) → ℂ :=
    fun φ D v => if v ∈ D then cF v (φ v) else φ₁ v

  let P : Finset (Pl F) → Prop := fun D => ∃ φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ,
    (∀ v ∈ D, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) ∧ cF v (φ v) ∈ SB (Fin b × Fin (a + b) → Fv F v)) ∧
    (B.v₁ ∈ D → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ ∧ cF B.v₁ (φ B.v₁) ∈ G₁.M'.SoLoc B.ψ B.τ₁) ∧
    G₁.M'.I om₁' (pure f₁ (cur φ D)) h₁ ≠ 0
  have curSB : ∀ D φ, (∀ v ∈ D, φ v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) ∧
      cF v (φ v) ∈ SB (Fin b × Fin (a + b) → Fv F v)) → ∀ v, cur φ D v ∈ SB (Fin b × Fin (a + b) → Fv F v) := by
    intro D φ h v
    by_cases hv : v ∈ D
    · simp only [cur, if_pos hv]; exact (h v hv).2
    · simp only [cur, if_neg hv]; exact hφ₁SB v
  have curVac : ∀ D φ, ∀ᶠ v in cofinite, cur φ D v = G₁.M'.vac v := by
    intro D φ
    filter_upwards [hφ₁vac, D.finite_toSet.compl_mem_cofinite] with v h1 h2
    simp only [cur, if_neg (show v ∉ D from h2), h1]
  have curStd : ∀ D φ, ∀ᶠ v in cofinite,
      cur φ D v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    intro D φ
    filter_upwards [curVac D φ, hstd₁] with v h1 h2
    rw [h1, h2]
  have curV₁ : ∀ D φ, (B.v₁ ∈ D → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ ∧ cF B.v₁ (φ B.v₁) ∈ G₁.M'.SoLoc B.ψ B.τ₁) →
      cur φ D B.v₁ ∈ G₁.M'.SoLoc B.ψ B.τ₁ := by
    intro D φ h
    by_cases hv : B.v₁ ∈ D
    · simp only [cur, if_pos hv]; exact (h hv).2
    · simp only [cur, if_neg hv]; exact hφ₁v

  have pureSo : ∀ (f : SInf F (Fin b × Fin (a + b))) (ψ : ∀ v : Pl F, (Fin b × Fin (a + b) → Fv F v) → ℂ),
      (∀ v, ψ v ∈ SB (Fin b × Fin (a + b) → Fv F v)) → (∀ᶠ v in cofinite, ψ v = G₁.M'.vac v) →
      ψ B.v₁ ∈ G₁.M'.SoLoc B.ψ B.τ₁ → pure f ψ ∈ G₁.M'.So B.ψ B.τ₁ :=
    fun f ψ h1 h2 h3 => Submodule.subset_span ⟨f, ψ, h1, h2, h3, rfl⟩

  have stepFin : ∀ (D : Finset (Pl F)) (w : Pl F), w ∉ D → w ≠ B.v₁ → P D → P (insert w D) := by
    rintro D w hwD hw1 ⟨φ, hφ1, hφ2, hφ3⟩
    have hSB := curSB D φ hφ1
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor w f₁ (cur φ D) (curStd D φ)
    have hupdSB : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F w), ∀ v,
        Function.update (cur φ D) w ψ v ∈ SB (Fin b × Fin (a + b) → Fv F v) := by
      intro ψ hψ v
      by_cases hv : v = w
      · subst hv; rw [Function.update_self]; exact hψ
      · rw [Function.update_of_ne hv]; exact hSB v
    have hSo : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F w), tens (evFin F w) ψ r ∈ G₁.M'.So B.ψ B.τ₁ := by
      intro ψ hψ
      rw [hrt]
      refine pureSo f₁ _ (hupdSB ψ hψ) ?_ ?_
      · filter_upwards [curVac D φ, Filter.eventually_cofinite_ne w] with v h1 h2
        rw [Function.update_of_ne h2, h1]
      · rw [Function.update_of_ne (Ne.symm hw1)]; exact curV₁ D φ hφ2
    have hSchA : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F w), tens (evFin F w) ψ r ∈ schA F (Fin b × Fin (a + b)) := by
      intro ψ hψ
      rw [hrt]
      exact GlobalTheory.TensUniq.pure_mem_schA f₁ _ (hupdSB ψ hψ) (GlobalTheory.PureFactor.update_eventually _ w ψ (curStd D φ))
    let l₀ : ↥(SB (Fin b × Fin (a + b) → Fv F w)) →ₗ[ℂ] ℂ :=
      { toFun := fun ψ => G₁.M'.I om₁' (tens (evFin F w) ψ.1 r) h₁
        map_add' := fun x y => by
          simp only [Submodule.coe_add]
          rw [tens_add']
          have := hlin _ (hSo x.1 x.2) _ (hSo y.1 y.2) 1 h₁
          rwa [one_smul, one_mul] at this
        map_smul' := fun c x => by
          simp only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul]
          rw [tens_smul', I_smul'] }
    obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
    have hl' : ∀ ψ (hψ : ψ ∈ SB (Fin b × Fin (a + b) → Fv F w)), l ψ = G₁.M'.I om₁' (tens (evFin F w) ψ r) h₁ := by
      intro ψ hψ
      have := congrArg (fun g => g ⟨ψ, hψ⟩) hl
      simpa [l₀] using this
    obtain ⟨φw, hφw, hcw, hlw⟩ := GlobalTheory.T.triple_pair_period_identity_case_b_two hK F E σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei ev hei hev hloc K hKs
      w (μKv w) (μv w) (hμKv w) (hμv w) l
      (fun g _ ψ hψ ψ' hψ' hact => by
        rw [hl' ψ' hψ', hl' ψ hψ, ← hact r ⟨hr, hSchA ψ hψ⟩]
        exact hinv _ (hSo ψ hψ) g h₁)
      ⟨cur φ D w, hSB w, by
        rw [hl' _ (hSB w), hrt, Function.update_eq_self]
        exact hφ3⟩
    refine ⟨Function.update φ w φw, fun v hv => ?_, fun hv => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hv with hvw | hv
      · subst hvw
        rw [Function.update_self]
        exact ⟨hφw, hcw⟩
      · have hne : v ≠ w := fun h => hwD (h ▸ hv)
        rw [Function.update_of_ne hne]
        exact hφ1 v hv
    · have hv' : B.v₁ ∈ D := (Finset.mem_insert.1 hv).resolve_left (Ne.symm hw1)
      rw [Function.update_of_ne (Ne.symm hw1)]
      exact hφ2 hv'
    · have e : cur (Function.update φ w φw) (insert w D) = Function.update (cur φ D) w (cF w φw) := by
        funext v
        by_cases hv : v = w
        · subst hv; simp [cur]
        · simp [cur, Function.update_of_ne hv, Finset.mem_insert, hv]
      rw [e, ← hrt]
      intro h0
      exact hlw ((hl' _ hcw).trans h0)
  have stepV₁ : P {B.v₁} := by
    have hstdφ₁ : ∀ᶠ v in cofinite, φ₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hφ₁vac, hstd₁] with v h1 h2
      rw [h1, h2]
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor B.v₁ f₁ φ₁ hstdφ₁
    have hupd : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁), ∀ v,
        Function.update φ₁ B.v₁ ψ v ∈ SB (Fin b × Fin (a + b) → Fv F v) := by
      intro ψ hψ v
      by_cases hv : v = B.v₁
      · subst hv; rw [Function.update_self]; exact hψ
      · rw [Function.update_of_ne hv]; exact hφ₁SB v
    have hSchA : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁),
        tens (evFin F B.v₁) ψ r ∈ schA F (Fin b × Fin (a + b)) := by
      intro ψ hψ
      rw [hrt]
      exact GlobalTheory.TensUniq.pure_mem_schA f₁ _ (hupd ψ hψ) (GlobalTheory.PureFactor.update_eventually _ B.v₁ ψ hstdφ₁)
    let S1 : Submodule ℂ ((Fin b × Fin (a + b) → Fv F B.v₁) → ℂ) := Submodule.span ℂ (G₁.M'.SoLoc B.ψ B.τ₁)
    have hSo : ∀ ψ ∈ S1, tens (evFin F B.v₁) ψ r ∈ G₁.M'.So B.ψ B.τ₁ := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem x hx =>
        rw [hrt]
        refine pureSo f₁ _ (hupd x hx.1) ?_ ?_
        · filter_upwards [hφ₁vac, Filter.eventually_cofinite_ne B.v₁] with v h1 h2
          rw [Function.update_of_ne h2, h1]
        · rw [Function.update_self]; exact hx
      | zero =>
        have e0 : tens (evFin F B.v₁) (0 : (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ) r = 0 := by
          funext t; simp [tens]
        rw [e0]; exact zero_mem _
      | add x y _ _ hx hy => rw [tens_add']; exact add_mem hx hy
      | smul c x _ hx => rw [tens_smul']; exact Submodule.smul_mem _ c hx
    let l₀ : ↥S1 →ₗ[ℂ] ℂ :=
      { toFun := fun ψ => G₁.M'.I om₁' (tens (evFin F B.v₁) ψ.1 r) h₁
        map_add' := fun x y => by
          simp only [Submodule.coe_add]
          rw [tens_add']
          have := hlin _ (hSo x.1 x.2) _ (hSo y.1 y.2) 1 h₁
          rwa [one_smul, one_mul] at this
        map_smul' := fun c x => by
          simp only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul]
          rw [tens_smul', I_smul'] }
    obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
    have hl' : ∀ ψ (hψ : ψ ∈ S1), l ψ = G₁.M'.I om₁' (tens (evFin F B.v₁) ψ r) h₁ := by
      intro ψ hψ
      have := congrArg (fun g => g ⟨ψ, hψ⟩) hl
      simpa [l₀] using this
    obtain ⟨φv, hφv, hcv, hlv⟩ := GlobalTheory.T.seesaw_triple_config_restriction hK F E σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei ev hei hev hloc K hKs
      (μKv B.v₁) (μv B.v₁) (hμKv B.v₁) (hμv B.v₁) l
      (fun g _ ψ hψ ψ' hψ' hact => by
        rw [hl' ψ' (Submodule.subset_span hψ'), hl' ψ (Submodule.subset_span hψ), ← hact r ⟨hr, hSchA ψ hψ.1⟩]
        exact hinv _ (hSo ψ (Submodule.subset_span hψ)) g h₁)
      ⟨φ₁ B.v₁, hφ₁v, by
        rw [hl' _ (Submodule.subset_span hφ₁v), hrt, Function.update_eq_self]
        exact hne₁⟩
    let φ0 : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ := fun _ => 0
    refine ⟨Function.update φ0 B.v₁ φv, fun v hv => ?_, fun _ => ?_, ?_⟩
    · rw [Finset.mem_singleton.1 hv, Function.update_self]
      exact ⟨hφv.1, hcv.1⟩
    · rw [Function.update_self]; exact ⟨hφv, hcv⟩
    · have e : cur (Function.update φ0 B.v₁ φv) {B.v₁} = Function.update φ₁ B.v₁ (cF B.v₁ φv) := by
        funext v
        by_cases hv : v = B.v₁
        · subst hv; simp [cur]
        · simp [cur, Function.update_of_ne hv, hv]
      rw [e, ← hrt]
      intro h0
      exact hlv ((hl' _ (Submodule.subset_span hcv)).trans h0)
  have hind : ∀ D : Finset (Pl F), B.v₁ ∉ D → P (insert B.v₁ D) := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro _; rw [Finset.insert_empty]; exact stepV₁
    | @insert w D hwD ih =>
      intro hv
      have hw1 : w ≠ B.v₁ := fun h => hv (h ▸ Finset.mem_insert_self _ _)
      have hv' : B.v₁ ∉ D := fun h => hv (Finset.mem_insert_of_mem h)
      have := stepFin (insert B.v₁ D) w (by simp [hwD, hw1]) hw1 (ih hv')
      rwa [Finset.insert_comm] at this
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ : P T := by
    have := hind (T.erase B.v₁) (Finset.notMem_erase _ _)
    rwa [Finset.insert_erase hv₁T] at this

  have hSBT := curSB T φ hφ1
  have hSoT : ∀ g : SInf F (Fin b × Fin (a + b)), pure g (cur φ T) ∈ G₁.M'.So B.ψ B.τ₁ :=
    fun g => pureSo g _ hSBT (curVac T φ) (curV₁ T φ hφ2)
  let L : SInf F (Fin b × Fin (a + b)) →ₗ[ℂ] ℂ :=
    { toFun := fun g => G₁.M'.I om₁' (pure g (cur φ T)) h₁
      map_add' := fun x y => by
        show G₁.M'.I om₁' (pure (x + y) (cur φ T)) h₁ = G₁.M'.I om₁' (pure x (cur φ T)) h₁ + G₁.M'.I om₁' (pure y (cur φ T)) h₁
        rw [pure_add']
        have := hlin _ (hSoT x) _ (hSoT y) 1 h₁
        rwa [one_smul, one_mul] at this
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [pure_smul', I_smul'] }
  have hLc : Continuous L := GlobalTheory.T.continuous_modelI_pure_archComponent hK F E σ B a b G₁ X om₁ om₁' hT₁ (cur φ T) hSBT (curVac T φ) (curV₁ T φ hφ2) h₁
  let l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ := ⟨L, hLc⟩
  have hlapp : ∀ g, l g = G₁.M'.I om₁' (pure g (cur φ T)) h₁ := fun g => rfl
  obtain ⟨f, hf, hlf⟩ := GlobalTheory.T.seesaw_triple_config_global_identity hK F E σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei ev hei hev hloc K hKs
    μKi μi hμKi hμi l
    (fun k _ g g' hact => by
      have e1 : om₁' (k, 1) (pure g (cur φ T)) = pure g' (cur φ T) :=
        hact (GlobalTheory.EvZeroInf.finPart (cur φ T)) ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz,
          GlobalTheory.TensUniq.pure_mem_schA g _ hSBT (curStd T φ)⟩
      rw [hlapp, hlapp, ← e1]
      exact hinv _ (hSoT g) k h₁)
    (fun h0 => hφ3 (by rw [← hlapp, h0, ContinuousLinearMap.zero_apply]))
  obtain ⟨κ, hκ, heul⟩ := GlobalTheory.T.triple_pair_period_identity_case_b hK F E σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei ev hei hev hloc K hKs
    μK μ hμK hμ μKv μv μKi μi hμKv hμv hμKi hμi T hXT
  let φF : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ := fun v => if v ∈ T then φ v else G.M'.vac v
  have hφFSB : ∀ v, φF v ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) := by
    intro v
    by_cases hv : v ∈ T
    · simp only [φF, if_pos hv]; exact (hφ1 v hv).1
    · simp only [φF, if_neg hv]; exact (hT.geo.hM'.vac v).1
  have hφFoff : ∀ v, v ∉ T → φF v = G.M'.vac v := fun v hv => by simp only [φF, if_neg hv]
  have hφFvac : ∀ᶠ v in cofinite, φF v = G.M'.vac v := by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv using hφFoff v hv
  have hφFv₁ : φF B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ := by
    simp only [φF, if_pos hv₁T]; exact (hφ2 hv₁T).1
  have hcone := heul f φF hφFSB hφFoff
  have hfam : (fun v => if v ∈ T then coneFin B G.M' om' v (ev v) K (μKv v) (μv v) (shiftB σ H H') X.ν
      ((a - (b + 2)) / 2 + 1) (φF v) else G₁.M'.vac v) = cur φ T := by
    funext v
    by_cases hv : v ∈ T
    · simp only [cur, cF, φF, if_pos hv]
    · simp only [cur, if_neg hv]; exact (hoff v hv).symm
  rw [hfam] at hcone
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_levi_element_skew_cm F E σ B _ _ G.W G₁.W H' a (a + b + 1) _ _ hT.base.cm hT.geo.hW hC.hH' h₁
  refine ⟨pure f φF, Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨f, hf, φF, hφFSB, hφFvac, rfl⟩,
    Submodule.subset_span ⟨f, φF, hφFSB, hφFvac, hφFv₁, rfl⟩⟩, 1, h₁, m, hm, ?_⟩
  have h11 : om' (1, 1) = 1 := by rw [← Prod.one_eq_mk, map_one]
  rw [h11, Module.End.one_apply, hcone, I_smul']
  exact mul_ne_zero hκ hlf

end GlobalTheory.ConeBNZ
