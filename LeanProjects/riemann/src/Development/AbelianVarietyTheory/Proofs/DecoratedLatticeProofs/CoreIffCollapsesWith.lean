import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.FlatOmegaSeries
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemNormalizerOfTri
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulFrameMulFrameInvApply

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.CollapseCompare

section Average
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [AddCommGroup V] [Module ℂ V]

theorem exists_average (ρ : Representation ℂ G V) (hρ : IsSmoothRep ρ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) :
    ∃ e : V →ₗ[ℂ] V, (∀ g ∈ K, ∀ w, e (ρ g w) = e w) ∧ (∀ w, (∀ g ∈ K, ρ g w = w) → e w = w) ∧
      ∀ j : V →ₗ[ℂ] V, (∀ g w, j (ρ g w) = ρ g (j w)) → ∀ w, j (e w) = e (j w) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  borelize ↥K
  let η : Measure K := (Measure.haar : Measure K).inv
  have hne : ((η.real Set.univ : ℝ) : ℂ) ≠ 0 := by
    have : η.real Set.univ ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(isOpen_univ.measure_pos η Set.univ_nonempty).ne', measure_ne_top _ _⟩
    exact_mod_cast this
  let ρK : Representation ℂ K V := ρ.comp K.subtype
  have hs : PRep.IsSmooth ρK := fun v => (hρ v).preimage continuous_subtype_val
  let f : K → ℂ := fun _ => ((η.real Set.univ : ℝ) : ℂ)⁻¹
  have hf : IsLocallyConstant f := IsLocallyConstant.const _
  have hc : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  refine ⟨OpTrace.smoothOp ρK η f, fun g hg w => ?_, fun w hw => ?_, fun j hj w => ?_⟩
  · refine OpTrace.eq_of_forall_dual fun l => ?_
    rw [hs.map_smoothOp hf hc, hs.map_smoothOp hf hc,
      ← integral_mul_right_eq_self (μ := η) (fun x => f x • l (ρK x w)) ⟨g, hg⟩]
    congr 1
    funext x
    simp [ρK, f]
  · refine OpTrace.eq_of_forall_dual fun l => ?_
    rw [hs.map_smoothOp hf hc]
    have : (fun x : K => f x • l (ρK x w)) = fun _ => ((η.real Set.univ : ℝ) : ℂ)⁻¹ * l w :=
      funext fun x => by rw [show ρK x w = w from hw x x.2]; rfl
    rw [this, integral_const, Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · exact hs.map_smoothOp_of_intertwining hs hf hc j (fun g v => hj g v) w

theorem exists_equivariant {H : Type} [Group H] (ρ : Representation ℂ G V) (hρ : IsSmoothRep ρ)
    (π : Representation ℂ H V) (hcomm : ∀ g h w, π h (ρ g w) = ρ g (π h w)) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module ℂ P) (π' : Representation ℂ G P) (θ : P →ₗ[ℂ] V →ₗ[ℂ] V) (φ : P),
      IsSmoothRep π' ∧ (∀ g h T w, θ (π' g T) (ρ g (π h w)) = π h (θ T w)) ∧
        ∀ w, (∀ g ∈ K, ρ g w = w) → θ φ w = w := by
  obtain ⟨e, he1, he2, he3⟩ := exists_average ρ hρ K hK
  let τ := Representation.linHom ρ (Representation.trivial ℂ G V)
  let U : Submodule ℂ (V →ₗ[ℂ] V) :=
    { carrier := {T | ∀ h w, T (π h w) = π h (T w)}
      add_mem' := fun ha hb h w => by simp [ha h w, hb h w]
      zero_mem' := fun h w => by simp
      smul_mem' := fun z T hT h w => by simp [hT h w] }
  have hτ : ∀ g T w, τ g T w = T (ρ g⁻¹ w) := fun _ _ _ => rfl
  let τU := PRep.sub τ U fun g T hT h w => by rw [hτ, hτ, ← hcomm, hT]
  let eU : U := ⟨e, fun h w => (he3 (π h) (fun g w => hcomm g h w) w).symm⟩
  have heU : eU ∈ PRep.smoothPart τU :=
    SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds (one_mem _)) fun g hg =>
      Subtype.ext (LinearMap.ext fun w => he1 g⁻¹ (inv_mem hg) w))
  refine ⟨PRep.smoothPart τU, Submodule.addCommGroup _, Submodule.module _, PRep.smoothRep τU,
    U.subtype ∘ₗ (PRep.smoothPart τU).subtype, ⟨eU, heU⟩, SmGL.isSmooth_smoothRep _, fun g h T w => ?_, he2⟩
  refine Eq.trans ?_ (T.1.2 h w)
  change T.1.1 (ρ g⁻¹ (ρ g (π h w))) = _
  rw [← Module.End.mul_apply (ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end Average

section Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def omRep (μ : kˣ →* ℂˣ) : Representation ℂ (GL n' k × GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := omS μ g.1 g.2
      map_add' := fun Φ Ψ => Subtype.ext (funext fun x => by simp [omS, om, mul_add])
      map_smul' := fun z Φ => Subtype.ext (funext fun x => by simp [omS, om]; ring) }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (om_one μ Φ.1)
  map_mul' g h := LinearMap.ext fun Φ => Subtype.ext (om_mul μ g.1 h.1 g.2 h.2 Φ.1)

theorem omRep_smooth {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ)) : IsSmoothRep (omRep (n := n) (n' := n') μ) :=
  fun Φ => by
    convert isOpen_stabilizer_om hμ Φ.2 using 3
    exact Subtype.ext_iff

variable [MeasurableSpace k] [BorelSpace k]

def Core (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (bas : GL (n ⊕ Fin c) k) (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ)
    (lam : J →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (κ : ℝ) : Prop :=
  ∀ (V' V A : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    (π : Representation ℂ (GL n k) V) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) (b : V →ₗ[ℂ] A →ₗ[ℂ] ℂ),
    (∀ γ φ (Ψ Ψ' : SB (Matrix n n' k)), Ψ'.1 = om μ 1 γ Ψ.1 → θ φ Ψ' = π γ (θ φ Ψ)) → IsPos ψ 1 π σ b →
    ∀ (φ : V') (v : A), (∀ h : J, σ (h : GL (n ⊕ Fin c) k) v = (lam h : ℂ) • v) →
    ∀ f : GL (n ⊕ Fin c) k → ℂ, (∀ h (Ψ : SB (Matrix n n' k)), Ψ.1 = flat ψ ν μ Φ 1 h → f h = b (θ φ Ψ) (σ h v)) →
    ∀ Ξ : SB (Matrix n n' k), Ξ.1 = xi ψ ν μ Φ J bas 1 1 →
    ∀ z : ℂ, IsQuotInt ν μX μG 1 f z ↔ z = (κ : ℂ) * b (θ φ Ξ) v

variable {ν : Measure k} {μX : Measure (GL n k)} {μG : Measure (GL (n ⊕ Fin c) k)}
  {J : Subgroup (GL (n ⊕ Fin c) k)} {bas : GL (n ⊕ Fin c) k} {ψ : AddChar k Circle} {μ : kˣ →* ℂˣ}
  {lam : J →* ℂˣ} {κ : ℝ}

theorem Core.collapsesWith {Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)}
    (H : Core ν μX μG J bas ψ μ lam Φ.1 κ) : CollapsesWith ν μX μG J bas ψ μ lam Φ κ := by
  intro P' P A _ _ _ _ _ _ π' π σ _ _ _ b hb θ hθ φ F hF z
  refine H P' P A π σ θ b (fun γ φ Ψ Ψ' e => ?_) hb φ F hF _ (fun h Ψ e => ?_) _ rfl z
  · have := hθ 1 γ φ Ψ
    rw [map_one, Module.End.one_apply] at this
    rw [← this]
    exact congrArg _ (Subtype.ext e)
  · rw [show Ψ = flatS ψ ν μ Φ h from Subtype.ext e]; rfl

theorem isQuotInt_zero_iff {Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)}
    (H : CollapsesWith ν μX μG J bas ψ μ lam Φ κ) (z : ℂ) : IsQuotInt ν μX μG 1 (fun _ => 0) z ↔ z = 0 := by
  have := H ℂ ℂ ℂ 1 1 1 (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) 0
    ⟨fun φ g _ v => by simp, fun g φ v => by simp⟩ 0 (fun g h φ Ψ => by simp) 0 0 (fun κ => by simp) z
  rw [show integrand ψ ν μ Φ (1 : Representation ℂ _ ℂ) (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) (0 : ℂ →ₗ[ℂ] _ →ₗ[ℂ] ℂ) 0 0 =
    fun _ => 0 from funext fun h => by simp [integrand]] at this
  simpa using this

theorem core_of_collapsesWith (hc : 1 ≤ c) [ν.IsAddHaarMeasure] (hμ : IsOpen (μ.ker : Set kˣ))
    (hJ : IsOpen (J : Set (GL (n ⊕ Fin c) k))) {Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)}
    (hΦ : HasTargetType μ J lam Φ.1) (H : CollapsesWith ν μX μG J bas ψ μ lam Φ κ) :
    Core ν μX μG J bas ψ μ lam Φ.1 κ := by
  intro V' V A _ _ _ _ _ _ π σ θ b hθ hb φ v hv f hf Ξ hΞ z
  obtain rfl : Ξ = xiOneS ψ ν μ Φ J bas := Subtype.ext hΞ
  obtain rfl : f = integrand ψ ν μ Φ σ b θ φ v := funext fun h => hf h _ rfl
  by_cases h0 : Φ = 0
  · have e : ∀ h, flatS ψ ν μ Φ h = 0 := fun h => Subtype.ext (funext fun x => by
      simp [flatS, flat, opE, om, h0])
    have e' : xiOneS ψ ν μ Φ J bas = 0 := Subtype.ext (funext fun x => by
      simp [xiOneS, xi, flat, opE, om, h0])
    rw [e', show integrand ψ ν μ Φ σ b θ φ v = fun _ => 0 from funext fun h => by simp [integrand, e]]
    simpa using isQuotInt_zero_iff H z
  have := t2Space k
  have hvs : v ∈ PRep.smoothPart σ := by
    refine SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset ((hJ.inter ((isOpen_stabilizer_om hμ Φ.2).preimage
      (Continuous.prodMk_right (1 : GL (n' ⊕ Fin (c + 1)) k)))).mem_nhds ⟨one_mem J, om_one μ _⟩) ?_)
    rintro g ⟨hg, hg'⟩
    have h1 : (((lam ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ) • Φ.1 = (1 : ℂ) • Φ.1 := by rw [← hΦ ⟨g, hg⟩, one_smul]; exact hg'
    have h2 := smul_left_injective ℂ (fun h => h0 (Subtype.ext h)) h1
    have h3 : lam ⟨g, hg⟩ = 1 := inv_eq_one.1 (Units.ext h2)
    show σ g v = v
    simpa [h3] using hv ⟨g, hg⟩
  let ρ' : Representation ℂ (GL n' k) (SB (Matrix n n' k)) := (omRep μ).comp (MonoidHom.inl _ _)
  let πS : Representation ℂ (GL n k) (SB (Matrix n n' k)) := (omRep μ).comp (MonoidHom.inr _ _)
  have hρ' : IsSmoothRep ρ' := fun Ψ => (omRep_smooth hμ Ψ).preimage (Continuous.prodMk_left 1)
  have hπS : IsSmoothRep πS := fun Ψ => (omRep_smooth hμ Ψ).preimage (Continuous.prodMk_right 1)
  have hcomm : ∀ g h Ψ, πS h (ρ' g Ψ) = ρ' g (πS h Ψ) := fun g h Ψ => Subtype.ext (by
    change om μ 1 h (om μ g 1 Ψ.1) = om μ g 1 (om μ 1 h Ψ.1)
    rw [← om_mul, ← om_mul]; simp)
  let K₀ : Subgroup (GL n' k) :=
    { carrier := {g | om μ (embX (c + 1) g) 1 Φ.1 = Φ.1}
      one_mem' := by simp [om_one]
      mul_mem' := fun {x y} hx hy => by
        have := om_mul μ (embX (c + 1) x) (embX (c + 1) y) 1 1 Φ.1
        rw [hy, hx, mul_one, ← map_mul] at this
        exact this
      inv_mem' := fun {x} hx => by
        have := om_mul μ (embX (c + 1) x⁻¹) (embX (c + 1) x) 1 1 Φ.1
        rw [hx, mul_one, ← map_mul, inv_mul_cancel, map_one, om_one] at this
        exact this.symm }
  have hK₀ : IsOpen (K₀ : Set (GL n' k)) :=
    (isOpen_stabilizer_om hμ Φ.2).preimage ((Continuous.prodMk_left 1).comp QuotStep.continuous_embX)
  have hKo : IsOpen ((KO k n' ⊓ K₀ : Subgroup _) : Set (GL n' k)) := SplitFlip.isOpen_KO.inter hK₀
  have hKc : IsCompact ((KO k n' ⊓ K₀ : Subgroup _) : Set (GL n' k)) :=
    SplitFlip.isCompact_KO.inter_right (K₀.isClosed_of_isOpen hK₀)
  obtain ⟨P', _, _, π', θ', e, hπ', he1, he2⟩ := exists_equivariant ρ' hρ' πS hcomm _ hKo hKc
  have hfl : ∀ h, θ' e (flatS ψ ν μ Φ h) = flatS ψ ν μ Φ h := fun h => he2 _ fun g hg => Subtype.ext (by
    have h1 := (opE_om_embX k n n' c 1 le_rfl hc ψ ν μ (om μ 1 h Φ.1)).2 g
    have h2 : om μ (embX (c + 1) g) 1 (om μ 1 h Φ.1) = om μ 1 h (om μ (embX (c + 1) g) 1 Φ.1) := by
      rw [← om_mul, ← om_mul]; simp
    rw [nabs_eq_one_of_valuation_eq_one (valuation_det_of_mem_KO hg.1), Real.one_rpow, Complex.ofReal_one, one_smul,
      h2, show om μ _ 1 Φ.1 = Φ.1 from hg.2] at h1
    exact h1.symm)
  have hxi : θ' e (xiOneS ψ ν μ Φ J bas) = xiOneS ψ ν μ Φ J bas := by
    rw [show xiOneS ψ ν μ Φ J bas = (((volNat ν bas (Cgrp J 1))⁻¹ : ℝ) : ℂ) • flatS ψ ν μ Φ 1 from rfl, map_smul, hfl]
  have key := H P' _ _ π' πS (PRep.smoothRep σ) hπ' hπS
    (SmGL.isSmooth_smoothRep _) ((b ∘ₗ θ φ).compl₂ (PRep.smoothPart σ).subtype)
    ⟨fun Ψ g hg a => hb.1 (θ φ Ψ) g hg a, fun g Ψ a => by
      have := hb.2 g (θ φ Ψ) a
      rw [← hθ g φ Ψ (πS g Ψ) rfl] at this
      exact this⟩
    θ' (fun g h T Ψ => by
      refine Eq.trans (congrArg (θ' (π' g T)) (Subtype.ext ?_)) (he1 g h T Ψ)
      change om μ g h Ψ.1 = om μ g 1 (om μ 1 h Ψ.1)
      rw [← om_mul]; simp)
    e ⟨v, hvs⟩ (fun j => Subtype.ext (hv j)) z
  rw [hxi, show integrand ψ ν μ Φ _ _ θ' e _ = integrand ψ ν μ Φ σ b θ φ v from funext fun h => by
    change b (θ φ (θ' e _)) (σ h v) = b (θ φ _) (σ h v)
    rw [hfl]] at key
  exact key

omit [BorelSpace k] in
theorem flat_eq_smul (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (h : GL (n ⊕ Fin c) k) :
    flat ψ ν μ Φ 1 h = (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) • flat ψ ν 1 Φ 1 h := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, flat, flat, ← OpELevi.opE_const_mul]
  congr 1
  funext y
  simp only [om, map_one, MonoidHom.one_apply, inv_one, Units.val_one]
  ring

omit [MeasurableSpace k] [BorelSpace k] in
theorem om_eq_smul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (Φ : Matrix b a k → ℂ) (h : GL b k) :
    om 1 1 h Φ = (μ (Matrix.GeneralLinearGroup.det h) : ℂ) • om μ 1 h Φ := by
  funext y
  simp only [om, map_one, MonoidHom.one_apply, inv_one, Units.val_one, Pi.smul_apply, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  field_simp

def untwist (μ : kˣ →* ℂˣ) (lam : J →* ℂˣ) : J →* ℂˣ :=
  lam * (μ.comp (Matrix.GeneralLinearGroup.det.comp J.subtype))⁻¹

omit [MeasurableSpace k] [BorelSpace k] in
theorem hasTargetType_untwist {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : HasTargetType μ J lam Φ) :
    HasTargetType 1 J (untwist μ lam) Φ := fun j => by
  rw [om_eq_smul μ, hΦ j, smul_smul]
  simp [untwist]

omit [BorelSpace k] in
theorem oneCoset_untwist {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : OneCoset ψ ν μ Φ J) :
    OneCoset ψ ν 1 Φ J := by
  rw [oneCoset_iff] at hΦ ⊢
  refine fun h hh => hΦ h ?_
  rw [flat_eq_smul]
  exact smul_ne_zero (Units.ne_zero _) hh

omit [BorelSpace k] in

theorem core_of_untwist {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (H : Core ν μX μG J bas ψ 1 (untwist μ lam) Φ κ) : Core ν μX μG J bas ψ μ lam Φ κ := by
  intro V' V A _ _ _ _ _ _ π σ θ b hθ hb φ v hv f hf Ξ hΞ z
  refine H V' V A (SmGL.twist π (μ.comp Matrix.GeneralLinearGroup.det))
    (SmGL.twist σ (μ.comp Matrix.GeneralLinearGroup.det)⁻¹) θ b (fun γ φ Ψ Ψ' e => ?_)
    ⟨fun φ g hg a => ?_, fun g φ a => ?_⟩ φ v (fun j => ?_) f (fun h Ψ e => ?_) Ξ ?_ z
  · rw [SmGL.twist_apply, ← hθ γ φ Ψ (omS μ 1 γ Ψ) rfl, ← map_smul]
    exact congrArg _ (Subtype.ext (e.trans (om_eq_smul μ _ _)))
  · have : Matrix.GeneralLinearGroup.det g = 1 :=
      Units.ext (VolN.det_unitri (lev 1) _ (RootEx.Model.mem_N_iff.1 hg))
    simpa [this] using hb.1 φ g hg a
  · have : Matrix.GeneralLinearGroup.det (embX c g) = Matrix.GeneralLinearGroup.det g :=
      Units.ext (by simp [VolN.val_embX, Matrix.GeneralLinearGroup.val_det_apply])
    simp only [SmGL.twist_apply, map_smul, LinearMap.smul_apply, hb.2 g φ a, smul_eq_mul, MonoidHom.inv_apply,
      MonoidHom.comp_apply, this, Units.val_inv_eq_inv_val]
    field_simp
  · rw [SmGL.twist_apply, hv j, smul_smul]
    simp [untwist, mul_comm]
  · rw [hf h ((((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) • Ψ) (by rw [flat_eq_smul, ← e]; rfl)]
    simp
  · rw [hΞ]
    funext x
    simp only [xi]
    rw [flat_eq_smul μ]
    simp

end Pointwise

section Transport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def cjG (t : GL (n ⊕ Fin c) k) : GL (n ⊕ Fin c) k ≃ₜ* GL (n ⊕ Fin c) k where
  toMulEquiv := MulAut.conj t
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

theorem cjG_apply (t h : GL (n ⊕ Fin c) k) : cjG t h = t * h * t⁻¹ := rfl

def cjJ (t : GL (n ⊕ Fin c) k) (J : Subgroup (GL (n ⊕ Fin c) k)) : Subgroup (GL (n ⊕ Fin c) k) :=
  J.comap (MulAut.conj t).toMonoidHom

def cjLam (t : GL (n ⊕ Fin c) k) {J : Subgroup (GL (n ⊕ Fin c) k)} (lam : J →* ℂˣ) : cjJ t J →* ℂˣ :=
  lam.comp ((MulAut.conj t).toMonoidHom.subgroupComap J)

structure Adapted (t : GL (n ⊕ Fin c) k) : Prop where
  norm : t ∈ Subgroup.normalizer (N k n c 1 : Set (GL (n ⊕ Fin c) k))
  comm : ∀ g : GL n k, t * embX c g * t⁻¹ = embX c g

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Adapted.mem_N {t : GL (n ⊕ Fin c) k} (ht : Adapted t) {u : GL (n ⊕ Fin c) k} :
    t * u * t⁻¹ ∈ N k n c 1 ↔ u ∈ N k n c 1 := (Subgroup.mem_normalizer_iff.1 ht.norm u).symm

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Adapted.inv {t : GL (n ⊕ Fin c) k} (ht : Adapted t) : Adapted t⁻¹ :=
  ⟨inv_mem ht.norm, fun g => by conv_lhs => rw [← ht.comm g]
                                group⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Adapted.conj_mem_R {t : GL (n ⊕ Fin c) k} (ht : Adapted t) {u : GL (n ⊕ Fin c) k} (hu : u ∈ R k n c 1) :
    t * u * t⁻¹ ∈ R k n c 1 := by
  obtain ⟨x, w, hw, rfl⟩ := VolN.exists_of_mem_R hu
  rw [show t * (embX c x * w) * t⁻¹ = (t * embX c x * t⁻¹) * (t * w * t⁻¹) by group, ht.comm]
  exact mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right (ht.mem_N.2 hw))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Adapted.prX_cjJ {t : GL (n ⊕ Fin c) k} (ht : Adapted t) (J : Subgroup (GL (n ⊕ Fin c) k)) :
    prX (Cgrp (cjJ t J) 1) = prX (Cgrp J 1) := by
  have hR : ∀ u ∈ N k n c 1, ∀ g : GL n k, u * embX c g ∈ R k n c 1 := fun u hu g =>
    mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩)
  have e : ∀ u (g : GL n k), t * (u * embX c g) * t⁻¹ = t * u * t⁻¹ * embX c g := fun u g => by
    conv_rhs => rw [← ht.comm g]
    group
  ext g
  simp only [mem_prX, mem_Cgrp, inv_one, one_mul, mul_one]
  constructor
  · rintro ⟨u, hu, -, h⟩
    exact ⟨_, ht.mem_N.2 hu, hR _ (ht.mem_N.2 hu) g, e u g ▸ h⟩
  · rintro ⟨u, hu, -, h⟩
    refine ⟨_, ht.inv.mem_N.2 hu, hR _ (ht.inv.mem_N.2 hu) g, ?_⟩
    change t * _ * t⁻¹ ∈ J
    rw [e]
    simpa [mul_assoc] using h

variable [MeasurableSpace k] [BorelSpace k]

theorem Adapted.exists_map_volN {t : GL (n ⊕ Fin c) k} (ht : Adapted t) (ν ν₀ : Measure k) [ν.IsAddHaarMeasure]
    [ν₀.IsAddHaarMeasure] :
    ∃ r : ℝ≥0, r ≠ 0 ∧ (∀ F : GL (n ⊕ Fin c) k → ℂ,
        ∫ u : N k n c 1, F (t * u * t⁻¹) ∂(volN ν₀ n c 1) = (r : ℝ) • ∫ u : N k n c 1, F u ∂(volN ν n c 1)) ∧
      ∀ S S₀ : Subgroup (GL (n ⊕ Fin c) k), (∀ u ∈ N k n c 1, u ∈ S₀ ↔ t * u * t⁻¹ ∈ S) →
        volN ν₀ n c 1 (S₀.subgroupOf (N k n c 1)) = r * volN ν n c 1 (S.subgroupOf (N k n c 1)) := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (N k n c 1) := (VolN.isClosed_N 1).locallyCompactSpace
  haveI := VolN.isHaarMeasure_volN (n := n) (c := c) ν 1
  haveI := VolN.isHaarMeasure_volN (n := n) (c := c) ν₀ 1
  haveI : SecondCountableTopology (N k n c 1) := TopologicalSpace.Subtype.secondCountableTopology _
  let e := ConjVol.cj (N k n c 1) ⟨t, ht.norm⟩
  haveI := e.isHaarMeasure_map (volN ν₀ n c 1)
  have h := Measure.isMulLeftInvariant_eq_smul ((volN ν₀ n c 1).map e) (volN ν n c 1)
  refine ⟨_, (Measure.haarScalarFactor_pos_of_isHaarMeasure ((volN ν₀ n c 1).map e) (volN ν n c 1)).ne',
    fun F => ?_, fun S S₀ hS => ?_⟩
  · have h3 := integral_map_equiv (μ := volN ν₀ n c 1) e.toHomeomorph.toMeasurableEquiv (fun u : N k n c 1 => F u)
    rw [show ⇑e.toHomeomorph.toMeasurableEquiv = ⇑e from rfl, h, integral_smul_nnreal_measure] at h3
    exact h3.symm
  · have h3 := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := volN ν₀ n c 1) (S.subgroupOf (N k n c 1))
    rw [show ⇑e.toHomeomorph.toMeasurableEquiv = ⇑e from rfl, h] at h3
    refine Eq.trans ?_ (h3.symm.trans rfl)
    congr 1
    ext u
    exact hS u u.2

theorem isHaarMeasure_cj (t : GL (n ⊕ Fin c) k) (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] :
    (μG.map (cjG t).symm).IsHaarMeasure := by
  haveI := secondCountable k
  haveI := t2Space k
  exact (cjG t).symm.isHaarMeasure_map μG

theorem map_cjJ (t : GL (n ⊕ Fin c) k) (μG : Measure (GL (n ⊕ Fin c) k)) (J : Subgroup (GL (n ⊕ Fin c) k)) :
    μG.map (cjG t).symm (cjJ t J) = μG J := by
  haveI := secondCountable k
  haveI := t2Space k
  refine ((cjG t).symm.toHomeomorph.toMeasurableEquiv.map_apply _).trans ?_
  congr 1
  ext g
  change cjG t ((cjG t).symm g) ∈ J ↔ _
  simp

theorem Adapted.isQuotInt_iff {t : GL (n ⊕ Fin c) k} (ht : Adapted t) {ν ν₀ : Measure k} {r : ℝ≥0} (hr : r ≠ 0)
    (H : ∀ F : GL (n ⊕ Fin c) k → ℂ,
        ∫ u : N k n c 1, F (t * u * t⁻¹) ∂(volN ν₀ n c 1) = (r : ℝ) • ∫ u : N k n c 1, F u ∂(volN ν n c 1))
    (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ) :
    IsQuotInt ν₀ (r⁻¹ • μX) (μG.map (cjG t).symm) 1 (fun h => f (cjG t h)) z ↔ IsQuotInt ν μX μG 1 f z := by
  haveI := secondCountable k
  haveI := t2Space k
  have h1 : ∀ (F : GL (n ⊕ Fin c) k → ℂ) h,
      ∫ g, (∫ u : N k n c 1, F (cjG t (embX c g * (u : GL (n ⊕ Fin c) k) * h)) ∂(volN ν₀ n c 1)) ∂(r⁻¹ • μX) =
      ∫ g, (∫ u : N k n c 1, F (embX c g * (u : GL (n ⊕ Fin c) k) * cjG t h) ∂(volN ν n c 1)) ∂μX := fun F h => by
    have : ∀ g, ∫ u : N k n c 1, F (cjG t (embX c g * (u : GL (n ⊕ Fin c) k) * h)) ∂(volN ν₀ n c 1) =
        (r : ℝ) • ∫ u : N k n c 1, F (embX c g * (u : GL (n ⊕ Fin c) k) * cjG t h) ∂(volN ν n c 1) := fun g => by
      rw [← H fun x => F (embX c g * x * cjG t h)]
      simp only [map_mul, cjG_apply, ht.comm]
    simp only [this]
    rw [integral_smul_nnreal_measure, integral_smul, NNReal.smul_def, smul_smul]
    simp [hr]
  have h2 : ∀ F : GL (n ⊕ Fin c) k → ℂ, ∫ h, F (cjG t h) ∂(μG.map (cjG t).symm) = ∫ h, F h ∂μG := fun F => by
    refine (integral_map_equiv (cjG t).symm.toHomeomorph.toMeasurableEquiv _).trans ?_
    congr 1
    funext h
    exact congrArg F ((cjG t).apply_symm_apply h)
  have h3 : ∀ (e : GL (n ⊕ Fin c) k ≃ₜ* GL (n ⊕ Fin c) k), ∀ F ∈ SB (GL (n ⊕ Fin c) k),
      (fun h => F (e h)) ∈ SB (GL (n ⊕ Fin c) k) := fun e F hF =>
    ⟨hF.1.comp_continuous e.continuous, hF.2.comp_homeomorph e.toHomeomorph⟩
  constructor
  · rintro ⟨F₀, hF, ha, hb⟩
    obtain ⟨F, rfl⟩ : ∃ F : GL (n ⊕ Fin c) k → ℂ, F₀ = fun h => F (cjG t h) :=
      ⟨fun h => F₀ ((cjG t).symm h), by simp⟩
    refine ⟨F, by simpa using h3 (cjG t).symm _ hF, fun h => ?_, hb.trans (h2 F)⟩
    obtain ⟨h, rfl⟩ := (cjG t).surjective h
    exact (ha h).trans (h1 F h)
  · rintro ⟨F, hF, ha, hb⟩
    exact ⟨_, h3 (cjG t) F hF, fun h => (ha _).trans (h1 F h).symm, hb.trans (h2 F).symm⟩

end Transport

section Normalise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical (frame)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem frame_conj_apply (b : ℕ → kˣ) (u : GL (n ⊕ Fin c) k) (r s : n ⊕ Fin c) :
    (frame n c b * u * (frame n c b)⁻¹).val r s =
      Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k)) r *
        Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k)⁻¹) s * u.val r s := by
  simpa using IdealChain.smul_frame_mul_frame_inv_apply (1 : k) b b u.val r s

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem adapted_frame (b : ℕ → kˣ) : Adapted (frame n c b) := by
  refine ⟨ConjVol.mem_normalizer_of_tri ?_ ?_, fun g => Units.ext ?_⟩
  · rw [show (frame n c b).val = Matrix.diagonal (Sum.elim (fun _ : n => (1 : k))
      (fun i : Fin c => (b (i.val + 1) : k))) from by rw [← Matrix.fromBlocks_diagonal]; rfl]
    exact blockTriangular_diagonal _
  · rw [show ((frame n c b)⁻¹).val = Matrix.diagonal (Sum.elim (fun _ : n => (1 : k))
      (fun i : Fin c => (((b (i.val + 1))⁻¹ : kˣ) : k))) from by rw [← Matrix.fromBlocks_diagonal]; rfl]
    exact blockTriangular_diagonal _
  · ext r s
    rw [frame_conj_apply]
    rcases r with r | r <;> rcases s with s | s <;> simp [VolN.val_embX]
    by_cases h : r = s <;> simp [h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem simpleSum_frame (β : kˣ) (u : GL (n ⊕ Fin c) k) :
    simpleSum (frame n c (fun i => 1⁻¹ * β⁻¹ ^ i) * u * (frame n c fun i => 1⁻¹ * β⁻¹ ^ i)⁻¹) = β * simpleSum u := by
  unfold simpleSum
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [frame_conj_apply]
    simp only [Sum.elim_inr, h]
    simp [pow_succ]
    field_simp
    simp
  · simp

theorem hasConductor_mulShift {ψ : AddChar k Circle} {β : kˣ} (h : HasConductor ψ β) :
    HasConductor (ψ.mulShift (β : k)) 1 := by
  have hβ : 0 < valuation k (β : k) := by simp [zero_lt_iff]
  intro x
  have h1 := h (β * x)
  rw [map_mul, mul_le_iff_le_one_right hβ] at h1
  rw [Units.val_one, map_one, ← h1]
  simp only [AddChar.mulShift_apply]
  refine ⟨fun H y hy => ?_, fun H y hy => H _ (by rw [map_mul]; exact mul_le_mul_right hy _)⟩
  have := H ((β⁻¹ : kˣ) * y) (by rwa [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hβ])
  simpa using this

variable [MeasurableSpace k] [BorelSpace k]

theorem exists_rescaled (β : kˣ) (ν ν₀ : Measure k) [ν.IsAddHaarMeasure] [ν₀.IsAddHaarMeasure]
    {t : GL (n ⊕ Fin c) k} (ht : t = frame n c fun i => 1⁻¹ * β⁻¹ ^ i)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _) :
    ∃ Φ₀ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ ψ μ h, flat (ψ.mulShift (β : k)) ν₀ μ Φ₀ 1 h = flat ψ ν μ Φ 1 (t * h * t⁻¹)) ∧
      ∀ μ h (z : ℂ), om μ 1 (t * h * t⁻¹) Φ = z • Φ → om μ 1 h Φ₀ = z • Φ₀ := by
  obtain ⟨C, -, hC⟩ := IdealChain.opE_rescale_frame k n n' c 1 1 β (fun i => β⁻¹ ^ i) ν ν₀
    (fun i _ _ => by simp [pow_succ]) inferInstance inferInstance
  rw [← ht] at hC
  set t' := frame n' (c + 1) fun i => β⁻¹ ^ i
  simp only [Units.val_one, one_smul, inv_one] at hC
  have key : ∀ μ h, om μ 1 h (fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => (C : ℂ) * Φ (t.val * y * (t'⁻¹).val)) =
      fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => (C : ℂ) * om μ 1 (t * h * t⁻¹) Φ (t.val * y * (t'⁻¹).val) := fun μ h => by
    funext y
    have e1 : Matrix.GeneralLinearGroup.det (t * h * t⁻¹) = Matrix.GeneralLinearGroup.det h := by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    have e2 : ((t * h * t⁻¹)⁻¹).val * (t.val * y * (t'⁻¹).val) = t.val * ((h⁻¹).val * y) * (t'⁻¹).val := by
      rw [show (t * h * t⁻¹)⁻¹ = t * h⁻¹ * t⁻¹ by group]
      simp only [Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (t⁻¹).val, Units.inv_mul, Matrix.one_mul]
    simp only [om, e1, Units.val_one, Matrix.mul_one, e2]
    ring
  refine ⟨fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => (C : ℂ) * Φ (t.val * y * (t'⁻¹).val), (SB _).smul_mem (C : ℂ)
    (x := fun y => Φ (sideMul t'⁻¹ t⁻¹ y))
    ⟨hΦ.1.comp_continuous (sideMul t'⁻¹ t⁻¹).continuous, hΦ.2.comp_homeomorph (sideMul t'⁻¹ t⁻¹)⟩,
    fun ψ μ h => funext fun x => ?_, fun μ h z hz => ?_⟩
  · rw [flat, flat, hC, key, OpELevi.opE_const_mul]
  · rw [key, hz]
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem exists_reduction (β : kˣ) (ν ν₀ : Measure k) [ν.IsAddHaarMeasure] [ν₀.IsAddHaarMeasure]
    (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (J : Subgroup (GL (n ⊕ Fin c) k)) (lam : J →* ℂˣ)
    (bas : GL (n ⊕ Fin c) k) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _)
    (h1 : HasTargetType μ J lam Φ) (h2 : OneCoset ψ ν μ Φ J) :
    ∃ (t : GL (n ⊕ Fin c) k) (r : ℝ≥0), ∃ Φ₀ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), Adapted t ∧ r ≠ 0 ∧
      HasTargetType μ (cjJ t J) (cjLam t lam) Φ₀ ∧ OneCoset (ψ.mulShift (β : k)) ν₀ μ Φ₀ (cjJ t J) ∧
      (∀ m : Measure (GL n k), IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν₀ (t⁻¹ * bas) m = r⁻¹ • IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν bas m) ∧
      ∀ (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)) (κ : ℝ),
        Core ν₀ (r⁻¹ • μX) (μG.map (cjG t).symm) (cjJ t J) (t⁻¹ * bas) (ψ.mulShift (β : k)) μ (cjLam t lam) Φ₀ κ →
        Core ν μX μG J bas ψ μ lam Φ κ := by
  set t : GL (n ⊕ Fin c) k := frame n c fun i => 1⁻¹ * β⁻¹ ^ i with hdef
  have ht : Adapted t := adapted_frame _
  obtain ⟨r, hr, hI, hV⟩ := ht.exists_map_volN ν ν₀
  obtain ⟨Φ₀, hΦ₀, hfl, hom⟩ := exists_rescaled β ν ν₀ hdef hΦ
  have v1 := hV (stabLat bas) (stabLat (t⁻¹ * bas)) fun u _ => by simp [mem_stabLat, mul_assoc]
  have v2 := hV (Cgrp J 1) (Cgrp (cjJ t J) 1) fun u hu => by
    simp only [mem_Cgrp, inv_one, one_mul, mul_one]
    exact ⟨fun h => ⟨ht.conj_mem_R h.1, h.2⟩, fun h => ⟨Subgroup.mem_sup_right hu, h.2⟩⟩
  refine ⟨t, r, Φ₀, hΦ₀, ht, hr, fun j => hom μ j _ (h1 ⟨_, j.2⟩), ?_, fun m => ?_, fun μX μG κ H => ?_⟩
  · rw [oneCoset_iff] at h2 ⊢
    intro h hh
    rw [hfl] at hh
    obtain ⟨x, hx, j, hj, e⟩ := h2 _ hh
    refine ⟨_, ht.inv.conj_mem_R hx, t⁻¹ * j * t, ?_, ?_⟩
    · change t * _ * t⁻¹ ∈ J
      simpa [mul_assoc] using hj
    · rw [show t⁻¹ * x * t⁻¹⁻¹ * (t⁻¹ * j * t) = t⁻¹ * (x * j) * t by group, ← e]; group
  · rw [IndefiniteRowSideFullHecke.FramePositiveSum.rescale, IndefiniteRowSideFullHecke.FramePositiveSum.rescale, v1, ENNReal.smul_def, smul_smul, ENNReal.coe_inv hr,
      ENNReal.mul_inv (Or.inl (by simpa using hr)) (Or.inl ENNReal.coe_ne_top)]
  intro V' V A _ _ _ _ _ _ π σ θ b hθ hb φ v hv f hf Ξ hΞ z
  rw [← ht.isQuotInt_iff hr hI]
  refine H V' V A π (σ.comp (MulAut.conj t).toMonoidHom) θ b hθ ⟨fun φ g hg a => ?_, fun g φ a => ?_⟩ φ v
    (fun j => hv ⟨_, j.2⟩) _ (fun h Ψ e => hf _ Ψ (e.trans (hfl ψ μ h))) Ξ ?_ z
  · have := hb.1 φ _ (ht.mem_N.2 hg) a
    rw [simpleSum_frame] at this
    exact this
  · have := hb.2 g φ a
    rw [← ht.comm g] at this
    exact this
  · rw [hΞ]
    funext x
    have hr' : ((r : ℝ≥0∞)).toReal ≠ 0 := by simpa using hr
    simp only [xi, hfl, volNat, v1, v2, ENNReal.toReal_mul, mul_div_mul_left _ _ hr', mul_one, mul_inv_cancel]

end Normalise

section Main

theorem core_iff_collapsesWith {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c : ℕ} (hc : 1 ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k))
    (μG : Measure (GL (n ⊕ Fin c) k)) {J : Subgroup (GL (n ⊕ Fin c) k)} (hJ : IsOpen (J : Set (GL (n ⊕ Fin c) k)))
    (bas : GL (n ⊕ Fin c) k) (ψ : AddChar k Circle) {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ)) (lam : J →* ℂˣ)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (hΦ : HasTargetType μ J lam Φ.1) (κ : ℝ) :
    Core ν μX μG J bas ψ μ lam Φ.1 κ ↔ CollapsesWith ν μX μG J bas ψ μ lam Φ κ :=
  ⟨Core.collapsesWith, core_of_collapsesWith hc hμ hJ hΦ⟩

theorem collapse_of_weak (H : CollapseWeak) : SymChain.Collapse := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c hc μ P Φ hΦ hJ h1 h2 bas m hm μG hG
  have := hν.1
  obtain ⟨κ, hκ, H'⟩ := H k n c hc ν m μG hν.1 hm hG P.J hJ.1 hJ.2 bas n' ψ hψ.continuous hψ.ne_one 1
    (untwist μ P.lam) ⟨Φ, hΦ⟩ (hasTargetType_untwist h1) (oneCoset_untwist h2)
  exact ⟨κ, hκ, core_of_untwist (core_of_collapsesWith (Φ := ⟨Φ, hΦ⟩) hc (by simp) hJ.1 (hasTargetType_untwist h1) H')⟩

theorem isCO_cjJ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : GL (n ⊕ Fin c) k) {J : Subgroup (GL (n ⊕ Fin c) k)}
    (ho : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (hc : IsCompact (J : Set (GL (n ⊕ Fin c) k))) :
    IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (cjJ t J) := isOpen_isCompact_conj t⁻¹ ho hc

theorem weak_of_collapse (H : SymChain.Collapse) : CollapseWeak := by
  intro k _ _ _ _ _ _ n _ _ c hc ν μX μG hν hX hG J ho hcp bas n' _ _ ψ hψ hψ1 μ lam Φ h1 h2
  obtain ⟨β, hβ⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  obtain ⟨ν₀, hν₀⟩ := exists_isUnitVol k
  have := hν₀.1
  obtain ⟨t, r, Φ₀, hΦ₀, -, hr, a1, a2, -, a3⟩ := exists_reduction β ν ν₀ ψ μ J lam bas Φ.2 h1 h2
  obtain ⟨κ, hκ, H'⟩ := H k _ ν₀ (hasConductor_mulShift hβ) hν₀ n n' c hc μ ⟨cjJ t J, cjLam t lam⟩ Φ₀ hΦ₀
    (isCO_cjJ t ho hcp) a1 a2 (t⁻¹ * bas) (r⁻¹ • μX) (Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hr)) _
    (isHaarMeasure_cj t μG)
  exact ⟨κ, hκ, (a3 μX μG κ H').collapsesWith⟩

theorem collapse_of_exact (H : SymChain.CollapseExact) : IndefiniteRowSideFullHecke.FlatOmegaSeries.Collapse := by
  intro k _ _ _ _ _ _ n _ _ c hc ν μX μG hν hX hG J ho hcp bas
  have hv := (ENNReal.toReal_pos_iff.1 (volN_stabLat ν bas))
  set m : Measure (GL n k) := volN ν n c 1 ((stabLat bas).subgroupOf (N k n c 1)) • μX with hmdef
  have hm : m.IsHaarMeasure := Measure.IsHaarMeasure.smul _ hv.1.ne' hv.2.ne
  have hres : IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν bas m = μX := by
    rw [IndefiniteRowSideFullHecke.FramePositiveSum.rescale, hmdef, smul_smul, ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne, one_smul]
  obtain ⟨ν₀, hν₀⟩ := exists_isUnitVol k
  have := hν₀.1
  obtain ⟨ψ₁, hψ₁⟩ := exists_hasConductor_one k
  obtain ⟨p1, p2, -⟩ := H k ψ₁ ν₀ hψ₁ hν₀ n n c hc 1 ⟨J, 1⟩ 0 (zero_mem _) ⟨ho, hcp⟩
    (fun h => funext fun x => by simp [om])
    (fun β ⟨h, _, hh⟩ => absurd (funext fun x => by simp [flat, opE, om]) hh) bas m hm μG hG
  refine ⟨_, div_pos p1 p2, fun n' _ _ ψ hψ hψ1 μ lam Φ h1 h2 => ?_⟩
  obtain ⟨β, hβ⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  obtain ⟨t, r, Φ₀, hΦ₀, ht, hr, a1, a2, a4, a3⟩ := exists_reduction β ν ν₀ ψ μ J lam bas Φ.2 h1 h2
  obtain ⟨-, -, H'⟩ := H k _ ν₀ (hasConductor_mulShift hβ) hν₀ n n' c hc μ ⟨cjJ t J, cjLam t lam⟩ Φ₀ hΦ₀
    (isCO_cjJ t ho hcp) a1 a2 (t⁻¹ * bas) m hm _ (isHaarMeasure_cj t μG)
  rw [a4, hres, map_cjJ, ht.prX_cjJ] at H'
  exact (a3 μX μG _ H').collapsesWith

def CollapseUniform : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c →
    ∀ (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)),
    ν.IsAddHaarMeasure → μX.IsHaarMeasure → μG.IsHaarMeasure →
    ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
      IsCompact (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (bas : GL (n ⊕ Fin c) k),
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
      ∀ (μ : kˣ →* ℂˣ) (lam : J →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
        HasTargetType μ J lam Φ.1 → OneCoset ψ ν μ Φ.1 J → Core ν μX μG J bas ψ μ lam Φ.1 κ

theorem uniform_iff : CollapseUniform ↔ IndefiniteRowSideFullHecke.FlatOmegaSeries.Collapse := by
  refine ⟨fun H => ?_, fun H => ?_⟩ <;>
    intro k _ _ _ _ _ _ n _ _ c hc ν μX μG hν hX hG J ho hcp bas <;>
    obtain ⟨κ, hκ, H'⟩ := H k n c hc ν μX μG hν hX hG J ho hcp bas <;>
    refine ⟨κ, hκ, fun n' _ _ ψ hψ hψ1 μ lam Φ h1 h2 => ?_⟩
  · exact (H' n' ψ hψ hψ1 μ lam Φ h1 h2).collapsesWith
  · exact core_of_untwist (core_of_collapsesWith hc (by simp) ho (hasTargetType_untwist h1)
      (H' n' ψ hψ hψ1 1 _ Φ (hasTargetType_untwist h1) (oneCoset_untwist h2)))

theorem collapse_compare :
    (SymChain.Collapse ↔ CollapseWeak) ∧ (CollapseUniform ↔ IndefiniteRowSideFullHecke.FlatOmegaSeries.Collapse) ∧
      (IndefiniteRowSideFullHecke.FlatOmegaSeries.Collapse → SymChain.Collapse) ∧ (SymChain.CollapseExact → IndefiniteRowSideFullHecke.FlatOmegaSeries.Collapse) :=
  ⟨⟨weak_of_collapse, collapse_of_weak⟩, uniform_iff, fun H => collapse_of_weak H.weak, collapse_of_exact⟩

end Main

end GlobalTheory.CollapseCompare
