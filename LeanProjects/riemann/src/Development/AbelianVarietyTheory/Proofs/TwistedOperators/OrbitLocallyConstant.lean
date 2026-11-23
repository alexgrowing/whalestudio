import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMemSBEqOneOnCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvariaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpECutOmEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColEInvMulAffPt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSupportUniform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentSubgroupSuccDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralWhittakerTwist
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.Unfolding

section Basic
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def omR {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL a k × GL b k) (SB (Matrix b a k)) where
  toFun gh :=
    { toFun := fun Φ => ⟨om μ gh.1 gh.2 Φ.1, om_mem_SB μ gh.1 gh.2 Φ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext; funext x
        simp only [om, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun z Φ => by
        apply Subtype.ext; funext x
        simp only [om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (om_one μ Φ.1)
  map_mul' g h := LinearMap.ext fun Φ => Subtype.ext (om_mul μ g.1 h.1 g.2 h.2 Φ.1)

theorem omR_val {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)) : (omR μ (g, h) Φ).1 = om μ g h Φ.1 := rfl

theorem omR_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g g' : GL a k) (h h' : GL b k) (Φ : SB (Matrix b a k)) :
    omR μ (g, h) (omR μ (g', h') Φ) = omR μ (g * g', h * h') Φ :=
  Subtype.ext (om_mul μ g g' h h' Φ.1).symm

theorem omR_smooth {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {μ : kˣ →* ℂˣ}
    (hμ : IsOpen (μ.ker : Set kˣ)) : IsSmoothRep (omR (a := a) (b := b) μ) := by
  intro Φ
  have := isOpen_stabilizer_om hμ Φ.2
  convert this using 3 with gh
  exact Subtype.ext_iff

theorem orbit_locallyConstant {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (h : IsSmoothRep ρ) (v : V) :
    IsLocallyConstant fun g => ρ g v := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous fun y : G => g⁻¹ * y := by fun_prop
  filter_upwards [((h v).preimage hc).mem_nhds (x := g) (by simp)] with y hy
  have hy' : ρ (g⁻¹ * y) v = v := hy
  conv_rhs => rw [← hy', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def cut (p : ℕ) (χ : (n' → k) → ℂ) (y : Matrix (n ⊕ Fin c) n' k) : ℂ :=
  ∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) s) else 0

omit [Field k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem cut_lc (p : ℕ) {χ : (n' → k) → ℂ} (hχ : IsLocallyConstant χ) :
    IsLocallyConstant (cut (n := n) (c := c) p χ) := by
  have h : ∀ l : Fin c, IsLocallyConstant fun y : Matrix (n ⊕ Fin c) n' k => χ (fun s => y (Sum.inr l) s) :=
    fun l => hχ.comp_continuous (by fun_prop)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [eventually_all.2 fun l => (h l).eventually_eq x] with y hy
  simp only [cut, hy]

omit [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem cut_eq {p : ℕ} (hp : 1 ≤ p) (hc : p < c) (χ : (n' → k) → ℂ) (y : Matrix (n ⊕ Fin c) n' k) :
    cut p χ y = χ fun s => y (Sum.inr ⟨p - 1, by omega⟩) s := by
  unfold cut
  rw [Finset.sum_eq_single (⟨p - 1, by omega⟩ : Fin c), if_pos (by simp only; omega)]
  · intro l _ hl
    exact if_neg fun e => hl (Fin.ext (by simp only; omega))
  · simp

def cutL (p : ℕ) (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ) :
    SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) where
  toFun Φ := ⟨fun y => cut p χ y.toCols₁ * Φ.1 y,
    ((cut_lc p hχ).comp_continuous (continuous_matrix fun i j => by
      simp only [toCols₁, Matrix.of_apply]; fun_prop)).mul Φ.2.1, Φ.2.2.mul_left⟩
  map_add' Φ Ψ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' z Φ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable [MeasurableSpace k] [BorelSpace k]

def opL {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (p : ℕ) :
    SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] SB (Matrix n n' k) where
  toFun Φ := ⟨opE ψ ν p Φ.1, (opE_SB_and_linear k n n' c p ψ hψ ν).1 _ Φ.2⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    have := (opE_SB_and_linear k n n' c p ψ hψ ν).2 1 _ Φ.2 _ Ψ.2
    simpa using this
  map_smul' z Φ := by
    apply Subtype.ext; funext x
    simp only [opE, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      integral_const_mul]

end Basic

section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ)
  {A P P' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) {π : Representation ℂ (GL n k) P} {π' : Representation ℂ (GL n' k) P'}
  (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (φ : P') (F : A)

def fc (p : ℕ) (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (h : GL (n ⊕ Fin c) k) : ℂ :=
  b (θ φ (opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, h) Φ)))) (σ h F)

variable {μ σ θ b}

theorem fc_lc (hμ : IsOpen (μ.ker : Set kˣ)) (hσ : IsSmoothRep σ) (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    IsLocallyConstant (fc hψ ν μ σ θ b φ F p χ hχ Φ) := by
  have h1 : IsLocallyConstant fun h : GL (n ⊕ Fin c) k => omR μ (1, h) Φ :=
    (orbit_locallyConstant (omR_smooth hμ) Φ).comp_continuous (by fun_prop)
  exact (h1.prodMk (orbit_locallyConstant hσ F)).comp
    fun q => b (θ φ (opL hψ ν (p + 1) (cutL p χ hχ q.1))) q.2

theorem fc_equiv (hp : 1 ≤ p) (hc : p < c)
    (hθ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ)) (hb : IsPos ψ p π σ b)
    (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (x : GL n k) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c p ⊓ N k n c (p + 1)) (h : GL (n ⊕ Fin c) k) :
    fc hψ ν μ σ θ b φ F p χ hχ Φ (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) - 2 * p) : ℝ) : ℂ) *
        fc hψ ν μ σ θ b φ F p χ hχ Φ h := by
  unfold fc
  set Ψ := opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, h) Φ)) with hΨ
  have e1 : opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, embX c x * u * h) Φ)) =
      (((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        (ψ (-simpleSum u) : ℂ)) • omR μ (1, x) Ψ := by
    have := _root_.GlobalTheory.RootEx.opE_cut_om_equivariant k n n' c p hp hc ψ ν μ χ (omR μ (1, h) Φ).1 x u hu
    rw [← omR_val, omR_mul, one_mul] at this
    exact Subtype.ext this
  have e2 : θ φ (omR μ (1, x) Ψ) = π x (θ φ Ψ) := by
    have := hθ 1 x φ Ψ _ (omR_val μ 1 x Ψ)
    rwa [map_one, Module.End.one_apply] at this
  have e3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
  have e4 : (nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) - 2 * p) : ℝ) =
      nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) *
      nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) := by
    rw [← Real.rpow_add (nabs_pos k _)]; congr 1; push_cast; ring
  rw [e1, map_smul, map_smul, e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.smul_apply, hb.2, hb.1 _ u hu.1, e4]
  push_cast
  rw [smul_eq_mul]
  linear_combination (((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p : ℝ) + 1)) : ℝ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * b (θ φ Ψ) (σ h F)) * e3

theorem fc_supp (hp : 1 ≤ p) (hc : p < c) (hψ1 : ψ ≠ 1) (hσ : IsSmoothRep σ) (hb : IsPos ψ p π σ b)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ Ω : Set (GL (n ⊕ Fin c) k), IsCompact Ω ∧ ∀ χ hχ h, fc hψ ν μ σ θ b φ F p χ hχ Φ h ≠ 0 →
      ∃ x : GL n k, ∃ u ∈ N k n c p ⊓ N k n c (p + 1), ∃ w ∈ Ω, h = embX c x * u * w := by
  obtain ⟨Λ, hΛ, hΦ⟩ := GlobalTheory.T.schwartzBruhat_matrix_exists_open_addSubgroup_invariant k _ _ Φ.1 Φ.2
  obtain ⟨Ω, hΩ, H⟩ := opE_support_compact_mod_R k n n' c (p + 1) (by omega) hc ψ hψ hψ1 ν
    (tsupport Φ.1) Φ.2.2 Λ hΛ
  obtain ⟨B, hB, HB⟩ := _root_.GlobalTheory.RootEx.RowSupport.row_support_uniform k n c p hp hc ψ hψ1 A σ hσ F Ω hΩ
  refine ⟨_, (hB.image (ExchangeSupport.continuous_rowE (c := c) (p := p))).mul hΩ, fun χ hχ h hne => ?_⟩
  have h1 : opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, h) Φ)) ≠ 0 := by
    intro e; apply hne; unfold fc; rw [e]; simp
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, (opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, h) Φ))).1 x₀ ≠ 0 := by
    by_contra hh
    push Not at hh
    exact h1 (Subtype.ext (funext hh))
  obtain ⟨r, hr, w, hw, rfl⟩ := H μ Φ.1 (subset_tsupport _) hΦ (cut p χ) (cut_lc p hχ) h x₀ hx₀
  obtain ⟨x, g, hg, rfl⟩ := Radical.exists_of_mem_R hr
  obtain ⟨g₁, hg₁, u, rfl⟩ := GlobalTheory.T.rootExchangeUnipotentSubgroup_succ_decomposition k n c p g hg
  refine ⟨x, g₁, hg₁, rowE c p u * w, Set.mul_mem_mul (Set.mem_image_of_mem _ ?_) hw, by group⟩
  by_contra hu
  apply hne
  unfold fc
  generalize θ φ _ = φ₁
  have e : φ₁ = π x (π x⁻¹ φ₁) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e]
  simp only [map_mul, Module.End.mul_apply]
  rw [hb.2, hb.1 _ g₁ hg₁.1, HB _ (hb.1 _) w hw u hu]
  simp

theorem fc_row (hp : 1 ≤ p) (hc : p < c) {b₁ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hb₁ : ∀ φ v, b₁ φ v = exUp ν p σ (b φ) v)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (h : GL (n ⊕ Fin c) k) :
    ∫ u : n → k, fc hψ ν μ σ θ b φ F p (fun _ => 1) (IsLocallyConstant.const 1) Φ (rowE c p u * h)
        ∂(Measure.pi fun _ => ν) =
      b₁ (θ φ (opL hψ ν (p + 1) (omR μ (1, h) Φ))) (σ h F) := by
  rw [hb₁, exUp]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : opL hψ ν (p + 1) (cutL p (fun _ => 1) (IsLocallyConstant.const 1) (omR μ (1, rowE c p u * h) Φ)) =
      opL hψ ν (p + 1) (omR μ (1, h) Φ) := by
    have e0 : ∀ Ψ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
        cutL p (fun _ => 1) (IsLocallyConstant.const 1) Ψ = Ψ := fun Ψ => by
      apply Subtype.ext; funext y
      show cut p _ _ * Ψ.1 y = _
      rw [cut_eq hp hc, one_mul]
    have h1 := (Radical.unipotent_radical_basic k n c (p + 1)).2.2.2.2.2.2.1 p u (by omega)
    have := opE_om_target_unipotent k n n' c (p + 1) (by omega) hc ψ ν μ (omR μ (1, h) Φ).1 _ h1.1
    rw [← omR_val, omR_mul, one_mul, h1.2] at this
    rw [e0]
    apply Subtype.ext
    rw [neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_smul] at this
    exact this
  simp only [fc, e, map_mul, Module.End.mul_apply]

def ev {X : Type*} [TopologicalSpace X] (x : X) : SB X →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (SB X).subtype

theorem fc_col (hp : 1 ≤ p) (hc : p < c) (hμ : IsOpen (μ.ker : Set kˣ)) (hb : IsPos ψ p π σ b)
    (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ) (Φ Φχ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΦχ : ∀ l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, l Φχ =
      ∫ u : n' → k, χ u * l (omR μ (rowE (c + 1) p u, 1) Φ) ∂(Measure.pi fun _ => ν))
    (h : GL (n ⊕ Fin c) k) :
    ∫ β : n → k, fc hψ ν μ σ θ b φ F p χ hχ Φ (colE c (p + 1) β * h) ∂(Measure.pi fun _ => ν) =
      b (θ φ (opL hψ ν p (omR μ (1, h) Φχ))) (σ h F) := by
  have := secondCountable k
  have := t2Space k
  set Φ' := omR μ (1, h) Φ with hΦ'
  let T : (n → k) → SB (Matrix n n' k) := fun β =>
    opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, colE c (p + 1) β) Φ'))
  have hT : IsLocallyConstant T :=
    ((orbit_locallyConstant (omR_smooth hμ) Φ').comp_continuous
      (continuous_const.prodMk ExchangeSupport.continuous_colE)).comp
      fun Ψ => opL hψ ν (p + 1) (cutL p χ hχ Ψ)
  obtain ⟨K, hK, HK⟩ := _root_.GlobalTheory.RootEx.ColumnSupport.opE_colE_eq_zero k n n' c p hc ψ ν μ Φ'.1 Φ'.2
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n → k) (Measure.pi fun _ => ν) _ T hT K hK
    fun β hβ => Subtype.ext (HK β hβ fun y => cut p χ y.toCols₁)
  have e : opL hψ ν p (omR μ (1, h) Φχ) = w := by
    apply Subtype.ext; funext x₀
    have h1 := hΦχ ((ev x₀).comp ((opL hψ ν p).comp (omR μ (1, h))))
    have h2 := hw (ev x₀)
    have h3 := (_root_.GlobalTheory.RootEx.Exchange.opE_exchange k n n' c p hp hc ψ hψ ν μ Φ'.1 Φ'.2 x₀ χ hχ).2.2
    refine h1.trans (Eq.trans ?_ (h3.trans h2.symm))
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [LinearMap.comp_apply]
    rw [← omR_val, hΦ', omR_mul, omR_mul, one_mul, mul_one, one_mul, mul_one]
    rfl
  rw [e]
  refine Eq.trans ?_ (hw ((b.flip (σ h F)).comp (θ φ))).symm
  refine integral_congr_ae (Eventually.of_forall fun β => ?_)
  have h1 := (Radical.unipotent_radical_basic k n c p).2.2.2.2.2.2.2 (p + 1) β (by omega)
  simp only [fc, T, LinearMap.comp_apply, LinearMap.flip_apply, hΦ', omR_mul, one_mul, map_mul,
    Module.End.mul_apply]
  rw [hb.1 _ _ h1.1, h1.2]
  simp

theorem step_two (hp : 1 ≤ p) (hc : p < c) (hψ1 : ψ ≠ 1) (hμ : IsOpen (μ.ker : Set kˣ)) (hσ : IsSmoothRep σ)
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    (hθ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ)) (hb : IsPos ψ p π σ b)
    {b₁ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hb₁ : ∀ φ v, b₁ φ v = exUp ν p σ (b φ) v)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ C : Set (n' → k), IsCompact C ∧ ∀ χ : (n' → k) → ℂ, IsLocallyConstant χ → (∀ u ∈ C, χ u = 1) →
      ∀ Φχ, (∀ l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, l Φχ =
        ∫ u : n' → k, χ u * l (omR μ (rowE (c + 1) p u, 1) Φ) ∂(Measure.pi fun _ => ν)) →
      ∃ z, IsQuotInt ν μX μG p (fun h => b (θ φ (opL hψ ν p (omR μ (1, h) Φχ))) (σ h F)) z ∧
        IsQuotInt ν μX μG (p + 1) (fun h => b₁ (θ φ (opL hψ ν (p + 1) (omR μ (1, h) Φ))) (σ h F)) z := by
  obtain ⟨Ω, hΩ, H⟩ := fc_supp hψ ν φ F (μ := μ) (θ := θ) hp hc hψ1 hσ hb Φ
  let row : GL (n ⊕ Fin c) k × Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → n' → k :=
    fun q s => (q.1.val * q.2) (Sum.inr ⟨p - 1, by omega⟩) (Sum.inl s)
  have hrow : Continuous row := by
    refine continuous_pi fun s => ?_
    exact (((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd).matrix_elem _ _)
  refine ⟨row '' (Ω ×ˢ tsupport Φ.1), (hΩ.prod Φ.2.2).image hrow, fun χ hχ h1 Φχ hΦχ => ?_⟩
  have hw : ∀ w ∈ Ω, fc hψ ν μ σ θ b φ F p χ hχ Φ w =
      fc hψ ν μ σ θ b φ F p (fun _ => 1) (IsLocallyConstant.const 1) Φ w := by
    intro w hw
    unfold fc
    congr 4
    apply Subtype.ext; funext y
    show cut p _ _ * om μ 1 w Φ.1 y = cut p _ _ * om μ 1 w Φ.1 y
    by_cases hy : (w⁻¹).val * y * (1 : GL (n' ⊕ Fin (c + 1)) k).val ∈ tsupport Φ.1
    · rw [cut_eq hp hc, cut_eq hp hc, h1]
      refine ⟨(w, _), ⟨hw, hy⟩, ?_⟩
      funext s
      simp only [row, Units.val_one, Matrix.mul_one, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rfl
    · simp only [om, image_eq_zero_of_notMem_tsupport hy, mul_zero]
  have hf : fc hψ ν μ σ θ b φ F p χ hχ Φ =
      fc hψ ν μ σ θ b φ F p (fun _ => 1) (IsLocallyConstant.const 1) Φ := by
    funext h
    by_contra hne
    obtain ⟨x, u, hu, w, hw', rfl⟩ : ∃ x : GL n k, ∃ u ∈ N k n c p ⊓ N k n c (p + 1), ∃ w ∈ Ω,
        h = embX c x * u * w := by
      by_cases h0 : fc hψ ν μ σ θ b φ F p χ hχ Φ h = 0
      · exact H _ _ h fun e => hne (h0.trans e.symm)
      · exact H _ _ h h0
    apply hne
    rw [fc_equiv hψ ν φ F hp hc hθ hb χ hχ Φ x u hu w,
      fc_equiv hψ ν φ F hp hc hθ hb (fun _ => 1) (IsLocallyConstant.const 1) Φ x u hu w, hw w hw']
  obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.weil_formula_rootExchange_parabolic_intersection k n c p hp hc ν μX μG (fc hψ ν μ σ θ b φ F p χ hχ Φ)
    (fc_lc hψ ν φ F hμ hσ χ hχ Φ) ⟨Ω, hΩ, fun h hh => by
      obtain ⟨x, u, hu, w, hw', rfl⟩ := H _ _ h hh
      exact ⟨_, ⟨Subgroup.mul_mem_sup ⟨x, rfl⟩ hu.1, Subgroup.mul_mem_sup ⟨x, rfl⟩ hu.2⟩, w, hw', rfl⟩⟩
    (fc_equiv hψ ν φ F hp hc hθ hb χ hχ Φ)
  refine ⟨z, ?_, ?_⟩
  · simpa only [fc_col hψ ν φ F hp hc hμ hb χ hχ Φ Φχ hΦχ] using hz1
  · simpa only [hf, fc_row hψ ν φ F hp hc hb₁ Φ] using hz2

end Step

end GlobalTheory.RootEx.Unfolding
