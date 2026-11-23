import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionsDoubleIntegralExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiTargetBilinearFormIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenberg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents RFJ app_coe)
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL)

noncomputable section
namespace GlobalTheory.DblInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem app_smul {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (l : SB X →ₗ[ℂ] V) {z : ℂ} (hz : z ≠ 0)
    (f : X → ℂ) : app l (z • f) = z • app l f := by
  by_cases h : f ∈ SB X
  · rw [show z • f = ((z • (⟨f, h⟩ : SB X) : SB X) : X → ℂ) from rfl, app_coe, map_smul, ← app_coe]
  · have h' : z • f ∉ SB X := fun h' => h ((Submodule.smul_mem_iff _ hz).1 h')
    simp [app, h, h']

omit [MeasurableSpace k] [BorelSpace k] in

theorem om_smul' {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k)
    (z : ℂ) (Φ : Matrix b a k → ℂ) : om μ g h (z • Φ) = z • om μ g h Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul]
  ring

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] in

theorem opE_smul (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (z : ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) : opE ψ ν p (z • Φ) = z • opE ψ ν p Φ := by
  funext x
  simp only [opE, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] in

theorem opEFJ_smul (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (z : ℂ) (Φ₀ : (n' → k) → ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) : opEFJ ψ ν p Φ₀ (z • Φ) = z • opEFJ ψ ν p Φ₀ Φ := by
  funext x
  simp only [opEFJ, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext u
  have := congrFun (opE_smul ψ ν p z (fun x => Φ (x + GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.rowM n c p u))) x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [mul_left_comm, ← this]
  rfl

theorem tInt_left {p : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
    {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ p σ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x : GL n k) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c p)
    (h : GL (n ⊕ Fin c) k) : tInt ψ ν μ p σ B F Φ.1 (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * tInt ψ ν μ p σ B F Φ.1 h := by
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1
  let E : GL (n ⊕ Fin c) k → SB (Matrix n n' k) := fun h =>
    ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩
  have hfE : ∀ h, tInt ψ ν μ p σ B F Φ.1 h = B (E h) (σ h F) := fun h => by
    unfold tInt
    rw [show opE ψ ν p (om μ 1 h Φ.1) = ((E h : SB (Matrix n n' k)) : Matrix n n' k → ℂ) from rfl, app_coe]
  have hmul : ∀ (g h : GL (n ⊕ Fin c) k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ),
      om μ 1 (g * h) Ψ = om μ 1 g (om μ 1 h Ψ) := fun g h Ψ => by
    rw [← om_mul, one_mul]
  set a : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) with ha
  let Ψ : SB (Matrix n n' k) := ⟨om μ 1 x (E h).1, om_mem_SB μ 1 x (E h).2⟩
  have h1 : E (embX c x * u * h) = (a * (ψ (-simpleSum u) : ℂ)) • Ψ := by
    apply Subtype.ext
    show opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) =
      (a * (ψ (-simpleSum u) : ℂ)) • om μ 1 x (opE ψ ν p (om μ 1 h Φ.1))
    rw [mul_assoc, hmul, (opE_om_embX k n n' c p hp hpc ψ ν μ _).1, hmul,
      opE_om_target_unipotent k n n' c p hp hpc ψ ν μ _ u hu]
    funext y
    simp only [om, Pi.smul_apply, smul_eq_mul, ha]
    ring
  have h3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
  have h4 : a * a =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) := by
    rw [ha, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos _ _)]
    congr 2
    ring
  have h5 := hB.1 (E h) u hu (σ h F)
  have h6 := hB.2 x (E h) Ψ (σ u (σ h F)) rfl
  rw [hfE, hfE, h1, map_smul, LinearMap.smul_apply, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply, h6, h5, ← h4, ← ha, smul_eq_mul]
  linear_combination (a * a * B (E h) (σ h F)) * h3

omit [BorelSpace k] in

theorem tInt_right (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (j : GL (n ⊕ Fin c) k) (l : ℂˣ) (h1 : om μ 1 j Φ = ((l⁻¹ : ℂˣ) : ℂ) • Φ) (h2 : σ j F = (l : ℂ) • F)
    (h : GL (n ⊕ Fin c) k) : tInt ψ ν μ p σ B F Φ (h * j) = tInt ψ ν μ p σ B F Φ h := by
  have e := om_mul μ 1 1 h j Φ
  rw [one_mul] at e
  unfold tInt
  rw [e, h1, om_smul', opE_smul, app_smul _ (Units.ne_zero _), map_mul, Module.End.mul_apply, h2, map_smul, map_smul,
    LinearMap.smul_apply, smul_smul]
  simp

theorem avg_RFJ {ρ : ℕ} (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (t : GL (n ⊕ Fin c) k → ℂ)
    (ht : ∀ (x : GL n k), ∀ u ∈ N k n c (ρ + 1), ∀ h, t (embX c x * u * h) =
      (((nabs k (Matrix.GeneralLinearGroup.det x))⁻¹ : ℝ) : ℂ) * t h)
    {r : GL (n ⊕ Fin c) k} (hr : r ∈ RFJ k n c ρ) (h : GL (n ⊕ Fin c) k) :
    ∫ β : n → k, t (colE c (ρ + 1) β * (r * h)) ∂(Measure.pi fun _ => ν) =
      ∫ β : n → k, t (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν) := by
  have := secondCountable k
  obtain ⟨H1, H2⟩ := FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2
  obtain ⟨r₁, hr₁, β₀, rfl⟩ := (H1 r).1 hr
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr₁
  have e : ∀ β : n → k, t (colE c (ρ + 1) β * (embX c x * u * colE c (ρ + 1) β₀ * h)) =
      (((nabs k (Matrix.GeneralLinearGroup.det x))⁻¹ : ℝ) : ℂ) *
        (fun γ => t (colE c (ρ + 1) (γ + β₀) * h)) ((x⁻¹).val.mulVec β) := by
    intro β
    rw [← ht x _ (H2 ((x⁻¹).val.mulVec β) u hu), ← FourierJacobiGroup.colE_add]
    congr 1
    simp only [← mul_assoc]
    rw [Exchange.colE_mul_embX]
    group
  simp only [e]
  rw [integral_const_mul, integral_comp_mulVec_eq_smul ν x⁻¹ (fun γ => t (colE c (ρ + 1) (γ + β₀) * h)),
    integral_add_right_eq_self (fun γ => t (colE c (ρ + 1) γ * h)) β₀, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul]
  have e2 : nabs k (Matrix.GeneralLinearGroup.det x⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det x))⁻¹ := by
    simp [nabs]
  rw [e2, inv_inv, inv_mul_cancel₀ (nabs_pos _ _).ne']
  simp

section Double
variable {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]

theorem exists_avg_form {ρ : ℕ} (hcρ : c + 1 = 2 * ρ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {ν : Measure k} (hν : IsSelfDual ψ ν) {μ₁ μ₂ : kˣ →* ℂˣ} (hμ₂ : IsOpen (μ₂.ker : Set kˣ))
    {τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A}
    {T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hT : TriPos ψ μ₁ μ₂ ρ τ T) (v : A) :
    ∃ (ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)))
      (B : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ),
      IsSrc μ₂ ρ₁ ∧ BilPos ψ μ₁ (ρ + 1) ρ₁ B ∧
      ∀ (Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
        (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) h w,
        HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h 1 Φ₂.1)) v) (fl ψ ν μ₁ ρ (om μ₁ 1 h Φ₁)) w →
        w = ∫ β : n₁ → k, tInt ψ ν μ₁ (ρ + 1) ρ₁ B Φ₂ Φ₁ (colE (c + 1) (ρ + 1) β * h) ∂(Measure.pi fun _ => ν) := by
  have := hν.1
  have h1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega
  let ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) :=
    (omR μ₂).comp (MonoidHom.inl (GL (n₁ ⊕ Fin (c + 1)) k) (GL (n₂ ⊕ Fin c) k))
  have hρ₁s : IsSrc μ₂ ρ₁ := fun _ _ => rfl
  have hρ₁ : IsSmoothRep ρ₁ := by
    intro Φ
    have := omR_smooth (a := n₁ ⊕ Fin (c + 1)) (b := n₂ ⊕ Fin c) hμ₂ Φ
    exact this.preimage (continuous_id.prodMk continuous_const)
  let b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    (T.compr₂ (LinearMap.applyₗ v)).compl₂ (opL hψ ν ρ)
  have hb : ∀ Ψ Φ, b Ψ Φ = T Ψ (opL hψ ν ρ Φ) v := fun _ _ => rfl
  have hL : ∀ Φ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k), (opL hψ ν ρ Φ).1 = opE ψ ν ρ Φ.1 := fun _ => rfl
  have hbpos : BilPos ψ μ₁ ρ ρ₁ b := by
    refine ⟨fun Ψ g hg Φ => ?_, fun g Ψ Ψ₁ Φ hΨ => ?_⟩
    · have e : opL hψ ν ρ (ρ₁ g Φ) = (ψ (simpleSum g) : ℂ) • opL hψ ν ρ Φ := Subtype.ext (by
        rw [hL, hρ₁s, GlobalTheory.RootExSource.opE_om_source k n₂ n₁ c ρ h1 hρc ψ ν μ₂ _ g hg]; rfl)
      rw [hb, hb, e, map_smul, LinearMap.smul_apply, smul_eq_mul]
    · let Ξ : SB (Matrix n₂ n₁ k) := ⟨om μ₂ g 1 (opL hψ ν ρ Φ).1, om_mem_SB μ₂ g 1 (opL hψ ν ρ Φ).2⟩
      have e : opL hψ ν ρ (ρ₁ (embX (c + 1) g) Φ) =
          ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) • Ξ := Subtype.ext (by
        rw [hL, hρ₁s, (opE_om_embX k n₂ n₁ c ρ h1 hρc ψ ν μ₂ _).2 g]; rfl)
      rw [hb, hb, e, map_smul, LinearMap.smul_apply, smul_eq_mul, hT.2 g Ψ Ψ₁ _ Ξ hΨ rfl]
      congr 3
      push_cast
      ring
  obtain ⟨B, hBpos, hBb⟩ := bilPos_exUp_exists (c := c + 1) h1 (by omega) hψ hψ1 ν hρ₁ hbpos
  obtain ⟨fj, hrep, hfj⟩ := exists_fj_of_exUp (c := c + 1) h1 (by omega) hψ hψ1 hν hρ₁ hbpos.1 hBpos.1 hBb
  have hw : ∀ Ψ (Φ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (Φ₀ : SB (n₁ → k)),
      app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 Φ.1) v = fj Ψ Φ Φ₀ := by
    intro Ψ Φ Φ₀
    obtain ⟨hmem, hop, hLL⟩ := (avg_self_and_props k n₂ n₁ c ρ h1 hρc ψ hψ hψ1 ν hν μ₂ hμ₂ Φ).2 Φ₀
    have e := hop 1
    rw [om_one, om_one] at e
    rw [hfj, ← hLL ρ₁ hρ₁s (b Ψ), ← e]
    refine Eq.trans ?_ (app_coe (b Ψ) ⟨_, hmem⟩).symm
    rw [hb]
    exact congrArg (fun l : A →ₗ[ℂ] ℂ => l v) (app_coe (T Ψ) (opL hψ ν ρ ⟨_, hmem⟩))
  refine ⟨ρ₁, B, hρ₁s, hBpos, ?_⟩
  rintro Φ₁ Φ₂ h w ⟨m, Ψ, Φ₀, hd, rfl⟩
  have hw' : ∀ Ψ (Φ₀ : SB (n₁ → k)), app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h 1 Φ₂.1)) v = fj Ψ (ρ₁ h Φ₂) Φ₀ :=
    fun Ψ Φ₀ => hw Ψ (ρ₁ h Φ₂) Φ₀
  simp only [hw', (hrep.2 _ _ _).2]
  rw [← integral_finset_sum _ fun i _ => (hrep.2 _ _ _).1]
  congr 1; funext β
  have e := om_mul μ₁ 1 1 (colE (c + 1) (ρ + 1) β) h Φ₁
  rw [one_mul] at e
  have : opE ψ ν (ρ + 1) (om μ₁ 1 (colE (c + 1) (ρ + 1) β) (om μ₁ 1 h Φ₁)) =
      (∑ i, (Φ₀ i).1 β • Ψ i : SB (Matrix n₁ n₀ k)).1 := by
    funext x₀
    refine (hd x₀ β).trans ?_
    simp [mul_comm]
  unfold tInt
  rw [e, this, app_coe, map_mul]
  simp

theorem pair_last {ρ : ℕ} (hcρ : c + 1 = 2 * ρ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {ν : Measure k} (hν : IsSelfDual ψ ν) {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ))
    {τ : Representation ℂ (GL (n ⊕ Fin c) k) A} {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ ρ τ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (j : GL (n ⊕ Fin c) k) (l : ℂˣ)
    (h1 : om μ 1 j Φ.1 = ((l⁻¹ : ℂˣ) : ℂ) • Φ.1) (h2 : τ j F = (l : ℂ) • F) {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c ρ)
    (x : GL (n' ⊕ Fin (c + 1)) k) (y : GL (n ⊕ Fin c) k) (Φ₀ : SB (n' → k)) :
    app B (opEFJ ψ ν ρ Φ₀.1 (om μ x (r * y * j) Φ.1)) (τ (r * y * j) F) = app B (opEFJ ψ ν ρ Φ₀.1 (om μ x y Φ.1)) (τ y F) := by
  have := hν.1
  have e := om_mul μ x 1 (r * y) j Φ.1
  rw [mul_one] at e
  have s1 : app B (opEFJ ψ ν ρ Φ₀.1 (om μ x (r * y * j) Φ.1)) (τ (r * y * j) F) =
      app B (opEFJ ψ ν ρ Φ₀.1 (om μ x (r * y) Φ.1)) (τ (r * y) F) := by
    rw [e, h1, om_smul', opEFJ_smul, app_smul _ (Units.ne_zero _), map_mul τ (r * y), Module.End.mul_apply, h2, map_smul,
      map_smul, LinearMap.smul_apply, smul_smul]
    simp
  let Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨om μ x 1 Φ.1, om_mem_SB μ x 1 Φ.2⟩
  obtain ⟨hmem, hop, -⟩ := (avg_self_and_props k n n' c ρ (by omega) (by omega) ψ hψ hψ1 ν hν μ hμ Φ').2 Φ₀
  have s2 : ∀ h, app B (opEFJ ψ ν ρ Φ₀.1 (om μ x h Φ.1)) (τ h F) = tInt ψ ν μ ρ τ B F (⟨_, hmem⟩ : SB _).1 h := by
    intro h
    have e := om_mul μ 1 x h 1 Φ.1
    rw [one_mul, mul_one] at e
    unfold tInt
    rw [hop h, e]
  obtain ⟨g, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  rw [s1, s2, s2, tInt_left (by omega) (by omega) hψ ν μ hB F _ g u hu]
  have : (c : ℝ) + 1 - 2 * ρ = 0 := by
    have : ((c + 1 : ℕ) : ℝ) = ((2 * ρ : ℕ) : ℝ) := by rw [hcρ]
    push_cast at this
    linarith
  rw [this]
  simp

theorem tensorVal_inv {ρ : ℕ} (hcρ : c + 1 = 2 * ρ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {ν : Measure k} (hν : IsSelfDual ψ ν) {μ₁ μ₂ : kˣ →* ℂˣ} (hμ₂ : IsOpen (μ₂.ker : Set kˣ))
    {τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A}
    {T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hT : TriPos ψ μ₁ μ₂ ρ τ T) (F : A)
    {L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1)) k)} {L₁ : Level (GL (n₁ ⊕ Fin (c + 1)) k)} {L₂ : Level (GL (n₂ ⊕ Fin c) k)}
    (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))
    (t₁ : HasTypes μ₁ L₀ L₁ Φ₁.1) (t₂ : HasTypes μ₂ L₁ L₂ Φ₂.1)
    (hF : ∀ j : L₂.J, τ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) (a x y)
    {r} (hr : r ∈ RFJ k n₁ (c + 1) ρ) {j} (hj : j ∈ L₁.J) {r'} (hr' : r' ∈ R k n₂ c ρ) {j'} (hj' : j' ∈ L₂.J) {z z' : ℂ}
    (hz' : HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ (r * x * j) (r' * y * j') Φ₂.1)) (τ (r' * y * j') F))
      (fl ψ ν μ₁ ρ (om μ₁ a (r * x * j) Φ₁.1)) z')
    (hz : HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ x y Φ₂.1)) (τ y F))
      (fl ψ ν μ₁ ρ (om μ₁ a x Φ₁.1)) z) : z' = z := by
  have := hν.1
  simp only [pair_last hcρ hψ hψ1 hν hμ₂ (hT.1 _) F Φ₂ j' (L₂.lam ⟨j', hj'⟩) (t₂.2 ⟨j', hj'⟩) (hF ⟨j', hj'⟩) hr'] at hz'
  obtain ⟨ρ₁, B, hρ₁, hB, H⟩ := exists_avg_form hcρ hψ hψ1 hν hμ₂ hT (τ y F)
  let Φ₁' : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) := ⟨om μ₁ a 1 Φ₁.1, om_mem_SB μ₁ a 1 Φ₁.2⟩
  let Φ₂' : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := ⟨om μ₂ 1 y Φ₂.1, om_mem_SB μ₂ 1 y Φ₂.2⟩
  have e1 : ∀ h, om μ₁ a h Φ₁.1 = om μ₁ 1 h Φ₁'.1 := fun h => by
    rw [show Φ₁'.1 = om μ₁ a 1 Φ₁.1 from rfl, ← om_mul, one_mul, mul_one]
  have e2 : ∀ h, om μ₂ h y Φ₂.1 = om μ₂ h 1 Φ₂'.1 := fun h => by
    rw [show Φ₂'.1 = om μ₂ 1 y Φ₂.1 from rfl, ← om_mul, one_mul, mul_one]
  rw [e1, e2] at hz hz'
  rw [H _ _ _ _ hz, H _ _ _ _ hz', mul_assoc r]
  have q1 : om μ₁ 1 j Φ₁'.1 = (((L₁.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • Φ₁'.1 := by
    rw [← e1, show Φ₁'.1 = om μ₁ a 1 Φ₁.1 from rfl, ← om_smul', ← t₁.2 ⟨j, hj⟩, ← om_mul, one_mul, mul_one]
  have q2 : ρ₁ j Φ₂' = (L₁.lam ⟨j, hj⟩ : ℂ) • Φ₂' := Subtype.ext (by
    rw [hρ₁, ← e2, Submodule.coe_smul, show Φ₂'.1 = om μ₂ 1 y Φ₂.1 from rfl, ← om_smul', ← t₂.1 ⟨j, hj⟩, ← om_mul, one_mul,
      mul_one])
  rw [avg_RFJ (by omega) (by omega) ν _ (fun g u hu h => ?_) hr]
  · simp only [← mul_assoc, tInt_right ψ ν μ₁ (ρ + 1) ρ₁ B Φ₂' Φ₁'.1 j _ q1 q2]
  · rw [tInt_left (by omega) (by omega) hψ ν μ₁ hB Φ₂' Φ₁' g u hu, ← Real.rpow_neg_one]
    congr 3
    have : ((c + 1 : ℕ) : ℝ) = ((2 * ρ : ℕ) : ℝ) := by rw [hcρ]
    rw [this]
    push_cast
    ring

end Double

end GlobalTheory.DblInv
