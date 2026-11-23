import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulOfSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiTargetBilinearFormIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearPositionMiddleVertexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearIsQuotIntTIntStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth)

noncomputable section
namespace GlobalTheory.PosOne

section Lemmas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem bilPos_exUp_exists {p : ℕ} (h1 : 1 ≤ p) (h2 : p < c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] {μ : kˣ →* ℂˣ}
    {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {b : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hb : BilPos ψ μ p σ b) :
    ∃ B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, BilPos ψ μ (p + 1) σ B ∧
      ∀ Ψ v, B Ψ v = exUp ν p σ (b Ψ) v := by
  let π : Representation ℂ (GL n k) (SB (Matrix n n' k)) :=
    (omR μ).comp (MonoidHom.inr (GL n' k) (GL n k))
  have hπv : ∀ g (Ψ : SB (Matrix n n' k)), (π g Ψ).1 = om μ 1 g Ψ.1 := fun _ _ => rfl
  have hpos : IsPos ψ p π σ b := ⟨hb.1, fun g φ v => hb.2 g φ (π g φ) v (hπv g φ)⟩
  obtain ⟨B, hB, hBpos⟩ :=
    ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c p h1 h2 ψ hψ hψ1 ν A σ hσ).2.2 _ π b).1 hpos
  refine ⟨B, ⟨hBpos.1, fun g Ψ Ψ₁ v hΨ => ?_⟩, hB⟩
  have e : Ψ₁ = π g Ψ := Subtype.ext (by rw [hΨ, hπv])
  rw [e]
  exact hBpos.2 g Ψ v

end Lemmas
end GlobalTheory.PosOne

noncomputable section
namespace GlobalTheory.PosOne

section LemmasB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable {P A : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]

theorem exists_fj_of_exUp {ρ : ℕ} (h1 : 1 ≤ ρ) (h2 : ρ < c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {ν : Measure k} (hν : IsSelfDual ψ ν)
    {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {b B : P →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hb : ∀ φ, IsNEquiv ψ ρ σ (b φ)) (hB : ∀ φ, IsNEquiv ψ (ρ + 1) σ (B φ))
    (hBb : ∀ φ v, B φ v = exUp ν ρ σ (b φ) v) :
    ∃ fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ, Represents ψ ν ρ σ fj B ∧
      ∀ φ v (Φ₀ : SB (n → k)), fj φ v Φ₀ =
        ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * b φ (σ (rowE c ρ u) v) ∂(Measure.pi fun _ => ν) := by
  have := hν.1
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have hS := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ
  have hI : ∀ φ v (Φ₀ : SB (n → k)),
      Integrable (fun β => Φ₀.1 β * B φ (σ (colE c (ρ + 1) β) v)) (Measure.pi fun _ => ν) := by
    intro φ v Φ₀
    have s := ((hS (B φ) v).2 (hB φ)).1
    exact GlobalTheory.RootEx.FourierJacobi.sb_int ⟨Φ₀.2.1.mul s.1, Φ₀.2.2.mul_right⟩
  let f : P → A → SB (n → k) → ℂ := fun φ v Φ₀ =>
    ∫ β, Φ₀.1 β * B φ (σ (colE c (ρ + 1) β) v) ∂(Measure.pi fun _ => ν)
  have fadd1 : ∀ φ φ' v Φ₀, f (φ + φ') v Φ₀ = f φ v Φ₀ + f φ' v Φ₀ := by
    intro φ φ' v Φ₀
    simp only [f, map_add, LinearMap.add_apply, mul_add]
    exact integral_add (hI φ v Φ₀) (hI φ' v Φ₀)
  have fsmul1 : ∀ (z : ℂ) φ v Φ₀, f (z • φ) v Φ₀ = z • f φ v Φ₀ := by
    intro z φ v Φ₀
    simp only [f, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext β; ring
  have fadd2 : ∀ φ v v' Φ₀, f φ (v + v') Φ₀ = f φ v Φ₀ + f φ v' Φ₀ := by
    intro φ v v' Φ₀
    simp only [f, map_add, mul_add]
    exact integral_add (hI φ v Φ₀) (hI φ v' Φ₀)
  have fsmul2 : ∀ (z : ℂ) φ v Φ₀, f φ (z • v) Φ₀ = z • f φ v Φ₀ := by
    intro z φ v Φ₀
    simp only [f, map_smul, smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext β; ring
  have fadd3 : ∀ φ v Φ₀ Φ₀', f φ v (Φ₀ + Φ₀') = f φ v Φ₀ + f φ v Φ₀' := by
    intro φ v Φ₀ Φ₀'
    simp only [f, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (hI φ v Φ₀) (hI φ v Φ₀')
  have fsmul3 : ∀ (z : ℂ) φ v Φ₀, f φ v (z • Φ₀) = z • f φ v Φ₀ := by
    intro z φ v Φ₀
    simp only [f, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext β; ring
  let fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => LinearMap.mk₂ ℂ (f φ) (fadd2 φ) (fun z v Φ₀ => fsmul2 z φ v Φ₀) (fadd3 φ)
        (fun z v Φ₀ => fsmul3 z φ v Φ₀)
      map_add' := fun φ φ' => by ext v Φ₀; exact fadd1 φ φ' v Φ₀
      map_smul' := fun z φ => by ext v Φ₀; exact fsmul1 z φ v Φ₀ }
  have fj_apply : ∀ φ v Φ₀, fj φ v Φ₀ = f φ v Φ₀ := fun _ _ _ => rfl
  refine ⟨fj, ⟨hB, fun φ v Φ₀ => ⟨hI φ v Φ₀, fj_apply φ v Φ₀⟩⟩, fun φ v Φ₀ => ?_⟩
  obtain ⟨s1, -, s3⟩ := (hS (b φ) v).1 (hb φ)
  have hh := (GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n ψ hψ hψ1 ν hν).1 Φ₀
  rw [fj_apply]
  simp only [f, hBb, s3, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, ← integral_const_mul, ← integral_mul_const]
  rw [integral_integral_swap]
  · congr 1; funext u; congr 1; funext β; ring
  · have := ((GlobalTheory.RootEx.FourierJacobi.sb_int (ν := ν) Φ₀.2).mul_prod
        (GlobalTheory.RootEx.FourierJacobi.sb_int (ν := ν) s1)).bdd_mul (c := 1)
      (f := fun z : (n → k) × (n → k) => (ψ (z.2 ⬝ᵥ z.1) : ℂ))
      (Continuous.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun z => (Circle.norm_coe _).le)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry]
    ring

end LemmasB
end GlobalTheory.PosOne

noncomputable section
namespace GlobalTheory.PosOne

theorem symDbl_existsUnique : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), ∃! z, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁.1 Φ₂.1 z := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ _ G₁ _ m₂ _ G₂ _ A _ _ σ hσ
    T hT F Φ₁ Φ₂
  have := hν.1
  have h1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega

  let ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) :=
    (omR μ₂).comp (MonoidHom.inl (GL (n₁ ⊕ Fin (c + 1)) k) (GL (n₂ ⊕ Fin c) k))
  have hρ₁v : ∀ g (Φ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), (ρ₁ g Φ).1 = om μ₂ g 1 Φ.1 :=
    fun _ _ => rfl
  have hρ₁s : IsSrc μ₂ ρ₁ := hρ₁v
  have hρ₁ : IsSmoothRep ρ₁ := by
    intro Φ
    have := omR_smooth (a := n₁ ⊕ Fin (c + 1)) (b := n₂ ⊕ Fin c) hμ₂ Φ
    exact this.preimage (continuous_id.prodMk continuous_const)

  let ρ₀ : Representation ℂ (GL (n₀ ⊕ Fin (c + 1 + 1)) k)
      (SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) :=
    (omR μ₁).comp (MonoidHom.inl (GL (n₀ ⊕ Fin (c + 1 + 1)) k) (GL (n₁ ⊕ Fin (c + 1)) k))
  have hρ₀s : IsSrc μ₁ ρ₀ := fun _ _ => rfl

  obtain ⟨b, hbpos, hbq, -⟩ := GlobalTheory.T.exists_bilinear_position_middle_vertex k n₀ n₁ n₂ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ G₁ m₂ G₂ A σ hσ
    T hT F ρ₁ hρ₁s

  obtain ⟨B, hBpos, hBb⟩ := bilPos_exUp_exists (c := c + 1) h1 (by omega) hψ hψ1 ν hρ₁ hbpos
  obtain ⟨fj, hrep, hfj⟩ := exists_fj_of_exUp (c := c + 1) h1 (by omega) hψ hψ1 hν hρ₁ hbpos.1 hBpos.1 hBb

  have hw : ∀ h Ψ (Φ₀ : SB (n₁ → k)), IsQuotInt ν m₂ G₂ ρ
      (fun h' => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h h' Φ₂.1)) (σ h' F)) (fj Ψ (ρ₁ h Φ₂) Φ₀) := by
    intro h Ψ Φ₀
    obtain ⟨-, hav⟩ := GlobalTheory.T.schwartzBruhat_self_average_heisenberg k n₂ n₁ c ρ h1 hρc ψ hψ hψ1 ν hν μ₂ hμ₂ (ρ₁ h Φ₂)
    obtain ⟨hmem, hop, hL⟩ := hav Φ₀
    have e1 := hbq Ψ ⟨_, hmem⟩
    have e2 : b Ψ ⟨_, hmem⟩ = fj Ψ (ρ₁ h Φ₂) Φ₀ := by
      rw [hfj, ← hL ρ₁ hρ₁s (b Ψ)]
      exact (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (b Ψ) ⟨_, hmem⟩).symm
    rw [e2] at e1
    convert e1 using 2 with h'
    simp only [tInt, hop]
    congr 3
    rw [hρ₁v]
    have := congrArg Subtype.val (omR_mul μ₂ (1 : GL (n₁ ⊕ Fin (c + 1)) k) h h' 1 Φ₂)
    simp only [omR_val, one_mul, mul_one] at this
    exact this.symm

  have hiff := GlobalTheory.T.fourierJacobi_target_bilinear_form_integral k n₁ n₀ (c + 1) ρ h1 (by omega) ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ _ ρ₁ hρ₁ fj B hrep hBpos
    Φ₂ Φ₁
  obtain ⟨Rr, hRr, -⟩ := GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n₁ n₀ (c + 1) (ρ + 1) (by omega) (by omega) ψ hψ hψ1 ν μ₁ hμ₁ m₁ G₁ _ ρ₁
    hρ₁ B hBpos Φ₂ ρ₀ hρ₀s
  refine ⟨Rr Φ₁, ⟨_, hw, (hiff _).1 (hRr Φ₁)⟩, ?_⟩
  rintro z ⟨w, hw', hz⟩
  have ew : w = fun h Ψ Φ₀ => fj Ψ (ρ₁ h Φ₂) Φ₀ := by
    funext h Ψ Φ₀
    exact (GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c ρ h1 hρc ν m₂ G₂ _).1 _ _ (hw' h Ψ Φ₀) (hw h Ψ Φ₀)
  subst ew
  exact (GlobalTheory.QuotInt.quotInt_unique_exists k n₁ (c + 1) (ρ + 1) (by omega) (by omega) ν m₁ G₁ _).1 _ _
    ((hiff z).2 hz) (hRr Φ₁)

end GlobalTheory.PosOne
