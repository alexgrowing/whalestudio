import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.IsGerm
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3

def LocSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ) (P : Submodule ℂ (SB (Matrix (Fin n) (Fin r) k))) (Φ : SB (Matrix (Fin n) (Fin r) k)), (∀ x, Φ.1 x ≠ 0 → ∃ U : Set (Matrix (Fin n) (Fin r) k), IsOpen U ∧ x ∈ U ∧ ∀ Ψ : SB (Matrix (Fin n) (Fin r) k), (∀ y, Ψ.1 y ≠ 0 → y ∈ U ∧ Φ.1 y ≠ 0) → Ψ ∈ P) → Φ ∈ P

def BallSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ), (∀ (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k), IsOpen (ballM c x₀) ∧ IsCompact (ballM c x₀) ∧ (ballM c x₀).indicator (fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k) ∧ (∀ x ∈ ballM c x₀, ballM c x = ballM c x₀) ∧ ∀ h ∈ KO k (Fin n), ∀ g ∈ KO k (Fin r), ∀ x, h.val * x * g.val ∈ ballM c (h.val * x₀ * g.val) ↔ x ∈ ballM c x₀) ∧ (∀ (x₀ : Matrix (Fin n) (Fin r) k) (U : Set (Matrix (Fin n) (Fin r) k)), U ∈ nhds x₀ → ∃ c : kˣ, valuation k (c : k) < 1 ∧ ballM c x₀ ⊆ U) ∧ ∀ Ψ : SB (Matrix (Fin n) (Fin r) k), ∃ c₀ : kˣ, ∀ c : kˣ, valuation k (c : k) ≤ valuation k (c₀ : k) → ∃ S : Finset (Matrix (Fin n) (Fin r) k), (∀ x ∈ S, ∀ y ∈ ballM c x, Ψ.1 y = Ψ.1 x ∧ Ψ.1 x ≠ 0) ∧ Ψ.1 = ∑ x ∈ S, Ψ.1 x • (ballM c x).indicator (fun _ => (1 : ℂ))

def NfSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r j : ℕ) (x : Matrix (Fin n) (Fin r) k), x.rank = j → (∃ (h : GL (Fin n) k) (g : GL (Fin r) k), x = h.val * idem k r n j * g.val) ∧ ∀ c : kˣ, valuation k (c : k) < 1 → x ∈ ballM c (idem k r n j) → ∃ h ∈ KO k (Fin n), ∃ g ∈ KO k (Fin r), x = h.val * idem k r n j * g.val

def RkSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r j : ℕ), j ≤ n → j ≤ r → ∀ c : kˣ, valuation k (c : k) < 1 → ∀ x ∈ ballM c (idem k r n j), j ≤ x.rank

def CoreSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (j : ℕ), j < r → 2 * j < n → IsUnitaryChar μ → IsUnitarisable σ → Equi μ σ π B → VanRk B (j + 1) → ∀ c : kˣ, valuation k (c : k) < 1 → ∀ Φ : SB (Matrix (Fin n) (Fin r) k), Φ.1 = (ballM c (idem k r n j)).indicator (fun _ => (1 : ℂ)) → B Φ = 0

def StepSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (j : ℕ), j < r → 2 * j < n → IsUnitaryChar μ → IsUnitarisable σ → Equi μ σ π B → VanRk B (j + 1) → VanRk B j

def GermSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W) (B : SB (Matrix (Fin (r + t)) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V), IsSmoothChar μ → IsSmooth π → Equi μ σ π B → ∀ w, ∃ v, IsGerm ν B (GlobalTheory.GodementJacquet.eMat k r t) w v

def UniqSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (n r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (x₀ : Matrix (Fin n) (Fin r) k), (∀ w, ∃ v, IsGerm ν B x₀ w v) → ∃ ev : W →ₗ[ℂ] V, ∀ w v, IsGerm ν B x₀ w v ↔ v = ev w

def CovSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (n r : ℕ) (h : GL (Fin n) k) (g : GL (Fin r) k) (Φ : Matrix (Fin n) (Fin r) k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂volM ν (Fin n) (Fin r) = ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(r : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(n : ℝ)) : ℝ) : ℂ) * ∫ x, Φ x ∂volM ν (Fin n) (Fin r)

def LawSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W) (B : SB (Matrix (Fin (r + t)) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V), Equi μ σ π B → ∀ ev : W →ₗ[ℂ] V, (∀ w v, IsGerm ν B (GlobalTheory.GodementJacquet.eMat k r t) w v ↔ v = ev w) → ParLaw μ σ π ev

def NzSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W) (B : SB (Matrix (Fin (r + t)) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V), Equi μ σ π B → (∀ w, IsGerm ν B (GlobalTheory.GodementJacquet.eMat k r t) w 0) → VanRk B r

def FrobSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W) (ev : W →ₗ[ℂ] V), IsSmooth π → ev ≠ 0 → ParLaw μ σ π ev → ∃ f : π.IntertwiningMap (prod₂ σ (detRep (Fin t) μ)), f.toLinearMap ≠ 0

end PositivityTheory.Tls2.Ming3
