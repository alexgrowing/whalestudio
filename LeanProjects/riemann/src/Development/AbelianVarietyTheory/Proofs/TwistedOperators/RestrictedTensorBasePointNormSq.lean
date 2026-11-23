import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def VacAt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) :
    Place D → (WO S T → ℂ) → Prop
  | .inl v => fun f => IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f
  | .inr τ => fun f => IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f

def IsLocOp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f₀ : WO S T → ℂ)
    (p : Place D) (x : WO S T → ℂ) : Prop :=
  ∃ L : (WO S T → ℂ) → ℂ, (∀ (c : ℂ) (φ : WO S T → ℂ), L (fun w => c * φ w) = c * L φ) ∧
    (∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧ ∀ g, IsThetaFunO ψ S T g →
      ipO μ 𝓕 f' g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f) g) ∧
    ∀ g, IsThetaFunO ψ S T g → ipO μ 𝓕 x g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f₀) g

open Classical in

def pull {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v))
    (Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ) : WO S T → ℂ :=
  fun t => if IsHalf a t then Φ (κ t) else 0

def IsCoord {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (Λ : AddSubgroup (WO S T))
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) : Prop :=
  (∀ x y, κ (x + y) = κ x + κ y) ∧ Set.BijOn κ {t | IsHalf a t} Set.univ ∧
    IsOpen (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∧ IsCompact (κ '' {t | t ∈ Λ ∧ IsHalf a t})

theorem wAt_eq_smul {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p w = idem D p • w := rfl

theorem onHalf_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) : onHalf φ S T BS BT e = pull e (mapCo φ S T BS BT) := rfl

theorem onHalfAdj_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) :
    onHalfAdj φ S T BS BT e = pull (cA D e) (adjCo φ S T BS BT) := rfl

theorem gAt_one (V : HSp D) (p : Place D) : gAt V p 1 = 1 := by
  cases p <;> simp [gAt]

theorem gAt_mul (V : HSp D) (p : Place D) (g g' : GA D V) : gAt V p (g * g') = gAt V p g * gAt V p g' := by
  cases p <;> simp [gAt]

theorem gAt_inv (V : HSp D) (p : Place D) (g : GA D V) : gAt V p g⁻¹ = (gAt V p g)⁻¹ := by
  cases p <;> simp [gAt]

theorem latO_mono {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P Q : FinPl D → Prop} (h : ∀ v, P v → Q v) : latO S T LS LT P ≤ latO S T LS LT Q := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hQ => hv v fun hP => hQ (h v hP), rest⟩

theorem isLatVac_mono {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ ≤ Λ') {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ' f) : IsLatVac hs Λ f := by
  unfold IsLatVac at hf ⊢
  exact ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f f₀ : WO S T → ℂ}

theorem vacAt_of_isLocal {p q : Place D} (h : IsLocal ψ θ S T sS sT ΛS ΛT p f) (hq : q ≠ p) :
    VacAt ψ θ S T sS sT ΛS ΛT q f := by
  rcases q with v | τ
  · exact isLatVac_mono (latO_mono fun u hu => hu ▸ hq) h.2.1
  · exact h.2.2 τ hq

theorem base_std (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsStdChar D ψ (-1) := by
  exact h.2.2.2.2.1

theorem base_inf (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsInfFam θ :=
  h.2.2.2.2.2.inf

theorem base_theta (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsThetaFunO ψ S T f₀ :=
  h.2.2.2.2.2.theta

theorem restrictedTensorBasePoint_norm_sq (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : nrm2 μ 𝓕 f₀ = 1 := by
  exact h.2.2.2.2.2.norm.2 (μ, 𝓕) hμ

theorem base_ne_zero (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : f₀ ≠ 0 := by
  rintro rfl
  obtain ⟨⟨μ, 𝓕⟩, hq⟩ := h.2.2.2.2.2.norm.1
  have h1 := restrictedTensorBasePoint_norm_sq h hq
  simp [nrm2] at h1

theorem base_isLocal (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : IsLocal ψ θ S T sS sT ΛS ΛT p f₀ :=
  ⟨h.2.2.2.2.2.theta, isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat,
    fun τ _ => h.2.2.2.2.2.fock τ⟩

theorem base_vacAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : VacAt ψ θ S T sS sT ΛS ΛT p f₀ := by
  rcases p with v | τ
  · exact isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat
  · exact h.2.2.2.2.2.fock τ

end

end GlobalTheory.PlaceTensor

end
