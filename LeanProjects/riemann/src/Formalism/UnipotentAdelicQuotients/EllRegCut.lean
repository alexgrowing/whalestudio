import Formalism.UnipotentAdelicQuotients.EllReg

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

variable {d : ℕ}

def cut (χ : E d → ℝ) (g : E d → ℂ) : E d → ℂ := fun x => (χ x : ℂ) * g x

def om (s M ε : ℝ) (ξ : E d) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ε ^ 2 * ‖ξ‖ ^ 2) ^ (-(M / 2))

def nrm (s M ε : ℝ) (F : E d → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (om s M ε ξ) ^ 2 * ‖F ξ‖ₑ ^ 2

def Hs (s : ℝ) (g : E d → ℂ) : Prop := nrm s 0 0 (𝓕 g) < ⊤

def conv (K F : E d → ℂ) (ξ : E d) : ℂ := ∫ η, K (ξ - η) * F η

def eF (ξ : E d) (y : E d) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)))

def mono {n : ℕ} (w : Fin n → Fin d) (η : E d) : ℂ := ∏ l, (2 * Real.pi * Complex.I * ((η (w l) : ℝ) : ℂ))

def MomentsSmooth : Prop :=
  ∀ (d : ℕ) (g : E d → ℂ), Continuous g → HasCompactSupport g → (∀ s : ℕ, Hs (s : ℝ) g) → ContDiff ℝ ∞ g

def Bump : Prop :=
  ∀ (d : ℕ) (x0 : E d) (r : ℝ), 0 < r → ∃ χ : E d → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ ball x0 r ∧ χ =ᶠ[𝓝 x0] fun _ => 1

def CutCont : Prop :=
  ∀ (d : ℕ) (U : Set (E d)) (u : E d → ℂ) (χ : E d → ℝ), IsOpen U → ContinuousOn u U → ContDiff ℝ ∞ χ →
    HasCompactSupport χ → tsupport χ ⊆ U → Continuous (cut χ u) ∧ HasCompactSupport (cut χ u)

def LocalGlobal : Prop :=
  ∀ (d : ℕ) (U : Set (E d)) (f : E d → ℂ), IsOpen U →
    (∀ x0 ∈ U, ∃ χ : E d → ℝ, χ =ᶠ[𝓝 x0] (fun _ => 1) ∧ ContDiff ℝ ∞ (cut χ f)) → ContDiffOn ℝ ∞ f U

def BaseLevel : Prop :=
  ∀ (d : ℕ) (g : E d → ℂ), Continuous g → HasCompactSupport g → Hs (-(d : ℝ) - 1) g

def Step : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ), Hyp P U u →
    ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∀ s : ℝ,
      (∀ χ : E d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball x0 r → Hs s (cut χ u)) →
      ∀ χ : E d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball x0 r → Hs (s + 1) (cut χ u)

def LocalSobolev : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ), Hyp P U u →
    ∀ x0 ∈ U, ∃ r > 0, ball x0 r ⊆ U ∧ ∀ χ : E d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ ball x0 r → ∀ s : ℕ, Hs (s : ℝ) (cut χ u)

theorem localSobolev_of (hB : BaseLevel) (hC : CutCont) (hS : Step) : LocalSobolev := by
  intro d ι _ P U u hH x0 hx0
  obtain ⟨r, hr, hrU, hstep⟩ := hS d ι P U u hH x0 hx0
  refine ⟨r, hr, hrU, ?_⟩
  have key : ∀ n : ℕ, ∀ χ : E d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball x0 r →
      Hs ((-(d : ℝ) - 1) + n) (cut χ u) := by
    intro n
    induction n with
    | zero =>
      intro χ hχ hχc hχs
      have h := (hC d U u χ hH.1 hH.2.2.2.1 hχ hχc (hχs.trans hrU))
      simpa using hB d (cut χ u) h.1 h.2
    | succ n ih =>
      intro χ hχ hχc hχs
      have := hstep ((-(d : ℝ) - 1) + n) ih χ hχ hχc hχs
      simpa [Nat.cast_succ, add_assoc] using this
  intro χ hχ hχc hχs s
  have h := key (s + d + 1) χ hχ hχc hχs
  have e : (-(d : ℝ) - 1) + ((s + d + 1 : ℕ) : ℝ) = (s : ℝ) := by push_cast; ring
  rw [e] at h
  exact h

theorem internal_of_leaves (hM : MomentsSmooth) (hBu : Bump) (hC : CutCont) (hL : LocalGlobal)
    (hB : BaseLevel) (hS : Step) : Internal := by
  intro d ι _ P U u hH
  apply hL d U u hH.1
  intro x0 hx0
  obtain ⟨r, hr, hrU, hsob⟩ := localSobolev_of hB hC hS d ι P U u hH x0 hx0
  obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := hBu d x0 r hr
  refine ⟨χ, hχ1, ?_⟩
  have hcc := hC d U u χ hH.1 hH.2.2.2.1 hχ hχc (hχs.trans hrU)
  exact hM d (cut χ u) hcc.1 hcc.2 (hsob χ hχ hχc hχs)

def SymbLower : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (x0 : E d) (k : ℕ), (∀ i, P.ord i ≤ k) →
    (∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x0 ξ ≠ 0) →
    ∃ c > 0, ∀ ξ : E d, ξ ≠ 0 → c * ‖ξ‖ ^ (2 * k) ≤ ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2

def WeightDiff : Prop :=
  ∀ (d : ℕ) (s M : ℝ), 0 ≤ M → ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ ξ η : E d,
    |om s M ε ξ - om s M ε η| ≤ C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η

def ConvBound : Prop :=
  ∀ (d : ℕ) (s M ε C N : ℝ), 0 ≤ C →
    (∀ ξ η : E d, |om s M ε ξ - om s M ε η| ≤ C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η) →
    ∀ K F : E d → ℂ, Continuous K → Continuous F →
      nrm s M ε (conv K F) ^ (1 / 2 : ℝ) ≤
        (∫⁻ ζ, ‖K ζ‖ₑ) * nrm s M ε F ^ (1 / 2 : ℝ) +
          ENNReal.ofReal C * (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ) *
            nrm (s - 1) M ε F ^ (1 / 2 : ℝ)

def KernelSmall : Prop :=
  ∀ (d : ℕ) (U : Set (E d)) (a : E d → ℂ) (x0 : E d) (ψ0 : E d → ℝ), IsOpen U → x0 ∈ U →
    ContDiffOn ℝ ∞ a U → ContDiff ℝ ∞ ψ0 → HasCompactSupport ψ0 → tsupport ψ0 ⊆ ball 0 2 →
    ∃ r0 > 0, ∃ C : ℝ, ball x0 (2 * r0) ⊆ U ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      (∫⁻ ζ, ‖𝓕 (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (a x - a x0)) ζ‖ₑ) ≤ ENNReal.ofReal (C * r) ∧
      ∀ N : ℝ, (∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) *
        ‖𝓕 (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (a x - a x0)) ζ‖ₑ) < ⊤

def PairingFourier : Prop :=
  ∀ (d m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (g : E d → ℂ),
    (∀ n w, ContDiff ℝ ∞ (b n w) ∧ HasCompactSupport (b n w)) → Continuous g → HasCompactSupport g →
    ∀ ξ : E d, ∫ y, g y * trOp m b (eF ξ) y =
      ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, conv (𝓕 (b n w)) (fun η => mono w η * 𝓕 g η) ξ

def DwExp : Prop :=
  ∀ (d : ℕ) (ξ : E d) (w : List (Fin d)),
    dw w (eF ξ) = fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y

def FourierPair : Prop :=
  ∀ (d : ℕ) (g : E d → ℂ), Continuous g → HasCompactSupport g → ∀ ξ : E d, ∫ y, g y * eF ξ y = 𝓕 g ξ

def PairingLocal : Prop :=
  ∀ (d m : ℕ) (b b' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (g φ : E d → ℂ) (V : Set (E d)), IsOpen V →
    tsupport g ⊆ V → (∀ n w, ∀ x ∈ V, b n w x = b' n w x) →
    ∫ y, g y * trOp m b φ y = ∫ y, g y * trOp m b' φ y

def WeakFourier : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ), Hyp P U u →
    ∀ (i : ι) (χ χ' : E d → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ContDiff ℝ ∞ χ' → HasCompactSupport χ' → tsupport χ' ⊆ U →
      (∀ x ∈ tsupport χ, χ' =ᶠ[𝓝 x] fun _ => 1) →
      ∃ c : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiff ℝ ∞ (c n w) ∧ HasCompactSupport (c n w)) ∧
        ∀ ξ : E d, ∫ y, cut χ u y * P.tr i (eF ξ) y =
          ∑ n ∈ Finset.range (P.ord i), ∑ w : Fin n → Fin d,
            ∫ y, cut χ' u y * c n w y * dw (List.ofFn w) (eF ξ) y

def StepOfParts : Prop :=
  SymbLower → WeightDiff → ConvBound → KernelSmall → PairingFourier → DwExp → FourierPair → PairingLocal →
    WeakFourier → Bump → CutCont → Step

theorem internal_of_all (hM : MomentsSmooth) (hBu : Bump) (hC : CutCont) (hL : LocalGlobal)
    (hB : BaseLevel) (hSL : SymbLower) (hW : WeightDiff) (hCB : ConvBound) (hK : KernelSmall)
    (hPF : PairingFourier) (hDE : DwExp) (hFP : FourierPair) (hPL : PairingLocal) (hWF : WeakFourier)
    (hSP : StepOfParts) : Internal :=
  internal_of_leaves hM hBu hC hL hB (hSP hSL hW hCB hK hPF hDE hFP hPL hWF hBu hC)

end

end ZetaZeros.D.EllReg
