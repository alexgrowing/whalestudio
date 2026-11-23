import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl

noncomputable section

open Finset MeasureTheory Matrix

namespace CompanionTheory.RgDs.K

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lword {M : Type*} [AddCommGroup M] [Module ℂ M] (L : Fin n → Fin n → Module.End ℂ M) :
    List (Fin n × Fin n) → Module.End ℂ M
  | [] => 1
  | p :: w => L p.1 p.2 * lword L w

def LowAlg : Prop :=
  ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : Fin n → Fin n → Module.End ℂ M) (μ η : Fin n → ℝ) (Φ x : M),
    IsGlRep L → (∀ a, L a a Φ = (μ a : ℂ) • Φ) → (∀ a b, b < a → L a b Φ = 0) →
    x ∈ Submodule.span ℂ (Set.range fun w : List (Fin n × Fin n) => lword L w Φ) →
    (∀ c, L c c x = (η c : ℂ) • x) → x ≠ 0 → InCone μ η ∧ (η = μ → ∃ c : ℂ, x = c • Φ)

def OmF (n : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {F | ContDiffOn ℂ ⊤ F (OmegaSet n) ∧ ∀ z ∉ OmegaSet n, F z = 0}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, fun z hz => by simp [ha.2 z hz, hb.2 z hz]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' := fun c _ ha => ⟨contDiffOn_const.smul ha.1, fun z hz => by simp [ha.2 z hz]⟩

open Classical in

def lop (Y : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun z => if z ∈ OmegaSet n then -(fderiv ℂ F z (Y * z)) else 0

def lw : List (Fin n × Fin n) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ)
  | [] => id
  | p :: w => fun F => lop (Matrix.single p.1 p.2 1) (lw w F)

def PhiO (μ : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℂ → ℂ := Set.indicator (OmegaSet n) (PhiM μ)

def HolFacts : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℤ),
    (∀ (Y : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ), F ∈ OmF n → lop Y F ∈ OmF n) ∧
    (∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b c d : Fin n), F ∈ OmF n →
      lop (Matrix.single a b 1) (lop (Matrix.single c d 1) F) - lop (Matrix.single c d 1) (lop (Matrix.single a b 1) F) =
        (if b = c then lop (Matrix.single a d 1) F else 0) - (if d = a then lop (Matrix.single c b 1) F else 0)) ∧
    PhiO μ ∈ OmF n ∧ (∀ a, lop (Matrix.single a a 1) (PhiO μ) = ((μ a : ℤ) : ℂ) • PhiO μ) ∧
    ∀ a b, b < a → lop (Matrix.single a b 1) (PhiO μ) = 0

abbrev Wd (n m : ℕ) : Type := Σ l : Fin (m + 1), (Fin l → Fin n × Fin n)

def ofW {m : ℕ} (x : Wd n m) : List (Fin n × Fin n) := List.ofFn x.2

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

abbrev AS (T : KType ε Λ) (m : ℕ) : Type := Wd n m → T.V

def adC (k : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n × Fin n) : ℂ := k q.1 p.1 * k⁻¹ p.2 q.2

def rhoA (T : KType ε Λ) (m : ℕ) (k : KG ε) (a : AS T m) : AS T m := fun x' =>
  ∑ w : Fin x'.1 → Fin n × Fin n, (∏ i, adC (toMK k) (w i) (x'.2 i)) • T.op k (a ⟨x'.1, w⟩)

def actF (T : KType ε Λ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) {m : ℕ} (a : AS T m) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  ∑ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (fun g => inner ℂ T.w (Ψ g (a x)))

def actL (T : KType ε Λ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) {m : ℕ} (a : AS T m) : L2 ε :=
  toL2 ε (actF T Ψ a)

def betaF (T : KType ε Λ) (μ : Fin n → ℤ) {m : ℕ} (a : AS T m) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  ∑ x : Wd n m, inner ℂ T.w (a x) • lw (ofW x) (PhiO μ)

def tor (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

def EquivSection : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (A S : Type) [NormedAddCommGroup A] [NormedSpace ℂ A]
    [FiniteDimensional ℂ A] [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ρ : G → (A →L[ℂ] A)) (σ : G → (S →L[ℂ] S)),
    ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g ∘L ρ h) → Continuous ρ →
    σ 1 = 1 → (∀ g h, σ (g * h) = σ g ∘L σ h) → (∀ y, Continuous fun g => σ g y) →
    ∀ f : A →ₗ[ℂ] S, Function.Surjective f → (∀ g a, f (ρ g a) = σ g (f a)) →
      ∃ s : S →ₗ[ℂ] A, (∀ y, f (s y) = y) ∧ ∀ g y, s (σ g y) = ρ g (s y)

def RhoRep : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (m : ℕ),
    (∀ a, rhoA T m 1 a = a) ∧ (∀ k k' a, rhoA T m (k * k') a = rhoA T m k (rhoA T m k' a)) ∧
    (∀ k, ∀ a a' : AS T m, rhoA T m k (a + a') = rhoA T m k a + rhoA T m k a') ∧
    (∀ k (c : ℂ) (a : AS T m), rhoA T m k (c • a) = c • rhoA T m k a) ∧
    ∀ a, Continuous fun k => rhoA T m k a

def ActEquiv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (m : ℕ), IsPsiFor ε lam T Ψ →
    ∀ (k : KG ε) (a : AS T m), rreg ε (toMK k) (actL T Ψ a) = actL T Ψ (rhoA T m k a)

def RhoTorus : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (m : ℕ) (θ : Fin n → ℝ) (k : KG ε),
    toMK k = tor θ → ∀ (a : AS T m) (x : Wd n m),
      rhoA T m k a x = Complex.exp (((∑ i, (θ (x.2 i).1 - θ (x.2 i).2) : ℝ) : ℂ) * Complex.I) • T.op k (a x)

def TorW : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (θ : Fin n → ℝ) (k : KG ε),
    toMK k = tor θ → T.op k T.w = Complex.exp (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) • T.w

def Transfer : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (m : ℕ),
    IsHCParam lam → IsMu lam μ → ∀ (a : AS T m) (g₀ : Matrix (Fin n) (Fin n) ℂ), inUJ ε g₀ →
      ∃ W ∈ nhds g₀, ∃ k₀ : KG ε, ∀ g ∈ W, inUJ ε g →
        actF T (PsiM T μ) a g = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) *
          ∫ k, betaF T μ (rhoA T m k⁻¹ a) (toMK k⁻¹ * (g⁻¹ * toMK k₀) * toMK k) *
            inner ℂ T.w (T.op (k₀ * k) T.w) ∂(muK ε)

def Exhaust : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
    (∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∃ (m : ℕ) (a : AS T m), (x : L2 ε) = actL T Ψ a) ∧
    (∀ (m m' : ℕ), m ≤ m' → ∀ a : AS T m, ∃ a' : AS T m', actL T Ψ a' = actL T Ψ a) ∧
    ∀ (m : ℕ) (a : AS T m), actL T Ψ a ∈ (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)).map (smD ε (rreg ε)).subtype

def BetaWeight : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (μ : Fin n → ℤ) (m : ℕ) (η : Fin n → ℝ)
    (a : AS T m),
    (∀ (θ : Fin n → ℝ) (k : KG ε), toMK k = tor θ →
      rhoA T m k a = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • a) →
    betaF T μ a ∈ Submodule.span ℂ (Set.range fun w : List (Fin n × Fin n) => lw w (PhiO μ)) ∧
    ∀ c, lop (Matrix.single c c 1) (betaF T μ a) = ((((μ c : ℤ) : ℝ) + η c - Λ c : ℝ) : ℂ) • betaF T μ a

end CompanionTheory.RgDs.K
