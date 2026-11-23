import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CutTailC

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open DiscreteGroups.T1.G (lInt0 IsPiPart UncutHalf CutTail2)
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

def ac (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (t : ℝ) : H E n 0 :=
  (splitCentre E n (t / (n * Module.finrank ℚ E)), 1)

def r0 (x : H E n 0) : ℝ := redSize (ac E n (-ldet x) * x).1

def vecM {D : Dom E n 0} (v : Lp ℂ 2 D.ν) (c : ι → ℂ) : Hs (ι := ι) D := WithLp.toLp 2 fun l => c l • v

def P0 (D : Dom E n 0) (π : CuspSub E n) (v : Lp ℂ 2 D.ν) : Lp ℂ 2 D.ν :=
  (piSp D π Unit).starProjection (vecM v fun _ : Unit => 1) ()

def Gk {D : Dom E n 0} (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D) (V : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (x y : H E n 0) : ℂ :=
  ∑ i, inner ℂ (k₁ x i) (V (k₂ y i))

def Inv {α : Type} (f : H E n 0 → α) : Prop := ∀ (γ : ratH E n 0) x, f ((γ : H E n 0) * x) = f x

end Defs

structure Su (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] where
  D : Dom E n 0
  π : CuspSub E n
  Φ₁ : Matrix ι ι (H E n 0 → ℂ)
  Φ₂ : Matrix ι ι (H E n 0 → ℂ)
  T₁ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D
  T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D
  M : Matrix ι ι ℂ
  k₁ : H E n 0 → ι → Hs (ι := ι) D
  k₂ : H E n 0 → ι → Hs (ι := ι) D
  pos : 1 ≤ n
  fix : ThetaFix π
  t₁ : IsTestM Φ₁
  t₂ : IsTestM Φ₂
  fin : ∀ i j, FinOn D.μ π (Φ₁ i j)
  o₁ : IsROp D Φ₁ T₁
  o₂ : IsROp D Φ₂ T₂
  vecs : IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂

section Mid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

structure Mid (s : Su E n ι) where
  U : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D
  Uπ : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D
  Φ : Matrix ι ι (H E n 0 → ℂ)
  t : IsTestM Φ
  o : IsROp s.D Φ (s.T₁ * U * s.T₂)
  pp : IsPiPart s.D s.π U Uπ

def Mid.G {s : Su E n ι} (m : Mid s) : H E n 0 → H E n 0 → ℂ := Gk s.k₁ s.k₂ m.Uπ

def Mid.φ {s : Su E n ι} (m : Mid s) : H E n 0 → ℂ := trM m.Φ s.M

structure Pts (π : CuspSub E n) : Type 1 where
  B : Type
  [fB : Fintype B]
  w : B → Sm E n
  x : B → H E n 0
  mem : ∀ b, w b ∈ π.V
  zero : ∀ b, ldet (x b) = 0

attribute [instance] Pts.fB

def Fac (s : Su E n ι) (p : Pts s.π) : Prop :=
  ∀ (m : Mid s) x y, m.G x y = ∑ b, (p.w b).1 x.1 * m.G (ac E n (ldet x) * p.x b) y

end Mid

def ForSu (P : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι], Su E n ι → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] (s : Su E n ι), P E n ι s

def Basic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
  (∀ t, ldet (ac E n t) = t) ∧ (∀ x y : H E n 0, ldet (x * y) = ldet x + ldet y) ∧ (∀ t x, ac E n t * x = x * ac E n t) ∧
  (∀ s t, ac E n (s + t) = ac E n s * ac E n t) ∧ ac E n 0 = 1 ∧ Continuous (ac E n) ∧
  (∀ x : H E n 0, ldet (th x) = -ldet x) ∧ (∀ x : H E n 0, th (th x) = x) ∧ (∀ x y : H E n 0, th (x * y) = th x * th y) ∧
  (∀ γ : ratH E n 0, ldet (γ : H E n 0) = 0 ∧ th (γ : H E n 0) ∈ ratH E n 0) ∧ Continuous (ldet : H E n 0 → ℝ) ∧
  Continuous (th : H E n 0 → H E n 0)

def ThetaInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (f : H E n 0 → ℂ),
  Inv f → Integrable f D.ν → Integrable (fun x => f (th x)) D.ν ∧ ∫ x, f (th x) ∂D.ν = ∫ x, f x ∂D.ν

def AeEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (f g : H E n 0 → ℂ) (I : Set ℝ),
  Continuous f → Continuous g → Inv f → Inv g → IsOpen I → (∀ᵐ x ∂D.ν, ldet x ∈ I → f x = g x) → ∀ x, ldet x ∈ I → f x = g x

def Zero : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (f : H E n 0 → ℂ) (I : Set ℝ),
  Continuous f → Inv f → IsOpen I →
    (∀ v : Lp ℂ 2 D.ν, (∀ᵐ y ∂D.ν, ldet y ∉ I → (v : H E n 0 → ℂ) y = 0) → ∫ y, (v : H E n 0 → ℂ) y * f y ∂D.ν = 0) →
    ∀ y, ldet y ∈ I → f y = 0

def KInv : Prop := ForSu fun _ _ _ _ _ _ _ s => Inv s.k₁ ∧ Inv s.k₂

def GBound : Prop := ForSu fun E _ _ _ n _ _ s => ∃ Ω : Set (H E n 0), IsCompact Ω ∧ ∀ x₀, ∃ C : ℝ, 0 ≤ C ∧
  ∀ (m : Mid s) t y, ‖m.G (ac E n t * x₀) y‖ₑ ≤ ENNReal.ofReal (C * ‖m.U‖) * cnt (ratH E n 0) Ω y

def Weak : Prop := ForSu fun E _ _ _ n ι _ s => ∀ (v : Lp ℂ 2 s.D.ν) (u : Hs (ι := ι) s.D) (i : ι),
  Integrable (fun y => (v : H E n 0 → ℂ) y * inner ℂ u (s.k₂ (th y) i)) s.D.ν ∧
    ∫ y, (v : H E n 0 → ℂ) y * inner ℂ u (s.k₂ (th y) i) ∂s.D.ν = inner ℂ u (s.T₂ (vecM v fun l => s.M l i))

def PointRep : Prop := ForSu fun E _ _ _ n ι _ s => ∀ (Φ : Matrix ι ι (H E n 0 → ℂ)) (T : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D),
  IsTestM Φ → IsROp s.D Φ T → ∀ h g : Hs (ι := ι) s.D, s.T₁ h = T g → ∀ x i,
    inner ℂ (s.k₁ x i) h = ∑ j, ∫ y, kerH (Φ i j) x y * (g j : H E n 0 → ℂ) y ∂s.D.ν

def PComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ : Matrix ι ι (H E n 0 → ℂ)) (T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D),
    IsTestM Φ → IsROp D Φ T → ∀ f, (piSp D π ι).starProjection (T f) = T ((piSp D π ι).starProjection f)

def PDiag : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (π : CuspSub E n)
  (ι : Type) [Fintype ι] (v : Lp ℂ 2 D.ν) (c : ι → ℂ), (piSp D π ι).starProjection (vecM v c) = vecM (P0 D π v) c

def PSupp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (π : CuspSub E n)
  (a b : ℝ) (v : Lp ℂ 2 D.ν), (∀ᵐ y ∂D.ν, ldet y ∉ Set.Icc a b → (v : H E n 0 → ℂ) y = 0) →
    ∀ᵐ y ∂D.ν, ldet y ∉ Set.Icc a b → (P0 D π v : H E n 0 → ℂ) y = 0

def Ker : Prop := ForSu fun E _ _ _ n _ _ s => ∀ (m : Mid s) (v : Lp ℂ 2 s.D.ν) (x : H E n 0),
  Integrable (fun y => (v : H E n 0 → ℂ) y * m.G x (th y)) s.D.ν ∧
    ∫ y, (v : H E n 0 → ℂ) y * m.G x (th y) ∂s.D.ν = ∫ y, kerH m.φ x y * (P0 s.D s.π v : H E n 0 → ℂ) y ∂s.D.ν

def Supp : Prop := ForSu fun _ _ _ _ _ _ _ s => ∀ (m : Mid s) (R : ℝ), (∀ z, m.φ z ≠ 0 → |ldet z| ≤ R) →
  ∀ x y, R < |ldet x + ldet y| → m.G x y = 0

def EvalBasis : Prop := ∀ (X V : Type) [AddCommGroup V] [Module ℂ V] (ev : X → (V →ₗ[ℂ] ℂ)), (∀ v, (∀ x, ev x v = 0) → v = 0) →
  ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → ∃ (d : ℕ) (x : Fin d → X) (w : Fin d → V), (∀ b, w b ∈ W) ∧
    ∀ v ∈ W, v = ∑ b, ev (x b) v • w b

def FinGen : Prop := ForSu fun E _ _ _ n ι _ s => ∃ W : Submodule ℂ (Sm E n), W ≤ s.π.V ∧ FiniteDimensional ℂ W ∧
  ∀ v : Hs (ι := ι) s.D, IsPiVec s.D s.π v → ∀ (i : ι) (t : ℝ), ∃ ψ ∈ W, ∀ x, ldet x = t → inner ℂ (s.k₁ x i) v = ψ.1 x.1

def FinFac : Prop := ForSu fun E _ _ _ n ι _ s => ∃ p : Pts s.π, ∀ v ∈ piSp s.D s.π ι, ∀ x i,
  inner ℂ (s.k₁ x i) v = ∑ b, (p.w b).1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * p.x b) i) v

def DropP : Prop := ForSu fun _ _ _ _ _ ι _ s => ∀ (m : Mid s) x y,
  m.G x y = Gk s.k₁ s.k₂ ((piSp s.D s.π ι).starProjection ∘L m.Uπ) x y

def GFac : Prop := ForSu fun _ _ _ _ _ _ _ s => ∃ p : Pts s.π, Fac s p

def Rep : Prop := ForSu fun E _ _ _ n _ _ s => ∀ (m : Mid s), ∀ ψ ∈ s.π.V, ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u → ∀ x₀,
  Integrable (fun x => ψ.1 x.1 * m.G x₀ x * u (ldet x)) s.D.ν ∧
    ∫ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) ∂s.D.ν =
      ∫ z, m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(ldet x₀ + ldet z)) ∂s.D.μ

def RangeW : Prop := ForSu fun E _ _ _ n _ _ s => ∀ p : Pts s.π, Fac s p → ∀ (m : Mid s), ∀ ψ ∈ s.π.V, ∀ x₀ : H E n 0, ldet x₀ = 0 →
  ∫ z, m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) ∂s.D.μ =
    ∑ b, (p.w b).1 x₀.1 * ∫ z, m.φ z * ψ.1 (thetaA E n ((p.x b).1 * z.1)) ∂s.D.μ

def Flip : Prop := ∀ (X Z : Type) [MeasurableSpace X] [MeasurableSpace Z] (ν : Measure X) [SFinite ν] (μ : Measure Z) [SFinite μ]
  (l : X → ℝ) (l' : Z → ℝ) (F : ℝ → X → ℂ) (m : Z → ℂ) (d : X → ℝ), Measurable l → Measurable l' →
  Measurable (Function.uncurry F) → (∀ x, Continuous fun s => F s x) → Integrable m μ → Integrable d ν →
  (∀ s x, |s - l x| ≤ 1 → ‖F s x‖ ≤ d x) →
  (∀ (s : ℝ) (u : ℝ → ℂ), Continuous u → HasCompactSupport u → ∫ x, F s x * u (l x) ∂ν = ∫ z, m z * u (-(s + l' z)) ∂μ) →
  Integrable (fun x => F (l x) x) ν ∧ ∫ x, F (l x) x ∂ν = (∫ z, m z ∂μ) / 2

def TrFin : Prop := ∀ (V B : Type) [AddCommGroup V] [Module ℂ V] [Fintype B] (L : V →ₗ[ℂ] V) (w : B → V) (e : B → (V →ₗ[ℂ] ℂ)),
  (∀ v, L v = ∑ b, e b (L v) • w b) →
    LinearMap.trace ℂ (LinearMap.range L) (L.restrict fun x _ => LinearMap.mem_range_self L x) = ∑ b, e b (L (w b))

def Sizes : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∃ c : ℝ, 0 ≤ c ∧ ∀ x : H E n 0,
  redSize x.1 ≤ r0 x + c * (1 + |ldet x|) ∧ |ldet x| ≤ c * (1 + logSize x.1) ∧ 0 ≤ r0 x

def InCut : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : ℝ) (g : GA E n),
  c * (1 + redSize g) ≤ τ → g ∈ cutSet E n τ

def DomInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ ψ ∈ π.V, ∀ Ω : Set (H E n 0), IsCompact Ω → ∃ N : ℕ, ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 ≤ C ∧ ∀ R ρ : ℝ, 0 ≤ R →
    ∫⁻ x, {x | |ldet x| ≤ R ∧ ρ ≤ r0 x}.indicator (fun x => ‖ψ.1 x.1‖ₑ * cnt (ratH E n 0) Ω x) x ∂D.ν ≤
      ENNReal.ofReal (C * (1 + R) ^ N * Real.exp (-(L * ρ)))

def HalfTerm : Prop := ForSu fun E _ _ _ n _ _ s => ∀ (m : Mid s), ∀ ψ ∈ s.π.V, ∀ x₀ : H E n 0, ldet x₀ = 0 →
  Integrable (fun x => ψ.1 x.1 * m.G (ac E n (ldet x) * x₀) x) s.D.ν ∧
    ∫ x, ψ.1 x.1 * m.G (ac E n (ldet x) * x₀) x ∂s.D.ν = (∫ z, m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) ∂s.D.μ) / 2

def TailInt : Prop := ForSu fun E _ _ _ n _ _ s => ∃ N : ℕ, ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : Mid s) (R ρ : ℝ), 0 ≤ R →
  (∀ z, m.φ z ≠ 0 → |ldet z| ≤ R) → ∀ A : Set (H E n 0), (∀ x ∈ A, |ldet x| ≤ R → ρ ≤ r0 x) →
    ∫⁻ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ∂s.D.ν ≤ ENNReal.ofReal (C * ‖m.U‖ * (1 + R) ^ N * Real.exp (-(L * ρ)))

def DiagInt : Prop := ForSu fun _ _ _ _ _ _ _ s => ∀ m : Mid s, Integrable (fun x => m.G x x) s.D.ν

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
