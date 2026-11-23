import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalCharacter
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

noncomputable section

open NumberField Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E
open scoped ComplexConjugate

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def fixK (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) : Submodule ℂ (Sm E n) :=
  π.V ⊓
    { carrier := {φ | ∀ k ∈ K, finRep E n k φ = φ}
      add_mem' := fun {a b} ha hb k hk => by rw [map_add, ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun c a ha k hk => by rw [map_smul, ha k hk] }

def e2G (w : InfinitePlace E) : Fin n → Fin n → Module.End ℂ (Sm E n) := fun a b => -PositivityTheory.RgBcC.Bridge.eopW w false b a

def kG (w : InfinitePlace E) : Fin n → Fin n → Module.End ℂ (Sm E n) := fun a b =>
  PositivityTheory.RgBcC.Bridge.eopW w true a b + e2G w a b

def hwG (w : InfinitePlace E) (μ : Fin n → ℝ) : Submodule ℂ (Sm E n) where
  carrier := {v | Formalism.REAL.KHighest (fun _ => true) (kG w) μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add, hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add, hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm], fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

def yOf (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (μ : InfinitePlace E → Fin n → ℝ) : Submodule ℂ (Sm E n) :=
  fixK π K ⊓ ⨅ w, hwG w (μ w)

def ThetaFixedHypotheses (π : CuspSub E n) (lam : InfinitePlace E → Fin n → ℤ) (K : Subgroup (GL (Fin n) (Af E))) : Prop :=
  (CG.mk π).IsRegAlg ∧ ThetaFix π ∧ (∀ w, Antitone (lam w)) ∧
    (∀ w, HasInfCharGL π.V w.embedding (Multiset.map (PositivityTheory.RgBcC.infOf (lam w) true) Finset.univ.val) ∧
      HasInfCharGL π.V (ComplexEmbedding.conjugate w.embedding)
        (Multiset.map (PositivityTheory.RgBcC.infOf (lam w) false) Finset.univ.val)) ∧
    IsOpen (K : Set (GL (Fin n) (Af E))) ∧ IsCompact (K : Set (GL (Fin n) (Af E))) ∧ (∀ k ∈ K, thetaF E n k ∈ K) ∧
    ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ K, finRep E n k ψ = ψ

def IsHarmOf (π : CuspSub E n) (lam : InfinitePlace E → Fin n → ℤ) (K : Subgroup (GL (Fin n) (Af E)))
    (μ : InfinitePlace E → Fin n → ℝ) : Prop :=
  (∀ w, μ w ∈ PositivityTheory.RgBcC.RealD.harmSet (lam w)) ∧ FiniteDimensional ℂ (yOf π K μ) ∧ yOf π K μ ≠ ⊥ ∧
    ∀ ν : InfinitePlace E → Fin n → ℝ, (∀ w, ν w ∈ PositivityTheory.RgBcC.RealD.harmSet (lam w)) → ν ≠ μ → yOf π K ν = ⊥

def IsHeckeAct [MeasurableSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E))) (K : Subgroup (GL (Fin n) (Af E)))
    (Y : Submodule ℂ (Sm E n)) (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ Y) : Prop :=
  ∀ h, IsHeckeF K h → ∀ y : Y, (((ρ h y : Y) : Sm E n) : GA E n → ℂ) = heckeOp μf h ((y : Sm E n) : GA E n → ℂ)

def HarmY : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
    (lam : InfinitePlace E → Fin n → ℤ) (K : Subgroup (GL (Fin n) (Af E))), ThetaFixedHypotheses π lam K → ∃ μ, IsHarmOf π lam K μ

def HeckeY : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
    (lam : InfinitePlace E → Fin n → ℤ) (K : Subgroup (GL (Fin n) (Af E))), ThetaFixedHypotheses π lam K →
    ∀ (μ : InfinitePlace E → Fin n → ℝ) [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure], ∃ ρ, IsHeckeAct μf K (yOf π K μ) ρ

def SimpleY : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
    (lam : InfinitePlace E → Fin n → ℤ) (K : Subgroup (GL (Fin n) (Af E))), ThetaFixedHypotheses π lam K →
    ∀ μ, IsHarmOf π lam K μ → ∀ [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ (yOf π K μ)),
      IsHeckeAct μf K (yOf π K μ) ρ → ∀ W : Submodule ℂ (yOf π K μ), (∀ h, IsHeckeF K h → ∀ y ∈ W, ρ h y ∈ W) →
        W = ⊥ ∨ W = ⊤

def TrY : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
    (lam : InfinitePlace E → Fin n → ℤ) (K : Subgroup (GL (Fin n) (Af E))), ThetaFixedHypotheses π lam K →
    ∀ μ, IsHarmOf π lam K μ →
    ∀ [MeasurableSpace (PositivityTheory.RgTw.G n)] [BorelSpace (PositivityTheory.RgTw.G n)] (μC : Measure (PositivityTheory.RgTw.G n))
      [μC.IsHaarMeasure] [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (μH : Measure (H E n 0)) [μH.IsHaarMeasure]
      (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ (yOf π K μ)), IsHeckeAct μf K (yOf π K μ) ρ →
    ∃ (A : Module.End ℂ (yOf π K μ)) (c : ℂ), A * A = 1 ∧
      (∀ h, IsHeckeF K h → A * ρ h = ρ (fun g => h (thetaF E n g)) * A) ∧ c ≠ 0 ∧
      ∀ (k : ∀ w, PositivityTheory.RgTw.Mat n → ((PositivityTheory.RgBcC.lefE n (lam w)).V →L[ℂ] (PositivityTheory.RgBcC.lefE n (lam w)).V))
        (val : InfinitePlace E → PositivityTheory.RgBcC.Inf n → ℂ) (T : InfinitePlace E → ℝ),
        (∀ w, PositivityTheory.RgBcC.IsMult μC (PositivityTheory.RgBcC.lefE n (lam w)) (k w) (val w) (T w)) →
        ∀ h, IsHeckeF K h →
          IsTwTr μH π (phiProd lam k h)
            (c * (∏ w, val w (PositivityTheory.RgBcC.infOf (lam w))) * LinearMap.trace ℂ (yOf π K μ) (ρ h * A))

def InfBridge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
    (lamE : (E →+* ℂ) → Formalism.BasicNotions.DomWeight n), ThetaFix π → (∀ φ, π.HasInfChar φ (infOfWeight (lamE φ))) →
    ∀ w : InfinitePlace E,
      HasInfCharGL π.V w.embedding (Multiset.map (PositivityTheory.RgBcC.infOf (lamE w.embedding).w true) Finset.univ.val) ∧
      HasInfCharGL π.V (ComplexEmbedding.conjugate w.embedding)
        (Multiset.map (PositivityTheory.RgBcC.infOf (lamE w.embedding).w false) Finset.univ.val)

def ThetaFixedGlobalWeights : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg →
    GlobalTheory.ContraPair.DualIsConj π → ∀ lamE : (E →+* ℂ) → Formalism.BasicNotions.DomWeight n,
    (∀ φ, π.HasInfChar φ (infOfWeight (lamE φ))) →
    ∀ K : Subgroup (GL (Fin n) (Af E)), IsOpen (K : Set (GL (Fin n) (Af E))) → IsCompact (K : Set (GL (Fin n) (Af E))) →
    (∀ k ∈ K, thetaF E n k ∈ K) → (∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ K, finRep E n k ψ = ψ) →
    ∀ [MeasurableSpace (PositivityTheory.RgTw.G n)] [BorelSpace (PositivityTheory.RgTw.G n)] (μC : Measure (PositivityTheory.RgTw.G n))
      [μC.IsHaarMeasure] [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (μ : Measure (H E n 0)) [μ.IsHaarMeasure],
    ∃ (Y : Submodule ℂ (Sm E n)) (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ Y) (A : Module.End ℂ Y) (c : ℂ),
      Y ≤ π.V ∧ FiniteDimensional ℂ Y ∧ Y ≠ ⊥ ∧ (∀ y ∈ Y, ∀ k ∈ K, finRep E n k y = y) ∧
      IsHeckeAct μf K Y ρ ∧
      (∀ W : Submodule ℂ Y, (∀ h, IsHeckeF K h → ∀ y ∈ W, ρ h y ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      A * A = 1 ∧ (∀ h, IsHeckeF K h → A * ρ h = ρ (fun g => h (thetaF E n g)) * A) ∧ c ≠ 0 ∧
      ∀ (k : ∀ w : InfinitePlace E, PositivityTheory.RgTw.Mat n → ((PositivityTheory.RgBcC.lefE n (lamE w.embedding).w).V →L[ℂ]
          (PositivityTheory.RgBcC.lefE n (lamE w.embedding).w).V))
        (val : InfinitePlace E → PositivityTheory.RgBcC.Inf n → ℂ) (T : InfinitePlace E → ℝ),
        (∀ w : InfinitePlace E, PositivityTheory.RgBcC.IsMult μC (PositivityTheory.RgBcC.lefE n (lamE w.embedding).w) (k w) (val w) (T w)) →
        ∀ h, IsHeckeF K h →
          IsTwTr μ π (phiProd (fun w => (lamE w.embedding).w) k h)
            (c * (∏ w : InfinitePlace E, val w (PositivityTheory.RgBcC.infOf (lamE w.embedding).w)) * LinearMap.trace ℂ Y (ρ h * A))

end PositivityTheory.Rg.BcB.Desc

end
