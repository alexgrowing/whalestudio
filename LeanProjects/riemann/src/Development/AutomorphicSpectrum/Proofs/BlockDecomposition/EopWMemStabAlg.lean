import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvF
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraTop

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace GlobalTheory.CompanionTheory.TwY

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev UU (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

open Classical in

def singleN (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun x := fun v => if v = w then x else 0
  map_mul' x y := by
    funext v
    by_cases hv : v = w <;> simp [hv]
  map_zero' := by
    funext v
    simp
  map_add' x y := by
    funext v
    by_cases hv : v = w <;> simp [hv]

def locInf (w : InfinitePlace E) : PositivityTheory.RgTw.G n →* GL (Fin n) (Cinf E) := cornerGL n (singleN w)

def gAt (w : InfinitePlace E) : PositivityTheory.RgTw.G n →* GA E n := (infGL E n).comp (locInf w)

def kAt (w : InfinitePlace E) : UU n →* GA E n := (gAt w).comp Unitary.toUnits

omit [NumberField E] [IsCMField E] in
theorem one_apply_pi (i j : Fin n) (v : InfinitePlace E) :
    (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j v = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

omit [NumberField E] [IsCMField E] in
open Classical in
theorem locInf_apply (w : InfinitePlace E) (g : PositivityTheory.RgTw.G n) (i j : Fin n) (v : InfinitePlace E) :
    ((locInf w g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j v =
      if v = w then (g : Matrix (Fin n) (Fin n) ℂ) i j else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  have e : ((locInf w g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j v =
      (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j v - singleN w ((1 : Matrix (Fin n) (Fin n) ℂ) i j) v +
        singleN w ((g : Matrix (Fin n) (Fin n) ℂ) i j) v := rfl
  rw [e, one_apply_pi]
  change _ - (if v = w then _ else 0) + (if v = w then _ else 0) = _
  by_cases hv : v = w <;> simp [hv]

def kInfAt (w : InfinitePlace E) (c : UU n) : Kinf E n :=
  ⟨(locInf w (Unitary.toUnits c) : GL (Fin n) (Cinf E)).val, by
    classical
    refine Matrix.mem_unitaryGroup_iff'.2 ?_
    ext i j v
    have hc : star c.1 * c.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 c.2
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    simp only [Matrix.star_apply, Pi.mul_apply, Pi.star_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, if_true]
      have := congrFun (congrFun hc i) j
      rw [Matrix.mul_apply] at this
      simp only [Matrix.star_apply] at this
      rw [← this]
      rfl
    · simp only [hv, if_false]
      simp [Matrix.one_apply, eq_comm]⟩

theorem infGL_kInfAt (w : InfinitePlace E) (c : UU n) :
    infGL E n (Unitary.toUnits (kInfAt w c)) = kAt w c := by
  unfold kAt gAt
  simp only [MonoidHom.comp_apply]
  congr 1
  exact Units.ext rfl

def sV (π : CuspSub E n) (w : InfinitePlace E) : UU n →* Module.End ℂ π.V where
  toFun c := (rt E n (kAt w c)).restrict fun ψ hψ => by
    have h := π.stable (.cpt (kInfAt w c)) ψ hψ
    have e : rt E n (kAt w c) ψ = cptRep E n (kInfAt w c) ψ := by
      rw [← infGL_kInfAt]; rfl
    rw [e]; exact h
  map_one' := by
    ext ψ; simp
  map_mul' a b := by
    ext ψ; simp

def stabAlg (π : CuspSub E n) : Subalgebra ℂ (Module.End ℂ (Sm E n)) where
  carrier := {T | ∀ ψ ∈ π.V, T ψ ∈ π.V}
  mul_mem' ha hb ψ hψ := ha _ (hb ψ hψ)
  add_mem' ha hb ψ hψ := π.V.add_mem (ha ψ hψ) (hb ψ hψ)
  algebraMap_mem' c ψ hψ := π.V.smul_mem c hψ

theorem Eop_mem_stabAlg (π : CuspSub E n) (τ : E →+* ℂ) (i j : Fin n) : Eop (a := n) τ i j ∈ stabAlg π := by
  have hL : ∀ X, lie E n X ∈ stabAlg π := fun X ψ hψ => π.stable (.lie X) ψ hψ
  exact (stabAlg π).smul_mem ((stabAlg π).sub_mem (hL _) ((stabAlg π).smul_mem (hL _) _)) _

theorem eopW_mem_stabAlg (π : CuspSub E n) (w : InfinitePlace E) (s : Bool) (i j : Fin n) :
    PositivityTheory.RgBcC.Bridge.eopW w s i j ∈ stabAlg π := by
  cases s
  · exact Eop_mem_stabAlg π _ i j
  · exact Eop_mem_stabAlg π _ i j

theorem kG_mem_stabAlg (π : CuspSub E n) (w : InfinitePlace E) (a b : Fin n) : kG w a b ∈ stabAlg π :=
  (stabAlg π).add_mem (eopW_mem_stabAlg π w true a b)
    ((stabAlg π).neg_mem (eopW_mem_stabAlg π w false b a))

def kV (π : CuspSub E n) (w : InfinitePlace E) (a b : Fin n) : Module.End ℂ π.V :=
  (kG w a b).restrict (kG_mem_stabAlg π w a b)

def fV (π : CuspSub E n) (k : GL (Fin n) (Af E)) : Module.End ℂ π.V :=
  (finRep E n k).restrict fun ψ hψ => π.stable (.fin k) ψ hψ

section Avg

variable [MeasurableSpace (UU n)] (κ : Measure (UU n)) (Em : PositivityTheory.RgBcC.KMod n) (T : Em.V →L[ℂ] Em.V)

def qFun (w : InfinitePlace E) (φ : GA E n → ℂ) : GA E n → ℂ :=
  fun x => ∫ c, GlobalTheory.CompanionTheory.TrPassage.chiT Em T c * φ (x * kAt w c) ∂κ

def IsQ (w : InfinitePlace E) (π : CuspSub E n) (Q : Module.End ℂ π.V) : Prop :=
  ∀ (ψ : π.V) (x : GA E n), ((Q ψ : π.V) : Sm E n).1 x = qFun κ Em T w (ψ : Sm E n).1 x

end Avg

def coefW (Em : PositivityTheory.RgBcC.KMod n) : Submodule ℂ (UU n → ℂ) :=
  Submodule.span ℂ (Set.range fun p : (Em.V →L[ℂ] ℂ) × Em.V => fun c : UU n => p.1 (Em.ρ c⁻¹ p.2))

def tlS (Em : PositivityTheory.RgBcC.KMod n) (w : InfinitePlace E) : Submodule ℂ (Sm E n) where
  carrier := {φ | ∀ x, (fun c : UU n => φ.1 (x * kAt w c)) ∈ coefW Em}
  add_mem' {a b} ha hb x := (coefW Em).add_mem (ha x) (hb x)
  zero_mem' x := (coefW Em).zero_mem
  smul_mem' r a ha x := (coefW Em).smul_mem r (ha x)

abbrev tl (lam : InfinitePlace E → Fin n → ℤ) (w : InfinitePlace E) : Submodule ℂ (Sm E n) :=
  tlS (PositivityTheory.RgBcC.lefE n (lam w)) w

def vMod (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (lam : InfinitePlace E → Fin n → ℤ)
    (μ : InfinitePlace E → Fin n → ℝ) (S : Finset (InfinitePlace E)) (w : InfinitePlace E) : Submodule ℂ (Sm E n) :=
  fixK π K ⊓ (⨅ v ∈ S, hwG v (μ v)) ⊓ ⨅ (v : InfinitePlace E) (_ : v ∉ S) (_ : v ≠ w), tl lam v

def wMod (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (lam : InfinitePlace E → Fin n → ℤ)
    (μ : InfinitePlace E → Fin n → ℝ) (S : Finset (InfinitePlace E)) : Submodule ℂ (Sm E n) :=
  fixK π K ⊓ (⨅ v ∈ S, hwG v (μ v)) ⊓ ⨅ (v : InfinitePlace E) (_ : v ∉ S), tl lam v

abbrev wV (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (lam : InfinitePlace E → Fin n → ℤ)
    (μ : InfinitePlace E → Fin n → ℝ) (S : Finset (InfinitePlace E)) : Submodule ℂ π.V :=
  (wMod π K lam μ S).comap π.V.subtype

def itF [MeasurableSpace (PositivityTheory.RgTw.G n)] (μC : Measure (PositivityTheory.RgTw.G n))
    (f : InfinitePlace E → PositivityTheory.RgTw.G n → ℂ) (l : List (InfinitePlace E)) (Φ : GA E n → ℂ) : GA E n → ℂ :=
  l.foldr (fun w Ψ x => ∫ y, f w y * Ψ (x * gAt w y) ∂μC) Φ

end GlobalTheory.CompanionTheory.TwY
end
