import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

namespace CxInt

section Integral

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

def setFibre (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) : Set (((k : K) → ι k) → ℂ) :=
  {w | ∃ z ∈ S, segre z = w ∧ Ψ w = Fin.cons 1 y}

def IsSetSheet (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) : Prop :=
  segre (γ y) = w ∧ ∀ᶠ y' in 𝓝 y,
    DifferentiableAt ℂ γ y' ∧ γ y' ∈ S ∧ Ψ (segre (γ y')) = Fin.cons 1 y'

def setSheetDensity (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSetSheet S Ψ y w γ then
    g (hγ.choose y) * maDensity (fun j y' => φ j (hγ.choose y')) y
  else 0

def setIntegralAt (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ∫ y, ∑ᶠ w ∈ setFibre S Ψ y, setSheetDensity S Ψ φ g y w

def IsSetGoodProj (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Prop :=
  ∀ z ∈ S, Ψ (segre z) ≠ 0

def setIntegral (S : Set ((Σ k, ι k) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ := by
  classical
  exact if hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsSetGoodProj S Ψ then
    setIntegralAt S hΨ.choose φ g
  else 0

def logNormC (A : HermLine ι) (s : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z s‖ / A.h z)

def IsCxVar (Q : Ideal (MRingOver ℂ ι)) (d : ℕ) : Prop :=
  Nonempty K ∧ IsMultiProjPrime Q ∧
    ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

theorem sheetDensity_eq_setSheetDensity (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    sheetDensity P Ψ = setSheetDensity (mcPts P) Ψ := rfl

theorem isGoodProj_eq_isSetGoodProj (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    IsGoodProj P Ψ = IsSetGoodProj (mcPts P) Ψ := rfl

end Integral

theorem mcPts_eq_conePts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    mcPts P = ReciprocityTheory.AnForm.R.conePts (P.map (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)) := by
  ext z
  simp only [mcPts, ReciprocityTheory.AnForm.R.conePts, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f hf => h _ (Ideal.mem_map_of_mem _ hf)⟩
  have hle : P ≤ Ideal.comap (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)
      (RingHom.ker (eval z)) :=
    fun g hg => Ideal.mem_comap.mpr (RingHom.mem_ker.mpr (h g hg))
  exact RingHom.mem_ker.mp (Ideal.map_le_of_le_comap hle hf)

end CxInt

open CxInt in

def PoincareLelongC : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRingOver ℂ ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    setIntegral (ReciprocityTheory.AnForm.R.conePts Q) (Fin.cons (fun z => Real.log (B.h z)) (pot L))
        (logNormC A s) =
      (∑ᶠ W ∈ divSupp Q s,
          (multAt (Q ⊔ Ideal.span {s}) W : ℝ) *
            setIntegral (ReciprocityTheory.AnForm.R.conePts W) (pot L) (fun z => Real.log (B.h z))) -
        setIntegral (ReciprocityTheory.AnForm.R.conePts Q) (Fin.cons (fun z => Real.log (A.h z)) (pot L))
          (fun z => Real.log (B.h z))

end GlobalTheory.CompanionTheory.Ar.Pub
