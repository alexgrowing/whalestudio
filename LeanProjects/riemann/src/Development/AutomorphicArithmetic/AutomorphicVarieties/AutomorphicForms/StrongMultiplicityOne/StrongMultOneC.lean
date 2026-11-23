import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Imports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

namespace UpperTheory.V.Af.StrongMultiplicityOne

section Glob

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

variable (E) in

def psiR (x : Cinf E) : ℂ := (𝐞 (-TG.tr E x) : ℂ)

def conv [IsTotallyComplex E] (f : GA E n → ℂ) (α : Lie E n → ℂ) (g : GA E n) : ℂ := ∫ x, chart f g x * α x

def Sat (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (U : Submodule ℂ (cuspForms E n)) : Prop :=
  ∀ φ ∈ U, (∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w n, φ.1 (g * finGL E n (locGL E n w k)) = φ.1 g) → EigAt w B φ.1

def SameSat (U U' : Submodule ℂ (cuspForms E n)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, Sat w B U ∧ Sat w B U'

def Irr (U : Submodule ℂ (cuspForms E n)) : Prop := U ≠ ⊥ ∧ ∀ W ≤ U, Fb.Stab W → W = ⊥ ∨ W = U

end Glob

def TrDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], ∃ (d : ℕ) (b b' : Module.Basis (Fin d) ℝ (Cinf E)),
    ∀ x y, TG.tr E (x * y) = ∑ i, b'.repr x i * b.repr y i

def ArchStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (m : Fin n), m.val + 1 < n →
    ∃ h : (Fin n → Cinf E) → ℂ, h ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m) = 1 ∧ (∀ ξ, h ξ ≠ 0 → IsUnit (rowM m ξ)) ∧
      ∀ α : 𝓢(Lie E n, ℂ), ∃ β : 𝓢(Lie E n, ℂ), ∀ (w : Lie E n → ℂ) (ξ : Fin n → Cinf E), Measurable w →
        (∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) → (∀ u x, w (lmul (toL (colM m u)) x) = psiR E (dotLe m ξ u) * w x) →
        ∫ x, w x * β x = h ξ * ∫ x, w x * α (lmul (toL (rowM m ξ)) x)

def LinChange : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∃ c : GL (Fin n) (Cinf E) → ℂ, c 1 = 1 ∧
    ∀ (s : GL (Fin n) (Cinf E)) (f : Lie E n → ℂ), ∫ x, f (lmul (toL s.val) x) = c s * ∫ x, f x

def ArchKir : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ), m < n → ∃ H : GL (Fin n) (Cinf E) → ℂ, H 1 = 1 ∧
    ∀ α : 𝓢(Lie E n, ℂ), ∃ β : 𝓢(Lie E n, ℂ), ∀ w : Lie E n → ℂ, Measurable w → (∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) →
      (∀ ν : GL (Fin n) (Cinf E), IsY 0 ν.val → ∀ x, w (lmul (toL ν.val) x) = psiR E (supN ν.val) * w x) →
      ∀ p : GL (Fin n) (Cinf E), IsY m p.val → ∫ x, w (lmul (toL p.val) x) * β x = H p * ∫ x, w x * α x

def PsiInf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : Cinf E), psiA E (sInf E x) = psiR E x

def EmbY : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n m : ℕ),
    (∀ w (y : GL (Fin n) (HeightOneSpectrum.adicCompletion E w)), IsY m y.val →
      IsY m (locGL E n w y).val ∧ supN (locGL E n w y).val = sLoc E w (supN y.val)) ∧
    (∀ y : GL (Fin n) (Af E), IsY m y.val → IsY m (finGL E n y).val ∧ supN (finGL E n y).val = sFin E (supN y.val)) ∧
    (∀ y : GL (Fin n) (Cinf E), IsY m y.val → IsY m (infGL E n y).val ∧ supN (infGL E n y).val = sInf E (supN y.val)) ∧
    ∀ w, Continuous (locGL E n w)

def FinKir : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), 1 ≤ n → ∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
    (U : OpenSubgroup (GL (Fin n) (Af E))), ∃ (c : GL (Fin n) (Af E) →₀ ℂ) (H : GL (Fin n) (Af E) → ℂ), H 1 = 1 ∧
      (∀ x ∈ c.support, SuppIn S x) ∧ ∀ W : GL (Fin n) (Af E) → ℂ,
        (∀ ν, SuppIn S ν → IsY 0 ν.val → ∀ g, SuppIn S g → W (ν * g) = psiF E (supN ν.val) * W g) →
        (∀ g, SuppIn S g → ∀ u ∈ U, SuppIn S u → W (g * u) = W g) →
        ∀ p, SuppIn S p → IsY (n - 1) p.val → comb c W p = H p * W 1

def ChartCont : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (f : GA E n → ℂ), Continuous f →
    ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n) ∧ ∀ g, Measurable (chart f g)

def ConvCont : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (f : GA E n → ℂ), Continuous f →
    (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) → ∀ α : 𝓢(Lie E n, ℂ), Continuous (conv f α) ∧ ∃ C : ℝ, ∀ g, ‖conv f α g‖ ≤ C

def ConvFub : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (f : GA E n → ℂ), Continuous f →
    (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) → ∀ (α : 𝓢(Lie E n, ℂ)) (X : Type) [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (u : X → GA E n) (a : X → ℂ),
    Continuous u → Continuous a → (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → ∀ g,
      ∫ x, conv f α (u x * g) * a x ∂ν = conv (fun g' => ∫ x, f (u x * g') * a x ∂ν) α g

def ConvNice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (f : GA E n → ℂ), Nice f → ∀ α : 𝓢(Lie E n, ℂ),
    Nice (conv f α) ∧ whittaker (conv f α) = conv (whittaker f) α

def SeedConv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (W : GA E n → ℂ), Continuous W →
    ∀ y, W (infGL E n y) ≠ 0 → ∃ α : 𝓢(Lie E n, ℂ), conv W α 1 = 1

def EigMap : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (f : GA E n → ℂ), EigAt w B f →
    (Nice f → EigAt w B (whittaker f)) ∧ (Nice f → ∀ α : 𝓢(Lie E n, ℂ), EigAt w B (conv f α)) ∧
    ∀ f', EigAt w B f' → EigAt w B (f - f')

def KillP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), 1 ≤ n → ∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
    (U : OpenSubgroup (GL (Fin n) (Af E))), ∃ (c : GL (Fin n) (Af E) →₀ ℂ) (H : GA E n → ℂ), H 1 = 1 ∧
      (∀ x ∈ c.support, SuppIn S x) ∧ ∀ α : 𝓢(Lie E n, ℂ), ∃ β : 𝓢(Lie E n, ℂ), ∀ W : GA E n → ℂ, Continuous W →
        (∃ C : ℝ, ∀ g, ‖W g‖ ≤ C) → IsWh (psiA E) W → (∀ g, ∀ u ∈ U, W (g * finGL E n u) = W g) →
        ∀ p, InPS S p → conv (fop c W) β p = H p * conv W α 1

def SphAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (W : GA E n → ℂ), IsWh (psiA E) W →
    (∀ w ∉ S, GoodAt w (psiL w) ∧ EigAt w (B w) W) → (∀ g k, InKS S k → W (g * finGL E n k) = W g) →
    ∀ p : GA E n, SuppIn S (GeneralLinearGroup.map (pFin E) p) → W p = 0 → ∀ k, Away S k → W (p * finGL E n k) = 0

def Vanish : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), 1 ≤ n → ∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
    (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (f : GA E n → ℂ), Nice f →
    (∀ w ∉ S, GoodAt w (psiL w) ∧ EigAt w (B w) f) → (∀ g k, InKS S k → f (g * finGL E n k) = f g) →
    (∀ p, InPS S p → whittaker f p = 0) → f = 0

def OrthStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure]
    (f : GA E n → ℂ), Continuous f → (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) → IsLeftInvariant f →
    ∀ a : RightCosetSpace (Reduction.rationalGLOne E n) → ℂ, Continuous a → (∃ C : ℝ, ∀ q, ‖a q‖ ≤ C) →
    (∀ g (h : IsLeftInvariant fun x => f (x * g)), ∫ q, a q * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) = 0) →
    ∀ (β : 𝓢(Lie E n, ℂ)) (h : IsLeftInvariant (conv f β)), ∫ q, a q * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) = 0

def OrthConv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure]
    (φ φ' : cuspForms E n), φ ∈ centralCuspForms E n → φ' ∈ centralCuspForms E n → Orth μ φ φ' →
    ∀ β β' : 𝓢(Lie E n, ℂ), conv φ.1 β = conv φ'.1 β' → conv φ.1 β = 0

def NiceOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : cuspForms E n),
    (∃ V : OpenSubgroup (GL (Fin n) (Af E)), ∀ g, ∀ v ∈ V, φ.1 (g * finGL E n v) = φ.1 g) ∧
      (φ ∈ centralCuspForms E n → Nice φ.1)

def Seed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (U : Submodule ℂ (cuspForms E n)), U ≠ ⊥ → U ≤ centralCuspForms E n →
    Fb.Stab U → ∃ φ ∈ U, ∃ α : 𝓢(Lie E n, ℂ), conv (whittaker φ.1) α 1 = 1

def SetUp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (U U' : Submodule ℂ (cuspForms E n)), SameSat U U' →
    ∀ φ φ' : cuspForms E n, ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ),
      (∀ w ∉ S, GoodAt w (psiL w) ∧ Sat w (B w) U ∧ Sat w (B w) U') ∧
      (∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g) ∧ ∀ g k, InKS S k → φ'.1 (g * finGL E n k) = φ'.1 g

def Pair : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), 1 ≤ n → ∀ U U' : Submodule ℂ (cuspForms E n), U ≠ ⊥ → U' ≠ ⊥ →
    U ≤ centralCuspForms E n → U' ≤ centralCuspForms E n → Fb.Stab U → Fb.Stab U' → SameSat U U' →
    ∃ φ ∈ U, ∃ φ' ∈ U', ∃ β β' : 𝓢(Lie E n, ℂ), conv φ.1 β = conv φ'.1 β' ∧ conv φ.1 β ≠ 0

def CenSame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (U U' : Submodule ℂ (cuspForms E n)), U ≠ ⊥ → SameSat U U' →
    U ≤ centralCuspForms E n → U' ≤ centralCuspForms E n

def Compl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure]
    (U : Submodule ℂ (cuspForms E n)), U ≤ centralCuspForms E n → Fb.Stab U →
    ∃ C : Submodule ℂ (cuspForms E n), Fb.Stab C ∧ U ⊔ C = centralCuspForms E n ∧
      ∀ φ ∈ U, ∀ φ' ∈ C, inner ℂ (CuspidalSpectrum.cuspToL2 μ φ) (CuspidalSpectrum.cuspToL2 μ φ') = 0

def Proj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (U U' C : Submodule ℂ (cuspForms E n)), Fb.Stab U → Fb.Stab U' →
    Fb.Stab C → U ⊓ U' = ⊥ → U' ≠ ⊥ → U' ≤ U ⊔ C → SameSat U U' →
    ∃ D ≤ C, D ≠ ⊥ ∧ Fb.Stab D ∧ SameSat U D

def SmoCentral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), 1 ≤ n → ∀ U U' : Submodule ℂ (cuspForms E n), Fb.Stab U → Fb.Stab U' →
    Irr U → Irr U' → U ≤ centralCuspForms E n → SameSat U U' → U = U'

theorem smoCentral_of (h2 : CenSame) (h3 : Pair) (h4 : Compl) (h4' : Proj) (h5 : OrthTr) (h6 : OrthConv) : SmoCentral := by
  intro E _ _ _ n hn U U' sU sU' iU iU' l hs
  have l' := h2 E n U U' iU.1 hs l
  have si : Fb.Stab (U ⊓ U') :=
    ⟨fun X φ h => ⟨sU.ρ X φ h.1, sU'.ρ X φ h.2⟩, fun X φ h => ⟨sU.σ X φ h.1, sU'.σ X φ h.2⟩,
      fun X φ h => ⟨sU.τ X φ h.1, sU'.τ X φ h.2⟩⟩
  rcases iU'.2 _ inf_le_right si with h0 | h0
  · exfalso
    let μ : Measure (Reduction.normOneGL E n) := Measure.haar
    obtain ⟨C, sC, hsup, ho⟩ := h4 E n μ U l sU
    obtain ⟨D, hD, hD0, sD, hs'⟩ := h4' E n U U' C sU sU' sC h0 iU'.1 (l'.trans hsup.ge) hs
    have lD : D ≤ centralCuspForms E n := hD.trans (le_sup_right.trans hsup.le)
    obtain ⟨φ, hφ, φ', hφ', β, β', e, h⟩ := h3 E n hn U D iU.1 hD0 l lD sU sD hs'
    exact h (h6 E n μ φ φ' (l hφ) (lD hφ')
      (h5 E n μ U D l lD sU sD (fun a ha b hb => ho a ha b (hD hb)) φ hφ φ' hφ') β β' e)
  · exact ((iU.2 U' (inf_eq_right.1 h0) sU').resolve_left iU'.1).symm

def Carrier : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : GlobalTheory.CuspRep.CuspSub E n),
    ∃ U : Submodule ℂ (cuspForms E n), Fb.Stab U ∧ Irr U ∧ ∀ f : GA E n → ℂ, (∃ ψ ∈ U, ψ.1 = f) ↔ ∃ φ ∈ π.V, φ.1 = f

def EigOfSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : GlobalTheory.CuspRep.CuspSub E n)
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → ∀ φ ∈ π.V,
    (∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w n, φ.1 (g * finGL E n (locGL E n w k)) = φ.1 g) → EigAt w B φ.1

def NormTwist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), 1 ≤ n → ∀ π : GlobalTheory.CuspRep.CuspSub E n,
    ∃ χ : Formalism.L2.Host.HChar E, ∀ φ ∈ (π.twist χ).V, ∀ (s : {r : ℝ // 0 < r}) (g : GA E n),
      φ.1 (Reduction.centralSection E n s * g) = φ.1 g

def StrongMultOneC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π π' : GlobalTheory.CuspRep.CuspSub E n),
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ B, GlobalTheory.LFun.HasSatGL w (π.locRep w) B ∧ GlobalTheory.LFun.HasSatGL w (π'.locRep w) B) → π.V = π'.V

theorem strong_of (h0 : SmoCentral) (h1 : Carrier) (h2 : EigOfSat) (h3 : NormTwist) : StrongMultOneC := by
  intro E _ _ _ n π π' hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have key : ∀ σ : GlobalTheory.CuspRep.CuspSub E 0, σ.V = ⊤ := fun σ => by
      obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot σ.ne_bot
      have h : φ.1 1 ≠ 0 := fun h => hne (Subtype.ext (funext fun g => by rw [Subsingleton.elim g 1]; exact h))
      refine eq_top_iff.2 fun ψ _ => ?_
      have e : ψ = (ψ.1 1 / φ.1 1) • φ := Subtype.ext (funext fun g => by
        rw [Subsingleton.elim g 1]
        exact (div_mul_cancel₀ _ h).symm)
      rw [e]
      exact σ.V.smul_mem _ hφ
    rw [key, key]
  obtain ⟨χ, hc⟩ := h3 E n hn π
  have hs' : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ B, GlobalTheory.LFun.HasSatGL w ((π.twist χ).locRep w) B ∧ GlobalTheory.LFun.HasSatGL w ((π'.twist χ).locRep w) B := by
    filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)] with w ⟨B, a, b⟩ hu
    exact ⟨_, GlobalTheory.SphGal.hasSatGL_twist E n π χ w B hu a, GlobalTheory.SphGal.hasSatGL_twist E n π' χ w B hu b⟩
  suffices h : π.twist χ = π'.twist χ by
    have h' := congrArg (·.twist χ⁻¹) h
    simp only [← GlobalTheory.CuspRep.CuspSub.twist_mul, mul_inv_cancel, GlobalTheory.CuspRep.CuspSub.twist_one] at h'
    rw [h']
  generalize π.twist χ = π at hc hs'
  generalize π'.twist χ = π' at hs'
  obtain ⟨U, sU, iU, hU⟩ := h1 E n π
  obtain ⟨U', sU', iU', hU'⟩ := h1 E n π'
  have sat : ∀ (σ : GlobalTheory.CuspRep.CuspSub E n) (W : Submodule ℂ (cuspForms E n)),
      (∀ f : GA E n → ℂ, (∃ ψ ∈ W, ψ.1 = f) ↔ ∃ φ ∈ σ.V, φ.1 = f) → ∀ w B, GlobalTheory.LFun.HasSatGL w (σ.locRep w) B →
      Sat w B W := fun σ W hW w B hB ψ hψ hK => by
    obtain ⟨φ, hφ, e⟩ := (hW _).1 ⟨ψ, hψ, rfl⟩
    rw [← e] at hK ⊢
    exact h2 E n σ w B hB φ hφ hK
  have e : U = U' := h0 E n hn U U' sU sU' iU iU' (fun ψ hψ s g => by
      obtain ⟨φ, hφ, e⟩ := (hU _).1 ⟨ψ, hψ, rfl⟩
      rw [← e]
      exact hc φ hφ s g)
    (hs'.mono fun w ⟨B, a, b⟩ => ⟨B, sat π U hU w B a, sat π' U' hU' w B b⟩)
  subst e
  refine GlobalTheory.CuspRep.CuspSub.ext (Submodule.ext fun φ => ⟨fun h => ?_, fun h => ?_⟩)
  · obtain ⟨φ', h', e⟩ := (hU' _).1 ((hU _).2 ⟨φ, h, rfl⟩)
    rwa [← Subtype.ext e]
  · obtain ⟨φ', h', e⟩ := (hU _).1 ((hU' _).2 ⟨φ, h, rfl⟩)
    rwa [← Subtype.ext e]

end UpperTheory.V.Af.StrongMultiplicityOne
