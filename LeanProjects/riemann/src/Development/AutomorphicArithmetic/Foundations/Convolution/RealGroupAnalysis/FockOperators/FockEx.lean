import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.GaussMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.QuaternaryFormPolarization

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private def PF (δ : F) (O : Ops F) (f : V4 F → ℂ) : Prop :=
  ∃ Λ m, ∃ φ ∈ O.Fk (Vac δ ⊓ Fix δ Λ) m, φ.1 = f

private theorem fk_mono {δ : F} {O : Ops F} {Λ Λ' : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)} {m m' : ℕ}
    (hΛ : Λ' ≤ Λ) (hm : m ≤ m') {φ : S4 F} (hφ : φ ∈ O.Fk (Vac δ ⊓ Fix δ Λ) m) :
    φ ∈ O.Fk (Vac δ ⊓ Fix δ Λ') m' :=
  (fkBasic F O).1 _ _ (inf_le_inf_left _ ((fixEx F δ).2 _ _ hΛ)) m m' hm hφ

private theorem PF.add {δ : F} {O : Ops F} {f f' : V4 F → ℂ} (h : PF δ O f) (h' : PF δ O f') :
    PF δ O (f + f') := by
  obtain ⟨Λ, m, φ, hφ, rfl⟩ := h
  obtain ⟨Λ', m', φ', hφ', rfl⟩ := h'
  exact ⟨Λ ⊓ Λ', max m m', φ + φ',
    add_mem (fk_mono inf_le_left (le_max_left _ _) hφ) (fk_mono inf_le_right (le_max_right _ _) hφ'), rfl⟩

private theorem PF.smul {δ : F} {O : Ops F} {f : V4 F → ℂ} (c : ℂ) (h : PF δ O f) :
    PF δ O (c • f) := by
  obtain ⟨Λ, m, φ, hφ, rfl⟩ := h
  exact ⟨Λ, m, c • φ, Submodule.smul_mem _ c hφ, rfl⟩

private theorem PF.zero (δ : F) (O : Ops F) : PF δ O 0 :=
  ⟨⊤, 0, 0, zero_mem _, rfl⟩

private theorem PF.coord {δ : F} {O : Ops F} {f : V4 F → ℂ} (i : Fin 4) (w : InfinitePlace F) (h : PF δ O f) :
    PF δ O ((fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)) * f) := by
  obtain ⟨Λ, m, φ, hφ, rfl⟩ := h
  exact ⟨Λ, m + 1, O.x w i φ, (fkBasic F O).2.1 _ m w i φ hφ, funext fun v => O.x_apply w i φ v⟩

private theorem PF.poly {δ : F} {O : Ops F} {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) :
    ∀ f, PF δ O f → PF δ O (p * f) := by
  refine Algebra.adjoin_induction (p := fun p _ => ∀ f, PF δ O f → PF δ O (p * f)) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨i, w, rfl⟩ f hf
    exact PF.coord i w hf
  · intro c f hf
    have : (algebraMap ℂ (V4 F → ℂ) c) * f = c • f := by
      rw [Algebra.smul_def]
    rw [this]
    exact PF.smul c hf
  · intro a b _ _ ha hb f hf
    rw [add_mul]
    exact (ha f hf).add (hb f hf)
  · intro a b _ _ ha hb f hf
    rw [mul_assoc]
    exact ha _ (hb f hf)

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.fockEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Ops F) (s : Set (S4 F)), s.Finite → (∀ φ ∈ s, φ ∈ Fock D.δ) → ∃ Λ m, ∀ φ ∈ s, φ ∈ O.Fk (Vac D.δ ⊓ Fix D.δ Λ) m := by
  intro F E _ _ _ _ _ _ _ D O s hs
  have hgauss : ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
      PF D.δ O (fun v => gauss D.δ v * g (finPartPi v)) := by
    intro g hg
    let φ₀ : S4 F := ⟨_, gaussMem F E D g hg⟩
    obtain ⟨Λ, hΛ⟩ := (fixEx F D.δ).1 φ₀
    have hV : φ₀ ∈ Vac D.δ := by
      intro v v' e
      change (gauss D.δ v * g (finPartPi v)) * gauss D.δ v' = (gauss D.δ v' * g (finPartPi v')) * gauss D.δ v
      rw [e]
      ring
    exact ⟨Λ, 0, φ₀, ⟨hV, hΛ⟩, rfl⟩
  have hfock : ∀ φ ∈ Fock D.δ, PF D.δ O φ.1 := by
    intro φ hφ
    have hφ' : φ.1 ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
        φ = fun v => p v * gauss D.δ v * g (finPartPi v)} := hφ
    refine Submodule.span_induction (p := fun f _ => PF D.δ O f) ?_ (PF.zero _ _) ?_ ?_ hφ'
    · rintro _ ⟨p, hp, g, hg, rfl⟩
      have := PF.poly hp _ (hgauss g hg)
      convert this using 1
      funext v
      simp only [Pi.mul_apply, mul_assoc]
    · intro a b _ _ ha hb
      exact ha.add hb
    · intro c a _ ha
      exact ha.smul c
  induction s, hs using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨⊤, 0, fun φ h => absurd h (Set.notMem_empty φ)⟩
  | @insert a s _ _ ih =>
    intro h
    obtain ⟨Λ, m, hm⟩ := ih fun φ hφ => h φ (Set.mem_insert_of_mem _ hφ)
    obtain ⟨Λ', m', φ, hφ, e⟩ := hfock a (h a (Set.mem_insert _ _))
    obtain rfl : φ = a := Subtype.ext e
    refine ⟨Λ ⊓ Λ', max m m', ?_⟩
    rintro ψ' (rfl | hψ)
    · exact fk_mono inf_le_right (le_max_right _ _) hφ
    · exact fk_mono inf_le_left (le_max_left _ _) (hm ψ' hψ)
