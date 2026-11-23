import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.VminusComp

def ht {n : ℕ} (μ : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * μ i

theorem ht_add {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ + ν) = ht μ + ht ν := by
  simp [ht, mul_add, Finset.sum_add_distrib]

theorem ht_sub {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ - ν) = ht μ - ht ν := by
  simp [ht, mul_sub, Finset.sum_sub_distrib]

theorem ht_root {n : ℕ} (a b : Fin n) : ht (Formalism.REAL.root a b) = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [ht, Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem weight_shift {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {ν : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F ν x) {a b : Fin n} (hab : ε a = ε b) :
    Formalism.REAL.IsWeight F (ν + Formalism.REAL.root a b) (F a b x) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ W => T x) (hF c c a b rfl hab)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, add_smul, add_comm]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, add_smul, sub_smul, add_comm]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2]

theorem word_weight {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {μ : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F μ x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ∃ ν, ht μ ≤ ht ν ∧ Formalism.REAL.IsWeight F ν (ew F w x) := by
  induction w with
  | nil => exact ⟨μ, le_rfl, by simpa [ew] using hx⟩
  | cons p w ih =>
    obtain ⟨ν, h1, h2⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have hp := hw p (List.mem_cons_self ..)
    refine ⟨ν + Formalism.REAL.root p.1 p.2, ?_, ?_⟩
    · rw [ht_add, ht_root]
      have : ((p.2 : ℕ) : ℝ) < ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp.2
      linarith
    · simpa only [ew, Module.End.mul_apply] using weight_shift hF h2 hp.1

theorem comp_weight {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℝ} {G : Arr V n 1}
    (hG : Formalism.REAL.IsWeight (arrE E 1) ν G) (a b : Fin n) :
    Formalism.REAL.IsWeight E (ν - Formalism.REAL.root a b) (G (fun _ => (a, b))) := by
  intro c
  have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hG c)
  simp only at h1
  rw [arr_operator_one_apply, PiLp.smul_apply, add_comm, ← eq_sub_iff_add_eq] at h1
  rw [h1]
  by_cases h1 : a = c <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, sub_smul]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, Ne.symm h1, add_smul, sub_smul]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2, Ne.symm h1]

theorem isoPart_stable {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (T : Set (Fin n → ℝ)) (S : Submodule ℂ W) :
    Formalism.REAL.KStable ε F (isoPart ε F T S) := by
  intro a b hab x hx
  have : isoPart ε F T S ≤ (isoPart ε F T S).comap (F a b) := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh z hz
    exact compact_span_le_isotypic_part hy hμ hyh (compact_span_stable_general y a b hab z hz)
  exact this hx

theorem vminus_comp : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (abelian₂ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E abelian₂ u → FiniteDimensional ℂ (kSpan ε E u) → KStable ε (arrE E 1) (Vminus ε E abelian₂ u) ∧ Vminus ε E abelian₂ u ≤ arrV0 ε E u 1 ∧ FiniteDimensional ℂ (Vminus ε E abelian₂ u) ∧ ∀ G ∈ Vminus ε E abelian₂ u, ∀ a b, ¬ b < a → ⟪u, at1 G a b⟫_ℂ = 0 := by
  intro V _ _ n ε E abelian₂ u hg hu hΛ hfd
  have hle : Vminus ε E abelian₂ u ≤ arrV0 ε E u 1 := by
    apply isotypic_part_le_of_forall
    intro y hy μ _ _
    exact compact_span_le_of_stable noncompact_arr_one_compact_stable hy
  have hfd0 := noncompact_arr_finite_dimensional (j := 1) hfd
  refine ⟨isoPart_stable _ _, hle, Submodule.finiteDimensional_of_le hle, ?_⟩
  intro G hG a b hab
  have hKR := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  let ℓ : Arr V n 1 →ₗ[ℂ] ℂ := (innerₛₗ ℂ u) ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V) (fun _ => (a, b)) ∘ₗ arrOf V n 1)
  have hℓ : ∀ G : Arr V n 1, ℓ G = ⟪u, G (fun _ => (a, b))⟫_ℂ := fun G => rfl
  have hker : Vminus ε E abelian₂ u ≤ LinearMap.ker ℓ := by
    apply isotypic_part_le_of_forall
    rintro y - μ ⟨a', b', hba, -, rfl⟩ hyh
    rw [(kLow _ n ε _ _ y hKR hyh).1, lowSpan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨ν, h1, h2⟩ := word_weight hKR hyh.1 w hw
    rw [SetLike.mem_coe, LinearMap.mem_ker, hℓ]
    refine kWtOrth V n ε E _ _ _ _ (isUnitary_kUnit ε E hu) hΛ.1 (comp_weight h2 a b) ?_
    intro h
    have h3 := congrArg ht h
    rw [ht_sub, ht_root] at h3
    rw [ht_add, ht_root] at h1
    have e1 : ((b' : ℕ) : ℝ) < ((a' : ℕ) : ℝ) := by exact_mod_cast hba
    have e2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast not_lt.mp hab
    linarith
  exact hker hG

end GlobalTheory.Jet.VminusComp
