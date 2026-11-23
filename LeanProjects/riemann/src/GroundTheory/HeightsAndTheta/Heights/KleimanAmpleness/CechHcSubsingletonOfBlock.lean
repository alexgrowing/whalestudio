import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart Cell CechC cellMon cechZc cechBc)

noncomputable section

def eulerChar (F : Type) [Field F] {K : Type} [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) : ℚ :=
  ∑ i ∈ Finset.range (∑ k, (Fintype.card (ι k) - 1) + 1),
    (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ)

def EulerVar.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (v : Σ k, ι k),
    NumbersDVR.IsMultiHomogIdeal V →
    (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) →
    (∀ (m : K → ℤ) (i : ℕ),
      FiniteDimensional F (cechHc ι (quotPart F (V.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}))) m i)) →
    (∀ (m : K → ℤ) (i : ℕ),
      FiniteDimensional F (cechHc ι (quotPart F (V ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) m i)) →
    ∀ m : K → ℤ, eulerChar F ι V m =
      eulerChar F ι (V.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) (m - Pi.single v.1 1) +
        eulerChar F ι (V ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) m

section Vanish

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in

theorem subsingleton_loc_of_block {V : Ideal (MvPolynomial (Σ k, ι k) F)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ V) (I : ∀ k, Finset (ι k)) (hI : (I k).Nonempty) :
    Subsingleton (LocalizedModule (cellMon F I) (MvPolynomial (Σ k, ι k) F ⧸ V)) := by
  obtain ⟨i, hi⟩ := hI
  have ht : (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ cellMon F I :=
    Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hz : ∀ x : LocalizedModule (cellMon F I) (MvPolynomial (Σ k, ι k) F ⧸ V), x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h a s =>
      rw [← LocalizedModule.zero_mk (1 : cellMon F I), LocalizedModule.mk_eq]
      refine ⟨⟨_, ht⟩, ?_⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp only [one_smul, smul_zero]
      rw [Submonoid.smul_def]
      change (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) • Ideal.Quotient.mk V a = 0
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact V.mul_mem_right _ (hk i)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem cechHc_subsingleton_of_block {V : Ideal (MvPolynomial (Σ k, ι k) F)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ V) (m : K → ℤ) (n : ℕ) :
    Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, Subsingleton (LocalizedModule (cellMon F I.1) (MvPolynomial (Σ k, ι k) F ⧸ V)) :=
    fun I => subsingleton_loc_of_block hk I.1 (I.2.1 k)
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

end Vanish

theorem EulerVar.hyps :
    let v : (Σ _ : Unit, Fin 1) := ⟨(), 0⟩
    let V : Ideal (MvPolynomial (Σ _ : Unit, Fin 1) ℚ) := Ideal.span {X v}
    NumbersDVR.IsMultiHomogIdeal V ∧
      (∀ (m : Unit → ℤ) (i : ℕ), FiniteDimensional ℚ (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ V) m i)) ∧
      (∀ (m : Unit → ℤ) (i : ℕ), FiniteDimensional ℚ
        (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ (V.colon (Ideal.span {(X v : MvPolynomial (Σ _ : Unit, Fin 1) ℚ)}))) m i)) ∧
      (∀ (m : Unit → ℤ) (i : ℕ), FiniteDimensional ℚ
        (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ (V ⊔ Ideal.span {(X v : MvPolynomial (Σ _ : Unit, Fin 1) ℚ)})) m i)) := by
  intro v V
  have hX : (X v : MvPolynomial (Σ _ : Unit, Fin 1) ℚ) ∈ V := Ideal.subset_span rfl
  have hfin : ∀ W : Ideal (MvPolynomial (Σ _ : Unit, Fin 1) ℚ), (X v : MvPolynomial _ ℚ) ∈ W →
      ∀ (m : Unit → ℤ) (i : ℕ), FiniteDimensional ℚ (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ W) m i) := by
    intro W hW m i
    have := cechHc_subsingleton_of_block (ι := fun _ : Unit => Fin 1) (V := W) (k := ())
      (fun j : Fin 1 => by rw [Subsingleton.elim j 0]; exact hW) m i
    have : Finite (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ W) m i) := Finite.of_subsingleton
    exact Module.Finite.of_finite
  refine ⟨NumbersDVR.isMultiHomogIdeal_span_singleton
    (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight (fun _ : Unit => Fin 1)) v), hfin V hX, hfin _ ?_,
    hfin _ (Ideal.mem_sup_left hX)⟩
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
  exact V.mul_mem_left _ hX

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
