import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.IsoDuality

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_herm (V : Formalism.BasicNotions.HSpace E) (x y : V.V) : star (V.hT x y) = V.hT y x := by
  have := V.herm.eq x y
  rw [← starRingEnd_apply]; exact this

theorem iso_zero (V : Formalism.BasicNotions.HSpace E) {W : Submodule E V.V} (hW : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W)
    {w v : V.V} (hw : w ∈ W) (hv : v ∈ W) : V.hT w v = 0 := by
  have := hW hv
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this w hw

theorem finrank_le_of_sep (V : Formalism.BasicNotions.HSpace E) (A B : Submodule E V.V)
    (h : ∀ y ∈ B, (∀ x ∈ A, V.hT x y = 0) → y = 0) :
    Module.finrank E B ≤ Module.finrank E A := by
  classical
  let bA := Module.finBasis E A
  let Φ : B →ₗ[E] (Fin (Module.finrank E A) → E) :=
    LinearMap.pi (fun i => (V.hT (bA i : V.V)).comp B.subtype)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, V.hT (bA i : V.V) y = 0 := fun i => congrFun hy i
    apply Subtype.ext
    apply h y y.2
    intro x hx
    have hx' : (⟨x, hx⟩ : A) = ∑ i, (bA.repr ⟨x, hx⟩ i) • bA i := (bA.sum_repr _).symm
    have : x = ∑ i, (bA.repr ⟨x, hx⟩ i) • (bA i : V.V) := by
      calc x = ((∑ i, (bA.repr ⟨x, hx⟩ i) • bA i : A) : V.V) := by rw [← hx']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [this, map_sum]
    simp [map_smulₛₗ, hy']
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end GlobalTheory.IsoDuality

namespace GlobalTheory.IsoDuality

theorem exists_dual_bases : ∀ {D : D7} {V : HSp D} (X X' : Submodule D.host.E V.V), X ≠ ⊥ → X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X → X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' → (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) → (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) → ∃ (a : ℕ) (x x' : Fin a → V.V), 0 < a ∧ a ≤ wittIndex V ∧ Submodule.span D.host.E (Set.range x) = X ∧ Submodule.span D.host.E (Set.range x') = X' ∧ LinearIndependent D.host.E (Sum.elim x x') ∧ (∀ i j, V.hD (x i) (x j) = 0) ∧ (∀ i j, V.hD (x' i) (x' j) = 0) ∧ (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) := by
  classical
  intro D V X X' hX0 hX hX' h1 h2
  have hTX := fun {w v : V.V} (hw : w ∈ X) (hv : v ∈ X) => iso_zero V hX hw hv
  have hTX' := fun {w v : V.V} (hw : w ∈ X') (hv : v ∈ X') => iso_zero V hX' hw hv

  have hle1 : Module.finrank D.host.E X ≤ Module.finrank D.host.E X' :=
    finrank_le_of_sep V X' X (fun y hy h => h1 y hy (fun z hz => h z hz))
  have hle2 : Module.finrank D.host.E X' ≤ Module.finrank D.host.E X :=
    finrank_le_of_sep V X X' (fun y hy h => h2 y hy (fun z hz => by
      show V.hT y z = 0
      rw [← hT_herm, h z hz, star_zero]))
  set a := Module.finrank D.host.E X with ha
  let bx := Module.finBasis D.host.E X
  let x : Fin a → V.V := fun i => (bx i : V.V)
  have hxX : ∀ i, x i ∈ X := fun i => (bx i).2
  let Φ : X' →ₗ[D.host.E] (Fin a → D.host.E) :=
    LinearMap.pi (fun i => (V.hT (x i)).comp X'.subtype)
  have hΦ : ∀ y i, Φ y i = V.hT (x i) y := fun y i => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : ∀ i, V.hT (x i) y = 0 := fun i => congrFun hy i
    apply Subtype.ext
    apply h2 y y.2
    intro z hz
    have hz' : (⟨z, hz⟩ : X) = ∑ i, (bx.repr ⟨z, hz⟩ i) • bx i := (bx.sum_repr _).symm
    have : z = ∑ i, (bx.repr ⟨z, hz⟩ i) • x i := by
      calc z = ((∑ i, (bx.repr ⟨z, hz⟩ i) • bx i : X) : V.V) := by rw [← hz']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
    show V.hT (y : V.V) z = 0
    rw [← hT_herm, this, map_sum]
    simp [map_smulₛₗ, hy']
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hinj
    · simp [a]; omega
  choose g hg using fun j : Fin a => hsurj (Pi.single j 1)
  let x' : Fin a → V.V := fun j => (g j : V.V)
  have hx'X : ∀ j, x' j ∈ X' := fun j => (g j).2
  have hxx' : ∀ i j, V.hT (x i) (x' j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hg j) i
    rw [hΦ] at this
    show V.hT (x i) (g j : V.V) = _
    rw [this, Pi.single_apply]
  have hxli : LinearIndependent D.host.E x :=
    bx.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hli : LinearIndependent D.host.E (Sum.elim x x') := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr] at hc
    have hd : ∀ k, c (Sum.inr k) = 0 := by
      intro k
      have := congrArg (V.hT (x k)) hc
      rw [map_add, map_sum, map_sum, map_zero] at this
      simp only [map_smul, smul_eq_mul, hTX (hxX k) (hxX _), mul_zero, Finset.sum_const_zero,
        zero_add, hxx', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
      exact this
    have hc' : ∑ i, c (Sum.inl i) • x i = 0 := by
      simpa [hd] using hc
    have hcl := Fintype.linearIndependent_iff.1 hxli _ hc'
    rintro (i | j)
    · exact hcl i
    · exact hd j
  have hx'li : LinearIndependent D.host.E x' := hli.comp Sum.inr Sum.inr_injective
  refine ⟨a, x, x', ?_, ?_, ?_, ?_, hli, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (fun h => hX0 (Submodule.finrank_eq_zero.1 h))
  · exact GlobalTheory.Cusp.finrank_le_wittIndex hX
  · have : Set.range x = X.subtype '' Set.range bx := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bx.span_eq, Submodule.map_top, Submodule.range_subtype]
  · apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact hx'X j
    · rw [finrank_span_eq_card hx'li]; simp [a]; omega
  · intro i j
    show V.hT (x j) (x i) = 0
    exact hTX (hxX j) (hxX i)
  · intro i j
    show V.hT (x' j) (x' i) = 0
    exact hTX' (hx'X j) (hx'X i)
  · intro i j
    show V.hT (x' j) (x i) = _
    rw [← hT_herm, hxx']
    split_ifs <;> simp

end GlobalTheory.IsoDuality
