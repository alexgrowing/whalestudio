import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedGraph
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedBase {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  stackedGraph b' a ⊔ Ideal.span (Set.range fun t => C (a t) * graphFirst t)

def IsStackedExc {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (E : Ideal (MRing (stackedBlocks T))) :
    Prop :=
  E ∈ (stackedBase b' a).minimalPrimes ∧ IsRelevant E

def DualStackedExcCycle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E ∧ ¬ IsHorizontal E ∧
      ∀ t : T,
        ((divCycle (stackedGraph b' a) (C (a t) * graphFirst t) E : ℤ) =
            divCycle (stackedGraph b' a) (graphSecond t) E + 1) ∧
        ∀ W : Ideal (MRing (stackedBlocks T)), ¬ IsHorizontal W → W ≠ E →
          divCycle (stackedGraph b' a) (C (a t) * graphFirst t) W = divCycle (stackedGraph b' a) (graphSecond t) W

def DualStackedExcGeoSecond.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      (geoNum (i - 1) E (fun _ => degSecond) : ℝ) * Real.log (charOf E) =
        Real.log (F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup)

def DualStackedExcGeoFirst.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∀ d : Fin (i - 1) → Unit ⊕ Unit → ℤ, (∀ j, d j = degFirst ∨ d j = degSecond) → (∃ j, d j = degFirst) →
        geoNum (i - 1) E d = 0

namespace DualStackedExcExample

open DualTopSimpleSubExample

theorem dualIdeal_eq_bot {F : HermLattice ℚ 1} {T : Type} [Fintype T] [Subsingleton T] (t₀ : T)
    (b : Module.Basis T ℤ (dualLattice F)) : dualIdeal b = ⊥ := by
  set c : ℚ := (b t₀ : Fin 1 → ℚ) 0 with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply b.ne_zero t₀
    apply Subtype.ext
    funext j
    fin_cases j
    simpa using h0
  let φ : MRing (dualBlocks T) →ₐ[ℤ] MvPolynomial (Fin 1) ℚ := aeval fun _ => C c * X 0
  let ψ : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] MvPolynomial (Fin 1) ℚ := aeval fun _ => C c⁻¹ * X 0
  have hcomp : ψ.toRingHom.comp φ.toRingHom =
      (map (Int.castRingHom ℚ)).comp (rename fun _ : (Σ _ : Unit, T) => (0 : Fin 1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · intro p
      simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, AlgHom.coe_toRingHom, φ, ψ, aeval_X, map_mul,
        aeval_C, rename_X, map_X, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
  have hinj : Function.Injective φ := by
    have h2 : Function.Injective
        ((map (Int.castRingHom ℚ)).comp (rename fun _ : (Σ _ : Unit, T) => (0 : Fin 1)).toRingHom) :=
      (map_injective _ Int.cast_injective).comp (rename_injective _ fun x y _ => by
        obtain ⟨⟨⟩, s⟩ := x
        obtain ⟨⟨⟩, s'⟩ := y
        rw [Subsingleton.elim s s'])
    rw [← hcomp, RingHom.coe_comp] at h2
    exact Function.Injective.of_comp h2
  have hev : ∀ f : MRing (dualBlocks T),
      MvPolynomial.eval (fun _ : Unit => (1 : ProjField ℚ 1)) (mConeMap (dualLatticeCoord b) f) =
        algebraMap (MvPolynomial (Fin 1) ℚ) (ProjField ℚ 1) (φ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C n => simp [mConeMap, φ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      have hq : q.2 = t₀ := Subsingleton.elim _ _
      simp only [map_mul, hp]
      congr 1
      simp [mConeMap, φ, dualLatticeCoord, hq, hc]
  rw [dualIdeal, mCoordIdeal, eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  apply hinj
  rw [map_zero]
  apply IsFractionRing.injective (MvPolynomial (Fin 1) ℚ) (ProjField ℚ 1)
  rw [map_zero, ← hev, RingHom.mem_ker.mp hf, map_zero]

theorem graphIdeal_bot {T : Type} [Fintype T] [DecidableEq T] [Subsingleton T] (t₀ : T) (a : T → ℤ)
    (ha : a t₀ ≠ 0) :
    graphIdeal (⊥ : Ideal (MRing (dualBlocks T))) (linForm (stackedDiag a)) = ⊥ := by
  set u : MRing (stackedBlocks T) := C (a t₀) * graphFirst t₀ with hu_def
  have hu : u ≠ 0 := mul_ne_zero (fun h => ha (C_eq_zero.mp h)) (X_ne_zero _)
  let θ : MRing (dualBlocks T) ⧸ (⊥ : Ideal (MRing (dualBlocks T))) →+* Localization.Away u :=
    (algebraMap (MRing (stackedBlocks T)) (Localization.Away u)).comp
      (Ideal.Quotient.lift ⊥ (rename fun p : (Σ _ : Unit, T) => (⟨Sum.inl (), p.2⟩ : Σ k, stackedBlocks T k)).toRingHom
        fun f hf => by rw [Submodule.mem_bot] at hf; rw [hf, map_zero])
  let ρ : MvPolynomial Unit (MRing (dualBlocks T) ⧸ (⊥ : Ideal (MRing (dualBlocks T)))) →+*
      Localization.Away u :=
    eval₂Hom θ fun _ => algebraMap _ _ (graphSecond t₀) * IsLocalization.Away.invSelf u
  have hρ : ρ.comp (graphMap ⊥ (linForm (stackedDiag a))) =
      algebraMap (MRing (stackedBlocks T)) (Localization.Away u) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · rintro ⟨(u | u), t⟩ <;> obtain ⟨⟩ := u
      · simp [ρ, θ, graphMap]
      · obtain rfl : t₀ = t := Subsingleton.elim (α := T) _ _
        have hg : linForm (ι := dualBlocks T) (ι₂ := dualBlocks T) (stackedDiag a) ⟨(), t₀⟩ =
            C (a t₀) * X ⟨(), t₀⟩ := by
          simp [linForm, stackedDiag, apply_ite C, ite_mul, Finset.sum_ite_eq]
        have h1 : graphMap ⊥ (linForm (stackedDiag a)) (X ⟨Sum.inr (), t₀⟩) =
            C (Ideal.Quotient.mk ⊥ (C (a t₀) * X ⟨(), t₀⟩)) * X () := by
          simp [graphMap, hg]
        have h2 : ρ (C (Ideal.Quotient.mk ⊥ (C (a t₀) * X ⟨(), t₀⟩))) =
            algebraMap (MRing (stackedBlocks T)) (Localization.Away u) u := by
          simp only [ρ, θ, coe_eval₂Hom, eval₂_C, RingHom.comp_apply, Ideal.Quotient.lift_mk,
            AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, rename_C, rename_X]
          rw [← map_mul]
          rfl
        have h3 : ρ (X ()) = algebraMap (MRing (stackedBlocks T)) (Localization.Away u) (graphSecond t₀) *
            IsLocalization.Away.invSelf u := by
          simp [ρ]
        rw [RingHom.comp_apply, h1, map_mul, h2, h3, mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
        rfl
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  have h0 : algebraMap (MRing (stackedBlocks T)) (Localization.Away u) f = 0 := by
    rw [← hρ, RingHom.comp_apply, RingHom.mem_ker.mp hf, map_zero]
  exact IsLocalization.injective (Localization.Away u) (powers_le_nonZeroDivisors_of_noZeroDivisors hu)
    (h0.trans (map_zero _).symm)

theorem isStackedExc_reduction {T : Type} [Fintype T] [DecidableEq T] [Subsingleton T] (t₀ : T)
    {F' : HermLattice ℚ 1} (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (ha : a t₀ ≠ 0) (q : ℕ)
    [Fact q.Prime] (hdvd : (q : ℤ) ∣ a t₀) :
    IsStackedExc b' a (RingHom.ker (MvPolynomial.map (Int.castRingHom (ZMod q)) :
      MRing (stackedBlocks T) →+* MvPolynomial (Σ k, stackedBlocks T k) (ZMod q))) := by
  set E := RingHom.ker (MvPolynomial.map (Int.castRingHom (ZMod q)) :
      MRing (stackedBlocks T) →+* MvPolynomial (Σ k, stackedBlocks T k) (ZMod q)) with hE_def
  have hΓ : stackedGraph b' a = ⊥ := by
    rw [stackedGraph, dualIdeal_eq_bot t₀ b']
    exact graphIdeal_bot t₀ a ha
  have hX : ∀ p, (X p : MRing (stackedBlocks T)) ∉ E := fun p h =>
    X_ne_zero (R := ZMod q) p (by simp only [hE_def, RingHom.mem_ker, map_X] at h; exact h)
  have hEprime : E.IsPrime := RingHom.ker_isPrime _
  have hbase : stackedBase b' a ≤ E := by
    rw [stackedBase, hΓ, bot_sup_eq, Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    obtain rfl : t = t₀ := Subsingleton.elim _ _
    show _ ∈ RingHom.ker _
    have h0 : (Int.castRingHom (ZMod q)) (a t) = 0 := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    rw [RingHom.mem_ker, map_mul, map_C, h0, C_0, zero_mul]
  refine ⟨⟨⟨hEprime, hbase⟩, fun Q ⟨hQ, hQb⟩ hQE => ?_⟩, fun k => ?_⟩
  · have hu : C (a t₀) * graphFirst t₀ ∈ Q :=
      hQb (Ideal.mem_sup_right (Ideal.subset_span ⟨t₀, rfl⟩))
    have hCa : (C (a t₀) : MRing (stackedBlocks T)) ∈ Q :=
      (hQ.mem_or_mem hu).resolve_right fun h => hX _ (hQE h)
    have hcomQ : (Q.comap (C : ℤ →+* MRing (stackedBlocks T))).IsMaximal := by
      refine Ideal.IsPrime.isMaximal (Ideal.IsPrime.comap _) fun hb => ha ?_
      have h1 : a t₀ ∈ Q.comap (C : ℤ →+* MRing (stackedBlocks T)) := hCa
      rw [hb] at h1
      exact h1
    have hne : E.comap (C : ℤ →+* MRing (stackedBlocks T)) ≠ ⊤ := fun h => by
      have h1 : (1 : ℤ) ∈ E.comap (C : ℤ →+* MRing (stackedBlocks T)) := h ▸ Submodule.mem_top
      exact hEprime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using h1))
    have hq : (q : ℤ) ∈ Q.comap (C : ℤ →+* MRing (stackedBlocks T)) := by
      rw [hcomQ.eq_of_le hne (Ideal.comap_mono hQE)]
      simp [hE_def, RingHom.mem_ker, Ideal.mem_comap]
    rw [hE_def, MvPolynomial.ker_map, Ideal.map_le_iff_le_comap, ZMod.ker_intCastRingHom, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hq
  · rcases k with ⟨⟩ | ⟨⟩
    · exact ⟨t₀, hX _⟩
    · exact ⟨t₀, hX _⟩

end DualStackedExcExample

end

end GroundTheory.Heights₂.Heights
