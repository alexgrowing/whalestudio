import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExpSums
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleCoverForms

namespace UpperTheory.V.Pr

open Matrix

private theorem comb {G ι : Type} [Group G] [Fintype ι] (R : G → ι → ι → Prop)
    (h1 : ∀ i, R 1 i i) (hinv : ∀ g i, ∃ k, R g i k ∧ R g⁻¹ k i)
    (hc : ∀ g h, ∃ x, (∀ i k j, R g i k → R h k j → R x i j) ∧
      (∀ i k j, R h⁻¹ i k → R g⁻¹ k j → R x⁻¹ i j)) :
    ∃ b, (∀ i, R b i i) ∧ (∀ i j, R b i j → R b⁻¹ i j) ∧
      ∀ g i k l j, R g i k → R b k l → R g⁻¹ l j → R b i j := by
  classical
  let T : G → Finset (Bool × ι × ι) := fun g =>
    Finset.univ.filter fun s => if s.1 then R g s.2.1 s.2.2 else R g⁻¹ s.2.1 s.2.2
  let P : G → Prop := fun g => (∀ i, R g i i) ∧ ∀ i, R g⁻¹ i i
  have hP1 : P 1 := ⟨h1, by rw [inv_one]; exact h1⟩
  obtain ⟨b, hb, hmax⟩ : ∃ b, P b ∧ ∀ c, P c → (T c).card ≤ (T b).card := by
    have hfin : ((fun g => (T g).card) '' {g | P g}).Finite :=
      (Set.finite_Iic (Fintype.card (Bool × ι × ι))).subset (by
        rintro _ ⟨g, _, rfl⟩
        exact Finset.card_le_univ _)
    obtain ⟨_, ⟨b, hb, rfl⟩, hm⟩ := Set.exists_max_image _ id hfin ⟨_, 1, hP1, rfl⟩
    exact ⟨b, hb, fun c hc => hm _ ⟨c, hc, rfl⟩⟩
  have key : ∀ c, P c → (∀ i j, R c i j → R b i j) ∧ ∀ i j, R c⁻¹ i j → R b⁻¹ i j := by
    intro c hcP
    obtain ⟨x, hx1, hx2⟩ := hc b c
    have hPx : P x := ⟨fun i => hx1 i i i (hb.1 i) (hcP.1 i), fun i => hx2 i i i (hcP.2 i) (hb.2 i)⟩
    have hsub : T b ⊆ T x := by
      rintro ⟨t, i, j⟩ hs
      cases t
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true, if_false] at hs ⊢
        exact hx2 i i j (hcP.2 i) hs
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, if_true] at hs ⊢
        exact hx1 i j j hs (hcP.1 j)
    have heq : T b = T x := Finset.eq_of_subset_of_card_le hsub (hmax x hPx)
    constructor
    · intro i j hij
      have : ((true, i, j) : Bool × ι × ι) ∈ T x := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, if_true]
        exact hx1 i i j (hb.1 i) hij
      rw [← heq] at this
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and, if_true] using this
    · intro i j hij
      have : ((false, i, j) : Bool × ι × ι) ∈ T x := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true, if_false]
        exact hx2 i j j hij (hb.2 j)
      rw [← heq] at this
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true, if_false] using this
  refine ⟨b, hb.1, ?_, ?_⟩
  · have := (key b⁻¹ ⟨hb.2, by rw [inv_inv]; exact hb.1⟩).2
    rwa [inv_inv] at this
  · intro g i k l j hik hkl hlj
    obtain ⟨x, hx1, hx2⟩ := hc g b
    obtain ⟨y, hy1, hy2⟩ := hc x g⁻¹
    rw [inv_inv] at hy2
    have hPy : P y := by
      constructor
      · intro t
        obtain ⟨s, hs1, hs2⟩ := hinv g t
        exact hy1 t s t (hx1 t s s hs1 (hb.1 s)) hs2
      · intro t
        obtain ⟨s, hs1, hs2⟩ := hinv g t
        exact hy2 t s t hs1 (hx2 s s t (hb.2 s) hs2)
    exact (key y hPy).1 i j (hy1 i l j (hx1 i k l hik hkl) hlj)

private theorem expProd {κ : Type} [Field κ] {n : ℕ} (α : Fin n → κˣ) (hα : FreeRatios α)
    (A B C D : Matrix (Fin n) (Fin n) κ) : ∃ m : ℕ,
    (∀ i k j, A i k ≠ 0 → B k j ≠ 0 → (A * diagonal (fun i => ((α i : κˣ) : κ)) ^ m * B) i j ≠ 0) ∧
    (∀ i k j, C i k ≠ 0 → D k j ≠ 0 → (C * diagonal (fun i => (((α i)⁻¹ : κˣ) : κ)) ^ m * D) i j ≠ 0) := by
  let c0 : Bool × Fin n × Fin n → Fin n → κ := fun s k =>
    if s.1 then A s.2.1 k * B k s.2.2 else C s.2.1 k * D k s.2.2
  let a0 : Bool → Fin n → κˣ := fun t k => if t then α k else (α k)⁻¹
  have ha0 : ∀ t, FreeRatios (a0 t) := by
    intro t
    cases t
    · intro i j hij m hm h
      apply hα i j hij m hm
      simpa [a0] using h
    · simpa [a0] using hα
  obtain ⟨m, hm⟩ := expSums κ (Fin n) {s : Bool × Fin n × Fin n // ∃ k, c0 s k ≠ 0}
    (fun s => a0 s.1.1) (fun s => c0 s.1) (fun s => ha0 _) (fun s => s.2)
  refine ⟨m, ?_, ?_⟩
  · intro i k j h1 h2
    have := hm ⟨(true, i, j), k, by simpa [c0] using ⟨h1, h2⟩⟩
    convert this using 1
    rw [diagonal_pow, mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [mul_diagonal, c0, a0, if_true, Pi.pow_apply]
    ring
  · intro i k j h1 h2
    have := hm ⟨(false, i, j), k, by simpa [c0] using ⟨h1, h2⟩⟩
    convert this using 1
    rw [diagonal_pow, mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [mul_diagonal, c0, a0, Bool.false_eq_true, if_false, Pi.pow_apply]
    ring

private theorem finOrbit {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) (hr : StrongIrr r)
    (W : Submodule κ (Fin n → κ)) (F : Set (Submodule κ (Fin n → κ))) (hF : F.Finite)
    (hW : ∀ g, W.map (Matrix.toLin' (gm r g)) ∈ F) : W = ⊥ ∨ W = ⊤ := by
  letI : MulAction G (Submodule κ (Fin n → κ)) :=
    { smul := fun g W => W.map (Matrix.toLin' (gm r g))
      one_smul := fun W => by
        change W.map (Matrix.toLin' (gm r 1)) = W
        simp [gm]
      mul_smul := fun g h W => by
        change W.map (Matrix.toLin' (gm r (g * h))) =
          (W.map (Matrix.toLin' (gm r h))).map (Matrix.toLin' (gm r g))
        rw [← Submodule.map_comp, ← Matrix.toLin'_mul]
        simp [gm] }
  have hfin : (MulAction.orbit G W).Finite := hF.subset (by
    rintro _ ⟨g, rfl⟩
    exact hW g)
  haveI : Finite (MulAction.orbit G W) := hfin
  haveI : Finite (G ⧸ MulAction.stabilizer G W) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G W)
  refine hr W (MulAction.stabilizer G W) Subgroup.finiteIndex_of_finite_quotient fun g => ?_
  rw [MulAction.mem_stabilizer_iff]
  change W.map (Matrix.toLin' (gm r g)) = W ↔ _
  constructor
  · intro h v hv
    rw [← h]
    exact ⟨v, hv, by simp⟩
  · intro h
    have hinj : Function.Injective (Matrix.toLin' (gm r g)) := by
      intro v w hvw
      have := congrArg (fun x => gm r g⁻¹ *ᵥ x) hvw
      have h1 : gm r g⁻¹ * gm r g = 1 := by
        rw [gm, gm, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      simpa only [toLin'_apply, mulVec_mulVec, h1, one_mulVec] using this
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      simpa using h v hv
    · exact (Submodule.equivMapOfInjective _ hinj W).finrank_eq.symm

end UpperTheory.V.Pr

open Matrix in
theorem UpperTheory.V.Pr.fullEx :
    UpperTheory.V.Pr.FullEx :=
  _root_.UpperTheory.Reformulated.B.StronglyIrreducibleFreeRatios.fullEx
