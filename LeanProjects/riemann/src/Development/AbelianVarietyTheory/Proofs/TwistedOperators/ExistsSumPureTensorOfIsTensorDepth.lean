import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
open MeasureTheory GlobalTheory.FunObj

noncomputable section
namespace GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitsPowInv_val (ϖ : kˣ) (e : ℕ) : (((ϖ ^ e)⁻¹ : kˣ) : k) = ((ϖ : k) ^ e)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

theorem resMk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  have h0 : (ϖ : k) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    unitsPowInv_val]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : (a : k) - b = (ϖ : k) ^ e * c := by
      have := congrArg Subtype.val hc
      simpa using this
    rw [h1, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]

theorem mem_of_inv_mul_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {x : k}
    (h : (((ϖ ^ e)⁻¹ : kˣ) : k) * x ∈ 𝒪[k]) : x ∈ 𝒪[k] := by
  have hx : x = (ϖ : k) ^ e * ((((ϖ ^ e)⁻¹ : kˣ) : k) * x) := by
    rw [unitsPowInv_val, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
  rw [hx]
  exact mul_mem (pow_mem hϖ.mem _) h

theorem mem_matLat_pow_smul_iff (ϖ : kˣ) (e : ℕ) {m n : ℕ} {Z : Matrix (Fin m) (Fin n) k} :
    Z ∈ matLat (Fin m) (ϖ ^ e • stdLat k (Fin n)) ↔ ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] :=
  ⟨fun h i j => mem_stdLat.1 ((mem_smul_lat _ _ _).1 (h i)) j,
   fun h i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => h i j)⟩

def resClass (ϖ : kˣ) {e : ℕ} {m n : ℕ} (c : Fin m → Fin n → Res k e) : Set (Matrix (Fin m) (Fin n) k) :=
  {X | ∀ i j, X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k]}

theorem isNatDatum_resClass {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {m n : ℕ} (c : Fin m → Fin n → Res k e) :
    IsNatDatum ϖ e ((resClass ϖ c).indicator (1 : Matrix (Fin m) (Fin n) k → ℂ)) := by
  classical
  refine ⟨fun X hX => Set.indicator_of_notMem (fun h => hX (mem_matLat_stdLat.2 fun i j => (h i j).1)) _,
    fun X Z hZ => ?_⟩
  have hZ' := (mem_matLat_pow_smul_iff ϖ e).1 hZ
  have hiff : X + Z ∈ resClass ϖ c ↔ X ∈ resClass ϖ c := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have hz : Z i j ∈ 𝒪[k] := mem_of_inv_mul_mem hϖ e (hZ' i j)
    have h1 : (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) =
        (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) + (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j := by ring
    show (X i j + Z i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) ∈ 𝒪[k]) ↔
      (X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k])
    rw [h1, add_mem_cancel_right hz, add_mem_cancel_right (hZ' i j)]
  simp only [Set.indicator_apply, hiff, Pi.one_apply]

theorem exists_sum_pureTensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  intro k _ _ _ _ G ϖ hϖ e γ T hT
  classical
  let L := γ.toFinset
  let I := ∀ b : L, Fin (G.rank b.1.tgt) → Fin (G.rank b.1.src) → Res k e
  let rep : I → G.Args := fun c b => if h : b ∈ L then liftRes (c ⟨b, h⟩) else 0
  let ψ : I → ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ :=
    fun c b => if h : b ∈ L then (resClass ϖ (c ⟨b, h⟩)).indicator 1 else 1
  have key : ∀ z, T z = ∑ c, T (rep c) * G.lines₂ γ (ψ c) z := by
    intro z
    simp only [Grid.lines₂]
    by_cases hint : ∀ b ∈ γ, z b ∈ matLat _ (stdLat k _)
    · let c0 : I := fun b i j => Ideal.Quotient.mk _
        ⟨z b.1 i j, mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2)) i j⟩
      have hmem : ∀ (c : I) (b : L), z b.1 ∈ resClass ϖ (c b) ↔ c b = c0 b := by
        intro c b
        have hz := mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2))
        constructor
        · intro h
          funext i j
          have := (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).2 (h i j).2
          rw [Ideal.Quotient.mk_out] at this
          exact this.symm
        · rintro h i j
          refine ⟨hz i j, ?_⟩
          exact (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).1
            (by rw [Ideal.Quotient.mk_out, h])
      rw [Finset.sum_eq_single c0]
      · have hprod : (γ.map fun b => ψ c0 b (z b)).prod = 1 := by
          refine List.prod_eq_one fun x hx => ?_
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
          have hb' : b ∈ L := List.mem_toFinset.2 hb
          simp only [ψ, dif_pos hb']
          exact Set.indicator_of_mem ((hmem c0 ⟨b, hb'⟩).2 rfl) _
        rw [hprod, mul_one]
        let w : G.Args := fun b => if b ∈ γ then z b - rep c0 b else 0
        have hw : ∀ b, w b ∈ matLat _ (ϖ ^ e • stdLat k _) := by
          intro b
          by_cases hb : b ∈ γ
          · have hb' : b ∈ L := List.mem_toFinset.2 hb
            have h2 := (hmem c0 ⟨b, hb'⟩).2 rfl
            refine (mem_matLat_pow_smul_iff ϖ e).2 fun i j => ?_
            simp only [w, if_pos hb, rep, dif_pos hb', Matrix.sub_apply]
            exact (h2 i j).2
          · simp only [w, if_neg hb]
            exact zero_mem _
        rw [← hT.2.2 (rep c0) w hw]
        refine hT.1 fun b hb => ?_
        have hb : b ∈ γ := hb
        simp [w, hb]
      · intro c _ hc
        obtain ⟨b, hb⟩ : ∃ b : L, c b ≠ c0 b := by
          by_contra hne
          push_neg at hne
          exact hc (funext hne)
        rw [List.prod_eq_zero (List.mem_map.2 ⟨b.1, List.mem_toFinset.1 b.2, ?_⟩), mul_zero]
        simp only [ψ, dif_pos b.2]
        exact Set.indicator_of_notMem (mt (hmem c b).1 hb) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hint
      obtain ⟨b, hb, hz⟩ := hint
      rw [hT.2.1 z b hb hz]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [List.prod_eq_zero (List.mem_map.2 ⟨b, hb, ?_⟩), mul_zero]
      have hb' : b ∈ L := List.mem_toFinset.2 hb
      simp only [ψ, dif_pos hb']
      have hn : z b ∉ resClass ϖ (c ⟨b, hb'⟩) := fun h =>
        hz (mem_matLat_stdLat.2 fun i j => (h i j).1)
      exact Set.indicator_of_notMem hn _
  refine ⟨Fintype.card I, fun i => T (rep ((Fintype.equivFin I).symm i)),
    fun i => ψ ((Fintype.equivFin I).symm i), ?_, ?_⟩
  · intro i b hb
    have hb' : b ∈ L := List.mem_toFinset.2 hb
    simp only [ψ, dif_pos hb']
    exact isNatDatum_resClass hϖ e _
  · intro z
    rw [key z]
    exact (Equiv.sum_comp (Fintype.equivFin I).symm (fun c => T (rep c) * G.lines₂ γ (ψ c) z)).symm

end GlobalTheory.TensorExpansion
