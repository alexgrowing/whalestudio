import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

noncomputable section

namespace GlobalTheory.IwasawaGL

theorem diagPow_val {K : Type} [Field K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    ((GlobalTheory.JSW.diagPow ϖ l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => ((ϖ ^ l i : Kˣ) : K)) := rfl

theorem exists_unit_part (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (x : w.adicCompletion E)
    (hx : x ≠ 0) :
    ∃ e : ℤ, Valued.v (x * ((ϖ ^ (-e) : (w.adicCompletion E)ˣ) : w.adicCompletion E)) = 1 := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.1 h0
  refine ⟨-Multiplicative.toAdd γ, ?_⟩
  rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← hγ, neg_neg,
    ← WithZero.coe_zpow, ← WithZero.coe_mul]
  rw [show (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

theorem iwasawa_diagPow : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w a, g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  intro E _ _ a w ϖ hϖ g
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.spherical_iwasawa E w g
  have hd : ∀ i, (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i ≠ 0 :=
    Formalism.UG.P.spherical_diag_ne_zero b hb
  choose e he using fun i => exists_unit_part E w ϖ hϖ _ (hd i)
  let c : Fin a → w.adicCompletion E := fun i =>
    (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i * ((ϖ ^ (-e i) : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have hc0 : ∀ i, c i ≠ 0 := fun i => mul_ne_zero (hd i) (Units.ne_zero _)
  have hcO : ∀ i, c i ∈ Ov E w := fun i => (he i).le
  have hcO' : ∀ i, (c i)⁻¹ ∈ Ov E w := fun i => by
    show Valued.v (c i)⁻¹ ≤ 1
    rw [map_inv₀, he i, inv_one]
  let Dc : GL (Fin a) (w.adicCompletion E) :=
    ⟨Matrix.diagonal c, Matrix.diagonal (fun i => (c i)⁻¹),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hc0 i),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hc0 i)⟩
  have hDc : Dc ∈ KGL w a := by
    refine Formalism.UG.P.glint_mem_range_of_integral (Ov E w) Dc
      ⟨Matrix.diagonal (fun i => (⟨c i, hcO i⟩ : Ov E w)), ?_⟩
      ⟨Matrix.diagonal (fun i => (⟨(c i)⁻¹, hcO' i⟩ : Ov E w)), ?_⟩
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc]
      split_ifs <;> simp
    · ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, Dc, Units.inv_mk]
      split_ifs <;> simp
  let N : ℕ := ∑ i, (e i).natAbs
  let l : Fin a → ℕ := fun i => (e i + N).toNat
  have hexp : ∀ i, ((ϖ⁻¹) ^ N * ϖ ^ (l i) : (w.adicCompletion E)ˣ) = ϖ ^ (e i) := by
    intro i
    have hle : (e i).natAbs ≤ N :=
      Finset.single_le_sum (f := fun j => (e j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h1 : -((e i).natAbs : ℤ) ≤ e i := by rw [Int.natCast_natAbs]; exact neg_abs_le _
    have h2 : ((e i).natAbs : ℤ) ≤ N := by exact_mod_cast hle
    have hl : ((l i : ℕ) : ℤ) = e i + N := Int.toNat_of_nonneg (by omega)
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add, hl]
    congr 1; ring
  have hT : ((GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc : GL (Fin a) (w.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) := by
    rw [Units.val_mul, Units.val_mul, diagPow_val, diagPow_val]
    change Matrix.diagonal _ * Matrix.diagonal _ * Matrix.diagonal c = _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← Units.val_mul, hexp i]
    simp only [c]
    rw [mul_left_comm, ← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]
  let u : GL (Fin a) (w.adicCompletion E) := b * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc)⁻¹
  have hu : u * (GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * Dc) = b := by
    simp only [u]; group
  have hmat : (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) *
      Matrix.diagonal (fun i => (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i i) = b := by
    rw [← hT, ← Units.val_mul, hu]
  have hent : ∀ i j, (u : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j *
      (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) j j = (b : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
    intro i j
    have := congrFun (congrFun hmat i) j
    rwa [Matrix.mul_diagonal] at this
  have hmem : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := hent i j
      rw [hb hij] at h
      exact (mul_eq_zero.1 h).resolve_right (hd j)
    · exact mul_right_cancel₀ (hd i) (by rw [one_mul]; exact hent i i)
  refine ⟨u, hmem, N, l, Dc * k, Subgroup.mul_mem _ hDc hk, ?_⟩
  simp only [u]
  group

end GlobalTheory.IwasawaGL
