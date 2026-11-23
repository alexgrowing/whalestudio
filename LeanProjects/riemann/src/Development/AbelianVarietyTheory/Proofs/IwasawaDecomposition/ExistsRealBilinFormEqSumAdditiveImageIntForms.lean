import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
open GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_toReal_span_fintype {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ) : ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (Q : κ → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let H := Module.Free.chooseBasis ℚ ℝ
  let S : Finset (Module.Free.ChooseBasisIndex ℚ ℝ) :=
    Finset.univ.biUnion fun p : Module.Free.ChooseBasisIndex ℤ L × Module.Free.ChooseBasisIndex ℤ L =>
      (H.repr (B (b p.1) (b p.2))).support
  let f : S × Module.Free.ChooseBasisIndex ℤ L × Module.Free.ChooseBasisIndex ℤ L → ℚ :=
    fun t => H.repr (B (b t.2.1) (b t.2.2)) t.1
  obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose m hm using hn
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
  have hm' : ∀ t, (m t : ℚ) = D * f t := fun t => by simpa [Submonoid.smul_def] using hm t
  let Q : S → LinearMap.BilinForm ℤ L := fun s => Matrix.toLinearMap₂ b b (fun i k => m (s, i, k))
  let g : S → ℝ →+ ℝ := fun s => (D : ℝ) • ((Rat.castHom ℝ).toAddMonoidHom.comp (H.coord s).toAddMonoidHom)
  have hQb : ∀ s i k, (Q s (b i) (b k) : ℝ) = D * (H.repr (B (b i) (b k)) s : ℝ) := fun s i k => by
    have h1 : Q s (b i) (b k) = m (s, i, k) := Matrix.toLinearMap₂_apply_basis _ _ _ _ _
    rw [h1]
    have := hm' (s, i, k)
    simp only [f] at this
    exact_mod_cast this
  have hQ : ∀ s y z, (Q s y z : ℝ) = g s (B y z) := by
    intro s
    have : toReal (Q s) = B.compr₂ (g s).toIntLinearMap := by
      refine LinearMap.ext_basis b b fun i k => ?_
      rw [toReal_apply, hQb]
      simp [g, H]
    intro y z
    simpa using LinearMap.congr_fun₂ this y z
  refine ⟨S, inferInstance, fun s => H s / D, Q, ?_, fun s => ⟨g s, hQ s⟩⟩
  refine LinearMap.ext_basis b b fun i k => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hQb, smul_eq_mul]
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD'
  have key : ∀ h r : ℝ, h / D * (D * r) = r * h := fun h r => by field_simp
  have e1 : ∀ x : S, H x / D * (D * (H.repr (B (b i) (b k)) x : ℝ)) = H.repr (B (b i) (b k)) x • H x := fun x => by
    rw [Rat.smul_def]; exact key _ _
  rw [Finset.sum_congr rfl fun x _ => e1 x]
  rw [Finset.sum_coe_sort S (fun x => H.repr (B (b i) (b k)) x • H x)]
  conv_lhs => rw [← H.linearCombination_repr (B (b i) (b k))]
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_of_support_subset _ ?_ (fun (x : Module.Free.ChooseBasisIndex ℚ ℝ) (a : ℚ) => a • H x)
    fun x _ => zero_smul ℚ (H x)
  intro x hx
  exact Finset.mem_biUnion.2 ⟨(i, k), Finset.mem_univ _, hx⟩

theorem exists_sum_toReal_additive_images : ∀ {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ), ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  intro L _ _ _ B
  obtain ⟨κ, _, w, Q, h1, h2⟩ := exists_toReal_span_fintype B
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun j => w (e.symm j), fun j => Q (e.symm j), ?_, fun j => h2 _⟩
  rw [h1]
  exact (e.symm.sum_comp fun s => w s • toReal (Q s)).symm

end GlobalTheory.PolFan
