import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join.KernelKilling

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem conj_entry (t : Fin n → kˣ) (u : GL (Fin n) k) (i j : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹ := by
  have hinv : (((diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal fun i => ((t i : k))⁻¹ := by
    rw [← map_inv, val_diagT]
    congr 1
    funext i
    simp
  rw [Units.val_mul, Units.val_mul, hinv, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_close {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    {c B : ValueGroupWithZero k} (hc : c ≤ 1) (hB0 : B ≠ 0)
    (hB : ∀ i j, valuation k ((u : Matrix (Fin n) (Fin n) k) i j) ≤ B)
    (t : Fin n → kˣ)
    (ht : ∀ i j, i < j → valuation k (t i : k) ≤ c * B⁻¹ * valuation k (t j : k)) (i j : Fin n) :
    valuation k (((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ c ∧
      valuation k (((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  rw [conj_entry]
  rw [mem_unipB] at hu
  obtain ⟨hlow, hdiag⟩ := hu
  have hc1 : c ≤ 1 := hc
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hne : i ≠ j := ne_of_lt hij
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne hne
    have hvj : valuation k (t j : k) ≠ 0 := by simp
    have key : valuation k ((t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹) ≤ c := by
      rw [map_mul, map_mul, map_inv₀]
      calc valuation k (t i : k) * valuation k ((u : Matrix (Fin n) (Fin n) k) i j) *
            (valuation k (t j : k))⁻¹
          ≤ c * B⁻¹ * valuation k (t j : k) * B * (valuation k (t j : k))⁻¹ := by
            gcongr
            · exact ht i j hij
            · exact hB i j
        _ = c * (B⁻¹ * B) * (valuation k (t j : k) * (valuation k (t j : k))⁻¹) := by
            simp only [mul_comm, mul_assoc, mul_left_comm]
        _ = c := by rw [inv_mul_cancel₀ hB0, mul_inv_cancel₀ hvj, mul_one, mul_one]
    rw [h1, sub_zero]
    exact ⟨key, le_trans key hc1⟩
  · rw [hdiag i, Matrix.one_apply_eq]
    have : (t i : k) * 1 * (t i : k)⁻¹ = 1 := by simp
    rw [this, sub_self, map_zero, map_one]
    exact ⟨zero_le', le_refl _⟩
  · have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
    rw [hlow i j hij, h1]
    simp

private theorem exists_bound (u : GL (Fin n) k) : ∃ B : ValueGroupWithZero k, B ≠ 0 ∧ ∀ i j,
    valuation k ((u : Matrix (Fin n) (Fin n) k) i j) ≤ B ∧
      valuation k (((u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ B := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun p : Fin n × Fin n =>
    max (valuation k ((u : Matrix (Fin n) (Fin n) k) p.1 p.2))
      (valuation k (((u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2)))
  refine ⟨max M 1, ?_, fun i j => ⟨?_, ?_⟩⟩
  · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  · exact le_trans (le_trans (le_max_left _ _) (hM (i, j))) (le_max_left _ _)
  · exact le_trans (le_trans (le_max_right _ _) (hM (i, j))) (le_max_left _ _)

private theorem conj_mem {K : Subgroup (GL (Fin n) k)} (hK : IsOpen (K : Set (GL (Fin n) k)))
    {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n)) :
    ∃ r : ValueGroupWithZero k, r ≠ 0 ∧ ∀ t : Fin n → kˣ,
      (∀ i j, i < j → valuation k (t i : k) ≤ r * valuation k (t j : k)) →
        diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ K := by
  obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1
    (hK.mem_nhds K.one_mem)
  obtain ⟨B, hB0, hB⟩ := exists_bound u
  set c : ValueGroupWithZero k :=
    valuation k ((GroundTheory.Automorphic.GLnLocal.uniformizer k : k)) ^ m with hcdef
  have hc : c ≤ 1 := pow_le_one₀ zero_le'
    (le_of_lt (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one k))
  have hc0 : c ≠ 0 := pow_ne_zero _ (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero k)
  have hui : u⁻¹ ∈ unipB k (Fin n) := inv_mem hu
  refine ⟨c * B⁻¹, mul_ne_zero hc0 (inv_ne_zero hB0), fun t ht => hm ?_⟩
  have hA := conj_close hu hc hB0 (fun i j => (hB i j).1) t ht
  have hI := conj_close hui hc hB0 (fun i j => (hB i j).2) t ht
  have hinv : (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹)⁻¹ =
      diagT k (Fin n) t * u⁻¹ * (diagT k (Fin n) t)⁻¹ := by group
  rw [SetLike.mem_coe, GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff,
    GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff, hinv]
  refine ⟨⟨fun i j => (Valuation.mem_integer_iff _ _).2 (hA i j).2,
    fun i j => (Valuation.mem_integer_iff _ _).2 (hI i j).2⟩, fun i j => (hA i j).1⟩

end UpperTheory.Gal.Join.KernelKilling

theorem UpperTheory.Gal.Join.kerKill :
    UpperTheory.Gal.Join.KerKill := by
  intro k _ _ _ _ n V _ _ π K hK e he v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, x, rfl⟩ := hw
    obtain ⟨r, hr, h⟩ := UpperTheory.Gal.Join.KernelKilling.conj_mem hK.co.2 u.2
    refine ⟨r, hr, fun t ht => ?_⟩
    have hk := he.inv _ (h t ht) (π (diagT k (Fin n) t) x)
    have hc : π (diagT k (Fin n) t * (u : GL (Fin n) k) * (diagT k (Fin n) t)⁻¹)
        (π (diagT k (Fin n) t) x) = π (diagT k (Fin n) t) (π (u : GL (Fin n) k) x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [hc] at hk
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hk, sub_self]
  | zero => exact ⟨1, one_ne_zero, fun t _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r₁, h₁, ha⟩ := ha
    obtain ⟨r₂, h₂, hb⟩ := hb
    refine ⟨min r₁ r₂, ?_, fun t ht => ?_⟩
    · rcases min_choice r₁ r₂ with h | h <;> rw [h] <;> assumption
    · rw [map_add, map_add,
        ha t fun i j hij => (ht i j hij).trans (mul_le_mul' (min_le_left _ _) le_rfl),
        hb t fun i j hij => (ht i j hij).trans (mul_le_mul' (min_le_right _ _) le_rfl), add_zero]
  | smul c a _ ha =>
    obtain ⟨r, hr, ha⟩ := ha
    exact ⟨r, hr, fun t ht => by rw [map_smul, map_smul, ha t ht, smul_zero]⟩
