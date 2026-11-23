import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixPreservesLatticeMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeUnitQuotientFiniteRepsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

open GlobalTheory.SphLineComm in

theorem GlobalTheory.SphLineComm.commensurated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (v : Pl F) (g : GlobalTheory.SphLine.locU σ G.W v),
      (((GlobalTheory.SphLine.locK σ G.W v).subgroupOf (GlobalTheory.SphLine.locU σ G.W v)).map (MulAut.conj g).toMonoidHom).relIndex
        ((GlobalTheory.SphLine.locK σ G.W v).subgroupOf (GlobalTheory.SphLine.locU σ G.W v)) ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v g
  have hlat : G.W.L.IsLattice E := hT.geo.hW.lat
  let ρ : GlobalTheory.SphLine.locU σ G.W v →* AddMonoid.End (Fin (a + a') → AE F E) :=
    { toFun := fun k => { toFun := fun z => mat k.1 *ᵥ z, map_zero' := Matrix.mulVec_zero _,
                          map_add' := Matrix.mulVec_add _ }
      map_one' := by
        apply AddMonoidHom.ext; intro z
        show mat (1 : UA σ G.W.J) *ᵥ z = z
        rw [GlobalTheory.SphLine.mat_one, Matrix.one_mulVec]
      map_mul' := by
        intro k1 k2
        apply AddMonoidHom.ext; intro z
        show mat (k1.1 * k2.1) *ᵥ z = mat k1.1 *ᵥ (mat k2.1 *ᵥ z)
        rw [GlobalTheory.SphLine.mat_mul, Matrix.mulVec_mulVec] }
  have hρ : ∀ k z, ρ k z = mat k.1 *ᵥ z := fun _ _ => rfl

  have hsupp : ∀ k : GlobalTheory.SphLine.locU σ G.W v, ∀ z, (mat k.1 - 1) *ᵥ z = (mat k.1 - 1) *ᵥ (unitAt v • z) := by
    intro k z
    have h0 : (1 - unitAt v) • (mat k.1 - 1) = 0 := k.2 _ (by rw [map_sub, map_one, evFin_unitAt_self, sub_self])
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec]
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    rw [← h0]
  let π : (Fin (a + a') → AE F E) →+ (Fin (a + a') → AE F E) := DistribMulAction.toAddMonoidHom _ (unitAt v)
  have hπ : ∀ k z, ρ k z - z = ρ k (π z) - π z := by
    intro k z
    simp only [hρ]
    show mat k.1 *ᵥ z - z = mat k.1 *ᵥ (unitAt v • z) - unitAt v • z
    have := hsupp k z
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at this
    exact this
  have hπ' : ∀ k z, ρ k (π z) = π (ρ k z) := by
    intro k z
    show mat k.1 *ᵥ (unitAt v • z) = unitAt v • (mat k.1 *ᵥ z)
    exact Matrix.mulVec_smul _ _ _
  obtain ⟨n1, hn1, h1⟩ := GlobalTheory.T.local_matrix_preserves_lattice_multiple F E (a + a') G.W v (mat g.1 - 1) hlat g.2
  obtain ⟨n2, hn2, h2⟩ := GlobalTheory.T.local_matrix_preserves_lattice_multiple F E (a + a') G.W v (mat g⁻¹.1 - 1) hlat (g⁻¹).2
  have hg : ∀ z ∈ latHat G.W, (n1 * n2) • ρ g z ∈ latHat G.W ∧ (n1 * n2) • ρ g⁻¹ z ∈ latHat G.W := by
    intro z hz
    constructor
    · have e : ρ g z = z + (mat g.1 - 1) *ᵥ z := by rw [hρ, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      rw [e, smul_add, mul_comm, mul_smul, mul_smul]
      exact (latHat G.W).add_mem ((latHat G.W).nsmul_mem ((latHat G.W).nsmul_mem hz _) _)
        ((latHat G.W).nsmul_mem (h1 z hz) _)
    · have e : ρ g⁻¹ z = z + (mat g⁻¹.1 - 1) *ᵥ z := by rw [hρ, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      rw [e, smul_add, mul_smul, mul_smul]
      exact (latHat G.W).add_mem ((latHat G.W).nsmul_mem ((latHat G.W).nsmul_mem hz _) _)
        ((latHat G.W).nsmul_mem (h2 z hz) _)
  have hn : n1 * n2 ≠ 0 := Nat.mul_ne_zero hn1 hn2
  have htf : ∀ x : Fin (a + a') → AE F E, (n1 * n2) • x = 0 → x = 0 := by
    intro x hx
    rw [← Nat.cast_smul_eq_nsmul F] at hx
    exact (smul_eq_zero.mp hx).resolve_left (by exact_mod_cast hn)
  obtain ⟨S, hS, hfin⟩ := GlobalTheory.T.lattice_unit_quotient_finite_reps F E (a + a') G.W v (unitAt v) hlat (evI_unitAt v) (fun w hw => evFin_unitAt_ne hw)
    (by rw [evFin_unitAt_self]; exact one_mem _) ((n1 * n2) * (n1 * n2)) (Nat.mul_ne_zero hn hn)
  refine relIndex_conj_ne_zero ρ (latHat G.W) _ ?_ π hπ hπ' g (n1 * n2) htf hg S hS hfin
  intro k
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hk z hz
    exact hk.2 z hz
  · intro hk
    exact ⟨k.2, fun z hz => hk z hz⟩
