import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def boundedCoeffSeries (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] : Subalgebra O K⟦X⟧ where
  carrier := {f | ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c}
  mul_mem' hf hg := Hom.bdd_mul hf hg
  add_mem' hf hg := Hom.bdd_add hf hg
  algebraMap_mem' c := ⟨1, (A O K).algebraMap_mem c⟩

theorem Hom.exists_E_pow_mul_frob_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.rdivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have key : ∀ {μ : Type} [Fintype μ] (Y : ZMod a → Matrix μ μ K⟦X⟧),
      (∀ τ i j, Y τ i j ∈ invE l e (A O K)) → ∃ n : ℕ, ∀ τ i j, E K l e ^ n * Y τ i j ∈ A O K := by
    intro μ _ Y hY
    choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
    refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (hn (τ, i, j))
  obtain ⟨n₁, hn₁⟩ := key P.mx P.mx_mem
  obtain ⟨n₂, hn₂⟩ := key Q.mxInv Q.mxInv_mem
  refine ⟨n₁ + n₂, fun τ h hh => ?_⟩
  obtain ⟨hb, Y, ⟨c, hc⟩, hF⟩ := hh
  have hA : ∀ f ∈ A O K, f ∈ boundedCoeffSeries O K := fun f hf => ⟨1, hf⟩
  have hfr : ∀ f ∈ boundedCoeffSeries O K, frob K l f ∈ boundedCoeffSeries O K := by
    rintro f ⟨d, hd⟩
    refine ⟨d, fun n => ?_⟩
    rw [coeff_frob]
    split_ifs
    · exact hd _
    · simpa using (norm_nonneg _).trans (hd 0)
  have hE : E K l e ∈ A O K := E_mem l e _
  refine ⟨mul_mem (hA _ (pow_mem hE _)) (hfr _ hb),
    (E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ), ?_, ?_⟩
  · have hmem : ∀ i j, ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ)) i j ∈
        boundedCoeffSeries O K := by
      intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact sum_mem fun k _ => mul_mem (sum_mem fun m _ =>
        mul_mem (hA _ (hn₁ τ i m)) (hfr _ ⟨c, fun n => hc m k n⟩)) (hA _ (hn₂ τ k j))
    choose d hd using hmem
    obtain ⟨D, hD⟩ := Finite.exists_le (fun p : ι × κ => d p.1 p.2)
    exact ⟨D, fun i j n => (hd i j n).trans (hD (i, j))⟩
  · have hmap : (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) =
        frob K l h • (1 : Matrix κ κ K⟦X⟧) := by
      have h1 : (F.mat (τ - 1) * Y).map (frob K l) = (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) :=
        Matrix.map_mul (f := (frob K l).toRingHom)
      rw [← h1, hF]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    calc F.mat τ * ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ))
        = (E K l e ^ n₁ * E K l e ^ n₂) • ((F.mat τ * P.mx τ) * Y.map (frob K l) * Q.mxInv τ) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = (E K l e ^ n₁ * E K l e ^ n₂) •
          (Q.mx τ * ((F.mat (τ - 1)).map (frob K l) * Y.map (frob K l)) * Q.mxInv τ) := by
          rw [F.comm, Matrix.mul_assoc (Q.mx τ)]
      _ = (E K l e ^ (n₁ + n₂) * frob K l h) • (1 : Matrix κ κ K⟦X⟧) := by
          rw [hmap, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mx_mul_mxInv, smul_smul, pow_add]

end GlobalTheory.BK
