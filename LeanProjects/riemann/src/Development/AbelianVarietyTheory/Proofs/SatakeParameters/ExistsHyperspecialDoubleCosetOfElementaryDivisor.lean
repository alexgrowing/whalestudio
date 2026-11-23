import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFactsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialOfSplitPlaceStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement

namespace GlobalTheory.SplitLabel

open Matrix

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem smul_mulVec_congr (ε : R) (M : Matrix n n R) {x y : n → R} (h : ε • x = ε • y) :
    ε • M *ᵥ x = ε • M *ᵥ y := by
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h]

omit [DecidableEq n] in
theorem smul_mulVec_mat (ε : R) {A B B' : Matrix n n R} (h : ε • (A * B) = ε • B') (x : n → R) :
    ε • A *ᵥ (B *ᵥ x) = ε • B' *ᵥ x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, h, Matrix.smul_mulVec]

omit [DecidableEq n] in

theorem stab_of_bases (ε : R) (hε : ε * ε = ε) (Λ Z : Set (n → R)) {A B B' : Matrix n n R}
    (h : ε • (A * B) = ε • B')
    (h1 : ∀ z ∈ Z, ε • B *ᵥ z ∈ Λ) (h2 : ∀ y ∈ Λ, ∃ z ∈ Z, ε • y = ε • B *ᵥ z)
    (h1' : ∀ z ∈ Z, ε • B' *ᵥ z ∈ Λ) (h2' : ∀ y ∈ Λ, ∃ z ∈ Z, ε • y = ε • B' *ᵥ z) :
    (∀ y ∈ Λ, ε • A *ᵥ y ∈ Λ) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ε • y = ε • A *ᵥ z := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := h2 y hy
    rw [smul_mulVec_congr ε A e, smul_mulVec_mat ε h]
    exact h1' z hz
  · obtain ⟨z, hz, e⟩ := h2' y hy
    refine ⟨_, h1 z hz, ?_⟩
    rw [e, ← smul_mulVec_mat ε h]
    apply smul_mulVec_congr
    rw [smul_smul, hε]

theorem stab_of_div (ε : R) (Λ Z : Set (n → R)) {A B B' M M' N b : Matrix n n R}
    (t t' : n → R) (h : ε • (A * B) = ε • B') (hN : N * (A * M) = 1) (hb : b = N * M')
    (hΛ : ∀ y ∈ Λ, ε • y ∈ Λ)
    (hu : ∀ z ∈ Z, ∃ w ∈ Z, ε • (fun i => t' i * z i) = ε • fun i => t i * w i)
    (hu' : ∀ z ∈ Z, ∃ w ∈ Z, ε • (fun i => t i * z i) = ε • fun i => t' i * w i)
    (h3 : ∀ y ∈ Λ, ∃ z ∈ Z, ε • M *ᵥ y = ε • B *ᵥ fun i => t i * z i)
    (h4 : ∀ z ∈ Z, ∃ y ∈ Λ, ε • M *ᵥ y = ε • B *ᵥ fun i => t i * z i)
    (h3' : ∀ y ∈ Λ, ∃ z ∈ Z, ε • M' *ᵥ y = ε • B' *ᵥ fun i => t' i * z i)
    (h4' : ∀ z ∈ Z, ∃ y ∈ Λ, ε • M' *ᵥ y = ε • B' *ᵥ fun i => t' i * z i) :
    (∀ y ∈ Λ, ε • b *ᵥ y ∈ Λ) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ε • y = ε • b *ᵥ z := by
  have key : ∀ y y' : n → R, ε • M' *ᵥ y' = ε • A *ᵥ (M *ᵥ y) → ε • b *ᵥ y' = ε • y := by
    intro y y' e
    rw [hb, ← Matrix.mulVec_mulVec, smul_mulVec_congr ε N e, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hN, Matrix.one_mulVec]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := h3' y hy
    obtain ⟨w, hw, ew⟩ := hu z hz
    obtain ⟨y', hy', e'⟩ := h4 w hw
    rw [key y' y]
    · exact hΛ y' hy'
    · rw [e, smul_mulVec_congr ε B' ew, smul_mulVec_congr ε A e', smul_mulVec_mat ε h]
  · obtain ⟨z, hz, e⟩ := h3 y hy
    obtain ⟨w, hw, ew⟩ := hu' z hz
    obtain ⟨y', hy', e'⟩ := h4' w hw
    refine ⟨y', hy', (key y y' ?_).symm⟩
    rw [e', smul_mulVec_congr ε A e, smul_mulVec_mat ε h, smul_mulVec_congr ε B' ew]

omit [DecidableEq n] in
theorem smul_mul_congr_left (ε : R) {X Y : Matrix n n R} (h : ε • X = ε • Y) (Z : Matrix n n R) :
    ε • (X * Z) = ε • (Y * Z) := by
  rw [← Matrix.smul_mul, h, Matrix.smul_mul]

omit [DecidableEq n] in
theorem smul_mul_congr_right (ε : R) {X Y : Matrix n n R} (h : ε • X = ε • Y) (Z : Matrix n n R) :
    ε • (Z * X) = ε • (Z * Y) := by
  rw [← Matrix.mul_smul, h, Matrix.mul_smul]

end Alg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem change_unif {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ ϖ' : 𝓞 D.host.E) (k : Fin V.rank → ℤ) (he : IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h1' : ϖ' ∈ P.asIdeal) (h2' : ϖ' ∉ P.asIdeal ^ 2)
    (z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (hz : IntVec z) :
    ∃ w, IntVec w ∧ finPart D e • (fun i => finPart D (incA D ((ϖ' : D.host.E) ^ k i)) * z i) =
      finPart D e • fun i => finPart D (incA D ((ϖ : D.host.E) ^ k i)) * w i := by
  have hε : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
  have h0 : (ϖ : D.host.E) ≠ 0 := by
    intro h
    have : ϖ = 0 := by exact_mod_cast h
    exact h2 (this ▸ zero_mem _)
  refine ⟨fun i => finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) * z i,
    fun i => GlobalTheory.SplitLatBasis.mul_mem_intAE D ((GlobalTheory.T.completedLattice_integrality V).2.1 P e ϖ ϖ' he h1 h2 h1' h2' (k i)) (hz i), ?_⟩
  funext i
  have e1 : finPart D (incA D ((ϖ' : D.host.E) ^ k i)) = finPart D (incA D ((ϖ : D.host.E) ^ k i)) *
      finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) := by
    rw [← map_mul, ← map_mul, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e1]
  linear_combination (-(finPart D (incA D ((ϖ : D.host.E) ^ k i)) *
      finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) * z i)) * hε

theorem split_label : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E) (d : List ℤ) (α α' : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → Formalism.L2.Theta.SuppAt e V α → Formalism.L2.Theta.SuppAt e V α' → DivAt V e (ϖ : D.host.E) d α → DivAt V e (ϖ' : D.host.E) d α' → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α * b := by
  intro D V P e ϖ ϖ' d α α' he h1 h2 h1' h2' hα hα' hd hd'
  obtain ⟨-, B, hB1, hB2, hB3, hB4⟩ := hd
  obtain ⟨-, B', hB1', hB2', hB3', hB4'⟩ := hd'
  have hε : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
  obtain ⟨C, hBC, hCB⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 _ B hε fun y hy => (hB2 y hy).imp fun _ h => h.2
  obtain ⟨C', hBC', hCB'⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 _ B' hε fun y hy => (hB2' y hy).imp fun _ h => h.2
  have hinv : finPart D e • ((B' * C) * (B * C')) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) := by
    have := smul_mul_congr_right _ (smul_mul_congr_left _ hCB C') B'
    rw [Matrix.one_mul, hBC'] at this
    rw [← this]
    simp only [Matrix.mul_assoc]
  obtain ⟨a, haS, ha⟩ := GlobalTheory.T.exists_adelic_unitary_split_place_component V e he.1 _ _ hinv
  have hAB : finPart D e • (finMat D.sp.cm.sig V.gram a * B) = finPart D e • B' := by
    rw [smul_mul_congr_left _ ha B, Matrix.mul_assoc, smul_mul_congr_right _ hCB B', Matrix.mul_one]
  have hs := stab_of_bases (finPart D e) hε {y | y ∈ LamHat V} {z | IntVec z} hAB
    (fun z hz => hB1 z hz) (fun y hy => hB2 y hy) (fun z hz => hB1' z hz) (fun y hy => hB2' y hy)
  have haK : a ∈ KsphC V ∅ := GlobalTheory.T.mem_hyperspecial_of_split_place_stabilizer V e a he.1 haS hs.1 hs.2
  obtain ⟨hf1, hf2, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e (e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨L, hL⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hf1 hf2).1
  have hbS : Formalism.L2.Theta.SuppAt e V ((a * α)⁻¹ * α') :=
    (hL _).1 (L.mul_mem (L.inv_mem (L.mul_mem ((hL _).2 haS) ((hL _).2 hα))) ((hL _).2 hα'))
  have hN : finMat D.sp.cm.sig V.gram (a * α)⁻¹ *
      (finMat D.sp.cm.sig V.gram a * finMat D.sp.cm.sig V.gram α) = 1 := by
    rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel,
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  have ht := stab_of_div (finPart D e) {y | y ∈ LamHat V} {z | IntVec z}
    (fun i => finPart D (incA D ((ϖ : D.host.E) ^ d.getD i.1 0)))
    (fun i => finPart D (incA D ((ϖ' : D.host.E) ^ d.getD i.1 0))) hAB hN
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ (a * α)⁻¹ α')
    (fun y hy => (GlobalTheory.T.completedLattice_integrality V).1 _ (GlobalTheory.AdIdem.idempotent_mem_intAE D _ hε) y hy)
    (fun z hz => change_unif V P e ϖ ϖ' _ he h1 h2 h1' h2' z hz)
    (fun z hz => change_unif V P e ϖ' ϖ _ he h1' h2' h1 h2 z hz)
    (fun y hy => hB3 y hy) (fun z hz => hB4 z hz) (fun y hy => hB3' y hy) (fun z hz => hB4' z hz)
  have hbK : (a * α)⁻¹ * α' ∈ KsphC V ∅ := GlobalTheory.T.mem_hyperspecial_of_split_place_stabilizer V e _ he.1 hbS ht.1 ht.2
  exact ⟨a, ⟨haK, haS⟩, _, ⟨hbK, hbS⟩, by rw [mul_inv_cancel_left]⟩

end GlobalTheory.SplitLabel
