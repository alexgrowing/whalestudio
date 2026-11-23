import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitVacAnnih

open GlobalTheory.FinPl.FrameLat

theorem trace_rankOne {k m n Y Y' : Type} [Field k] [Fintype m] [DecidableEq m] [Fintype n] [Fintype Y] [Fintype Y']
    (A G : Matrix m m k) (hAG : G * A = 1) (N : Matrix m n k) (B : Matrix n n k) (βT : Matrix n Y k) (βS : Matrix m Y' k)
    (γS : Matrix Y' m k) (hS : βS * γS = 1) (c : Y → k) (x : m → k) :
    Matrix.trace (A * N * B * (βT * vecMulVec c ((x ᵥ* G) ᵥ* βS) * γS)) = x ⬝ᵥ (N * B) *ᵥ (βT *ᵥ c) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hS,
    Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc A, ← Matrix.mul_assoc G, hAG, Matrix.one_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_of_char {ψk : AddChar k Circle} (h : HasConductor ψk 1) {b : k} (hb : ∀ a ∈ 𝒪[k], ψk (a * b) = 1) :
    b ∈ 𝒪[k] := by
  by_cases h0 : b = 0
  · rw [h0]; exact zero_mem _
  have h1 := (h b).1 fun t ht => by
    have := hb (t / b) (by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ ht zero_le)
    rwa [div_mul_cancel₀ _ h0] at this
  rw [Valuation.mem_integer_iff]
  simpa using h1

theorem annihilator_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ y : WO S T, IsHalf (cA D q.e) y → (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) → y ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT ψ ψk _ hχ hc y hy hann
  have hce : cA D q.e ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
    rw [← sec_one q]
    exact ⟨csec_mem_idAt 1, (cA_int_iff _).2 (sec_mem_intAt q 1 (one_mem _)).2⟩
  have hcs : ∀ a : AE D, cA D (q.sec (q.pr (cA D a))) = cA D q.e * a := fun a => by
    rw [q.sec_pr, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj]
  have hgram : ∀ (V : HSp D) i j, q.pr (cA D (incA D (V.gram i j))) = (V.gram.map (q.pr.comp (incA D))) j i :=
    fun V i j => by rw [cA_incA, GlobalTheory.LatVac.gram_star]; rfl
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, hU.2 T LT]
  refine ⟨fun i j => ?_, fun x hx => ?_⟩
  · rw [← hy i j]
    exact Ideal.mul_mem_right _ _ hce.1
  set N : Matrix (Fin S.rank) (Fin T.rank) k := Matrix.of fun b c => q.pr (cA D (y c b)) with hN
  set x' : Fin S.rank → k := fun j => q.pr (cA D (x j)) with hx'
  have hyN : y = N.transpose.map fun a => cA D ((ofSplit q).ι a) := by
    ext i j
    exact ((hcs _).trans (hy i j)).symm
  have hx1 : (fun j => cA D (q.sec (x' j))) ∈ GlobalTheory.FinPl.latV S LS (· = q.v) := by
    have := smul_mem hS hx hce
    convert this using 1
    funext j
    exact hcs _
  have hyx : (y : Matrix _ _ (AE D)) *ᵥ x = fun i => cA D (q.sec ((x' ᵥ* N) i)) := by
    funext i
    have : (x' ᵥ* N) i = q.pr (cA D (((y : Matrix _ _ (AE D)) *ᵥ x) i)) := by
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, RingHom.map_mul, hN, hx', Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this, hcs]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, hy i j]
  show (y : Matrix _ _ (AE D)) *ᵥ x ∈ _
  rw [hyx, csec_mem_iff hT]
  intro u hu
  have huc : FT.β *ᵥ (FT.γ *ᵥ u) = u := by rw [Matrix.mulVec_mulVec, FT.βγ, Matrix.one_mulVec]
  have hcint : ∀ i, (FT.γ *ᵥ u) i ∈ 𝒪[k] := (hFT _).2 (by rw [huc]; exact hu)
  set f := q.pr.comp (incA D) with hf
  have hrow : ∀ s, ((x' ᵥ* S.gram.map f) ᵥ* FS.β) s ∈ 𝒪[k] := fun s => by
    have h1 := (csec_mem_iff hS x').1 hx1 _ ((hFS (Pi.single s 1)).1 fun i => by
      by_cases h : i = s
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
    convert h1 using 1
    simp only [hgram, Matrix.mulVec_single_one, Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.col, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine int_of_char hc fun a ha => ?_
  have h2 := hann (vecMulVec (a • (FT.γ *ᵥ u)) ((x' ᵥ* S.gram.map f) ᵥ* FS.β)) fun r s =>
    mul_mem (mul_mem ha (hcint r)) (hrow s)
  have hA : S.gram.map f * (S.gram⁻¹).map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero f) (map_one f)]
  rw [GlobalTheory.LocSympl.psi_sympl_up _ FS FT ψ ψk hχ, hyN, GlobalTheory.LocSympl.pi_hO_up] at h2
  have h3 := trace_rankOne _ _ hA N (T.gram.map f) FT.β FS.β FS.γ FS.βγ (a • (FT.γ *ᵥ u)) x'
  rw [Matrix.mulVec_smul, huc, Matrix.mulVec_smul, dotProduct_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at h3
  have h4 : ∑ i, ∑ j, u i * q.pr (cA D (incA D (T.gram i j))) * (x' ᵥ* N) j = (x' ᵥ* N) ⬝ᵥ T.gram.map f *ᵥ u := by
    rw [Finset.sum_comm]
    simp only [hgram, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h4, ← smul_eq_mul, ← h3]
  exact Circle.ext h2

end GlobalTheory.SplitVacAnnih

end
