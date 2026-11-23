import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbedding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped GlobalTheory.MixModel

namespace GlobalTheory.WittSect

theorem sub_one_mulVec_eq_zero {R : Type*} [CommRing R] {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin a) R) (Q : Matrix (Fin n) (Fin b) R) (v : Fin n → R) (p : Fin a → R) (q : Fin b → R)
    (hv : v = P *ᵥ p + Q *ᵥ q) (hP : M * P = P) (hQ : M * Q = Q) : (M - 1) *ᵥ v = 0 := by
  rw [hv, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP, hQ,
    sub_self]

theorem exists_hypDec_mem_NI : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B →
    ∃ d : GlobalTheory.MixModel.HypDec V V' r, d.e = C ∧ d.i₀ = B ∧ ∀ m : GA D V,
      HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = C.map (incA D) →
      HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = B.map (incA D) → m ∈ NI V C := by
  intro D V V' r C B hs
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hs
  have e : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D M = Mᴴ := fun _ => rfl
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  rw [e] at h1 h2 h3
  have hee : Cᴴ * V.gram * C = 0 := hs.frame.2.2
  have horth : Cᴴ * V.gram * B = 0 := by rw [← e]; exact hs.orth
  have hiso : Bᴴ * V.gram * B = V'.gram := by rw [← e]; exact hs.isom
  have h1' : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have h0e : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose horth
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have h0e' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  let d : GlobalTheory.MixModel.HypDec V V' r :=
    { e := C, e' := C', i₀ := B, ee := hee, e'e' := h2, e'e := h1', iso := hiso, i₀e := h0e, i₀e' := h0e',
      rank_add := hs.rank.symm }
  refine ⟨d, rfl, rfl, fun m hC hB => Subgroup.subset_closure ?_⟩

  have hu := GlobalTheory.MixModel.mt_unitary V m
  have hsum : C * (C'ᴴ * V.gram) + B * (V'.gram⁻¹ * (Bᴴ * V.gram)) + C' * (Cᴴ * V.gram) = 1 :=
    d.sum_eq_one_rat
  have hCm : GlobalTheory.MixModel.adj (C.map (incA D)) ⬝ GlobalTheory.MixModel.gA V ⬝ mt V m =
      GlobalTheory.MixModel.adj (C.map (incA D)) ⬝ GlobalTheory.MixModel.gA V := by
    calc GlobalTheory.MixModel.adj (C.map (incA D)) ⬝ GlobalTheory.MixModel.gA V ⬝ mt V m
        = GlobalTheory.MixModel.adj (mt V m ⬝ C.map (incA D)) ⬝ GlobalTheory.MixModel.gA V ⬝ mt V m := by rw [hC]
      _ = GlobalTheory.MixModel.adj (C.map (incA D)) ⬝ (GlobalTheory.MixModel.adj (mt V m) ⬝ (GlobalTheory.MixModel.gA V ⬝ mt V m)) := by
          rw [GlobalTheory.MixModel.adj_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · change (mt V m - 1) ⬝ C.map (incA D) = 0
    rw [Matrix.sub_mul, hC, Matrix.one_mul, sub_self]
  · rw [Matrix.map_mul]
    change GlobalTheory.MixModel.adj (C.map (incA D)) ⬝ GlobalTheory.MixModel.gA V ⬝ (mt V m - 1) = 0
    rw [Matrix.mul_sub, hCm, Matrix.mul_one, sub_self]
  · intro x hx
    refine ⟨0, ?_⟩
    rw [Matrix.mulVec_zero]
    have hx0 : (Cᴴ * V.gram) *ᵥ x = 0 := hx
    obtain ⟨u, hu⟩ : ∃ u, u = (C'ᴴ * V.gram) *ᵥ x := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = (V'.gram⁻¹ * (Bᴴ * V.gram)) *ᵥ x := ⟨_, rfl⟩
    have hx' : x = C *ᵥ u + B *ᵥ w := by
      have := congrArg (fun M => M *ᵥ x) hsum
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec (M := C),
        ← Matrix.mulVec_mulVec (M := B), ← Matrix.mulVec_mulVec (M := C'), hx0, Matrix.mulVec_zero, add_zero] at this
      rw [hu, hw]; exact this.symm
    have hxA : (fun i => incA D (x i)) = C.map (incA D) *ᵥ (incA D ∘ u) + B.map (incA D) *ᵥ (incA D ∘ w) := by
      funext i
      have hi : x i = (C *ᵥ u) i + (B *ᵥ w) i := congrFun hx' i
      have ha := RingHom.map_mulVec (incA D) C u i
      have hb := RingHom.map_mulVec (incA D) B w i
      rw [Pi.add_apply, ← ha, ← hb, hi]
      exact RingHom.map_add (incA D) _ _
    refine sub_one_mulVec_eq_zero _ (C.map (incA D)) (B.map (incA D)) _ (incA D ∘ u) (incA D ∘ w) ?_ ?_ ?_
    · exact hxA
    · exact hC
    · exact hB

end GlobalTheory.WittSect
