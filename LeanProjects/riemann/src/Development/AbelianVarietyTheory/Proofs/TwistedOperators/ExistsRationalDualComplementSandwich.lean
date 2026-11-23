import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerfectCompl

open GlobalTheory.MixModel

theorem exists_left_inv {K : Type} [Field K] {n a : ℕ} (M : Matrix (Fin n) (Fin a) K) (h : M.rank = a) :
    ∃ L : Matrix (Fin a) (Fin n) K, L * M = 1 := by
  have hk : LinearMap.ker M.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have e2 : Module.finrank K (LinearMap.range M.mulVecLin) = a := h
    rw [e2, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

variable {D : D7} (V W : HSp D)

def pr {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E) (x : WO V W) :
    Mx D a b :=
  rat Aᴴ * gA W * x * giA V * rat Bᴴ

theorem hO_emb_right {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (x : WO V W) (y : Mx D a b) : hO V W x (GlobalTheory.IsoMean.emb V W A B y) = (adj y * pr V W A B x).trace := by
  rw [hO_eq_trace]
  have e : adj (GlobalTheory.IsoMean.emb V W A B y) = rat Bᴴ * (adj y * rat Aᴴ) := by
    show adj (rat A * y * rat B) = _
    rw [adj_mul, adj_mul, ← rat_conjTranspose, ← rat_conjTranspose]
  rw [e, pr]
  rw [show giA V ⬝ (rat Bᴴ ⬝ (adj y ⬝ rat Aᴴ) ⬝ (gA W ⬝ x)) =
      (giA V ⬝ rat Bᴴ) ⬝ (adj y ⬝ (rat Aᴴ ⬝ gA W ⬝ x)) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem hO_emb_left {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (s : Mx D a b) (z : WO V W) : hO V W (GlobalTheory.IsoMean.emb V W A B s) z = (adj (pr V W A B z) * s).trace := by
  change hO V W (rat A * s * rat B) z = _
  rw [hO_eq_trace]
  have e : adj (pr V W A B z) = rat B * (giA V * (adj z * (gA W * rat A))) := by
    rw [pr]
    simp only [adj_mul, adj_giA, adj_gA, ← rat_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e]
  rw [show giA V ⬝ (adj z ⬝ (gA W ⬝ (rat A ⬝ s ⬝ rat B))) =
      (giA V ⬝ (adj z ⬝ (gA W ⬝ rat A)) ⬝ s) ⬝ rat B by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pr_emb {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E} {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s : Mx D a b) :
    pr V W P Q (GlobalTheory.IsoMean.emb V W P' Q' s) = s := by
  change rat Pᴴ ⬝ gA W ⬝ (rat P' ⬝ s ⬝ rat Q') ⬝ giA V ⬝ rat Qᴴ = s
  have e1 : rat Pᴴ ⬝ gA W ⬝ rat P' = 1 := by rw [gA, ← rat_mul, ← rat_mul, hA, rat_one]
  have e2 : rat Q' ⬝ giA V ⬝ rat Qᴴ = 1 := by rw [giA, ← rat_mul, ← rat_mul, hB, rat_one]
  calc _ = (rat Pᴴ ⬝ gA W ⬝ rat P') ⬝ s ⬝ (rat Q' ⬝ giA V ⬝ rat Qᴴ) := by simp only [Matrix.mul_assoc]
    _ = s := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]

theorem pr_sub {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (x x' : WO V W) : pr V W A B (x - x') = pr V W A B x - pr V W A B x' := by
  simp only [pr, Matrix.mul_sub, Matrix.sub_mul]

theorem pr_rat {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    {x : WO V W} (hx : x ∈ ratMx D W.rank V.rank) : pr V W A B x ∈ ratMx D a b := by
  obtain ⟨M, rfl⟩ := mem_ratMx.1 hx
  exact ⟨Aᴴ * W.gram * M * V.gram⁻¹ * Bᴴ, by show rat _ = _; simp only [pr, gA, giA, rat_mul]⟩

theorem trace_adj_mul {a b : ℕ} (y s : Mx D a b) : (adj y * s).trace = ∑ i, ∑ j, cA D (y i j) * s i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

end GlobalTheory.PerfectCompl

namespace GlobalTheory.PerfectCompl

open GlobalTheory.MixModel

variable {D : D7}

theorem trace_nondeg (z : AE D) (h : ∀ w : AE D, Algebra.trace (AF D.host.F) (AE D) (w * z) = 0) : z = 0 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨e0, he0⟩ := GlobalTheory.RatAnnih.tensor_rat (R := AF D.host.F) z fun e => ⟨0, by rw [map_zero]; exact h _⟩
  subst he0
  by_cases hne : e0 = 0
  · rw [hne, TensorProduct.tmul_zero]
  · exfalso
    have h1 := h ((1 : AF D.host.F) ⊗ₜ[D.host.F] e0⁻¹)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hne, GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul,
      ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, D.sp.cm.deg2] at h1
    have := NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F (h1.trans (map_zero _).symm)
    norm_num at this

theorem sum_single_left {a b : ℕ} (i : Fin a) (j : Fin b) (t : AE D) (s : Mx D a b) :
    ∑ i', ∑ j', cA D (Matrix.single i j t i' j') * s i' j' = cA D t * s i j := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne hc.symm, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_single_right {a b : ℕ} (i : Fin a) (j : Fin b) (u : AE D) (y : Mx D a b) :
    ∑ i', ∑ j', cA D (y i' j') * Matrix.single i j u i' j' = cA D (y i j) * u := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne hc.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

variable (V W : HSp D)

theorem symplO_emb {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E} {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s y : Mx D a b) :
    symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * ∑ i, ∑ j, cA D (y i j) * s i j) := by
  rw [symplO_eq, hO_emb_right, pr_emb V W hA hB, trace_adj_mul]

theorem symplO_emb_any {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E}
    {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s : Mx D a b) (z : WO V W) :
    symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) z =
      symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q (pr V W P' Q' z)) := by
  rw [symplO_eq, symplO_eq, hO_emb_left, hO_emb_right, pr_emb V W hA hB]

theorem emb_rat {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E)
    (γ : Matrix (Fin a) (Fin b) D.host.E) :
    GlobalTheory.IsoMean.emb V W P Q ((incA D).toAddMonoidHom.mapMatrix γ) = ratW W V (P * γ * Q) := by
  simp [GlobalTheory.IsoMean.emb, ratW, Matrix.map_mul]

end GlobalTheory.PerfectCompl

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PerfectCompl.exists_dual_complement : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (P' : Matrix (Fin W.rank) (Fin a) D.host.E) (Q' : Matrix (Fin b) (Fin V.rank) D.host.E), (∀ x : WO V W, ∃ s : Mx D a b, ∀ y : Mx D a b, symplO V W (x - GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ s : Mx D a b, (∀ y : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) = 0) → s = 0) ∧ (∀ s : Mx D a b, (∀ γ ∈ GlobalTheory.MixModel.ratMx D a b, ψ (symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q γ)) = 1) ↔ s ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ γ ∈ GlobalTheory.MixModel.ratMx D a b, (∀ s : Mx D a b, ψ (symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q γ)) = 1) → γ = 0) := by
  intro D V W a b P Q hP hQ ψ hψ
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨L, hL⟩ := GlobalTheory.PerfectCompl.exists_left_inv P hP
  obtain ⟨L', hL'⟩ := GlobalTheory.PerfectCompl.exists_left_inv Qᵀ (by rw [Matrix.rank_transpose]; exact hQ)
  have hR : Q * L'ᵀ = 1 := by
    have := congrArg Matrix.transpose hL'
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hA : Pᴴ * W.gram * (W.gram⁻¹ * Lᴴ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (GlobalTheory.MixModel.gram_isUnit_det W), ← conjTranspose_mul, hL,
      conjTranspose_one]
  have hB : (L'ᵀ)ᴴ * V.gram * V.gram⁻¹ * Qᴴ = 1 := by
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (GlobalTheory.MixModel.gram_isUnit_det V), ← conjTranspose_mul, hR, conjTranspose_one]
  clear hL hL' hR
  obtain ⟨P', Q', hA, hB⟩ : ∃ (P' : Matrix (Fin W.rank) (Fin a) D.host.E) (Q' : Matrix (Fin b) (Fin V.rank) D.host.E),
      Pᴴ * W.gram * P' = 1 ∧ Q' * V.gram⁻¹ * Qᴴ = 1 := ⟨_, _, hA, hB⟩
  refine ⟨P', Q', ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨GlobalTheory.PerfectCompl.pr V W P Q x, fun y => ?_⟩
    rw [GlobalTheory.MixModel.symplO_eq, GlobalTheory.PerfectCompl.hO_emb_right, GlobalTheory.PerfectCompl.pr_sub, GlobalTheory.PerfectCompl.pr_emb V W hA hB, sub_self,
      Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]
  · intro s hs
    ext i j
    rw [Matrix.zero_apply]
    apply GlobalTheory.PerfectCompl.trace_nondeg
    intro w
    have h := hs (Matrix.single i j (cA D (incA D D.host.xi0⁻¹ * w)))
    rw [GlobalTheory.PerfectCompl.symplO_emb V W hA hB, GlobalTheory.PerfectCompl.sum_single_left, cA_cA] at h
    rw [← h]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul]
  · intro s
    constructor
    · intro h
      have hx : GlobalTheory.IsoMean.emb V W P' Q' s ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 fun z hz => ?_
        rw [GlobalTheory.PerfectCompl.symplO_emb_any V W hA hB]
        exact h _ (GlobalTheory.PerfectCompl.pr_rat V W _ _ hz)
      have := GlobalTheory.PerfectCompl.pr_rat V W P Q hx
      rwa [GlobalTheory.PerfectCompl.pr_emb V W hA hB] at this
    · rintro ⟨s0, rfl⟩ γ ⟨γ0, rfl⟩
      rw [GlobalTheory.PerfectCompl.emb_rat, GlobalTheory.PerfectCompl.emb_rat]
      obtain ⟨c, hc⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D V W (P' * s0 * Q') (P * γ0 * Q)
      rw [hc]
      exact hψ.1.2.2.1 c
  · rintro γ ⟨g, rfl⟩ h
    by_contra hne
    have hex : ∃ i j, g i j ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      ext i j
      show incA D (g i j) = 0
      rw [hall i j, map_zero]
    obtain ⟨i, j, hij⟩ := hex
    obtain ⟨x0, hx0⟩ := hψ.1.2.2.2
    apply hx0
    have hc : star (g i j) ≠ 0 := star_ne_zero.2 hij
    have h1 := h (Matrix.single i j
      (x0 • incA D (D.host.xi0⁻¹ * (star (g i j))⁻¹ * algebraMap D.host.F D.host.E (1 / 2))))
    rw [GlobalTheory.PerfectCompl.symplO_emb V W hA hB, GlobalTheory.PerfectCompl.sum_single_right] at h1
    have e0 : ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b) g) i j = incA D (g i j) := rfl
    rw [e0] at h1
    have e3 : incA D D.host.xi0 * (cA D (incA D (g i j)) *
        x0 • incA D (D.host.xi0⁻¹ * (star (g i j))⁻¹ * algebraMap D.host.F D.host.E (1 / 2))) =
        x0 • incA D (algebraMap D.host.F D.host.E (1 / 2)) := by
      rw [GlobalTheory.DualPairCheck.cA_incA, mul_smul_comm, mul_smul_comm, ← map_mul, ← map_mul]
      congr 2
      field_simp [GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D, hc]
    have t : Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E (1 / 2))) = 1 := by
      have := GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul (F := D.host.F) (E := D.host.E) (AF D.host.F)
        (algebraMap D.host.F D.host.E (1 / 2))
      rw [Algebra.trace_algebraMap, D.sp.cm.deg2] at this
      refine this.trans ?_
      norm_num
    rw [e3, map_smul, t, smul_eq_mul, mul_one] at h1
    exact h1
