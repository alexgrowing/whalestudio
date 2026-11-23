import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanChangesByScalarOfTrivialActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SourceUnip

open GlobalTheory.MixModel GlobalTheory.UnipMean

variable {D : D7} {V V' W : HSp D} {r : ℕ}

theorem corner_alg {R a b c : Type} [CommRing R] [Fintype b] [Fintype c] {x1 : Matrix a b R} {m p q : Matrix b b R}
    {C' : Matrix b c R} {B : Matrix c b R} (hq : q = C' * B) (hp : x1 * p = 0)
    (r3 : m = p * m + m * q - p * m * q) : x1 * m = x1 * m * C' * B := by
  have a1 : x1 * (p * m) = 0 := by rw [← Matrix.mul_assoc, hp, Matrix.zero_mul]
  have a2 : x1 * (p * m * q) = 0 := by rw [← Matrix.mul_assoc, a1, Matrix.zero_mul]
  calc x1 * m = x1 * (p * m + m * q - p * m * q) := by rw [← r3]
    _ = x1 * (p * m) + x1 * (m * q) - x1 * (p * m * q) := by rw [Matrix.mul_sub, Matrix.mul_add]
    _ = x1 * m * C' * B := by rw [a1, a2, zero_add, sub_zero, hq]; simp only [Matrix.mul_assoc]

theorem hO_iso (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : WO V W) (y : Mx D W.rank r) :
    hO V W x (y ⬝ rat (Cᴴ * V.gram)) = (adj y ⬝ (gA W ⬝ (x ⬝ rat C))).trace := by
  rw [hO_eq_trace, rat_mul, rat_conjTranspose, adj_mul, adj_mul, adj_adj, ← gA, adj_gA]
  simp only [Matrix.mul_assoc, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplO_iso_of (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : WO V W} (hx : x ⬝ rat C = 0)
    (y : Mx D W.rank r) : symplO V W x (y ⬝ rat (Cᴴ * V.gram)) = 0 := by
  rw [symplO_eq, hO_iso, hx, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]

theorem mulC_eq_zero_of_symplO (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : WO V W}
    (h : ∀ y : Mx D W.rank r, symplO V W x (y ⬝ rat (Cᴴ * V.gram)) = 0) : x ⬝ rat C = 0 := by
  obtain ⟨u, hu⟩ : ∃ u : Mx D W.rank r, u = gA W ⬝ (x ⬝ rat C) := ⟨_, rfl⟩
  have hu0 : u = 0 := by
    ext i j
    have key : ∀ w : AE D, Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * u i j * w) = 0 := fun w => by
      have := h (adj (Matrix.single j i w : Mx D r W.rank))
      rw [symplO_eq, hO_iso, adj_adj, ← hu, trace_single_mul', ← mul_assoc] at this
      exact this
    have hz := eq_zero_of_trace_mul (F := D.host.F) (E := D.host.E) (R := AF D.host.F) _ key
    have hξ : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
    have := congrArg (incA D D.host.xi0⁻¹ * ·) hz
    simpa [← mul_assoc, hξ] using this
  have e : giA W ⬝ u = giA W ⬝ (gA W ⬝ (x ⬝ rat C)) := by rw [hu]
  rw [giA_gA_cancel, hu0, Matrix.mul_zero] at e
  exact e.symm

theorem iso_mulC {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) (y : Mx D W.rank r) :
    y ⬝ rat (Cᴴ * V.gram) ⬝ rat C = 0 := by
  have h : Cᴴ * V.gram * C = 0 := hC.2.2
  rw [Matrix.mul_assoc, ← rat_mul, h, rat_zero, Matrix.mul_zero]

theorem mid_mulC {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B) (x : WO V' W) :
    x ⬝ rat (V'.gram⁻¹ * Bᴴ * V.gram) ⬝ rat C = 0 := by
  have h0 : Cᴴ * V.gram * B = 0 := hs.orth
  have h1 : Bᴴ * (V.gram * C) = 0 := by
    have := congrArg Matrix.conjTranspose h0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      Matrix.conjTranspose_zero] at this
  rw [Matrix.mul_assoc, ← rat_mul]
  simp only [Matrix.mul_assoc, h1, Matrix.mul_zero, rat_zero]

section Gen

variable {C : Matrix (Fin V.rank) (Fin r) D.host.E} {C' : Matrix (Fin V.rank) (Fin r) D.host.E}
  {L B₀ : Matrix (Fin r) (Fin V.rank) D.host.E}

theorem gen_fix_iso (h : IsDualPair V C C' L B₀) {g : GA D V} (g2 : rat B₀ ⬝ (mt V g - 1) = 0)
    (y : Mx D W.rank r) : actO V W g 1 (y ⬝ rat (Cᴴ * V.gram)) = y ⬝ rat (Cᴴ * V.gram) := by
  have e1 : rat B₀ ⬝ mt V g = rat B₀ := by
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at g2
  have e2 : rat B₀ ⬝ mt V g⁻¹ = rat B₀ := by
    rw [← e1, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, e1]
  rw [actO_eq, mt_one, Matrix.one_mul, ← h.hB, Matrix.mul_assoc, e2]

theorem gen_move (h : IsDualPair V C C' L B₀) {g : GA D V} (g1 : (mt V g - 1) ⬝ rat C = 0)
    (r3 : mt V g - 1 = rat (C * L) * (mt V g - 1) + (mt V g - 1) * rat (C' * B₀) -
      rat (C * L) * (mt V g - 1) * rat (C' * B₀))
    {x : WO V W} (hx : x ⬝ rat C = 0) :
    ∃ y : Mx D W.rank r, actO V W g 1 x = x + y ⬝ rat (Cᴴ * V.gram) := by
  have e1 : mt V g ⬝ rat C = rat C := by
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at g1
  have e2 : mt V g⁻¹ ⬝ rat C = rat C := by
    rw [← e1, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul, e1]
  obtain ⟨x1, hx1⟩ : ∃ x1 : WO V W, x1 = x ⬝ mt V g⁻¹ := ⟨_, rfl⟩
  have hx1C : x1 ⬝ rat C = 0 := by rw [hx1, Matrix.mul_assoc, e2, hx]
  have hx1p : x1 ⬝ rat (C * L) = 0 := by rw [rat_mul, ← Matrix.mul_assoc, hx1C, Matrix.zero_mul]
  have hx1g : x1 ⬝ mt V g = x := by rw [hx1, Matrix.mul_assoc, mt_inv_mul, Matrix.mul_one]
  have k : x1 ⬝ (mt V g - 1) = x1 ⬝ (mt V g - 1) ⬝ rat C' ⬝ rat B₀ :=
    corner_alg (rat_mul C' B₀) hx1p r3
  refine ⟨-(x1 ⬝ (mt V g - 1) ⬝ rat C'), ?_⟩
  rw [actO_eq, mt_one, Matrix.one_mul, ← h.hB, Matrix.neg_mul, ← k, Matrix.mul_sub, hx1g, Matrix.mul_one, ← hx1]
  abel

end Gen

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem weilRepresentation_source_mul (g g' : GA D V) (f : WO V W → ℂ) : ω (g * g', 1) f = ω (g, 1) (ω (g', 1) f) := by
  have : (g * g', (1 : GA D W)) = (g, 1) * (g', 1) := by simp
  rw [this, map_mul]; rfl

theorem weilRepresentation_source_one (f : WO V W → ℂ) : ω (1, 1) f = f := by
  have : ((1 : GA D V), (1 : GA D W)) = 1 := rfl
  rw [this, map_one]; rfl

theorem unit_product_rescale_disjoint_finsets {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B) (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) {g : GA D V} (hg : g ∈ NI V C) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f, IsThetaFunO ψ V W f →
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (g, 1) f) = c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  have hC := hs.frame
  obtain ⟨C', L, B₀, h⟩ := exists_dualPair hC
  have hP : (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).rank = W.rank := by
    rw [Matrix.rank_one, Fintype.card_fin]
  have hQ : (Cᴴ * V.gram).rank = r := by
    refine le_antisymm ?_ ?_
    · simpa using Matrix.rank_le_card_height (Cᴴ * V.gram)
    · have := Matrix.rank_mul_le_left (Cᴴ * V.gram) C'
      rw [← h.hB] at this ⊢
      rwa [h.BC', Matrix.rank_one, Fintype.card_fin] at this
  have eI : ∀ y : Mx D W.rank r, (HMul.hMul (HMul.hMul ((1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
      (y : Matrix (Fin W.rank) (Fin r) (AE D))) ((Cᴴ * V.gram).map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) =
      y ⬝ rat (Cᴴ * V.gram) := fun y => by
    show rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ y ⬝ rat (Cᴴ * V.gram) = _
    rw [rat_one, Matrix.one_mul]
  unfold NI at hg
  refine Subgroup.closure_induction (p := fun g _ => ∃ c : ℂ, c ≠ 0 ∧ ∀ f, IsThetaFunO ψ V W f →
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (g, 1) f) = c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨g1, g2, g3⟩
    have g1' : (mt V g - 1) ⬝ rat C = 0 := g1
    obtain ⟨r1, r2, r3⟩ := gen_relations h (x := mt V g - 1) g1' (by rw [h.hB]; exact g2)
      (fun v hv => g3 v (by rw [← h.hB']; exact hv))
    have g2' : rat B₀ ⬝ (mt V g - 1) = 0 := by rw [h.hB]; exact g2
    obtain ⟨c, hc⟩ := GlobalTheory.T.isotropicMean_changes_by_scalar_of_trivial_action D V W W.rank r 1 (Cᴴ * V.gram) hP hQ
      (fun y y' => by rw [eI, eI]; exact symplO_iso_of C (iso_mulC hC y) y') ψ χS χT ω hω μ 𝓨 hcov g 1
      (fun y => by rw [eI]; exact gen_fix_iso h g2' y)
      (fun x hx => by
        obtain ⟨y, hy⟩ := gen_move h g1' r3 (mulC_eq_zero_of_symplO C fun y => by rw [← eI]; exact hx y)
        exact ⟨y, by rw [eI]; exact hy⟩)
    refine ⟨c, Circle.coe_ne_zero c, fun f hf => ?_⟩
    funext x'
    have hm := mid_mulC hs (W := W) x'
    have hh : ∀ (F : WO V W → ℂ) (y : Mx D W.rank r),
        heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') F
          (HMul.hMul (HMul.hMul ((1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
            (y : Matrix (Fin W.rank) (Fin r) (AE D))) ((Cᴴ * V.gram).map (incA D)) :
            Matrix (Fin W.rank) (Fin V.rank) (AE D)) =
          F (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') := fun F y => by
      rw [eI]
      show ψ (symplOH V W _ _) * F _ = _
      have h0 : symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') (y ⬝ rat (Cᴴ * V.gram)) = 0 := symplO_iso_of C hm y
      rw [symplOH_skew]
      unfold symplOH
      rw [h0, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
      rfl
    have := hc f hf (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') (fun y => by rw [eI]; exact symplO_iso_of C hm y)
    simp only [hh] at this
    show ∫ y in 𝓨, ω (g, 1) f _ ∂μ = (c : ℂ) • ∫ y in 𝓨, f _ ∂μ
    rw [this, smul_eq_mul]
  · exact ⟨1, one_ne_zero, fun f _ => by rw [weilRepresentation_source_one, one_smul]⟩
  · rintro a b - - ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c * d, mul_ne_zero hc hd, fun f hf => by
      rw [weilRepresentation_source_mul, ha _ (hω.om_pres _ _ hf), hb f hf, smul_smul]⟩
  · rintro a - ⟨c, hc, ha⟩
    refine ⟨c⁻¹, inv_ne_zero hc, fun f hf => ?_⟩
    have := ha _ (hω.om_pres (a⁻¹, 1) f hf)
    rw [← weilRepresentation_source_mul, mul_inv_cancel, weilRepresentation_source_one] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Main

end GlobalTheory.SourceUnip

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem GlobalTheory.SourceUnip.scal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ g : GA D V, g ∈ NI V C → ∃ c : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (g, 1) f) = c • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcov g hg
  obtain ⟨c, -, hc⟩ := GlobalTheory.SourceUnip.unit_product_rescale_disjoint_finsets hs hω hcov hg
  exact ⟨c, hc⟩

end
