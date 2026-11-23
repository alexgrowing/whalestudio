import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SubquotientSizeInequality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSizeEqLeast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAndNcardLeProdOfLevels
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSubspaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRealSubmoduleBlockFinrankLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubmoduleSkewBlockFinrankLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarProjectionInfOrthogonalEqOfMemOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFramesSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoweringDifferenceOfIsometries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFirstBlocksByLayers
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerAddInnerEqZeroSpan

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open GlobalTheory.IndefiniteRowSideFullHecke.SubquotientSizeInequality
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.NearCount

abbrev Hn (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

def opM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Hn n →L[ℂ] Hn n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

theorem opM_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Hn n) :
    opM M u = WithLp.toLp 2 (M *ᵥ u.ofLp) := rfl

theorem opM_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) : opM (M - N) = opM M - opM N := by
  simp [opM]

theorem norm_opM_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ‖opM M‖ ≤ Real.sqrt (hs M) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun u => ?_
  rw [opM_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (by unfold hs; positivity)]
  apply Real.sqrt_le_sqrt
  unfold hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(M *ᵥ u.ofLp) i‖ ≤ ∑ j, ‖M i j‖ * ‖u j‖ := by
    unfold Matrix.mulVec dotProduct
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

theorem inner_opM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u z : Hn n) :
    ⟪u, opM M z⟫_ℂ = star u.ofLp ⬝ᵥ (M *ᵥ z.ofLp) := by
  rw [opM_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem norm_opJ {n : ℕ} (ε : Fin n → Bool) (u : Hn n) : ‖opM (Jm ε) u‖ = ‖u‖ := by
  rw [opM_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Jm, Matrix.mulVec_diagonal, norm_mul]
  split_ifs <;> simp

theorem inner_opJ {n : ℕ} (ε : Fin n → Bool) (u z : Hn n) :
    ⟪opM (Jm ε) u, z⟫_ℂ = ⟪u, opM (Jm ε) z⟫_ℂ := by
  rw [opM_apply, opM_apply, PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Jm, Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem finrank_piece {n : ℕ} {A A' : Submodule ℂ (Hn n)} (h : A' ≤ A) :
    Module.finrank ℂ ↥(A ⊓ A'ᗮ) = Module.finrank ℂ A - Module.finrank ℂ A' := by
  have := Submodule.finrank_add_inf_finrank_orthogonal h
  rw [inf_comm] at this
  omega

variable (I : AutInst) (x : I.GA)

abbrev pt (w : InfinitePlace I.E) (y : Fin I.n → I.E) : Hn I.n := ptAt (bas I) (frm I x) w y

abbrev sp (w : InfinitePlace I.E) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Submodule ℂ (Hn I.n) :=
  spanAt (bas I) (frm I x) w S

def op (w : InfinitePlace I.E) (φ : Matrix (Fin I.n) (Fin I.n) I.E) : Hn I.n →L[ℂ] Hn I.n :=
  opM ((frm I x w)⁻¹ * φ.map w.embedding * frm I x w)

def sg (w : InfinitePlace I.E) : Hn I.n →L[ℂ] Hn I.n := opM (Jm (I.ε (w.comap (algebraMap I.F I.E))))

abbrev hf (y z : Fin I.n → I.E) : I.E := Formalism.UG.hform (starRingEnd I.E) I.J y z

theorem op_sub (w : InfinitePlace I.E) (φ ψ : Matrix (Fin I.n) (Fin I.n) I.E) :
    op I x w (φ - ψ) = op I x w φ - op I x w ψ := by
  unfold op
  rw [← opM_sub, Matrix.map_sub _ (map_sub _), Matrix.mul_sub, Matrix.sub_mul]

theorem frm_pt (w : InfinitePlace I.E) (y : Fin I.n → I.E) :
    frm I x w *ᵥ (pt I x w y).ofLp = fun i => w.embedding (y i) := by
  show frm I x w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = _
  unfold Formalism.HermitianLatticesTheory.fcoord
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (FrameMajorant.frm_unit I x w), Matrix.one_mulVec]
  funext i
  simp [Formalism.HermitianLatticesTheory.vecAt]

theorem op_pt (w : InfinitePlace I.E) (φ : Matrix (Fin I.n) (Fin I.n) I.E) (y : Fin I.n → I.E) :
    op I x w φ (pt I x w y) = pt I x w (φ *ᵥ y) := by
  unfold op
  rw [opM_apply, ← Matrix.mulVec_mulVec, frm_pt, ← Matrix.mulVec_mulVec]
  show _ = WithLp.toLp 2 ((frm I x w)⁻¹ *ᵥ Formalism.HermitianLatticesTheory.vecAt (bas I) w (φ *ᵥ y))
  congr 2
  funext i
  simp [Formalism.HermitianLatticesTheory.vecAt, Matrix.mulVec, dotProduct]

theorem inner_pt (w : InfinitePlace I.E) (y z : Fin I.n → I.E) :
    ⟪pt I x w y, sg I w (pt I x w z)⟫_ℂ = w.embedding (hf I y z) := by
  have hc := I.cm.cmUnram.2.1
  have h1 : w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z) =
      star (fun i => w.embedding (y i)) ⬝ᵥ (I.J.map w.embedding *ᵥ fun i => w.embedding (z i)) := by
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Finset.mul_sum, starRingEnd_apply, hc, mul_assoc]
  rw [sg, inner_opM, hf, h1, ← frm_pt I x w y, ← frm_pt I x w z, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ((FrameMajorant.frames_give_majorants I x).2.2.2.2 w).2.1]

theorem finrank_sp (w : InfinitePlace I.E) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Module.finrank ℂ (sp I x w S) = rkK S := by
  have := I.cm.cmUnram.1
  have h : sp I x w S = (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w '' (S : Set _))).map
      ((WithLp.linearEquiv 2 ℂ (Fin I.n → ℂ)).symm : (Fin I.n → ℂ) →ₗ[ℂ] Hn I.n) := by
    rw [Submodule.map_span, Set.image_image]; rfl
  rw [h, LinearEquiv.finrank_map_eq]
  exact PlaceDecomposition.finrank_span_complex _ _ (FrameMajorant.frm_unit I x) S w

theorem sp_mono (w : InfinitePlace I.E) {S S' : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : S ≤ S') :
    sp I x w S ≤ sp I x w S' := Submodule.span_mono (Set.image_mono h)

theorem op_mem (w : InfinitePlace I.E) (φ : Matrix (Fin I.n) (Fin I.n) I.E)
    {A B : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : ∀ y ∈ A, φ *ᵥ y ∈ B) :
    ∀ u ∈ sp I x w A, op I x w φ u ∈ sp I x w B := by
  have : sp I x w A ≤ (sp I x w B).comap (op I x w φ : Hn I.n →ₗ[ℂ] Hn I.n) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    show op I x w φ (pt I x w y) ∈ sp I x w B
    rw [op_pt]
    exact Submodule.subset_span ⟨_, h y hy, rfl⟩
  exact fun u hu => this hu

theorem span_inner {n : ℕ} (L M : Hn n →L[ℂ] Hn n) (s t : Set (Hn n))
    (h : ∀ u ∈ s, ∀ z ∈ t, ⟪L u, z⟫_ℂ + ⟪u, M z⟫_ℂ = 0) :
    ∀ u ∈ Submodule.span ℂ s, ∀ z ∈ Submodule.span ℂ t, ⟪L u, z⟫_ℂ + ⟪u, M z⟫_ℂ = 0 := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.InnerSumZeroSpan.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.InnerSumZeroSpan.main
  | exact @_root_.GlobalTheory.InnerSumZeroSpan.main
  | exact _root_.GlobalTheory.InnerSumZeroSpan.main
  | (apply _root_.GlobalTheory.InnerSumZeroSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InnerSumZeroSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InnerSumZeroSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InnerSumZeroSpan.main ..)

theorem sp_orth (w : InfinitePlace I.E) {A B : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (h : ∀ s ∈ A, ∀ y ∈ B, hf I s y = 0) :
    ∀ u ∈ sp I x w B, ∀ z ∈ sp I x w A, ⟪z, sg I w u⟫_ℂ = 0 := by
  intro u hu z hz
  have := span_inner 0 (sg I w) _ _ (by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [inner_pt, h s hs y hy]; simp) z hz u hu
  simpa using this

theorem sp_skew (w : InfinitePlace I.E) (φ : Matrix (Fin I.n) (Fin I.n) I.E)
    {A : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (h : ∀ s ∈ A, ∀ y ∈ A, hf I (φ *ᵥ s) y + hf I s (φ *ᵥ y) = 0) :
    ∀ u ∈ sp I x w A, ∀ z ∈ sp I x w A,
      ⟪(sg I w ∘L op I x w φ) u, z⟫_ℂ + ⟪u, (sg I w ∘L op I x w φ) z⟫_ℂ = 0 := by
  refine span_inner _ _ _ _ ?_
  rintro _ ⟨s, hs, rfl⟩ _ ⟨y, hy, rfl⟩
  simp only [ContinuousLinearMap.comp_apply]
  rw [op_pt, op_pt, sg, inner_opJ, ← sg, inner_pt, inner_pt, ← map_add, h s hs y hy, map_zero]

def rho (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (p : ℕ) : ℕ := rkK (G (p + 1)) - rkK (G p)

def dimB (a : ℕ) (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (q p : ℕ) : ℕ :=
  if q + p = 2 * a then rho I G p ^ 2 else 2 * rho I G (2 * a - q) * rho I G p

def lowSet (a : ℕ) (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (de : ℝ) :
    Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {γ | Formalism.UG.cT (starRingEnd I.E) γ * I.J * γ = I.J ∧
    (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ - 1) *ᵥ y ∈ G p) ∧ ∀ w, ‖op I x w (γ - 1)‖ ≤ de}

theorem block_count (a : ℕ) (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : G 0 = ⊥)
    (hmono : Monotone G) (hsat : ∀ p, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G p))
    (hperp : ∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, hf I s y = 0)
    (hrk : ∀ p ≤ 2 * a + 1, rkK (G (2 * a + 1 - p)) + rkK (G p) = I.n)
    (q p : ℕ) (hqp : q < p) (hle : q + p ≤ 2 * a) (lo hi : ℝ) (hlo0 : 0 < lo) (hhi0 : 0 < hi)
    (hlo : ∀ N, G q < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N (G q))
    (hhi : G (p + 1) ≠ ⊥ → largestSize (bas I) (frm I x) (G (p + 1)) ≤ hi)
    (de : ℝ) (hde : 0 < de) (T : Finset (Matrix (Fin I.n) (Fin I.n) I.E))
    (hT : (↑T : Set _) ⊆ lowSet I x a G de)
    (hlev : ∀ γ ∈ T, ∀ γ' ∈ T, ∀ q' p' : ℕ, q' < p' → q' + p' ≤ 2 * a → p' - q' < p - q →
      ∀ y ∈ G (p' + 1), (γ - γ') *ᵥ y ∈ G q')
    (hsep : ∀ γ ∈ T, ∀ γ' ∈ T, (∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G q) → γ = γ') :
    (T.card : ℝ) ≤ (1 + 2 * (2 * de) / (lo / hi)) ^ (dimB I a G q p * I.f) := by
  have := I.cm.cmUnram.1
  rcases T.eq_empty_or_nonempty with rfl | ⟨γ₀, hγ₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hadj := fun γ (hγ : γ ∈ T) γ' (hγ' : γ' ∈ T) =>
    GlobalTheory.lowering_difference_of_isometries I.E (𝓞 I.E) I.n I.J I.J_herm a G h0 hmono hperp γ γ' (hT hγ).1 (hT hγ').1
      (hT hγ).2.1 (hT hγ').2.1 (p - q) (by omega) (hlev γ hγ γ' hγ')
  have horth : ∀ i k, i + k ≤ 2 * a + 1 → ∀ s ∈ G i, ∀ y ∈ G k, hf I s y = 0 := fun i k h s hs y hy =>
    ((hperp i (by omega) y).1 (hmono (by omega) hy)).2 s hs
  let E := fun w => sp I x w (G (p + 1)) ⊓ (sp I x w (G p))ᗮ
  let E' := fun w => sp I x w (G (2 * a - q + 1)) ⊓ (sp I x w (G (2 * a - q)))ᗮ
  have hE : ∀ w r, Module.finrank ℂ ↥(sp I x w (G (r + 1)) ⊓ (sp I x w (G r))ᗮ) = rho I G r := by
    intro w r
    rw [finrank_piece (sp_mono I x w (hmono (Nat.le_succ r))), finrank_sp, finrank_sp, rho]
  let blk := fun w (φ : Matrix (Fin I.n) (Fin I.n) I.E) =>
    (E' w).starProjection ∘L (sg I w ∘L op I x w φ) ∘L (E w).starProjection
  have hsub : ∀ w φ ψ, blk w φ - blk w ψ = blk w (φ - ψ) := by
    intro w φ ψ
    simp only [blk, op_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  have hU : ∀ w, ∃ U : Submodule ℝ (Hn I.n →L[ℂ] Hn I.n), Module.finrank ℝ U ≤ dimB I a G q p ∧
      ∀ γ ∈ T, blk w (γ - γ₀) ∈ U := by
    intro w
    by_cases h : q + p = 2 * a
    · obtain ⟨U, h1, h2⟩ := GlobalTheory.exists_submodule_skew_block_finrank_le I.n (E w)
      refine ⟨U, by rw [dimB, if_pos h, ← hE w p]; exact h1, fun γ hγ => ?_⟩
      have hp : 2 * a - q = p := by omega
      simp only [blk, E', hp]
      refine h2 _ fun u hu z hz => sp_skew I x w _ (A := G (p + 1)) ?_ u hu.1 z hz.1
      exact fun s hs y hy => (hadj γ hγ γ₀ hγ₀).2 p p (by omega) (by omega) (by omega) s hs y hy
    · obtain ⟨U, h1, h2⟩ := GlobalTheory.exists_real_submodule_block_finrank_le I.n (E w) (E' w)
      exact ⟨U, by rw [dimB, if_neg h, ← hE w p, ← hE w (2 * a - q)]; exact h1, fun γ _ => h2 _⟩
  choose U hU1 hU2 using hU
  have hnorm : ∀ w φ, ‖blk w φ‖ ≤ ‖op I x w φ‖ := by
    intro w φ
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    simp only [blk, ContinuousLinearMap.comp_apply]
    refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
    rw [sg, norm_opJ]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ _) (norm_nonneg _))
  have hf' : Fintype.card (InfinitePlace I.E) = I.f := (FrameMajorant.frames_give_majorants I x).2.1
  have : FiniteDimensional ℝ (Hn I.n →L[ℂ] Hn I.n) := Module.Finite.trans ℂ _
  rw [← hf']
  refine GlobalTheory.packing_geometric_mean_subspaces (InfinitePlace I.E) (Hn I.n →L[ℂ] Hn I.n) U _ hU1 _ T
    (fun γ w => blk w (γ - γ₀)) (lo / hi) (2 * de) (div_pos hlo0 hhi0) (by positivity) ?_ ?_
  · intro γ hγ w
    refine ⟨hU2 w γ hγ, (hnorm w _).trans ?_⟩
    have : γ - γ₀ = (γ - 1) - (γ₀ - 1) := by abel
    rw [this, op_sub]
    have h1 := (hT hγ).2.2 w
    have h2 := (hT hγ₀).2.2 w
    exact (norm_sub_le _ _).trans (by linarith)
  · intro γ hγ γ' hγ' hne
    have hex : ∃ y ∈ G (p + 1), (γ - γ') *ᵥ y ∉ G q := by
      by_contra hcon
      push Not at hcon
      exact hne (hsep γ hγ γ' hγ' hcon)
    have hD := (hadj γ hγ γ' hγ').1
    have hA : ∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G (q + 1) := fun y hy => by
      have := hD (p + 1) (by omega) y hy
      rwa [show p + 1 - (p - q) = q + 1 by omega] at this
    have hA' : ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G q := fun y hy => by
      have := hD p (by omega) y hy
      rwa [show p - (p - q) = q by omega] at this
    have hFG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1
    have hne0 : G (p + 1) ≠ ⊥ := by
      obtain ⟨y, hy, hy'⟩ := hex
      intro h
      rw [h, Submodule.mem_bot] at hy
      exact hy' (by rw [hy, Matrix.mulVec_zero]; exact zero_mem _)
    simp only [hsub, sub_sub_sub_cancel_right]
    refine GlobalTheory.SizeSubToQuot.size_ineq_sub_to_quot I.E I.n (frm I x) (FrameMajorant.frm_unit I x) (γ - γ') (G (p + 1)) (lamX I x)
      (G q) (Submodule.FG.of_le hFG (hsat _).1) hFG (hsat q) (fun y hy => (hsat _).1 (hA y hy)) hex lo hi hlo0
      hlo (hhi hne0) (fun w => ‖blk w (γ - γ')‖) (fun w => norm_nonneg _) fun w u hu => ?_
    refine GlobalTheory.infDist_le_norm_block_mul I.n (sp I x w (G (p + 1))) (sp I x w (G p)) (sp I x w (G (q + 1)))
      (sp I x w (G q)) (sp I x w (G (2 * a - q + 1))) (sp I x w (G (2 * a - q))) (sg I w)
      (op I x w (γ - γ')) (norm_opJ _) (sp_mono I x w (hmono (Nat.le_succ _)))
      (sp_mono I x w (hmono (Nat.le_succ _))) (sp_orth I x w (horth _ _ (by omega)))
      (sp_orth I x w (horth _ _ (by omega))) ?_ (op_mem I x w _ hA) (op_mem I x w _ hA') u hu
    rw [finrank_sp, finrank_sp, show 2 * a - q + 1 = 2 * a + 1 - q by omega]
    exact hrk q (by omega)

theorem core_count (a : ℕ) (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : G 0 = ⊥)
    (hmono : Monotone G) (hsat : ∀ p, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G p))
    (hperp : ∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, hf I s y = 0)
    (hrk : ∀ p ≤ 2 * a + 1, rkK (G (2 * a + 1 - p)) + rkK (G p) = I.n)
    (htop : G (2 * a + 1) = lamX I x) (t : ℕ → ℝ) (ht : ∀ p, 0 < t p)
    (hlo : ∀ q < a, ∀ N, G q < N → N ≤ lamX I x → t q ≤ sizeQ (bas I) (frm I x) N (G q))
    (hhi : ∀ p ≤ 2 * a, G (p + 1) ≠ ⊥ → largestSize (bas I) (frm I x) (G (p + 1)) ≤ t p)
    (de : ℝ) (hde : 0 < de) :
    (lowSet I x a G de).Finite ∧ (((lowSet I x a G de).ncard : ℕ) : ℝ) ≤
      ∏ b ∈ ((Finset.range a) ×ˢ (Finset.range (2 * a + 1))).filter
        (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a),
        (1 + 2 * (2 * de) / (t b.1 / t b.2)) ^ (dimB I a G b.1 b.2 * I.f) := by
  have hmem : ∀ q p : ℕ, q < p → q + p ≤ 2 * a → (q, p) ∈ ((Finset.range a) ×ˢ
      (Finset.range (2 * a + 1))).filter (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a) := by
    intro q p h1 h2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  refine GlobalTheory.finite_and_ncard_le_prod_of_levels _ (ℕ × ℕ) _ _ (fun b => b.2 - b.1)
    (fun b γ γ' => ∀ y ∈ G (b.2 + 1), (γ - γ') *ᵥ y ∈ G b.1) _ ?_ ?_ ?_
  · intro b
    refine ⟨fun γ y _ => by simp, fun {γ γ'} h y hy => ?_, fun {γ γ' γ''} h h' y hy => ?_⟩
    · rw [← neg_sub, Matrix.neg_mulVec]; exact neg_mem (h y hy)
    · rw [← sub_add_sub_cancel γ γ' γ'', Matrix.add_mulVec]; exact add_mem (h y hy) (h' y hy)
  · intro γ hγ γ' hγ' h
    have hD := (GlobalTheory.lowering_difference_of_isometries I.E (𝓞 I.E) I.n I.J I.J_herm a G h0 hmono hperp γ γ' hγ.1 hγ'.1
      hγ.2.1 hγ'.2.1 (2 * a + 1) (by omega) (fun q p h1 h2 _ => h (q, p) (hmem q p h1 h2))).1
      (2 * a + 1) le_rfl
    rw [Nat.sub_self, h0, htop] at hD
    have hspan := (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1
    have : Matrix.toLin' (γ - γ') = 0 := by
      refine LinearMap.ext_on hspan fun y hy => ?_
      simpa [Matrix.sub_mulVec] using hD y hy
    rw [← sub_eq_zero]
    exact Matrix.toLin'.injective (by rw [this, map_zero])
  · rintro ⟨q, p⟩ hb T hT hlev hsep
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb
    exact block_count I x a G h0 hmono hsat hperp hrk q p hb.2.1 hb.2.2 _ _ (ht q) (ht p)
      (hlo q hb.1.1) (hhi p (by omega)) de hde T hT
      (fun γ hγ γ' hγ' q' p' h1 h2 h3 => hlev γ hγ γ' hγ' (q', p') (hmem q' p' h1 h2) h3) hsep

theorem hf_dot (y z : Fin I.n → I.E) : hf I y z = (starRingEnd I.E ∘ y) ⬝ᵥ (I.J *ᵥ z) := by
  simp only [hf, Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]

theorem mem_perpIn (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, hf I s y = 0 := by
  refine ⟨fun hy => ?_, fun h => Submodule.subset_span h⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => by simp [hf, Formalism.UG.hform]⟩
  | add y z _ _ h1 h2 =>
    refine ⟨add_mem h1.1 h2.1, fun s hs => ?_⟩
    have e1 := h1.2 s hs
    have e2 := h2.2 s hs
    rw [hf_dot] at *
    rw [Matrix.mulVec_add, dotProduct_add, e1, e2, add_zero]
  | smul c y _ h1 =>
    refine ⟨Submodule.smul_mem _ _ h1.1, fun s hs => ?_⟩
    have e1 := h1.2 s hs
    rw [hf_dot] at *
    rw [Matrix.mulVec_smul, dotProduct_smul, e1, smul_zero]

theorem exists_chain (a : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (h : HasType I x j τ) :
    ∃ (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (t : ℕ → ℝ), G 0 = ⊥ ∧ Monotone G ∧
      (∀ p, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G p)) ∧
      (∀ p ≤ 2 * a + 1, G (2 * a + 1 - p) = perpIn I x (G p)) ∧
      (∀ p ≤ 2 * a, G (p + 1) = stepLe I x (t p)) ∧
      (∀ p ≤ 2 * a, G p = stepLt I x (if p = a then 1 / 2 else t p)) ∧ (∀ p, 0 < t p) ∧
      (∀ i : Fin a, t i = τ i ∧ t (2 * a - i) = (τ i)⁻¹ ∧ rkK (G (i + 1)) = rkK (G i) + j i) ∧ t a = 2 := by
  obtain ⟨S, hF, hj⟩ := h
  have hF' := ((GlobalTheory.PointFlag.flag_spec I x).2.2 a S τ hF).1
  obtain ⟨hS0, hSm, hSl, -, hSi, -⟩ := hF
  have hst := GlobalTheory.CountSteps.steps I x
  obtain ⟨-, -, hd, hp⟩ := GlobalTheory.Count.PerpStep.main I x
  have hsat : ∀ i, IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S i) := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hSl]; exact (hst _ (by norm_num)).2.1
    | cast i => rw [(hF' i).1]; exact (hst _ (hSi i).1).2.1
  let S' : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E) := fun p => S ⟨min p a, by omega⟩
  have hS'm : Monotone S' := fun p q h => hSm.monotone (by simp only [Fin.mk_le_mk]; omega)
  have hS'a : S' a = stepLt I x (1 / 2) := by
    rw [← hSl]; exact congrArg S (Fin.ext (by simp))
  have hS'c : ∀ i : Fin a, S' i = S i.castSucc := fun i => congrArg S (Fin.ext (by simp))
  have hS's : ∀ i : Fin a, S' (i + 1) = S i.succ := fun i => congrArg S (Fin.ext (by simp))
  have hiso : S' a ≤ perpIn I x (S' a) := by
    rw [hS'a, (hd _ (by norm_num)).2]
    exact ((hst (1 / 2) (by norm_num)).2.2.1.trans ((hst (1 / 2) (by norm_num)).2.2.2.1 _ (by norm_num))).trans
      (hst (1 / 2)⁻¹ (by norm_num)).2.2.1
  have hanti : ∀ p q, p ≤ q → perpIn I x (S' q) ≤ perpIn I x (S' p) := fun p q h =>
    (hp _ _ (hsat _) (hsat _) (hS'm h)).2.2.2.1
  let τ' : ℕ → ℝ := fun p => if h : p < a then τ ⟨p, h⟩ else 1
  have hτ' : ∀ i : Fin a, τ' i = τ i := fun i => dif_pos i.2
  have hτ0 : ∀ p, 0 < τ' p := fun p => by
    simp only [τ']; split_ifs with h
    · exact (hSi _).1
    · exact one_pos
  have hLe : ∀ p < a, S' (p + 1) = stepLe I x (τ' p) := fun p h => by
    rw [hS's ⟨p, h⟩, (hSi _).2.2.1, ← hτ']
  have hLt : ∀ p < a, S' p = stepLt I x (τ' p) := fun p h => by
    rw [hS'c ⟨p, h⟩, (hF' _).1, ← hτ']
  refine ⟨fun p => if p ≤ a then S' p else perpIn I x (S' (2 * a + 1 - p)),
    fun p => if p < a then τ' p else if p = a then 2 else (τ' (2 * a - p))⁻¹,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩
  · simp only [Nat.zero_le, if_true]
    rw [← hS0]; exact congrArg S (Fin.ext (by simp))
  · intro p q h
    by_cases h1 : q ≤ a
    · simp only [if_pos h1, if_pos (h.trans h1)]; exact hS'm h
    · by_cases h2 : p ≤ a
      · simp only [if_neg h1, if_pos h2]
        exact ((hS'm h2).trans hiso).trans (hanti _ _ (by omega))
      · simp only [if_neg h1, if_neg h2]
        exact hanti _ _ (by omega)
  · intro p
    by_cases h1 : p ≤ a
    · simp only [if_pos h1]; exact hsat _
    · simp only [if_neg h1]; exact (hp _ _ (hsat _) (hsat _) le_rfl).1
  · intro p hpa
    by_cases h1 : p ≤ a
    · simp only [if_pos h1, if_neg (show ¬ 2 * a + 1 - p ≤ a by omega)]
      rw [show 2 * a + 1 - (2 * a + 1 - p) = p by omega]
    · simp only [if_neg h1, if_pos (show 2 * a + 1 - p ≤ a by omega)]
      exact (hp _ _ (hsat _) (hsat _) le_rfl).2.2.1.symm
  · intro p hpa
    rcases lt_trichotomy p a with h1 | rfl | h1
    · simp only [if_pos h1, if_pos (show p + 1 ≤ a by omega)]; exact hLe p h1
    · simp only [lt_irrefl, if_false, if_true, if_neg (show ¬ p + 1 ≤ p by omega)]
      rw [show 2 * p + 1 - (p + 1) = p by omega, hS'a, (hd _ (by norm_num)).2]
      norm_num
    · simp only [if_neg h1.not_gt, if_neg h1.ne', if_neg (show ¬ p + 1 ≤ a by omega)]
      rw [show 2 * a + 1 - (p + 1) = 2 * a - p by omega, hLt _ (by omega), (hd _ (hτ0 _)).2]
  · intro p hpa
    rcases lt_trichotomy p a with h1 | rfl | h1
    · simp only [if_pos h1, if_pos h1.le, if_neg h1.ne]; exact hLt p h1
    · simp only [le_rfl, if_true]; exact hS'a
    · simp only [if_neg h1.not_gt, if_neg h1.ne', if_neg h1.not_ge]
      rw [show 2 * a + 1 - p = 2 * a - p + 1 by omega, hLe _ (by omega), (hd _ (hτ0 _)).1]
  · intro p
    have := hτ0 p
    have := hτ0 (2 * a - p)
    dsimp only
    split_ifs <;> positivity
  · intro i
    have hi := i.2
    refine ⟨by simp only [if_pos hi, hτ'], ?_, ?_⟩
    · simp only [if_neg (show ¬ 2 * a - i < a by omega), if_neg (show ¬ 2 * a - i = a by omega)]
      rw [show 2 * a - (2 * a - i) = i by omega, hτ']
    · simp only [if_pos (show i + 1 ≤ a by omega), if_pos hi.le]
      rw [hS's, hS'c, hj]

theorem mem_lowSet (de : ℝ) (hde : 0 < de) (hde' : de < 1 / 4) (a : ℕ)
    (G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (t : ℕ → ℝ) (ht : ∀ p, 0 < t p) (hta : t a = 2)
    (hLe : ∀ p ≤ 2 * a, G (p + 1) = stepLe I x (t p))
    (hLt : ∀ p ≤ 2 * a, G p = stepLt I x (if p = a then 1 / 2 else t p))
    (g : I.GA) (hg : g ∈ nearSet I x de) (γ : GL (Fin I.n) I.E)
    (h1 : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (h2 : ∀ v, uMat (g.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (h3 : I.fmat g.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) ∈ lowSet I x a G de := by
  refine ⟨h1, fun p hp y hy => ?_, fun w => ?_⟩
  · have hl := (GlobalTheory.NearLower.near_lowers_steps I x de hde hde').1 γ g h1 h2 h3 hg (t p) (ht p)
    rw [hLe p hp] at hy
    have hm : ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y ∈ stepLe I x (de * t p) :=
      hl ⟨y, hy, Matrix.toLin'_apply _ _⟩
    rw [hLt p hp]
    refine (GlobalTheory.CountSteps.steps I x _ (mul_pos hde (ht p))).2.2.2.1 _ ?_ hm
    split_ifs with h
    · rw [h, hta]; linarith
    · nlinarith [ht p]
  · have he : (frm I x w)⁻¹ * ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1).map w.embedding * frm I x w =
        (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w - 1 := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ (FrameMajorant.frm_unit I x w)]
    have hn := hg.2.2 (w.comap (algebraMap I.F I.E))
    rw [op, he]
    refine (norm_opM_le _).trans (le_trans (le_of_eq ?_) hn)
    rcases (GlobalTheory.PointEquivariance.equivariance I x γ g h1 h2 h3).2.2.2.2.2.2 w with h | h
    · rw [h]
    · rw [h]
      congr 1
      unfold hs
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.norm_conj]
      simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Complex.conj_conj, Matrix.one_apply]
      split_ifs <;> simp

theorem pow_le_pow_ratio {de l l' : ℝ} (hde : 0 < de) (hl : 0 < l) (h : l ≤ 3 * l') (m : ℕ) :
    (1 + 2 * (2 * de) / l') ^ m ≤ (1 + 12 * de / l) ^ m := by
  have hl' : 0 < l' := by linarith
  refine pow_le_pow_left₀ (by positivity) ?_ m
  have : 2 * (2 * de) / l' ≤ 12 * de / l := by
    rw [div_le_div_iff₀ hl' hl]; nlinarith
  linarith

theorem near_count : ∀ (I : AutInst) (x : I.GA) (de : ℝ), 0 < de → de < 1 / 4 → ∀ (a : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ), HasType I x j τ → (nearSet I x de).Finite ∧ (((nearSet I x de).ncard : ℕ) : ℝ) ≤ layerProd I.n I.f j τ (fun la => 1 + 12 * de / la) := by
  intro I x de hde hde' a j τ hty
  classical
  obtain ⟨G, t, h0, hmono, hsat, hperp, hLe, hLt, ht, hti, hta⟩ := exists_chain I x a j τ hty
  have hst := GlobalTheory.CountSteps.steps I x
  have htop : G (2 * a + 1) = lamX I x := by
    have := hperp 0 (by omega)
    rw [Nat.sub_zero, h0] at this
    rw [this]
    ext y
    rw [mem_perpIn]
    refine ⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp [hf, Formalism.UG.hform]
  have hrk : ∀ p ≤ 2 * a + 1, rkK (G (2 * a + 1 - p)) + rkK (G p) = I.n := fun p hp => by
    rw [hperp p hp]
    exact ((GlobalTheory.Count.PerpStep.main I x).2.2.2 _ _ (hsat p) (hsat p) le_rfl).2.1
  obtain ⟨hfin, hcard⟩ := core_count I x a G h0 hmono hsat
    (fun p hp y => by rw [hperp p hp, mem_perpIn, htop]) hrk htop t ht
    (fun q hq N h1 h2 => by
      rw [hLt q (by omega), if_neg hq.ne] at h1 ⊢
      exact (hst _ (ht q)).2.2.2.2.2.2.2.1 N h1 h2)
    (fun p hp hne => by
      rw [hLe p hp] at hne ⊢
      exact (hst _ (ht p)).2.2.2.2.1 hne) de hde
  let e : I.GA → Matrix (Fin I.n) (Fin I.n) I.E := fun g =>
    if h : g ∈ I.GFset then (h.choose : GL (Fin I.n) I.E) else 0
  have hmap : Set.MapsTo e (nearSet I x de) (lowSet I x a G de) := fun g hg => by
    have hs := hg.1.choose_spec
    simp only [e, dif_pos hg.1]
    exact mem_lowSet I x de hde hde' a G t ht hta hLe hLt g hg _ hs.1 hs.2.1 hs.2.2
  have hinj : Set.InjOn e (nearSet I x de) := fun g hg g' hg' h => by
    have hs := hg.1.choose_spec
    have hs' := hg'.1.choose_spec
    simp only [e, dif_pos hg.1, dif_pos hg'.1] at h
    refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))
    · exact (hs.2.1 v).trans (h ▸ (hs'.2.1 v).symm)
    · exact hs.2.2.trans (h ▸ hs'.2.2.symm)
  refine ⟨hfin.of_injOn hmap hinj, ?_⟩
  have hle : (((nearSet I x de).ncard : ℕ) : ℝ) ≤ ((lowSet I x a G de).ncard : ℕ) := by
    exact_mod_cast Set.ncard_le_ncard_of_injOn e hmap hinj hfin
  refine hle.trans (hcard.trans ?_)
  rw [GlobalTheory.prod_first_blocks_by_layers a (fun q p => (1 + 2 * (2 * de) / (t q / t p)) ^ (dimB I a G q p * I.f))]
  have hτ : ∀ i, 0 < τ i := fun i => (hti i).1 ▸ ht i
  have r1 : ∀ i : Fin a, rho I G i = j i := fun i => by rw [rho, (hti i).2.2]; omega
  have r2 : ∀ i : Fin a, rho I G (2 * a - i) = j i := fun i => by
    have hi := i.2
    have e1 := hrk i (by omega)
    have e2 := hrk (i + 1) (by omega)
    have e3 := (hti i).2.2
    rw [show 2 * a + 1 - (i + 1) = 2 * a - i by omega] at e2
    rw [rho, show 2 * a - i + 1 = 2 * a + 1 - i by omega]
    omega
  have hsum : rkK (G a) = ∑ l, j l := by
    have key : ∀ m, m ≤ a → rkK (G m) = ∑ l ∈ Finset.range m, rho I G l := by
      intro m
      induction m with
      | zero => intro _; rw [h0]; simp [rkK]
      | succ m ih =>
        intro hm
        have e3 := (hti ⟨m, hm⟩).2.2
        have e4 := r1 ⟨m, hm⟩
        rw [Finset.sum_range_succ, ← ih (by omega)]
        dsimp only at e3 e4
        omega
    rw [key a le_rfl, Finset.sum_range]
    exact Finset.sum_congr rfl fun i _ => r1 i
  have r3 : rho I G a = I.n - 2 * ∑ l, j l := by
    have e1 := hrk a (by omega)
    rw [show 2 * a + 1 - a = a + 1 by omega] at e1
    rw [rho]
    omega
  have hpos : ∀ q p m, 0 ≤ (1 + 2 * (2 * de) / (t q / t p)) ^ m := fun q p m => by
    have := ht q
    have := ht p
    positivity
  unfold layerProd
  refine mul_le_mul (Finset.prod_le_prod
      (fun i _ => Finset.prod_nonneg fun k _ => mul_nonneg (hpos _ _ _) (hpos _ _ _))
      fun i _ => Finset.prod_le_prod (fun k _ => mul_nonneg (hpos _ _ _) (hpos _ _ _)) fun k hk => ?_)
    (Finset.prod_le_prod (fun i _ => mul_nonneg (hpos _ _ _) (hpos _ _ _)) fun i _ => ?_)
    (Finset.prod_nonneg fun i _ => mul_nonneg (hpos _ _ _) (hpos _ _ _))
    (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => by
      have := hτ i
      have := hτ k
      positivity)
  · have hik : (i : ℕ) < k := (Finset.mem_filter.1 hk).2
    have hk' := k.2
    have := hτ i
    have := hτ k
    rw [dimB, dimB, if_neg (by omega), if_neg (by omega), r1, r2, r2, (hti i).1, (hti k).1, (hti k).2.1,
      div_inv_eq_mul]
    refine mul_le_mul (pow_le_pow_ratio hde (by positivity) ?_ _) (pow_le_pow_ratio hde (by positivity) ?_ _)
      (by positivity) (by positivity)
    · have : 0 < τ i / τ k := by positivity
      linarith
    · have : 0 < τ i * τ k := by positivity
      linarith
  · have hi := i.2
    have := hτ i
    rw [dimB, dimB, if_neg (by omega), if_pos (by omega), r2, r3, (hti i).1, hta, (hti i).2.1,
      div_inv_eq_mul]
    refine mul_le_mul (pow_le_pow_ratio hde (by positivity) (by linarith) _)
      (pow_le_pow_ratio hde (by positivity) (by nlinarith) _) (by positivity) (by positivity)

end GlobalTheory.NearCount
