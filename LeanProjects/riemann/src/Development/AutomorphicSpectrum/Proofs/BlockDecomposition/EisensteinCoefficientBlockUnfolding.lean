import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterIntegralOrthogonalityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodizationIntegralUnfoldingStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

namespace Core

variable {D : D7}

theorem continuous_trA_AE : Continuous (trA (D := D)) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))

theorem continuous_halfTr_AE : Continuous (halfTr (D := D)) := by
  unfold halfTr
  exact continuous_const.mul continuous_trA_AE

theorem continuous_inner_pair (V : HSp D) {n : ℕ} {X : Type*} [TopologicalSpace X] {u v : X → Mx D V.rank n}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => inner V (u x) (v x) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold StdUnn.inner
  exact (continuous_adj.comp hu).matrix_mul (continuous_const.matrix_mul hv)

theorem continuous_colJoin_left {X : Type*} [TopologicalSpace X] {m r s : ℕ} {u : X → Mx D m r} (hu : Continuous u)
    (v : Mx D m s) : Continuous fun x => colJoin (u x) v := by
  refine continuous_matrix fun i k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [colJoin_castAdd]
    exact hu.matrix_elem i j
  · simp only [colJoin_natAdd]
    exact continuous_const

theorem continuous_quad (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) :
    Continuous fun t : Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr_AE.comp
    (continuous_const.matrix_mul (continuous_inner_pair V continuous_id continuous_id)).matrix_trace)

theorem continuous_lin (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (x : Mx D V.rank s) :
    Continuous fun y : Mx D V.rank s => ψ (trA (Matrix.trace (inner V x y))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_trA_AE.comp
    (continuous_inner_pair V continuous_const continuous_id).matrix_trace)

theorem enorm_char (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (x : AF D.host.F) : ‖ψ x‖ₑ = 1 := by
  rw [← ofReal_norm_eq_enorm, hψ.2.1, ENNReal.ofReal_one]

theorem join_mul_eq {m r s : ℕ} (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (p : Matrix (Fin m) (Fin r) D.host.E) (q : Matrix (Fin m) (Fin s) D.host.E) (y : Mx D m r) :
    HMul.hMul (colJoin (rat p - y) (rat q)) (rat a) =
      rat (colJoin p q * a) + -(HMul.hMul (colJoin y (0 : Mx D m s)) (rat a) : Mx D m (r + s)) := by
  have h : colJoin (rat p - y) (rat q) = colJoin (rat p) (rat q) - colJoin y (0 : Mx D m s) := by
    rw [← colJoin_sub, sub_zero]
  rw [h, Matrix.sub_mul, rat_mul, rat_colJoin, sub_eq_add_neg]

theorem join_mul_injective {m r s : ℕ} {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det) :
    Function.Injective fun pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E =>
      colJoin pq.1 pq.2 * a := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  have h' : colJoin p q = colJoin p' q' := by
    have := congrArg (· * a⁻¹) h
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha] using this
  obtain ⟨h1, h2⟩ := colJoin_injective h'
  rw [h1, h2]

theorem tsum_join_le {m r s : ℕ} {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det)
    {Φ : Mx D m (r + s) → ℂ} {B : ℝ≥0}
    (hB : ∀ w, ∑' ξ : Matrix (Fin m) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) (y : Mx D m r) :
    ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
      ‖Φ (HMul.hMul (colJoin (rat pq.1 - y) (rat pq.2)) (rat a))‖ₑ ≤ B := by
  set w : Mx D m (r + s) := -(HMul.hMul (colJoin y (0 : Mx D m s)) (rat a) : Mx D m (r + s)) with hw
  calc ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
        ‖Φ (HMul.hMul (colJoin (rat pq.1 - y) (rat pq.2)) (rat a))‖ₑ
      = ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
          (fun ξ : Matrix (Fin m) (Fin (r + s)) D.host.E => ‖Φ (rat ξ + w)‖ₑ) (colJoin pq.1 pq.2 * a) := by
        refine tsum_congr fun pq => ?_
        simp only [join_mul_eq, hw]
    _ ≤ ∑' ξ : Matrix (Fin m) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective (join_mul_injective ha) _
    _ ≤ B := hB w

theorem countable_mat (D : D7) (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  exact inferInstanceAs (Countable (Fin m → Fin n → D.host.E))

theorem enorm_cellTerm (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (Φ : Mx D V.rank (r + s) → ℂ) (p : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) :
    ‖cellTerm ψ V b a Φ p q y₁ y₂‖ₑ = ‖Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a))‖ₑ := by
  simp only [cellTerm, enorm_mul, enorm_char ψ hψ, one_mul]

def cellRest (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r))) *
    Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a))

theorem continuous_cellRest (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    {Φ : Mx D V.rank (r + s) → ℂ} (hΦ : Continuous Φ) (p : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) : Continuous (cellRest ψ V b a Φ p q) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, -⟩ := lattice_Mx D V.rank r
  haveI : ContinuousSub (Mx D V.rank r) := IsTopologicalAddGroup.to_continuousSub
  have h1 : Continuous fun y₁ : Mx D V.rank r => y₁ - rat p := continuous_id.sub continuous_const
  have h2 : Continuous fun y₁ : Mx D V.rank r => rat p - y₁ :=
    (continuous_const (y := rat p)).sub continuous_id
  exact ((continuous_quad ψ hψ V b).comp h1).mul
    (hΦ.comp ((continuous_colJoin_left h2 _).matrix_mul continuous_const))

def cellZero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ) (t : Mx D V.rank r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
    Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a))

theorem cellRest_zero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Mx D V.rank r) :
    cellRest ψ V b a Φ p 0 y = cellZero ψ V b a Φ (y - rat p) := by
  simp only [cellRest, cellZero, rat_zero, neg_sub]

theorem continuous_cellZero (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    {Φ : Mx D V.rank (r + s) → ℂ} (hΦ : Continuous Φ) : Continuous (cellZero (s := s) ψ V b a Φ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, -⟩ := lattice_Mx D V.rank r
  exact (continuous_quad ψ hψ V b).mul
    (hΦ.comp ((continuous_colJoin_left continuous_neg _).matrix_mul continuous_const))

theorem tsum_cellZero_le (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det)
    {Φ : Mx D V.rank (r + s) → ℂ} {B : ℝ≥0}
    (hB : ∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) (y : Mx D V.rank r) :
    ∑' p : Matrix (Fin V.rank) (Fin r) D.host.E, ‖cellZero (s := s) ψ V b a Φ (y - rat p)‖ₑ ≤ B := by
  have hinj : Function.Injective fun p : Matrix (Fin V.rank) (Fin r) D.host.E =>
      ((p, 0) : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E) :=
    fun _ _ h => congrArg Prod.fst h
  refine le_trans (le_of_eq (tsum_congr fun p => ?_))
    ((ENNReal.tsum_comp_le_tsum_of_injective hinj _).trans (tsum_join_le (s := s) ha hB y))
  simp only [cellZero, enorm_mul, enorm_char ψ hψ, one_mul, neg_sub, rat_zero]

end Core

theorem integral_cells_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (μr : Measure (Mx D V.rank r)) (𝓕r : Set (Mx D V.rank r)) (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)),
    IsCovolOne (ratMx D V.rank r) μr 𝓕r → IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ Φ : Mx D V.rank (r + s) → ℂ, Continuous Φ →
    ∀ B : ℝ≥0, (∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) →
      ∫ z in 𝓕r ×ˢ 𝓕s, ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
          cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂(μr.prod μs) =
        ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr := by
  intro D ψ hψ V r s μr 𝓕r μs 𝓕s hr hs b a ha Φ hΦ B hB
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D V.rank s
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  haveI := Core.countable_mat D V.rank r
  haveI := Core.countable_mat D V.rank s
  haveI : IsFiniteMeasure (μr.restrict 𝓕r) := ⟨by simp [hr.2.2]⟩
  haveI : IsFiniteMeasure (μs.restrict 𝓕s) := ⟨by simp [hs.2.2]⟩
  rw [← Measure.prod_restrict]
  have hνu : ((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    simp [hr.2.2, hs.2.2]
  have hform : ∀ (pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E)
      (z : Mx D V.rank r × Mx D V.rank s), cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 =
        Core.cellRest ψ V b a Φ pq.1 pq.2 z.1 * ψ (trA (Matrix.trace (inner V (rat pq.2) z.2))) :=
    fun pq z => mul_comm _ _
  have hcont : ∀ pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      Continuous fun z : Mx D V.rank r × Mx D V.rank s => cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 := fun pq => by
    simp only [hform]
    exact ((Core.continuous_cellRest ψ hψ V b a hΦ pq.1 pq.2).comp continuous_fst).mul
      ((Core.continuous_lin ψ hψ V (rat pq.2)).comp continuous_snd)
  have hsum : ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      ∫⁻ z, ‖cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2‖ₑ ∂((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) ≠ ∞ := by
    rw [← lintegral_tsum fun pq => (hcont pq).enorm.measurable.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (g := fun _ => (B : ℝ≥0∞)) fun z => ?_)
    · simp [hνu]
    · simp only [Core.enorm_cellTerm ψ hψ]
      exact Core.tsum_join_le ha hB z.1
  rw [integral_tsum (fun pq => (hcont pq).aestronglyMeasurable) hsum]
  have hterm : ∀ pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      ∫ z, cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) =
        (∫ y in 𝓕r, Core.cellRest ψ V b a Φ pq.1 pq.2 y ∂μr) *
          ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat pq.2) y))) ∂μs := fun pq => by
    simp only [hform]
    exact integral_prod_mul (Core.cellRest ψ V b a Φ pq.1 pq.2)
      (fun y => ψ (trA (Matrix.trace (inner V (rat pq.2) y))))
  simp only [hterm]
  have hinj : Function.Injective fun p : Matrix (Fin V.rank) (Fin r) D.host.E =>
      ((p, 0) : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E) :=
    fun _ _ h => congrArg Prod.fst h
  rw [← hinj.tsum_eq]
  · obtain ⟨-, hu⟩ := GlobalTheory.T.periodization_integral_unfolding D V.rank r μr 𝓕r hr (Core.cellZero (s := s) ψ V b a Φ)
      (Core.continuous_cellZero ψ hψ V b a hΦ) B (Core.tsum_cellZero_le ψ hψ V b ha hB)
    refine Eq.trans (tsum_congr fun p => ?_) hu
    simp only [(GlobalTheory.T.character_integral_orthogonality D ψ hψ V s μs 𝓕s hs 0).1 rfl, mul_one, Core.cellRest_zero]
  · rintro ⟨p, q⟩ hne
    by_cases hq : q = 0
    · exact ⟨p, by rw [hq]⟩
    · exact absurd (by simp only [(GlobalTheory.T.character_integral_orthogonality D ψ hψ V s μs 𝓕s hs q).2 hq, mul_zero]) hne

end GlobalTheory.CompanionTheory.EisUnfold

end
