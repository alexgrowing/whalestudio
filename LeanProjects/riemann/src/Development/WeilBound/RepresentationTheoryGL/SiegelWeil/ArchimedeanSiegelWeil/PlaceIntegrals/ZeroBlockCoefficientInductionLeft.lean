import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitIntegralInvariantE0Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependentStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.LocalGramFibreIntegralEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExists
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem vH_eta {K : Type} {M : ℕ} (x : Fin (M + 2) → K) : vH (x 0) (x 1) (tailH x) = x := by
  funext i
  refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem hR_tail_zero (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E) :
    hR R σ J x 0 = 0 := by
  simp [hR, hform]

theorem isotropic_cvec_apply_basis_zero (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin (M + 2) → R ⊗[F] E)
    (ht : hR R σ (hypOne J) x x = 0) : cvec R σ J x (Fin.cons 1 fun _ => 0) = x := by
  have h0 : tailH (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E) = 0 := by
    funext i; rfl
  have h1 : (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E) 1 = 0 := rfl
  have h2 : (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E) 0 = 1 := rfl
  conv_rhs => rw [← vH_eta x]
  simp only [cvec, tHalf, ht, h0, h1, h2, hR_tail_zero, mul_zero, zero_mul, sub_zero, mul_one, one_mul, add_zero]
  congr 1
  funext i
  have : (Fin.cons 1 fun _ => 0 : Fin (M + 2) → R ⊗[F] E) i.succ.succ = 0 := rfl
  simp [this, tailH]

theorem chartS_zero (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (ht : hR R σ (hypOne J) (x 0) (x 0) = 0)
    (c : HA R σ (hypOne J))
    (hc : ∀ v : Fin (M + 2) → R ⊗[F] E, ((HA.mat R σ (hypOne J) c : GL (Fin (M + 2)) (R ⊗[F] E)) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J (x 0) v)
    (a : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) :
    chartS R σ J x a 0 Y = actW R σ (hypOne J) c (consA a Y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show x 0 = ((HA.mat R σ (hypOne J) c : GL (Fin (M + 2)) (R ⊗[F] E)) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec (Fin.cons 1 fun _ => 0)
    rw [hc, isotropic_cvec_apply_basis_zero R σ J _ ht]
  · show cvec R σ J (x 0) (vH (a 0 j) (0 - tHalf R σ J (x 0) * a 0 j) (Y j)) =
      ((HA.mat R σ (hypOne J) c : GL (Fin (M + 2)) (R ⊗[F] E)) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec (Fin.cons (a 0 j) (Fin.cons 0 (Y j)))
    rw [hc]
    simp only [tHalf, ht, mul_zero, zero_mul, sub_zero]
    rfl

theorem gramR_e0 (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    gramR R σ (hypOne J) (e0 (R ⊗[F] E) M) = 0 := by
  funext a b
  show hR R σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 1 fun _ => 0) = 0
  simp only [hR, hform, JR]
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ, hypOne_zero_zero, hypOne_zero_one]

end Local

theorem exists_seq_cover {X G : Type} [TopologicalSpace X] [SecondCountableTopology X] [Nonempty G]
    (O : G → Set X) (hO : ∀ g, IsOpen (O g)) : ∃ gk : ℕ → G, ⋃ k, O (gk k) = ⋃ g, O g := by
  obtain ⟨T, hT, hU⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  obtain ⟨g₀⟩ := ‹Nonempty G›
  have hT' : (insert g₀ T).Countable := hT.insert g₀
  obtain ⟨gk, hgk⟩ := hT'.exists_eq_range (Set.insert_nonempty _ _)
  refine ⟨gk, Set.Subset.antisymm (Set.iUnion_subset fun k => Set.subset_iUnion O _) ?_⟩
  rw [← hU]
  refine Set.iUnion₂_subset fun g hg => ?_
  have : g ∈ Set.range gk := hgk ▸ Set.mem_insert_of_mem _ hg
  obtain ⟨k, rfl⟩ := this
  exact Set.subset_iUnion (fun k => O (gk k)) k

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

set_option maxHeartbeats 4000000 in

theorem local_stages : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b) (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ g : HA R σ (hypOne J), Ψ (actW R σ (hypOne J) g (e0 _ M)) = stageInt R σ J b lam (m' (hermOf R σ (0 : Matrix (Fin n) (Fin n) E) h₀)) φ g) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁)) = ∫⁻ y, Ψ y ∂(m₁ (hermOf R σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn hnM h₀ h₁ h₂ R _ _ _ _ _ hLoc d b lam hlam m m₁ m' hm hm₁ hm' φ hφ
  have hR' := hLoc
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hJH, -⟩ := GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem F E σ hCM M J hJ
  obtain ⟨_, _, _, _, _, gAct⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 2) (hypOne J) hJH R
  obtain ⟨_, _, _, _, _, uAct⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ R
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hb1 := hbor 1 (M + 2)
  have hb2 := hbor (n + 1) (M + 2)
  have hb3 := hbor n M
  have hb4 := hbor 1 n
  have hz0 : hermOf R σ (0 : Matrix (Fin n) (Fin n) E) h₀ = 0 := Subtype.ext (by ext i j; simp [hermOf])
  have hz1 : hermOf R σ (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁ = 0 :=
    Subtype.ext (by ext i j; simp [hermOf])
  have hz2 : hermOf R σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := Subtype.ext (by ext i j; simp [hermOf])
  simp only [hz0, hz1, hz2]
  have hH2 := hH (n + 1)
  have hW2 := hW (n + 1) (M + 2)
  have hW1 := hW 1 (M + 2)
  have hH1 := hH 1
  have hW3 := hW 1 n
  have hinv : ∀ g : HA R σ (hypOne J), (m 0).map (actW R σ (hypOne J) g) = m 0 := fun g =>
    GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free F E σ hCM (M + 2) (hypOne J) hJH R hLoc (n + 1) _ _ m
      hW2 hH2 hm g 0
  have hinv1 : ∀ g : HA R σ (hypOne J), (m₁ 0).map (actW R σ (hypOne J) g) = m₁ 0 := fun g =>
    GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free F E σ hCM (M + 2) (hypOne J) hJH R hLoc 1 _ _ m₁
      hW1 hH1 hm₁ g 0
  have hinvU : ∀ h : HA R σ J, (m' 0).map (actW R σ J h) = m' 0 := fun h =>
    GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free F E σ hCM M J hJ R hLoc n _ _ m' (hW n M) (hH n) hm' h 0
  haveI hσ' : SigmaFinite (m' 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_fib hm' (GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hLoc n M) 0
  have hact1 : ∀ g : HA R σ (hypOne J), Continuous (actW R σ (hypOne J) g : (Fin 1 → Fin (M + 2) → R ⊗[F] E) → _) :=
    fun g => (gAct 1).1.comp (Continuous.prodMk_right g)
  have hact2 : ∀ g : HA R σ (hypOne J),
      Continuous (actW R σ (hypOne J) g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → _) :=
    fun g => (gAct (n + 1)).1.comp (Continuous.prodMk_right g)
  have hcancel : ∀ (g : HA R σ (hypOne J)) (y : Fin 1 → Fin (M + 2) → R ⊗[F] E),
      actW R σ (hypOne J) g⁻¹ (actW R σ (hypOne J) g y) = y := fun g y => by
    rw [← (gAct 1).2.2.1, inv_mul_cancel, (gAct 1).2.1]
  have hcancel' : ∀ (g : HA R σ (hypOne J)) (y : Fin 1 → Fin (M + 2) → R ⊗[F] E),
      actW R σ (hypOne J) g (actW R σ (hypOne J) g⁻¹ y) = y := fun g y => by
    rw [← (gAct 1).2.2.1, mul_inv_cancel, (gAct 1).2.1]
  have hUo : IsOpen {k : R ⊗[F] E | IsUnit k} := by
    have := (GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM R hLoc).isOpen_range
    convert this using 1
    ext x
    simp [IsUnit]

  let O : HA R σ (hypOne J) → Set (Fin 1 → Fin (M + 2) → R ⊗[F] E) := fun g =>
    {y | IsUnit (actW R σ (hypOne J) g⁻¹ y 0 0)}
  have hO : ∀ g, IsOpen (O g) := fun g => by
    have hc : Continuous fun y : Fin 1 → Fin (M + 2) → R ⊗[F] E => actW R σ (hypOne J) g⁻¹ y 0 0 :=
      (continuous_apply 0).comp ((continuous_apply 0).comp (hact1 g⁻¹))
    exact hUo.preimage hc
  obtain ⟨gk, hgk⟩ := exists_seq_cover O hO
  let P : ℕ → Set (Fin 1 → Fin (M + 2) → R ⊗[F] E) := disjointed fun k => O (gk k)
  have hPm : ∀ k, MeasurableSet (P k) := MeasurableSet.disjointed fun k => (hO _).measurableSet
  have hPsub : ∀ k, P k ⊆ O (gk k) := fun k => disjointed_subset _ k
  have hPd : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed _
  have hPU : ⋃ k, P k = ⋃ g, O g := (iUnion_disjointed).trans hgk
  have hOrb : ∀ g : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) ∈ ⋃ k, P k := fun g => by
    rw [hPU]
    refine Set.mem_iUnion.2 ⟨g, ?_⟩
    show IsUnit (actW R σ (hypOne J) g⁻¹ (actW R σ (hypOne J) g (e0 _ M)) 0 0)
    rw [hcancel]
    exact isUnit_one
  have hchM := (GlobalTheory.T.free_cell_open_independent F E σ hCM M J hJ R hLoc n).2.2.2.2

  let Lc : ℕ → (Fin 1 → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞ := fun k x =>
    ∫⁻ Y, ∫⁻ a, φ (actW R σ (hypOne J) (gk k) (chartS R σ J x a 0 Y)) ∂(coordW R b lam 1 n) ∂(m' 0)
  have hLc : ∀ k, Measurable (Lc k) := fun k => by
    have h0 : Measurable fun q : ((Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E)) ×
        (Fin 1 → Fin n → R ⊗[F] E) =>
        φ (actW R σ (hypOne J) (gk k) (chartS R σ J q.1.1 q.2 0 q.1.2)) := by
      have hq : Measurable fun q : ((Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E)) ×
          (Fin 1 → Fin n → R ⊗[F] E) =>
          ((q.1.1, q.2, (0 : Fin 1 → Fin n → R ⊗[F] E), q.1.2) : (Fin 1 → Fin (M + 2) → R ⊗[F] E) ×
            (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E)) :=
        (measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk
          ((measurable_const).prodMk (measurable_snd.comp measurable_fst)))
      exact hφ.comp ((hact2 _).measurable.comp (hchM.comp hq))
    exact (h0.lintegral_prod_right').lintegral_prod_right'
  let H : ℕ → (Fin 1 → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞ := fun k =>
    (P k).indicator fun y => Lc k (actW R σ (hypOne J) (gk k)⁻¹ y)
  have hHm : ∀ k, Measurable (H k) := fun k =>
    ((hLc k).comp (hact1 _).measurable).indicator (hPm k)
  refine ⟨fun y => ∑' k, H k y, Measurable.ennreal_tsum hHm, ?_, ?_⟩
  · intro g
    obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.1 (hOrb g)
    have hs : (∑' k, H k (actW R σ (hypOne J) g (e0 _ M))) = H k₀ (actW R σ (hypOne J) g (e0 _ M)) :=
      tsum_eq_single k₀ fun k hk => Set.indicator_of_notMem
        (fun hmem => Set.disjoint_left.1 (hPd hk) hmem hk₀) _
    show (∑' k, H k (actW R σ (hypOne J) g (e0 _ M))) = _
    rw [hs]
    show (P k₀).indicator _ _ = _
    rw [Set.indicator_of_mem hk₀]
    set y := actW R σ (hypOne J) g (e0 _ M) with hy
    set x := actW R σ (hypOne J) (gk k₀)⁻¹ y with hx
    have hxu : IsUnit (x 0 0) := hPsub k₀ hk₀
    have hxg : gramR R σ (hypOne J) x = 0 := by
      rw [hx, (gAct 1).2.2.2, hy, (gAct 1).2.2.2, gramR_e0]
    have hxt : hR R σ (hypOne J) (x 0) (x 0) = 0 := congrFun (congrFun hxg 0) 0
    obtain ⟨c, hc⟩ := GlobalTheory.T.unitary_moving_unit_vector F E σ hCM M J hJ R (x 0) hxu
    have hch := chartS_zero (n := n) R σ J x hxt c hc
    have hce : actW R σ (hypOne J) c (e0 _ M) = x := by
      funext i
      rw [Subsingleton.elim i 0]
      show ((HA.mat R σ (hypOne J) c : GL (Fin (M + 2)) (R ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec (Fin.cons 1 fun _ => 0) = x 0
      rw [hc, isotropic_cvec_apply_basis_zero R σ J _ hxt]
    have hst : Lc k₀ x = stageInt R σ J b lam (m' 0) φ (gk k₀ * c) := by
      show (∫⁻ Y, ∫⁻ a, φ (actW R σ (hypOne J) (gk k₀) (chartS R σ J x a 0 Y)) ∂(coordW R b lam 1 n) ∂(m' 0)) =
        ∫⁻ Y, ∫⁻ a, φ (actW R σ (hypOne J) (gk k₀ * c) (consA a Y)) ∂(coordW R b lam 1 n) ∂(m' 0)
      simp only [hch, (gAct (n + 1)).2.2.1]
    rw [hst]
    refine GlobalTheory.T.orbit_integral_invariant_e0 F E σ hCM M J hJ R hLoc n d b lam hlam (m' 0) hinvU φ hφ _ _ ?_
    rw [(gAct 1).2.2.1, hce, hx, hcancel']
  · have hae : ∀ᵐ X ∂(m 0), (fun _ : Fin 1 => X 0) ∈ ⋃ k, P k := by
      obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R (n + 1)
      obtain ⟨gl, -, hgf⟩ := hlift (M + 2) _ hJH
      filter_upwards [GlobalTheory.CompanionTheory.SW.FibreUniq.ae_eq_of_isFibreFamily Subtype.val_injective hgf hm 0] with X hX
      have hXg : gramR R σ (hypOne J) X = 0 := by
        rw [hgf, hX.1]
        rfl
      have hfree : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => X 0) :=
        LinearIndependent.comp hX.2 (fun _ : Fin 1 => (0 : Fin (n + 1))) (Function.injective_of_subsingleton _)
      have hg0 : gramR R σ (hypOne J) (fun _ : Fin 1 => X 0) = 0 := by
        funext a c
        exact congrFun (congrFun hXg 0) 0
      obtain ⟨g, hg⟩ := GlobalTheory.T.local_witt_isotropic_to_e0 F E σ hCM M J hJ R hLoc _ hfree hg0
      rw [← hg]
      exact hOrb g
    have hfm : Measurable fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => (fun _ : Fin 1 => X 0) :=
      measurable_pi_lambda _ fun _ => measurable_pi_apply 0
    let B : ℕ → (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞ := fun k =>
      ((fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => (fun _ : Fin 1 => X 0)) ⁻¹' P k).indicator φ
    have hBm : ∀ k, Measurable (B k) := fun k => hφ.indicator (hfm (hPm k))
    have hsplit : ∫⁻ X, φ X ∂(m 0) = ∑' k, ∫⁻ X, B k X ∂(m 0) := by
      rw [← lintegral_tsum fun k => (hBm k).aemeasurable]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with X hX
      obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.1 hX
      have hs : (∑' i, B i X) = B k₀ X := tsum_eq_single k₀ fun k hk =>
        Set.indicator_of_notMem (s := (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E =>
          (fun _ : Fin 1 => X 0)) ⁻¹' P k) (fun hmem => Set.disjoint_left.1 (hPd hk) hmem hk₀) φ
      rw [hs]
      exact (Set.indicator_of_mem (s := (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E =>
        (fun _ : Fin 1 => X 0)) ⁻¹' P k₀) hk₀ φ).symm
    have hterm : ∀ k, ∫⁻ X, B k X ∂(m 0) = ∫⁻ y, H k y ∂(m₁ 0) := by
      intro k
      have hunit : ∀ X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E, ¬ IsUnit (X 0 0) →
          B k (actW R σ (hypOne J) (gk k) X) = 0 := by
        intro X hX
        refine Set.indicator_of_notMem (fun hmem => hX ?_) _
        have h3 : IsUnit (actW R σ (hypOne J) (gk k)⁻¹ (actW R σ (hypOne J) (gk k) (fun _ : Fin 1 => X 0)) 0 0) :=
          hPsub k hmem
        rwa [hcancel] at h3
      calc ∫⁻ X, B k X ∂(m 0) = ∫⁻ X, B k X ∂((m 0).map (actW R σ (hypOne J) (gk k))) := by rw [hinv]
        _ = ∫⁻ X, B k (actW R σ (hypOne J) (gk k) X) ∂(m 0) :=
            lintegral_map (hBm k) (hact2 _).measurable
        _ = ∫⁻ x, ∫⁻ Y, ∫⁻ a, B k (actW R σ (hypOne J) (gk k) (chartS R σ J x a 0 Y))
              ∂(coordW R b lam 1 n) ∂(m' 0) ∂(m₁ 0) :=
            GlobalTheory.T.local_gram_fibre_integral_eq F E σ hCM M J hJ R hLoc n d b lam hlam m m₁ m' hm hm₁ hm' _
              ((hBm k).comp (hact2 _).measurable) hunit
        _ = ∫⁻ x, H k (actW R σ (hypOne J) (gk k) x) ∂(m₁ 0) := by
            refine lintegral_congr fun x => ?_
            have hfx : ∀ (a : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E),
                (fun _ : Fin 1 => actW R σ (hypOne J) (gk k) (chartS R σ J x a 0 Y) 0) =
                  actW R σ (hypOne J) (gk k) x := by
              intro a Y
              funext i
              rw [Subsingleton.elim i 0]
              rfl
            by_cases hxP : actW R σ (hypOne J) (gk k) x ∈ P k
            · have hB : ∀ a Y, B k (actW R σ (hypOne J) (gk k) (chartS R σ J x a 0 Y)) =
                  φ (actW R σ (hypOne J) (gk k) (chartS R σ J x a 0 Y)) := fun a Y =>
                Set.indicator_of_mem (show _ ∈ (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E =>
                  (fun _ : Fin 1 => X 0)) ⁻¹' P k from by
                    show (fun _ : Fin 1 => actW R σ (hypOne J) (gk k) (chartS R σ J x a 0 Y) 0) ∈ P k
                    rw [hfx]; exact hxP) φ
              simp only [hB]
              show _ = (P k).indicator _ _
              rw [Set.indicator_of_mem hxP, hcancel]
            · have hB : ∀ a Y, B k (actW R σ (hypOne J) (gk k) (chartS R σ J x a 0 Y)) = 0 := fun a Y =>
                Set.indicator_of_notMem (fun hmem => hxP (by
                  have : (fun _ : Fin 1 => actW R σ (hypOne J) (gk k) (chartS R σ J x a 0 Y) 0) ∈ P k := hmem
                  rwa [hfx] at this)) φ
              simp only [hB, lintegral_zero]
              exact (Set.indicator_of_notMem hxP _).symm
        _ = ∫⁻ y, H k y ∂((m₁ 0).map (actW R σ (hypOne J) (gk k))) :=
            (lintegral_map (hHm k) (hact1 _).measurable).symm
        _ = ∫⁻ y, H k y ∂(m₁ 0) := by rw [hinv1]
    rw [hsplit, lintegral_tsum fun k => (hHm k).aemeasurable]
    exact tsum_congr hterm

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
