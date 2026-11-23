import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory

namespace GlobalTheory.HilbertSamuel.Model

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem exists_intGens : ∃ (n : ℕ) (w : Fin n → Fin G.N → F),
    Submodule.span ℤ (Set.range w) = G.lattice.restrictScalars ℤ := by
  have h : G.lattice.FG := Submodule.fg_span (Set.finite_range _)
  have : Module.Finite (𝓞 F) G.lattice := Module.Finite.iff_fg.2 h
  have : Module.Finite ℤ G.lattice := Module.Finite.trans (𝓞 F) _
  have h' : (G.lattice.restrictScalars ℤ).FG := Module.Finite.iff_fg.1 this
  exact Submodule.fg_iff_exists_fin_generating_family.1 h'

def regen {n : ℕ} (w : Fin n → Fin G.N → F) (hw : Submodule.span F (Set.range w) = ⊤) (Λ : ℝ) : Geo F :=
  { G with
    n := n
    w := Matrix.of fun j k => w k j
    abelian₂ := Λ
    geom := ⟨⟨G.geom.alg.variety, G.geom.alg.indep, hw, G.geom.alg.bpf⟩, G.geom.bd_ne⟩
    herm := G.herm
    conj := G.conj
    alg₂ := ⟨G.alg₂.1, G.alg₂.2, G.alg₂.3, G.alg₂.4⟩
    herm₂ := G.herm₂
    conj₂ := G.conj₂
    U_le := G.U_le }

theorem exists_regen : ∃ (n : ℕ) (w : Fin n → Fin G.N → F) (hw : _) (Λ : ℝ),
    (regen G w hw Λ).ShortGenerators ∧ (regen G w hw Λ).lattice = G.lattice := by
  obtain ⟨n, w, h⟩ := exists_intGens G
  have hm (k) : w k ∈ G.lattice := h.le (Submodule.subset_span ⟨k, rfl⟩)
  have hl : Submodule.span (𝓞 F) (Set.range w) = G.lattice :=
    le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 hm))
      fun u hu => Submodule.span_le_restrictScalars ℤ (𝓞 F) _ (h.ge hu)
  have hw : Submodule.span F (Set.range w) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 F), hl, HermSys.lattice, Submodule.span_span_of_tower]
    exact G.geom.alg.spans
  refine ⟨n, w, hw, 1 + ∑ k, ∑ σ : F →+* ℂ, G.normAt σ (w k), ⟨fun u hu => h.ge (hl.le hu), fun k σ => ?_, ?_⟩, hl⟩
  · have h0 (k) (σ : F →+* ℂ) : 0 ≤ G.normAt σ (w k) := Real.sqrt_nonneg _
    exact ((Finset.single_le_sum (fun σ _ => h0 k σ) (Finset.mem_univ σ)).trans
      (Finset.single_le_sum (f := fun k => ∑ σ : F →+* ℂ, G.normAt σ (w k))
        (fun k _ => Finset.sum_nonneg fun σ _ => h0 k σ) (Finset.mem_univ k))).trans (le_add_of_nonneg_left zero_le_one)
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)

theorem positivity_regen (h : G.Positivity) {n : ℕ} (w : Fin n → Fin G.N → F) (hw) (Λ : ℝ) :
    (regen G w hw Λ).Positivity :=
  ⟨⟨h.bir.1, h.bir.2, h.bir.3, h.bir.4, h.bir.5⟩, h.nef, h.big⟩

theorem mulW_mem_global (j : ℕ) (u : Fin G.N → F) {f : G.Sec j} (hf : f ∈ G.global j) :
    G.mulW j u f ∈ G.global (j + 1) := by
  obtain ⟨f, rfl⟩ := hf
  refine ⟨(oneChart (isLB_tens G.K.isLB G.isLBA) G.isLB (Nat.cast_succ j).symm).mul
    (H0.ofSec G.str ⊤ (G.comb u)) f, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec, G.ofSec_comb]
  simp [Geo.mulW, Fintype.linearCombination_apply]

def mulG (j : ℕ) : (Fin G.N → F) →ₗ[F] G.global j →ₗ[F] G.global (j + 1) :=
  LinearMap.mk₂ F (fun u f => ⟨G.mulW j u f, mulW_mem_global G j u f.2⟩)
    (fun _ _ _ => Subtype.ext (by simp)) (fun _ _ _ => Subtype.ext (by simp))
    (fun _ _ _ => Subtype.ext (by simp)) (fun _ _ _ => Subtype.ext (by simp))

def lat (j : ℕ) : Submodule (𝓞 F) (G.global j) :=
  Nat.rec (motive := fun j => Submodule (𝓞 F) (G.global j))
    (Submodule.span (𝓞 F) (Set.range (Module.finBasis F (G.global 0))))
    (fun j M => Submodule.span (𝓞 F) (Set.range (Module.finBasis F (G.global (j + 1)))) ⊔
      Submodule.map₂ ((mulG G j).restrictScalars₁₂ (𝓞 F) (𝓞 F)) G.lattice M) j

theorem basis_mem_lat (j : ℕ) (i) : Module.finBasis F (G.global j) i ∈ lat G j := by
  cases j with
  | zero => exact Submodule.subset_span ⟨i, rfl⟩
  | succ j => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem isFull_lat (j : ℕ) : IsFull (lat G j) := by
  refine ⟨?_, top_le_iff.1 ((Module.finBasis F (G.global j)).span_eq.ge.trans
    (Submodule.span_mono (Set.range_subset_iff.2 (basis_mem_lat G j))))⟩
  induction j with
  | zero => exact Submodule.fg_span (Set.finite_range _)
  | succ j ih =>
    have h : G.lattice.FG := Submodule.fg_span (Set.finite_range _)
    exact (Submodule.fg_span (Set.finite_range _)).sup (h.map₂ _ ih)

def data (T : ℕ) (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β) : Data F :=
  { G.globalData T hT with M := lat G, full := isFull_lat G, beta := β, one_le_beta := hβ, J := J }

variable {T : ℕ} (hT : G.D + 1 ≤ T) (β J : ℝ) (hβ : 1 ≤ β)

theorem mulStable : (data G T hT β J hβ).MulStable := fun j _ w hw f hf =>
  have h : mulG G j w f ∈ lat G (j + 1) := Submodule.mem_sup_right
    (Submodule.apply_mem_map₂ ((mulG G j).restrictScalars₁₂ (𝓞 F) (𝓞 F)) hw hf)
  ⟨mulG G j w f, h, rfl⟩

theorem shortFamily (j : ℕ) : (data G T hT β J hβ).ShortFamily j 1 :=
  have e := (data G T hT β J hβ).latRank_M j
  ⟨Module.finBasis F (G.global j) ∘ Fin.cast e, fun _ => basis_mem_lat G j _,
    (Module.finBasis F (G.global j)).linearIndependent.comp _ (Fin.cast_injective e),
    fun _ σ => (nrm_ofBasis _ σ _).le⟩

omit [NumberField F] in

theorem nrm_ofBasis_eq {V n : Type} [AddCommGroup V] [Module F V] [Fintype n] [DecidableEq n]
    (b : Module.Basis n F V) (σ : F →+* ℂ) (x : V) :
    (ofBasis b).nrm σ x = Real.sqrt (∑ i, ‖σ (b.repr x i)‖ ^ 2) := by
  simp [HermFam.nrm, ofBasis, ofGram, ofCoords, basisCoords, dotProduct, Complex.conj_mul', ← Complex.ofReal_pow]

theorem exists_bound {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] {N m m' : ℕ}
    (b : Module.Basis (Fin m) F V) (b' : Module.Basis (Fin m') F V') (μ : (Fin N → F) →ₗ[F] V →ₗ[F] V')
    (σ : F →+* ℂ) {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ w f, (ofBasis b').nrm σ (μ w f) ≤ c * frameNorm A (fun k => σ (w k)) * (ofBasis b).nrm σ f := by
  refine ⟨∑ l, ∑ k, ∑ i, archSize A (Pi.single k 1) * ‖σ (b'.repr (μ (Pi.single k 1) (b i)) l)‖,
    by unfold archSize; positivity, fun w f => ?_⟩
  have hw (k) : ‖σ (w k)‖ ≤ frameNorm A (fun k => σ (w k)) * archSize A (Pi.single k 1) := by
    simpa [Pi.single_apply] using norm_pairing_le hA (fun k => σ (w k)) (Pi.single k 1)
  have hf (i) : ‖σ (b.repr f i)‖ ≤ (ofBasis b).nrm σ f := by
    rw [nrm_ofBasis_eq]
    exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun i => ‖σ (b.repr f i)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  have e (l) : b'.repr (μ w f) l = ∑ k, ∑ i, w k * b.repr f i * b'.repr (μ (Pi.single k 1) (b i)) l := by
    conv_lhs => rw [pi_eq_sum_univ' w, ← b.sum_repr f]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [nrm_ofBasis_eq b']
  refine (Real.sqrt_le_iff.2 ⟨by positivity, Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _⟩).trans ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [e, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_mul, map_mul, norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_right (mul_le_mul (hw k) (hf i) (norm_nonneg _) ((norm_nonneg _).trans (hw k)))
    (norm_nonneg (σ (b'.repr (μ (Pi.single k 1) (b i)) l)))
  linarith

theorem exists_mulBound : ∃ β₀ : ℝ, ∀ β ≥ β₀, ∀ (hβ : 1 ≤ β) (J : ℝ), (data G T hT β J hβ).MulBound fun _ => β := by
  choose c h0 hc using fun (j : ℕ) (σ : F →+* ℂ) => exists_bound (Module.finBasis F (G.global j))
    (Module.finBasis F (G.global (j + 1))) (mulG G j) σ (G.herm σ)
  refine ⟨(∑ j ∈ Finset.range T, ∑ σ, c j σ) ^ 2, fun β h _ J j hj σ w _ f _ g e => ?_⟩
  obtain rfl : g = mulG G j w f := Subtype.ext e
  have h₁ : c j σ ≤ Real.sqrt β := Real.le_sqrt_of_sq_le ((pow_le_pow_left₀ (h0 j σ)
    ((Finset.single_le_sum (fun σ _ => h0 j σ) (Finset.mem_univ σ)).trans
      (Finset.single_le_sum (f := fun j => ∑ σ, c j σ) (fun j _ => Finset.sum_nonneg fun σ _ => h0 j σ)
        (Finset.mem_range.2 hj))) 2).trans h)
  exact (hc j σ w f).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h₁ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

include hT in

theorem exists_data_of_positivity (h : G.Positivity) :
    ∃ X : Data F, X.D = G.D ∧ X.T = T ∧ X.d = Module.finrank F (G.global T) ∧ X.del = G.del ∧ X.Positivity ∧
      X.MulStable ∧ X.MulBound (fun _ => X.beta) ∧ X.ShortGenerators ∧ X.ShortFamily X.D X.LamD ∧
      X.ShortFamily X.T X.LamT := by
  obtain ⟨n, w, hw, Λ, hs, -⟩ := exists_regen G
  obtain ⟨β, hβ⟩ := exists_mulBound (regen G w hw Λ) (T := T) hT
  have h1 := le_max_right β 1
  exact ⟨data (regen G w hw Λ) T hT (max β 1) 0 h1, rfl, rfl, Data.d_eq_finrank _, rfl,
    positivity_regen G h w hw Λ, mulStable (regen G w hw Λ) hT _ 0 h1, hβ _ (le_max_left _ _) h1 0, hs,
    shortFamily (regen G w hw Λ) hT _ 0 h1 _, shortFamily (regen G w hw Λ) hT _ 0 h1 _⟩

omit G in

theorem exists_data {M : ℕ} (hM : 1 ≤ M) {T : ℕ} (hT : M + 1 ≤ T) :
    ∃ X : Data F, X.D = M ∧ X.T = T ∧ 0 < X.d ∧ X.del = 1 ∧ X.Positivity ∧ X.MulStable ∧
      X.MulBound (fun _ => X.beta) ∧ X.ShortGenerators ∧ X.ShortFamily X.D X.LamD ∧ X.ShortFamily X.T X.LamT := by
  obtain ⟨X, h₁, h₂, h₃, h₄, h⟩ := exists_data_of_positivity (Proj.geo F hM) (T := T) hT (Proj.positivity F hM)
  exact ⟨X, h₁, h₂, (Proj.finrank_global_pos F hM T).trans_eq h₃.symm, h₄.trans (projSys.del_eq_one F M), h⟩

omit G in

theorem not_shortGenerators_geo [IsTotallyComplex F] {M : ℕ} (hM : 1 ≤ M) : ¬ (Proj.geo F hM).ShortGenerators := by
  intro h
  have key (a : 𝓞 F) : ∃ z : ℤ, (a : F) = z := by
    have hm : a • (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) F).col 0 ∈ (Proj.geo F hM).lattice :=
      (Proj.geo F hM).lattice.smul_mem a (Submodule.subset_span ⟨(0 : Fin (M + 1)), rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (h.int _ hm)
    have : (∑ i : Fin (M + 1), c i • (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) F).col i) 0 =
      (a • (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) F).col 0) 0 := congrFun hc (0 : Fin (M + 1))
    exact ⟨c (0 : Fin (M + 1)), by simpa [Matrix.one_apply, Algebra.smul_def] using this.symm⟩
  obtain ⟨σ⟩ : Nonempty (F →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal σ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  obtain ⟨p, hp⟩ := key a
  obtain ⟨q, hq⟩ := key b
  rw [show algebraMap (𝓞 F) F a = p from hp, show algebraMap (𝓞 F) F b = q from hq]
  simp

end GlobalTheory.HilbertSamuel.Model
