import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraPropertiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LDL

section Abstract

variable {R K : Type} [CommRing R] [CommRing K]

abbrev Up (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

def unip {n : ℕ} (u : Up n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j then u ⟨(i, j), h⟩ else 0

def headU {n : ℕ} (u : Up (n + 1) → K) (j : Fin n) : K := u ⟨(0, j.succ), Fin.succ_pos j⟩

def tailU {n : ℕ} (u : Up (n + 1) → K) : Up n → K :=
  fun p => u ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_lt_succ_iff.2 p.2⟩

theorem up_snd_ne {n : ℕ} (p : Up (n + 1)) : p.1.2 ≠ 0 := fun h => Fin.not_lt_zero _ (h ▸ p.2)

def joinU {n : ℕ} (c : Fin n → K) (v : Up n → K) : Up (n + 1) → K := fun p =>
  if h : p.1.1 = 0 then c (p.1.2.pred (up_snd_ne p))
  else v ⟨(p.1.1.pred h, p.1.2.pred (up_snd_ne p)), (Fin.pred_lt_pred_iff (ha := h) (hb := up_snd_ne p)).2 p.2⟩

theorem joinU_head_tail {n : ℕ} (u : Up (n + 1) → K) : joinU (headU u) (tailU u) = u := by
  funext p
  obtain ⟨⟨i, j⟩, h⟩ := p
  induction j using Fin.cases with
  | zero => exact absurd h (Fin.not_lt_zero _)
  | succ j =>
    induction i using Fin.cases with
    | zero => simp [joinU, headU]
    | succ i => simp [joinU, tailU, Fin.succ_ne_zero]

theorem headU_join {n : ℕ} (c : Fin n → K) (v : Up n → K) : headU (joinU c v) = c := by
  funext j
  simp [headU, joinU]

theorem tailU_join {n : ℕ} (c : Fin n → K) (v : Up n → K) : tailU (joinU c v) = v := by
  funext p
  simp [tailU, joinU, Fin.succ_ne_zero]

theorem unip_zero_zero {n : ℕ} (u : Up (n + 1) → K) : unip u 0 0 = 1 := by simp [unip]

theorem unip_succ_zero {n : ℕ} (u : Up (n + 1) → K) (k : Fin n) : unip u k.succ 0 = 0 := by
  simp [unip, Fin.succ_ne_zero]

theorem unip_zero_succ {n : ℕ} (u : Up (n + 1) → K) (j : Fin n) : unip u 0 j.succ = headU u j := by
  simp [unip, headU, (Fin.succ_ne_zero j).symm, Fin.succ_pos]

theorem unip_succ_succ {n : ℕ} (u : Up (n + 1) → K) (i j : Fin n) :
    unip u i.succ j.succ = unip (tailU u) i j := by
  by_cases h : i = j
  · simp [unip, h]
  · by_cases h' : i < j
    · simp [unip, h, h', tailU]
    · simp [unip, h, h']

variable (ι : R →+* K) (τ : K →+* K)

def gram {n : ℕ} (d : Fin n → Rˣ) (u : Up n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => ∑ k, τ (unip u k i) * ι (d k) * unip u k j

def Hm (n : ℕ) : Set (Matrix (Fin n) (Fin n) K) := {S | ∀ a b, τ (S b a) = S a b}

def blk {n : ℕ} (A : K) (c : Fin n → K) (S : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => Fin.cases (Fin.cases A c j) (fun a => Fin.cases (τ (c a)) (S a) j) i

theorem gram_zero_zero {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) :
    gram ι τ d u 0 0 = ι (d 0) := by
  simp [gram, Fin.sum_univ_succ, unip_zero_zero, unip_succ_zero]

theorem gram_zero_succ {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) (j : Fin n) :
    gram ι τ d u 0 j.succ = ι (d 0) * headU u j := by
  simp [gram, Fin.sum_univ_succ, unip_zero_zero, unip_succ_zero, unip_zero_succ]

theorem gram_succ_zero {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) (i : Fin n) :
    gram ι τ d u i.succ 0 = τ (headU u i) * ι (d 0) := by
  simp [gram, Fin.sum_univ_succ, unip_zero_zero, unip_succ_zero, unip_zero_succ]

theorem gram_succ_succ {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) (i j : Fin n) :
    gram ι τ d u i.succ j.succ =
      gram ι τ (Fin.tail d) (tailU u) i j + τ (headU u i) * ι (d 0) * headU u j := by
  simp [gram, Fin.sum_univ_succ, unip_zero_succ, unip_succ_succ, Fin.tail, add_comm]

variable {ι τ}

theorem gram_split (hτι : ∀ r, τ (ι r) = ι r) {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) :
    gram ι τ d u = blk τ (ι (d 0)) (fun j => ι (d 0) * headU u j)
      (fun a b => gram ι τ (Fin.tail d) (tailU u) a b + τ (headU u a) * ι (d 0) * headU u b) := by
  funext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simpa [blk] using gram_zero_zero ι τ d u
    | succ j => simpa [blk] using gram_zero_succ ι τ d u j
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simpa [blk, hτι, mul_comm] using gram_succ_zero ι τ d u i
    | succ j => simpa [blk] using gram_succ_succ ι τ d u i j

theorem gram_mem (hττ : ∀ x, τ (τ x) = x) (hτι : ∀ r, τ (ι r) = ι r) {n : ℕ} (d : Fin n → Rˣ)
    (u : Up n → K) : gram ι τ d u ∈ Hm τ n := by
  intro a b
  simp only [gram, map_sum, map_mul, hττ, hτι]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem blk_mem (hττ : ∀ x, τ (τ x) = x) {n : ℕ} {A : K} (hA : τ A = A) (c : Fin n → K)
    {S : Matrix (Fin n) (Fin n) K} (hS : S ∈ Hm τ n) : blk τ A c S ∈ Hm τ (n + 1) := by
  intro i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simpa [blk] using hA
    | succ j => simp [blk, hττ]
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [blk]
    | succ j => simpa [blk] using hS i j

theorem gram_eq (ι : R →+* K) (τ : K →+* K) {n : ℕ} (d : Fin n → Rˣ) (u : Up n → K) :
    gram ι τ d u = cT τ (unip u) * Matrix.diagonal (fun i => ι (d i)) * unip u := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  rfl

section Top

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace K] [IsTopologicalRing K]

def eD (n : ℕ) : ((Fin (n + 1) → Rˣ) × (Up (n + 1) → K)) ≃ₜ
    Rˣ × (Fin n → K) × (Fin n → Rˣ) × (Up n → K) where
  toFun x := (x.1 0, headU x.2, Fin.tail x.1, tailU x.2)
  invFun y := (Fin.cons y.1 y.2.2.1, joinU y.2.1 y.2.2.2)
  left_inv x := by
    obtain ⟨d, u⟩ := x
    exact Prod.ext (Fin.cons_self_tail d) (joinU_head_tail u)
  right_inv y := by
    obtain ⟨s, c, d, v⟩ := y
    refine Prod.ext rfl (Prod.ext (headU_join c v) (Prod.ext ?_ (tailU_join c v)))
    show Fin.tail (Fin.cons s d : Fin (n + 1) → Rˣ) = d
    funext i
    simp [Fin.tail]
  continuous_toFun := by
    have h1 : Continuous fun x : (Fin (n + 1) → Rˣ) × (Up (n + 1) → K) => x.1 := continuous_fst
    have h2 : Continuous fun x : (Fin (n + 1) → Rˣ) × (Up (n + 1) → K) => x.2 := continuous_snd
    refine ((continuous_apply 0).comp h1).prodMk
      ((continuous_pi fun j => (continuous_apply _).comp h2).prodMk
        ((continuous_pi fun j => (continuous_apply _).comp h1).prodMk
          (continuous_pi fun p => (continuous_apply _).comp h2)))
  continuous_invFun := by
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)
    · induction i using Fin.cases with
      | zero => simpa using continuous_fst
      | succ i =>
        simpa [Function.comp_def] using
          (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
    · by_cases h : p.1.1 = 0
      · simp only [joinU, h, dif_pos]
        exact (continuous_apply _).comp (continuous_fst.comp continuous_snd)
      · simp only [joinU, h, dif_neg, not_false_eq_true]
        exact (continuous_apply _).comp (continuous_snd.comp (continuous_snd.comp continuous_snd))

variable {ι : R →+* K} {τ : K →+* K}

def shear (hι : Continuous ι) (hτ : Continuous τ) (hττ : ∀ x, τ (τ x) = x) (hτι : ∀ r, τ (ι r) = ι r)
    (n : ℕ) : (Rˣ × (Fin n → K) × Hm τ n) ≃ₜ (Rˣ × (Fin n → K) × Hm τ n) where
  toFun x := (x.1, fun j => ι x.1 * x.2.1 j,
    ⟨fun a b => x.2.2.1 a b + τ (x.2.1 a) * ι x.1 * x.2.1 b, by
      intro a b
      simp only [map_add, map_mul, hττ, hτι]
      rw [x.2.2.2 a b]
      ring⟩)
  invFun x := (x.1, fun j => ι ((x.1⁻¹ : Rˣ) : R) * x.2.1 j,
    ⟨fun a b => x.2.2.1 a b - τ (x.2.1 a) * ι ((x.1⁻¹ : Rˣ) : R) * x.2.1 b, by
      intro a b
      simp only [map_sub, map_mul, hττ, hτι]
      rw [x.2.2.2 a b]
      ring⟩)
  left_inv x := by
    obtain ⟨s, c, S⟩ := x
    have hw : ι (s : R) * ι ((s⁻¹ : Rˣ) : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    refine Prod.ext rfl (Prod.ext ?_ (Subtype.ext ?_))
    · funext j
      show ι ((s⁻¹ : Rˣ) : R) * (ι (s : R) * c j) = c j
      linear_combination c j * hw
    · funext a b
      show S.1 a b + τ (c a) * ι (s : R) * c b - τ (ι (s : R) * c a) * ι ((s⁻¹ : Rˣ) : R) * (ι (s : R) * c b) = S.1 a b
      rw [map_mul, hτι]
      linear_combination (-(τ (c a) * ι (s : R) * c b)) * hw
  right_inv x := by
    obtain ⟨s, c, S⟩ := x
    have hw : ι (s : R) * ι ((s⁻¹ : Rˣ) : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    refine Prod.ext rfl (Prod.ext ?_ (Subtype.ext ?_))
    · funext j
      show ι (s : R) * (ι ((s⁻¹ : Rˣ) : R) * c j) = c j
      linear_combination c j * hw
    · funext a b
      show S.1 a b - τ (c a) * ι ((s⁻¹ : Rˣ) : R) * c b + τ (ι ((s⁻¹ : Rˣ) : R) * c a) * ι (s : R) * (ι ((s⁻¹ : Rˣ) : R) * c b) = S.1 a b
      rw [map_mul, hτι]
      linear_combination (τ (c a) * ι ((s⁻¹ : Rˣ) : R) * c b) * hw
  continuous_toFun := by
    have hs : Continuous fun x : Rˣ × (Fin n → K) × Hm τ n => ι (x.1 : R) :=
      hι.comp (Units.continuous_val.comp continuous_fst)
    have hc : ∀ j, Continuous fun x : Rˣ × (Fin n → K) × Hm τ n => x.2.1 j := fun j =>
      (continuous_apply j).comp (continuous_fst.comp continuous_snd)
    have hS : Continuous fun x : Rˣ × (Fin n → K) × Hm τ n => x.2.2.1 :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    refine continuous_fst.prodMk ((continuous_pi fun j => hs.mul (hc j)).prodMk
      (Continuous.subtype_mk (continuous_matrix fun a b => ?_) _))
    exact (hS.matrix_elem a b).add (((hτ.comp (hc a)).mul hs).mul (hc b))
  continuous_invFun := by
    have hs : Continuous fun x : Rˣ × (Fin n → K) × Hm τ n => ι ((x.1⁻¹ : Rˣ) : R) :=
      hι.comp (Units.continuous_val.comp (continuous_inv.comp continuous_fst))
    have hc : ∀ j, Continuous fun x : Rˣ × (Fin n → K) × Hm τ n => x.2.1 j := fun j =>
      (continuous_apply j).comp (continuous_fst.comp continuous_snd)
    have hS : Continuous fun x : Rˣ × (Fin n → K) × Hm τ n => x.2.2.1 :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    refine continuous_fst.prodMk ((continuous_pi fun j => hs.mul (hc j)).prodMk
      (Continuous.subtype_mk (continuous_matrix fun a b => ?_) _))
    exact (hS.matrix_elem a b).sub (((hτ.comp (hc a)).mul hs).mul (hc b))

def eH {lev : K → R} (hι : Continuous ι) (hτ : Continuous τ) (hlev : Continuous lev)
    (hττ : ∀ x, τ (τ x) = x) (hτι : ∀ r, τ (ι r) = ι r) (hlι : ∀ r, lev (ι r) = r)
    (hfix : ∀ y, τ y = y → ∃ r, y = ι r) (n : ℕ) :
    (R × (Fin n → K) × Hm τ n) ≃ₜ Hm τ (n + 1) where
  toFun x := ⟨blk τ (ι x.1) x.2.1 x.2.2.1, blk_mem hττ (hτι _) _ x.2.2.2⟩
  invFun T := (lev (T.1 0 0), fun b => T.1 0 b.succ,
    ⟨fun a b => T.1 a.succ b.succ, fun a b => T.2 a.succ b.succ⟩)
  left_inv x := by
    obtain ⟨r, c, S⟩ := x
    refine Prod.ext (hlι r) (Prod.ext ?_ (Subtype.ext ?_))
    · funext b; simp [blk]
    · funext a b; simp [blk]
  right_inv T := by
    obtain ⟨r, hr⟩ := hfix (T.1 0 0) (T.2 0 0)
    apply Subtype.ext
    funext i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp [blk, hr, hlι]
      | succ j => simp [blk]
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [blk] using T.2 i.succ 0
      | succ j => simp [blk]
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    have hc : ∀ j, Continuous fun x : R × (Fin n → K) × Hm τ n => x.2.1 j := fun j =>
      (continuous_apply j).comp (continuous_fst.comp continuous_snd)
    have hS : Continuous fun x : R × (Fin n → K) × Hm τ n => x.2.2.1 :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa [blk, Function.comp_def] using hι.comp continuous_fst
      | succ j => simpa [blk] using hc j
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [blk, Function.comp_def] using hτ.comp (hc i)
      | succ j => simpa [blk] using hS.matrix_elem i j
  continuous_invFun := by
    have hT : Continuous fun T : Hm τ (n + 1) => T.1 := continuous_subtype_val
    refine (hlev.comp (hT.matrix_elem 0 0)).prodMk
      ((continuous_pi fun b : Fin n => hT.matrix_elem 0 b.succ).prodMk
        (Continuous.subtype_mk (continuous_matrix fun (a b : Fin n) => hT.matrix_elem a.succ b.succ) _))

def oH (ι : R →+* K) (τ : K →+* K) (hττ : ∀ x, τ (τ x) = x) (hτι : ∀ r, τ (ι r) = ι r) (n : ℕ)
    (x : (Fin n → Rˣ) × (Up n → K)) : Hm τ n :=
  ⟨gram ι τ x.1 x.2, gram_mem hττ hτι x.1 x.2⟩

theorem oH_isOpenEmbedding {lev : K → R} (hι : Continuous ι) (hτ : Continuous τ) (hlev : Continuous lev)
    (hττ : ∀ x, τ (τ x) = x) (hτι : ∀ r, τ (ι r) = ι r) (hlι : ∀ r, lev (ι r) = r)
    (hfix : ∀ y, τ y = y → ∃ r, y = ι r) (hU : IsOpenEmbedding (Units.val : Rˣ → R)) (n : ℕ) :
    IsOpenEmbedding (oH ι τ hττ hτι n) := by
  induction n with
  | zero =>
    haveI : IsEmpty (Up 0) := ⟨fun p => (p.1.1).elim0⟩
    haveI : Unique ((Fin 0 → Rˣ) × (Up 0 → K)) :=
      ⟨⟨(fun i => i.elim0, fun p => isEmptyElim p)⟩, fun x =>
        Prod.ext (funext fun i => i.elim0) (funext fun p => isEmptyElim p)⟩
    haveI : Unique (Hm τ 0) :=
      ⟨⟨⟨0, fun a => a.elim0⟩⟩, fun S => Subtype.ext (Subsingleton.elim _ _)⟩
    have h : oH ι τ hττ hτι 0 = Homeomorph.homeomorphOfUnique _ _ := Subsingleton.elim _ _
    rw [h]
    exact (Homeomorph.homeomorphOfUnique _ _).isOpenEmbedding
  | succ n ih =>
    have h : oH ι τ hττ hτι (n + 1) =
        (eH hι hτ hlev hττ hτι hlι hfix n) ∘ (Prod.map Units.val id) ∘ (shear hι hτ hττ hτι n) ∘
          (Prod.map id (Prod.map id (oH ι τ hττ hτι n))) ∘ (eD n) := by
      funext x
      apply Subtype.ext
      exact gram_split hτι x.1 x.2
    rw [h]
    exact (eH hι hτ hlev hττ hτι hlι hfix n).isOpenEmbedding.comp
      ((hU.prodMap .id).comp ((shear hι hτ hττ hτι n).isOpenEmbedding.comp
        ((IsOpenEmbedding.id.prodMap (IsOpenEmbedding.id.prodMap ih)).comp (eD n).isOpenEmbedding)))

end Top

end Abstract

theorem ldl_isOpenEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ n : ℕ, ∃ o : (Fin n → Rˣ) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) → HermR R σ n, IsOpenEmbedding o ∧ ∀ d u, ∀ N : Matrix (Fin n) (Fin n) (R ⊗[F] E), (N = Matrix.of fun i j => if i = j then 1 else if h : i < j then u ⟨(i, j), h⟩ else 0) → (o (d, u) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) N * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * N := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ hloc n
  obtain ⟨hTR, hLC, hSC, hT2, hAr, hRed, hU, -⟩ := hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hAr
  haveI := hRed
  obtain ⟨-, -, -, hinv, -, hfix, -⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hcm R
  obtain ⟨hKT, -, -, -, hsc, htr, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := hKT
  have hfr : Module.finrank F E = 2 := hcm.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hιt : ∀ r : R, algebraMap R (R ⊗[F] E) r = r ⊗ₜ[F] (1 : E) := fun r => by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hι : Continuous (algebraMap R (R ⊗[F] E)) := by
    have e : (algebraMap R (R ⊗[F] E) : R → R ⊗[F] E) = fun r => r • (1 : R ⊗[F] E) :=
      funext fun r => Algebra.algebraMap_eq_smul_one r
    rw [e]
    exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))
  have hτι : ∀ r : R, sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := fun r => by
    rw [hιt]
    simp [sigR]
  have hfix' : ∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = algebraMap R (R ⊗[F] E) r := fun y hy => by
    obtain ⟨r, hr⟩ := hfix y hy
    exact ⟨r, hr.trans (hιt r).symm⟩
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    norm_num
  have hlι : ∀ r : R, algebraMap F R (1 / 2) *
      Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) r) = r := fun r => by
    have h := Algebra.trace_algebraMap_of_basis
      (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E hfr)) r
    rw [h]
    simp only [Fintype.card_fin, two_nsmul]
    linear_combination r * h2
  have hlev : Continuous fun y : R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) y := continuous_const.mul htr
  refine ⟨oH (algebraMap R (R ⊗[F] E)) (sigR R σ) hinv hτι n,
    oH_isOpenEmbedding hι hsc hlev hinv hτι hlι hfix' hU n, ?_⟩
  rintro d u N rfl
  have hd : (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) =
      fun i => algebraMap R (R ⊗[F] E) (d i) := funext fun i => (hιt _).symm
  rw [hd]
  exact gram_eq _ _ d u

end GlobalTheory.CompanionTheory.SW.LDL
