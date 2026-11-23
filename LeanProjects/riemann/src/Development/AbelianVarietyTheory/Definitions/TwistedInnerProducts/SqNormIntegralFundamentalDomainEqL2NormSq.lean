import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace
open GlobalTheory.Ker (ipO)
open scoped TensorProduct ENNReal ComplexConjugate

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Words

variable {ι X : Type} (A : ι → X → X) (p : X → ℝ≥0∞)

def wordAct (l : List ι) (x : X) : X := l.foldr (fun i y => A i y) x

@[simp] theorem wordAct_nil (x : X) : wordAct A [] x = x := rfl

@[simp] theorem wordAct_cons (i : ι) (l : List ι) (x : X) : wordAct A (i :: l) x = A i (wordAct A l x) := rfl

theorem wordAct_append (l l' : List ι) (x : X) : wordAct A (l ++ l') x = wordAct A l (wordAct A l' x) :=
  List.foldr_append

theorem wordAct_rel {Y : Type} {A : ι → X → X} {B : ι → Y → Y} {R : X → Y → Prop} (l : List ι)
    (h : ∀ i ∈ l, ∀ x y, R x y → R (A i x) (B i y)) {x : X} {y : Y} (hx : R x y) :
    R (wordAct A l x) (wordAct B l y) := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact h i List.mem_cons_self _ _ (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

variable [Fintype ι]

def wordSum (d : ℕ) (x : X) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (d + 1), ∑ a : Fin k → ι, p (wordAct A (List.ofFn a) x)

@[simp] theorem wordSum_zero (x : X) : wordSum A p 0 x = p x := by simp [wordSum]

theorem wordSum_one (x : X) : wordSum A p 1 x = p x + ∑ i, p (A i x) := by
  simp only [wordSum, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  congr 1
  · simp
  · exact Fintype.sum_equiv (Equiv.funUnique _ _) _ _ fun a => by simp

variable {A p}

theorem le_wordSum {d : ℕ} {l : List ι} (hl : l.length ≤ d) (x : X) : p (wordAct A l x) ≤ wordSum A p d x := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ a : Fin k → ι, p (wordAct A (List.ofFn a) x))
    (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hl)))
  simpa using Finset.single_le_sum (f := fun a : Fin l.length → ι => p (wordAct A (List.ofFn a) x))
    (fun _ _ => zero_le) (Finset.mem_univ l.get)

theorem wordSum_mono {d d' : ℕ} (h : d ≤ d') (x : X) : wordSum A p d x ≤ wordSum A p d' x :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h))

theorem wordSum_ne_top_iff {d : ℕ} {x : X} :
    wordSum A p d x ≠ ∞ ↔ ∀ l : List ι, l.length ≤ d → p (wordAct A l x) ≠ ∞ :=
  ⟨fun h _ hl => ne_top_of_le_ne_top h (le_wordSum hl x), fun h =>
    ENNReal.sum_ne_top.2 fun k hk => ENNReal.sum_ne_top.2 fun a _ =>
      h _ (by simpa using Nat.le_of_lt_succ (Finset.mem_range.1 hk))⟩

theorem wordSum_le_add {d : ℕ} {x y z : X}
    (h : ∀ l, p (wordAct A l z) ≤ p (wordAct A l x) + p (wordAct A l y)) :
    wordSum A p d z ≤ wordSum A p d x + wordSum A p d y := by
  simp only [wordSum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => h _

theorem wordSum_eq_mul {d : ℕ} {x y : X} {c : ℝ≥0∞} (h : ∀ l, p (wordAct A l y) = c * p (wordAct A l x)) :
    wordSum A p d y = c * wordSum A p d x := by
  simp only [wordSum, Finset.mul_sum, h]

theorem wordSum_letter_le (d : ℕ) (i : ι) (x : X) : wordSum A p d (A i x) ≤ wordSum A p (d + 1) x := by
  classical
  unfold wordSum
  rw [Finset.sum_range_succ' _ (d + 1)]
  refine le_add_right (Finset.sum_le_sum fun k _ => ?_)
  have hi : Function.Injective fun a : Fin k → ι => (Fin.snoc a i : Fin (k + 1) → ι) :=
    fun a b h => by simpa using congrArg (Fin.init (α := fun _ => ι)) h
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset (Finset.subset_univ (Finset.univ.map ⟨_, hi⟩)))
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [List.ofFn_succ', wordAct_append, -List.ofFn_succ]

end Words

section Group

variable {D : D7} (θ : InfFam D) (V : HSp D)

theorem height_laws : (∀ g, 1 ≤ height V g) ∧ height V 1 = 1 ∧ (∀ g, height V g⁻¹ = height V g) ∧
    (∀ g h, height V (g * h) ≤ height V g * height V h) ∧ Continuous (height V) :=
  ⟨one_le_height V, height_one V, height_inv V, height_mul_le V, continuous_height V⟩

theorem quotHeight_laws : (∀ g, 1 ≤ quotHeight V g ∧ quotHeight V g ≤ height V g) ∧
    (∀ γ ∈ GQ V, ∀ g, quotHeight V (γ * g) = quotHeight V g) ∧
    (∀ g h, quotHeight V (g * h) ≤ quotHeight V g * height V h ∧ quotHeight V g / height V h ≤ quotHeight V (g * h)) ∧
    Continuous (quotHeight V) :=
  ⟨fun g => ⟨one_le_quotHeight V g, quotHeight_le_height V g⟩, fun _ hγ => quotHeight_left V hγ,
    fun g h => ⟨quotHeight_mul_le V g h, (div_le_iff₀ (height_pos V h)).2 (by
      simpa using quotHeight_mul_le V (g * h) h⁻¹)⟩, continuous_quotHeight V⟩

def growthSize (N : ℕ) (φ : GA D V → ℂ) : ℝ≥0∞ := ⨆ g, ENNReal.ofReal (‖φ g‖ / height V g ^ N)

def IsLieWord (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) : Prop := ∀ p ∈ l, p.2 ∈ lieAt V p.1

def rWord (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) : GA D V → ℂ :=
  wordAct (fun p => Rder θ V p.1 p.2) l φ

def glDer (a : D.what₂.Tau × Fin V.rank × Fin V.rank) (φ : GA D V → ℂ) : GA D V → ℂ :=
  RderC θ V a.1 (Matrix.single a.2.1 a.2.2 1) φ

def growthSob (d N : ℕ) (φ : GA D V → ℂ) : ℝ≥0∞ := wordSum (glDer θ V) (growthSize V N) d φ

structure RapidDecSm (φ : GA D V → ℂ) : Prop extends IsAutFun V φ where
  smooth : φ ∈ SmFun θ V
  decay : ∀ l, IsLieWord V l → RapidDec V (rWord θ V l φ)

theorem rWord_const (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) :
    ∃ c' : ℂ, rWord θ V l (fun _ => c) = fun _ => c' := foldrRder_const θ V l c

open scoped ComplexOrder in

theorem rapidDecSm_const (hV : ∀ τ, (gramAt D V τ).PosDef) (c : ℂ) : RapidDecSm θ V fun _ => c := by
  refine ⟨(isAutFunSm_const θ V c).toIsAutFun, (isAutFunSm_const θ V c).smooth, fun l _ => ?_⟩
  obtain ⟨K, hK, h⟩ := GlobalTheory.definite_unitary_cocompact V hV
  obtain ⟨c', hc⟩ := rWord_const θ V l c
  rw [hc]
  refine .of_isCompact (fun _ _ _ => rfl) continuous_const hK fun g => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by simpa using hk⟩

def posSp (D : D7) (n : ℕ) : HSp D := Examples₂.posSpace Examples₂.star_isIntegral n

theorem gramAt_posSp (n : ℕ) (τ : D.what₂.Tau) : gramAt D (posSp D n) τ = 1 := by
  have hg : (posSp D n).gram = 1 := by
    funext i j
    refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral n (fun _ => false) n 0 i j).trans ?_
    change (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0
    by_cases h : i = j <;> simp [h, Examples₂.sgn]
  unfold gramAt
  rw [hg]
  exact Matrix.map_one _ (map_zero _) (map_one _)

open scoped ComplexOrder in

theorem rapidDecSm_one_posSp (n : ℕ) : RapidDecSm θ (posSp D n) fun _ => 1 :=
  rapidDecSm_const θ _ (fun τ => by rw [gramAt_posSp]; exact Matrix.PosDef.one) 1

variable {θ V} {φ φ' : GA D V → ℂ} {N : ℕ}

theorem growthSize_le_iff {C : ℝ} (hC : 0 ≤ C) :
    growthSize V N φ ≤ ENNReal.ofReal C ↔ ∀ g, ‖φ g‖ ≤ C * height V g ^ N := by
  simp only [growthSize, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hC, div_le_iff₀ (pow_pos (height_pos V _) N)]

theorem modGrowthExp_iff : ModGrowthExp V N φ ↔ growthSize V N φ ≠ ∞ :=
  ⟨fun ⟨_, hC⟩ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((growthSize_le_iff (nonneg_of_growth hC)).2 hC),
    fun h => ⟨_, (growthSize_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal h).ge⟩⟩

theorem growthSize_eq_quot (hφ : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    growthSize V N φ = ⨆ g, ENNReal.ofReal (‖φ g‖ / quotHeight V g ^ N) := by
  refine le_antisymm (iSup_mono fun g => ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (norm_nonneg _)
    (pow_pos (quotHeight_pos V g) N) (pow_le_pow_left₀ (quotHeight_pos V g).le (quotHeight_le_height V g) N)))
    (iSup_le fun g => ?_)
  rcases eq_or_ne (growthSize V N φ) ∞ with h | h
  · exact h ▸ le_top
  have h1 := (growthSize_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal h).ge
  rw [← ENNReal.ofReal_toReal h]
  refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ (pow_pos (quotHeight_pos V g) N)).2 ?_)
  have hc : IsClosed {x : ℝ | ‖φ g‖ ≤ (growthSize V N φ).toReal * x ^ N} := isClosed_le continuous_const (by fun_prop)
  refine hc.closure_subset_iff.2 ?_ (csInf_mem_closure (Set.range_nonempty fun γ : GQ V => height V (γ * g))
    ⟨1, by rintro _ ⟨_, rfl⟩; exact one_le_height V _⟩)
  rintro _ ⟨γ, rfl⟩
  simpa only [hφ γ γ.2, Set.mem_setOf_eq] using h1 (γ * g)

theorem growthSize_anti {N' : ℕ} (h : N ≤ N') : growthSize V N' φ ≤ growthSize V N φ :=
  iSup_mono fun g => ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (norm_nonneg _)
    (pow_pos (height_pos V g) N) (pow_le_pow_right₀ (one_le_height V g) h))

theorem growthSize_add_le : growthSize V N (φ + φ') ≤ growthSize V N φ + growthSize V N φ' := by
  refine iSup_le fun g => le_trans ?_ (add_le_add (le_iSup _ g) (le_iSup _ g))
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  rw [← add_div]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (pow_pos (height_pos V g) N).le

theorem growthSize_smul (c : ℂ) : growthSize V N (c • φ) = ‖c‖ₑ * growthSize V N φ := by
  simp only [growthSize, ENNReal.mul_iSup, Pi.smul_apply, norm_smul, mul_div_assoc,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm_eq_enorm]

theorem growthSize_const (c : ℂ) : growthSize V N (fun _ => c) = ‖c‖ₑ := by
  rw [← ofReal_norm_eq_enorm]
  refine le_antisymm ((growthSize_le_iff (norm_nonneg c)).2 fun g =>
    le_mul_of_one_le_right (norm_nonneg c) (one_le_pow₀ (one_le_height V g))) (le_iSup_of_le 1 (by simp))

theorem unifModGrowth_iff : UnifModGrowth V θ φ ↔ ∃ N, ∀ l, IsLieWord V l → growthSize V N (rWord θ V l φ) ≠ ∞ :=
  exists_congr fun _ => forall₂_congr fun _ _ => modGrowthExp_iff

theorem linOnSm_rWord {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) :
    LinOnSm θ V (rWord θ V l) :=
  linOnSm_foldr _ l fun p hp => linOnSm_Rder (hl p hp)

theorem linOnSm_glWord (l : List (D.what₂.Tau × Fin V.rank × Fin V.rank)) : LinOnSm θ V (wordAct (glDer θ V) l) :=
  linOnSm_foldr _ l fun a _ => linOnSm_RderC a.1 _

theorem growthSob_add_le (h : φ ∈ SmFun θ V) (h' : φ' ∈ SmFun θ V) (d N : ℕ) :
    growthSob θ V d N (φ + φ') ≤ growthSob θ V d N φ + growthSob θ V d N φ' :=
  wordSum_le_add fun l => by rw [(linOnSm_glWord l).add φ h φ' h']; exact growthSize_add_le

theorem growthSob_smul (c : ℂ) (d N : ℕ) : growthSob θ V d N (c • φ) = ‖c‖ₑ * growthSob θ V d N φ :=
  wordSum_eq_mul fun l => by rw [(linOnSm_glWord l).smul, growthSize_smul]

variable (θ V) in

def allDer (M : Submodule ℂ (GA D V → ℂ)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | φ ∈ SmFun θ V ∧ ∀ l, IsLieWord V l → rWord θ V l φ ∈ M}
  add_mem' h h' := ⟨add_mem h.1 h'.1, fun l hl => by
    rw [(linOnSm_rWord hl).add _ h.1 _ h'.1]; exact add_mem (h.2 l hl) (h'.2 l hl)⟩
  zero_mem' := ⟨zero_mem _, fun l hl => by
    have := (linOnSm_rWord (θ := θ) hl).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]; exact zero_mem _⟩
  smul_mem' c _ h := ⟨(SmFun θ V).smul_mem c h.1, fun l hl => by
    rw [(linOnSm_rWord hl).smul]; exact M.smul_mem c (h.2 l hl)⟩

theorem Rder_mem_allDer {M : Submodule ℂ (GA D V → ℂ)} (h : φ ∈ allDer θ V M) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ allDer θ V M :=
  ⟨Rder_mem h.1 hX, fun l hl => by
    have := h.2 (l ++ [(τ, X)]) fun p hp => (List.mem_append.1 hp).elim (hl p) fun e => by
      rw [List.mem_singleton.1 e]; exact hX
    rwa [rWord, wordAct_append] at this⟩

theorem RderC_mem_allDer {M : Submodule ℂ (GA D V → ℂ)} (h : φ ∈ allDer θ V M) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) : RderC θ V τ Z φ ∈ allDer θ V M :=
  add_mem (Rder_mem_allDer h (GlobalTheory.SmoothAutCheck.parts_mem V τ Z).1)
    (Submodule.smul_mem _ _ (Rder_mem_allDer h (GlobalTheory.SmoothAutCheck.parts_mem V τ Z).2))

theorem exists_growthSob_ne_top (hs : φ ∈ SmFun θ V) (h : UnifModGrowth V θ φ) :
    ∃ N, ∀ d, growthSob θ V d N φ ≠ ∞ := by
  obtain ⟨N, hN⟩ := unifModGrowth_iff.1 h
  let M : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | growthSize V N f ≠ ∞}
      add_mem' := fun a b => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨a, b⟩) growthSize_add_le
      zero_mem' := (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top
      smul_mem' := fun c _ a => (growthSize_smul c).trans_ne (ENNReal.mul_ne_top enorm_ne_top a) }
  refine ⟨N, fun d => wordSum_ne_top_iff.2 fun l _ => ?_⟩
  exact (wordAct_rel (A := glDer θ V) (B := glDer θ V) (R := fun f _ => f ∈ allDer θ V M) l
    (fun a _ _ _ hf => RderC_mem_allDer hf a.1 _) (y := φ) ⟨hs, hN⟩).2 [] (fun _ h => by simp at h)

variable (V) in

def rapidSub : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | RapidDec V φ}
  add_mem' := RapidDec.add
  zero_mem' := RapidDec.zero
  smul_mem' c _ h := h.smul c

theorem rapidDecSm_iff : RapidDecSm θ V φ ↔ φ ∈ allDer θ V (rapidSub V) ∧
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g :=
  ⟨fun h => ⟨⟨h.smooth, h.decay⟩, h.level⟩, fun h =>
    have h0 : RapidDec V φ := h.1.2 [] fun _ e => by simp at e
    ⟨⟨h0.1, h.2, h0.continuous⟩, h.1.1, h.1.2⟩⟩

theorem RapidDecSm.rapidDec (h : RapidDecSm θ V φ) : RapidDec V φ := h.decay [] fun _ e => by simp at e

theorem RapidDecSm.unifModGrowth (h : RapidDecSm θ V φ) : UnifModGrowth V θ φ :=
  ⟨0, fun l hl => (h.decay l hl).bounded.imp fun _ hC g => (hC g).trans_eq (by simp)⟩

theorem RapidDecSm.add (h : RapidDecSm θ V φ) (h' : RapidDecSm θ V φ') : RapidDecSm θ V (φ + φ') := by
  obtain ⟨a, U, hU, hk⟩ := rapidDecSm_iff.1 h
  obtain ⟨a', U', hU', hk'⟩ := rapidDecSm_iff.1 h'
  exact rapidDecSm_iff.2 ⟨add_mem a a', U ⊓ U', hU.inter hU', fun k h1 h2 g => by
    simp only [Pi.add_apply, hk k h1.1 h2 g, hk' k h1.2 h2 g]⟩

theorem RapidDecSm.smul (c : ℂ) (h : RapidDecSm θ V φ) : RapidDecSm θ V (c • φ) := by
  obtain ⟨a, U, hU, hk⟩ := rapidDecSm_iff.1 h
  exact rapidDecSm_iff.2 ⟨Submodule.smul_mem _ c a, U, hU, fun k h1 h2 g => by simp only [Pi.smul_apply, hk k h1 h2 g]⟩

theorem Rder_rTr_fin {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : GA D V → ℂ) : Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ X φ) := by
  funext g
  simp only [Rder, rTr, mul_assoc, oneP,
    GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ _) hk]

theorem RapidDecSm.rder (h : RapidDecSm θ V φ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : RapidDecSm θ V (Rder θ V τ X φ) := by
  obtain ⟨a, U, hU, hk⟩ := rapidDecSm_iff.1 h
  refine rapidDecSm_iff.2 ⟨Rder_mem_allDer a hX, U, hU, fun k h1 h2 g => ?_⟩
  have e : rTr V k φ = φ := funext (hk k h1 h2)
  exact (congrFun (Rder_rTr_fin h2 τ X φ) g).symm.trans (by rw [e])

theorem RapidDecSm.rTr_fin (h : RapidDecSm θ V φ) {k : GA D V} (hk : k ∈ GfC V) : RapidDecSm θ V (rTr V k φ) := by
  obtain ⟨a, U, hU, hl⟩ := rapidDecSm_iff.1 h
  refine rapidDecSm_iff.2 ⟨⟨fun n τs Xs hX g => ?_, fun l hl => ?_⟩, U.comap (MulAut.conj k⁻¹).toMonoidHom,
    hU.preimage (f := fun u => k⁻¹ * u * k⁻¹⁻¹) (by fun_prop), fun u h1 h2 g => ?_⟩
  · have hm : ∀ t : Fin n → ℝ, (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod ∈ GinfC V := fun t =>
      list_prod_mem fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact GlobalTheory.PointAtPlaceHom.atTau_mem V _ _
    simpa only [rTr, mul_assoc, GlobalTheory.PointAtPlaceHom.comm_of_mem V (hm _) hk] using a.1 n τs Xs hX (g * k)
  · have e : rWord θ V l (rTr V k φ) = rTr V k (rWord θ V l φ) :=
      wordAct_rel (R := fun f f' => f = rTr V k f') l (fun p _ _ _ e => e ▸ Rder_rTr_fin hk p.1 p.2 _) rfl
    rw [e]
    exact RapidDec.mul_right (a.2 l hl) k
  · have := hl (k⁻¹ * u * k⁻¹⁻¹) h1 (mul_mem (mul_mem (inv_mem hk) h2) (inv_mem (inv_mem hk))) (g * k)
    simpa [rTr, mul_assoc] using this

end Group

section Theta

open GlobalTheory.OrientedHeis

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {V W : HSp D}
  (μ : Measure (WO V W)) (𝓕 : Set (WO V W))

def l2O (f : WO V W → ℂ) : ℝ≥0∞ := eLpNorm f 2 (μ.restrict 𝓕)

def heisDer (a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool) (f : WO V W → ℂ) : WO V W → ℂ :=
  Formalism.IndefR.Datum.dRho (heisO ψ V W) θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) f

def sobO (d : ℕ) (f : WO V W → ℂ) : ℝ≥0∞ := wordSum (heisDer ψ θ) (l2O μ 𝓕) d f

variable (V W) in

def thetaLevel (U : AddSubgroup (WO V W)) : Submodule ℂ (WO V W → ℂ) where
  carrier := {f | IsThetaFunO ψ V W f ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W u f = f}
  add_mem' h h' := ⟨theta_add h.1 h'.1, fun u hu h0 =>
    ((GlobalTheory.FinTranslate.heisL V W ψ u).map_add _ _).trans (congrArg₂ _ (h.2 u hu h0) (h'.2 u hu h0))⟩
  zero_mem' := ⟨theta_zero, fun u _ _ => (GlobalTheory.FinTranslate.heisL V W ψ u).map_zero⟩
  smul_mem' c _ h := ⟨theta_smul c h.1, fun u hu h0 =>
    ((GlobalTheory.FinTranslate.heisL V W ψ u).map_smul _ _).trans (congrArg _ (h.2 u hu h0))⟩

theorem l2O_sq_eq_lintegral (f : WO V W → ℂ) : l2O μ 𝓕 f ^ 2 = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
  have := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ.restrict 𝓕) (p := 2) two_ne_zero
  simpa [l2O] using this

theorem l2O_smul (c : ℂ) (f : WO V W → ℂ) : l2O μ 𝓕 (c • f) = ‖c‖ₑ * l2O μ 𝓕 f := eLpNorm_const_smul c f 2 _

theorem l2O_add_le_of_continuous {f f' : WO V W → ℂ} (h : Continuous f) (h' : Continuous f') :
    l2O μ 𝓕 (f + f') ≤ l2O μ 𝓕 f + l2O μ 𝓕 f' :=
  have : BorelSpace (WO V W) := ⟨rfl⟩
  eLpNorm_add_le h.measurable.aestronglyMeasurable h'.measurable.aestronglyMeasurable one_le_two

theorem ipO_conj (f f' : WO V W → ℂ) : conj (ipO μ 𝓕 f f') = ipO μ 𝓕 f' f := by
  simp only [ipO, ← integral_conj, map_mul, Complex.conj_conj, mul_comm]

theorem ipO_smul_left (c : ℂ) (f f' : WO V W → ℂ) : ipO μ 𝓕 (c • f) f' = c * ipO μ 𝓕 f f' := by
  simp only [ipO, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem ipO_smul_right (c : ℂ) (f f' : WO V W → ℂ) : ipO μ 𝓕 f (c • f') = conj c * ipO μ 𝓕 f f' := by
  rw [← ipO_conj, ipO_smul_left, map_mul, ipO_conj]

theorem ipO_self (f : WO V W → ℂ) : ipO μ 𝓕 f f = nrm2 μ 𝓕 f := by
  simp only [ipO, nrm2, Complex.mul_conj', ← Complex.ofReal_pow]
  exact integral_complex_ofReal

theorem sqNormIntegralFundamentalDomain_eq_l2Norm_sq {f : WO V W → ℂ} (h : Continuous f) : nrm2 μ 𝓕 f = (l2O μ 𝓕 f).toReal ^ 2 := by
  have : BorelSpace (WO V W) := ⟨rfl⟩
  rw [← ENNReal.toReal_pow, l2O_sq_eq_lintegral, nrm2, GlobalTheory.Ker.ScalarProduct.integral_normSq_eq _ h.measurable]

theorem enorm_ipO_le {f f' : WO V W → ℂ} (h : Continuous f) (h' : Continuous f') :
    ‖ipO μ 𝓕 f f'‖ₑ ≤ l2O μ 𝓕 f * l2O μ 𝓕 f' := by
  have : BorelSpace (WO V W) := ⟨rfl⟩
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm]
  have := eLpNorm_smul_le_mul_eLpNorm (μ := μ.restrict 𝓕) (p := 2) (q := 2) (r := 1) (φ := f) (f := star f')
    h'.star.measurable.aestronglyMeasurable h.measurable.aestronglyMeasurable
  rwa [eLpNorm_star] at this

variable (V W) in

theorem exists_isCovolOne : ∃ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  exact (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO V W) (ratL W V) K hK hKc).1

variable {ψ θ μ 𝓕} {f f' f'' : WO V W → ℂ}

theorem measure_dom (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ) : μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ∞ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  obtain ⟨N, hN⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO V W) (ratL W V) K hK hKc).2 0
    continuous_const fun _ _ _ => rfl
  exact ⟨(hN μ 𝓕 hμ h𝓕).1, (hN μ 𝓕 hμ h𝓕).2.1⟩

theorem covolOne_unique {μ' : Measure (WO V W)} {𝓕' : Set (WO V W)} (h : IsCovolOne (ratL W V) μ 𝓕)
    (h' : IsCovolOne (ratL W V) μ' 𝓕') : μ' = μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ
  have h1 : IsAddFundamentalDomain (ratL W V) 𝓕 μ' := a2.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h2 := h1.measure_eq b2
  rw [b3, e, Measure.smul_apply, a3, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h2
  rw [e, h2, one_smul]

theorem mul_conj_periodic (hψ : IsStdChar D ψ (-1)) (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    ∀ γ ∈ ratL W V, ∀ w, f (γ + w) * conj (f' (γ + w)) = f w * conj (f' w) := by
  rintro _ ⟨γ, rfl⟩ w
  have := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.1.2.1 (-(symplOH V W (ratW W V γ) w)))
  have e := h.quasi γ w
  have e' := h'.quasi γ w
  change f (ratW W V γ + w) * conj (f' (ratW W V γ + w)) = _
  rw [e, e', map_mul]
  linear_combination (f w * conj (f' w)) * this

theorem ipO_dom_eq (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {𝓕' : Set (WO V W)} (h𝓕' : IsAddFundamentalDomain (ratL W V) 𝓕' μ) (h : IsThetaFunO ψ V W f)
    (h' : IsThetaFunO ψ V W f') : ipO μ 𝓕 f f' = ipO μ 𝓕' f f' := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact h𝓕.setIntegral_eq h𝓕' (f := fun w => f w * conj (f' w)) fun γ w => mul_conj_periodic hψ h h' γ γ.2 w

theorem memLp_theta (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    (h : IsThetaFunO ψ V W f) : MemLp f 2 (μ.restrict 𝓕) := by
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (measure_dom hμ h𝓕).2
  obtain ⟨C, hC⟩ := theta_bounded hψ h
  exact .of_bound h.cont.measurable.aestronglyMeasurable C (.of_forall hC)

theorem l2NormOnFundamentalDomain_thetaFunction_ne_top (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    (h : IsThetaFunO ψ V W f) : l2O μ 𝓕 f ≠ ∞ := (memLp_theta hψ hμ h𝓕 h).2.ne

theorem integrableOn_mul_conj (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ) (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    IntegrableOn (fun w => f w * conj (f' w)) 𝓕 μ :=
  (memLp_theta hψ hμ h𝓕 h).integrable_mul (memLp_theta hψ hμ h𝓕 h').star

theorem ipO_add_left (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') (h'' : IsThetaFunO ψ V W f'') :
    ipO μ 𝓕 (f + f') f'' = ipO μ 𝓕 f f'' + ipO μ 𝓕 f' f'' := by
  simp only [ipO, Pi.add_apply, add_mul]
  exact integral_add (integrableOn_mul_conj hψ hμ h𝓕 h h'') (integrableOn_mul_conj hψ hμ h𝓕 h' h'')

theorem ipO_add_right (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') (h'' : IsThetaFunO ψ V W f'') :
    ipO μ 𝓕 f (f' + f'') = ipO μ 𝓕 f f' + ipO μ 𝓕 f f'' := by
  rw [← ipO_conj, ipO_add_left hψ hμ h𝓕 h' h'' h, map_add, ipO_conj, ipO_conj]

theorem l2O_eq_zero_iff_of_isThetaFunO (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ) (h : IsThetaFunO ψ V W f) : l2O μ 𝓕 f = 0 ↔ f = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  refine ⟨fun h0 => eq_zero_of_lintegral_eq_zero (G := WO V W) (ratL W V) μ 𝓕 h𝓕 f h.cont (theta_norm_periodic hψ h) ?_,
    fun h0 => by simp [h0, l2O]⟩
  rw [← l2O_sq_eq_lintegral, h0, zero_pow two_ne_zero]

theorem ipO_self_eq_zero_iff (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ) (h : IsThetaFunO ψ V W f) : ipO μ 𝓕 f f = 0 ↔ f = 0 := by
  rw [ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 h.cont, ← l2O_eq_zero_iff_of_isThetaFunO hψ hμ h𝓕 h]
  simp [ENNReal.toReal_eq_zero_iff, l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ h𝓕 h]

theorem thetaL2_fundamentalDomain_indep (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {𝓕' : Set (WO V W)} (h𝓕' : IsAddFundamentalDomain (ratL W V) 𝓕' μ) (h : IsThetaFunO ψ V W f) :
    l2O μ 𝓕 f = l2O μ 𝓕' f := by
  have e := ipO_dom_eq hψ hμ h𝓕 h𝓕' h h
  rw [ipO_self, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 h.cont, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕' h.cont, Complex.ofReal_inj,
    pow_left_inj₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg two_ne_zero] at e
  exact (ENNReal.toReal_eq_toReal_iff' (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ h𝓕 h) (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ h𝓕' h)).1 e

theorem ipO_heisO (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') (u : WO V W) :
    ipO μ 𝓕 (heisO ψ V W u f) (heisO ψ V W u f') = ipO μ 𝓕 f f' := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  refine Eq.trans (integral_congr_ae (.of_forall fun w => ?_)) (GlobalTheory.HeisOrtho.setIntegral_add_right (G := WO V W)
    (ratL W V) μ 𝓕 h𝓕 (fun w => f w * conj (f' w)) (mul_conj_periodic hψ h h') u)
  have := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.1.2.1 (symplOH V W w u))
  simp only [heisO, map_mul]
  linear_combination (f (w + u) * conj (f' (w + u))) * this

theorem l2O_om_apply_eq_of_isThetaFunO {χS χT : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hom : IsWeilDatumO ψ V W χS χT om) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    (h : IsThetaFunO ψ V W f) (p : GA D V × GA D W) : l2O μ 𝓕 (om p f) = l2O μ 𝓕 f :=
  (ENNReal.pow_right_strictMono two_ne_zero).injective (by
    beta_reduce
    rw [l2O_sq_eq_lintegral, l2O_sq_eq_lintegral, hom.om_unit μ 𝓕 hμ h𝓕 p f h])

theorem ipO_om {χS χT : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hom : IsWeilDatumO ψ V W χS χT om) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') (p : GA D V × GA D W) :
    ipO μ 𝓕 (om p f) (om p f') = ipO μ 𝓕 f f' := by
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (measure_dom hμ h𝓕).2
  have hb : ∀ f, IsThetaFunO ψ V W f → GlobalTheory.Ker.ScalarProduct.BM f := fun f h =>
    ⟨h.cont.measurable, theta_bounded hom.std h⟩
  have e : ∀ c : ℂ, ∫ w in 𝓕, ‖(om p f + c • om p f') w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖(f + c • f') w‖ ^ 2 ∂μ := fun c => by
    have hs := theta_add h (theta_smul c h')
    rw [← map_smul, ← map_add]
    exact (sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 (hom.om_pres p _ hs).cont).trans (by
      rw [l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hs]; exact (sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hs.cont).symm)
  simp only [ipO]
  rw [GlobalTheory.Ker.ScalarProduct.integral_polar _ (hb _ (hom.om_pres p f h)) (hb _ (hom.om_pres p f' h')),
    GlobalTheory.Ker.ScalarProduct.integral_polar _ (hb f h) (hb f' h'), e, e, e, e]

end Theta

section Sob

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
  {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {f f' : WO V W → ℂ}

theorem sobO_zero : sobO ψ θ μ 𝓕 0 f = l2O μ 𝓕 f := wordSum_zero _ _ _

theorem sobO_mono {d d' : ℕ} (h : d ≤ d') : sobO ψ θ μ 𝓕 d f ≤ sobO ψ θ μ 𝓕 d' f := wordSum_mono h f

theorem sobO_heisDer_le (d : ℕ) (a : D.what₂.Tau × Fin W.rank × Fin V.rank × Bool) :
    sobO ψ θ μ 𝓕 d (heisDer ψ θ a f) ≤ sobO ψ θ μ 𝓕 (d + 1) f := wordSum_letter_le d a f

theorem dRho_smul (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (c : ℂ) (f : WO V W → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f := by
  funext w
  simp only [Formalism.IndefR.Datum.dRho, heisO, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact deriv_const_mul_field c

theorem dRho_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (f + f') =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f + Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f' := by
  funext w
  have hL := isRealDir_lineAt (S := V) (T := W) hθ τ z
  simp only [Formalism.IndefR.Datum.dRho, Pi.add_apply]
  rw [← deriv_fun_add (hasDerivAt_heisO hθ hψ hL h w 0).differentiableAt
    (hasDerivAt_heisO hθ hψ hL h' w 0).differentiableAt]
  simp only [heisO, Pi.add_apply, mul_add]

theorem theta_word (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool))
    (h : IsThetaFunO ψ V W f) : IsThetaFunO ψ V W (wordAct (heisDer ψ θ) l f) :=
  wordAct_rel (B := heisDer ψ θ) (R := fun g _ => IsThetaFunO ψ V W g) l
    (fun a _ _ _ hg => theta_dRho hθ hψ a.1 _ hg) (y := f) h

theorem sobO_ne_top (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ) (h : IsThetaFunO ψ V W f) (d : ℕ) : sobO ψ θ μ 𝓕 d f ≠ ∞ :=
  wordSum_ne_top_iff.2 fun l _ => l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ h𝓕 (theta_word hψ hθ l h)

theorem sobO_smul (d : ℕ) (c : ℂ) : sobO ψ θ μ 𝓕 d (c • f) = ‖c‖ₑ * sobO ψ θ μ 𝓕 d f :=
  wordSum_eq_mul fun l => by
    rw [← l2O_smul]
    exact congrArg _ (wordAct_rel (R := fun g g' => g = c • g') l (fun a _ _ _ e => e ▸ dRho_smul a.1 _ c _) rfl)

theorem sobO_add_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f')
    (d : ℕ) : sobO ψ θ μ 𝓕 d (f + f') ≤ sobO ψ θ μ 𝓕 d f + sobO ψ θ μ 𝓕 d f' := by
  refine wordSum_le_add fun l => le_of_eq_of_le (congrArg _ ?_)
    (l2O_add_le_of_continuous μ 𝓕 (theta_word hψ hθ l h).cont (theta_word hψ hθ l h').cont)
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, ih]
    exact dRho_add hψ hθ a.1 _ (theta_word hψ hθ l h) (theta_word hψ hθ l h')

theorem sobO_eq_zero_iff (hψ : IsStdChar D ψ (-1)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ) (h : IsThetaFunO ψ V W f) (d : ℕ) : sobO ψ θ μ 𝓕 d f = 0 ↔ f = 0 := by
  refine ⟨fun h0 => (l2O_eq_zero_iff_of_isThetaFunO hψ hμ h𝓕 h).1 (le_zero_iff.1 ?_), fun h0 => ?_⟩
  · exact (sobO_zero (ψ := ψ) (θ := θ)).ge.trans ((sobO_mono d.zero_le).trans h0.le)
  · have := sobO_smul (ψ := ψ) (θ := θ) (μ := μ) (𝓕 := 𝓕) (f := f) d 0
    rwa [zero_smul, enorm_zero, zero_mul, ← h0] at this

theorem isTheta_iff_level : IsThetaFunO ψ V W f ↔
    ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ f ∈ thetaLevel ψ V W U :=
  ⟨fun h => h.level.imp fun _ hU => ⟨hU.1, h, hU.2⟩, fun ⟨_, _, h⟩ => h.1⟩

theorem thetaLevel_anti {U U' : AddSubgroup (WO V W)} (h : U ≤ U') : thetaLevel ψ V W U' ≤ thetaLevel ψ V W U :=
  fun _ hf => ⟨hf.1, fun u hu => hf.2 u (h hu)⟩

theorem dRho_mem_thetaLevel (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {U : AddSubgroup (WO V W)}
    (h : f ∈ thetaLevel ψ V W U) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f ∈ thetaLevel ψ V W U :=
  ⟨theta_dRho hθ hψ τ z h.1, fun u hu h0 => by rw [← GlobalTheory.FinTranslate.dRho_heisO hθ h0, h.2 u hu h0]⟩

end Sob

section Examples

variable {D : D7}

open scoped ComplexOrder in

theorem exists_theta_posSp (D : D7) (m n : ℕ) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (WO (posSp D m) (posSp D n))) (𝓕 : Set (WO (posSp D m) (posSp D n)))
    (U : AddSubgroup (WO (posSp D m) (posSp D n))) (f : WO (posSp D m) (posSp D n) → ℂ),
    IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ IsCovolOne (ratL (posSp D n) (posSp D m)) μ 𝓕 ∧
      IsOpen (U : Set (WO (posSp D m) (posSp D n))) ∧ f ∈ thetaLevel ψ _ _ U ∧ ipO μ 𝓕 f f ≠ 0 ∧
      ∀ d, sobO ψ θ μ 𝓕 d f ≠ 0 ∧ sobO ψ θ μ 𝓕 d f ≠ ∞ := by
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  have hc : ∀ k τ, IsCartanInv (gramAt D (posSp D k) τ) 1 := fun k τ => by
    rw [gramAt_posSp]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ (posSp D m) (posSp D n) _ _ (hc m) (hc n) _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  have h : IsThetaFunO ψ _ _ f := by simpa using (hf 1).1
  obtain ⟨μ, 𝓕, hm⟩ := exists_isCovolOne (posSp D m) (posSp D n)
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 h
  exact ⟨ψ, θ, μ, 𝓕, U, f, hψ, hθ, hm, hU, hl, mt (ipO_self_eq_zero_iff hψ hm.1 hm.2.1 h).1 f0, fun d =>
    ⟨mt (sobO_eq_zero_iff hψ hm.1 hm.2.1 h d).1 f0, sobO_ne_top hψ hθ hm.1 hm.2.1 h d⟩⟩

example {V W : HSp D} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (h : μ 𝓕 = 1) :
    ipO μ 𝓕 (fun _ => 1) (fun _ => Complex.I) = -Complex.I := by
  have : μ.real 𝓕 = 1 := by rw [Measure.real, h, ENNReal.toReal_one]
  rw [ipO, setIntegral_const, this, one_smul, one_mul, Complex.conj_I]

example (V : HSp D) : growthSize V 1 (fun g => (height V g : ℂ)) = 1 := by
  simp [growthSize, abs_of_pos (height_pos V _), (height_pos V _).ne']

example (θ : InfFam D) (V : HSp D) (N : ℕ) (c : ℂ) : growthSob θ V 1 N (fun _ => c) = ‖c‖ₑ := by
  simp [growthSob, wordSum_one, glDer, RderC_const, growthSize_const]

end Examples

end GlobalTheory.Size

end
