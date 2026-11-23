import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabfin
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

noncomputable section
namespace Formalism.MainNotions.Gaps.LevGap
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section DefCong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

def CongAt (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (g : GL n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i j, ∃ s ∈ intV E v, (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
    (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j = (c : E ⊗[F] v.adicCompletion F) * s

end DefCong

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem rsmul_tmul (a : R) (e : E) (r : R) : a • (e ⊗ₜ[F] r) = e ⊗ₜ[F] (a * r) := by
  rw [Algebra.smul_def]
  show ((1 : E) ⊗ₜ[F] a) * (e ⊗ₜ[F] r) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def comb {ι : Type} [Fintype ι] (e : ι → E) : (ι → R) →ₗ[R] E ⊗[F] R :=
  Fintype.linearCombination R (fun i => e i ⊗ₜ[F] (1 : R))

theorem comb_apply {ι : Type} [Fintype ι] (e : ι → E) (a : ι → R) :
    comb (F := F) R e a = ∑ i, e i ⊗ₜ[F] a i := by
  unfold comb
  rw [Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rsmul_tmul, mul_one]

theorem comb_surj {ι : Type} [Fintype ι] (e : ι → E) (he : Submodule.span F (Set.range e) = ⊤) :
    Function.Surjective (comb (F := F) R e) := by
  intro x
  rw [← LinearMap.mem_range]
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a r =>
    have ha : a ∈ Submodule.span F (Set.range e) := by rw [he]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 ha
    refine ⟨fun i => c i • r, ?_⟩
    rw [comb_apply, ← hc, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul]

def crd {ι : Type} (b : Module.Basis ι F E) (i : ι) : E ⊗[F] R →ₗ[R] R where
  toFun x := TensorProduct.lid F R ((b.coord i).rTensor R x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add, map_add, smul_add]
    | tmul e r =>
      rw [rsmul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        TensorProduct.lid_tmul, RingHom.id_apply, smul_eq_mul, mul_smul_comm]

theorem crd_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (e : E) (r : R) :
    crd R b i (e ⊗ₜ[F] r) = b.repr e i • r := by
  show TensorProduct.lid F R ((b.coord i).rTensor R (e ⊗ₜ[F] r)) = _
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply]

theorem comb_crd {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (x : E ⊗[F] R) :
    comb R b (fun i => crd R b i x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact map_zero _
  | add x y hx hy =>
    have : (fun i => crd R b i (x + y)) = (fun i => crd R b i x) + (fun i => crd R b i y) := by
      ext i; simp
    rw [this, map_add, hx, hy]
  | tmul e r =>
    rw [comb_apply]
    simp only [crd_tmul]
    conv_rhs => rw [← b.sum_repr e, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul]

variable [TopologicalSpace R] [IsTopologicalRing R]

local instance topT : TopologicalSpace (E ⊗[F] R) := tensTopL (F := F) (E := E) R

local instance modT : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩

variable [FiniteDimensional F E]

theorem finT : Module.Finite R (E ⊗[F] R) :=
  Module.Finite.of_surjective (comb (F := F) R (Module.finBasis F E))
    (comb_surj R _ (Module.finBasis F E).span_eq)

theorem ringT : IsTopologicalRing (E ⊗[F] R) :=
  haveI := finT (F := F) (E := E) R
  IsModuleTopology.isTopologicalRing R (E ⊗[F] R)

theorem t2T [T2Space R] : T2Space (E ⊗[F] R) := by
  refine T2Space.of_injective_continuous
    (f := fun x : E ⊗[F] R => fun i => crd R (Module.finBasis F E) i x) ?_ ?_
  · intro x y h
    rw [← comb_crd R (Module.finBasis F E) x, ← comb_crd R (Module.finBasis F E) y]
    exact congrArg _ h
  · exact continuous_pi fun i => IsModuleTopology.continuous_of_linearMap (crd R (Module.finBasis F E) i)

theorem comb_cont {ι : Type} [Fintype ι] (e : ι → E) : Continuous (comb (F := F) R e) :=
  haveI := IsModuleTopology.toContinuousAdd R (E ⊗[F] R)
  IsModuleTopology.continuous_of_linearMap _

theorem comb_open {ι : Type} [Fintype ι] (e : ι → E) (he : Submodule.span F (Set.range e) = ⊤) :
    IsOpenMap (comb (F := F) R e) :=
  haveI := IsModuleTopology.toContinuousAdd R (E ⊗[F] R)
  IsModuleTopology.isOpenMap_of_surjective (comb_surj R e he)

theorem sigR_cont (σ : E →ₐ[F] E) : Continuous (sigR σ R) := by
  have := ringT (F := F) (E := E) R
  refine IsModuleTopology.continuous_of_ringHom (R := R) (sigR σ R) ?_
  have h : (sigR σ R).comp (algebraMap R (E ⊗[F] R)) = algebraMap R (E ⊗[F] R) := by
    ext a
    show (Algebra.TensorProduct.map σ (AlgHom.id F R)) ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] a
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [h]
  exact continuous_algebraMap R (E ⊗[F] R)

theorem isClosed_UPts [T2Space R] {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E)
    (J : Matrix n n E) : IsClosed (UPts σ J R : Set (GL n (E ⊗[F] R))) := by
  have := ringT (F := F) (E := E) R
  have := t2T (F := F) (E := E) R
  have hc : Continuous fun g : GL n (E ⊗[F] R) =>
      cT (sigR σ R) (g : Matrix n n (E ⊗[F] R)) * J.map (inclE (F := F) R) * (g : Matrix n n (E ⊗[F] R)) := by
    unfold cT
    exact (((Units.continuous_val.matrix_map (sigR_cont R σ)).matrix_transpose).matrix_mul
      continuous_const).matrix_mul Units.continuous_val
  exact isClosed_eq hc continuous_const

end Gen

section GLc

variable {M : Type} [CommRing M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_GL_of (C : Set M) (hC : IsCompact C) :
    IsCompact {g : GL n M | ∀ i j, (g : Matrix n n M) i j ∈ C ∧ ((g⁻¹ : GL n M) : Matrix n n M) i j ∈ C} := by
  have hCM : IsCompact {X : Matrix n n M | ∀ i j, X i j ∈ C} := by
    have := isCompact_univ_pi (fun _ : n => isCompact_univ_pi (fun _ : n => hC))
    have e : {X : Matrix n n M | ∀ i j, X i j ∈ C} =
        (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n => C : Set (n → n → M)) := by
      ext X; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]; exact this
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix n n M)).isCompact_preimage
    (hCM.prod (hCM.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, Set.mem_image]
  constructor
  · intro h
    exact ⟨fun i j => (h i j).1, _, fun i j => (h i j).2, rfl⟩
  · rintro ⟨h1, X, hX, hXe⟩ i j
    have : X = ((g⁻¹ : GL n M) : Matrix n n M) := MulOpposite.op_injective hXe
    exact ⟨h1 i j, this ▸ hX i j⟩

end GLc

section Dec

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
variable {R : Type} [CommRing R] [Algebra F R] (O : Subring R)

theorem tmul_mem_tensInt (e : 𝓞 E) {y : R} (hy : y ∈ O) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] y ∈ tensInt (F := F) R (intOE E) O := by
  have : algebraMap (𝓞 E) E e ⊗ₜ[F] y =
      (algebraMap (𝓞 E) E e ⊗ₜ[F] (1 : R)) * ((1 : E) ⊗ₜ[F] y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this]
  exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩))

def QD {m : ℕ} (b : Fin m → 𝓞 E) (s : E ⊗[F] R) : Prop :=
  ∃ r : Fin m → R, (∀ j, r j ∈ O) ∧ s = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j

theorem QD_zero {m : ℕ} (b : Fin m → 𝓞 E) : QD (F := F) O b 0 :=
  ⟨0, fun _ => zero_mem _, by simp⟩

theorem QD_add {m : ℕ} (b : Fin m → 𝓞 E) {x y : E ⊗[F] R} (hx : QD O b x) (hy : QD O b y) :
    QD O b (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  refine ⟨r + r', fun j => add_mem (hr j) (hr' j), ?_⟩
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_add _ _ _).symm

theorem QD_neg {m : ℕ} (b : Fin m → 𝓞 E) {x : E ⊗[F] R} (hx : QD O b x) : QD O b (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  refine ⟨-r, fun j => neg_mem (hr j), ?_⟩
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_neg _ _).symm

theorem QD_sum {m : ℕ} (b : Fin m → 𝓞 E) {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] R)
    (h : ∀ i ∈ s, QD O b (f i)) : QD O b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (QD O b) (fun _ _ hx hy => QD_add O b hx hy) (QD_zero O b) h

theorem QD_tmul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (e : 𝓞 E) {y : R} (hy : y ∈ O) : QD (F := F) O b (algebraMap (𝓞 E) E e ⊗ₜ[F] y) := by
  have he : e ∈ Submodule.span ℤ (Set.range b) := by rw [hb]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 he
  refine ⟨fun j => c j • y, fun j => zsmul_mem hy _, ?_⟩
  rw [← hc, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, TensorProduct.smul_tmul]

theorem QD_mul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : E ⊗[F] R} (hx : QD O b x) (hy : QD O b y) : QD O b (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine QD_sum O b _ _ fun j _ => QD_sum O b _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
  exact QD_tmul O b hb _ (mul_mem (hr j) (hr' k))

theorem QD_of_mem {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) O) : QD O b s := by
  refine Subring.closure_induction (p := fun s _ => QD O b s) ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact QD_tmul O b hb e' (one_mem _)
    · have := QD_tmul (F := F) O b hb 1 hy
      rwa [map_one] at this
  · exact QD_zero O b
  · have := QD_tmul (F := F) O b hb 1 (one_mem O)
    rwa [map_one, ← Algebra.TensorProduct.one_def] at this
  · intro x y _ _ hx hy; exact QD_add O b hx hy
  · intro x _ hx; exact QD_neg O b hx
  · intro x y _ _ hx hy; exact QD_mul O b hb hx hy

variable [NumberField F]

theorem crd_int (hO : ∀ t : 𝓞 F, algebraMap F R (algebraMap (𝓞 F) F t) ∈ O)
    {ι : Type} (b : Module.Basis ι F E) {m : ℕ} (β : Fin m → 𝓞 E)
    (hβ : Submodule.span ℤ (Set.range β) = ⊤) (N1 : F)
    (hN1 : ∀ j l, ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = N1 * b.repr (algebraMap (𝓞 E) E (β j)) l)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) O) (l : ι) :
    algebraMap F R N1 * crd R b l s ∈ O := by
  obtain ⟨r, hr, rfl⟩ := QD_of_mem O β hβ hs
  rw [map_sum, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  obtain ⟨t, ht⟩ := hN1 j l
  rw [crd_tmul, Algebra.smul_def, ← mul_assoc, ← map_mul, ← ht]
  exact mul_mem (hO t) (hr j)

theorem crd_natCast_mul {ι : Type} (b : Module.Basis ι F E) (l : ι) (k : ℕ) (x : E ⊗[F] R) :
    crd R b l ((k : E ⊗[F] R) * x) = (k : R) * crd R b l x := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem latS_den (Λ : Submodule (𝓞 E) (n → E)) (N' : ℕ)
    (h2 : ∀ x ∈ Λ, ∀ i, (N' : E) * x i ∈ intOE E) {y : n → E ⊗[F] R}
    (hy : y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ) (i : n) :
    (N' : E ⊗[F] R) * y i ∈ tensInt (F := F) R (intOE E) O := by
  unfold latS at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x0, hx0, rfl⟩ := hx
    have : (N' : E ⊗[F] R) * inclE (F := F) R (x0 i) = inclE (F := F) R ((N' : E) * x0 i) := by
      rw [map_mul, map_natCast]
    show (N' : E ⊗[F] R) * inclE (F := F) R (x0 i) ∈ _
    rw [this]
    exact Subring.subset_closure (Or.inl ⟨⟨_, h2 x0 hx0 i⟩, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [Pi.add_apply, mul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have : (N' : E ⊗[F] R) * (a • x) i = (a : E ⊗[F] R) * ((N' : E ⊗[F] R) * x i) := by
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
    rw [this]
    exact mul_mem a.2 hx

theorem stab_entry (Λ : Submodule (𝓞 E) (n → E)) (N : ℕ)
    (h1 : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (g : GL n (E ⊗[F] R))
    (hg : g ∈ stabGL (latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ)) (j : n) :
    ∃ y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ,
      ∀ i, y i = (N : E ⊗[F] R) * (g : Matrix n n (E ⊗[F] R)) i j := by
  refine ⟨_, (hg _).1 (Submodule.subset_span ⟨_, h1 j, rfl⟩), fun i => ?_⟩
  show ∑ k, (g : Matrix n n (E ⊗[F] R)) i k *
    inclE (F := F) R (((N : E) • (Pi.single j 1 : n → E)) k) = _
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro k _ hk; simp [hk]
  · simp

theorem entry_bd (hO : ∀ t : 𝓞 F, algebraMap F R (algebraMap (𝓞 F) F t) ∈ O)
    {ι : Type} (b : Module.Basis ι F E) {m : ℕ} (β : Fin m → 𝓞 E)
    (hβ : Submodule.span ℤ (Set.range β) = ⊤) (N1 : F)
    (hN1 : ∀ j l, ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = N1 * b.repr (algebraMap (𝓞 E) E (β j)) l)
    (Λ : Submodule (𝓞 E) (n → E)) (N N' : ℕ)
    (h1 : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ)
    (h2 : ∀ x ∈ Λ, ∀ i, (N' : E) * x i ∈ intOE E) (g : GL n (E ⊗[F] R))
    (hg : g ∈ stabGL (latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ)) (i j : n) (l : ι) :
    algebraMap F R (N1 * N' * N) * crd R b l ((g : Matrix n n (E ⊗[F] R)) i j) ∈ O := by
  obtain ⟨y, hy, hyi⟩ := stab_entry O Λ N h1 g hg j
  have h := crd_int O hO b β hβ N1 hN1 (latS_den O Λ N' h2 hy i) l
  rw [hyi, crd_natCast_mul, crd_natCast_mul] at h
  have e : algebraMap F R (N1 * N' * N) * crd R b l ((g : Matrix n n (E ⊗[F] R)) i j) =
      algebraMap F R N1 * ((N' : R) * ((N : R) * crd R b l ((g : Matrix n n (E ⊗[F] R)) i j))) := by
    rw [map_mul, map_mul, map_natCast, map_natCast]; ring
  rw [e]; exact h

end Dec

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem compact_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) := by
  have h1 : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have h2 : IsClosed ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isClosed_valuationSubring _
  have h3 : CompleteSpace (v.adicCompletionIntegers F) := h2.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
    ⟨h3, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), h1⟩

theorem isCompact_intAd : IsCompact (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) := compact_Ov
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_intAd : IsOpen (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

open scoped RestrictedProduct in
theorem t2Space_adeleRing_numberField : T2Space 𝔸 :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem isCompact_scaled (c : F) (hc : c ≠ 0) :
    IsCompact {a : 𝔸 | algebraMap F 𝔸 c * a ∈ intAd F} := by
  have e : {a : 𝔸 | algebraMap F 𝔸 c * a ∈ intAd F} =
      (fun y => algebraMap F 𝔸 c⁻¹ * y) '' (intAd F : Set 𝔸) := by
    ext a
    constructor
    · intro h
      refine ⟨_, h, ?_⟩
      show algebraMap F 𝔸 c⁻¹ * (algebraMap F 𝔸 c * a) = a
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    · rintro ⟨y, hy, rfl⟩
      show algebraMap F 𝔸 c * (algebraMap F 𝔸 c⁻¹ * y) ∈ intAd F
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
      exact hy
  rw [e]
  exact isCompact_intAd.image (continuous_const.mul continuous_id)

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem crd_prV {ι : Type} (b : Module.Basis ι F E) (l : ι) (v : HeightOneSpectrum (𝓞 F))
    (x : E ⊗[F] 𝔸) : crd (v.adicCompletion F) b l (prV (E := E) v x) = (crd 𝔸 b l x) v := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]; rfl
  | tmul e a =>
    rw [Formalism.UG.P.afsplit_prV_tmul, crd_tmul, crd_tmul, Formalism.UG.P.afsplit_smul_apply]

theorem hO_v (v : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F t) ∈
      (v.adicCompletionIntegers F).toSubring := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  exact Formalism.UG.P.levelaf_int_mem_v v t

theorem exists_int_span : ∃ e : Fin (Module.finrank F E) → 𝓞 E,
    Submodule.span F (Set.range fun l => algebraMap (𝓞 E) E (e l)) = ⊤ := by
  set b := Module.finBasis F E
  obtain ⟨d, hd, -, hdi⟩ := Formalism.UG.P.sf_den (fun l => b l)
  refine ⟨fun l => ⟨d * b l, hdi l⟩, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ l, b.repr (d⁻¹ * x) l • (d * b l) := by
    simp_rw [← mul_smul_comm]
    rw [← Finset.mul_sum, b.sum_repr, mul_inv_cancel_left₀ hd]
  rw [hx]
  exact sum_mem fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem prV_comb_mem {ι : Type} [Fintype ι] (e : ι → 𝓞 E) (a : ι → 𝔸) (ha : ∀ l, a l ∈ intAd F)
    (v : HeightOneSpectrum (𝓞 F)) :
    prV (E := E) v (comb 𝔸 (fun l => algebraMap (𝓞 E) E (e l)) a) ∈ intV E v := by
  rw [comb_apply, map_sum]
  refine sum_mem fun l _ => ?_
  rw [Formalism.UG.P.afsplit_prV_tmul]
  exact tmul_mem_tensInt _ (e l) (ha l v)

theorem exists_den {ι : Type} [Finite ι] (b : Module.Basis ι F E) {m : ℕ} (β : Fin m → 𝓞 E) :
    ∃ N1 : F, N1 ≠ 0 ∧
      ∀ j l, ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = N1 * b.repr (algebraMap (𝓞 E) E (β j)) l := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun p : Fin m × ι => b.repr (algebraMap (𝓞 E) E (β p.1)) p.2)
  refine ⟨algebraMap (𝓞 F) F d, ?_, fun j l => ?_⟩
  · intro h
    apply nonZeroDivisors.coe_ne_zero d
    exact (IsFractionRing.injective (𝓞 F) F) (by simp at h)
  · obtain ⟨t, ht⟩ := hd (j, l)
    exact ⟨t, by rw [ht, Algebra.smul_def]⟩

end Adele

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance topT' (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) := tensTopL (F := F) (E := E) R

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL n A) (i j : n) :
    (bc φ g : Matrix n n B) i j = φ ((g : Matrix n n A) i j) := rfl

theorem congAt_of {ι : Type} [Fintype ι] (e : ι → 𝓞 E) (c : ℕ) (hc : c ≠ 0) (g : GL n (E ⊗[F] 𝔸))
    (hg : ∀ i j, algebraMap F (E ⊗[F] 𝔸) (c : F)⁻¹ * ((g : Matrix n n (E ⊗[F] 𝔸)) i j -
      (1 : Matrix n n (E ⊗[F] 𝔸)) i j) ∈
        comb 𝔸 (fun l => algebraMap (𝓞 E) E (e l)) '' (Set.pi Set.univ fun _ => (intAd F : Set 𝔸)))
    (v : HeightOneSpectrum (𝓞 F)) : CongAt v c (bc (prV (E := E) v) g) := by
  intro i j
  obtain ⟨a, ha, hae⟩ := hg i j
  refine ⟨_, prV_comb_mem e a (fun l => ha l trivial) v, ?_⟩
  have h1 : ((c : ℕ) : E ⊗[F] 𝔸) * algebraMap F (E ⊗[F] 𝔸) (c : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (E ⊗[F] 𝔸)) c, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hc), map_one]
  have h3 : (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j =
      prV (E := E) v ((1 : Matrix n n (E ⊗[F] 𝔸)) i j) := by
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [hae, bc_apply, h3, ← map_sub, ← map_natCast (prV (E := E) v) c, ← map_mul, ← mul_assoc, h1,
    one_mul]

theorem level_top (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
    (N N' c : ℕ) (hN : N ≠ 0) (hN' : N' ≠ 0) (hc : c ≠ 0)
    (h1 : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ)
    (h2 : ∀ x ∈ Λ, ∀ i, (N' : E) * x i ∈ intOE E)
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F)))
    (hlev : ∀ v, Uloc v ≤ levelVL σ J v Λ)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 F), ∀ g ∈ UPts σ J (v.adicCompletion F), CongAt v c g → CongAt v c g⁻¹ → g ∈ Uloc v)
    (U : Subgroup (GL n (E ⊗[F] 𝔸)))
    (hU : ∀ x, x ∈ U ↔ x ∈ UPts σ J 𝔸 ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v) :
    IsCompact (U : Set (GL n (E ⊗[F] 𝔸))) ∧ IsOpen {x : UPts σ J 𝔸 | (x : GL n (E ⊗[F] 𝔸)) ∈ U} := by
  have iR : IsTopologicalRing (E ⊗[F] 𝔸) := ringT (F := F) (E := E) 𝔸
  have iA : T2Space 𝔸 := t2Space_adeleRing_numberField
  have iT : T2Space (E ⊗[F] 𝔸) := t2T (F := F) (E := E) 𝔸

  obtain ⟨e, he⟩ := exists_int_span (F := F) (E := E)
  set O1 : Set (E ⊗[F] 𝔸) :=
    comb 𝔸 (fun l => algebraMap (𝓞 E) E (e l)) '' (Set.pi Set.univ fun _ => (intAd F : Set 𝔸)) with hO1
  have hO1o : IsOpen O1 :=
    comb_open 𝔸 _ he _ (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_intAd)
  have hO10 : (0 : E ⊗[F] 𝔸) ∈ O1 := ⟨0, fun _ _ => zero_mem _, map_zero _⟩
  set ci : E ⊗[F] 𝔸 := algebraMap F (E ⊗[F] 𝔸) (c : F)⁻¹ with hci
  set W : Set (GL n (E ⊗[F] 𝔸)) := {g | ∀ i j,
    ci * ((g : Matrix n n (E ⊗[F] 𝔸)) i j - (1 : Matrix n n (E ⊗[F] 𝔸)) i j) ∈ O1 ∧
    ci * (((g⁻¹ : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) i j -
      (1 : Matrix n n (E ⊗[F] 𝔸)) i j) ∈ O1} with hW
  have hWo : IsOpen W := by
    rw [hW]
    simp only [Set.ofPred_forall, Set.ofPred_and]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
    · exact hO1o.preimage (continuous_const.mul
        ((Units.continuous_val.matrix_elem i j).sub continuous_const))
    · exact hO1o.preimage (continuous_const.mul
        ((Units.continuous_coe_inv.matrix_elem i j).sub continuous_const))
  have hW1 : (1 : GL n (E ⊗[F] 𝔸)) ∈ W := by
    intro i j
    simp only [inv_one, Units.val_one, sub_self, mul_zero]
    exact ⟨hO10, hO10⟩
  have hWU : ∀ g ∈ UPts σ J 𝔸, g ∈ W → g ∈ U := by
    intro g hg hgW
    refine (hU g).2 ⟨hg, fun v => hcong v _ (Formalism.UG.P.afsplit_bc_mem σ J v g hg) ?_ ?_⟩
    · exact congAt_of e c hc g (fun i j => (hgW i j).1) v
    · rw [← map_inv]
      exact congAt_of e c hc g⁻¹ (fun i j => (hgW i j).2) v
  have hopen : IsOpen ((U.subgroupOf (UPts σ J 𝔸) : Subgroup (UPts σ J 𝔸)) : Set (UPts σ J 𝔸)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    refine Filter.mem_of_superset ((hWo.preimage continuous_subtype_val).mem_nhds hW1) ?_
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hWU x x.2 hx)
  have hclosed : IsClosed (U : Set (GL n (E ⊗[F] 𝔸))) := by
    have hc1 := Subgroup.isClosed_of_isOpen _ hopen
    have hc2 := (isClosed_UPts 𝔸 σ J).isClosedEmbedding_subtypeVal.isClosedMap _ hc1
    convert hc2 using 1
    ext g
    constructor
    · intro hg
      exact ⟨⟨g, ((hU g).1 hg).1⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hx
  refine ⟨?_, hopen⟩

  set b := Module.finBasis F E
  set β := Module.finBasis ℤ (𝓞 E)
  obtain ⟨N1, hN10, hN1⟩ := exists_den b (fun j => β j)
  set c' : F := N1 * N' * N with hc'
  have hc'0 : c' ≠ 0 :=
    mul_ne_zero (mul_ne_zero hN10 (Nat.cast_ne_zero.2 hN')) (Nat.cast_ne_zero.2 hN)
  set C : Set (E ⊗[F] 𝔸) :=
    comb 𝔸 b '' (Set.pi Set.univ fun _ => {a : 𝔸 | algebraMap F 𝔸 c' * a ∈ intAd F}) with hC
  have hCc : IsCompact C :=
    (isCompact_univ_pi fun _ => isCompact_scaled c' hc'0).image (comb_cont 𝔸 _)
  have hent : ∀ g ∈ U, ∀ i j, (g : Matrix n n (E ⊗[F] 𝔸)) i j ∈ C := by
    intro g hg i j
    refine ⟨fun l => crd 𝔸 b l ((g : Matrix n n (E ⊗[F] 𝔸)) i j), fun l _ v => ?_, comb_crd 𝔸 b _⟩
    have hs := (Subgroup.mem_inf.1 (hlev v (((hU g).1 hg).2 v))).2
    have := entry_bd (v.adicCompletionIntegers F).toSubring (hO_v v) b (fun j => β j)
      β.span_eq N1 hN1 Λ N N' h1 h2 _ hs i j l
    rw [bc_apply, crd_prV] at this
    exact this
  refine (isCompact_GL_of C hCc).of_isClosed_subset hclosed ?_
  intro g hg i j
  exact ⟨hent g hg i j, hent g⁻¹ (inv_mem hg) i j⟩

theorem level_top' (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
    (N N' c : ℕ) (hN : N ≠ 0) (hN' : N' ≠ 0) (hc : c ≠ 0)
    (h1 : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ)
    (h2 : ∀ x ∈ Λ, ∀ i, (N' : E) * x i ∈ intOE E)
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F)))
    (hlev : ∀ v, Uloc v ≤ levelVL σ J v Λ)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 F), ∀ g ∈ UPts σ J (v.adicCompletion F),
      CongAt v c g → CongAt v c g⁻¹ → g ∈ Uloc v)
    (U : Subgroup (GL n (E ⊗[F] 𝔸)))
    (hU : ∀ x, x ∈ U ↔ x ∈ UPts σ J 𝔸 ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v) :
    (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F);
      IsCompact (U : Set (GL n (E ⊗[F] 𝔸)))) ∧
    (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F);
      IsOpen {x : UPts σ J 𝔸 | (x : GL n (E ⊗[F] 𝔸)) ∈ U}) :=
  level_top σ J Λ N N' c hN hN' hc h1 h2 Uloc hlev hcong U hU

end Main

section Bridge

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem exists_nat_smul_mem (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ := by
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.csGlob_single Λ hspan
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, fun j => ?_⟩
  have h1 : ((m.natAbs : ℕ) : E) • (Pi.single j 1 : n → E) = Pi.single j ((m.natAbs : ℤ) : E) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one, Int.cast_natCast]
  rw [h1]
  rcases Int.natAbs_eq m with h | h
  · rw [← h]; exact hm j
  · have h2 : ((m.natAbs : ℤ) : E) = -(m : E) := by
      have h3 : (m.natAbs : ℤ) = -m := by omega
      rw [h3, Int.cast_neg]
    rw [h2, Pi.single_neg]; exact neg_mem (hm j)

theorem mem_stabGL_of {A R : Type} [CommRing A] [CommRing R] [Algebra R A] (Λ : Submodule R (n → A))
    (g : GL n A) (h1 : ∀ y ∈ Λ, (g : Matrix n n A) *ᵥ y ∈ Λ)
    (h2 : ∀ y ∈ Λ, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ y ∈ Λ) : g ∈ stabGL Λ := by
  change ∀ x : n → A, x ∈ Λ ↔ (g : Matrix n n A) *ᵥ x ∈ Λ
  intro x
  refine ⟨h1 x, fun h => ?_⟩
  have := h2 _ h
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

section Loc

variable (v : HeightOneSpectrum (𝓞 F))

theorem incl_mem_intV {e : E} (he : e ∈ intOE E) :
    inclE (F := F) (v.adicCompletion F) e ∈ intV E v :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

theorem smul_mem_lat (L : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F))
    {a : E ⊗[F] v.adicCompletion F} (ha : a ∈ intV E v) {z : n → E ⊗[F] v.adicCompletion F}
    (hz : z ∈ L) : a • z ∈ L := L.smul_mem ⟨a, ha⟩ hz

theorem CongAt.mono {c c' : ℕ} (h : c' ∣ c) {g : GL n (E ⊗[F] v.adicCompletion F)}
    (hg : CongAt v c g) : CongAt v c' g := by
  obtain ⟨e, rfl⟩ := h
  intro i j
  obtain ⟨s, hs, he⟩ := hg i j
  exact ⟨(e : E ⊗[F] v.adicCompletion F) * s, mul_mem (natCast_mem _ e) hs, by
    rw [he, Nat.cast_mul, mul_assoc]⟩

theorem latS_int (Λ : Submodule (𝓞 E) (n → E)) (hint : ∀ x ∈ Λ, ∀ i, x i ∈ intOE E)
    {y : n → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ) (i : n) : y i ∈ intV E v := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, hx, rfl⟩ := hy; exact incl_mem_intV v (hint x hx i)
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul s a _ ha => exact mul_mem s.2 ha

theorem latS_of_int (Λ : Submodule (𝓞 E) (n → E)) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (z : n → E ⊗[F] v.adicCompletion F)
    (hz : ∀ i, z i ∈ intV E v) :
    (N : E ⊗[F] v.adicCompletion F) • z ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ := by
  have h : (N : E ⊗[F] v.adicCompletion F) • z = ∑ j, (⟨z j, hz j⟩ : intV E v) •
      (fun i => inclE (F := F) (v.adicCompletion F) (((N : E) • (Pi.single j 1 : n → E)) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show (N : E ⊗[F] v.adicCompletion F) * z i =
        z i * inclE (F := F) (v.adicCompletion F) (((N : E) • (Pi.single i 1 : n → E)) i)
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_natCast, mul_comm]
    · intro j _ hj
      show z j * inclE (F := F) (v.adicCompletion F) (((N : E) • (Pi.single j 1 : n → E)) i) = 0
      rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero, map_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [h]
  exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hN j, rfl⟩)

theorem cong_sub (Λ : Submodule (𝓞 E) (n → E)) (N c1 : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (hint : ∀ x ∈ Λ, ∀ i, x i ∈ intOE E)
    (g : GL n (E ⊗[F] v.adicCompletion F)) (hg : CongAt v (N * c1) g)
    {y : n → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ) :
    ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ,
      (g : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (c1 : E ⊗[F] v.adicCompletion F) • z := by
  choose s hs he using hg
  refine ⟨(N : E ⊗[F] v.adicCompletion F) • (fun i => ∑ j, s i j * y j),
    latS_of_int v Λ N hN _ (fun i => sum_mem fun j _ => mul_mem (hs i j) (latS_int v Λ hint hy j)), ?_⟩
  ext i
  have h : ((g : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ y - y) i =
      ∑ j, ((g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
        (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j) * y j := by
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp [Matrix.one_apply]
  rw [h]
  simp only [he, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Nat.cast_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cong_map (Λ : Submodule (𝓞 E) (n → E)) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (hint : ∀ x ∈ Λ, ∀ i, x i ∈ intOE E)
    (g : GL n (E ⊗[F] v.adicCompletion F)) (hg : CongAt v N g)
    {y : n → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ) :
    (g : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Λ := by
  obtain ⟨z, hz, he⟩ := cong_sub v Λ N 1 hN hint g (by rwa [mul_one]) hy
  have h : (g : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ y =
      y + ((1 : ℕ) : E ⊗[F] v.adicCompletion F) • z := by rw [← he]; abel
  rw [h]
  exact add_mem hy (smul_mem_lat v _ (natCast_mem _ 1) hz)

theorem cong_levelVL (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (hint : ∀ x ∈ Λ, ∀ i, x i ∈ intOE E)
    (g : GL n (E ⊗[F] v.adicCompletion F)) (hU : g ∈ UPts σ J (v.adicCompletion F))
    (hg : CongAt v N g) (hg' : CongAt v N g⁻¹) : g ∈ levelVL σ J v Λ :=
  ⟨hU, mem_stabGL_of _ g (fun _ hy => cong_map v Λ N hN hint g hg hy)
    (fun _ hy => cong_map v Λ N hN hint g⁻¹ hg' hy)⟩

theorem isUnit_natCast {T : ℕ} (hT : T ≠ 0) : IsUnit ((T : ℕ) : E ⊗[F] v.adicCompletion F) := by
  have h : ((T : ℕ) : E ⊗[F] v.adicCompletion F) =
      algebraMap F (E ⊗[F] v.adicCompletion F) (T : F) := (map_natCast _ _).symm
  rw [h]
  exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hT)).map _

end Loc

section ParSec

variable {k : ℕ} (P : Par F E k) (v : HeightOneSpectrum (𝓞 F))

theorem lb_int : ∀ x ∈ P.Lb, ∀ i, x i ∈ intOE E := by
  intro x hx i
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    unfold lbVec
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same]
      split_ifs
      · exact ⟨P.pz, rfl⟩
      · exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul r a _ ha => exact mul_mem ⟨r, rfl⟩ ha

theorem lb_int' : ∀ x ∈ P.Lb, ∀ i, ((1 : ℕ) : E) * x i ∈ intOE E := by
  intro x hx i
  rw [Nat.cast_one, one_mul]; exact lb_int P x hx i

theorem lbV_le_ldV {d : ℕ} (hL : P.LbOK d) : P.LbV v ≤ P.LdV v :=
  Submodule.span_mono (Set.image_mono fun x hx => Submodule.subset_span (hL.int x hx))

theorem T_smul_mem_dual_lattice {d : ℕ} (hL : P.LbOK d) {x : Fin k → E} (hx : x ∈ P.Ld) : (P.T : E) • x ∈ P.Lb := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hL.dual x hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ r ha

theorem T_smul_mem_local_dual_lattice {d : ℕ} (hL : P.LbOK d) {y : Fin k → E ⊗[F] v.adicCompletion F} (hy : y ∈ P.LdV v) :
    (P.T : E ⊗[F] v.adicCompletion F) • y ∈ P.LbV v := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    refine Submodule.subset_span ⟨_, T_smul_mem_dual_lattice P hL hx, ?_⟩
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul s a _ ha =>
    have h : (P.T : E ⊗[F] v.adicCompletion F) • s • a = s • (P.T : E ⊗[F] v.adicCompletion F) • a := by
      ext i
      show (P.T : E ⊗[F] v.adicCompletion F) * ((s : E ⊗[F] v.adicCompletion F) * a i) =
        (s : E ⊗[F] v.adicCompletion F) * ((P.T : E ⊗[F] v.adicCompletion F) * a i)
      ring
    rw [h]; exact Submodule.smul_mem _ s ha

theorem ld_sub {d : ℕ} (hL : P.LbOK d) (hT : P.T ≠ 0) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : Fin k → E) ∈ P.Lb)
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (hg : CongAt v (N * P.T) g)
    {y : Fin k → E ⊗[F] v.adicCompletion F} (hy : y ∈ P.LdV v) :
    (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ P.LbV v := by
  obtain ⟨z, hz, he⟩ := cong_sub v P.Lb N P.T hN (lb_int P) g hg (T_smul_mem_local_dual_lattice P v hL hy)
  have h : (P.T : E ⊗[F] v.adicCompletion F) •
      ((g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y) =
      (P.T : E ⊗[F] v.adicCompletion F) • z := by
    rw [smul_sub, ← Matrix.mulVec_smul, he]
  rw [(isUnit_natCast (E := E) v hT).smul_left_cancel.1 h]
  exact hz

theorem ld_map {d : ℕ} (hL : P.LbOK d) (hT : P.T ≠ 0) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : Fin k → E) ∈ P.Lb)
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (hg : CongAt v (N * P.T) g)
    {y : Fin k → E ⊗[F] v.adicCompletion F} (hy : y ∈ P.LdV v) :
    (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ P.LdV v := by
  have h := add_mem (lbV_le_ldV P v hL (ld_sub P v hL hT N hN g hg hy)) hy
  rwa [sub_add_cancel] at h

theorem cong_stabFun {d : ℕ} (hL : P.LbOK d) (hT : P.T ≠ 0) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : Fin k → E) ∈ P.Lb)
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (hg : CongAt v (N * P.T) g)
    (hg' : CongAt v (N * P.T) g⁻¹) : g ∈ stabFun _ (P.fT v) := by
  refine ⟨mem_stabGL_of _ g (fun _ hy => ld_map P v hL hT N hN g hg hy)
    (fun _ hy => ld_map P v hL hT N hN g⁻¹ hg' hy), fun x => ?_⟩
  unfold Par.fT
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Submodule.mem_sup_left (ld_sub P v hL hT N hN g hg x.2)

theorem par_lev (hIw : P.IwLe) (S : P.Splits) : P.Uloc S v ≤ levelVL P.σ P.J v P.Lb := by
  unfold Par.Uloc
  split_ifs with h h0 h1
  · exact inf_le_left
  · exact hIw 0 v h0 _
  · exact hIw 1 v h1 _
  · exact le_rfl

theorem natCast_mem_max {p : ℕ} (hp : (p : 𝓞 F) ∈ v.asIdeal) :
    ((p : ℕ) : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h := (v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 hp
  rw [← Formalism.UG.P.levelaf_valued_algebraMap] at h
  have e : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) =
      (p : v.adicCompletion F) := by rw [map_natCast, map_natCast]
  replace h : Valued.v ((p : ℕ) : v.adicCompletion F) < 1 := by rw [← e]; exact h
  intro h1
  rw [show (((p : ℕ) : v.adicCompletionIntegers F) : v.adicCompletion F) = (p : v.adicCompletion F) from
    by push_cast; rfl] at h1
  exact absurd h1 h.ne

theorem map_one_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (i j : Fin k) :
    f ((1 : Matrix (Fin k) (Fin k) A) i j) = (1 : Matrix (Fin k) (Fin k) B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem cong_iw {a : E} (s : SplitAt P.σ v a) {p : ℕ} (hp : (p : 𝓞 F) ∈ v.asIdeal)
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (hU : g ∈ UPts P.σ P.J (v.adicCompletion F))
    (hg : CongAt v p g) (hg' : CongAt v p g⁻¹) : g ∈ P.iwPre v s.φ := by
  refine ⟨hU, ?_⟩
  set ψ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F :=
    (RingHom.fst _ _).comp s.φ.toRingHom with hψ
  have hint : ∀ x ∈ intV E v, ψ x ∈ v.adicCompletionIntegers F := fun x hx => ((s.int x).1 hx).1
  let ι : v.adicCompletionIntegers F →+* v.adicCompletion F := algebraMap _ _
  have key : ∀ g : GL (Fin k) (E ⊗[F] v.adicCompletion F), CongAt v p g →
      ∃ A : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F),
        RingHom.mapMatrix ι A = ((bc ψ g : GL (Fin k) (v.adicCompletion F)) :
          Matrix (Fin k) (Fin k) (v.adicCompletion F)) ∧
        ∀ i j, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (A i j) =
          (1 : Matrix (Fin k) (Fin k) _) i j := by
    intro g hg
    choose t ht he using hg
    refine ⟨fun i j => (1 : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) i j +
      ((p : ℕ) : v.adicCompletionIntegers F) * ⟨ψ (t i j), hint _ (ht i j)⟩, ?_, fun i j => ?_⟩
    · refine Matrix.ext fun i j => ?_
      have h1 : (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i j =
          (1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i j +
            (p : E ⊗[F] v.adicCompletion F) * t i j := by rw [← he i j]; ring
      show ι ((1 : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) i j +
        ((p : ℕ) : v.adicCompletionIntegers F) * ⟨ψ (t i j), hint _ (ht i j)⟩) =
        ψ ((g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i j)
      rw [h1, map_add, map_add, map_mul, map_mul, map_one_apply, map_one_apply, map_natCast,
        map_natCast]
      rfl
    · rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (natCast_mem_max v hp), zero_mul,
        add_zero, map_one_apply]
  obtain ⟨A, hA, hA1⟩ := key g hg
  obtain ⟨B, hB, _⟩ := key g⁻¹ hg'
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin k) ι) := by
    intro X Y h
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  rw [map_inv] at hB
  have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  refine Subgroup.mem_map.2 ⟨⟨A, B, hAB, hBA⟩, ?_, Units.ext hA⟩
  have h1 : redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
      (⟨A, B, hAB, hBA⟩ : GL (Fin k) (v.adicCompletionIntegers F)) = 1 :=
    Units.ext (Matrix.ext fun i j => hA1 i j)
  rw [Subgroup.mem_comap, h1]
  exact one_mem _

theorem par_cong {d : ℕ} (hL : P.LbOK d) (hT : P.T ≠ 0) (hg : ∀ i, P.gp i ≠ 0) :
    ∃ c : ℕ, c ≠ 0 ∧ ∀ (S : P.Splits) (v : HeightOneSpectrum (𝓞 F)),
      ∀ g ∈ UPts P.σ P.J (v.adicCompletion F), CongAt v c g → CongAt v c g⁻¹ → g ∈ P.Uloc S v := by
  obtain ⟨N, hN0, hN⟩ := exists_nat_smul_mem P.Lb hL.span
  refine ⟨N * P.T * (P.gp 0 * P.gp 1),
    mul_ne_zero (mul_ne_zero hN0 hT) (mul_ne_zero (hg 0) (hg 1)), fun S v g hU h h' => ?_⟩
  have d1 : N ∣ N * P.T * (P.gp 0 * P.gp 1) := Dvd.dvd.mul_right (Dvd.intro _ rfl) _
  have d2 : N * P.T ∣ N * P.T * (P.gp 0 * P.gp 1) := Dvd.intro _ rfl
  have d3 : P.gp 0 ∣ N * P.T * (P.gp 0 * P.gp 1) := Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  have d4 : P.gp 1 ∣ N * P.T * (P.gp 0 * P.gp 1) := Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _
  have hlev : g ∈ levelVL P.σ P.J v P.Lb :=
    cong_levelVL v P.σ P.J P.Lb N hN (lb_int P) g hU (CongAt.mono v d1 h) (CongAt.mono v d1 h')
  unfold Par.Uloc
  split_ifs with hTv h0 h1
  · exact ⟨hlev, cong_stabFun P v hL hT N hN g (CongAt.mono v d2 h) (CongAt.mono v d2 h')⟩
  · exact cong_iw P v _ h0 g hU (CongAt.mono v d3 h) (CongAt.mono v d3 h')
  · exact cong_iw P v _ h1 g hU (CongAt.mono v d4 h) (CongAt.mono v d4 h')
  · exact hlev

end ParSec

end Bridge

section Facts

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

theorem par_top (P : Par F E k) {d : ℕ} (hL : P.LbOK d) (hIw : P.IwLe) (hT : P.T ≠ 0)
    (hg : ∀ i, P.gp i ≠ 0) : P.UCompact ∧ P.UOpen := by
  obtain ⟨N, hN, h1⟩ := exists_nat_smul_mem P.Lb hL.span
  obtain ⟨c, hc, hcong⟩ := par_cong P hL hT hg
  have key := fun S : P.Splits => level_top' P.σ P.J P.Lb N 1 c hN one_ne_zero hc h1 (lb_int' P)
    (P.Uloc S) (fun v => par_lev P v hIw S) (hcong S) (P.U S)
    (fun x => by simp only [Par.U, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap])
  exact ⟨fun S => (key S).1, fun S => (key S).2⟩

theorem factUCompact_of (h2 : FactLb) (h4 : FactIwLe) : FactUCompact :=
  fun H T pz piG h => (par_top _ (h2 H T pz piG h) (h4 H T pz piG h) h.T_prime.ne_zero
    (fun i => (H.g_prime i).ne_zero)).1

theorem factUOpen_of (h2 : FactLb) (h4 : FactIwLe) : FactUOpen :=
  fun H T pz piG h => (par_top _ (h2 H T pz piG h) (h4 H T pz piG h) h.T_prime.ne_zero
    (fun i => (H.g_prime i).ne_zero)).2

theorem factUCompact : FactUCompact := factUCompact_of factLb factIwLe

theorem factUOpen : FactUOpen := factUOpen_of factLb factIwLe

end Facts

end Formalism.MainNotions.Gaps.LevGap
