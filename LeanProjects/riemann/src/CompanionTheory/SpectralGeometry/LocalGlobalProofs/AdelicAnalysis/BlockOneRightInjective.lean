import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StabFirst

section Blocks

variable {K : Type} [CommRing K] {M : ℕ}

@[simp] lemma blockOne_zero_zero (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl
@[simp] lemma blockOne_zero_succ (t : K) (A : Matrix (Fin M) (Fin M) K) (j : Fin M) :
    blockOne t A 0 j.succ = 0 := rfl
@[simp] lemma blockOne_succ_zero (t : K) (A : Matrix (Fin M) (Fin M) K) (i : Fin M) :
    blockOne t A i.succ 0 = 0 := rfl
@[simp] lemma blockOne_succ_succ (t : K) (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    blockOne t A i.succ j.succ = A i j := rfl

lemma blockOne_mul (a b : K) (A B : Matrix (Fin M) (Fin M) K) :
    blockOne a A * blockOne b B = blockOne (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

lemma blockOne_one : blockOne (1 : K) (1 : Matrix (Fin M) (Fin M) K) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

lemma blockOne_right_injective {a b : K} {A B : Matrix (Fin M) (Fin M) K}
    (h : blockOne a A = blockOne b B) : A = B := by
  ext i j
  simpa using congrFun (congrFun h i.succ) j.succ

lemma map_blockOne {L : Type} [CommRing L] (φ : K →+* L) (a : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne a A).map φ = blockOne (φ a) (A.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

lemma cT_blockOne (σ : K →+* K) (a : K) (A : Matrix (Fin M) (Fin M) K) :
    cT σ (blockOne a A) = blockOne (σ a) (cT σ A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [cT]

def blockHom : Matrix (Fin M) (Fin M) K →* Matrix (Fin (M + 1)) (Fin (M + 1)) K where
  toFun A := blockOne 1 A
  map_one' := blockOne_one
  map_mul' A B := by rw [blockOne_mul, one_mul]

def blockGL : GL (Fin M) K →* GL (Fin (M + 1)) K := Units.map blockHom

lemma coe_blockGL (g : GL (Fin M) K) :
    ((blockGL g : GL (Fin (M + 1)) K) : Matrix (Fin (M + 1)) (Fin (M + 1)) K) =
      blockOne 1 (g : Matrix (Fin M) (Fin M) K) := rfl

lemma blockGL_injective : Function.Injective (blockGL : GL (Fin M) K → GL (Fin (M + 1)) K) := by
  intro a b h
  apply Units.ext
  apply blockOne_right_injective (a := (1 : K)) (b := 1)
  simpa [coe_blockGL] using congrArg (fun g : GL (Fin (M + 1)) K =>
    (g : Matrix (Fin (M + 1)) (Fin (M + 1)) K)) h

lemma blockGL_mem_UJ (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) (s : K) {g : GL (Fin M) K}
    (hg : g ∈ UJ σ J) : blockGL g ∈ UJ σ (blockOne s J) := by
  have hg' : cT σ (g : Matrix (Fin M) (Fin M) K) * J * (g : Matrix (Fin M) (Fin M) K) = J := hg
  change cT σ (blockOne 1 (g : Matrix (Fin M) (Fin M) K)) * blockOne s J *
    blockOne 1 (g : Matrix (Fin M) (Fin M) K) = blockOne s J
  rw [cT_blockOne, blockOne_mul, blockOne_mul, hg', map_one, one_mul, mul_one]

lemma of_blockGL_mem_UJ (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) (s : K) {g : GL (Fin M) K}
    (hg : blockGL g ∈ UJ σ (blockOne s J)) : g ∈ UJ σ J := by
  have hg' : cT σ (blockOne 1 (g : Matrix (Fin M) (Fin M) K)) * blockOne s J *
    blockOne 1 (g : Matrix (Fin M) (Fin M) K) = blockOne s J := hg
  rw [cT_blockOne, blockOne_mul, blockOne_mul] at hg'
  exact blockOne_right_injective hg'

lemma eq_blockOne_of_col (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) {s : K} (hs : IsUnit s)
    {h : Matrix (Fin (M + 1)) (Fin (M + 1)) K} (hm : cT σ h * blockOne s J * h = blockOne s J)
    (h00 : h 0 0 = 1) (hi0 : ∀ i : Fin M, h i.succ 0 = 0) :
    h = blockOne 1 (h.submatrix Fin.succ Fin.succ) := by
  have h1 : ∀ k, (cT σ h * blockOne s J) 0 k = blockOne s J 0 k := by
    intro k
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [cT, h00, hi0]
  have h2 : ∀ j : Fin M, h 0 j.succ = 0 := by
    intro j
    have e := congrFun (congrFun hm 0) j.succ
    rw [Matrix.mul_apply] at e
    simp only [h1] at e
    rw [Fin.sum_univ_succ] at e
    simp at e
    exact (hs.mul_right_eq_zero).1 e
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [h00, hi0, h2]

lemma exists_blockGL (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) {s : K} (hs : IsUnit s)
    {h : GL (Fin (M + 1)) K} (hm : h ∈ UJ σ (blockOne s J))
    (h00 : (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) 0 0 = 1)
    (hi0 : ∀ i : Fin M, (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) i.succ 0 = 0) :
    ∃ g : GL (Fin M) K, blockGL g = h := by
  set A := (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) with hA
  set B := ((h⁻¹ : GL (Fin (M + 1)) K) : Matrix (Fin (M + 1)) (Fin (M + 1)) K) with hB
  have hAB : A * B = 1 := by rw [hA, hB]; exact Units.mul_inv h
  have hBA : B * A = 1 := by rw [hA, hB]; exact Units.inv_mul h
  have eA := eq_blockOne_of_col σ J hs (h := A) hm h00 hi0
  have hcol : ∀ a, (B * A) a 0 = B a 0 := by
    intro a
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [h00, hi0]
  have hB00 : B 0 0 = 1 := by rw [← hcol, hBA]; simp
  have hBi0 : ∀ i : Fin M, B i.succ 0 = 0 := by
    intro i
    rw [← hcol, hBA]
    simp [Matrix.one_apply, Fin.succ_ne_zero]
  have eB := eq_blockOne_of_col σ J hs (h := B) ((UJ σ (blockOne s J)).inv_mem hm) hB00 hBi0
  have e1 : A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ = 1 := by
    apply blockOne_right_injective (a := (1 : K)) (b := 1)
    rw [← one_mul (1 : K), ← blockOne_mul, ← eA, ← eB, hAB, one_mul, blockOne_one]
  have e2 : B.submatrix Fin.succ Fin.succ * A.submatrix Fin.succ Fin.succ = 1 := by
    apply blockOne_right_injective (a := (1 : K)) (b := 1)
    rw [← one_mul (1 : K), ← blockOne_mul, ← eA, ← eB, hBA, one_mul, blockOne_one]
  refine ⟨⟨A.submatrix Fin.succ Fin.succ, B.submatrix Fin.succ Fin.succ, e1, e2⟩, ?_⟩
  apply Units.ext
  rw [coe_blockGL]
  exact eA.symm

lemma bc_blockGL {L : Type} [CommRing L] (φ : K →+* L) (g : GL (Fin M) K) :
    bc φ (blockGL g) = blockGL (bc φ g) := by
  apply Units.ext
  change (blockOne 1 (g : Matrix (Fin M) (Fin M) K)).map φ =
    blockOne 1 ((g : Matrix (Fin M) (Fin M) K).map φ)
  rw [map_blockOne, map_one]

lemma mulVec_first (A : Matrix (Fin (M + 1)) (Fin (M + 1)) K) (a : Fin (M + 1)) :
    A.mulVec (Fin.cons 1 (fun _ => 0)) a = A a 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma blockOne_mulVec_cons (A : Matrix (Fin M) (Fin M) K) (x : Fin M → K) :
    (blockOne 1 A).mulVec (Fin.cons 0 x) = Fin.cons 0 (A.mulVec x) := by
  ext a
  refine Fin.cases ?_ (fun i => ?_) a <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma continuous_blockOne [TopologicalSpace K] :
    Continuous (fun A : Matrix (Fin M) (Fin M) K => blockOne (1 : K) A) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_id.matrix_elem i j

end Blocks

section Grp

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)

lemma JR_blockOne : JR (F := F) R (blockOne s J) = blockOne (inclR (F := F) R s) (JR (F := F) R J) :=
  map_blockOne (inclR (F := F) R) s J

lemma blockGL_mem_HR {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    blockGL g ∈ HR R σ (blockOne s J) := by
  unfold HR
  rw [JR_blockOne]
  exact blockGL_mem_UJ _ _ _ hg

lemma of_blockGL_mem_HR {g : GL (Fin M) (R ⊗[F] E)} (hg : blockGL g ∈ HR R σ (blockOne s J)) :
    g ∈ HR R σ J := by
  unfold HR at hg ⊢
  rw [JR_blockOne] at hg
  exact of_blockGL_mem_UJ _ _ _ hg

def mkHA (g : GL (Fin M) (R ⊗[F] E)) (hg : g ∈ HR R σ J) : HA R σ J :=
  (⟨g, hg⟩ : HR R σ J)

lemma mat_mem (u : HA R σ J) : HA.mat R σ J u ∈ HR R σ J :=
  Subtype.property (p := fun g => g ∈ HR R σ J) u

lemma mat_injective : Function.Injective (HA.mat R σ J) :=
  fun _ _ h => Subtype.ext (p := fun g => g ∈ HR R σ J) h

def iotaHom : HA R σ J →* HA R σ (blockOne s J) where
  toFun u := mkHA R σ _ (blockGL (HA.mat R σ J u)) (blockGL_mem_HR R σ J s (mat_mem R σ J u))
  map_one' := mat_injective R σ _ (map_one (blockGL (K := R ⊗[F] E) (M := M)))
  map_mul' a b := mat_injective R σ _
    (map_mul (blockGL (K := R ⊗[F] E) (M := M)) (HA.mat R σ J a) (HA.mat R σ J b))

lemma mat_iotaHom (u : HA R σ J) :
    HA.mat R σ _ (iotaHom R σ J s u) = blockGL (HA.mat R σ J u) := rfl

lemma act_first_iff {n : ℕ} (h : HA R σ (blockOne s J)) :
    actW R σ _ h (fun _ : Fin n.succ => Fin.cons 1 (fun _ => 0)) =
        (fun _ : Fin n.succ => Fin.cons 1 (fun _ => 0)) ↔
      ((HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) 0 0 = 1 ∧
        ∀ i : Fin M, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) i.succ 0 = 0) := by
  constructor
  · intro e
    have e' : ∀ a, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) a 0 =
        (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) a := by
      intro a
      exact (mulVec_first _ a).symm.trans (congrFun (congrFun e 0) a)
    exact ⟨by simpa using e' 0, fun i => by simpa using e' i.succ⟩
  · rintro ⟨h0, hi⟩
    funext c a
    change (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec _ a = _
    rw [mulVec_first]
    refine Fin.cases ?_ (fun i => ?_) a
    · simpa using h0
    · simpa using hi i

lemma mem_range_iff (hs : s ≠ 0) (h : HA R σ (blockOne s J)) :
    h ∈ (iotaHom R σ J s).range ↔
      ((HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) 0 0 = 1 ∧
        ∀ i : Fin M, (HA.mat R σ _ h : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) i.succ 0 = 0) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [mat_iotaHom, coe_blockGL]
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨h0, hi⟩
    have hu : IsUnit (inclR (F := F) R s) := (isUnit_iff_ne_zero.2 hs).map (inclR (F := F) R)
    have hm : HA.mat R σ _ h ∈ UJ (sigR R σ) (blockOne (inclR (F := F) R s) (JR (F := F) R J)) := by
      have := mat_mem R σ _ h
      unfold HR at this
      rwa [JR_blockOne] at this
    obtain ⟨g, hg⟩ := exists_blockGL _ _ hu hm h0 hi
    have hgm : g ∈ HR R σ J := by
      apply of_blockGL_mem_HR R σ J s
      rw [hg]
      exact mat_mem R σ _ h
    exact ⟨mkHA R σ J g hgm, mat_injective R σ _ hg⟩

lemma mem_HFin_iff (hs : s ≠ 0) (u : HA R σ J) :
    HA.mat R σ _ (iotaHom R σ J s u) ∈ HFin R σ (blockOne s J) ↔ HA.mat R σ J u ∈ HFin R σ J := by
  rw [mat_iotaHom]
  constructor
  · rintro ⟨γ, hγ, e⟩
    rcases subsingleton_or_nontrivial (R ⊗[F] E) with hK | hK
    · have : Subsingleton (GL (Fin M) (R ⊗[F] E)) := inferInstance
      rw [Subsingleton.elim (HA.mat R σ J u) 1]
      exact one_mem _
    · have inj : Function.Injective (inclR (F := F) (E := E) R) := by
        exact RingHom.injective _
      have ent : ∀ a b, inclR (F := F) R ((γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) a b) =
          blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E)) a b := by
        intro a b
        exact congrFun (congrFun (congrArg (fun g : GL (Fin (M + 1)) (R ⊗[F] E) =>
          (g : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E))) e) a) b
      have h0 : (γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) 0 0 = 1 :=
        inj (by rw [ent]; simp)
      have hi : ∀ i : Fin M, (γ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i.succ 0 = 0 :=
        fun i => inj (by rw [ent]; simp)
      obtain ⟨g, rfl⟩ := exists_blockGL _ _ (isUnit_iff_ne_zero.2 hs) hγ h0 hi
      refine ⟨g, of_blockGL_mem_UJ _ _ _ hγ, ?_⟩
      apply blockGL_injective
      rw [← bc_blockGL]
      exact e
  · rintro ⟨g, hg, e⟩
    exact ⟨blockGL g, blockGL_mem_UJ _ _ _ hg, by rw [bc_blockGL, e]⟩

lemma act_iota {n : ℕ} (u : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ _ (iotaHom R σ J s u) (consTup X) = consTup (actW R σ J u X) := by
  funext a
  refine Fin.cases ?_ (fun c => ?_) a
  · funext i
    change (blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E))).mulVec
      (Fin.cons 1 (fun _ => 0)) i = (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) i
    rw [mulVec_first]
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  · exact blockOne_mulVec_cons _ _

section Top

variable [TopologicalSpace R]

def pairMap {N : ℕ} (J' : Matrix (Fin N) (Fin N) E) (h : HA R σ J') :
    Matrix (Fin N) (Fin N) (R ⊗[F] E) × (Matrix (Fin N) (Fin N) (R ⊗[F] E))ᵐᵒᵖ :=
  Units.embedProduct _ (HA.mat R σ J' h)

lemma isEmbedding_pairMap {N : ℕ} (J' : Matrix (Fin N) (Fin N) E) :
    IsEmbedding (pairMap R σ J') :=
  (Units.isEmbedding_embedProduct).comp
    (IsEmbedding.subtypeVal (p := fun g => g ∈ HR R σ J'))

lemma continuous_iotaHom : Continuous (iotaHom R σ J s) := by
  rw [(isEmbedding_pairMap R σ (blockOne s J)).isInducing.continuous_iff]
  have hp := (isEmbedding_pairMap R σ J).continuous
  have : pairMap R σ (blockOne s J) ∘ iotaHom R σ J s = fun u =>
      (blockOne 1 (pairMap R σ J u).1,
        MulOpposite.op (blockOne 1 (MulOpposite.unop (pairMap R σ J u).2))) := rfl
  rw [this]
  exact (continuous_blockOne.comp hp.fst).prodMk
    (MulOpposite.continuous_op.comp
      (continuous_blockOne.comp (MulOpposite.continuous_unop.comp hp.snd)))

lemma isEmbedding_iotaHom : IsEmbedding (iotaHom R σ J s) := by
  have hp := (isEmbedding_pairMap R σ (blockOne s J)).continuous
  let P : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) × (Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E))ᵐᵒᵖ →
      Matrix (Fin M) (Fin M) (R ⊗[F] E) × (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    fun p => (p.1.submatrix Fin.succ Fin.succ,
      MulOpposite.op ((MulOpposite.unop p.2).submatrix Fin.succ Fin.succ))
  have hP : Continuous P := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.matrix_submatrix _ _
    · exact MulOpposite.continuous_op.comp
        ((MulOpposite.continuous_unop.comp continuous_snd).matrix_submatrix _ _)
  refine IsEmbedding.of_comp (continuous_iotaHom R σ J s) (hP.comp hp) ?_
  have : (P ∘ pairMap R σ (blockOne s J)) ∘ iotaHom R σ J s = pairMap R σ J := by
    funext u
    rfl
  rw [this]
  exact isEmbedding_pairMap R σ J

lemma isClosed_range_iotaHom [T2Space (R ⊗[F] E)] (hs : s ≠ 0) :
    IsClosed (Set.range (iotaHom R σ J s)) := by
  have hp := (isEmbedding_pairMap R σ (blockOne s J)).continuous
  have e : Set.range (iotaHom R σ J s) =
      {h | (pairMap R σ (blockOne s J) h).1 0 0 = 1} ∩
        ⋂ i : Fin M, {h | (pairMap R σ (blockOne s J) h).1 i.succ 0 = 0} := by
    ext h
    have := mem_range_iff R σ J s hs h
    simp only [MonoidHom.mem_range] at this
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact this
  rw [e]
  refine IsClosed.inter (isClosed_eq (hp.fst.matrix_elem 0 0) continuous_const) ?_
  exact isClosed_iInter fun i => isClosed_eq (hp.fst.matrix_elem i.succ 0) continuous_const

end Top

end Grp

lemma t2_tensor_product {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have hc : Continuous b.equivFun.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  exact T2Space.of_injective_continuous b.equivFun.injective hc

theorem stab_first :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R], ∃ ι : HA R σ J →* HA R σ (blockOne (algebraMap F E t) J), IsClosedEmbedding ι ∧ (∀ u, (HA.mat R σ _ (ι u) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) = blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) ∧ (∀ h, h ∈ ι.range ↔ actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) ∧ (∀ u, HA.mat R σ _ (ι u) ∈ HFin R σ (blockOne (algebraMap F E t) J) ↔ HA.mat R σ J u ∈ HFin R σ J) ∧ ∀ (u : HA R σ J) (n : ℕ) (X : Fin n → Fin M → R ⊗[F] E), actW R σ _ (ι u) (consTup X) = consTup (actW R σ J u X) := by
  intro F E _ _ _ _ _ σ hCM M J _ t ht R _ _ _ _ _
  have hs : algebraMap F E t ≠ 0 := by
    simpa using ht
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : T2Space (R ⊗[F] E) := t2_tensor_product R
  refine ⟨iotaHom R σ J (algebraMap F E t), ?_, fun _ => rfl, ?_, ?_, ?_⟩
  · exact ⟨isEmbedding_iotaHom R σ J _, isClosed_range_iotaHom R σ J _ hs⟩
  · intro h
    rw [mem_range_iff R σ J _ hs h]
    exact (act_first_iff R σ J _ (n := 0) h).symm
  · exact fun u => mem_HFin_iff R σ J _ hs u
  · exact fun u n X => act_iota R σ J _ u X

end GlobalTheory.CompanionTheory.SW.StabFirst
