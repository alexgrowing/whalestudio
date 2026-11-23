import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FiniteDimensionalCoeffSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import GroundTheory.LocalFields.CompleteTrivialLocal
import GroundTheory.PAdicHodge.Admissible
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames

open Formalism.REAL

variable {n n' : ℕ}

def incl (e : Fin n' → Fin n) : Matrix (Fin n) (Fin n') ℂ :=
  (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e

theorem incl_ct_mul {e : Fin n' → Fin n} (he : Function.Injective e) : (incl e)ᴴ * incl e = 1 := by
  ext a b
  simp [incl, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, he.eq_iff]

theorem incl_mul_apply {e : Fin n' → Fin n} (he : Function.Injective e) {m : Type} (X : Matrix (Fin n') m ℂ)
    (a : Fin n') (c : m) : (incl e * X) (e a) c = X a c := by
  simp [incl, Matrix.mul_apply, Matrix.one_apply, he.eq_iff]

theorem incl_mul_apply_of_notMem {e : Fin n' → Fin n} {m : Type} (X : Matrix (Fin n') m ℂ)
    {i : Fin n} (hi : i ∉ Set.range e) (c : m) : (incl e * X) i c = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : i ≠ e a := fun h => hi ⟨a, h.symm⟩
  simp [incl, Matrix.one_apply, this]

theorem Jm_mul_incl (ε : Fin n → Bool) (e : Fin n' → Fin n) : Jm ε * incl e = incl e * Jm (ε ∘ e) := by
  ext i c
  simp only [Formalism.REAL.Jm, incl, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply, id, Matrix.one_apply,
    Function.comp]
  split_ifs <;> simp_all

theorem incl_ct_mul_Jm (ε : Fin n → Bool) (e : Fin n' → Fin n) : (incl e)ᴴ * Jm ε = Jm (ε ∘ e) * (incl e)ᴴ := by
  have := congrArg Matrix.conjTranspose (Jm_mul_incl ε e)
  simpa only [Matrix.conjTranspose_mul, Jm_conjTranspose] using this

def blk (e : Fin n' → Fin n) (a : Matrix (Fin n') (Fin n') ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + incl e * (a - 1) * (incl e)ᴴ

theorem blk_one (e : Fin n' → Fin n) : blk e 1 = 1 := by simp [blk]

theorem blk_mul_incl {e : Fin n' → Fin n} (he : Function.Injective e) (a : Matrix (Fin n') (Fin n') ℂ) :
    blk e a * incl e = incl e * a := by
  rw [blk, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, incl_ct_mul he, Matrix.mul_one,
    ← Matrix.mul_one (incl e), Matrix.mul_assoc, Matrix.one_mul, ← Matrix.mul_add]
  simp

theorem blk_mul {e : Fin n' → Fin n} (he : Function.Injective e) (a b : Matrix (Fin n') (Fin n') ℂ) :
    blk e (a * b) = blk e a * blk e b := by
  have h := incl_ct_mul he
  have h2 : incl e * (a - 1) * (incl e)ᴴ * (incl e * (b - 1) * (incl e)ᴴ) =
      incl e * ((a - 1) * (b - 1)) * (incl e)ᴴ := by
    calc _ = incl e * (a - 1) * ((incl e)ᴴ * incl e) * (b - 1) * (incl e)ᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  simp only [blk]
  rw [e2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h2]
  abel

theorem blk_ct (e : Fin n' → Fin n) (a : Matrix (Fin n') (Fin n') ℂ) : (blk e a)ᴴ = blk e aᴴ := by
  simp [blk, Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.mul_assoc]

theorem blk_comm {ε : Fin n → Bool} (e : Fin n' → Fin n) {a : Matrix (Fin n') (Fin n') ℂ}
    (ha : a * Jm (ε ∘ e) = Jm (ε ∘ e) * a) : blk e a * Jm ε = Jm ε * blk e a := by
  have h1 : (a - 1) * Jm (ε ∘ e) = Jm (ε ∘ e) * (a - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, ha, Matrix.one_mul, Matrix.mul_one]
  simp only [blk, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  congr 1
  calc incl e * (a - 1) * (incl e)ᴴ * Jm ε = incl e * ((a - 1) * Jm (ε ∘ e)) * (incl e)ᴴ := by
        rw [Matrix.mul_assoc, incl_ct_mul_Jm]; simp only [Matrix.mul_assoc]
    _ = Jm ε * (incl e * (a - 1) * (incl e)ᴴ) := by
        rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Jm_mul_incl]; simp only [Matrix.mul_assoc]

theorem Kset_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  have h1 : gᴴ * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg.1
  change gᴴ * Jm ε * g = Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem blk_mem {ε : Fin n → Bool} {e : Fin n' → Fin n} (he : Function.Injective e)
    {a : Matrix (Fin n') (Fin n') ℂ} (ha : a ∈ Kset (ε ∘ e)) : blk e a ∈ Kset ε := by
  refine ⟨Matrix.mem_unitaryGroup_iff.2 ?_, blk_comm e ha.2⟩
  have h1 : a * aᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 ha.1
  rw [Matrix.star_eq_conjTranspose, blk_ct, ← blk_mul he, h1, blk_one]

def blockDiagonalOfBlocks {e : Fin n' → Fin n} (he : Function.Injective e) (ε : Fin n → Bool) : KG (ε ∘ e) →* KG ε :=
  MonoidHom.mk' (fun k' => ⟨⟨⟨blk e (toMK k'), blk e (toMK k')ᴴ,
      by have h1 : toMK k' * (toMK k')ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 k'.2.1
         rw [← blk_mul he, h1, blk_one],
      by have h1 : (toMK k')ᴴ * toMK k' = 1 := Matrix.mem_unitaryGroup_iff'.1 k'.2.1
         rw [← blk_mul he, h1, blk_one]⟩, Kset_inUJ (blk_mem he k'.2)⟩, blk_mem he k'.2⟩)
    (fun a b => Subtype.ext (Subtype.ext (Units.ext (blk_mul he (toMK a) (toMK b)))))

theorem isEmbedding_toMK (ε : Fin n → Bool) : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
  (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal

theorem continuous_conj_blockEmbedding {e : Fin n' → Fin n} (he : Function.Injective e) (ε : Fin n → Bool) (k : KG ε) :
    Continuous ((MulAut.conj k).toMonoidHom.comp (blockDiagonalOfBlocks he ε)) := by
  refine (isEmbedding_toMK ε).continuous_iff.2 ?_
  have hc : Continuous fun k' : KG (ε ∘ e) => toMK k' := (isEmbedding_toMK _).continuous
  have : ((fun k : KG ε => toMK k) ∘ ((MulAut.conj k).toMonoidHom.comp (blockDiagonalOfBlocks he ε))) =
      fun k' => toMK k * blk e (toMK k') * toMK k⁻¹ := rfl
  rw [this]
  refine Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
  exact continuous_const.add (Continuous.matrix_mul (Continuous.matrix_mul continuous_const
    (hc.sub continuous_const)) continuous_const)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames
end

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames

open Formalism.REAL

variable {n n' : ℕ}

theorem toMK_mul_ct {ε : Fin n → Bool} (k : KG ε) : toMK k * (toMK k)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 k.2.1

theorem toMK_inv {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h : toMK k⁻¹ * toMK k = 1 := by
    have : toMK (k⁻¹ * k) = 1 := by rw [inv_mul_cancel]; rfl
    exact this
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * (toMK k)ᴴ) := by rw [toMK_mul_ct, Matrix.mul_one]
    _ = (toMK k)ᴴ := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem ct_J_ct {ε : Fin n → Bool} (k : KG ε) (P : Matrix (Fin n) (Fin n) ℂ) :
    ((toMK k)ᴴ * P)ᴴ * Jm ε * ((toMK k)ᴴ * P) = Pᴴ * Jm ε * P := by
  have hc : toMK k * Jm ε = Jm ε * toMK k := k.2.2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Pᴴ * toMK k * Jm ε * ((toMK k)ᴴ * P) = Pᴴ * (toMK k * Jm ε) * (toMK k)ᴴ * P := by
        simp only [Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * (toMK k * (toMK k)ᴴ) * P := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [toMK_mul_ct, Matrix.mul_one]

theorem rows_zero {κ : Type} [Fintype κ] {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ}
    (k : KG ε) (S : Set (Fin n)) (C : Matrix (Fin n) κ ℂ) (M : Matrix (Fin n) (Fin n') ℂ)
    (hspan : Submodule.span ℂ (Set.range fun c => P *ᵥ C.col c) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
        (toMK k).mulVecLin)
    (hCM : Mᴴ * (Pᴴ * Jm ε * P) * C = 0) {i : Fin n} (hi : i ∈ S) (c : Fin n') :
    ((toMK k)ᴴ * P * M) i c = 0 := by
  have hle : Submodule.span ℂ (Set.range fun c => P *ᵥ C.col c) ≤
      LinearMap.ker (Mᴴ * Pᴴ * Jm ε).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, rfl⟩
    change (Mᴴ * Pᴴ * Jm ε) *ᵥ (P *ᵥ C.col d) = 0
    rw [Matrix.mulVec_mulVec]
    have h0 : (Mᴴ * Pᴴ * Jm ε * P) * C = 0 := by rw [← hCM]; simp only [Matrix.mul_assoc]
    funext a
    exact congrFun (congrFun h0 a) d
  have hmem : toMK k *ᵥ (Pi.single i (1 : ℂ)) ∈ Submodule.span ℂ (Set.range fun c => P *ᵥ C.col c) := by
    rw [hspan]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  have h0 : (Mᴴ * Pᴴ * Jm ε) *ᵥ (toMK k *ᵥ (Pi.single i (1 : ℂ))) = 0 := hle hmem
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h0
  have hc : toMK k * Jm ε = Jm ε * toMK k := k.2.2
  have h1 : Mᴴ * Pᴴ * Jm ε * toMK k = (Mᴴ * Pᴴ * toMK k) * Jm ε := by
    rw [Matrix.mul_assoc _ (Jm ε), ← hc]; simp only [Matrix.mul_assoc]
  have h2 := congrFun h0 c
  rw [h1] at h2
  simp only [Matrix.col_apply, Formalism.REAL.Jm, Matrix.mul_diagonal, Pi.zero_apply] at h2
  have h3 : (Mᴴ * Pᴴ * toMK k) c i = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exfalso; split_ifs at h <;> simp at h
  have h4 : (toMK k)ᴴ * P * M = (Mᴴ * Pᴴ * toMK k)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [h4, Matrix.conjTranspose_apply, h3, star_zero]

theorem card_le_card {κ : Type} [Fintype κ] [DecidableEq κ] {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (k : KG ε) (S : Set (Fin n)) [Fintype S] (C : Matrix (Fin n) κ ℂ)
    (hspan : Submodule.span ℂ (Set.range fun c => P *ᵥ C.col c) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
        (toMK k).mulVecLin)
    (L : Matrix κ (Fin n) ℂ) (hL : L * C = 1) : Fintype.card κ ≤ Fintype.card S := by
  classical
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hinj : Function.Injective (P * C).mulVec := by
    refine Function.LeftInverse.injective (g := (L * P⁻¹).mulVec) fun v => ?_
    rw [Matrix.mulVec_mulVec]
    have : L * P⁻¹ * (P * C) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, hL]
    rw [this, Matrix.one_mulVec]
  have hli : LinearIndependent ℂ fun c => P *ᵥ C.col c := by
    have hfun : (fun c => P *ᵥ C.col c) = (P * C).col := by
      funext c a
      rfl
    rw [hfun]
    exact Matrix.mulVec_injective_iff.1 hinj
  calc Fintype.card κ = Module.finrank ℂ (Submodule.span ℂ (Set.range fun c => P *ᵥ C.col c)) :=
        (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))) := by
        rw [hspan]; exact Submodule.finrank_map_le _ _
    _ ≤ Fintype.card S := finrank_range_le_card _

theorem le_card_compl {A : Matrix (Fin n) (Fin n') ℂ} (hA : Function.Injective A.mulVec) (S : Set (Fin n))
    [Fintype (Sᶜ : Set (Fin n))] (h0 : ∀ i ∈ S, ∀ c, A i c = 0) : n' ≤ Fintype.card (Sᶜ : Set (Fin n)) := by
  classical
  let R : Matrix (Sᶜ : Set (Fin n)) (Fin n') ℂ := A.submatrix Subtype.val id
  have hinj : Function.Injective R.mulVecLin := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    refine hA ?_
    rw [Matrix.mulVec_zero]
    funext i
    by_cases hi : i ∈ S
    · simp [Matrix.mulVec, dotProduct, h0 i hi]
    · exact congrFun hv ⟨i, hi⟩
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames
end

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames

open Formalism.REAL

variable {n n' : ℕ}

theorem incl_ct_mul_apply (e : Fin n' → Fin n) {m : Type} (Y : Matrix (Fin n) m ℂ) (a : Fin n') (c : m) :
    ((incl e)ᴴ * Y) a c = Y (e a) c := by
  simp [incl, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

theorem exists_frame {κ : Type} [Fintype κ] [DecidableEq κ] {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) (k : KG ε) (S : Set (Fin n)) (C : Matrix (Fin n) κ ℂ) (M : Matrix (Fin n) (Fin n') ℂ)
    (hspan : Submodule.span ℂ (Set.range fun c => P *ᵥ C.col c) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
        (toMK k).mulVecLin)
    (hCM : Mᴴ * (Pᴴ * Jm ε * P) * C = 0) (L : Matrix κ (Fin n) ℂ) (hL : L * C = 1)
    (hG : IsUnit (Mᴴ * (Pᴴ * Jm ε * P) * M)) (hcard : n ≤ Fintype.card κ + n') :
    ∃ (ε' : Fin n' → Bool) (F : Matrix (Fin n') (Fin n') ℂ) (j : KG ε' →* KG ε),
      IsUnit F ∧ Fᴴ * Jm ε' * F = Mᴴ * (Pᴴ * Jm ε * P) * M ∧ Continuous j ∧
      ∀ k', GlobalTheory.RealBessel.IsEmb (Pᴴ * Jm ε * P) M (P⁻¹ * toMK (j k') * P) (F⁻¹ * toMK k' * F) := by
  classical
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hGd : IsUnit (Mᴴ * (Pᴴ * Jm ε * P) * M).det := (Matrix.isUnit_iff_isUnit_det _).1 hG
  obtain ⟨K, hKdef⟩ : ∃ K, K = toMK k := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = Kᴴ * P * M := ⟨_, rfl⟩
  have hKK : K * Kᴴ = 1 := hKdef ▸ toMK_mul_ct k
  have hAG : Aᴴ * Jm ε * A = Mᴴ * (Pᴴ * Jm ε * P) * M := by
    have h := ct_J_ct k P
    rw [← hKdef] at h
    calc Aᴴ * Jm ε * A = Mᴴ * ((Kᴴ * P)ᴴ * Jm ε * (Kᴴ * P)) * M := by
          simp only [hA, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hAinj : Function.Injective A.mulVec := by
    refine Function.LeftInverse.injective (g := ((Mᴴ * (Pᴴ * Jm ε * P) * M)⁻¹ * (Aᴴ * Jm ε)).mulVec) fun v => ?_
    have h : ((Mᴴ * (Pᴴ * Jm ε * P) * M)⁻¹ * (Aᴴ * Jm ε)) * A = 1 := by
      rw [Matrix.mul_assoc, hAG, Matrix.nonsing_inv_mul _ hGd]
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have h0 : ∀ i ∈ S, ∀ c, A i c = 0 := fun i hi c => by
    rw [hA, hKdef]; exact rows_zero k S C M hspan hCM hi c
  have c1 := card_le_card hP k S C hspan L hL
  have c2 := le_card_compl hAinj S h0
  have c3 : Fintype.card (Sᶜ : Set (Fin n)) = n - Fintype.card S := by
    rw [Fintype.card_compl_set, Fintype.card_fin]
  have c4 : Fintype.card S ≤ n := by simpa using set_fintype_card_le_univ S
  have hce : Fintype.card (Sᶜ : Set (Fin n)) = n' := by omega
  obtain ⟨e0⟩ : Nonempty (Fin n' ≃ (Sᶜ : Set (Fin n))) := ⟨(Fintype.equivFinOfCardEq hce).symm⟩
  obtain ⟨e, he'⟩ : ∃ e : Fin n' → Fin n, e = fun a => (e0 a : Fin n) := ⟨_, rfl⟩
  have he : Function.Injective e := by
    rw [he']; exact Subtype.val_injective.comp e0.injective
  have hre : ∀ i, i ∉ S → i ∈ Set.range e := fun i hi => ⟨e0.symm ⟨i, hi⟩, by simp [he']⟩
  have hrn : ∀ i, i ∈ S → i ∉ Set.range e := by
    rintro i hi ⟨a, rfl⟩
    rw [he'] at hi
    exact (e0 a).2 hi
  obtain ⟨E, hE⟩ : ∃ E, E = incl e := ⟨_, rfl⟩
  obtain ⟨F, hFd⟩ : ∃ F, F = Eᴴ * A := ⟨_, rfl⟩
  have hEE : Eᴴ * E = 1 := hE ▸ incl_ct_mul he
  have hEF : E * F = A := by
    ext i c
    by_cases hi : i ∈ S
    · rw [hE, incl_mul_apply_of_notMem _ (hrn i hi), h0 i hi]
    · obtain ⟨a, rfl⟩ := hre i hi
      rw [hE, incl_mul_apply he, hFd, hE, incl_ct_mul_apply]
  have hJE : Jm ε * E = E * Jm (ε ∘ e) := hE ▸ Jm_mul_incl ε e
  have hEJ : Eᴴ * Jm ε = Jm (ε ∘ e) * Eᴴ := hE ▸ incl_ct_mul_Jm ε e
  have hFJ : Fᴴ * Jm (ε ∘ e) * F = Mᴴ * (Pᴴ * Jm ε * P) * M := by
    rw [← hAG, ← hEF, Matrix.conjTranspose_mul]
    calc Fᴴ * Jm (ε ∘ e) * F = Fᴴ * ((Eᴴ * E) * Jm (ε ∘ e)) * F := by rw [hEE, Matrix.one_mul]
      _ = Fᴴ * (Eᴴ * (E * Jm (ε ∘ e))) * F := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hJE]; simp only [Matrix.mul_assoc]
  have hdet : IsUnit ((Fᴴ * Jm (ε ∘ e)).det * F.det) := by
    rw [← Matrix.det_mul, hFJ]; exact hGd
  have hFdet : IsUnit F.det := isUnit_of_mul_isUnit_right hdet
  have hFu : IsUnit F := (Matrix.isUnit_iff_isUnit_det F).2 hFdet
  have hFJd : IsUnit (Fᴴ * Jm (ε ∘ e)).det := isUnit_of_mul_isUnit_left hdet
  have hFJu : IsUnit (Fᴴ * Jm (ε ∘ e)) := (Matrix.isUnit_iff_isUnit_det _).2 hFJd
  have hM : P⁻¹ * K * A = M := by
    rw [hA]
    calc P⁻¹ * K * (Kᴴ * P * M) = P⁻¹ * (K * Kᴴ) * P * M := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hKK, Matrix.mul_one, Matrix.nonsing_inv_mul _ hPd, Matrix.one_mul]
  have hFF : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ hFdet
  refine ⟨ε ∘ e, F, (MulAut.conj k).toMonoidHom.comp (blockDiagonalOfBlocks he ε), hFu, hFJ, continuous_conj_blockEmbedding he ε k,
    fun k' => ?_⟩
  have hj : toMK (((MulAut.conj k).toMonoidHom.comp (blockDiagonalOfBlocks he ε)) k') = K * blk e (toMK k') * Kᴴ := by
    rw [hKdef, ← toMK_inv]; rfl
  obtain ⟨a, ha⟩ : ∃ a, a = toMK k' := ⟨_, rfl⟩
  rw [hj, ← ha]
  refine ⟨?_, fun x hx => ?_⟩
  · calc P⁻¹ * (K * blk e a * Kᴴ) * P * M = P⁻¹ * K * blk e a * A := by simp only [hA, Matrix.mul_assoc]
      _ = P⁻¹ * K * (blk e a * E) * F := by rw [← hEF]; simp only [Matrix.mul_assoc]
      _ = P⁻¹ * K * E * (F * F⁻¹) * a * F := by
          rw [hE, blk_mul_incl he, hFF, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P⁻¹ * K * (E * F) * (F⁻¹ * a * F) := by simp only [Matrix.mul_assoc]
      _ = M * (F⁻¹ * a * F) := by rw [hEF, hM]
  · have h1 : Mᴴ * (Pᴴ * Jm ε * P) = Fᴴ * Jm (ε ∘ e) * (Eᴴ * (Kᴴ * P)) := by
      have h := ct_J_ct k P
      rw [← hKdef] at h
      have h2 : Mᴴ * (Kᴴ * P)ᴴ = Fᴴ * Eᴴ := by
        rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hEF, hA, Matrix.mul_assoc]
      calc Mᴴ * (Pᴴ * Jm ε * P) = Mᴴ * (Kᴴ * P)ᴴ * Jm ε * (Kᴴ * P) := by
            rw [← h]; simp only [Matrix.mul_assoc]
        _ = Fᴴ * (Eᴴ * Jm ε) * (Kᴴ * P) := by rw [h2]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hEJ]; simp only [Matrix.mul_assoc]
    have hz : (Eᴴ * (Kᴴ * P)) *ᵥ x = 0 := by
      rw [h1, ← Matrix.mulVec_mulVec] at hx
      refine Matrix.mulVec_injective_iff_isUnit.2 hFJu ?_
      rw [hx, Matrix.mulVec_zero]
    have h2 : P⁻¹ * (K * blk e a * Kᴴ) * P = 1 + P⁻¹ * K * E * (a - 1) * (Eᴴ * (Kᴴ * P)) := by
      have h3 : P⁻¹ * (K * Kᴴ) * P = 1 := by
        rw [hKK, Matrix.mul_one, Matrix.nonsing_inv_mul _ hPd]
      rw [blk, ← hE]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
      rw [h3]
      simp only [Matrix.mul_assoc]
    rw [h2, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, add_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames
end

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames

variable {D : D7}

theorem map_cT (τ : D.what₂.Tau) {p q : Type} (A : Matrix p q D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A).map (tauE D τ) = (A.map (tauE D τ))ᴴ := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
  exact Formalism.IndefR.Eqv.tauE_star D τ _

theorem cT_gram_mul_apply (V : HSp D) {p q : Type} (A : Matrix (Fin V.rank) p D.host.E)
    (B : Matrix (Fin V.rank) q D.host.E) (a : p) (b : q) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) a b =
      V.hT (V.frame.equivFun.symm fun j => A j a) (V.frame.equivFun.symm fun j => B j b) := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
    Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, HSpace.gram, Finset.sum_mul,
    Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, starRingEnd_apply]
  change star (A j a) * _ * _ = _
  ring

theorem frame_col (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) (c : Fin V'.rank) :
    (V.frame.equivFun.symm fun j => frameMat V V' ι j c) = ι (V'.frame c) := by
  have : (fun j => frameMat V V' ι j c) = V.frame.equivFun (ι (V'.frame c)) := by
    funext j
    simp [frameMat, LinearMap.toMatrix_apply]
  rw [this, LinearEquiv.symm_apply_apply]

theorem ct_gramAt_map (V : HSp D) (τ : D.what₂.Tau) {p q : Type} (A : Matrix (Fin V.rank) p D.host.E)
    (B : Matrix (Fin V.rank) q D.host.E) [Fintype p] :
    (A.map (tauE D τ))ᴴ * gramAt D V τ * B.map (tauE D τ) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).map (tauE D τ) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_cT]
  rfl

theorem gramAt_isom (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) (hι : HSpace.IsIsomEmb V' V ι) (τ : D.what₂.Tau) :
    ((frameMat V V' ι).map (tauE D τ))ᴴ * gramAt D V τ * (frameMat V V' ι).map (tauE D τ) = gramAt D V' τ := by
  rw [ct_gramAt_map]
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram * frameMat V V' ι = V'.gram := by
    refine Matrix.ext fun a b => ?_
    rw [cT_gram_mul_apply, frame_col, frame_col]
    exact hι _ _
  rw [h]
  rfl

theorem isUnit_gramAt (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
  have h := (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).map (tauE D τ)
  rw [RingHom.map_det] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames
end

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames

variable {D : D7}

theorem exists_leftInv (V : HSp D) (τ : D.what₂.Tau) (hG : (gramAt D V τ)ᴴ = gramAt D V τ) {m : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) (U : Set (Fin m)) [Fintype U] [DecidableEq U] :
    ∃ L : Matrix (U ⊕ U) (Fin V.rank) ℂ,
      L * Matrix.fromCols ((X.map (tauE D τ)).submatrix id ((↑) : U → Fin m))
        ((Y.map (tauE D τ)).submatrix id ((↑) : U → Fin m)) = 1 := by
  have hv : Function.Injective ((↑) : U → Fin m) := Subtype.val_injective
  have key : ∀ (A B : Matrix (Fin V.rank) (Fin m) D.host.E),
      ((A.map (tauE D τ)).submatrix id ((↑) : U → Fin m))ᴴ * gramAt D V τ *
        (B.map (tauE D τ)).submatrix id ((↑) : U → Fin m) =
      ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).map (tauE D τ)).submatrix (↑) (↑) := by
    intro A B
    rw [← ct_gramAt_map]
    ext a b
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
  have hxx := key X X
  have hyy := key Y Y
  have hxy := key X Y
  rw [hW.xx] at hxx
  rw [hW.yy] at hyy
  rw [hW.xy] at hxy
  have hxx0 : ((X.map (tauE D τ)).submatrix id ((↑) : U → Fin m))ᴴ * gramAt D V τ *
      (X.map (tauE D τ)).submatrix id ((↑) : U → Fin m) = 0 := by
    rw [hxx]; ext a b; simp
  have hyy0 : ((Y.map (tauE D τ)).submatrix id ((↑) : U → Fin m))ᴴ * gramAt D V τ *
      (Y.map (tauE D τ)).submatrix id ((↑) : U → Fin m) = 0 := by
    rw [hyy]; ext a b; simp
  have hxy1 : ((X.map (tauE D τ)).submatrix id ((↑) : U → Fin m))ᴴ * gramAt D V τ *
      (Y.map (tauE D τ)).submatrix id ((↑) : U → Fin m) = 1 := by
    rw [hxy]; ext a b; simp [Matrix.one_apply, hv.eq_iff]
  have hyx1 : ((Y.map (tauE D τ)).submatrix id ((↑) : U → Fin m))ᴴ * gramAt D V τ *
      (X.map (tauE D τ)).submatrix id ((↑) : U → Fin m) = 1 := by
    have := congrArg Matrix.conjTranspose hxy1
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, hG,
      Matrix.mul_assoc] using this
  refine ⟨Matrix.fromRows (((Y.map (tauE D τ)).submatrix id ((↑) : U → Fin m))ᴴ * gramAt D V τ)
    (((X.map (tauE D τ)).submatrix id ((↑) : U → Fin m))ᴴ * gramAt D V τ), ?_⟩
  rw [Matrix.fromRows_mul_fromCols, hyx1, hyy0, hxx0, hxy1, Matrix.fromBlocks_one]

theorem rank_le_card_add (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) {κ : Type} [Fintype κ] (u : κ → V.V)
    (hr : ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ c, V.hT (u c) v = 0) :
    V.rank ≤ Fintype.card κ + V'.rank := by
  let ψ : V.V →ₗ[D.host.E] (κ → D.host.E) := LinearMap.pi fun c => V.hT (u c)
  have hk : LinearMap.ker ψ = LinearMap.range ι := by
    ext v
    rw [hr v, LinearMap.mem_ker]
    exact funext_iff
  have a := LinearMap.finrank_range_add_finrank_ker ψ
  have b : Module.finrank D.host.E (LinearMap.range ψ) ≤ Fintype.card κ :=
    (Submodule.finrank_le _).trans_eq (Module.finrank_fintype_fun_eq_card _)
  have c : Module.finrank D.host.E (LinearMap.ker ψ) ≤ V'.rank := by
    rw [hk, ← V'.rank_eq]
    exact LinearMap.finrank_range_le ι
  rw [V.rank_eq] at a
  omega

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames
end

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames

variable {D : D7}

theorem exists_at (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D)
    (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hP : IsUnit P)
    (hPG : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) (T : Finset (Fin m)) (k : Formalism.REAL.KG e)
    (S : Set (Fin V.rank))
    (hk : Submodule.span ℂ (Set.range (fun i : upTo T => (P *ᵥ fun j => tauE D τ (X j i))) ∪
        Set.range (fun i : upTo T => (P *ᵥ fun j => tauE D τ (Y j i)))) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin V.rank) (1 : ℂ) : Fin V.rank → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin)
    (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) (hι : HSpace.IsIsomEmb V' V ι)
    (hr : ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧
      V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0)
    (s : GA D V' →* GA D V) (hs : ∀ h, EmbRel V V' ι (s h) h) :
    ∃ (e' : Fin V'.rank → Bool) (F : Matrix (Fin V'.rank) (Fin V'.rank) ℂ) (j : Formalism.REAL.KG e' →* Formalism.REAL.KG e),
      (IsUnit F ∧ Fᴴ * Formalism.REAL.Jm e' * F = gramAt D V' τ) ∧ Continuous j ∧
      ∀ k', s (kAt θ V' τ e' F k') = kAt θ V τ e P (j k') := by
  classical
  have hGH : (gramAt D V τ)ᴴ = gramAt D V τ := by
    rw [← hPG]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.REAL.Jm_conjTranspose,
      Matrix.mul_assoc]
  obtain ⟨L, hL⟩ := exists_leftInv V τ hGH X Y hW (upTo T)
  obtain ⟨Xu, hXu⟩ : ∃ Xu, Xu = (X.map (tauE D τ)).submatrix id ((↑) : upTo T → Fin m) := ⟨_, rfl⟩
  obtain ⟨Yu, hYu⟩ : ∃ Yu, Yu = (Y.map (tauE D τ)).submatrix id ((↑) : upTo T → Fin m) := ⟨_, rfl⟩
  rw [← hXu, ← hYu] at hL
  obtain ⟨M, hM⟩ : ∃ M, M = (frameMat V V' ι).map (tauE D τ) := ⟨_, rfl⟩
  have hspan : Submodule.span ℂ (Set.range fun c => P *ᵥ (Matrix.fromCols Xu Yu).col c) =
      (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin V.rank) (1 : ℂ) : Fin V.rank → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin := by
    have h : (fun c => P *ᵥ (Matrix.fromCols Xu Yu).col c) =
        Sum.elim (fun i : upTo T => (P *ᵥ fun j => tauE D τ (X j i)))
          (fun i : upTo T => (P *ᵥ fun j => tauE D τ (Y j i))) := by
      funext c
      rcases c with i | i
      · simp only [Sum.elim_inl]
        congr 1
        funext j
        simp [hXu, Matrix.col_apply]
      · simp only [Sum.elim_inr]
        congr 1
        funext j
        simp [hYu, Matrix.col_apply]
    rw [h, Set.Sum.elim_range]
    exact hk
  have orth : ∀ A : Matrix (Fin V.rank) (Fin m) D.host.E,
      (∀ i ∈ upTo T, ∀ c, V.hT (V.frame.equivFun.symm fun j => A j i) (ι (V'.frame c)) = 0) →
      Mᴴ * gramAt D V τ * (A.map (tauE D τ)).submatrix id ((↑) : upTo T → Fin m) = 0 := by
    intro A hA
    have h1 : ((A.map (tauE D τ)).submatrix id ((↑) : upTo T → Fin m))ᴴ * gramAt D V τ * M = 0 := by
      have h2 := ct_gramAt_map V τ A (frameMat V V' ι)
      ext i c
      have h3 := congrFun (congrFun h2 i.1) c
      rw [Matrix.map_apply, cT_gram_mul_apply, frame_col, hA i.1 i.2 c, map_zero] at h3
      refine Eq.trans ?_ h3
      rw [hM]
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    have h4 := congrArg Matrix.conjTranspose h1
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero, hGH,
      Matrix.mul_assoc] using h4
  have hXM : Mᴴ * gramAt D V τ * Xu = 0 := by
    rw [hXu]
    exact orth X fun i hi c => ((hr _).1 ⟨_, rfl⟩ i hi).1
  have hYM : Mᴴ * gramAt D V τ * Yu = 0 := by
    rw [hYu]
    exact orth Y fun i hi c => ((hr _).1 ⟨_, rfl⟩ i hi).2
  have hCM : Mᴴ * (Pᴴ * Formalism.REAL.Jm e * P) * Matrix.fromCols Xu Yu = 0 := by
    rw [hPG, Matrix.mul_fromCols, hXM, hYM]
    ext a c
    rcases c with c | c <;> rfl
  have hG' : Mᴴ * (Pᴴ * Formalism.REAL.Jm e * P) * M = gramAt D V' τ := by
    rw [hPG, hM]
    exact gramAt_isom V V' ι hι τ
  have hGu : IsUnit (Mᴴ * (Pᴴ * Formalism.REAL.Jm e * P) * M) := by
    rw [hG']
    exact isUnit_gramAt V' τ
  have hcard : V.rank ≤ Fintype.card (upTo T ⊕ upTo T) + V'.rank := by
    refine rank_le_card_add V V' ι (Sum.elim (fun i => V.frame.equivFun.symm fun j => X j i)
      (fun i => V.frame.equivFun.symm fun j => Y j i)) fun v => ?_
    rw [hr v]
    constructor
    · rintro h (i | i)
      · exact (h i.1 i.2).1
      · exact (h i.1 i.2).2
    · intro h i hi
      exact ⟨h (Sum.inl ⟨i, hi⟩), h (Sum.inr ⟨i, hi⟩)⟩
  obtain ⟨e', F, j, hFu, hFJ, hjc, hemb⟩ := exists_frame hP k S (Matrix.fromCols Xu Yu) M hspan hCM L hL hGu hcard
  rw [hG'] at hFJ
  obtain ⟨s0, -, hs0, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  refine ⟨e', F, j, ⟨hFu, hFJ⟩, hjc, fun k' => ?_⟩
  have hE := hemb k'
  rw [hPG, hM] at hE
  have hrel := GlobalTheory.EmbAtPlace.embRel_atTau D θ hθ V' V ι τ _ _ (conj_mem_UH hFu hFJ k')
    (conj_mem_UH hP hPG (j k')) hE
  rw [(hs0 _ _).1 (hs _)]
  exact ((hs0 _ _).1 hrel).symm

theorem exists_restricted_frame : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε fr → ∀ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∃ (ε' : D.what₂.Tau → Fin V'.rank → Bool) (fr' : D.what₂.Tau → Matrix (Fin V'.rank) (Fin V'.rank) ℂ) (j : ∀ τ, Formalism.REAL.KG (ε' τ) →* Formalism.REAL.KG (ε τ)), IsFrameFam V' ε' fr' ∧ (∀ τ, Continuous (j τ)) ∧ ∀ τ k, s (kAt θ V' τ (ε' τ) (fr' τ) k) = kAt θ V τ (ε τ) (fr τ) (j τ k) := by
  intro D θ hθ V ε fr hfr m X Y hW T hA V' ι hι hr s hs
  have key : ∀ τ, ∃ (e' : Fin V'.rank → Bool) (F : Matrix (Fin V'.rank) (Fin V'.rank) ℂ)
      (j : Formalism.REAL.KG e' →* Formalism.REAL.KG (ε τ)),
      (IsUnit F ∧ Fᴴ * Formalism.REAL.Jm e' * F = gramAt D V' τ) ∧ Continuous j ∧
      ∀ k', s (kAt θ V' τ e' F k') = kAt θ V τ (ε τ) (fr τ) (j k') := fun τ => by
    obtain ⟨k, S, hk⟩ := hA τ
    exact exists_at θ hθ V τ (ε τ) (fr τ) (hfr τ).1 (hfr τ).2 m X Y hW T k S hk V' ι hι hr s hs
  choose ε' fr' j h1 h2 h3 using key
  exact ⟨ε', fr', j, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Frames
end
