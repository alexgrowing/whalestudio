import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Proj

open GlobalTheory.StdPar

section Abstract

variable {A : Type} [CommRing A] {n r : ℕ} {X : Matrix (Fin n) (Fin r) A} {K : Matrix (Fin r) (Fin n) A}

theorem mulVec_left_inv (hKX : K * X = 1) {I : Set (Fin r)} {y : Fin n → A}
    (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : X *ᵥ (K *ᵥ y) = y := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.eqLocus (X * K).mulVecLin LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, -, rfl⟩
    change (X * K * X).col i = _
    rw [Matrix.mul_assoc, hKX, Matrix.mul_one]
    rfl
  rw [mulVec_mulVec]
  exact this hy

theorem mulVec_mem_span {I : Set (Fin r)} {a : Fin r → A} (ha : ∀ i, i ∉ I → a i = 0) :
    X *ᵥ a ∈ Submodule.span A ((fun i => Xᵀ i) '' I) := by
  rw [mulVec_eq_sum]
  refine sum_mem fun i _ => ?_
  rw [op_smul_eq_smul]
  by_cases hi : i ∈ I
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [ha i hi, zero_smul]
    exact zero_mem _

theorem coef_mul (hKX : K * X = 1) (M N : Matrix (Fin n) (Fin n) A) (hN : (N - 1) * X = X * (K * ((N - 1) * X))) :
    K * ((M * N - 1) * X) = K * ((M - 1) * X) + K * ((N - 1) * X) + K * ((M - 1) * X) * (K * ((N - 1) * X)) := by
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc K, Matrix.mul_assoc (M - 1) X, ← hN,
    Matrix.mul_assoc (M - 1)]

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}
  {K : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)}

omit [NumberField E] in

theorem col_mem {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) (j : Fin r) :
    (((matHom _ σ J g).1 - 1) * adMat F X).col j ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := by
  have := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  rw [Matrix.sub_mul, Matrix.one_mul]
  exact this

omit [NumberField E] in

theorem coef_eq_zero (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {i j : Fin r}
    (hi : ¬ ∃ k ∈ T, i ≤ k ∧ k < j) : (K * (((matHom _ σ J g).1 - 1) * adMat F X) : Matrix (Fin r) (Fin r) _) i j = 0 :=
  Norm.row_span (Z := K) (a := i) (fun m hm => by
    rw [hKX, Matrix.one_apply_ne]
    rintro rfl
    exact hi hm) (col_mem hg j)

omit [NumberField E] in

theorem eq_mul_coef (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) :
    ((matHom _ σ J g).1 - 1) * adMat F X = adMat F X * (K * (((matHom _ σ J g).1 - 1) * adMat F X)) :=
  Matrix.ext_col fun j => (mulVec_left_inv hKX (col_mem hg j)).symm

theorem exists_blockProj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∃ π : GlobalTheory.StdPar.unip σ J Xf (insert k S) → (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E), Continuous π ∧
          (∀ a b, π (a * b) = π a + π b) ∧
          (∀ (a : GlobalTheory.StdPar.unip σ J Xf (insert k S)) x, (a : GAd σ J) = ι (GlobalTheory.CuspRep.unip x) → π a = x) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), π a = 0 ↔ (a : GAd σ J) ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), (a : GAd σ J) ∈ ratPts σ J → π a ∈ GlobalTheory.CuspRep.ratN E d r') := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, hΦc, _, hj, hΦ, hι⟩ hS ⟨k₀, hk₀, hk₀'⟩ hl r' hr0 hrd k hk
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
  have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
  have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hKY : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [hm, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show jj (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  let c : GAd σ J → Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun g =>
    adMat F (cT (σ : E →+* E) Y * J) * (((matHom _ σ J g).1 - 1) * adMat F X)
  have hc : Continuous c := continuous_const.matrix_mul ((continuous_mat.sub continuous_const).matrix_mul continuous_const)
  refine ⟨fun a p => Φ (c a (e p.1.1) (e p.1.2)), ?_, fun a b => ?_, fun a x hx => ?_, fun a => ⟨fun h0 => ?_, fun ha => ?_⟩,
    fun a ha => ?_⟩
  · exact continuous_pi fun p => hΦc.comp ((hc.comp continuous_subtype_val).matrix_elem _ _)
  · funext p
    have h1 : c (a * b : unip σ J X (insert k S)) = c a + c b + c a * c b := by
      simp only [c]
      rw [Subgroup.coe_mul, map_mul, Units.val_mul]
      exact coef_mul hKX _ _ (eq_mul_coef hKX b.2)
    have h2 : (c a * c b) (e p.1.1) (e p.1.2) = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have hp2 := p.1.2.2
      by_cases hmk : m ≤ k
      · rw [show c a (e p.1.1) m = 0 from coef_eq_zero hKX a.2 ?_, zero_mul]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : l + p.1.1.val ≤ k'.val := h3
        have h4' : k'.val < m.val := h4
        have h5 : m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
      · rw [show c b m (e p.1.2) = 0 from coef_eq_zero hKX b.2 ?_, mul_zero]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : m.val ≤ k'.val := h3
        have h4' : k'.val < l + p.1.2.val := h4
        have h5 : ¬ m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
    change Φ (c (a * b : unip σ J X (insert k S)) _ _) = Φ _ + Φ _
    rw [h1, Matrix.add_apply, h2, add_zero, Matrix.add_apply, map_add]
  · funext p
    have b1 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h X) = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hKX (e i)) (e j)).trans (by simp [Matrix.one_apply, e, Fin.ext_iff])
    have b2 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h Y) = 0 := Matrix.ext fun i j =>
      congrFun (congrFun hKY (e i)) (e j)
    have h1 : c a (e p.1.1) (e p.1.2) = (adMat F (cT (σ : E →+* E) (blkCols h Y) * J) *
        (((matHom _ σ J (a : GAd σ J)).1 - 1) * adMat F (blkCols h X)) : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 := rfl
    have hne : p.1.1 ≠ p.1.2 := fun h' => by have := p.2; rw [h'] at this; omega
    change Φ (c a _ _) = _
    rw [h1, hx, hι, add_assoc, add_sub_cancel_left, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc, b1,
      Matrix.mul_one, ← Matrix.mul_assoc, b1, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F _),
      b2, Matrix.zero_mul, add_zero, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, Matrix.map_apply,
      RingEquiv.apply_symm_apply]
    change (1 + GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 = _
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, GlobalTheory.CuspRep.nilM, Matrix.of_apply, dif_pos p.2]
  · have ha := a.2
    have hset : {i | ∃ k' ∈ insert k S, i ≤ k'} = {i | ∃ k' ∈ S, i ≤ k'} := Set.ext fun i =>
      ⟨fun ⟨k', hk', h1⟩ => by
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · exact ⟨k₀, hk₀, h1.trans (show k'.val ≤ k₀.val by omega)⟩
        · exact ⟨k', hk', h1⟩,
      fun ⟨k', hk', h1⟩ => ⟨k', Finset.mem_insert_of_mem hk', h1⟩⟩
    refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan ha ?_, fun y hy => ?_⟩, hset ▸ ha.2⟩
    · rintro i ⟨k', hk', hik, hkj⟩ m hm
      exact ⟨k', hk', hm.le.trans hik, hkj⟩
    · unfold colSpan at hy
      rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
      obtain ⟨t, rfl⟩ := hy
      rw [mulVec_smul, ← smul_sub]
      refine Submodule.smul_mem _ t ?_
      have h1 : (matHom _ σ J (a : GAd σ J)).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j = adMat F X *ᵥ (c a).col j := by
        have := congrArg (fun Z => Matrix.col Z j) (eq_mul_coef hKX ha)
        rw [Matrix.sub_mul, Matrix.one_mul] at this
        refine Eq.trans ?_ (this.trans ?_)
        · rfl
        · simp only [c]
          rw [Matrix.sub_mul, Matrix.one_mul]
          rfl
      rw [h1]
      refine mulVec_mem_span fun i hi => ?_
      by_cases hi' : ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j
      · obtain ⟨k', hk', h2, h3⟩ := hi'
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · have h2' : i.val ≤ k'.val := h2
          have h3' : k'.val < j.val := h3
          have h4 : j.val < l + d := by
            by_contra h4
            exact hi ⟨k₀, hk₀, show i.val ≤ k₀.val by omega, show k₀.val < j.val by omega⟩
          have h5 : l ≤ i.val := by
            by_contra h5
            rcases hl with hl | ⟨p, hp, hp'⟩
            · omega
            · exact hi ⟨p, hp, show i.val ≤ p.val by omega, show p.val < j.val by omega⟩
          have h6 := congrFun h0 ⟨(⟨i.val - l, by omega⟩, ⟨j.val - l, by omega⟩), by constructor <;> dsimp only <;> omega⟩
          have h7 : e ⟨i.val - l, by omega⟩ = i := Fin.ext (show l + (i.val - l) = i.val by omega)
          have h8 : e ⟨j.val - l, by omega⟩ = j := Fin.ext (show l + (j.val - l) = j.val by omega)
          change Φ (c a (e ⟨i.val - l, _⟩) (e ⟨j.val - l, _⟩)) = 0 at h6
          rw [h7, h8] at h6
          exact (map_eq_zero_iff Φ Φ.injective).1 h6
        · exact absurd ⟨k', hk', h2, h3⟩ hi
      · exact coef_eq_zero hKX ha hi'
  · funext p
    change Φ (c a _ _) = 0
    rw [show c a (e p.1.1) (e p.1.2) = 0 from coef_eq_zero hKX ha ?_, map_zero]
    rintro ⟨k', hk', h3, h4⟩
    have h3' : l + p.1.1.val ≤ k'.val := h3
    have h4' : k'.val < l + p.1.2.val := h4
    have hp2 := p.1.2.2
    exact hS k' (by omega) (by omega) hk'
  · obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
    have h1 : (matHom _ σ J (a : GAd σ J)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    refine ⟨fun p => (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X) : Matrix (Fin r) (Fin r) E) (e p.1.1) (e p.1.2), funext fun p => ?_⟩
    have h2 : c a = adMat F (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X)) := by
      simp only [c]
      rw [h1, ← hm (cT (σ : E →+* E) Y * J), ← hm (γ.1 - 1)]
      congr 2
      rw [adMat, adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    change _ = Φ (c a _ _)
    rw [h2]
    exact (hΦE _).symm

end GlobalTheory.BlockForms.Proj

end
