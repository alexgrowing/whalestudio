import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Formalism.GradedWeylDivisibility.FinalC

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.SubstMem

open Formalism.GradedWeylDivisibility

variable {K : Type} [Field K]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in

theorem _root_.GlobalTheory.SubstMem.rename_mem_dualWeyl {a b : ℕ} (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ)
    (h1 : ∀ i, ν' (Fin.castLE hab i) = ν i) (h2 : ∀ j : Fin b, a ≤ (j : ℕ) → ν' j = 0)
    (f : MvPolynomial (Fin a × Fin a) K) (hf : f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K a a ν) :
    rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K b b ν' := by
  rw [_root_.Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hhom, hinv⟩ := hf
  refine ⟨?_, ?_⟩
  · intro d hd
    have hinj : Function.Injective (Prod.map (Fin.castLE hab) (Fin.castLE hab)) :=
      (Fin.castLE_injective hab).prodMap (Fin.castLE_injective hab)
    have hmem : d ∈ (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f).support :=
      mem_support_iff.2 hd
    rw [support_rename_of_injective hinj, Finset.mem_image] at hmem
    obtain ⟨d0, hd0, rfl⟩ := hmem
    have h0 := hhom (mem_support_iff.1 hd0)
    rw [Finsupp.weight_apply] at h0
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
    funext k
    by_cases hk : (k : ℕ) < a
    · have hk' : k = Fin.castLE hab ⟨k, hk⟩ := Fin.ext rfl
      rw [hk', h1, ← h0]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [_root_.Formalism.GradedWeylDivisibility.colW, Pi.single_apply]
      simp only [Fin.ext_iff, Fin.coe_castLE]
    · rw [h2 k (not_lt.1 hk)]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_eq_zero fun v _ => ?_
      have hne : Fin.castLE hab v.2 ≠ k := by
        intro h; apply hk; rw [← h]; simp
      simp [_root_.Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hne]
  · intro l j hlj
    by_cases hj : (j : ℕ) < a
    · have hl : (l : ℕ) < a := lt_trans hlj hj
      obtain ⟨l', rfl⟩ : ∃ l' : Fin a, Fin.castLE hab l' = l := ⟨⟨l, hl⟩, Fin.ext rfl⟩
      obtain ⟨j', rfl⟩ : ∃ j' : Fin a, Fin.castLE hab j' = j := ⟨⟨j, hj⟩, Fin.ext rfl⟩
      have key : (_root_.Formalism.GradedWeylDivisibility.colAddGen K (Fin.castLE hab l') (Fin.castLE hab j')).comp
          (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) =
          (rename (Option.map (Prod.map (Fin.castLE hab) (Fin.castLE hab)))).comp
            (_root_.Formalism.GradedWeylDivisibility.colAddGen K (r := a) l' j') := by
        apply MvPolynomial.algHom_ext
        rintro ⟨v1, v2⟩
        by_cases hv : v2 = j'
        · subst hv
          simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, Prod.map_fst,
            if_pos rfl]
          simp only [ite_true, if_true, map_add, map_mul, rename_X]
          rfl
        · have hv' : Fin.castLE hab v2 ≠ Fin.castLE hab j' :=
            fun h => hv (Fin.castLE_injective hab h)
          simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, Prod.map_fst,
            if_neg hv, if_neg hv']
          rfl
      have e := DFunLike.congr_fun key f
      simp only [AlgHom.comp_apply] at e
      rw [e, hinv l' j' (show l' < j' from hlj), rename_rename, rename_rename]
      rfl
    · have key : (_root_.Formalism.GradedWeylDivisibility.colAddGen K l j).comp (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) =
          (rename some).comp (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) := by
        apply MvPolynomial.algHom_ext
        intro v
        have hne : Fin.castLE hab v.2 ≠ j := by
          intro h; apply hj; rw [← h]; exact v.2.isLt
        simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, if_neg hne]
      exact DFunLike.congr_fun key f

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in

theorem _root_.GlobalTheory.SubstMem.det_pow_mem (a m : ℕ) :
    _root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl ^ m ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K a a (fun _ => m) := by
  refine _root_.Formalism.GradedWeylDivisibility.dualWeyl_of_eq (_root_.Formalism.GradedWeylDivisibility.dualWeyl_pow (_root_.Formalism.GradedWeylDivisibility.initMinor_mem (R := K) (id : Fin a → Fin a) le_rfl) m) ?_
  funext i
  simp [_root_.Formalism.GradedWeylDivisibility.initW]

def padRows {a b : ℕ} (A : Matrix (Fin a) (Fin b) K) : Matrix (Fin b) (Fin b) K :=
  fun α β => if h : (α : ℕ) < a then A ⟨α, h⟩ β else 0

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.substAdj_blockEmb {ι : Type} {a b : ℕ} (hab : a ≤ b)
    (ap : ι → Matrix (Fin a) (Fin b) K) (τ : ι) (f : MvPolynomial (Fin a × Fin a) K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab ap (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ f) =
      _root_.Formalism.GradedWeylDivisibility.blockEmb K τ (_root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))
        (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f)) := by
  have key : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab ap).comp (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ) = (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ).comp
      ((_root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))).comp
        (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)))) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj, _root_.Formalism.GradedWeylDivisibility.blockEmb, _root_.Formalism.GradedWeylDivisibility.rowAct, _root_.GlobalTheory.SubstMem.padRows, map_sum]
  exact DFunLike.congr_fun key f

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem DomWeight_detShift_eq_w_last {N : ℕ} (l : _root_.Formalism.BasicNotions.DomWeight N) (h : 0 < N) :
    l.detShift = l.w ⟨N - 1, by omega⟩ := by
  unfold _root_.Formalism.BasicNotions.DomWeight.detShift
  rw [dif_pos h]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem DomWeight_detShift_le_w {N : ℕ} (l : _root_.Formalism.BasicNotions.DomWeight N) (i : Fin N) : l.detShift ≤ l.w i := by
  rw [DomWeight_detShift_eq_w_last l (Fin.pos i)]
  exact l.anti (Fin.le_def.2 (by simp; omega))

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem isWeightedHomogeneous_colW_rowAct_of_isWeightedHomogeneous {R : Type} [CommRing R] {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) {f : MvPolynomial (Fin r × Fin n) R} {ν : Fin n → ℕ}
    (hf : IsWeightedHomogeneous (_root_.Formalism.GradedWeylDivisibility.colW r n) f ν) :
    IsWeightedHomogeneous (_root_.Formalism.GradedWeylDivisibility.colW r n) (_root_.Formalism.GradedWeylDivisibility.rowAct R g f) ν := by
  rw [← mem_weightedHomogeneousSubmodule]
  rw [← support_sum_monomial_coeff f, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule, ← hf (mem_support_iff.1 hd)]
  have e : _root_.Formalism.GradedWeylDivisibility.rowAct R g (monomial d (coeff d f)) =
      C (coeff d f) * d.prod (fun v k => (_root_.Formalism.GradedWeylDivisibility.rowAct R g (X v)) ^ k) := by
    simp only [_root_.Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, aeval_X, algebraMap_eq]
  rw [e, Finsupp.weight_apply, ← zero_add (d.sum fun i c => c • _root_.Formalism.GradedWeylDivisibility.colW r n i)]
  exact (isWeightedHomogeneous_C _ _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun v _ => (_root_.Formalism.GradedWeylDivisibility.rowAct_X_isWH g v).pow (d v))

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem rowAct_mem_dualWeyl_of_mem_dualWeyl {R : Type} [CommRing R] {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : _root_.Formalism.GradedWeylDivisibility.rowAct R g f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
  rw [_root_.Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hf ⊢
  refine ⟨isWeightedHomogeneous_colW_rowAct_of_isWeightedHomogeneous g hf.1, fun l j hlj => ?_⟩
  rw [_root_.Formalism.GradedWeylDivisibility.colAddGen_rowAct, hf.2 l j hlj, ← _root_.Formalism.GradedWeylDivisibility.rename_rowAct]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem frDet_eq_blockEmb_initMinor_id {K : Type} [Field K] {ι : Type} (a : ℕ) (τ : ι) :
    _root_.Formalism.L2.Ker.frDet K a τ = _root_.Formalism.GradedWeylDivisibility.blockEmb K τ (_root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl) := by
  simp only [_root_.Formalism.L2.Ker.frDet, _root_.Formalism.GradedWeylDivisibility.initMinor, AlgHom.map_det]
  congr 1
  ext p q
  simp [_root_.Formalism.GradedWeylDivisibility.blockEmb]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in

theorem _root_.GlobalTheory.SubstMem.substAdj_sharp_mem : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι]
    (a b : ℕ) (hab : a < b) (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (lam' : ι → _root_.Formalism.BasicNotions.DomWeight b) (s s' : ι → ℤ)
    (n : ι → ℕ), _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.WtCompat hab lam lam' s s' n →
    ∀ (ap : ι → Matrix (Fin a) (Fin b) K), ∀ P ∈ _root_.Formalism.L2.DIV.VV K lam,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab.le ap (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n P) ∈ _root_.Formalism.L2.DIV.VV K lam' := by
  intro K _ ι _ a b hab lam lam' s s' n hc ap P hP
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hd' : ∀ τ, (lam' τ).detShift = -s τ := fun τ => by
    rw [DomWeight_detShift_eq_w_last _ (by omega)]
    exact hc2 τ _ (by simp; omega)
  have hw1 : ∀ τ i, (lam' τ).natW (Fin.castLE hab.le i) = (lam τ).natW i + n τ := by
    intro τ i
    have e1 := hc1 τ i
    have e2 := hc3 τ
    have e3 := DomWeight_detShift_le_w (lam τ) i
    have e4 := hd' τ
    simp only [_root_.Formalism.BasicNotions.DomWeight.natW]
    omega
  have hw2 : ∀ τ (j : Fin b), a ≤ (j : ℕ) → (lam' τ).natW j = 0 := by
    intro τ j hj
    have e1 := hc2 τ j hj
    have e4 := hd' τ
    simp only [_root_.Formalism.BasicNotions.DomWeight.natW]
    omega
  have hsharp : ∀ Q : _root_.Formalism.L2.DIV.Pol K ι a, _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n Q = Q * ∏ τ, _root_.Formalism.L2.Ker.frDet K a τ ^ n τ :=
    fun Q => rfl
  unfold _root_.Formalism.L2.DIV.VV _root_.Formalism.GradedWeylDivisibility.tensorLat at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [hsharp, ← Finset.prod_mul_distrib, map_prod]
    refine Submodule.subset_span ⟨fun τ => _root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))
      (rename (Prod.map (Fin.castLE hab.le) (Fin.castLE hab.le))
        (F τ * _root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl ^ n τ)), fun τ => ?_, ?_⟩
    · refine rowAct_mem_dualWeyl_of_mem_dualWeyl _ ?_
      refine _root_.GlobalTheory.SubstMem.rename_mem_dualWeyl hab.le ((lam τ).natW + fun _ => n τ) _
        (fun i => by simp [hw1]) (hw2 τ) _ ?_
      exact _root_.Formalism.GradedWeylDivisibility.dualWeyl_mul (hF τ) (_root_.GlobalTheory.SubstMem.det_pow_mem a (n τ))
    · refine Finset.prod_congr rfl fun τ _ => ?_
      rw [frDet_eq_blockEmb_initMinor_id, ← map_pow, ← map_mul, _root_.GlobalTheory.SubstMem.substAdj_blockEmb]
  | zero => simp [hsharp]
  | add x y _ _ hx hy =>
    rw [hsharp, add_mul, map_add]
    exact add_mem (by rw [← hsharp]; exact hx) (by rw [← hsharp]; exact hy)
  | smul c x _ hx =>
    rw [hsharp, smul_mul_assoc, map_smul]
    exact Submodule.smul_mem _ c (by rw [← hsharp]; exact hx)

end GlobalTheory.SubstMem
