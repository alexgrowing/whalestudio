import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FracZeroOfPos

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR
open scoped TensorProduct

namespace GlobalTheory.W1

variable {K L : Type} [Field K] [Algebra ℂ K] [Field L] [Algebra ℂ L]

structure IsProdField (i1 i2 : K →ₐ[ℂ] L) : Prop where
  inj : Function.Injective (Algebra.TensorProduct.productMap i1 i2)
  gen : IntermediateField.adjoin ℂ (Set.range i1 ∪ Set.range i2) = ⊤

def prDR (i : K →ₐ[ℂ] L) : DR ℂ K →+* DR ℂ L :=
  letI : Algebra K L := i.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (i.commutes c).symm
  (mapDR ℂ K L).toRingHom

theorem prDR_ι_D (i : K →ₐ[ℂ] L) (x : K) :
    prDR i (ExteriorAlgebra.ι K (D ℂ K x)) = ExteriorAlgebra.ι L (D ℂ L (i x)) := by
  letI : Algebra K L := i.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (i.commutes c).symm
  show (mapDR ℂ K L) (ExteriorAlgebra.ι K _) = _
  rw [mapDR, ExteriorAlgebra.lift_ι_apply]
  show ExteriorAlgebra.ι L (KaehlerDifferential.map ℂ ℂ K L (D ℂ K x)) = _
  rw [map_D]
  rfl

def prodRing (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) : Subalgebra ℂ L := Algebra.adjoin ℂ (i1 '' B ∪ i2 '' B)

theorem fst_mem_prodRing (i1 i2 : K →ₐ[ℂ] L) {B : Subalgebra ℂ K} {b : K} (hb : b ∈ B) : i1 b ∈ prodRing i1 i2 B :=
  Algebra.subset_adjoin (Or.inl ⟨b, hb, rfl⟩)

theorem snd_mem_prodRing (i1 i2 : K →ₐ[ℂ] L) {B : Subalgebra ℂ K} {b : K} (hb : b ∈ B) : i2 b ∈ prodRing i1 i2 B :=
  Algebra.subset_adjoin (Or.inr ⟨b, hb, rfl⟩)

def prodMap (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) : B ⊗[ℂ] B →ₐ[ℂ] L :=
  Algebra.TensorProduct.productMap (i1.comp B.val) (i2.comp B.val)

theorem range_prodMap (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) : (prodMap i1 i2 B).range = prodRing i1 i2 B := by
  rw [prodMap, Algebra.TensorProduct.productMap_range, prodRing, Algebra.adjoin_union, AlgHom.range_comp, AlgHom.range_comp,
    Subalgebra.range_val, ← Subalgebra.coe_map, ← Subalgebra.coe_map, Algebra.adjoin_eq, Algebra.adjoin_eq]

theorem IsProdField.prodMap_injective {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) (B : Subalgebra ℂ K) :
    Function.Injective (prodMap i1 i2 B) := by
  have e : prodMap i1 i2 B =
      (Algebra.TensorProduct.productMap i1 i2).comp (Algebra.TensorProduct.map B.val B.val) := by
    ext <;> simp [prodMap]
  rw [e, AlgHom.coe_comp]
  exact hP.inj.comp (TensorProduct.map_injective_of_flat_flat B.val.toLinearMap B.val.toLinearMap
    Subtype.val_injective Subtype.val_injective)

def IsProdField.prodEquiv {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) (B : Subalgebra ℂ K) :
    B ⊗[ℂ] B ≃ₐ[ℂ] prodRing i1 i2 B :=
  (AlgEquiv.ofInjective _ (hP.prodMap_injective B)).trans (Subalgebra.equivOfEq _ _ (range_prodMap i1 i2 B))

theorem IsProdField.coe_prodEquiv {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) (B : Subalgebra ℂ K) (z : B ⊗[ℂ] B) :
    (hP.prodEquiv B z : L) = prodMap i1 i2 B z := rfl

def IsProdField.diagMul {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) (B : Subalgebra ℂ K) : prodRing i1 i2 B →ₐ[ℂ] K :=
  (Algebra.TensorProduct.productMap B.val B.val).comp (hP.prodEquiv B).symm.toAlgHom

theorem IsProdField.diagMul_spec {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) (B : Subalgebra ℂ K) :
    ∀ b ∈ B, ∀ (h1 : i1 b ∈ prodRing i1 i2 B) (h2 : i2 b ∈ prodRing i1 i2 B),
      hP.diagMul B ⟨i1 b, h1⟩ = b ∧ hP.diagMul B ⟨i2 b, h2⟩ = b := by
  intro b hb h1 h2
  have e1 : (⟨i1 b, h1⟩ : prodRing i1 i2 B) = hP.prodEquiv B ((⟨b, hb⟩ : B) ⊗ₜ 1) :=
    Subtype.ext (by rw [hP.coe_prodEquiv]; simp [prodMap])
  have e2 : (⟨i2 b, h2⟩ : prodRing i1 i2 B) = hP.prodEquiv B (1 ⊗ₜ (⟨b, hb⟩ : B)) :=
    Subtype.ext (by rw [hP.coe_prodEquiv]; simp [prodMap])
  rw [e1, e2]
  constructor <;> simp [IsProdField.diagMul]

theorem IsProdField.eq_diagMul {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) (B : Subalgebra ℂ K)
    (μ : prodRing i1 i2 B →ₐ[ℂ] K)
    (hμ : ∀ b ∈ B, ∀ (h1 : i1 b ∈ prodRing i1 i2 B) (h2 : i2 b ∈ prodRing i1 i2 B), μ ⟨i1 b, h1⟩ = b ∧ μ ⟨i2 b, h2⟩ = b) :
    μ = hP.diagMul B := by
  refine AlgHom.ext_of_eq_adjoin (s := i1 '' B ∪ i2 '' B) rfl ?_
  rintro x (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
  · exact (hμ b hb _ (snd_mem_prodRing i1 i2 hb)).1.trans (hP.diagMul_spec B b hb _ (snd_mem_prodRing i1 i2 hb)).1.symm
  · exact (hμ b hb (fst_mem_prodRing i1 i2 hb) _).2.trans (hP.diagMul_spec B b hb (fst_mem_prodRing i1 i2 hb) _).2.symm

def diagEq (i1 i2 : K →ₐ[ℂ] L) {d : ℕ} (t : Fin d → K) : Fin d → L := fun l => i1 (t l) - i2 (t l)

theorem diagEq_mem_prodRing (i1 i2 : K →ₐ[ℂ] L) {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : ∀ l, t l ∈ B)
    (l : Fin d) : diagEq i1 i2 t l ∈ prodRing i1 i2 B :=
  sub_mem (fst_mem_prodRing i1 i2 (ht l)) (snd_mem_prodRing i1 i2 (ht l))

def diagForm (i1 i2 : K →ₐ[ℂ] L) {d : ℕ} (t : Fin d → K) (a : ℕ) : DR ℂ L :=
  ∑ S ∈ Finset.univ.powersetCard a, (List.ofFn fun l : Fin d =>
    if l ∈ S then prDR i1 (ExteriorAlgebra.ι K (D ℂ K (t l))) else -prDR i2 (ExteriorAlgebra.ι K (D ℂ K (t l)))).prod

example (i1 i2 : K →ₐ[ℂ] L) (t : Fin 1 → K) :
    diagForm i1 i2 t 1 = ExteriorAlgebra.ι L (D ℂ L (i1 (t 0))) ∧
      diagForm i1 i2 t 0 = -ExteriorAlgebra.ι L (D ℂ L (i2 (t 0))) := by
  constructor
  · have e : (Finset.univ : Finset (Fin 1)).powersetCard 1 = {Finset.univ} := by decide
    rw [diagForm, e]
    simp [prDR_ι_D]
  · simp [diagForm, prDR_ι_D]

example (i1 i2 : K →ₐ[ℂ] L) (t : Fin 2 → K) :
    diagForm i1 i2 t 1 =
      -(ExteriorAlgebra.ι L (D ℂ L (i1 (t 0))) * ExteriorAlgebra.ι L (D ℂ L (i2 (t 1)))) -
        ExteriorAlgebra.ι L (D ℂ L (i2 (t 0))) * ExteriorAlgebra.ι L (D ℂ L (i1 (t 1))) := by
  have e : (Finset.univ : Finset (Fin 2)).powersetCard 1 = {{0}, {1}} := by decide
  rw [diagForm, e, Finset.sum_pair (by decide)]
  simp [prDR_ι_D, sub_eq_add_neg]

structure IsEtFrame (B : Subalgebra ℂ K) {d : ℕ} (t : Fin d → K) : Prop where
  indep : LinearIndependent K (fun l => D ℂ K (t l))
  comb : ∀ b ∈ B, ∃ c : Fin d → K, (∀ l, c l ∈ B) ∧ D ℂ K b = ∑ l, c l • D ℂ K (t l)
  frac : IsFractionRing B K

def IsEtCoord (B : Subalgebra ℂ K) {d : ℕ} (t : Fin d → K) : Prop :=
  (∀ l, t l ∈ B) ∧ IsEtFrame B t

theorem IsEtCoord.span_eq_top {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : IsEtCoord B t) :
    Submodule.span K (Set.range fun l => D ℂ K (t l)) = ⊤ := by
  haveI := ht.2.frac
  have hB : ∀ b : B, D ℂ K (algebraMap B K b) ∈ Submodule.span K (Set.range fun l => D ℂ K (t l)) := by
    intro b
    obtain ⟨c, -, hc⟩ := ht.2.2 b b.2
    rw [show algebraMap B K b = (b : K) from rfl, hc]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [SetLike.mem_coe, Derivation.leibniz_div]
  exact Submodule.smul_mem _ _ (sub_mem (Submodule.smul_mem _ _ (hB a)) (Submodule.smul_mem _ _ (hB b)))

def IsEtCoord.basis {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : IsEtCoord B t) :
    Module.Basis (Fin d) K Ω[K⁄ℂ] := Module.Basis.mk ht.2.1 ht.span_eq_top.ge

theorem IsEtCoord.finrank_eq {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : IsEtCoord B t) :
    Module.finrank K Ω[K⁄ℂ] = d := by
  rw [Module.finrank_eq_card_basis ht.basis, Fintype.card_fin]

structure IsDiagChart (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) {d : ℕ} (t : Fin d → K) (h : L) : Prop where
  mem : h ∈ prodRing i1 i2 B
  cut : ∀ μ : prodRing i1 i2 B →ₐ[ℂ] K,
    (∀ b ∈ B, ∀ (h1 : i1 b ∈ prodRing i1 i2 B) (h2 : i2 b ∈ prodRing i1 i2 B), μ ⟨i1 b, h1⟩ = b ∧ μ ⟨i2 b, h2⟩ = b) →
    μ ⟨h, mem⟩ = 1 ∧ ∀ (z : L) (hz : z ∈ prodRing i1 i2 B), μ ⟨z, hz⟩ = 0 →
      ∃ (N : ℕ) (c : Fin d → L), (∀ l, c l ∈ prodRing i1 i2 B) ∧ h ^ N * z = ∑ l, c l * diagEq i1 i2 t l
  prod : IsProdField i1 i2
  coord : ∀ l, t l ∈ B

theorem isDiagChart_iff {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K}
    (ht : ∀ l, t l ∈ B) (h : L) :
    IsDiagChart i1 i2 B t h ↔ ∃ hh : h ∈ prodRing i1 i2 B, hP.diagMul B ⟨h, hh⟩ = 1 ∧
      ∀ (z : L) (hz : z ∈ prodRing i1 i2 B), hP.diagMul B ⟨z, hz⟩ = 0 →
        ∃ (N : ℕ) (c : Fin d → L), (∀ l, c l ∈ prodRing i1 i2 B) ∧ h ^ N * z = ∑ l, c l * diagEq i1 i2 t l := by
  refine ⟨fun H => ⟨H.mem, H.cut _ (hP.diagMul_spec B)⟩, fun ⟨hh, H⟩ => ⟨hh, fun μ hμ => ?_, hP, ht⟩⟩
  rw [hP.eq_diagMul B μ hμ]
  exact H

theorem IsDiagChart.ne_zero {i1 i2 : K →ₐ[ℂ] L} {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} {h : L}
    (H : IsDiagChart i1 i2 B t h) : h ≠ 0 := by
  rintro rfl
  have h1 := (H.cut _ (H.prod.diagMul_spec B)).1
  rw [show (⟨0, H.mem⟩ : prodRing i1 i2 B) = 0 from rfl, map_zero] at h1
  exact zero_ne_one h1

def chartRing (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) (h : L) : Subalgebra ℂ L := Algebra.adjoin ℂ (prodRing i1 i2 B ∪ {h⁻¹})

theorem prodRing_le_chartRing (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) (h : L) :
    prodRing i1 i2 B ≤ chartRing i1 i2 B h := fun _ hx => Algebra.subset_adjoin (Or.inl hx)

def biForms (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) (h : L) (a b : ℕ) : Submodule (chartRing i1 i2 B h) (DR ℂ L) :=
  Submodule.span _ {y | ∃ c ∈ chartRing i1 i2 B h, ∃ α ∈ GlobalTheory.PD.omB ℂ K B a, ∃ β ∈ GlobalTheory.PD.omB ℂ K B b,
    y = c • (prDR i1 α * prDR i2 β)}

theorem ι_mul_listProd {M : Type} [AddCommGroup M] [Module L M] (m : M) (ms : List M) :
    ExteriorAlgebra.ι L m * (ms.map (ExteriorAlgebra.ι L)).prod = (ms.map (ExteriorAlgebra.ι L)).prod * ExteriorAlgebra.ι L m ∨
    ExteriorAlgebra.ι L m * (ms.map (ExteriorAlgebra.ι L)).prod =
      -((ms.map (ExteriorAlgebra.ι L)).prod * ExteriorAlgebra.ι L m) := by
  induction ms with
  | nil => left; simp
  | cons n ms ih =>
    have e : ExteriorAlgebra.ι L m * ExteriorAlgebra.ι L n = -(ExteriorAlgebra.ι L n * ExteriorAlgebra.ι L m) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m n)
    rw [List.map_cons, List.prod_cons, ← mul_assoc, e, neg_mul, mul_assoc]
    rcases ih with ih | ih <;> rw [ih]
    · right; rw [mul_assoc]
    · left; rw [mul_neg, neg_neg, mul_assoc]

theorem listProd_shuffle {M : Type} [AddCommGroup M] [Module L M] {d : ℕ} (u v : Fin d → M) (S : Finset (Fin d))
    (js : List (Fin d)) :
    (js.map fun j => if j ∈ S then ExteriorAlgebra.ι L (u j) else -ExteriorAlgebra.ι L (v j)).prod =
        (((js.filter (· ∈ S)).map u).map (ExteriorAlgebra.ι L)).prod *
          (((js.filter (· ∉ S)).map v).map (ExteriorAlgebra.ι L)).prod ∨
      (js.map fun j => if j ∈ S then ExteriorAlgebra.ι L (u j) else -ExteriorAlgebra.ι L (v j)).prod =
        -((((js.filter (· ∈ S)).map u).map (ExteriorAlgebra.ι L)).prod *
          (((js.filter (· ∉ S)).map v).map (ExteriorAlgebra.ι L)).prod) := by
  induction js with
  | nil => left; simp
  | cons j js ih =>
    by_cases hj : j ∈ S
    · simp only [List.map_cons, List.prod_cons, List.filter_cons, hj, if_true, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, if_false]
      rcases ih with e | e <;> rw [e]
      · left; rw [mul_assoc]
      · right; rw [mul_neg, mul_assoc]
    · simp only [List.map_cons, List.prod_cons, List.filter_cons, hj, if_true, not_false_eq_true,
        decide_true, decide_false, Bool.false_eq_true, if_false]
      rcases ih with e | e <;> rw [e] <;>
        rcases ι_mul_listProd (L := L) (v j) ((js.filter (· ∈ S)).map u) with c | c <;>
        simp only [neg_mul, mul_neg, neg_neg, ← mul_assoc, c, true_or, or_true]

theorem listProd_mem_omB {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : ∀ l, t l ∈ B) (js : List (Fin d)) :
    (js.map fun j => ExteriorAlgebra.ι K (D ℂ K (t j))).prod ∈ GlobalTheory.PD.omB ℂ K B js.length := by
  refine Submodule.subset_span ⟨1, one_mem _, fun i => t (js.get i), fun i => ht _, ?_⟩
  rw [one_smul, ExteriorAlgebra.ιMulti_apply]
  congr 1
  conv_lhs => rw [← List.ofFn_get js, List.map_ofFn]
  rfl

theorem diagForm_mem_biForms (i1 i2 : K →ₐ[ℂ] L) {B : Subalgebra ℂ K} {d : ℕ} {t : Fin d → K} (ht : ∀ l, t l ∈ B)
    (h : L) (a : ℕ) : diagForm i1 i2 t a ∈ biForms i1 i2 B h a (d - a) := by
  refine Submodule.sum_mem _ fun S hS => ?_
  have hcard : S.card = a := (Finset.mem_powersetCard.1 hS).2
  have hl1 : ((List.finRange d).filter (· ∈ S)).length = a := by
    rw [← hcard, ← List.toFinset_card_of_nodup ((List.nodup_finRange d).filter _)]
    congr 1; ext j; simp
  have hl2 : ((List.finRange d).filter (· ∉ S)).length = d - a := by
    rw [← hcard, ← List.toFinset_card_of_nodup ((List.nodup_finRange d).filter _)]
    rw [show ((List.finRange d).filter (· ∉ S)).toFinset = Sᶜ by ext j; simp, Finset.card_compl, Fintype.card_fin]
  have h1 := listProd_mem_omB ht ((List.finRange d).filter (· ∈ S))
  have h2 := listProd_mem_omB ht ((List.finRange d).filter (· ∉ S))
  rw [hl1] at h1
  rw [hl2] at h2
  have hX := Submodule.subset_span (R := chartRing i1 i2 B h) (s := {y | ∃ c ∈ chartRing i1 i2 B h,
    ∃ α ∈ GlobalTheory.PD.omB ℂ K B a, ∃ β ∈ GlobalTheory.PD.omB ℂ K B (d - a), y = c • (prDR i1 α * prDR i2 β)})
    ⟨1, one_mem _, _, h1, _, h2, rfl⟩
  have hp : ∀ (i : K →ₐ[ℂ] L) (js : List (Fin d)), prDR i (js.map fun j => ExteriorAlgebra.ι K (D ℂ K (t j))).prod =
      ((js.map fun j => D ℂ L (i (t j))).map (ExteriorAlgebra.ι L)).prod := by
    intro i js
    rw [map_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun j _ => prDR_ι_D i (t j))
  rw [one_smul, hp, hp] at hX
  rw [List.ofFn_eq_map]
  simp only [prDR_ι_D]
  rcases listProd_shuffle (L := L) (fun j => D ℂ L (i1 (t j))) (fun j => D ℂ L (i2 (t j))) S (List.finRange d) with e | e <;>
    rw [e]
  · exact hX
  · exact Submodule.neg_mem _ hX

def diagSeq (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) {d : ℕ} (t : Fin d → K) (ht : ∀ l, t l ∈ B) (h : L) :
    Fin d → chartRing i1 i2 B h :=
  fun l => ⟨diagEq i1 i2 t l, prodRing_le_chartRing i1 i2 B h (diagEq_mem_prodRing i1 i2 ht l)⟩

def diagClass (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) {d : ℕ} (t : Fin d → K) (ht : ∀ l, t l ∈ B) (h : L) (a : ℕ) :
    LC (diagSeq i1 i2 B t ht h) (biForms i1 i2 B h a (d - a)) :=
  frac _ (⟨diagForm i1 i2 t a, diagForm_mem_biForms i1 i2 ht h a⟩ : biForms i1 i2 B h a (d - a)) 1

open Classical in

def locDiag (i1 i2 : K →ₐ[ℂ] L) (B : Subalgebra ℂ K) {d : ℕ} (t : Fin d → K) (h : L) (a : ℕ) :
    LC (fun l => (if hl : diagEq i1 i2 t l ∈ chartRing i1 i2 B h then ⟨_, hl⟩ else 0 : chartRing i1 i2 B h))
      (biForms i1 i2 B h a (d - a)) :=
  if hw : diagForm i1 i2 t a ∈ biForms i1 i2 B h a (d - a) then frac _ (⟨_, hw⟩ : biForms i1 i2 B h a (d - a)) 1 else 0

theorem isProdField_fractionRing (K : Type) [Field K] [Algebra ℂ K] [IsDomain (K ⊗[ℂ] K)] :
    IsProdField
      ((IsScalarTower.toAlgHom ℂ (K ⊗[ℂ] K) (FractionRing (K ⊗[ℂ] K))).comp Algebra.TensorProduct.includeLeft)
      ((IsScalarTower.toAlgHom ℂ (K ⊗[ℂ] K) (FractionRing (K ⊗[ℂ] K))).comp Algebra.TensorProduct.includeRight) := by
  set j := IsScalarTower.toAlgHom ℂ (K ⊗[ℂ] K) (FractionRing (K ⊗[ℂ] K)) with hj
  have e : Algebra.TensorProduct.productMap (j.comp Algebra.TensorProduct.includeLeft)
      (j.comp Algebra.TensorProduct.includeRight) = j := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    simp [← map_mul]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact IsFractionRing.injective (K ⊗[ℂ] K) (FractionRing (K ⊗[ℂ] K))
  · have hm : ∀ z : K ⊗[ℂ] K, j z ∈ IntermediateField.adjoin ℂ
        (Set.range (j.comp Algebra.TensorProduct.includeLeft) ∪ Set.range (j.comp Algebra.TensorProduct.includeRight)) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
      | tmul x y =>
        rw [show x ⊗ₜ[ℂ] y = (x ⊗ₜ[ℂ] (1 : K)) * ((1 : K) ⊗ₜ[ℂ] y) by simp, map_mul]
        exact mul_mem (IntermediateField.subset_adjoin _ _ (Or.inl ⟨x, rfl⟩))
          (IntermediateField.subset_adjoin _ _ (Or.inr ⟨y, rfl⟩))
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] K) x
    exact div_mem (hm a) (hm b)

theorem IsProdField.isDiagChart_adjoin {i1 i2 : K →ₐ[ℂ] L} (hP : IsProdField i1 i2) {d : ℕ} (t : Fin d → K) :
    IsDiagChart i1 i2 (Algebra.adjoin ℂ (Set.range t)) t 1 := by
  set B := Algebra.adjoin ℂ (Set.range t) with hB
  have ht : ∀ l, t l ∈ B := fun l => Algebra.subset_adjoin ⟨l, rfl⟩
  let f : Fin d → prodRing i1 i2 B := fun l => ⟨_, diagEq_mem_prodRing i1 i2 ht l⟩
  let I : Ideal (prodRing i1 i2 B) := Ideal.span (Set.range f)
  let p1 : B →ₐ[ℂ] prodRing i1 i2 B := (i1.comp B.val).codRestrict _ fun b => fst_mem_prodRing i1 i2 b.2
  let p2 : B →ₐ[ℂ] prodRing i1 i2 B := (i2.comp B.val).codRestrict _ fun b => snd_mem_prodRing i1 i2 b.2
  have h12 : (Ideal.Quotient.mkₐ ℂ I).comp p1 = (Ideal.Quotient.mkₐ ℂ I).comp p2 := by
    refine AlgHom.ext_of_eq_adjoin (s := Set.range t) rfl ?_
    rintro x ⟨l, rfl⟩
    exact Ideal.Quotient.eq.2 (Ideal.subset_span ⟨l, rfl⟩)
  have key : ((Ideal.Quotient.mkₐ ℂ I).comp p1).comp (Algebra.TensorProduct.productMap (AlgHom.id ℂ B) (AlgHom.id ℂ B)) =
      (Ideal.Quotient.mkₐ ℂ I).comp (hP.prodEquiv B).toAlgHom := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    have e : hP.prodEquiv B (x ⊗ₜ y) = p1 x * p2 y := Subtype.ext (by rw [hP.coe_prodEquiv, prodMap, Algebra.TensorProduct.productMap_apply_tmul]; rfl)
    have e2 := DFunLike.congr_fun h12 y
    simp only [AlgHom.comp_apply] at e2
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, map_mul, e2]
    rw [← map_mul, ← e]
    rfl
  refine (isDiagChart_iff hP ht 1).2 ⟨one_mem _, map_one _, fun z hz h0 => ?_⟩
  obtain ⟨w, hw⟩ := (hP.prodEquiv B).surjective ⟨z, hz⟩
  have hw0 : Algebra.TensorProduct.productMap (AlgHom.id ℂ B) (AlgHom.id ℂ B) w = 0 := by
    have e : B.val.comp (Algebra.TensorProduct.productMap (AlgHom.id ℂ B) (AlgHom.id ℂ B)) =
        Algebra.TensorProduct.productMap B.val B.val := by
      ext <;> simp
    apply Subtype.val_injective
    have e2 := DFunLike.congr_fun e w
    rw [← hw] at h0
    simp only [IsProdField.diagMul, AlgHom.comp_apply] at h0 e2
    exact e2.trans (by simpa using h0)
  have hI : (⟨z, hz⟩ : prodRing i1 i2 B) ∈ I := by
    have e := DFunLike.congr_fun key w
    simp only [AlgHom.comp_apply, hw0, map_zero] at e
    rw [← hw]
    exact Ideal.Quotient.eq_zero_iff_mem.1 e.symm
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hI
  refine ⟨0, fun l => c l, fun l => (c l).2, ?_⟩
  have e := congrArg Subtype.val hc
  simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] at e
  rw [pow_zero, one_mul]
  exact e.symm

theorem isEtCoord_adjoin {d : ℕ} (t : Fin d → K) [IsFractionRing (Algebra.adjoin ℂ (Set.range t)) K]
    (hli : LinearIndependent K fun l => D ℂ K (t l)) : IsEtCoord (Algebra.adjoin ℂ (Set.range t)) t := by
  classical
  refine ⟨fun l => Algebra.subset_adjoin ⟨l, rfl⟩, hli, fun b hb => ?_, inferInstance⟩
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    refine ⟨Pi.single l 1, fun m => ?_, by simp [Pi.single_apply]⟩
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  | algebraMap r => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, e⟩ := hx
    obtain ⟨c', hc', e'⟩ := hy
    exact ⟨c + c', fun l => add_mem (hc l) (hc' l), by simp [e, e', add_smul, Finset.sum_add_distrib]⟩
  | mul x y hx' hy' hx hy =>
    obtain ⟨c, hc, e⟩ := hx
    obtain ⟨c', hc', e'⟩ := hy
    exact ⟨fun l => x * c' l + y * c l, fun l => add_mem (mul_mem hx' (hc' l)) (mul_mem hy' (hc l)), by
      simp [e, e', add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]⟩

namespace Aff

abbrev Fn (d : ℕ) : Type := FractionRing (MvPolynomial (Fin d) ℂ)

def coord (d : ℕ) : Fin d → Fn d := fun l => algebraMap (MvPolynomial (Fin d) ℂ) (Fn d) (MvPolynomial.X l)

abbrev polyRing (d : ℕ) : Subalgebra ℂ (Fn d) := Algebra.adjoin ℂ (Set.range (coord d))

theorem algebraMap_mem (d : ℕ) (p : MvPolynomial (Fin d) ℂ) : algebraMap _ (Fn d) p ∈ polyRing d := by
  induction p using MvPolynomial.induction_on with
  | C c => exact (polyRing d).algebraMap_mem c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p l hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨l, rfl⟩)

instance isFractionRing (d : ℕ) : IsFractionRing (polyRing d) (Fn d) :=
  IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin d) ℂ) z
    exact ⟨⟨_, algebraMap_mem d a⟩, ⟨_, algebraMap_mem d b⟩, rfl⟩

theorem isEtCoord (d : ℕ) : IsEtCoord (polyRing d) (coord d) := by
  refine isEtCoord_adjoin _ ?_
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin d) ℂ) (Fn d) := .of_isLocalization (nonZeroDivisors _)
  let b : Module.Basis (Fin d) (Fn d) Ω[Fn d⁄ℂ] := ((mvPolynomialBasis ℂ (Fin d)).baseChange (Fn d)).map
    (tensorKaehlerEquivOfFormallyEtale ℂ (MvPolynomial (Fin d) ℂ) (Fn d))
  have hb : (fun l => D ℂ (Fn d) (coord d l)) = b := by
    funext l
    simp only [b, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D, coord]
  rw [hb]
  exact b.linearIndependent

theorem isDomain_tensor (k : Type) [Field k] (σ : Type) (A : Type) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] A) := by
  let P := MvPolynomial σ k
  let F := FractionRing P
  letI : Algebra (P ⊗[k] A) (F ⊗[k] A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P F) (AlgHom.id k A)).toAlgebra
  haveI : IsScalarTower P (P ⊗[k] A) (F ⊗[k] A) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) F
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  let e : P ⊗[k] A ≃+* MvPolynomial σ A :=
    ((Algebra.TensorProduct.comm k P A).toRingEquiv.trans (MvPolynomial.scalarRTensorAlgEquiv).toRingEquiv)
  haveI : IsDomain (P ⊗[k] A) := e.toMulEquiv.isDomain
  have hinj : Function.Injective (algebraMap P (P ⊗[k] A)) :=
    Algebra.TensorProduct.includeLeft_injective (S := P) (algebraMap k A).injective
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (F ⊗[k] A)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] A) (nonZeroDivisors P)) ?_
  rintro _ ⟨p, hp, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp (hinj (h.trans (map_zero _).symm))

instance isDomain_tensor_self (d : ℕ) : IsDomain (Fn d ⊗[ℂ] Fn d) := isDomain_tensor ℂ (Fin d) (Fn d)

abbrev Fn2 (d : ℕ) : Type := FractionRing (Fn d ⊗[ℂ] Fn d)

def pr1 (d : ℕ) : Fn d →ₐ[ℂ] Fn2 d :=
  (IsScalarTower.toAlgHom ℂ (Fn d ⊗[ℂ] Fn d) (Fn2 d)).comp Algebra.TensorProduct.includeLeft

def pr2 (d : ℕ) : Fn d →ₐ[ℂ] Fn2 d :=
  (IsScalarTower.toAlgHom ℂ (Fn d ⊗[ℂ] Fn d) (Fn2 d)).comp Algebra.TensorProduct.includeRight

theorem isProdField (d : ℕ) : IsProdField (pr1 d) (pr2 d) := isProdField_fractionRing (Fn d)

theorem isDiagChart (d : ℕ) : IsDiagChart (pr1 d) (pr2 d) (polyRing d) (coord d) 1 := (isProdField d).isDiagChart_adjoin _

example (d : ℕ) : Module.finrank (Fn d) Ω[Fn d⁄ℂ] = d ∧ IsProdField (pr1 d) (pr2 d) ∧ IsEtCoord (polyRing d) (coord d) ∧
    IsDiagChart (pr1 d) (pr2 d) (polyRing d) (coord d) 1 :=
  ⟨(isEtCoord d).finrank_eq, isProdField d, isEtCoord d, isDiagChart d⟩

end Aff

end GlobalTheory.W1
