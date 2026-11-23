import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt.DualHT

section

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

def omLin {n : ℕ} (e : (Fin n → O) ≃ LieG P.Gt) (he1 : ∀ x y, e (x + y) = lieAdd (e x) (e y))
    (he2 : ∀ (a : O) x, e (a • x) = AvDefs.lieScale P.Gt a (e x)) (F : omega P.Gt) :
    (Fin n → O) →ₗ[O] O where
  toFun x := F.1 (e x)
  map_add' x y := by rw [he1]; exact omega_lieAdd F _ _
  map_smul' a x := by rw [he2]; exact omega_lieScale F a _

theorem coord_mem_omega {n : ℕ} (e : (Fin n → O) ≃ LieG P.Gt) (he1 : ∀ x y, e (x + y) = lieAdd (e x) (e y))
    (he2 : ∀ (a : O) x, e (a • x) = AvDefs.lieScale P.Gt a (e x)) (i : Fin n) :
    (fun y => (e.symm y) i) ∈ omega P.Gt :=
  ⟨fun x y h => by
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    rw [show (⟨_, h⟩ : LieG P.Gt) = e (a + b) from Subtype.ext (congrArg Subtype.val (he1 a b)).symm]
    simp,
   fun r x h => by
    obtain ⟨a, rfl⟩ := e.surjective x
    rw [show (⟨_, h⟩ : LieG P.Gt) = e (r • a) from Subtype.ext (congrArg Subtype.val (he2 r a)).symm]
    simp⟩

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem exists_coords : ∃ (n : ℕ) (e : (Fin n → O) ≃ LieG P.Gt),
    (∀ x y, e (x + y) = lieAdd (e x) (e y)) ∧ ∀ (a : O) x, e (a • x) = AvDefs.lieScale P.Gt a (e x) := by
  haveI := P.isLocalRing
  obtain ⟨e, h₁, h₂⟩ := OmegaRank.exists_param P.G (OmegaRank.smoothDim_model P)
  obtain ⟨e', h₃, h₄⟩ := OmegaRank.exists_lieEquiv P
  exact ⟨_, e.trans e', fun x y => Subtype.ext (h₃ _ _ _ (h₁ x y)),
    fun a x => Subtype.ext (h₄ a _ _ (h₂ a x))⟩

variable [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem pairV_bLie_inclT (y : LieG P.Gt) (x : O ⊗[ℤ_[p]] P.T) :
    P.pairV (P.bLie y) (P.inclT x) = algebraMap O C ((P.al x).1 y) := by
  rw [pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, evLie, TensorProduct.mk_apply,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem exists_pairV_inclT {w : P.V} (hw : w ∈ P.latT) (x : O ⊗[ℤ_[p]] P.T) :
    ∃ κ : O, algebraMap O C κ = P.pairV w (P.inclT x) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]⟩
  | tmul a t =>
    obtain ⟨d, hd⟩ := (P.mem_latT_iff w).1 hw t
    refine ⟨a * d, ?_⟩
    have h : P.inclT (a ⊗ₜ t) = algebraMap O C a • ((1 : C) ⊗ₜ t) := by
      rw [P.inclT_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h, map_smul, smul_eq_mul, ← hd, map_mul]

end

theorem smul_mem_wRec_of_mem_span : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HTChar p v P.Gt → ∀ (τ : Λ →+* O) {w : P.V}, w ∈ P.latT → w ∈ Submodule.span C (P.wRec τ : Set P.V) → ∀ {c : O}, v (algebraMap O C c) ^ (p - 1) ≤ v (p : C) → algebraMap O C c • w ∈ P.wRec τ := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hHT τ w hwT hwS c hc
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  by_cases hc0 : c = 0
  · rw [hc0, map_zero, zero_smul]; exact Submodule.zero_mem _
  obtain ⟨n, e, he1, he2⟩ := exists_coords P
  have ht : ∀ i : Fin n, ∃ t : O ⊗[ℤ_[p]] P.T, (P.al t).1 = c • (fun y => (e.symm y) i) := by
    intro i
    have h2 := hHT c hc _ (coord_mem_omega P e he1 he2 i)
    rw [← (weilChar_surjective_and_map_range_al p C v O Λ P).2] at h2
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := h2
    exact ⟨t, ht⟩
  choose t ht using ht
  have hpair : ∀ y i, P.pairV (P.bLie y) (P.inclT (t i)) = algebraMap O C (c * (e.symm y) i) := by
    intro y i
    rw [pairV_bLie_inclT, ht i]
    rfl
  have hinj : ∀ y y', P.bLie y = P.bLie y' → y = y' := by
    intro y y' h
    apply e.symm.injective
    funext i
    have h1 := hpair y i
    rw [h, hpair y' i] at h1
    exact (mul_left_cancel₀ hc0 (P.integers.hom_inj h1)).symm
  set u : Fin n → LieG P.Gt := fun i => e (fun j => if i = j then (1 : O) else 0) with hu
  have hexp : ∀ x, P.bLie (e x) = ∑ i, algebraMap O C (x i) • P.bLie (u i) := by
    intro x
    refine P.eq_of_pairV fun s => ?_
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Point.pairV_bLie, smul_eq_mul]
    simp only [← map_mul, ← map_sum]
    congr 1
    exact (omLin P e he1 he2 (P.al₀ s)).pi_apply_eq_sum_univ x
  have hspan : w ∈ Submodule.span C (Set.range fun i => P.bLie (u i)) := by
    refine Submodule.span_le.2 ?_ hwS
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, ← e.apply_symm_apply y.1, hexp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hspan
  have hb : ∀ i, ∃ κ : O, algebraMap O C κ = algebraMap O C c * β i := by
    intro i
    obtain ⟨κ, hκ⟩ := exists_pairV_inclT P hwT (t i)
    refine ⟨κ, hκ.trans ?_⟩
    rw [← hβ, map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
    · rw [map_smul, LinearMap.smul_apply, hpair, smul_eq_mul, hu, e.symm_apply_apply, if_pos rfl,
        _root_.mul_one, mul_comm]
    · intro j _ hj
      rw [map_smul, LinearMap.smul_apply, hpair, hu, e.symm_apply_apply, if_neg hj, mul_zero, map_zero,
        smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  choose κ hκ using hb
  have hcw : algebraMap O C c • w = P.bLie (e κ) := by
    rw [hexp, ← hβ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hκ]
  have hwE : w ∈ P.eigV τ := (Submodule.span_le (p := P.eigV τ)).2 (fun x hx => (P.wRec_le τ hx).2) hwS
  have hE : AvDefs.IsEig P.Gt P.oGt τ (e κ) := by
    intro a
    apply hinj
    have hz := mem_eigenSub.1 ((P.eigV τ).smul_mem (algebraMap O C c) hwE) a
    rw [P.bLie_act, P.bLie_scale, ← hcw, hz, RingHom.comp_apply, algebraMap_smul]
  rw [hcw]
  exact ⟨⟨e κ, hE⟩, rfl⟩

end GlobalTheory.CompHt.DualHT
