import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint

noncomputable section

namespace GlobalTheory.FunObj.HatFrame

section General

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.L2.DIV GlobalTheory.NormSum.AdLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => Formalism.L2.Herm.intAf F E
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable (F) in

def genGrp (M : Submodule (𝓞 E) (Matrix (Fin m) (Fin n) E)) :
    AddSubgroup (Matrix (Fin m) (Fin n) 𝒜) :=
  AddSubgroup.closure {w | ∃ α ∈ intAd F, ∃ x ∈ M, w = Matrix.of fun i j => x i j ⊗ₜ[F] α}

theorem smul_mem_genGrp (M : Submodule (𝓞 E) (Matrix (Fin m) (Fin n) E)) (s : 𝒜) (hs : s ∈ 𝒮) :
    ∀ w ∈ genGrp F M, s • w ∈ genGrp F M := by
  have key : ∀ s : 𝒜, (∀ α ∈ intAd F, ∀ x ∈ M,
      s • (Matrix.of fun i j => x i j ⊗ₜ[F] α : Matrix (Fin m) (Fin n) 𝒜) ∈ genGrp F M) →
      ∀ w ∈ genGrp F M, s • w ∈ genGrp F M := by
    intro s h w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw => obtain ⟨α, hα, x, hx, rfl⟩ := hw; exact h α hα x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | neg a _ ha => rw [smul_neg]; exact neg_mem ha
  induction hs using Subring.closure_induction with
  | mem s hs =>
    rcases hs with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨y, rfl⟩
    · refine key _ fun α hα x hx => AddSubgroup.subset_closure ⟨α, hα, b • x, M.smul_mem b hx, ?_⟩
      ext i j
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    · refine key _ fun α hα x hx => AddSubgroup.subset_closure ⟨y * α, mul_mem y.2 hα, x, hx, ?_⟩
      ext i j
      simp [Algebra.TensorProduct.tmul_mul_tmul]
  | zero => intro w _; rw [zero_smul]; exact zero_mem _
  | one => intro w hw; rwa [one_smul]
  | add a b _ _ ha hb => intro w hw; rw [add_smul]; exact add_mem (ha w hw) (hb w hw)
  | neg a _ ha => intro w hw; rw [neg_smul]; exact neg_mem (ha w hw)
  | mul a b _ _ ha hb => intro w hw; rw [mul_smul]; exact ha _ (hb w hw)

theorem map_mulVec_hat {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {x : Matrix (Fin m) (Fin n) E} (hx : ∀ y ∈ Λ, x *ᵥ y ∈ Λ') {u : Fin n → 𝒜}
    (hu : u ∈ Formalism.L2.Herm.hatL (F := F) Λ) : (x.map ι) *ᵥ u ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    refine Submodule.subset_span ⟨x *ᵥ y, hx y hy, ?_⟩
    funext i
    exact RingHom.map_mulVec _ _ _ _
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ c ha

theorem col_mem_hat {Λ : Submodule (𝓞 E) (Fin n → E)} {β : GL (Fin n) 𝒜} (hβ : IsFrame β Λ) (j : Fin n) :
    (β : Matrix (Fin n) (Fin n) 𝒜) *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine (hβ _).2 fun k => ?_
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem frame_int {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} {β' : GL (Fin m) 𝒜} (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ')
    {x : Matrix (Fin m) (Fin n) E} (hx : ∀ y ∈ Λ, x *ᵥ y ∈ Λ') (i : Fin m) (j : Fin n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val (x.map ι)) β.val i j ∈ 𝒮 := by
  have h := (hβ' _).1 (map_mulVec_hat hx (col_mem_hat hβ j)) i
  rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at h

def frGrp (β : GL (Fin n) 𝒜) (β' : GL (Fin m) 𝒜) (I : Ideal 𝒮) : AddSubgroup (Matrix (Fin m) (Fin n) 𝒜) where
  carrier := {w | ∀ i j, ∃ s ∈ I, (s : 𝒜) = HMul.hMul (HMul.hMul (β'⁻¹).val w) β.val i j}
  zero_mem' := fun i j => ⟨0, zero_mem _, by simp⟩
  add_mem' := fun {a b} ha hb i j => by
    obtain ⟨s, hs, e⟩ := ha i j
    obtain ⟨t, ht, e'⟩ := hb i j
    refine ⟨s + t, add_mem hs ht, ?_⟩
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, ← e, ← e']; rfl
  neg_mem' := fun {a} ha i j => by
    obtain ⟨s, hs, e⟩ := ha i j
    refine ⟨-s, neg_mem hs, ?_⟩
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, ← e]; rfl

theorem smul_mem_frGrp (β : GL (Fin n) 𝒜) (β' : GL (Fin m) 𝒜) {I : Ideal 𝒮} {s : 𝒮} (hs : s ∈ I)
    {w : Matrix (Fin m) (Fin n) 𝒜} (hw : ∀ i j, HMul.hMul (HMul.hMul (β'⁻¹).val w) β.val i j ∈ 𝒮) :
    (s : 𝒜) • w ∈ frGrp β β' I := by
  intro i j
  refine ⟨s * ⟨_, hw i j⟩, Ideal.mul_mem_right _ _ hs, ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Subring.coe_mul]

theorem gen_smul (a : 𝓞 E) (α : FiniteAdeleRing (𝓞 F) F) (x : Matrix (Fin m) (Fin n) E) :
    (Matrix.of fun i j => (a • x) i j ⊗ₜ[F] α : Matrix (Fin m) (Fin n) 𝒜) =
      (((oToS F E a : 𝒮) : 𝒜) * ((1 : E) ⊗ₜ[F] α)) • x.map ι := by
  ext i j
  show _ = ((algebraMap (𝓞 E) E a ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] α)) *
    (x i j ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul,
    ← Algebra.smul_def]
  rfl

theorem gen_add (α : FiniteAdeleRing (𝓞 F) F) (x y : Matrix (Fin m) (Fin n) E) :
    (Matrix.of fun i j => (x + y) i j ⊗ₜ[F] α : Matrix (Fin m) (Fin n) 𝒜) =
      (Matrix.of fun i j => x i j ⊗ₜ[F] α) + (Matrix.of fun i j => y i j ⊗ₜ[F] α) := by
  ext i j
  exact TensorProduct.add_tmul _ _ _

theorem gen_mem_frGrp {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} {β' : GL (Fin m) 𝒜} (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ') {𝔪 : Ideal (𝓞 E)}
    {α : FiniteAdeleRing (𝓞 F) F} (hα : α ∈ intAd F) {a : 𝓞 E} (ha : a ∈ 𝔪) {x : Matrix (Fin m) (Fin n) E}
    (hx : ∀ y ∈ Λ, x *ᵥ y ∈ Λ') :
    (Matrix.of fun i j => (a • x) i j ⊗ₜ[F] α : Matrix (Fin m) (Fin n) 𝒜) ∈ frGrp β β' (idS F 𝔪) := by
  have hα' : (1 : E) ⊗ₜ[F] α ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
  have h1 : oToS F E a ∈ idS F 𝔪 := Ideal.mem_map_of_mem _ ha
  have h3 : oToS F E a * (⟨_, hα'⟩ : 𝒮) ∈ idS F 𝔪 := Ideal.mul_mem_right _ _ h1
  have h2 := smul_mem_frGrp β β' h3 (w := x.map ι) (fun i j => frame_int hβ hβ' hx i j)
  rw [Subring.coe_mul] at h2
  rw [gen_smul]
  exact h2

theorem genGrp_le_frGrp {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} {β' : GL (Fin m) 𝒜} (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ')
    {H : Submodule (𝓞 E) (Matrix (Fin m) (Fin n) E)} (hH : ∀ x ∈ H, ∀ y ∈ Λ, x *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    genGrp F (𝔪 • H) ≤ frGrp β β' (idS F 𝔪) := by
  have key : ∀ α ∈ intAd F, ∀ x ∈ 𝔪 • H, (Matrix.of fun i j => x i j ⊗ₜ[F] α : Matrix (Fin m) (Fin n) 𝒜) ∈
      frGrp β β' (idS F 𝔪) := by
    intro α hα x hx
    induction hx using Submodule.smul_induction_on' with
    | smul a ha x hx => exact gen_mem_frGrp hβ hβ' hα ha (hH x hx)
    | add x _ y _ hx hy => rw [gen_add]; exact AddSubgroup.add_mem _ hx hy
  unfold genGrp
  rw [AddSubgroup.closure_le]
  intro w hw
  obtain ⟨α, hα, x, hx, e⟩ := hw
  rw [e]
  exact key α hα x hx

theorem vecMulVec_mem_hom {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} (hβ : IsFrame β Λ) {l' : Fin m → E} (hl' : l' ∈ Λ') {l : Fin n → E}
    (hl : ∀ k, ((β : Matrix (Fin n) (Fin n) 𝒜)ᵀ *ᵥ fun j => ι (l j)) k ∈ 𝒮) :
    ∀ y ∈ Λ, vecMulVec l' l *ᵥ y ∈ Λ' := by
  intro y hy
  have h1 := (hβ (fun j => ι (y j))).1 (Submodule.subset_span ⟨y, hy, rfl⟩)
  have h2 : ι (l ⬝ᵥ y) ∈ 𝒮 := by
    have e : ι (l ⬝ᵥ y) = ((β : Matrix (Fin n) (Fin n) 𝒜)ᵀ *ᵥ fun j => ι (l j)) ⬝ᵥ
        (((β⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ fun j => ι (y j)) := by
      rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec]
      simp [dotProduct]
    rw [e]
    exact sum_mem fun k _ => mul_mem (hl k) (h1 k)
  obtain ⟨b, hb⟩ := (incl_mem_iff _).1 h2
  have e : vecMulVec l' l *ᵥ y = b • l' := by
    funext i
    rw [Pi.smul_apply, Algebra.smul_def, hb]
    simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [e]
  exact Λ'.smul_mem b hl'

theorem frGrp_le_genGrp {Λ : Submodule (𝓞 E) (Fin n → E)} {Λ' : Submodule (𝓞 E) (Fin m → E)}
    {β : GL (Fin n) 𝒜} {β' : GL (Fin m) 𝒜} (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ')
    {H : Submodule (𝓞 E) (Matrix (Fin m) (Fin n) E)} (hH : ∀ x, (∀ y ∈ Λ, x *ᵥ y ∈ Λ') → x ∈ H) (𝔪 : Ideal (𝓞 E)) :
    frGrp β β' (idS F 𝔪) ≤ genGrp F (𝔪 • H) := by
  let γ : GL (Fin n) 𝒜 := ⟨((β⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜)ᵀ, (β : Matrix (Fin n) (Fin n) 𝒜)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one], by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  have hγ : ((γ⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) = (β : Matrix (Fin n) (Fin n) 𝒜)ᵀ := rfl
  have st : ∀ (c : 𝒮) {w}, w ∈ genGrp F (𝔪 • H) → c • w ∈ genGrp F (𝔪 • H) :=
    fun c w hw => smul_mem_genGrp _ c.1 c.2 w hw
  have k1 : ∀ a ∈ 𝔪, ∀ l' ∈ Λ', ∀ l ∈ lat γ,
      oToS F E a • vecMulVec (fun i => ι (l' i)) (fun j => ι (l j)) ∈ genGrp F (𝔪 • H) := by
    intro a ha l' hl' l hl
    refine AddSubgroup.subset_closure ⟨1, one_mem _, a • vecMulVec l' l,
      Submodule.smul_mem_smul ha (hH _ (vecMulVec_mem_hom hβ hl' ((mem_lat γ l).1 hl))), ?_⟩
    ext i j
    show ((oToS F E a : 𝒮) : 𝒜) * (ι (l' i) * ι (l j)) = _
    simp [oToS_coe, inclE, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def, vecMulVec]
  have k2 : ∀ a ∈ 𝔪, ∀ l' ∈ Λ', ∀ v ∈ Submodule.span 𝒮 ((fun x : Fin n → E => fun i => ι (x i)) '' (lat γ : Set (Fin n → E))),
      oToS F E a • vecMulVec (fun i => ι (l' i)) v ∈ genGrp F (𝔪 • H) := by
    intro a ha l' hl' v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨l, hl, rfl⟩ := hv; exact k1 a ha l' hl' l hl
    | zero =>
      have e : vecMulVec (fun i => ι (l' i)) (0 : Fin n → 𝒜) = 0 := by ext i j; exact mul_zero _
      rw [e, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [vecMulVec_add, smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [vecMulVec_smul, smul_comm]; exact st c hx
  have k3 : ∀ a ∈ 𝔪, ∀ u ∈ Formalism.L2.Herm.hatL (F := F) Λ',
      ∀ v ∈ Submodule.span 𝒮 ((fun x : Fin n → E => fun i => ι (x i)) '' (lat γ : Set (Fin n → E))),
      oToS F E a • vecMulVec u v ∈ genGrp F (𝔪 • H) := by
    intro a ha u hu v hv
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨l, hl, rfl⟩ := hu; exact k2 a ha l hl v hv
    | zero =>
      have e : vecMulVec (0 : Fin m → 𝒜) v = 0 := by ext i j; exact zero_mul _
      rw [e, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_vecMulVec, smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_vecMulVec, smul_comm]; exact st c hx
  have k4 : ∀ s ∈ idS F 𝔪, ∀ u ∈ Formalism.L2.Herm.hatL (F := F) Λ',
      ∀ v ∈ Submodule.span 𝒮 ((fun x : Fin n → E => fun i => ι (x i)) '' (lat γ : Set (Fin n → E))),
      s • vecMulVec u v ∈ genGrp F (𝔪 • H) := by
    intro s hs u hu v hv
    induction hs using Submodule.span_induction with
    | mem s hs => obtain ⟨a, ha, rfl⟩ := hs; exact k3 a ha u hu v hv
    | zero => rw [zero_smul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_smul]; exact st c hx
  intro w hw
  choose s hs he using hw
  have e0 : w = HMul.hMul (HMul.hMul β'.val (Matrix.of fun i j => (s i j : 𝒜))) (β⁻¹).val := by
    have : (Matrix.of fun i j => (s i j : 𝒜)) = HMul.hMul (HMul.hMul (β'⁻¹).val w) β.val := by
      ext i j; exact he i j
    rw [this, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul]
  have e : w = ∑ i, ∑ j, s i j • vecMulVec ((β' : Matrix (Fin m) (Fin m) 𝒜) *ᵥ Pi.single i 1)
      ((γ : Matrix (Fin n) (Fin n) 𝒜) *ᵥ Pi.single j 1) := by
    rw [e0]
    ext a b
    simp only [mulVec_single_one, Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show _ = (s i j : 𝒜) * (β'.val a i * (β⁻¹).val j b)
    ring
  rw [e]
  refine sum_mem fun i _ => sum_mem fun j _ => k4 _ (hs i j) _ (col_mem_hat hβ' i) _ ((lat_span γ _).2 fun k => ?_)
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_hatMx_iff (D : D7) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (z : Mx D m n) :
    z ∈ GlobalTheory.ChiGrid.hatMx M ↔ (∀ i j, infPart D (z i j) = 0) ∧ z.map (toEAf D) ∈ genGrp D.host.F M := by
  have h1 : ∀ z ∈ GlobalTheory.ChiGrid.hatMx M, (∀ i j, infPart D (z i j) = 0) ∧ z.map (toEAf D) ∈ genGrp D.host.F M := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hw
      refine ⟨fun i j => ?_, AddSubgroup.subset_closure ⟨α, hα, x, hx, rfl⟩⟩
      show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x i j = 0
      exact TensorProduct.zero_tmul _ _
    | zero =>
      refine ⟨fun i j => RingHom.map_zero _, ?_⟩
      rw [Matrix.map_zero _ (RingHom.map_zero _)]; exact zero_mem _
    | add a b _ _ ha hb =>
      refine ⟨fun i j => ?_, ?_⟩
      · rw [Matrix.add_apply, RingHom.map_add, ha.1, hb.1, add_zero]
      · rw [Matrix.map_add _ (RingHom.map_add _)]; exact add_mem ha.2 hb.2
    | neg a _ ha =>
      refine ⟨fun i j => ?_, ?_⟩
      · rw [Matrix.neg_apply, RingHom.map_neg, ha.1, neg_zero]
      · rw [Matrix.map_neg _ (RingHom.map_neg _)]; exact neg_mem ha.2
  have h2 : ∀ w ∈ genGrp D.host.F M, ∃ z ∈ GlobalTheory.ChiGrid.hatMx M, z.map (toEAf D) = w := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hw
      exact ⟨_, AddSubgroup.subset_closure ⟨α, hα, x, hx, rfl⟩, rfl⟩
    | zero => exact ⟨0, zero_mem _, Matrix.map_zero _ (RingHom.map_zero _)⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha, rfl⟩ := ha
      obtain ⟨b', hb, rfl⟩ := hb
      exact ⟨a' + b', add_mem ha hb, Matrix.map_add _ (RingHom.map_add _) _ _⟩
    | neg a _ ha =>
      obtain ⟨a', ha, rfl⟩ := ha
      exact ⟨-a', neg_mem ha, Matrix.map_neg _ (RingHom.map_neg _) _⟩
  refine ⟨h1 z, fun h => ?_⟩
  obtain ⟨z', hz', e⟩ := h2 _ h.2
  have : z' = z := by
    ext i j
    refine GlobalTheory.FunObj.ae_ext (by rw [(h1 z' hz').1, h.1]) fun Q => ?_
    rw [show toEAf D (z' i j) = toEAf D (z i j) from congrFun (congrFun e i) j]
  exact this ▸ hz'

theorem mem_hatMx_homLat_iff : ∀ (D : D7) {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (β' : GL (Fin m) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame β' Λ' → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (z : Mx D m n), z ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat Λ Λ') ↔ (∀ i j, infPart D (z i j) = 0) ∧ ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F 𝔪, (s : Formalism.IndefR.Lev.EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val (z.map (toEAf D))) β.val i j := by
  intro D m n Λ Λ' β β' hβ hβ' 𝔪 z
  rw [mem_hatMx_iff]
  exact and_congr_right fun _ => ⟨fun h => genGrp_le_frGrp hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) 𝔪 h,
    fun h => frGrp_le_genGrp hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) 𝔪 h⟩

end GlobalTheory.FunObj.HatFrame

end
