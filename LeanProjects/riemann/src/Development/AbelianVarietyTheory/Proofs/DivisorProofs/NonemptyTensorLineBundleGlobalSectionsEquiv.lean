import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

noncomputable section

namespace GlobalTheory.SecTensor

open TensorProduct

theorem isLocalizedModule_mulTensor {R M N B : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [CommRing B] [Algebra R B] (r : R) [IsLocalization.Away r B]
    (c : M →ₗ[R] B) (d : N →ₗ[R] B) [IsLocalizedModule.Away r c] [IsLocalizedModule.Away r d] :
    IsLocalizedModule.Away r (TensorProduct.lift ((LinearMap.mul R B).compl₁₂ c d)) := by
  have hc : IsBaseChange B c := (isLocalizedModule_iff_isBaseChange (.powers r) B c).1 inferInstance
  have hd : IsBaseChange B d := (isLocalizedModule_iff_isBaseChange (.powers r) B d).1 inferInstance
  show IsLocalizedModule (.powers r) _
  rw [isLocalizedModule_iff_isBaseChange (.powers r) B]
  have h1 := isBaseChange_tensorProduct_map (R := R) (P := N) B hc
  have h2 := h1.comp (IsBaseChange.ofEquiv hd.equiv)
  have heq : TensorProduct.lift ((LinearMap.mul R B).compl₁₂ c d) =
      (hd.equiv.toLinearMap.restrictScalars R) ∘ₗ
        (AlgebraTensorModule.map c (LinearMap.id (R := R) (M := N))).restrictScalars R := by
    ext m n
    simp [IsBaseChange.equiv_tmul]
  rw [heq]
  exact h2

theorem bijective_of_mulTensor {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (μ : M ⊗[R] N →ₗ[R] P)
    (s : Set R) (hs : Ideal.span s = ⊤) (B : s → Type*) [∀ r, CommRing (B r)]
    [∀ r, Algebra R (B r)] [∀ r : s, IsLocalization.Away r.1 (B r)]
    (c : ∀ r, M →ₗ[R] B r) (d : ∀ r, N →ₗ[R] B r) (e : ∀ r, P →ₗ[R] B r)
    [∀ r : s, IsLocalizedModule.Away r.1 (c r)] [∀ r : s, IsLocalizedModule.Away r.1 (d r)]
    [∀ r : s, IsLocalizedModule.Away r.1 (e r)]
    (h : ∀ r m n, e r (μ (m ⊗ₜ n)) = c r m * d r n) : Function.Bijective μ := by
  have (r : s) := isLocalizedModule_mulTensor r.1 (c r) (d r)
  refine bijective_of_isLocalized_span s hs (fun r => B r)
    (fun r => TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (fun r => B r) e μ
    fun r => ?_
  have : IsLocalizedModule.map (.powers r.1)
      (TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (e r) μ = LinearMap.id := by
    apply IsLocalizedModule.linearMap_ext (.powers r.1)
      (TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (e r)
    rw [IsLocalizedModule.map_comp]
    ext m n
    simp [h]
  rw [this]
  exact Function.bijective_id

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

variable {T : Scheme.{0}}

def mulFun (A B : LB T) (s : LB.Sec A) (t : LB.Sec B) (p : A.ι × B.ι) :
    Γ(T, A.U p.1 ⊓ B.U p.2) :=
  resG T (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ A.U p.1) (s.f p.1) *
    resG T (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2) (t.f p.2)

def mulSec (A B : LB T) (s : LB.Sec A) (t : LB.Sec B) : LB.Sec (CechPic.tens A B) where
  f := mulFun A B s t
  compat := fun (p q : A.ι × B.ι) => by
    unfold CechPic.tens
    change resG T _ (_ * _) = _ * resG T _ (_ * _)
    simp only [map_mul, resG_resG]
    rw [sec_rel s p.1 q.1 (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)),
      sec_rel t p.2 q.2 (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))]
    simp only [Units.val_mul, val_res, resG_resG]
    ring

def mulBil (A B : LB T) :
    LB.Sec A →ₗ[Γ(T, ⊤)] LB.Sec B →ₗ[Γ(T, ⊤)] LB.Sec (CechPic.tens A B) :=
  LinearMap.mk₂ Γ(T, ⊤) (mulSec A B)
    (fun s s' t => f_injective (show mulFun A B (s + s') t = mulFun A B s t + mulFun A B s' t from
      funext fun p => by simp only [mulFun, add_f, map_add, add_mul, Pi.add_apply]))
    (fun a s t => f_injective (show mulFun A B (a • s) t =
      fun (p : A.ι × B.ι) => resG T (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) a * mulFun A B s t p
      from funext fun p => by simp only [mulFun, smul_f, map_mul, resG_resG]; ring))
    (fun s t t' => f_injective (show mulFun A B s (t + t') = mulFun A B s t + mulFun A B s t' from
      funext fun p => by simp only [mulFun, add_f, map_add, mul_add, Pi.add_apply]))
    (fun a s t => f_injective (show mulFun A B s (a • t) =
      fun (p : A.ι × B.ι) => resG T (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) a * mulFun A B s t p
      from funext fun p => by simp only [mulFun, smul_f, map_mul, resG_resG]; ring))

def chartLoc (L : LB T) (r : Γ(T, ⊤)) (i : L.ι) (h : T.basicOpen r ≤ L.U i) :
    LB.Sec L →ₗ[Γ(T, ⊤)] Γ(T, T.basicOpen r) where
  toFun s := resG T h (s.f i)
  map_add' s t := by simp only [add_f, map_add]
  map_smul' a s := by
    simp only [smul_f, map_mul, resG_resG, RingHom.id_apply, Algebra.smul_def]
    rfl

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

variable {T : Scheme.{0}}

def chartEquivTop (L : LB T) (hL : L.IsLB) (r : Γ(T, ⊤)) (i : L.ι) (h : T.basicOpen r ≤ L.U i) :
    AbLaw.SecOn L (T.basicOpen r) ≃ₗ[Γ(T, ⊤)] Γ(T, T.basicOpen r) :=
  { chartEquiv hL i h with
    map_smul' := fun a s => by
      rw [AbLaw.SecOn.smul_basicOpen_def]
      exact ((chartEquiv hL i h).map_smul _ s).trans (Algebra.smul_def a _).symm }

theorem isLocalizedModule_chartLoc [IsAffine T] (L : LB T) (hL : L.IsLB) (r : Γ(T, ⊤)) (i : L.ι)
    (h : T.basicOpen r ≤ L.U i) : IsLocalizedModule.Away r (chartLoc L r i h) := by
  haveI := AbLaw.SecOn.isLocalizedModule_resBasicOpen hL (isAffineOpen_top T) r
  haveI := IsLocalizedModule.of_linearEquiv (S := .powers r) (f := AbLaw.SecOn.resBasicOpen L r)
    (chartEquivTop L hL r i h)
  haveI := IsLocalizedModule.of_linearEquiv_right (S := .powers r)
    (f := (chartEquivTop L hL r i h).toLinearMap ∘ₗ AbLaw.SecOn.resBasicOpen L r)
    (globalEquiv L).symm
  have e : chartLoc L r i h = ((chartEquivTop L hL r i h).toLinearMap ∘ₗ
      AbLaw.SecOn.resBasicOpen L r) ∘ₗ (globalEquiv L).symm.toLinearMap := by
    ext s
    change resG T h (s.f i) = chartEquiv hL i h (AbLaw.SecOn.restrict L _ (ofSec s ⊤))
    rw [chartEquiv_apply, AbLaw.SecOn.restrict_eq_map, coord_map, coord_ofSec, resG_resG, resG_resG]
  rw [e]
  infer_instance

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

theorem tensorSecEquiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB →
    Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)]
      LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  intro T _ A B hA hB
  let s : Set Γ(T, ⊤) := {f | ∃ i j, T.basicOpen f ≤ A.U i ⊓ B.U j}
  have hs : Ideal.span s = ⊤ := by
    rw [← (isAffineOpen_top T).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hA.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hB.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨f, hf, hxf⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := A.U i ⊓ B.U j) ⟨x, hi, hj⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, j, hf⟩, hxf⟩
  have (r : s) := (isAffineOpen_top T).isLocalization_basicOpen r.1
  let i (r : s) : A.ι := r.2.choose
  let j (r : s) : B.ι := r.2.choose_spec.choose
  have hij (r : s) : T.basicOpen r.1 ≤ A.U (i r) ⊓ B.U (j r) := r.2.choose_spec.choose_spec
  have (r : s) := isLocalizedModule_chartLoc A hA r.1 (i r) ((hij r).trans inf_le_left)
  have (r : s) := isLocalizedModule_chartLoc B hB r.1 (j r) ((hij r).trans inf_le_right)
  have (r : s) := isLocalizedModule_chartLoc (CechPic.tens A B) (CechPic.isLB_tens hA hB) r.1
    ((i r, j r) : A.ι × B.ι) (hij r)
  refine ⟨LinearEquiv.ofBijective (TensorProduct.lift (mulBil A B))
    (bijective_of_mulTensor _ s hs (fun r => Γ(T, T.basicOpen r.1))
      (fun r => chartLoc A r.1 (i r) ((hij r).trans inf_le_left))
      (fun r => chartLoc B r.1 (j r) ((hij r).trans inf_le_right))
      (fun r => chartLoc (CechPic.tens A B) r.1 ((i r, j r) : A.ι × B.ι) (hij r))
      fun r m n => ?_)⟩
  rw [TensorProduct.lift.tmul]
  change resG T (hij r) (mulFun A B m n (i r, j r)) = _ * _
  simp only [mulFun, map_mul, resG_resG]
  rfl

end GlobalTheory.SecTensor
