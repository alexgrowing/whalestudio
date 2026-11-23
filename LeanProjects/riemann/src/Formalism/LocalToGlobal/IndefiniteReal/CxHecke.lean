import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteForms.PairingConditionOfInverseMatrixIdentity

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cpt_smul (σ : K →+* ℂ) {n : ℕ} (a : K) (x : Fin n → K) : cpt σ (a • x) = σ a • cpt σ x := by
  funext i
  simp [cpt]

theorem relMat_op_key (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {D : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E)
    (S : Module.End ℂ E) (hS : ∀ y, S (f y) ∈ LinearMap.range f) (hr : IsRat σ (relMat f (S ∘ₗ f)))
    (x : Fin D → K) :
    f (cpt σ ((kMat σ (relMat f (S ∘ₗ f))).mulVec x)) = S (f (cpt σ x)) := by
  have hsol : ∀ e ∈ LinearMap.range f, f (solve f e) = e := by
    rintro e ⟨y, rfl⟩
    have h : ∃ y', f y' = f y := ⟨y, rfl⟩
    simp only [solve, dif_pos h]
    exact h.choose_spec
  have hk : ∀ i k, σ (kOf σ (relMat f (S ∘ₗ f) i k)) = relMat f (S ∘ₗ f) i k := by
    intro i k
    obtain ⟨a, ha⟩ := hr i k
    have h : ∃ a : K, σ a = relMat f (S ∘ₗ f) i k := ⟨a, ha⟩
    simp only [kOf, dif_pos h]
    exact h.choose_spec
  have hc : cpt σ ((kMat σ (relMat f (S ∘ₗ f))).mulVec x) = (relMat f (S ∘ₗ f)).mulVec (cpt σ x) := by
    funext i
    simp only [cpt, Matrix.mulVec, dotProduct, kMat, Matrix.map_apply, map_sum, map_mul, hk]
  rw [hc]
  have hv : ∀ v : Fin D → ℂ, v = ∑ k, v k • (Pi.single k (1 : ℂ) : Fin D → ℂ) := fun v => by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hcol : ∀ k, f (fun i => relMat f (S ∘ₗ f) i k) = S (f (Pi.single k 1)) := by
    intro k
    have h : (fun i => relMat f (S ∘ₗ f) i k) = solve f (S (f (Pi.single k 1))) := by
      funext i
      simp [relMat]
    rw [h, hsol _ (hS _)]
  have hM : (relMat f (S ∘ₗ f)).mulVec (cpt σ x) =
      ∑ k, (cpt σ x) k • (fun i => relMat f (S ∘ₗ f) i k) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hM, map_sum]
  conv_rhs => rw [hv (cpt σ x), map_sum, map_sum]
  simp only [map_smul, hcol]

theorem eig_transport (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {D : ℕ} {H : Type}
    (f : (Fin D → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (S : H → Module.End ℂ E)
    (hS : ∀ T y, S T (f y) ∈ LinearMap.range f) (hr : ∀ T, IsRat σ (relMat f (S T ∘ₗ f)))
    (P : Submodule ℂ E) (e : H → K)
    (hP : P ⊓ LinearMap.range f = (⨅ T, LinearMap.ker (S T - σ (e T) • LinearMap.id)) ⊓ LinearMap.range f) :
    P.comap (f.comp (cptL σ D)) =
      ⨅ T, LinearMap.ker (Matrix.toLin' (kMat σ (relMat f (S T ∘ₗ f))) - e T • LinearMap.id) := by
  have hcinj : ∀ {a b : Fin D → K}, cpt σ a = cpt σ b → a = b := fun h =>
    funext fun i => σ.injective (congrFun h i)
  have key : ∀ x, x ∈ P.comap (f.comp (cptL σ D)) ↔ f (cpt σ x) ∈ P := fun x => Iff.rfl
  ext x
  rw [key]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Matrix.toLin'_apply, sub_eq_zero]
  have hmem : f (cpt σ x) ∈ LinearMap.range f := LinearMap.mem_range_self f _
  constructor
  · intro hx T
    have h1 : f (cpt σ x) ∈ P ⊓ LinearMap.range f := Submodule.mem_inf.mpr ⟨hx, hmem⟩
    rw [hP] at h1
    have h2 := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp h1).1 T
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h2
    apply hcinj
    apply hf
    rw [relMat_op_key σ f (S T) (hS T) (hr T) x, cpt_smul, map_smul]
    exact h2
  · intro hx
    have h1 : f (cpt σ x) ∈ P ⊓ LinearMap.range f := by
      rw [hP]
      refine Submodule.mem_inf.mpr ⟨(Submodule.mem_iInf _).mpr fun T => ?_, hmem⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      have h3 := relMat_op_key σ f (S T) (hS T) (hr T) x
      rw [hx T, cpt_smul, map_smul] at h3
      exact h3.symm
    exact (Submodule.mem_inf.mp h1).1

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)
  (cf : ConvFace Bs)

structure HeckeRowsC where

  hC : cf.Hk → Module.End ℂ X.EE

  maps : ∀ T, ∀ e ∈ X.EEl b, hC T e ∈ X.EEl b

  rat : ∀ T, IsRat Bs.v0.embedding (relMat (X.iC cr b Bs.μ0) (hC T ∘ₗ X.iC cr b Bs.μ0))

  eig : ∀ c, X.EEp c ⊓ X.EEl b =
    (⨅ T, LinearMap.ker (hC T - Bs.v0.embedding (cf.ev c T) • LinearMap.id)) ⊓ X.EEl b

structure HeckeWC where

  hC : ∀ j, cf.Hk → Module.End ℂ (X.W j)

  maps : ∀ j T y, hC j T (X.w0C b j y) ∈ LinearMap.range (X.w0C b j)

  rat : ∀ j T, IsRat Bs.v0.embedding (relMat (X.w0C b j) (hC j T ∘ₗ X.w0C b j))

  eig : ∀ j c, X.Wp j c ⊓ LinearMap.range (X.w0C b j) =
    (⨅ T, LinearMap.ker (hC j T - Bs.v0.embedding (cf.ev c T) • LinearMap.id)) ⊓ LinearMap.range (X.w0C b j)

variable {X cr b cf}

def HeckeRowsC.hEK (H : X.HeckeRowsC cr b cf) (T : cf.Hk) :
    Module.End K (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :=
  Matrix.toLin' (kMat Bs.v0.embedding (relMat (X.iC cr b Bs.μ0) (H.hC T ∘ₗ X.iC cr b Bs.μ0)))

def HeckeWC.hWK (H : X.HeckeWC b cf) (j : Bs.J) (T : cf.Hk) : Module.End K (Fin (X.dW b j) → K) :=
  Matrix.toLin' (kMat Bs.v0.embedding (relMat (X.w0C b j) (H.hC j T ∘ₗ X.w0C b j)))

theorem HeckeRowsC.maps' (h2 : X.H2 cr b) (H : X.HeckeRowsC cr b cf) (T : cf.Hk) (y) :
    H.hC T (X.iC cr b Bs.μ0 y) ∈ LinearMap.range (X.iC cr b Bs.μ0) := by
  rw [h2.2.2]
  apply H.maps
  rw [← h2.2.2]
  exact LinearMap.mem_range_self _ y

theorem HeckeRowsC.key (h2 : X.H2 cr b) (H : X.HeckeRowsC cr b cf) (T : cf.Hk)
    (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :
    X.iC cr b Bs.μ0 (cpt Bs.v0.embedding (H.hEK T x)) = H.hC T (X.iC cr b Bs.μ0 (cpt Bs.v0.embedding x)) := by
  simpa [HeckeRowsC.hEK, Matrix.toLin'_apply] using
    relMat_op_key Bs.v0.embedding (X.iC cr b Bs.μ0) (H.hC T) (H.maps' h2 T) (H.rat T) x

theorem HeckeWC.key (H : X.HeckeWC b cf) (j : Bs.J) (T : cf.Hk) (x : Fin (X.dW b j) → K) :
    X.w0C b j (cpt Bs.v0.embedding (H.hWK j T x)) = H.hC j T (X.w0C b j (cpt Bs.v0.embedding x)) := by
  simpa [HeckeWC.hWK, Matrix.toLin'_apply] using
    relMat_op_key Bs.v0.embedding (X.w0C b j) (H.hC j T) (H.maps j T) (H.rat j T) x

theorem HeckeRowsC.eigE (h2 : X.H2 cr b) (H : X.HeckeRowsC cr b cf) (c : Bs.Ix) :
    X.Ep cr b c = ⨅ T, LinearMap.ker (H.hEK T - cf.ev c T • LinearMap.id) := by
  have h := eig_transport Bs.v0.embedding (X.iC cr b Bs.μ0) h2.1 H.hC (H.maps' h2) H.rat (X.EEp c) (cf.ev c)
    (by rw [h2.2.2]; exact H.eig c)
  exact h

theorem HeckeWC.eigW (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (H : X.HeckeWC b cf) (j : Bs.J)
    (c : Bs.Ix) :
    X.WpK b j c = ⨅ T, LinearMap.ker (H.hWK j T - cf.ev c T • LinearMap.id) := by
  have hinjW : Function.Injective (X.wC b j Bs.v0) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c' hc
    simp only [wC, lin, Fintype.linearCombination_apply] at hc
    funext i
    exact Fintype.linearIndependent_iff.mp (hk j Bs.v0).1 c' hc i
  have hinjE : Function.Injective (X.eW b j) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := he j x x
    rw [hx, inner_zero_left] at h
    have h' : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h'' : ⟪x, x⟫_ℂ = 0 := (mul_eq_zero.mp h.symm).resolve_left h'
    exact inner_self_eq_zero.mp h''
  have hinj : Function.Injective (X.w0C b j) := by
    first
    | exact hinjE.comp hinjW
    | (simp only [w0C, LinearMap.coe_comp]; exact hinjE.comp hinjW)
  exact eig_transport Bs.v0.embedding (X.w0C b j) hinj (H.hC j) (H.maps j) (H.rat j) (X.Wp j c) (cf.ev c)
    (H.eig j c)

def heckeRows_of (h2 : X.H2 cr b) (H : X.HeckeRowsC cr b cf) : HeckeRows cf (X.data cr b) where
  hE := H.hEK
  eigE := H.eigE h2

def heckeAll_of (h2 : X.H2 cr b) (hk : X.KForm b) (he : X.EWnorm b) (hn : 0 < X.nP b) (H : X.HeckeRowsC cr b cf)
    (HW : X.HeckeWC b cf) : HeckeAll cf (X.data cr b) where
  toHeckeRows := heckeRows_of h2 H
  hW := HW.hWK
  eigW := HW.eigW hk he hn

theorem heckeB_of (h2 : X.H2 cr false) (hk : X.KForm false) (he : X.EWnorm false) (hp : X.H4pos)
    (H : X.HeckeRowsC cr false cf) (HW : X.HeckeWC false cf) : Nonempty (HeckeAll cf (X.data cr false)) := ⟨heckeAll_of h2 hk he (hp.2.2 false) H HW⟩

theorem heckeC_of (h2 : X.H2 cr true) (H : X.HeckeRowsC cr true cf) : Nonempty (HeckeRows cf (X.data cr true)) := ⟨heckeRows_of h2 H⟩

end CxData

end Formalism.IndefR.Cx
