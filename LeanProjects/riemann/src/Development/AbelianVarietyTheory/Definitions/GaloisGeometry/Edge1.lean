import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.VerticalBoundHeightCompare
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD
open scoped TensorProduct

namespace GlobalTheory.WH

section Wd

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]

def wd (w : ι → Module.End k E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  LinearMap.pi fun t => ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • (w i ∘ₗ LinearMap.proj (t.erase i))

def pw (f : Module.End k E) : Module.End k (Finset ι → E) := LinearMap.pi fun t => f ∘ₗ LinearMap.proj t

def tD (w : ι → Module.End k E) (κ : Module.End k E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  wd w + LinearMap.pi fun t => ((-1 : ℤ) ^ t.card) • (κ ∘ₗ LinearMap.proj t)

def tcx (T : ℤ → Finset ι → Submodule k E) (w : ι → Module.End k E) (κ : Module.End k E) : Cx k (Finset ι → E) :=
  ⟨fun n => Submodule.pi Set.univ fun s => T (n - s.card) s, tD w κ⟩

def acx (A : Finset ι → Submodule k E) (w : ι → Module.End k E) : Cx k (Finset ι → E) :=
  ⟨fun n => Submodule.pi Set.univ fun s => if (s.card : ℤ) = n then A s else ⊥, wd w⟩

def cupE {E' E'' : Type} [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'')
    (a : Finset ι → E) (b : Finset ι → E') : Finset ι → E'' := fun u =>
  ∑ j ∈ u, μ (a (u.filter (· ≤ j))) (b (u.filter (j ≤ ·)))

def vec (v : ι → E) : Finset ι → E := fun t => ∑ i ∈ t, if t.card = 1 then v i else 0

end Wd

section Join

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

def lft (s : Finset (ι ⊕ₗ κ)) : Finset ι := (s.map (ofLex : ι ⊕ₗ κ ≃ ι ⊕ κ).toEmbedding).toLeft

def rgt (s : Finset (ι ⊕ₗ κ)) : Finset κ := (s.map (ofLex : ι ⊕ₗ κ ≃ ι ⊕ κ).toEmbedding).toRight

def uni (I : Finset ι) (J : Finset κ) : Finset (ι ⊕ₗ κ) := (I.disjSum J).map (toLex : ι ⊕ κ ≃ ι ⊕ₗ κ).toEmbedding

variable {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']

def join (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') : Finset (ι ⊕ₗ κ) → E'' :=
  fun s => μ (a (lft s)) (b (rgt s))

def edge1 (a : Finset ι → E) : Finset (ι ⊕ₗ κ) → E := fun s => if (rgt s).card = 1 then a (lft s) else 0

def edge2 (b : Finset κ → E) : Finset (ι ⊕ₗ κ) → E := fun s => if (lft s).card = 1 then b (rgt s) else 0

def lcup (μ : E →ₗ[k] E' →ₗ[k] E'') (x : Finset ι → E) (c : Finset (ι ⊕ₗ κ) → E') : Finset (ι ⊕ₗ κ) → E'' := fun s =>
  ∑ i ∈ lft s, μ (x ((lft s).filter (· ≤ i))) (c (s.filter fun t => toLex (Sum.inl i) ≤ t))

def mixF (A : Finset ι → Finset κ → Submodule k E) (s : Finset (ι ⊕ₗ κ)) : Submodule k E :=
  if (lft s).Nonempty ∧ (rgt s).Nonempty then A (lft s) (rgt s) else ⊥

end Join

section Koszul

variable {k : Type} [Field k] {σ : Type} [LinearOrder σ] {E : Type} [AddCommGroup E] [Module k E]

def kFam (Y : σ → Module.End k E) (u v : Module.End k E) (M : Submodule k E) (q : ℤ) : Submodule k (Finset σ → E) :=
  (⨅ T ∈ {T : Finset σ | (T.card : ℤ) ≠ q}, LinearMap.ker (LinearMap.proj T : (Finset σ → E) →ₗ[k] E)) ⊓
    LinearMap.ker (wd Y) ⊓ Submodule.pi Set.univ fun _ => M.map (u ^ (q - 1).toNat * v)

def ytop (Y : σ → Module.End k E) (m : E) : Finset σ → E := wd Y (Pi.single ∅ m)

end Koszul

section Forms

variable (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → F)

def XZ (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  LinearMap.rTensor _ ((Algebra.lsmul ℂ ℂ (DR ℂ K)) (algebraMap F K (x l)))

def YZ (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  LinearMap.lTensor _ ((Algebra.lsmul ℂ ℂ (DR ℂ K)) (algebraMap F K (x l)))

def actZ : K ⊗[ℂ] K →ₐ[ℂ] Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K)))

def MZ (a : ℕ) (I J : Finset (Fin (d + 1))) : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  Submodule.map₂ (TensorProduct.mk ℂ _ _) (omB ℂ K (rB ℂ K x I) (d - a)) (omB ℂ K (rB ℂ K x J) a)

def ctr (τ : DR ℂ K →ₗ[K] K) (w : DR ℂ K) : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  TensorProduct.lift ((Algebra.lsmul ℂ ℂ (DR ℂ K)).toLinearMap ∘ₗ ((Algebra.linearMap F K).restrictScalars ℂ ∘ₗ
    (Algebra.trace F K).restrictScalars ℂ ∘ₗ τ.restrictScalars ℂ ∘ₗ LinearMap.mulLeft ℂ w))

end Forms

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ}

def pr2L (j2 : K →ₐ[ℂ] K') : DR ℂ K →ₗ[ℂ] DR ℂ K' :=
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  (GlobalTheory.W1.mapDR ℂ K K').toLinearMap.restrictScalars ℂ

def R2 (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') (J : Finset (Fin (d + 1))) : Subalgebra ℂ K' :=
  (integralClosure ((rB ℂ K x J).map j2) K').restrictScalars ℂ

variable [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']

def RY (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) : Subalgebra ℂ K' :=
  rB ℂ K' x I ⊔ R2 x j2 J

def gY (j2 : K →ₐ[ℂ] K') : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K' :=
  TensorProduct.lift ((LinearMap.mul ℂ (DR ℂ K')).compl₁₂ ((GlobalTheory.W1.mapDR ℂ K K').toLinearMap.restrictScalars ℂ) (pr2L j2))

def Val (B : Subalgebra ℂ K') (e : B →ₐ[ℂ] ℂ) (v : K') (c : ℂ) : Prop :=
  ∃ (b : K') (hb : b ∈ B) (hbv : b * v ∈ B), e ⟨b, hb⟩ ≠ 0 ∧ e ⟨b * v, hbv⟩ = e ⟨b, hb⟩ * c

def IsFix (B : Subalgebra ℂ K') (e : B →ₐ[ℂ] ℂ) (j2 : K →ₐ[ℂ] K') (B0 : Subalgebra ℂ K) : Prop :=
  ∀ b ∈ B0, ∀ h1 : algebraMap K K' b ∈ B, Val B e (j2 b) (e ⟨_, h1⟩)

end Y

end GlobalTheory.WH
