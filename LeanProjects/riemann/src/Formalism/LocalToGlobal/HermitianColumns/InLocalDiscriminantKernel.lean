import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD

noncomputable section

namespace Formalism.L2.Herm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

abbrev Af (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F

def crd (S : HSpace E) : S.V ≃ₗ[E] (Fin S.rank → E) := S.frame.equivFun

def crdLat (S : HSpace E) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (Fin S.rank → E) :=
  L.map ((crd S : S.V →ₗ[E] (Fin S.rank → E)).restrictScalars (𝓞 E))

theorem hT_crd (hc : CMData F E) (S : HSpace E) (x y : S.V) :
    S.hT x y = hform (hc.sig : E →+* E) S.gram (crd S x) (crd S y) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum]
  unfold hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply, crd, Module.Basis.equivFun_apply, CMData.sig, HSpace.gram]
  show _ = star _ * _ * _
  ring

def UF (hc : CMData F E) (S : HSpace E) : Subgroup (GL (Fin S.rank) E) :=
  UJ (hc.sig : E →+* E) S.gram

def Uv (hc : CMData F E) (S : HSpace E) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) :=
  UPts hc.sig S.gram (v.adicCompletion F)

def UAf (hc : CMData F E) (S : HSpace E) : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F)) :=
  UPts hc.sig S.gram (Af F)

def UFin (hc : CMData F E) (S : HSpace E) : Subgroup (UAf hc S) :=
  (ratPts hc.sig S.gram (Af F)).subgroupOf (UAf hc S)

abbrev intAf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (E ⊗[F] Af F) :=
  tensInt (F := F) (Af F) (intOE E) (intAd F)

def hatL {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (intAf F E) (Fin n → E ⊗[F] Af F) :=
  latS (F := F) (Af F) (intAf F E) Λ

def locL {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

def dualL (hc : CMData F E) (S : HSpace E) (Λ : Submodule (𝓞 E) (Fin S.rank → E)) :
    Submodule (𝓞 E) (Fin S.rank → E) :=
  Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) S.gram Λ)

def InLocalDiscriminantKernel (hc : CMData F E) (S : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) (x : GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) : Prop :=
  x ∈ levelVL hc.sig S.gram v Λ ∧
    ∀ y ∈ locL v (dualL hc S Λ),
      (x : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ locL v Λ

def InPrinc (hc : CMData F E) (S : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) (x : GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) : Prop :=
  x ∈ levelVL hc.sig S.gram v Λ ∧
    ∀ y ∈ locL v Λ, ∃ z ∈ locL v Λ,
      (x : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y =
        (g : E ⊗[F] v.adicCompletion F) • z

structure StepLevel (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ) (T f : ℕ) where

  Lb : Submodule (𝓞 E) (Fin S.rank → E)
  Lb_fin : Module.Finite (𝓞 E) Lb
  Lb_span : Submodule.span E (Lb : Set (Fin S.rank → E)) = ⊤
  Lb_int : Lb ≤ dualL hc S Lb
  Lb_dual : ∀ y ∈ dualL hc S Lb, (T : E) • y ∈ Lb
  Lb_index : Lb.toAddSubgroup.relIndex (dualL hc S Lb).toAddSubgroup = T ^ (2 * f)

  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))
  Uloc_lev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) →
    ((gp 1 : 𝓞 F) ∉ v.asIdeal) → ((T : 𝓞 F) ∉ v.asIdeal) → Uloc v = levelVL hc.sig S.gram v Lb
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    ∀ x, InPrinc hc S v (gp i) Lb x → x ∈ Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x, x ∈ Uloc v ↔ InLocalDiscriminantKernel hc S v Lb x

  U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

structure StepLevel0 (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) where

  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))
  Uloc_lev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) →
    ((gp 1 : 𝓞 F) ∉ v.asIdeal) → Uloc v = levelVL hc.sig S.gram v Lb
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    ∀ x, InPrinc hc S v (gp i) Lb x → x ∈ Uloc v

  U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

structure ClassTie (hc : CMData F E) (S : HSpace E) (Lb : Submodule (𝓞 E) (Fin S.rank → E))
    (U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) S.V) where
  y : cls → UAf hc S
  y_bij : Function.Bijective (fun c : cls =>
    (Quotient.mk'' (y c) : ClassSet (UFin hc S) (U.subgroupOf (UAf hc S))))
  y_lat : ∀ c (x : Fin S.rank → E ⊗[F] Af F), x ∈ hatL (F := F) (crdLat S (lat c)) ↔
    ((((y c : GL (Fin S.rank) (E ⊗[F] Af F)))⁻¹ : GL (Fin S.rank) (E ⊗[F] Af F)) :
      Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) *ᵥ x ∈ hatL (F := F) Lb
  stabI : ∀ c, stab c →* UF hc S
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UF hc S), γ ∈ (stabI c).range ↔
    bc (inclE (F := F) (Af F)) (γ : GL (Fin S.rank) E) ∈
      U.map (MulAut.conj (y c : GL (Fin S.rank) (E ⊗[F] Af F))).toMonoidHom

structure FvTie (hc : CMData F E) (S : HSpace E) (Lb : Submodule (𝓞 E) (Fin S.rank → E)) {cls : Type}
    (y : cls → UAf hc S) (lat : cls → Submodule (𝓞 E) S.V) (w : HeightOneSpectrum (𝓞 F))
    (k : Type) [AddCommGroup k] (fz : ∀ c, Formalism.HermitianLatticesTheory.dual S.hT (lat c) → k) where

  fb : locL w (dualL hc S Lb) →+ k
  fvI : ∀ c (z : Formalism.HermitianLatticesTheory.dual S.hT (lat c)) (t : locL w (dualL hc S Lb)),
    ((bc (prV (E := E) w) (y c : GL (Fin S.rank) (E ⊗[F] Af F)) : GL (Fin S.rank) (E ⊗[F] w.adicCompletion F)) :
      Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] w.adicCompletion F)).mulVec t.1 =
      (fun a => inclE (F := F) (w.adicCompletion F) (crd S z.1 a)) →
    fz c z = fb t

def IsStd (S : HSpace E) : Prop :=
  ∃ b : Module.Basis (Fin S.rank) E S.V, (∀ a a', S.hT (b a) (b a') = if a = a' then 1 else 0) ∧
    S.L0 = Submodule.span (𝓞 E) (Set.range b)

def unitaryOneFiniteAdeles (hc : CMData F E) : Subgroup (GL (Fin 1) (E ⊗[F] Af F)) :=
  UPts hc.sig (1 : Matrix (Fin 1) (Fin 1) E) (Af F)

def IntegralUnitGroup (hc : CMData F E) : Subgroup (GL (Fin 1) (E ⊗[F] Af F)) :=
  levelAf hc.sig (1 : Matrix (Fin 1) (Fin 1) E)

def unitaryOneRationalAdele (F : Type) [Field F] [NumberField F] [Algebra F E] (z : unitary E) : (E ⊗[F] Af F)ˣ :=
  Units.map (inclE (F := F) (Af F)).toMonoidHom (Unitary.toUnits z)

def UstdAf (hc : CMData F E) (N : ℕ) : Subgroup (GL (Fin N) (E ⊗[F] Af F)) :=
  UPts hc.sig (1 : Matrix (Fin N) (Fin N) E) (Af F)

def Carries {N : ℕ} (g : GL (Fin N) (E ⊗[F] Af F)) (L L' : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  ∀ x : Fin N → E ⊗[F] Af F, x ∈ hatL (F := F) L' ↔
    ((g⁻¹ : GL (Fin N) (E ⊗[F] Af F)) : Matrix (Fin N) (Fin N) (E ⊗[F] Af F)) *ᵥ x ∈ hatL (F := F) L

def IsDetOf (hc : CMData F E) {N : ℕ} (x : unitaryOneFiniteAdeles hc) (g : GL (Fin N) (E ⊗[F] Af F)) : Prop :=
  Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (E ⊗[F] Af F)) = Matrix.GeneralLinearGroup.det g

end Formalism.L2.Herm

end
