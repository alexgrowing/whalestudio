import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataLevel

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Tensor

variable {ι : Type} [Fintype ι]

def ten {R : Type} [CommRing R] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R :=
  ∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)

def nfAll {n : ℕ} (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : ℂ :=
  Formalism.REAL.fockF p q / ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))

def CSpan {n : ℕ} (lam : ι → DomWeight n) : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ delSq ℂ n (lam τ)) ∧ p = ten f}

end Tensor

section Frames

variable {ι : Type} [Fintype ι] {n : ℕ}

def Frames (_G : ι → Matrix (Fin n) (Fin n) ℂ) : Type :=
  {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}

def Frames.IsON {G : ι → Matrix (Fin n) (Fin n) ℂ} (y : Frames G) : Prop :=
  ∀ τ, (y.1 τ)ᴴ * G τ * y.1 τ = 1 ∨ (y.1 τ)ᴴ * G τ * y.1 τ = -1

def IsTr {G : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (y y' : Frames G) : Prop :=
  ∀ τ, y'.1 τ = g τ * y.1 τ

def fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₗ[ℂ] (Frames G → ℂ) where
  toFun P := fun y => (∏ τ, (M τ * y.1 τ).det ^ s τ) *
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (M x.1 * y.1 x.1) x.2.1 x.2.2) P
  map_add' P Q := by funext y; simp [mul_add]
  map_smul' c P := by funext y; simp [MvPolynomial.smul_eval]; ring

def shiftOf (lam : ι → DomWeight n) : ι → ℤ := fun τ => (lam τ).detShift

def ValC (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : Submodule ℂ (Frames G → ℂ) :=
  (CSpan lam).map (fnOf G (shiftOf lam) 1)

end Frames

section Level

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure StepLevel (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ)
    (bad : Set (HeightOneSpectrum (𝓞 F))) where
  Lb : Submodule (𝓞 E) (Fin n → E)
  Lb_fin : Module.Finite (𝓞 E) Lb
  Lb_span : Submodule.span E (Lb : Set (Fin n → E)) = ⊤
  Lb_int : ∀ x ∈ Lb, x ∈ dualSet (σ : E →+* E) J Lb
  Lb_dual : ∀ y ∈ dualSet (σ : E →+* E) J Lb, (T : E) • y ∈ Lb
  Lb_index : Lb.toAddSubgroup.relIndex
    (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)).toAddSubgroup = T ^ (2 * f)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F))
  Uloc_le : ∀ v, Uloc v ≤ UPts σ J (v.adicCompletion F)
  Uloc_lev : ∀ v, Uloc v ≤ levelVL σ J v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ bad → ((T : 𝓞 F) ∉ v.asIdeal) → Uloc v = levelVL σ J v Lb
  fM : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → Type
  [fM_acg : ∀ v h, AddCommGroup (fM v h)]
  [fM_mod : ∀ v h, Module (intV E v) (fM v h)]
  fT : ∀ v h, latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) →ₗ[intV E v] fM v h
  fT_ne : ∀ v h, fT v h ≠ 0
  fT_T : ∀ v h x, fT v h ((T : intV E v) • x) = 0
  fM_card : ∀ v h, Nat.card (fM v h) = T
  fT_L : ∀ v h x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb → fT v h x = 0
  UlocAlt : ∀ v h, Uloc v = levelVL σ J v Lb ⊓ stabFun _ (fT v h)
  U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v
  U_compact : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsCompact (U : Set (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
  U_open : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ U}
  chi : U →* ℂˣ
  chi_triv : ∀ x : U, (∀ v ∈ bad, bc (prV (E := E) v) x.1 = 1) → chi x = 1

attribute [instance] StepLevel.fM_acg StepLevel.fM_mod

end Level

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

def gramC (J : Matrix (Fin n) (Fin n) E) (emb : ι → E →+* ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => J.map (emb τ)

def atInf (emb : ι → E →+* ℂ) (γ : Matrix (Fin n) (Fin n) E) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => γ.map (emb τ)

def AdFun (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) :
    Submodule ℂ (UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ) where
  carrier := {g | ∀ (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (κ : S.U), x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1 →
    ∀ y y' : Frames (gramC J emb), IsTr (atInf emb γ) y' y → g x' y = (S.chi κ : ℂ) * g x y'}
  zero_mem' := by intro γ _ x x' κ _ y y' _; simp
  add_mem' := by
    intro a b ha hb γ hγ x x' κ h y y' hy
    simp only [Pi.add_apply]
    rw [ha γ hγ x x' κ h y y' hy, hb γ hγ x x' κ h y y' hy]; ring
  smul_mem' := by
    intro c a ha γ hγ x x' κ h y y' hy
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ha γ hγ x x' κ h y y' hy]; ring

def AdForms (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) :
    Submodule ℂ (UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ) :=
  AdFun S emb ⊓ Submodule.pi Set.univ (fun _ => ValC (gramC J emb) lam)

def res {c : Type} (emb : ι → E →+* ℂ) (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    (UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ) →ₗ[ℂ] (c → Frames (gramC J emb) → ℂ) :=
  LinearMap.funLeft ℂ _ yc

def FiC (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) {c : Type}
    (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Submodule ℂ (c → Frames (gramC J emb) → ℂ) :=
  (AdForms S emb lam).map (res emb yc)

abbrev Cls (S : StepLevel F E σ J T f bad) : Type :=
  ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
    (S.U.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))

def IsDia (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ)
    (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  (∀ v', v' ≠ v → bc (prV (E := E) v') δ.1 = 1) ∧
  bc (prV (E := E) v) δ.1 ∈ levelVL σ J v S.Lb ∧
  ∃ hg : bc (prV (E := E) v) δ.1 ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
    ∀ x : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      a • S.fT v hv ⟨(bc (prV (E := E) v) δ.1).1 *ᵥ x.1, (hg x.1).1 x.2⟩ = S.fT v hv x

def IsLocBasis (l : ℕ) (L : Set (Fin n → E)) (B : GL (Fin n) E) : Prop :=
  ∀ x : Fin n → E, (∃ s : ℕ, ¬ l ∣ s ∧ (s : E) • x ∈ L) ↔
    ∃ s : ℕ, ¬ l ∣ s ∧ ∀ a, (s : E) * (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) a ∈
      (algebraMap (𝓞 E) E).range

end Adelic

end Formalism.L2.Forms
