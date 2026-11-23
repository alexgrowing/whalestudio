import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviProjTwo

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

section Abstract

variable {G : Type} [Group G]

def dcos (Q P : Subgroup G) (x : G) : Set G := {g | ∃ q ∈ Q, ∃ p ∈ P, g = q * x * p}

def LocSec [TopologicalSpace G] (Q P : Subgroup G) (x : G) : Prop :=
  ∀ OQ ∈ 𝓝 (1 : G), ∀ OP ∈ 𝓝 (1 : G), ∃ O ∈ 𝓝 (1 : G), ∀ u ∈ O, x * u ∈ dcos Q P x →
    ∃ s ∈ Q, s ∈ OQ ∧ ∃ p ∈ P, p ∈ OP ∧ x * u = s * x * p

variable [TopologicalSpace G] [IsTopologicalGroup G]
  {W₁ W₂ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

def resInd {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v)) :
    smoothPart (ind Q σ) →ₗ[ℂ] smoothPart (ind H τ) where
  toFun f := ⟨⟨fun p => E (f.1.1 (x * (p : G))), by
      intro h p
      have hq := (hH h).1 h.2
      have e : x * (((h * p : P)) : G) = (⟨_, hq⟩ : Q) * (x * (p : G)) := by
        simp [mul_assoc]
      show E (f.1.1 (x * (((h : P) * p : P) : G))) = τ h (E (f.1.1 (x * (p : G))))
      rw [hE h hq, show x * (((h : P) * p : P) : G) = ((⟨_, hq⟩ : Q) : G) * (x * (p : G)) from e]
      exact congrArg E (f.1.2 _ _)⟩, by
      have hf : IsOpen {g : G | ind Q σ g f.1 = f.1} := f.2
      have hopen : IsOpen {p : P | ind Q σ (p : G) f.1 = f.1} := hf.preimage continuous_subtype_val
      refine mem_smoothPart_of_nhds ?_
      filter_upwards [hopen.mem_nhds (by simp)] with p hp
      refine Subtype.ext (funext fun y => ?_)
      have := congrArg (fun F : indSpace Q σ => F.1 (x * (y : G))) hp
      show E (f.1.1 (x * ((y * p : P) : G))) = E (f.1.1 (x * (y : G)))
      rw [show x * ((y * p : P) : G) = x * (y : G) * (p : G) by simp [mul_assoc]]
      exact congrArg E this⟩
  map_add' a b := by
    refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    exact map_add E _ _
  map_smul' c a := by
    refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    exact map_smul E _ _

@[simp] theorem resInd_apply {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v))
    (f : smoothPart (ind Q σ)) (p : P) :
    (resInd σ H hH τ E hE f).1.1 p = E (f.1.1 (x * (p : G))) := rfl

end Abstract

section Concrete

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def eGPg {m j n : ℕ} (h : m + j = n) : (Σ x, Two (Fin m) (Fin (j + 1)) x) ≃ Fin (n + 1) :=
  two (stdSum (by omega))

def HGPg {m j n : ℕ} (h : m + j = n) : Subgroup (Mir k n) := (parab k (eGPg h)).comap (Mir k n).subtype

def hgpInclg {m j n : ℕ} (h : m + j = n) : HGPg k h →* parab k (eGPg h) where
  toFun g := ⟨((g : Mir k n) : GL (Fin (n + 1)) k), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hgpg_block_mem {m j n : ℕ} (h : m + j = n) (g : HGPg k h) :
    (leviProj k (eGPg h) (hgpInclg k h g) true : GL (Fin (j + 1)) k) ∈ Mir k j := by
  subst h
  exact hgp_block_mem _ _ g

def gpProjg {m j n : ℕ} (h : m + j = n) : HGPg k h →* GL (Fin m) k × Mir k j :=
  MonoidHom.prod ((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) false).comp
      ((leviProj k (eGPg h)).comp (hgpInclg k h)))
    (((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) true).comp
      ((leviProj k (eGPg h)).comp (hgpInclg k h))).codRestrict (Mir k j) (hgpg_block_mem k h))

def wPerm {i t : ℕ} (h : (i + 1) + t = i + t + 1) : Equiv.Perm (Fin (i + t + 1)) :=
  (two (stdSum h)).symm.trans (ePG i t)

def wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) : GL (Fin (i + t + 1)) k where
  val := (1 : Matrix _ _ k).submatrix (wPerm h) id
  inv := (1 : Matrix _ _ k).submatrix id (wPerm h)
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, mul_one]
    exact Matrix.submatrix_one_equiv (wPerm h)
  inv_val := by
    rw [← Matrix.submatrix_mul _ _ _ (wPerm h) _ (wPerm h).bijective, mul_one]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

end Concrete

section Inducing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

abbrev sQ {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (parab k (two (stdSum h))) (⨂[ℂ] x, TwoT V W x) :=
  (twist (piTensor (twoRep π₁ π₂)) (deltaHalf k (Two (Fin r) (Fin t)))).comp (leviProj k (two (stdSum h)))

abbrev tE (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    (⨂[ℂ] x, TwoT V W x) ≃ₗ[ℂ] V ⊗[ℂ] W :=
  Exponents.boolTensorEquiv (X := TwoT V W)

end Inducing

section Row

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_updateRow_one {N : ℕ} (a : Fin N) (y : Fin N → k) :
    ((1 : Matrix (Fin N) (Fin N) k).updateRow a y).det = y a := by
  have h := Matrix.cramer_apply (1 : Matrix (Fin N) (Fin N) k) y a
  rw [Matrix.cramer_one] at h
  have e : ((1 : Matrix (Fin N) (Fin N) k).updateCol a y) = ((1 : Matrix (Fin N) (Fin N) k).updateRow a y)ᵀ := by
    rw [← Matrix.updateCol_transpose, Matrix.transpose_one]
  rw [e, Matrix.det_transpose] at h
  simpa using h.symm

theorem exists_rowSec {N : ℕ} (a : Fin N) : ∃ b : (Fin N → k) → GL (Fin N) k,
    ContinuousAt b (Pi.single a 1) ∧ b (Pi.single a 1) = 1 ∧
      ∀ y : Fin N → k, y a ≠ 0 → (b y : Matrix (Fin N) (Fin N) k) = (1 : Matrix (Fin N) (Fin N) k).updateRow a y := by
  classical
  let M : (Fin N → k) → Matrix (Fin N) (Fin N) k := fun y => (1 : Matrix (Fin N) (Fin N) k).updateRow a y
  have hM : Continuous M := by
    refine continuous_matrix fun c d => ?_
    by_cases h : c = a
    · subst h
      simpa [M] using continuous_apply d
    · simpa [M, Matrix.updateRow_ne h] using continuous_const
  have hdet : ∀ y, (M y).det = y a := fun y => det_updateRow_one a y
  let b : (Fin N → k) → GL (Fin N) k := fun y =>
    if h : y a ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (M y) (by rw [hdet]; exact h) else 1
  have hb : ∀ y : Fin N → k, y a ≠ 0 → (b y : Matrix (Fin N) (Fin N) k) = M y := fun y h => by
    simp only [b, dif_pos h]
    rfl
  have h0 : (Pi.single a 1 : Fin N → k) a ≠ 0 := by simp
  have hne : ∀ᶠ y : Fin N → k in 𝓝 (Pi.single a 1), y a ≠ 0 :=
    (continuous_apply a).continuousAt.eventually_ne h0
  refine ⟨b, ?_, ?_, hb⟩
  · rw [Units.isInducing_embedProduct.continuousAt_iff]
    have h1 : ContinuousAt (fun y => (b y : Matrix (Fin N) (Fin N) k)) (Pi.single a 1) :=
      hM.continuousAt.congr (hne.mono fun y h => (hb y h).symm)
    have h2 : ContinuousAt (fun y => (((b y)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) (Pi.single a 1) := by
      have h3 : ContinuousAt (fun y : Fin N → k => (y a)⁻¹ • (M y).adjugate) (Pi.single a 1) :=
        ((continuous_apply a).continuousAt.inv₀ h0).smul hM.matrix_adjugate.continuousAt
      refine h3.congr (hne.mono fun y h => ?_)
      show (y a)⁻¹ • (M y).adjugate = (((b y)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
      rw [Matrix.coe_units_inv, hb y h, Matrix.inv_def, hdet, Ring.inverse_eq_inv]
    exact h1.prodMk (MulOpposite.continuous_op.continuousAt.comp h2)
  · ext1
    rw [hb _ h0]
    show (1 : Matrix (Fin N) (Fin N) k).updateRow a (Pi.single a 1) = 1
    ext c d
    by_cases h : c = a
    · subst h
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.updateRow_ne h]

end Row

end GlobalTheory.CompanionTheory.BZRes

end
