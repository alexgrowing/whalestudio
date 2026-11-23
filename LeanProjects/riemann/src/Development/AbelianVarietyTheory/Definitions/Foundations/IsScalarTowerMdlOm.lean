import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.ZetaB

open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.NeedB GlobalTheory.KEdge

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def tInv (l N R : ℕ) : ZMod N := ((l : ZMod N) ^ R)⁻¹

def uIdx (l N R : ℕ) (x : ZMod N) : Fin 2 → ℚ := ![1 / (l : ℚ) ^ R, ((x * tInv l N R).val : ℚ) / N]

def vIdx (l N R : ℕ) : Fin 2 → ℚ := ![0, 1 / (l : ℚ) ^ R + ((tInv l N R).val : ℚ) / N]

def uIdxMu (l N R : ℕ) (x : ZMod N) : Fin 2 → ℚ := ![1 / (l : ℚ) ^ R + ((x * tInv l N R).val : ℚ) / N, 0]

def vIdxMu (l N R : ℕ) : Fin 2 → ℚ := ![((tInv l N R).val : ℚ) / N, 1 / (l : ℚ) ^ R]

def atN (X : Tower Ω ε) (N : ℕ) (f : X.K) : X.K := X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f

def topLev (N M' : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma M'

def cycFix (Ω : Type) [Field Ω] [Algebra ℚ Ω] (M : ℕ) : Subgroup (Ω ≃ₐ[ℚ] Ω) where
  carrier := {s | ∀ z : Ω, z ^ M = 1 → s z = z}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb z hz
    simp only [Set.mem_setOf_eq] at *
    rw [AlgEquiv.mul_apply, hb z hz, ha z hz]
  inv_mem' := by
    intro a ha z hz
    simp only [Set.mem_setOf_eq] at *
    show a.symm z = z
    rw [AlgEquiv.symm_apply_eq]
    exact (ha z hz).symm

abbrev Om (X : Tower Ω ε) : Type := AlgebraicClosure X.K

attribute [local instance] algMdl

theorem isScalarTower_mdl_om (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    @IsScalarTower (mdl X Γ' S) (lev X Γ') (Om X) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_mdl_om

open Classical in

def rootOf {L : Type*} [Field L] (k : ℕ) (a : L) : L := if h : ∃ b : L, b ^ k = a then h.choose else 0

open Classical in

def kumHom {F L : Type*} [Field F] [Field L] [Algebra F L] (N : ℕ) (ζ θ : L) : (L ≃ₐ[F] L) →* Multiplicative (ZMod N) :=
  if h : ∀ g g' : L ≃ₐ[F] L, kum (N := N) ζ θ (g * g') = kum ζ θ g + kum ζ θ g' then
    { toFun := fun g => Multiplicative.ofAdd (kum (N := N) ζ θ g)
      map_one' := by
        have h1 := h 1 1
        rw [mul_one] at h1
        have h0 : kum (N := N) ζ θ (1 : L ≃ₐ[F] L) = 0 := by
          have := congrArg (fun t => t - kum (N := N) ζ θ (1 : L ≃ₐ[F] L)) h1
          simpa using this.symm
        rw [h0]; rfl
      map_mul' := fun g g' => by rw [h g g']; rfl }
  else 1

abbrev topR (r n : ℕ) : ℕ := r + n

abbrev topG (l N m r n : ℕ) : Subgroup SL(2, ℤ) := topLev N (m * l ^ (r + n))

abbrev topK (X : Tower Ω ε) (l N m r n : ℕ) : Subfield X.K := lev X (topG l N m r n)

abbrev topF (X : Tower Ω ε) (l N m r n : ℕ) : Subfield X.K :=
  mdl X (topG l N m r n) (cycFix Ω (m * l ^ (r + n)))

def zetaOm (X : Tower Ω ε) (l n : ℕ) : Om X := algebraMap Ω (Om X) (eOm ε (1 / (l : ℚ) ^ n))

def uTop (X : Tower Ω ε) (l N r n c : ℕ) (x : ZMod N) : X.K := atN X N (siegel X c (uIdxMu l N (r + n) x))

def vTop (X : Tower Ω ε) (l N r n d : ℕ) : X.K := atN X N (siegel X d (vIdxMu l N (r + n)))

def kapU (X : Tower Ω ε) (l N m r n c : ℕ) (x : ZMod N) : (Om X ≃ₐ[topF X l N m r n] Om X) →* Multiplicative (ZMod (l ^ n)) :=
  kumHom (l ^ n) (zetaOm X l n) (rootOf (l ^ n) (algebraMap X.K (Om X) (uTop X l N r n c x)))

def kapV (X : Tower Ω ε) (l N m r n d : ℕ) : (Om X ≃ₐ[topF X l N m r n] Om X) →* Multiplicative (ZMod (l ^ n)) :=
  kumHom (l ^ n) (zetaOm X l n) (rootOf (l ^ n) (algebraMap X.K (Om X) (vTop X l N r n d)))

open Classical in

def etaTop (X : Tower Ω ε) (l N m r n c d : ℕ) (x : ZMod N) : (Om X ≃ₐ[topF X l N m r n] Om X) → ZMod (l ^ n) :=
  if h : ∃ η : (Om X ≃ₐ[topF X l N m r n] Om X) → ZMod (l ^ n),
      IsLocallyConstant (fun g : geo (topF X l N m r n) (topK X l N m r n) (Om X) => η g) ∧
      CobOn (geo (topF X l N m r n) (topK X l N m r n) (Om X)) (kapU X l N m r n c x) (kapV X l N m r n d) η ∧
      ∀ B : ValuationSubring (Om X), (∀ a : Ω, algebraMap Ω (Om X) a ∈ B) → algebraMap X.K (Om X) X.jK ∈ B →
        ∀ g ∈ geo (topF X l N m r n) (topK X l N m r n) (Om X), Inert B g → η g = 0
  then h.choose else 0

def wTop (X : Tower Ω ε) (l N m r n c d : ℕ) (x : ZMod N) (σ : Om X ≃ₐ[topF X l N m r n] Om X) :
    topK X l N m r n :=
  topW (F := topF X l N m r n) (K := topK X l N m r n) (Ω := Om X) (zetaOm X l n) (kapU X l N m r n c x)
    (kapV X l N m r n d) (etaTop X l N m r n c d x) σ⁻¹

open Classical in

def unitOf (X : Tower Ω ε) (a : X.K) : X.Kˣ := if h : a = 0 then 1 else Units.mk0 a h

def clsHat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.K) : X.Khat l :=
  AdicCompletion.of (idl l) (X.Kl l) ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul (unitOf X a))

def secF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) (a : X.K) : X.Fn l :=
  fun u => (u 0) ^ w • clsHat X l a

def cR (l N : ℕ) (r₀ : ZMod l) : ℤ := (N : ℤ) * ((-r₀ * (N : ZMod l)⁻¹).val : ℤ)

def gR (l N : ℕ) (r₀ : ZMod l) : SL(2, ℤ) :=
  ⟨!![1, 0; cR l N r₀, 1], by simp [Matrix.det_fin_two]⟩

abbrev TopCos (l N m r n : ℕ) : Type :=
  Quotient (QuotientGroup.rightRel ((topG l N m r n).subgroupOf (Gam N l)))

def push (X : Tower Ω ε) (l N m r n : ℕ) [Fact l.Prime] (b : X.Fn l) : X.Fn l :=
  ∑ r₀ : (ZMod l)ˣ, ∑ᶠ q : TopCos l N m r n,
    X.act l (((gR l N (r₀ : ZMod l) * ((Quotient.out q : Gam N l) : SL(2, ℤ)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) b

open Classical in

def liftF (X : Tower Ω ε) (F : Subfield X.K) (s : Ω ≃ₐ[ℚ] Ω) : Om X ≃ₐ[F] Om X :=
  if h : ∀ a : F, IsAlgClosure.equivOfEquiv (Om X) (Om X) (X.gal s) (algebraMap F (Om X) a) = algebraMap F (Om X) a then
    AlgEquiv.ofRingEquiv h
  else 1

def clsGam (X : Tower Ω ε) (l N m r n w c d : ℕ) [Fact l.Prime] (x : ZMod N)
    (τ : Om X ≃ₐ[topF X l N m r n] Om X) : X.Fn l :=
  push X l N m r n (secF X l w ((wTop X l N m r n c d x τ : topK X l N m r n) : X.K))

open Classical in

def shap {G V U : Type*} [Group G] [AddCommMonoid V] [Group U] (H : Subgroup G) (χ : G →* U) (act : G → V → V) (z : G → V)
    (s : G) (x : U) : V :=
  ∑ᶠ (q : G ⧸ H) (_ : χ (Quotient.out q) = x),
    act (Quotient.out q) (z ((Quotient.out q)⁻¹ * s * Quotient.out (QuotientGroup.mk (s⁻¹ * Quotient.out q) : G ⧸ H)))

def zetaBχ (X : Tower Ω ε) (l N m r n w c d : ℕ) [Fact l.Prime] (x : ZMod N) {U : Type*} [Group U]
    (χ : Formalism.ConjugateSelfDual.G ℚ Ω →* U) :
    Formalism.ConjugateSelfDual.G ℚ Ω → U → X.Fn l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Fn l))) :=
  fun s x' => Submodule.Quotient.mk
    (shap (cycFix Ω (m * l ^ (r + n))) χ (fun g b => X.galB l g b)
      (fun t => clsGam X l N m r n w c d x (liftF X (topF X l N m r n) t)) s x')

def zetaB (X : Tower Ω ε) (l N m r n w c d : ℕ) [Fact l.Prime] (x : ZMod N) :
    Formalism.ConjugateSelfDual.G ℚ Ω → (ZMod (l ^ r))ˣ → X.Fn l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Fn l))) :=
  zetaBχ X l N m r n w c d x (ReciprocityTheory.Gal.cycMod ℚ Ω l r)

theorem cR_mod (l N : ℕ) [Fact l.Prime] (hN : (N : ZMod l) ≠ 0) (r₀ : ZMod l) : ((cR l N r₀ : ℤ) : ZMod l) = -r₀ := by
  simp only [cR, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [mul_comm (-r₀), ← mul_assoc, mul_inv_cancel₀ hN, one_mul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.eval_clsHat (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n
        (_root_.GlobalTheory.ZetaB.clsHat X l a) =
      X.cls l n (_root_.GlobalTheory.ZetaB.unitOf X a) := by
  unfold _root_.GlobalTheory.ZetaB.clsHat
  rw [AdicCompletion.eval_of]
  rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.unitOf_val (X : _root_.GlobalTheory.KZ.Tower Ω ε) {a : X.K}
    (ha : a ≠ 0) : ((_root_.GlobalTheory.ZetaB.unitOf X a : (X.K)ˣ) : X.K) = a := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dif_neg ha]
  rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.unitOf_zero (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    _root_.GlobalTheory.ZetaB.unitOf X 0 = 1 := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dif_pos rfl]

theorem vecMul_gR (l N : ℕ) [Fact l.Prime] (hN : (N : ZMod l) ≠ 0) (r₀ : ZMod l) :
    ![-r₀, -1] ᵥ* (((gR l N r₀ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod l)) = ![0, -1] := by
  funext i
  fin_cases i <;> simp [gR, Matrix.vecMul, dotProduct, Fin.sum_univ_two, cR_mod l N hN]

example : tInv 3 5 1 = 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [tInv, pow_one]
  exact inv_eq_of_mul_eq_one_right (by decide +revert)

example : uIdxMu 3 5 1 1 = ![11 / 15, 0] ∧ vIdxMu 3 5 1 = ![2 / 5, 1 / 3] := by
  have h : tInv 3 5 1 = 2 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [tInv, pow_one]
    exact inv_eq_of_mul_eq_one_right (by decide +revert)
  have h2 : (2 : ZMod 5).val = 2 := rfl
  unfold uIdxMu vIdxMu
  rw [h, one_mul, h2]
  constructor <;> norm_num

example : cR 3 5 1 = 5 := by
  have h : (-1 * ((5 : ℕ) : ZMod 3)⁻¹) = 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [inv_eq_of_mul_eq_one_right (show ((5 : ℕ) : ZMod 3) * 2 = 1 by decide +revert)]
    decide +revert
  rw [cR, h]
  rfl

example : ((gR 3 5 1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = cR 3 5 1 := by
  simp [gR]

end GlobalTheory.ZetaB
