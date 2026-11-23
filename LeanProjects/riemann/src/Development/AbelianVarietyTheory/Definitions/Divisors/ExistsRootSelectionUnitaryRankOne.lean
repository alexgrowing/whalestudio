import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

section Generic

def nrmG {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ : H) : H :=
  (List.map (fun i => (⇑θ)^[i] δ) (List.range r)).prod

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

theorem conj_mul_star (σ : S →+* Sᵐᵒᵖ) (b : S) (x y : Sˣ) (t : Aˣ) (s : A)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t) (hy : (y : S) * b * (σ y).unop = algebraMap A S s * b) :
    ((x * y * x⁻¹ : Sˣ) : S) * (σ ((x * y * x⁻¹ : Sˣ) : S)).unop = algebraMap A S s := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht : algebraMap A S ((t⁻¹ : Aˣ) : A) * algebraMap A S (t : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t⁻¹ : Aˣ) : A) * b := by
    calc ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop
        = algebraMap A S ((t⁻¹ : Aˣ) : A) * (((x⁻¹ : Sˣ) : S) * algebraMap A S (t : A) *
            (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [← Algebra.commutes (t : A), ← mul_assoc, ← mul_assoc, ht, one_mul]
      _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((((x⁻¹ : Sˣ) : S) * x) * b *
            ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)) := by
          rw [← hx]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]
  calc ((x * y * x⁻¹ : Sˣ) : S) * (σ ((x * y * x⁻¹ : Sˣ) : S)).unop
      = x * (y * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ y).unop) * (σ x).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * (x * (y * b * (σ y).unop) * (σ x).unop) := by
        rw [h2]; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
    _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * (algebraMap A S s * (x * b * (σ x).unop)) := by
        rw [hy]; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
    _ = _ := by rw [hx, Algebra.commutes s, ← mul_assoc, ht, one_mul]

end Generic

variable {p : ℕ} [Fact p.Prime]

def sh (G : HTGroup p) (x : G.C) : G.C := (G.star x).unop

def inC (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] : G.C →+* R ⊗[ℚ] G.C :=
  ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] R ⊗[ℚ] G.C) : G.C →+* R ⊗[ℚ] G.C)

def Triv (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) : Prop :=
  (x : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R x).unop = algebraMap R (R ⊗[ℚ] G.C) t

structure Pair (G : HTGroup p) where

  β : G.Cˣ

  γ : G.Cˣ

  c : ℚˣ
  sym : sh G β = β
  sim : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β
  reg : (minpoly G.F (γ : G.C)).natDegree = G.n ∧ (minpoly G.F (γ : G.C)).Separable
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t
  trivR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1

abbrev Gp (G : HTGroup p) : Type := ℚ_[p]ˣ × ((w : Fin G.m) → GL (Fin G.n) (G.Fw w))

abbrev Gr (G : HTGroup p) (r : ℕ) : Type := GHT p G.m G.n r G.Fw

abbrev sigG (G : HTGroup p) (r : ℕ) : Gr G r →* Gr G r := sigHT p G.m G.n r G.Fw

def inclG (G : HTGroup p) (r : ℕ) : Gp G →* Gr G r :=
  ((GeneralLinearGroup.scalar (Fin 1)).comp (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom)).prodMap
    (Pi.monoidHom fun w => (GeneralLinearGroup.map (inclK p (G.Fw w) r).toRingHom).comp (Pi.evalMonoidHom _ w))

def locC (G : HTGroup p) : G.Cˣ × ℚˣ →* Gp G :=
  ((Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom).comp (MonoidHom.snd _ _)).prod
    (Pi.monoidHom fun w => (Units.map (G.rho w).toMonoidHom).comp (MonoidHom.fst _ _))

def Kp0 (G : HTGroup p) : Subgroup (Gp G) := (KHT p G.m G.n 1 G.Fw).comap (inclG G 1)

def regular₂ (G : HTGroup p) (γ : Gp G) : Prop := ∀ w, (γ.2 w).val.charpoly.Separable

def IsNrm (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r) : Prop :=
  nrmG (sigG G r) r δ = z⁻¹ * inclG G r γ * z

def carry (G : HTGroup p) (r : ℕ) (z : Gr G r) : Gp G →* Gr G r :=
  (MulAut.conj z⁻¹).toMonoidHom.comp (inclG G r)

def lorb (G : HTGroup p) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (γ : Gp G) : ℂ :=
  if h : ∃ dz : Gr G r × Gr G r, IsNrm G r γ dz.1 dz.2 then
    GlobalTheory.LKCount.orbC (sigG G r) K ((Subgroup.centralizer {γ} ⊓ Kp0 G).map (carry G r h.choose.2)) h.choose.1 φ
  else 0

def Match (G : HTGroup p) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (K' : Subgroup (Gr G 1))
    (f : Gr G 1 → ℂ) : Prop :=
  ∀ γ : Gp G, regular₂ G γ → lorb G r K φ γ = lorb G 1 K' f γ

def IsTest {H : Type} [Group H] (θ : H →* H) (K₀ K : Subgroup H) (φ : H → ℂ) : Prop :=
  Subgroup.Commensurable K K₀ ∧ K.map θ ≤ K ∧ (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * θ k) = φ g) ∧
    ∃ S : Finset H, ∀ g, φ g ≠ 0 → ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂

namespace Pair

variable {G : HTGroup p}

def pol (P : Pair G) : Polynomial G.F := minpoly G.F (P.γ : G.C)

def Rel (P Q : Pair G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y) ∧ Q.γ = y * P.γ * y⁻¹

def cent (P : Pair G) : Subgroup (G.Cˣ × ℚˣ) where
  carrier := {y | y.1 * P.γ = P.γ * y.1 ∧ (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C y.2 * P.β}
  one_mem' := ⟨by simp, by simp [sh]⟩
  mul_mem' := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · change y * y' * P.γ = P.γ * (y * y')
      change y * P.γ = P.γ * y at h1
      change y' * P.γ = P.γ * y' at h1'
      rw [mul_assoc, h1', ← mul_assoc, h1, mul_assoc]
    · change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
      change (y' : G.C) * P.β * sh G y' = algebraMap ℚ G.C s' * P.β at h2'
      change ((y * y' : G.Cˣ) : G.C) * P.β * sh G ((y * y' : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s * s' : ℚˣ) : ℚ) * P.β
      have e : sh G ((y * y' : G.Cˣ) : G.C) = sh G y' * sh G y := by
        simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
      rw [e, Units.val_mul, Units.val_mul, map_mul]
      calc (y : G.C) * y' * P.β * (sh G y' * sh G y) = y * (y' * P.β * sh G y') * sh G y := by
            simp only [mul_assoc]
        _ = algebraMap ℚ G.C s' * (y * P.β * sh G y) := by
            rw [h2']; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (s' : ℚ)]
  inv_mem' := by
    rintro ⟨y, s⟩ ⟨h1, h2⟩
    change y * P.γ = P.γ * y at h1
    change (y : G.C) * P.β * sh G y = algebraMap ℚ G.C s * P.β at h2
    refine ⟨?_, ?_⟩
    · change y⁻¹ * P.γ = P.γ * y⁻¹
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_inv_cancel_right]
    · change ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * P.β
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      have hs : algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ G.C (s : ℚ) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc ((y⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((y⁻¹ : G.Cˣ) : G.C)
          = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * (((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (s : ℚ) * P.β) *
              sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes ((s⁻¹ : ℚˣ) : ℚ), mul_assoc ((y⁻¹ : G.Cˣ) : G.C) _ (algebraMap ℚ G.C (s : ℚ)), hs, mul_one]
        _ = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * ((((y⁻¹ : G.Cˣ) : G.C) * y) * P.β *
              (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
            rw [← h2]; simp only [mul_assoc]
        _ = _ := by rw [Units.inv_mul, e, one_mul, mul_one]

def self (P : Pair G) : P.cent := ⟨(P.γ, P.c), rfl, P.sim⟩

def toAf (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : P.cent →* G.GAf :=
  MonoidHom.codRestrict
    ((((MulAut.conj x).toMonoidHom.comp (Units.map (inC G (AfP p)).toMonoidHom)).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).comp P.cent.subtype) _ fun y => by
      have h := congrArg (inC G (AfP p)) y.2.2
      rw [map_mul, map_mul, map_mul] at h
      have e1 : inC G (AfP p) (sh G y.1.1) = (starT G.star (AfP p) (inC G (AfP p) y.1.1)).unop :=
        (starT_tmul G.star (AfP p) 1 _).symm
      have e2 : inC G (AfP p) (algebraMap ℚ G.C y.1.2) =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) y.1.2) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
      rw [e1, e2] at h
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) P.β) x
        (Units.map (inC G (AfP p)).toMonoidHom y.1.1) t _ hx h

def atP (P : Pair G) : Gp G := locC G (P.γ, P.c)

def toQr (P : Pair G) (r : ℕ) (z : Gr G r) : P.cent →* Gr G r :=
  ((carry G r z).comp (locC G)).comp P.cent.subtype

def termAt (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r) : ℂ :=
  GlobalTheory.LKCount.pointSum (P.toAf x t hx) (P.toQr r z) (sigG G r) Kf K (P.toAf x t hx P.self) δ f φ

def term (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  if h : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 then
    P.termAt Kf f r K φ P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec
      h.choose.1 h.choose.2
  else 0

def Mark (P : Pair G) (μ : ℂ) : Prop :=
  ∃ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 ∧ ∃ x : Fin G.n → ℂ,
    G.psi v P.γ *ᵥ x = μ • x ∧ 0 < (star x ⬝ᵥ ((G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re

end Pair

def Cls (G : HTGroup p) : Type := Quot (Pair.Rel (G := G))

def IsSel (G : HTGroup p) (sel : Polynomial G.F → ℂ) : Prop :=
  ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ P : Polynomial G.F, P.Monic → P.natDegree = G.n →
    P.eval₂ v.embedding (sel P) = 0

def markedSum (G : HTGroup p) (wt sel : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if (Quot.out q).Mark (sel (Quot.out q).pol) then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

def fullSum (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if ∃ μ, (Quot.out q).Mark μ then wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

def IsSimple (G : HTGroup p) : Prop := (∀ x : G.C, x ≠ 0 → IsUnit x) ∧ G.a = 1

def Compare : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), IsSimple G → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (r : ℕ), 0 < r → ∀ (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
      IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      Match G r K φ K' f' →
      (G.n : ℂ) * markedSum G wt sel L.K.toSubgroup f r K φ = fullSum G wt L.K.toSubgroup f 1 K' f'

end GlobalTheory.LKMid

namespace GlobalTheory.LKMid

section Inhabitants

variable {p : ℕ} [Fact p.Prime]

def scal (G : HTGroup p) (a : G.Fˣ) : G.Cˣ := Units.map (algebraMap G.F G.C).toMonoidHom a

theorem scal_val (G : HTGroup p) (a : G.Fˣ) : ((scal G a : G.Cˣ) : G.C) = algebraMap G.F G.C a := rfl

theorem sh_algebraMap (G : HTGroup p) (x : G.F) :
    sh G (algebraMap G.F G.C x) = algebraMap G.F G.C (IsCMField.complexConj G.F x) := G.star_F x

theorem sh_one_eq (G : HTGroup p) : sh G 1 = 1 := by simp [sh]

def Pair.ofScalar (G : HTGroup p) (hn : G.n = 1) (a : G.Fˣ) (c : ℚˣ)
    (h : (a : G.F) * IsCMField.complexConj G.F a = algebraMap ℚ G.F c) : Pair G where
  β := 1
  γ := scal G a
  c := c
  sym := sh_one_eq G
  sim := by
    rw [scal_val, Units.val_one, mul_one, mul_one, sh_algebraMap, ← map_mul, h]
    exact (IsScalarTower.algebraMap_apply ℚ G.F G.C _).symm
  reg := by
    rw [scal_val, minpoly.eq_X_sub_C, hn]
    exact ⟨Polynomial.natDegree_X_sub_C _, Polynomial.separable_X_sub_C⟩
  trivAf := ⟨1, 1, by simp [Triv, inC]⟩
  trivR := ⟨1, by simp [Triv, inC]⟩

theorem Pair.ofScalar_pol (G : HTGroup p) (hn : G.n = 1) (a : G.Fˣ) (c : ℚˣ)
    (h : (a : G.F) * IsCMField.complexConj G.F a = algebraMap ℚ G.F c) :
    (Pair.ofScalar G hn a c h).pol = Polynomial.X - Polynomial.C (a : G.F) := by
  show minpoly G.F (algebraMap G.F G.C (a : G.F)) = _
  exact minpoly.eq_X_sub_C _ _

theorem exists_isSel (G : HTGroup p) (h : G.a ≤ 1) : ∃ sel, IsSel G sel := by
  by_cases h0 : ∃ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1
  · obtain ⟨v0, hv0⟩ := h0
    refine ⟨fun P => if hP : 0 < (P.map v0.embedding).degree then (Complex.exists_root hP).choose else 0, ?_⟩
    intro v hv P hm hd
    have h1 : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := h
    have hvv : v = v0 := congrArg Subtype.val (Fintype.card_le_one_iff.1 h1 ⟨v, hv⟩ ⟨v0, hv0⟩)
    subst hvv
    have hP : 0 < (P.map v.embedding).degree := by
      rw [Polynomial.degree_eq_natDegree (hm.map _).ne_zero, hm.natDegree_map, hd]
      exact_mod_cast G.n_pos
    simp only [dif_pos hP]
    rw [← Polynomial.eval_map]
    exact (Complex.exists_root hP).choose_spec
  · exact ⟨0, fun v hv _ _ _ => absurd ⟨v, hv⟩ h0⟩

theorem exists_isSel_of_isSimple (G : HTGroup p) (h : IsSimple G) : ∃ sel, IsSel G sel :=
  exists_isSel G h.2.le

theorem isTest_indicator {H : Type} [Group H] (θ : H →* H) (K : Subgroup H) (hK : K.map θ ≤ K) :
    IsTest θ K K (Set.indicator (K : Set H) 1) := by
  refine ⟨Subgroup.Commensurable.refl K, hK, fun k hk g => ?_, {1}, fun g hg => ?_⟩
  · have hθ : θ k ∈ K := hK ⟨k, hk, rfl⟩
    by_cases hg : g ∈ K
    · have h' : k⁻¹ * g * θ k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk) hg) hθ
      simp [Set.indicator_apply, hg, h']
    · have h' : k⁻¹ * g * θ k ∉ K := fun h => hg (by
        have e : g = k * (k⁻¹ * g * θ k) * (θ k)⁻¹ := by group
        rw [e]; exact K.mul_mem (K.mul_mem hk h) (K.inv_mem hθ))
      simp [Set.indicator_apply, hg, h']
  · have hgK : g ∈ K := by
      by_contra hn; exact hg (by simp [Set.indicator_apply, hn])
    exact ⟨1, Finset.mem_singleton_self _, 1, K.one_mem, g, hgK, by simp⟩

theorem match_refl (G : HTGroup p) (K : Subgroup (Gr G 1)) (φ : Gr G 1 → ℂ) : Match G 1 K φ K φ :=
  fun _ _ => rfl

end Inhabitants

namespace Example

open GlobalTheory.LKTrip.Example

abbrev gi : QI := IsCyclotomicExtension.zeta 4 ℚ QI

theorem conj_gi : IsCMField.complexConj QI gi = -gi := by
  let φ : QI →+* ℂ := Classical.arbitrary _
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  have h3 : φ gi ^ 2 = Complex.I ^ 2 := by
    rw [← map_pow, zeta_sq, map_neg, map_one, Complex.I_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h <;> rw [h] <;> simp

theorem two_add_gi_ne_zero : (2 + gi : QI) ≠ 0 := by
  intro h
  have e : gi = -2 := by linear_combination h
  have h2 : gi ^ 2 = -1 := zeta_sq
  rw [e] at h2
  norm_num at h2

def a21 : QIˣ := Units.mk0 (2 + gi) two_add_gi_ne_zero

theorem norm_gaussian_element_eq_five : ((a21 : QI)) * IsCMField.complexConj QI a21 = algebraMap ℚ QI ((Units.mk0 (5 : ℚ) (by norm_num) : ℚˣ) : ℚ) := by
  show (2 + gi) * IsCMField.complexConj QI (2 + gi) = algebraMap ℚ QI 5
  rw [map_add, conj_gi, map_ofNat, map_ofNat]
  linear_combination (-1 : QI) * zeta_sq

def exPair : Pair (ex 1 one_ne_zero) :=
  Pair.ofScalar (ex 1 one_ne_zero) rfl a21 (Units.mk0 5 (by norm_num)) norm_gaussian_element_eq_five

theorem isSimple_unitaryRankOne : IsSimple (ex 1 one_ne_zero) := by
  refine ⟨fun x hx => ?_, a_ex_one⟩
  have key : ∀ y : Matrix (Fin 1) (Fin 1) QI, y ≠ 0 → IsUnit y := by
    intro y hy
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
    refine isUnit_iff_ne_zero.2 fun h => hy ?_
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, h]
    rfl
  exact key x hx

theorem exPair_mark : ∃ μ : ℂ, exPair.Mark μ := by
  have ha : 0 < (ex 1 one_ne_zero).a := by rw [a_ex_one]; exact one_pos
  obtain ⟨⟨v, hv⟩⟩ := Fintype.card_pos_iff.1 ha
  refine ⟨v.embedding (show (ex 1 one_ne_zero).F from (2 + gi : QI)), v, hv, fun _ => 1, ?_, ?_⟩
  · show (ex 1 one_ne_zero).psi v (algebraMap (ex 1 one_ne_zero).F (ex 1 one_ne_zero).C (show (ex 1 one_ne_zero).F from (2 + gi : QI))) *ᵥ (fun _ => (1 : ℂ)) =
      v.embedding (show (ex 1 one_ne_zero).F from (2 + gi : QI)) • (fun _ => (1 : ℂ))
    rw [(ex 1 one_ne_zero).psi_F v, Matrix.scalar_apply]
    ext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  · show 0 < (star (fun _ => (1 : ℂ)) ⬝ᵥ (((ex 1 one_ne_zero).gram v *
      (ex 1 one_ne_zero).psi v (((1 : (ex 1 one_ne_zero).Cˣ)⁻¹ : (ex 1 one_ne_zero).Cˣ) : (ex 1 one_ne_zero).C)) *ᵥ
      (fun _ => (1 : ℂ)))).re
    rw [inv_one, Units.val_one, map_one, Matrix.mul_one]
    show 0 < (star (fun _ : Fin 1 => (1 : ℂ)) ⬝ᵥ (gramAt (Hc 1) (v.embedding : QI →+* ℂ) *ᵥ fun _ : Fin 1 => (1 : ℂ))).re
    simp [gramAt, Hc, dotProduct, Matrix.mulVec]
    have h1 : ((v.embedding : QI →+* ℂ) 1).re = 1 := by rw [map_one]; rfl
    exact lt_of_lt_of_eq zero_lt_one h1.symm

theorem exists_rootSelection_unitaryRankOne : ∃ sel, IsSel (ex 1 one_ne_zero) sel := exists_isSel_of_isSimple _ isSimple_unitaryRankOne

theorem exists_cls_mark : ∃ q : Cls (ex 1 one_ne_zero), ∃ P : Pair (ex 1 one_ne_zero), Quot.mk _ P = q ∧ ∃ μ, P.Mark μ :=
  ⟨Quot.mk _ exPair, exPair, rfl, exPair_mark⟩

example : ((exPair.c : ℚˣ) : ℚ) = 5 := rfl

example : exPair.pol = Polynomial.X - Polynomial.C (2 + gi) :=
  Pair.ofScalar_pol (ex 1 one_ne_zero) rfl a21 _ norm_gaussian_element_eq_five

example : Nonempty (ex 1 one_ne_zero).Level := GlobalTheory.LKTrip.LevelExists.level_exists 5 (ex 1 one_ne_zero)

end Example

end GlobalTheory.LKMid
