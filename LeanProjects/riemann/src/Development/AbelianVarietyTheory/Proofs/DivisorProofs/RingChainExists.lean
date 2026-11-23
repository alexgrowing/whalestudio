import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageFiniteProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSubOneSmulMemBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfCompEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectoidLatticeSurjectiveProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSubOneMemJacobson
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LLEquivLieTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccSubOneDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSemilinearCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TeichmullerExtensionOfScalarsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLiftOfReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeNakayamaApproximationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector
open scoped TensorProduct Pointwise ChangeOfRings

namespace GlobalTheory.RingChain.Exist

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat

section Generic

variable {A R : Type} [CommRing A] [CommRing R] {σ : A →+* R} {M N M' N' : Type} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

theorem exists_quot_bij (f : M →ₛₗ[σ] M') (P : Submodule A M) (P' : Submodule R M') (h : ∀ x, x ∈ P ↔ f x ∈ P')
    (hs : ∀ z, ∃ x, z - f x ∈ P') : ∃ Φ : (M ⧸ P) →ₛₗ[σ] M' ⧸ P', Function.Bijective Φ ∧
      ∀ x, Φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := by
  refine ⟨P.mapQ P' f fun x hx => (h x).1 hx, ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun z => ?_⟩, fun _ => rfl⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 ((h x).2 ((Submodule.Quotient.mk_eq_zero _).1 hx))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨x, hx⟩ := hs z
    exact ⟨Submodule.Quotient.mk x, ((Submodule.Quotient.eq _).2 hx).symm⟩

omit [Module A M] in

theorem exists_add_lift (Ψ : N →ₛₗ[σ] N') (hΨ : Function.Bijective Ψ) (f : M →+ N') :
    ∃ ψ : M →+ N, ∀ x, Ψ (ψ x) = f x := by
  choose g hg using fun x => hΨ.2 (f x)
  exact ⟨AddMonoidHom.mk' g fun x y => hΨ.1 (by rw [map_add, hg, hg, hg, map_add]), hg⟩

theorem exists_lin_lift (Ψ : N →ₛₗ[σ] N') (hΨ : Function.Bijective Ψ) (f : M →ₛₗ[σ] N') :
    ∃ ψ : M →ₗ[A] N, ∀ x, Ψ (ψ x) = f x := by
  choose g hg using fun x => hΨ.2 (f x)
  exact ⟨⟨⟨g, fun x y => hΨ.1 (by rw [map_add, hg, hg, hg, map_add])⟩,
    fun a x => hΨ.1 (by rw [map_smulₛₗ, hg, hg, map_smulₛₗ]; rfl)⟩, hg⟩

def res (f : M →ₛₗ[σ] M') (H : Submodule R M') : H.comap f →ₛₗ[σ] H where
  toFun x := ⟨f x.1, x.2⟩
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_smul' _ _ := Subtype.ext (map_smulₛₗ f _ _)

theorem exists_qt_bij (f : M →ₛₗ[σ] M') (H B : Submodule R M') (hB : B ≤ H) (P : Submodule A M) (h : ∀ x, x ∈ P ↔ f x ∈ B)
    (hs : ∀ z, ∃ x, z - f x ∈ B) : ∃ Φ : Qt (H.comap f) P →ₛₗ[σ] Qt H B, Function.Bijective Φ ∧
      ∀ x, Φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (res f H x) :=
  exists_quot_bij (res f H) _ _ (fun x => h x.1) fun z => by
    obtain ⟨x, hx⟩ := hs z.1
    exact ⟨⟨x, by simpa using H.sub_mem z.2 (hB hx)⟩, hx⟩

theorem exists_j_rho {X P Ω : Type} [AddCommGroup X] [Module R X] [AddCommGroup P] [Module R P] [AddCommGroup Ω]
    [Module R Ω] (H B : Submodule R X) (al : P →ₗ[R] X) (hr : LinearMap.range al ≤ H) (pr : H →ₗ[R] Ω)
    (hs : Function.Surjective pr) (hk : ∀ x : H, pr x = 0 ↔ (x : X) ∈ LinearMap.range al) :
    ∃ (j : P →ₗ[R] Qt H B) (ρ : Ω →ₗ[R] Qt H B ⧸ LinearMap.range j),
      (∀ y, j y = Submodule.Quotient.mk ⟨al y, hr ⟨y, rfl⟩⟩) ∧
      (∀ x, ρ (pr x) = Submodule.Quotient.mk (Submodule.Quotient.mk x)) ∧
      ∀ x x' : H, (Submodule.Quotient.mk (Submodule.Quotient.mk x) : Qt H B ⧸ LinearMap.range j) =
        Submodule.Quotient.mk (Submodule.Quotient.mk x') ↔ (x' : X) - x ∈ B ⊔ LinearMap.range al := by
  let j : P →ₗ[R] Qt H B := Submodule.mkQ _ ∘ₗ al.codRestrict H fun y => hr ⟨y, rfl⟩
  let q : H →ₗ[R] Qt H B ⧸ LinearMap.range j := Submodule.mkQ _ ∘ₗ Submodule.mkQ _
  have hq : LinearMap.ker pr ≤ LinearMap.ker q := fun x hx => by
    obtain ⟨y, hy⟩ := (hk x).1 hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y, congrArg Submodule.Quotient.mk (Subtype.ext hy)⟩
  refine ⟨j, (LinearMap.ker pr).liftQ q hq ∘ₗ (pr.quotKerEquivOfSurjective hs).symm.toLinearMap, fun _ => rfl,
    fun x => ?_, fun x x' => ?_⟩
  · have h1 : (pr.quotKerEquivOfSurjective hs).symm (pr x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    exact congrArg ((LinearMap.ker pr).liftQ q hq) h1
  · rw [eq_comm, Submodule.Quotient.eq, ← Submodule.Quotient.mk_sub, Submodule.mem_sup]
    constructor
    · rintro ⟨y, hy⟩
      have h1 : (x' : X) - x - al y ∈ B := (Submodule.Quotient.eq (B.comap H.subtype)).1 hy.symm
      exact ⟨_, h1, _, ⟨y, rfl⟩, sub_add_cancel _ _⟩
    · rintro ⟨u, hu, _, ⟨y, rfl⟩, e⟩
      refine ⟨y, ((Submodule.Quotient.eq _).2 ?_).symm⟩
      change (x' : X) - x - al y ∈ B
      rwa [← e, add_sub_cancel_right]

variable [Algebra A R]

def unitMap (e : R ⊗[A] M ≃ₗ[R] M') : M →ₛₗ[algebraMap A R] M' where
  toFun y := e (1 ⊗ₜ y)
  map_add' x y := by rw [TensorProduct.tmul_add, map_add]
  map_smul' a y := by
    rw [← map_smul, TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, Algebra.smul_def, smul_eq_mul]

theorem pi_modIso {a : A} {g : R} (hg : algebraMap A R a = g) (h : ModIso R a) (n : ℕ) :
    (∀ x, x ∈ baseOf a n ↔ piMap (algebraMap A R) _ x ∈ baseOf g n) ∧
      ∀ z, ∃ x, z - piMap (algebraMap A R) _ x ∈ baseOf g n := by
  subst hg
  refine ⟨fun x => ?_, fun z => ?_⟩
  · simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    refine ⟨fun ⟨y, hy⟩ => ⟨piMap (algebraMap A R) _ y, by rw [← hy, map_smulₛₗ]⟩, fun ⟨y, hy⟩ => ?_⟩
    choose u hu using fun i => h.2 (x i) ⟨y i, (congrFun hy i).symm⟩
    exact ⟨u, funext fun i => (hu i).symm⟩
  · choose x u hu using fun i => h.1 (z i)
    exact ⟨x, (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨u, trivial, funext fun i => (hu i).symm⟩⟩

theorem modIso_of_dvd {q : A} (ec : AdicCompletion (Ideal.span {q}) A ≃+* R)
    (he : ∀ a, ec (algebraMap A _ a) = algebraMap A R a) {a : A} (ha : a ∣ q) : ModIso R a := by
  obtain ⟨t, ht⟩ := ha
  refine ⟨fun r => ?_, fun x ⟨r, hr⟩ => ?_⟩
  · obtain ⟨x, y, hy⟩ := LatDescent.adic_surj A q (ec.symm r)
    have h1 := congrArg ec hy
    rw [ec.apply_symm_apply, map_add, map_mul, he, he] at h1
    exact ⟨x, algebraMap A R t * ec y, by rw [h1, ← mul_assoc, ← map_mul, ← ht]; ring⟩
  · obtain ⟨x', y, hy⟩ := LatDescent.adic_surj A q (ec.symm r)
    obtain ⟨b, hb⟩ := LatDescent.adic_inj A q (x - a * x') (algebraMap A _ a * y) (ec.injective (by
      have h1 := congrArg ec hy
      rw [ec.apply_symm_apply, map_add, map_mul, he, he] at h1
      rw [map_mul, map_mul, he, he, he, map_sub, map_mul, hr, h1]; ring))
    exact ⟨x' + t * b, by rw [mul_add, ← mul_assoc, ← ht, ← hb]; ring⟩

end Generic

section Group

variable {p : ℕ} [Fact p.Prime] (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)
  {A : Type} [CommRing A] [Algebra A S.R]

variable (A) in

abbrev lat (n : ℕ) : Submodule A (Fin G.height → A) := (H D c n).comap (piMap (algebraMap A S.R) _)

variable (A) in

abbrev up (n : ℕ) : lat D c A n →ₛₗ[algebraMap A S.R] H D c n := res _ _

theorem zeta_dvd_theta_xiN (S : CycPerfd p) (n : ℕ) : zeta S.ε (n + 2) - 1 ∣ fontaineTheta S.R p (xiN S 1) := by
  have h1 : fontaineTheta S.R p (xiN S 1) = ∑ i ∈ Finset.range p, zeta S.ε 2 ^ i := by
    simp [xiN, xi, fontaineTheta_teichmuller, zeta]
  have h2 : ∑ i ∈ Finset.range p, zeta S.ε 2 ^ i = (p : S.R) + ∑ i ∈ Finset.range p, (zeta S.ε 2 ^ i - 1) := by simp
  rw [h1, h2]
  exact (FrobQuot.zeta_sub_one_dvd_two S n).trans (dvd_add (FrobQuot.zeta_sub_one_dvd_p S 1)
    (Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one _ i))

variable {π : A} (hπ : algebraMap A S.R π = zeta S.ε 1 - 1) (mπ : ModIso S.R π)

include hπ mπ

theorem exists_qq (n : ℕ) : ∃ Φ : Qt (lat D c A n) (baseOf π G.height) →ₛₗ[algebraMap A S.R] QQ D c n,
    Function.Bijective Φ ∧ ∀ x, Φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (up D c A n x) :=
  exists_qt_bij _ _ _ (base_le_H D c n) _ (pi_modIso hπ mπ _).1 (pi_modIso hπ mπ _).2

theorem exists_ll (n : ℕ) : ∃ Φ : Qt (lat D c A n) (lat D c A (n + 1)) →ₛₗ[algebraMap A S.R] LL D c n,
    Function.Bijective Φ ∧ ∀ x, Φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (up D c A n x) :=
  exists_qt_bij _ _ _ (H_succ_le D c n) _ (fun _ => Iff.rfl) fun z =>
    ((pi_modIso hπ mπ _).2 z).imp fun _ h => base_le_H D c (n + 1) h

theorem exists_psi (mp : ModIso S.R (p : A)) (n : ℕ) :
    ∃ ψ : Qt (lat D c A (n + 1)) (baseOf π G.height) →+ Qt (lat D c A n) (baseOf π G.height), IsFrobLin A p p ψ ∧
      ∀ (x : lat D c A (n + 1)) (y : lat D c A n), ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
        ∃ k ∈ K D c (n + 2), (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ k =
          (zeta S.ε (n + 2) - 1) • toR rfl x.1 ∧
          ∃ y₀, (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ (piMap frobenius _ k) = (zeta S.ε (n + 1) - 1) • y₀ ∧
            toR rfl y.1 - y₀ ∈ base S G.height := by
  obtain ⟨Φ, hΦ, kΦ⟩ := exists_qq D c hπ mπ (n + 1)
  obtain ⟨Ψ, hΨ, kΨ⟩ := exists_qq D c hπ mπ n
  obtain ⟨ψ', h1, h2⟩ := frobenius_quot_T p D S G c n
  obtain ⟨ψ, hψ⟩ := exists_add_lift Ψ hΨ (ψ'.comp Φ.toAddMonoidHom)
  refine ⟨ψ, ?_, fun x y => ?_⟩
  · have h := GlobalTheory.T.frobenius_semilinear_compatible p 1 A S.R mp _ _ _ _ Φ Ψ hΦ hΨ ψ ψ' hψ (by rw [pow_one]; exact h2)
    rwa [pow_one] at h
  have h3 : ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      ψ' (Submodule.Quotient.mk (up D c A _ x)) = Submodule.Quotient.mk (up D c A _ y) := by
    rw [← hΨ.1.eq_iff, hψ, kΨ, ← kΦ]; rfl
  rw [h3]
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := (mem_H D c (n + 1) _).1 (up D c A _ x).2
    obtain ⟨v, hv⟩ := zeta_sub_one_dvd S n
    have e' : (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ (piMap frobenius _ k) =
        (zeta S.ε (n + 1) - 1) • v • piMap (fontaineTheta S.R p) _ (piMap frobenius _ k) := by rw [smul_smul, ← hv]
    rw [h1 k _ ⟨_, (mem_H D c n _).2 ⟨_, hk, e'⟩⟩ hk e e'] at h
    exact ⟨k, hk, e, _, e', (Submodule.Quotient.eq ((base S G.height).comap (H D c n).subtype)).1 h.symm⟩
  · rintro ⟨k, hk, e, y₀, e', h⟩
    rw [h1 k _ ⟨_, (mem_H D c n _).2 ⟨_, hk, e'⟩⟩ hk e e']
    exact ((Submodule.Quotient.eq ((base S G.height).comap (H D c n).subtype)).2 h).symm

variable {Lie : Type} [AddCommGroup Lie] [Module A Lie] (eL : S.R ⊗[A] Lie ≃ₗ[S.R] G.Lie)

set_option maxHeartbeats 800000 in

theorem exists_kappa (mp : ModIso S.R (p : A)) (n : ℕ) :
    ∃ κ : Qt (lat D c A n) (lat D c A (n + 1)) →+ Lie ⧸ (p : A) • (⊤ : Submodule A Lie), IsFrobLin A p (p ^ (n + 1)) κ ∧
      ∀ (x : lat D c A n) (y : Lie), κ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
        ∃ m : D.Cov G, (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ (fun j => (phiInv p S.R)^[n + 1] (coord D c m j)) =
          (zeta S.ε (n + 1) - 1) • toR rfl x.1 ∧ ∃ y₀ : G.Lie, c.alDual y₀ = b D c m ∧
            eL (1 ⊗ₜ y) - y₀ ∈ (p : S.R) • (⊤ : Submodule S.R G.Lie) := by
  obtain ⟨Φ, hΦ, kΦ⟩ := exists_ll D c hπ mπ n
  obtain ⟨q1, q2⟩ := GlobalTheory.T.base_change_nakayama_approximation A S.R p p (map_natCast _ p) mp Lie G.Lie eL
  obtain ⟨Ψ, hΨ, kΨ⟩ := exists_quot_bij (unitMap eL) ((p : A) • ⊤) ((p : S.R) • ⊤) (fun y => ⟨fun h => by
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    rw [map_smulₛₗ, map_natCast]
    exact Submodule.smul_mem_pointwise_smul _ _ _ trivial, q2 y⟩) q1
  obtain ⟨-, lam, h1, h2⟩ := LieTwist.LL_equiv_lie_twist p D S G c n
  obtain ⟨-, ⟨w, hw⟩, -, s, hs⟩ := CycElem.theta_xiN_facts p S n
  obtain ⟨e, he⟩ := h2 s hs
  obtain ⟨u, hu⟩ := b_eq_unit_smul_alDual p D S
  obtain ⟨hb, hinj⟩ := hu G c
  obtain ⟨κ', k1, k2⟩ := GlobalTheory.T.teichmuller_extension_of_scalars p (n + 1) S.R _ u s ⟨w, by rw [hw, mul_comm]⟩ (fun r => by
    obtain ⟨a, rfl⟩ := S.surj r
    exact ⟨_, hs a, (CycElem.theta_xiN_facts p S (n + 1)).1 a⟩) _ _ lam e he
  obtain ⟨κ, hκ⟩ := exists_add_lift Ψ hΨ (κ'.comp Φ.toAddMonoidHom)
  refine ⟨κ, GlobalTheory.T.frobenius_semilinear_compatible p (n + 1) A S.R mp _ _ _ _ Φ Ψ hΦ hΨ κ κ' hκ k2, fun x y => ?_⟩
  have h3 : κ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      κ' (Submodule.Quotient.mk (up D c A _ x)) = Submodule.Quotient.mk (eL (1 ⊗ₜ y)) := by
    rw [← kΦ x]
    exact hΨ.1.eq_iff.symm.trans (Iff.of_eq (congrArg₂ Eq (hκ _) (kΨ y)))
  rw [h3]
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := (mem_H D c n _).1 (up D c A _ x).2
    obtain ⟨m, hm⟩ := (mem_K D c _ k).1 hk
    obtain rfl : (fun j => (phiInv p S.R)^[n + 1] (coord D c m j)) = k := funext hm
    rw [← h1 m _ e, k1] at h
    exact ⟨m, e, _, by rw [hb, map_smul], (Submodule.Quotient.eq _).1 h.symm⟩
  · rintro ⟨m, e, y₀, e', h⟩
    rw [hb, ← map_smul] at e'
    rw [← h1 m (up D c A _ x) e, k1, ← hinj e']
    exact ((Submodule.Quotient.eq _).2 h).symm

theorem exists_j_rho_lat {Om : Type} [AddCommGroup Om] [Module A Om] [Module.Finite A Om] [Module.Projective A Om]
    (eO : S.R ⊗[A] Om ≃ₗ[S.R] G.dual.omega) :
    ∃ (j : Lie →ₗ[A] Qt (lat D c A 0) (baseOf π G.height))
      (ρ : Om →ₗ[A] Qt (lat D c A 0) (baseOf π G.height) ⧸ LinearMap.range j), Function.Surjective ρ ∧
      (∀ (y : Lie) (x : lat D c A 0), j y = Submodule.Quotient.mk x ↔
        toR rfl x.1 - c.alDual (eL (1 ⊗ₜ y)) ∈ base S G.height) ∧
      ∀ (w : Om) (x : lat D c A 0), ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk x) ↔
        ∃ x₀ ∈ H D c 0, (zeta S.ε 1 - 1) • eO (1 ⊗ₜ w) = c.al x₀ ∧
          toR rfl x.1 - x₀ ∈ base S G.height ⊔ LinearMap.range c.alDual := by
  have : Module.Projective S.R G.dual.omega := Module.Projective.of_equiv' eO
  have : Module.Finite S.R G.dual.omega := Module.Finite.equiv eO
  have hrefl : Module.IsReflexive S.R G.dual.omega := inferInstance
  have hreg : IsSMulRegular G.dual.omega (zeta S.ε 1 - 1) := Module.Flat.isSMulRegular_of_isRegular
    ((Commute.isRegular_iff fun _ => Commute.all _ _).2 (isSMulRegular_zeta_sub_one S 0))
  obtain ⟨Φ, hΦ, kΦ⟩ := exists_qq D c hπ mπ 0
  obtain ⟨pr, hs, hal, hk⟩ := OmegaProj.exists_projection p D S G c hrefl
  have hr := (FirstLattice.exact_seq p D S G c hrefl).2.2.1
  obtain ⟨j', ρ', j1, r1, r2⟩ := exists_j_rho (H D c 0) (base S G.height) c.alDual hr pr hs hk
  have kill : ∀ z : QQ D c 0, (zeta S.ε 1 - 1) • z = 0 := fun z => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_base S _).2 ⟨z.1, rfl⟩)
  obtain ⟨j, hj⟩ := exists_lin_lift Φ hΦ (j'.comp (unitMap eL))
  obtain ⟨Ψ, hΨ, kΨ⟩ := exists_quot_bij Φ (LinearMap.range j) (LinearMap.range j') (fun x => ⟨by
    rintro ⟨y, rfl⟩
    exact ⟨_, (hj y).symm⟩, by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.T.base_change_nakayama_approximation A S.R π _ hπ mπ Lie G.Lie eL).1 z
    obtain ⟨t, -, ht⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    refine ⟨y, hΦ.1 ?_⟩
    rw [hj, ← hz, ← sub_add_cancel z (eL (1 ⊗ₜ y)), ← ht, map_add, map_smul, kill, zero_add]
    rfl⟩) fun z => (hΦ.2 z).imp fun x hx => by rw [hx, sub_self]; exact zero_mem _
  obtain ⟨ρ, hρ⟩ := exists_lin_lift Ψ hΨ (ρ'.comp (unitMap eO))
  refine ⟨j, ρ, fun z => ?_, fun y x => ?_, fun w x => ?_⟩
  · obtain ⟨z', hz'⟩ := Submodule.Quotient.mk_surjective _ (Ψ z)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    obtain ⟨w, hw⟩ := (GlobalTheory.T.base_change_nakayama_approximation A S.R π _ hπ mπ Om _ eO).1 (pr x)
    obtain ⟨t, -, ht⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
    obtain ⟨t, rfl⟩ := hs t
    refine ⟨w, hΨ.1 ?_⟩
    rw [hρ, ← hz', ← r1, ← sub_add_cancel (pr x) (eO (1 ⊗ₜ w)), ← ht, map_add, map_smul, r1,
      ← Submodule.Quotient.mk_smul, kill, Submodule.Quotient.mk_zero, zero_add]
    rfl
  · rw [← hΦ.1.eq_iff, hj, kΦ, LinearMap.comp_apply, j1, eq_comm]
    exact Submodule.Quotient.eq _
  · rw [← hΨ.1.eq_iff, hρ, kΨ, kΦ]
    change ρ' (eO (1 ⊗ₜ w)) = _ ↔ _
    constructor
    · intro h
      obtain ⟨x₀, hx⟩ := hs (eO (1 ⊗ₜ w))
      rw [← hx, r1, r2] at h
      exact ⟨x₀, x₀.2, by rw [← hx, hal], h⟩
    · rintro ⟨x₀, hx, e, h⟩
      have h1 : eO (1 ⊗ₜ w) = pr ⟨x₀, hx⟩ := hreg (e.trans (hal ⟨x₀, hx⟩).symm)
      rw [h1, r1, r2]
      exact h

end Group

theorem existsSt : ExistsSt := by
  intro p _ D S G c A _ _ _ _ ec he h o e π γ hπp hγp hπ hγ Lie Om _ _ _ _ _ _ _ _ eL eO
  subst e
  have mπ : ModIso S.R π := modIso_of_dvd ec he hπp
  have mp : ModIso S.R (p : A) := modIso_of_dvd ec he dvd_rfl
  choose ψ ψ1 ψ2 using exists_psi D c hπ mπ mp
  choose κ κ1 κ2 using exists_kappa D c hπ mπ eL mp
  obtain ⟨j, ρ, ρ1, j1, ρ2⟩ := exists_j_rho_lat D c hπ mπ eL eO
  have fp := fun n => LatDescent.preimage_finite_projective p D A S ec he G c n (lat D c A n) fun _ => Iff.rfl
  have : Module.Projective S.R G.Lie := Module.Projective.of_equiv' eL
  refine ⟨{
      L := lat D c A
      finite := fun n => (fp n).1
      projective := fun n => (fp n).2.1
      base_le := fun n x hx => base_le_H D c n (((pi_modIso hπ mπ _).1 x).1 hx)
      succ_le := fun n => Submodule.comap_mono (H_succ_le D c n)
      kill := fun n _ x hx => ?_
      gam := fun n hn x hx => ?_
      lfree := fun n hn => ?_
      j := j, ρ := ρ, ρ_surj := ρ1, ψ := ψ, ψ_lin := fun n _ => ψ1 n, κ := κ, κ_lin := fun n _ => κ1 n },
    hπ, fun _ _ => Iff.rfl, j1, ρ2, fun n _ => ψ2 n, fun n _ => κ2 n⟩
  · obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    obtain ⟨v, hv⟩ := zeta_dvd_theta_xiN S n
    rw [(pi_modIso hπ mπ _).1, map_smulₛₗ, hγ 0 (Nat.zero_le _), zero_add, hv, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (zeta_sub_one_smul_mem_base p D S G c (n + 1) _ hy)
  · obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [Submodule.mem_comap, map_smulₛₗ, hγ n hn.le]
    exact (LieTwist.LL_equiv_lie_twist p D S G c n).1 _ hy
  · obtain ⟨Φ, hΦ, -⟩ := exists_ll D c hπ mπ n
    obtain ⟨-, lam, -, h2⟩ := LieTwist.LL_equiv_lie_twist p D S G c n
    obtain ⟨-, -, -, s, hs⟩ := CycElem.theta_xiN_facts p S n
    obtain ⟨e, he'⟩ := h2 s hs
    exact GlobalTheory.T.projective_lift_of_reduction A S.R (γ n) _ (hγ n hn.le) (modIso_of_dvd ec he (hγp n hn.le)) s _ _ _ Φ hΦ lam e he'

end GlobalTheory.RingChain.Exist

end
