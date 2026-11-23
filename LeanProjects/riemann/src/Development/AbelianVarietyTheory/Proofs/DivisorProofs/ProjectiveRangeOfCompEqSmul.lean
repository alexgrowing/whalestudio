import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector TensorProduct

namespace GlobalTheory.PerfdLat

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published
open scoped Pointwise

theorem injective_of_comp_eq_smul {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Flat R M] [Module.Finite R N] [Module.Flat R N]
    (hr : Module.rankAtStalk (R := R) M = Module.rankAtStalk N) (u : N →ₗ[R] M) (w : M →ₗ[R] N) {a : R}
    (ha : IsSMulRegular R a) (h : ∀ x, w (u x) = a • x) : Function.Injective w := by
  let B := Localization.Away a
  have hc : w ∘ₗ u = a • LinearMap.id := LinearMap.ext h
  have hs : Function.Surjective (w.baseChange B) := fun y => by
    obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := B) a
    refine ⟨u.baseChange B ((v⁻¹ : Bˣ) • y), ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc, LinearMap.baseChange_smul, LinearMap.baseChange_id,
      LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul B a, ← hv, Units.smul_def, smul_smul, Units.mul_inv,
      one_smul]
  have hb := Module.bijective_of_surjective_of_rankAtStalk_eq hs fun q _ => by
    rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_baseChange, hr]
  refine (injective_iff_map_eq_zero _).2 fun m hm => ?_
  have h1 : TensorProduct.mk R B M 1 m = 0 := hb.1 (by simp [hm])
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a) _).1 h1
  have h2 : IsSMulRegular M a := Module.Flat.isSMulRegular_of_isRegular
    ((Commute.isRegular_iff (Commute.all a)).2 (isLeftRegular_iff.2 ha))
  exact (h2.pow k) (hk.trans (smul_zero _).symm)

theorem projective_range_of_comp_eq_smul {A R M : Type} [CommRing A] [CommRing R] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] {h : ℕ} (hr : ∀ q, Module.rankAtStalk (R := A) M q = h)
    (u : (Fin h → A) →ₗ[A] M) (w : M →ₗ[A] Fin h → A) {a : A} (ψ : A →+* R) [RingHomSurjective ψ]
    (ha : IsSMulRegular R (ψ a)) (hc : ∀ x, w (u x) = a • x) :
    Module.Projective R (LinearMap.range ((piMap ψ _).comp w)) ∧
      Module.Finite R (LinearMap.range ((piMap ψ _).comp w)) := by
  letI := ψ.toAlgebra
  have hi : Function.Injective (w.baseChange R) := by
    refine injective_of_comp_eq_smul (funext fun q => ?_) (u.baseChange R) _ ha fun x => ?_
    · haveI := (PrimeSpectrum.comap (algebraMap A R) q).nontrivial
      rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_baseChange, hr, Module.rankAtStalk_eq_finrank_of_free]
      simp
    · rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, show w ∘ₗ u = a • LinearMap.id from LinearMap.ext hc,
        LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply,
        ← algebraMap_smul R a]
      rfl
  let F := (TensorProduct.piScalarRight A R R (Fin h)).toLinearMap ∘ₗ w.baseChange R
  have hF : ∀ r m, F (r ⊗ₜ m) = r • piMap ψ _ (w m) := fun r m => funext fun j => by
    simp [F, Algebra.smul_def, mul_comm]
    rfl
  have he : LinearMap.range F = LinearMap.range ((piMap ψ _).comp w) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      induction x with
      | zero => simp
      | tmul r m => rw [hF]; exact Submodule.smul_mem _ _ ⟨m, rfl⟩
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rintro _ ⟨m, rfl⟩
      exact ⟨1 ⊗ₜ m, (hF 1 m).trans (one_smul _ _)⟩
  have e := (LinearEquiv.ofInjective F ((TensorProduct.piScalarRight A R R (Fin h)).injective.comp hi)).trans
    (LinearEquiv.ofEq _ _ he)
  exact ⟨.of_equiv e, .equiv e⟩

variable {p : ℕ} [Fact p.Prime]

def thetaPhiInv (S : CycPerfd p) (n : ℕ) : Ainf p S.R →+* S.R := (fontaineTheta S.R p).comp (phiInv p S.R ^ n)

theorem thetaPhiInv_apply (S : CycPerfd p) (n : ℕ) (a : Ainf p S.R) :
    thetaPhiInv S n a = fontaineTheta S.R p ((phiInv p S.R)^[n] a) := by
  rw [thetaPhiInv, RingHom.comp_apply, RingHom.coe_pow]

instance thetaPhiInv_surjective (S : CycPerfd p) (n : ℕ) : RingHomSurjective (thetaPhiInv S n) :=
  ⟨fun x => by
    obtain ⟨a, rfl⟩ := S.surj x
    obtain ⟨b, rfl⟩ := (Function.RightInverse.surjective (Dieudonne.phiInv_frobenius (p := p) (O := S.R))).iterate n a
    exact ⟨b, thetaPhiInv_apply S n b⟩⟩

theorem thetaPhiInv_mu (S : CycPerfd p) (n : ℕ) : thetaPhiInv S n (Sandwich.mu S.ε) = zeta S.ε n - 1 := by
  rw [thetaPhiInv_apply, ← theta_muN]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiInv_muN]

variable (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

theorem thetaK_eq_range (n : ℕ) : thetaK D c n = LinearMap.range ((piMap (thetaPhiInv S n) _).comp (coord D c)) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨m, hm⟩ := (mem_K D c n k).1 hk
    exact ⟨m, funext fun j => (thetaPhiInv_apply S n _).trans (congrArg _ (hm j))⟩
  · rintro ⟨m, rfl⟩
    exact ⟨_, (mem_K D c n _).2 ⟨m, fun _ => rfl⟩, funext fun j => (thetaPhiInv_apply S n _).symm⟩

theorem projective_thetaK (n : ℕ) :
    Module.Projective S.R (thetaK D c (n + 1)) ∧ Module.Finite S.R (thetaK D c (n + 1)) := by
  rw [thetaK_eq_range]
  exact projective_range_of_comp_eq_smul (D.rank_eq S G.dual) (inj D c) (coord D c) _
    (by rw [thetaPhiInv_mu]; exact isSMulRegular_zeta_sub_one S n) (coord_inj D c)

theorem H_eq_map_thetaK (n : ℕ) {v : S.R} (hv : zeta S.ε 1 - 1 = (zeta S.ε (n + 1) - 1) * v) :
    H D c n = (thetaK D c (n + 1)).map (LinearMap.lsmul S.R _ v) := by
  ext x
  rw [mem_H, hv]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨_, ⟨k, hk, rfl⟩, funext fun j => isSMulRegular_zeta_sub_one S n ((mul_smul ..).symm.trans (congrFun h j))⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, mul_smul ..⟩

theorem projective_finite_H (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p) (G : PDivGroup p S.R)
    (c : ConstTate (eps S) G) (n : ℕ) : Module.Projective S.R (H D c n) ∧ Module.Finite S.R (H D c n) := by
  obtain ⟨v, hv⟩ := zeta_sub_one_dvd S n
  have hr : IsSMulRegular S.R v := IsSMulRegular.of_mul (a := zeta S.ε (n + 1) - 1) (hv ▸ isSMulRegular_zeta_sub_one S 0)
  obtain ⟨h1, h2⟩ := projective_thetaK D c n
  have e := Submodule.equivMapOfInjective (LinearMap.lsmul S.R (Fin G.height → S.R) v)
    (fun x y h => funext fun j => hr (congrFun h j)) (thetaK D c (n + 1))
  rw [H_eq_map_thetaK D c n hv]
  exact ⟨.of_equiv e, .equiv e⟩

end GlobalTheory.PerfdLat
