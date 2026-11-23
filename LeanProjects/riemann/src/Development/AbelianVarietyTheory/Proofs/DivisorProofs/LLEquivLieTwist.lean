import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRangeOfCompEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSubOneMemJacobson

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector TensorProduct GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise

namespace GlobalTheory.PerfdLat.LieTwist

theorem mem_ker_smul_top {A R M : Type} [CommRing A] [CommRing R] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] {h : ℕ} (hr : ∀ q, Module.rankAtStalk (R := A) M q = h)
    (u : (Fin h → A) →ₗ[A] M) (w : M →ₗ[A] Fin h → A) {a : A} (ψ : A →+* R) (hψ : Function.Surjective ψ)
    (ha : IsSMulRegular R (ψ a)) (hc : ∀ x, w (u x) = a • x) (m : M) (hm : piMap ψ _ (w m) = 0) :
    m ∈ RingHom.ker ψ • (⊤ : Submodule A M) := by
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
  have h1 : (1 : R) ⊗ₜ[A] m = 0 := hi <| (TensorProduct.piScalarRight A R R (Fin h)).injective <| funext fun j => by
    simp [Algebra.smul_def]
    exact congrFun hm j
  let e := (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A R) hψ).symm
  have h2 := congrArg (e.toLinearMap.rTensor M) h1
  rw [LinearMap.rTensor_tmul, map_zero, AlgEquiv.toLinearMap_apply, map_one] at h2
  exact (LinearMap.ker_tensorProductMk (I := RingHom.ker ψ) (Q := M)).le h2

theorem exists_addEquiv {A R B M L Q : Type} [CommRing A] [CommRing R] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup L] [Module R L] [AddCommGroup Q] [Module R Q] [Module B Q] {θ ψ : A →+* R}
    (hθ : Function.Surjective θ) (hψ : Function.Surjective ψ) (s q : R →+* B) (hq : Function.Surjective q)
    (hs : ∀ a, s (θ a) = q (ψ a)) (hQ : ∀ (r : R) (x : Q), q r • x = r • x)
    (t : M →ₛₗ[θ] L) (ht : Function.Surjective t) (π : M →ₛₗ[ψ] Q) (hπ : Function.Surjective π)
    (lam : L →+ Q) (hl : ∀ m, lam (t m) = π m)
    (hk : ∀ m, π m = 0 → ∃ f, t f = 0 ∧ m - f ∈ RingHom.ker ψ • (⊤ : Submodule A M)) :
    ∃ e : (ModuleCat.extendScalars s).obj (ModuleCat.of R L) ≃+ Q,
      ∀ (r : R) (y : L), e (q r ⊗ₜ[R, s] y) = r • lam y := by
  letI : Module R B := Module.compHom B s
  have hsm : ∀ (a : A) (r : B) (m : M), (s (θ a) * r) ⊗ₜ[R] t m = r ⊗ₜ[R] t (a • m) := fun a r m => by
    rw [map_smulₛₗ]
    exact TensorProduct.smul_tmul (θ a) r (t m)
  let F : B ⊗[R] L →+ Q :=
    TensorProduct.liftAddHom ((smulAddHom B Q).flip.comp lam).flip fun b r y => by
      obtain ⟨a, rfl⟩ := hθ b
      obtain ⟨m, rfl⟩ := ht y
      change (s (θ a) * r) • lam (t m) = r • lam (θ a • t m)
      rw [← map_smulₛₗ t, hl, hl, map_smulₛₗ π, hs, mul_comm, mul_smul, hQ]
  have hF : ∀ (r : R) (y : L), F (q r ⊗ₜ[R] y) = r • lam y := fun r y => hQ r (lam y)
  have hz : ∀ z : B ⊗[R] L, ∃ m, z = (1 : B) ⊗ₜ[R] t m := fun z => by
    induction z with
    | zero => exact ⟨0, by rw [map_zero, tmul_zero]⟩
    | tmul r y =>
      obtain ⟨r, rfl⟩ := hq r
      obtain ⟨a, rfl⟩ := hψ r
      obtain ⟨m, rfl⟩ := ht y
      exact ⟨a • m, by rw [← hsm, mul_one, hs]⟩
    | add x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨m', rfl⟩ := hy
      exact ⟨m + m', by rw [map_add, tmul_add]⟩
  have h1 : ∀ m, F ((1 : B) ⊗ₜ[R] t m) = π m := fun m => by rw [← map_one q, hF, one_smul, hl]
  refine ⟨AddEquiv.ofBijective F ⟨(injective_iff_map_eq_zero _).2 fun z h => ?_, fun x => ?_⟩, hF⟩
  · obtain ⟨m, rfl⟩ := hz z
    obtain ⟨f, hf, hm⟩ := hk m ((h1 m).symm.trans h)
    rw [← sub_zero (t m), ← hf, ← map_sub]
    refine Submodule.smul_induction_on (p := fun x => (1 : B) ⊗ₜ[R] t x = 0) hm (fun a ha m _ => ?_)
      fun x y hx hy => ?_
    · rw [← hsm, hs, show ψ a = 0 from ha, map_zero, zero_mul, zero_tmul]
    · rw [map_add, tmul_add, hx, hy, add_zero]
  · obtain ⟨m, rfl⟩ := hπ x
    exact ⟨_, h1 m⟩

variable {p : ℕ} [Fact p.Prime] (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

abbrev red (n : ℕ) : D.Cov G →ₛₗ[thetaPhiInv S n] (Fin G.height → S.R) :=
  (piMap (thetaPhiInv S n) _).comp (coord D c)

theorem red_of_φ_eq (n : ℕ) {f m : D.Cov G} (h : D.φ S G.dual f = frobenius (xi S.ε) • m) :
    red D c n f = fontaineTheta S.R p (xiN S n) • red D c (n + 1) m := by
  funext j
  have h1 := congrFun (coord_φ D c f) j
  rw [h, map_smul, piMap_apply, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : coord D c f j = xi S.ε * phiInv p S.R (coord D c m j) := Dieudonne.frobenius_injective (by
    rw [map_mul, Dieudonne.frobenius_phiInv, h1])
  change thetaPhiInv S n (coord D c f j) = _ * thetaPhiInv S (n + 1) (coord D c m j)
  rw [h2, map_mul, thetaPhiInv_apply, thetaPhiInv_apply, thetaPhiInv_apply, CycElem.phiInv_iterate_xi,
    Function.iterate_succ_apply]

theorem mem_H_iff (n : ℕ) {v : S.R} (hv : zeta S.ε 1 - 1 = (zeta S.ε (n + 1) - 1) * v) (x : Fin G.height → S.R) :
    x ∈ H D c n ↔ ∃ m, v • red D c (n + 1) m = x := by
  rw [H_eq_map_thetaK D c n hv, thetaK_eq_range]
  exact ⟨fun ⟨_, ⟨m, rfl⟩, h⟩ => ⟨m, h⟩, fun ⟨m, h⟩ => ⟨_, ⟨m, rfl⟩, h⟩⟩

theorem theta_xiN_smul_mem (n : ℕ) (x : Fin G.height → S.R) (hx : x ∈ H D c n) :
    fontaineTheta S.R p (xiN S (n + 1)) • x ∈ H D c (n + 1) := by
  obtain ⟨k, hk, h⟩ := (mem_H D c n x).1 hx
  refine (mem_H D c _ _).2 ⟨k, K_le_succ D c _ hk, ?_⟩
  rw [h, smul_smul, mul_comm, CycElem.theta_xiN_mul]

theorem LL_equiv_lie_twist : ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p) (G : PDivGroup p S.R)
    (c : ConstTate (eps S) G), ∀ n,
    (∀ x ∈ H D c n, fontaineTheta S.R p (xiN S (n + 1)) • x ∈ H D c (n + 1)) ∧
    ∃ lam : G.Lie →+ LL D c n,
      (∀ (m : D.Cov G) (x : H D c n), (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _
          (fun j => (phiInv p S.R)^[n + 1] (coord D c m j)) = (zeta S.ε (n + 1) - 1) • (x : Fin G.height → S.R) →
        lam (D.toLie G m) = Submodule.Quotient.mk x) ∧
      ∀ s : S.R →+* S.R ⧸ Ideal.span {fontaineTheta S.R p (xiN S (n + 1))},
        (∀ a : Ainf p S.R, s (fontaineTheta S.R p a) =
          Ideal.Quotient.mk _ (fontaineTheta S.R p ((phiInv p S.R)^[n + 1] a))) →
        ∃ e : (ModuleCat.extendScalars s).obj (ModuleCat.of S.R G.Lie) ≃+ LL D c n, ∀ (r : S.R) (y : G.Lie),
          e ((Ideal.Quotient.mk _ r : S.R ⧸ Ideal.span {fontaineTheta S.R p (xiN S (n + 1))}) ⊗ₜ[S.R, s] y) =
            r • lam y := by
  intro p _ D S G c n
  refine ⟨theta_xiN_smul_mem D c n, ?_⟩
  obtain ⟨v, hv⟩ := zeta_sub_one_dvd S n
  have hr : IsSMulRegular S.R v := IsSMulRegular.of_mul (a := zeta S.ε (n + 1) - 1) (hv ▸ isSMulRegular_zeta_sub_one S 0)
  have hv' : zeta S.ε 1 - 1 = (zeta S.ε (n + 1 + 1) - 1) * (v * fontaineTheta S.R p (xiN S (n + 1))) := by
    rw [hv, ← CycElem.theta_xiN_mul S (n + 1)]; ring
  let x : D.Cov G →ₛₗ[thetaPhiInv S (n + 1)] H D c n :=
    ((LinearMap.lsmul S.R _ v).comp (red D c (n + 1))).codRestrict _ fun m => (mem_H_iff D c n hv _).2 ⟨m, rfl⟩
  let π : D.Cov G →ₛₗ[thetaPhiInv S (n + 1)] LL D c n := (Submodule.mkQ _).comp x
  have hπ0 : ∀ m, π m = 0 ↔ ∃ m', (v * fontaineTheta S.R p (xiN S (n + 1))) • red D c (n + 1 + 1) m' =
      v • red D c (n + 1) m := fun m =>
    (Submodule.Quotient.mk_eq_zero _).trans (mem_H_iff D c (n + 1) hv' _)
  have hle : (D.toLie G).toAddMonoidHom.ker ≤ π.toAddMonoidHom.ker := fun f hf => by
    obtain ⟨m, hm⟩ := (D.mem_Fil G f).1 hf
    exact (hπ0 f).2 ⟨m, by rw [red_of_φ_eq D c _ hm, mul_smul]⟩
  let lam := (D.toLie G).toAddMonoidHom.liftOfSurjective (D.toLie_surjective G) ⟨π.toAddMonoidHom, hle⟩
  have hl : ∀ m, lam (D.toLie G m) = π m := fun m =>
    AddMonoidHom.liftOfRightInverse_comp_apply (D.toLie G).toAddMonoidHom _ _ _ m
  have hI : Module.IsTorsionBySet S.R (LL D c n) (Ideal.span {fontaineTheta S.R p (xiN S (n + 1))}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact (Submodule.Quotient.mk_eq_zero _ (x := _ • y)).2 (theta_xiN_smul_mem D c n _ y.2)
  letI := hI.module
  refine ⟨lam, fun m y h => (hl m).trans (congrArg Submodule.Quotient.mk (Subtype.ext (funext fun j => ?_))),
    fun s hs => exists_addEquiv S.surj (thetaPhiInv S (n + 1)).surjective s _ Ideal.Quotient.mk_surjective
      (fun a => by rw [hs, thetaPhiInv_apply]) (fun _ _ => rfl) _ (D.toLie_surjective G) π (fun q => ?_) lam hl
      fun m hm => ?_⟩
  · refine isSMulRegular_zeta_sub_one S n (Eq.trans ?_ (congrFun h j))
    rw [hv]
    change _ * (v * thetaPhiInv S (n + 1) (coord D c m j)) = _
    rw [thetaPhiInv_apply, ← mul_assoc]
    rfl
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨m, hm⟩ := (mem_H_iff D c n hv _).1 y.2
    exact ⟨m, congrArg Submodule.Quotient.mk (Subtype.ext hm)⟩
  · obtain ⟨m', h⟩ := (hπ0 m).1 hm
    obtain ⟨f, hf⟩ := D.exists_φ_eq S G.dual m'
    refine ⟨f, (D.mem_Fil G f).2 ⟨m', hf⟩, mem_ker_smul_top (D.rank_eq S G.dual) (inj D c) (coord D c) _
      (thetaPhiInv S (n + 1)).surjective (by rw [thetaPhiInv_mu]; exact isSMulRegular_zeta_sub_one S n)
      (coord_inj D c) _ ?_⟩
    rw [mul_smul, ← red_of_φ_eq D c _ hf] at h
    change red D c (n + 1) (m - f) = 0
    rw [map_sub, sub_eq_zero]
    exact funext fun j => hr (congrFun h j).symm

end GlobalTheory.PerfdLat.LieTwist
