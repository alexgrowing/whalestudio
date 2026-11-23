import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRangeOfCompEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfCompEqSmul
open CategoryTheory WittVector GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PerfdLat.OmegaProj

variable {p : ℕ} [Fact p.Prime]

theorem eq_zero_of_theta_phiInv_all (S : CycPerfd p) (a : Ainf p S.R)
    (h : ∀ n, fontaineTheta S.R p ((phiInv p S.R)^[n + 1] a) = 0) : a = 0 := by
  have hc : ∀ (n : ℕ) (a : Ainf p S.R), ((phiInv p S.R)^[n] a).coeff 0 =
      (_root_.frobeniusEquiv (PreTilt S.R p) p).symm^[n] (a.coeff 0) := fun n a => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
  have hp : ∀ (n : ℕ) (a : Ainf p S.R), (phiInv p S.R)^[n] (a * p) = (phiInv p S.R)^[n] a * p := fun n a => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_natCast]
  have key : ∀ (k : ℕ) (a : Ainf p S.R), (∀ n, fontaineTheta S.R p ((phiInv p S.R)^[n + 1] a) = 0) →
      a ∈ Ideal.span {(p : Ainf p S.R) ^ k} := fun k => by
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a h
      have h0 : (_root_.frobeniusEquiv (PreTilt S.R p) p).symm (a.coeff 0) = 0 := Perfection.ext fun n => by
        have h1 := mk_fontaineTheta ((phiInv p S.R)^[n + 1] a)
        rw [h, map_zero, hc, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add,
          ← PreTilt.coeff_frobeniusEquiv_symm] at h1
        exact h1.symm.trans (map_zero _).symm
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1
        ((mem_span_p_iff_coeff_zero_eq_zero a).2 ((map_eq_zero_iff _ (RingEquiv.injective _)).1 h0))
      rw [pow_succ, ← Ideal.span_singleton_mul_span_singleton]
      refine Ideal.mul_mem_mul (ih b fun n => S.reg ?_) (Ideal.mem_span_singleton_self _)
      have h1 := h n
      rw [hp, map_mul, map_natCast] at h1
      simpa [mul_comm] using h1
  ext m
  simpa using (mem_span_p_pow_iff_le_coeff_eq_zero a (m + 1)).1 (key _ a h) m m.lt_succ_self

theorem mu_regular (S : CycPerfd p) : IsSMulRegular (Ainf p S.R) (Sandwich.mu S.ε) :=
  IsSMulRegular.of_right_eq_zero_of_smul fun a ha => eq_zero_of_theta_phiInv_all S a fun n => by
    have h : ∀ n, muN S n * (phiInv p S.R)^[n] a = 0 := fun n => by
      induction n with
      | zero => exact ha
      | succ n ih => rw [Function.iterate_succ_apply', ← phiInv_muN, ← map_mul, ih, map_zero]
    have h1 := congrArg (fontaineTheta S.R p) (h (n + 1))
    rw [map_mul, theta_muN, map_zero] at h1
    exact (isSMulRegular_zeta_sub_one S n).right_eq_zero_of_smul h1

theorem xi_mul_muN_one (S : CycPerfd p) : xi S.ε * muN S 1 = Sandwich.mu S.ε := xiN_mul_muN S 0

theorem frobenius_mu (S : CycPerfd p) :
    frobenius (Sandwich.mu S.ε) = Sandwich.mu S.ε * frobenius (xi S.ε) := by
  have h := congrArg frobenius (xiN_mul_muN S 0)
  rw [map_mul, frobenius_muN] at h
  change frobenius (muN S 0) = muN S 0 * frobenius (xiN S 0)
  rw [← h, mul_comm]

theorem xi_regular (S : CycPerfd p) : IsSMulRegular (Ainf p S.R) (xi S.ε) :=
  IsSMulRegular.of_mul (a := muN S 1) (by rw [mul_comm, xi_mul_muN_one]; exact mu_regular S)

theorem frobenius_xi_regular (S : CycPerfd p) : IsSMulRegular (Ainf p S.R) (frobenius (xi S.ε)) := by
  have h : IsSMulRegular (Ainf p S.R) (frobenius (Sandwich.mu S.ε)) := fun a b hab => by
    have h1 := congrArg (phiInv p S.R) hab
    simp only [smul_eq_mul, map_mul, Dieudonne.phiInv_frobenius] at h1
    have h2 := mu_regular S h1
    simpa [Dieudonne.frobenius_phiInv] using congrArg frobenius h2
  rw [frobenius_mu] at h
  exact IsSMulRegular.of_mul h

theorem theta_mu (S : CycPerfd p) : fontaineTheta S.R p (Sandwich.mu S.ε) = 0 := by
  have h := theta_muN S 0
  rw [S.zeta_zero, sub_self] at h
  exact h

theorem theta_muN_one (S : CycPerfd p) : fontaineTheta S.R p (muN S 1) = zeta S.ε 1 - 1 := theta_muN S 1

theorem exists_smul_dual {B Y : Type} [CommRing B] [AddCommGroup Y] [Module B Y] {a : B} (ha : IsSMulRegular B a)
    (f : Module.Dual B Y) (hf : ∀ y, ∃ r, a * r = f y) : ∃ g : Module.Dual B Y, ∀ y, a * g y = f y := by
  choose g hg using hf
  refine ⟨{ toFun := g, map_add' := fun x y => ha ?_, map_smul' := fun r x => ha ?_ }, hg⟩
  · change a * g (x + y) = a * (g x + g y)
    rw [hg, mul_add, hg, hg, map_add]
  · change a * g (r • x) = a * (r * g x)
    rw [hg, map_smul, ← hg, smul_eq_mul]
    ring

theorem exists_smul_dual₂ {B X Y : Type} [CommRing B] [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    {a : B} (ha : IsSMulRegular B a) (F : X →ₗ[B] Module.Dual B Y) (hF : ∀ x y, ∃ r, a * r = F x y) :
    ∃ Ψ : X →ₗ[B] Module.Dual B Y, ∀ x y, a * Ψ x y = F x y := by
  choose g hg using hF
  refine ⟨LinearMap.mk₂ B g (fun x₁ x₂ y => ha ?_) (fun r x y => ha ?_) (fun x y₁ y₂ => ha ?_)
    (fun r x y => ha ?_), hg⟩
  · change a * g (x₁ + x₂) y = a * (g x₁ y + g x₂ y)
    rw [hg, mul_add, hg, hg, map_add, LinearMap.add_apply]
  · change a * g (r • x) y = a * (r * g x y)
    rw [hg, map_smul, LinearMap.smul_apply, ← hg, smul_eq_mul]
    ring
  · change a * g x (y₁ + y₂) = a * (g x y₁ + g x y₂)
    rw [hg, mul_add, hg, hg, map_add]
  · change a * g x (r • y) = a * (r * g x y)
    rw [hg, map_smul, ← hg, smul_eq_mul]
    ring

variable (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

theorem exists_du_eq (l : Module.Dual (Ainf p S.R) (D.Cov G.dual)) : ∃ f : D.Cov G, ∀ y, D.du S G.dual y f = l y :=
  ⟨(Module.evalEquiv (Ainf p S.R) (D.Cov G)).symm (l ∘ₗ (D.du S G.dual).symm.toLinearMap), fun y => by
    have h := LinearMap.congr_fun ((Module.evalEquiv (Ainf p S.R) (D.Cov G)).apply_symm_apply
      (l ∘ₗ (D.du S G.dual).symm.toLinearMap)) (D.du S G.dual y)
    simpa using h⟩

theorem eq_zero_of_du (f : D.Cov G) (h : ∀ y, D.du S G.dual y f = 0) : f = 0 := by
  apply (Module.evalEquiv (Ainf p S.R) (D.Cov G)).injective
  rw [map_zero]
  refine LinearMap.ext fun l => ?_
  obtain ⟨y, rfl⟩ := (D.du S G.dual).surjective l
  simpa using h y

theorem coord_injective : Function.Injective (coord D c) := by
  refine injective_of_comp_eq_smul (funext fun q => ?_) (inj D c) (coord D c) (mu_regular S) (coord_inj D c)
  haveI := q.nontrivial
  rw [D.rank_eq S G.dual q, Module.rankAtStalk_eq_finrank_of_free]
  simp

theorem inj_coord (m : D.Cov G) : inj D c (coord D c m) = Sandwich.mu S.ε • m :=
  coord_injective D c (by rw [coord_inj, map_smul])

theorem du_inj_single (m' : D.Cov G.dual) (i : Fin G.height) :
    D.du S G.dual m' (D.map S G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) (D.l S)) = coord D c.dual m' i := by
  rw [← D.du_map]
  have h : dualHom G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) = constHom G.dual.dual (c.dual.t' i) :=
    dualHom_charHom G.dual _
  rw [h, coord_apply]
  set y : D.M S (const p S.R) := D.map S (const p S.R) G.dual.dual (constHom G.dual.dual (c.dual.t' i)) m'
  change D.du S (PDivGroup.mu p S.R) y (D.l S) = D.eCoord S y
  conv_lhs => rw [← D.eCoord_smul y]
  rw [map_smul, LinearMap.smul_apply, D.du_e_l, smul_eq_mul, mul_one]

theorem sum_coord_mul (m : D.Cov G) (m' : D.Cov G.dual) :
    ∑ j, coord D c m j * coord D c.dual m' j = Sandwich.mu S.ε * D.du S G.dual m' m := by
  have h := congrArg (D.du S G.dual m') (inj_coord D c m)
  rw [map_smul, smul_eq_mul, inj_apply, map_sum] at h
  simp only [map_smul, smul_eq_mul, du_inj_single D c] at h
  exact h

theorem du_φ (c : ConstTate (eps S) G) (m : D.Cov G) (x : D.Cov G.dual) :
    D.du S G.dual (D.φ S G.dual.dual x) (D.φ S G.dual m) = frobenius (xi S.ε) * frobenius (D.du S G.dual x m) := by
  apply mu_regular S
  simp only [smul_eq_mul]
  rw [← sum_coord_mul D c, coord_φ, coord_φ D c.dual]
  simp only [piMap_apply, ← map_mul, ← map_sum]
  rw [sum_coord_mul D c, map_mul, frobenius_mu]
  simp only [map_mul]
  ring

end GlobalTheory.PerfdLat.OmegaProj

namespace GlobalTheory.PerfdLat.OmegaProj

variable {p : ℕ} [Fact p.Prime] (D : PrismData p) {S : CycPerfd p} {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

theorem sum_mul_coord_dual (k : Fin G.height → Ainf p S.R) (m : D.Cov G) (hk : piMap frobenius _ k = coord D c m)
    (m' : D.Cov G.dual) : ∑ j, k j * coord D c.dual m' j =
      muN S 1 * phiInv p S.R (D.du S G.dual (D.φ S G.dual.dual m') m) := by
  apply Dieudonne.frobenius_injective
  rw [map_sum, map_mul, frobenius_muN S 0, Dieudonne.frobenius_phiInv]
  have h : ∀ j, frobenius (k j * coord D c.dual m' j) = coord D c m j * coord D c.dual (D.φ S G.dual.dual m') j :=
    fun j => by rw [map_mul, ← piMap_apply frobenius _ k j, hk, coord_φ, piMap_apply]
  simp only [h]
  exact sum_coord_mul D c m _

theorem apply_al (v : G.dual.Lie) (x : Fin G.height → S.R) : v (c.al x) = ∑ j, x j * c.dual.alDual v j := by
  rw [c.al_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]; rfl

theorem unit_mul_apply_al (u : (S.R)ˣ) (hb : ∀ m', b D c.dual m' = (u : S.R) • c.dual.alDual (D.toLie G.dual m'))
    (m' : D.Cov G.dual) (x : Fin G.height → S.R) :
    (u : S.R) * (D.toLie G.dual m') (c.al x) = ∑ j, x j * fontaineTheta S.R p (coord D c.dual m' j) := by
  rw [apply_al, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (hb m') j
  rw [b_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  ring

end GlobalTheory.PerfdLat.OmegaProj

open GlobalTheory.PerfdLat.OmegaProj in

theorem GlobalTheory.PerfdLat.OmegaProj.exists_projection (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p) (G : PDivGroup p S.R)
    (c : ConstTate (eps S) G) (hω : Module.IsReflexive S.R G.dual.omega) :
    ∃ pr : H D c 0 →ₗ[S.R] G.dual.omega, Function.Surjective pr ∧
      (∀ x : H D c 0, (zeta S.ε 1 - 1) • pr x = c.al (x : Fin G.height → S.R)) ∧
      ∀ x : H D c 0, pr x = 0 ↔ (x : Fin G.height → S.R) ∈ LinearMap.range c.alDual := by
  obtain ⟨u, hu⟩ := GlobalTheory.PerfdLat.b_eq_unit_smul_alDual p D S
  have hb := (hu G c).1
  have hb' := (hu G.dual c.dual).1
  have hπ : IsSMulRegular S.R (zeta S.ε 1 - 1) := by simpa using isSMulRegular_zeta_sub_one S 0
  let F : H D c 0 →ₗ[S.R] Module.Dual S.R G.dual.Lie :=
    (Module.Dual.eval S.R G.dual.omega) ∘ₗ c.al ∘ₗ (H D c 0).subtype
  have hF : ∀ x y, F x y = y (c.al (x : Fin G.height → S.R)) := fun _ _ => rfl
  have hH : ∀ x : H D c 0, ∃ (k : Fin G.height → Ainf p S.R) (m : D.Cov G),
      piMap frobenius _ k = coord D c m ∧ (x : Fin G.height → S.R) = piMap (fontaineTheta S.R p) _ k := by
    intro x
    have hx : (x : Fin G.height → S.R) ∈ thetaK D c 1 := by rw [← H_zero]; exact x.2
    obtain ⟨k, hk, hx⟩ := hx
    obtain ⟨m, hm⟩ := (mem_K_succ D c 0 k).1 hk
    exact ⟨k, m, hm.symm, hx.symm⟩
  have hval : ∀ (k : Fin G.height → Ainf p S.R) (m : D.Cov G), piMap frobenius _ k = coord D c m →
      ∀ m' : D.Cov G.dual, (u : S.R) * (D.toLie G.dual m') (c.al (piMap (fontaineTheta S.R p) _ k)) =
        (zeta S.ε 1 - 1) * fontaineTheta S.R p (phiInv p S.R (D.du S G.dual (D.φ S G.dual.dual m') m)) := by
    intro k m hk m'
    rw [unit_mul_apply_al D c u hb', ← theta_muN_one, ← map_mul, ← sum_mul_coord_dual D c k m hk, map_sum]
    simp only [piMap_apply, map_mul]
  have hdiv : ∀ x y, ∃ r, (zeta S.ε 1 - 1) * r = F x y := by
    intro x y
    obtain ⟨k, m, hk, hx⟩ := hH x
    obtain ⟨m', rfl⟩ := D.toLie_surjective G.dual y
    refine ⟨(↑u⁻¹ : S.R) * fontaineTheta S.R p (phiInv p S.R (D.du S G.dual (D.φ S G.dual.dual m') m)), ?_⟩
    rw [hF, hx, mul_left_comm, ← hval k m hk m', ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨Ψ, hΨ⟩ := exists_smul_dual₂ hπ F hdiv
  let e := Module.evalEquiv S.R G.dual.omega
  have he : ∀ w y, e w y = y w := fun _ _ => rfl
  have hΨ0 : ∀ x, Ψ x = 0 ↔ ∀ y : G.dual.Lie, y (c.al (x : Fin G.height → S.R)) = 0 := fun x =>
    ⟨fun h y => by rw [← hF, ← hΨ, h, LinearMap.zero_apply, mul_zero],
      fun h => LinearMap.ext fun y => hπ.right_eq_zero_of_smul (by rw [smul_eq_mul, hΨ, hF, h])⟩
  refine ⟨e.symm.toLinearMap ∘ₗ Ψ, ?_, ?_, ?_⟩
  · intro w
    let γ : D.Cov G.dual →ₛₗ[fontaineTheta S.R p] S.R := (u : S.R) • ((e w).comp (D.toLie G.dual))
    have hγ : ∀ m', γ m' = (u : S.R) * e w (D.toLie G.dual m') := fun _ => rfl
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (D.projective S G.dual.dual)
    choose a ha using fun q : D.Cov G.dual => S.surj (γ q)
    let l : Module.Dual (Ainf p S.R) (D.Cov G.dual) := Finsupp.linearCombination (Ainf p S.R) a ∘ₗ s
    have hl : ∀ m', fontaineTheta S.R p (l m') = γ m' := by
      intro m'
      have h1 : Finsupp.linearCombination (Ainf p S.R) id (s m') = m' := LinearMap.congr_fun hs m'
      conv_rhs => rw [← h1]
      simp only [l, LinearMap.comp_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
        map_smulₛₗ, smul_eq_mul, map_mul, ha, id]
    obtain ⟨f, hf⟩ := exists_du_eq D l
    have hdivf : ∀ y, ∃ r, frobenius (xi S.ε) * r = (D.du S G.dual).toLinearMap.flip (D.φ S G.dual f) y := by
      intro y
      obtain ⟨x', hx'⟩ := D.exists_φ_eq S G.dual.dual y
      have hfil : D.toLie G.dual x' = 0 := (D.mem_Fil G.dual x').2 ⟨y, hx'⟩
      have h1 : l x' ∈ Ideal.span {xi S.ε} := by
        rw [← S.ker_eq, RingHom.mem_ker, hl, hγ, hfil, map_zero, mul_zero]
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
      refine ⟨frobenius r, frobenius_xi_regular S ?_⟩
      change frobenius (xi S.ε) • (frobenius (xi S.ε) * frobenius r) =
        frobenius (xi S.ε) • D.du S G.dual y (D.φ S G.dual f)
      rw [← LinearMap.smul_apply, ← map_smul, ← hx', du_φ D c, hf, ← hr, map_mul, smul_eq_mul]
      ring
    obtain ⟨g2, hg2⟩ := exists_smul_dual (frobenius_xi_regular S) _ hdivf
    obtain ⟨m, hm⟩ := exists_du_eq D g2
    have hφf : D.φ S G.dual f = frobenius (xi S.ε) • m := by
      rw [← sub_eq_zero]
      refine eq_zero_of_du D _ fun y => ?_
      rw [map_sub, map_smul, hm, smul_eq_mul, hg2]
      exact sub_self _
    let k : Fin G.height → Ainf p S.R := piMap (phiInv p S.R) _ (coord D c m)
    have hk : piMap frobenius _ k = coord D c m := funext fun j => Dieudonne.frobenius_phiInv _
    let x : H D c 0 := ⟨piMap (fontaineTheta S.R p) _ k, by
      rw [H_zero]; exact ⟨k, (mem_K_succ D c 0 k).2 ⟨m, hk.symm⟩, rfl⟩⟩
    have hΨx : Ψ x = e w := by
      refine LinearMap.ext fun y => hπ ?_
      obtain ⟨m', rfl⟩ := D.toLie_surjective G.dual y
      simp only [smul_eq_mul]
      rw [hΨ, hF]
      apply u.isUnit.mul_left_cancel
      have h5 : D.du S G.dual (D.φ S G.dual.dual m') m = frobenius (D.du S G.dual m' f) := by
        refine frobenius_xi_regular S ?_
        change frobenius (xi S.ε) * D.du S G.dual (D.φ S G.dual.dual m') m =
          frobenius (xi S.ε) * frobenius (D.du S G.dual m' f)
        rw [← smul_eq_mul _ (D.du S G.dual _ m), ← map_smul, ← hφf, du_φ D c]
      have h6 := hval k m hk m'
      change (u : S.R) * (D.toLie G.dual m') (c.al (piMap (fontaineTheta S.R p) _ k)) = _
      rw [h6, h5, Dieudonne.phiInv_frobenius, hf, hl, hγ]
      ring
    refine ⟨x, ?_⟩
    rw [LinearMap.comp_apply, hΨx]
    exact e.symm_apply_apply w
  · intro x
    apply e.injective
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, e.apply_symm_apply]
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.smul_apply, smul_eq_mul, hΨ, hF, he]
  · intro x
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, hΨ0]
    constructor
    · intro h0
      obtain ⟨k, m, hk, hx⟩ := hH x
      have hθ : ∀ m' : D.Cov G.dual,
          fontaineTheta S.R p (phiInv p S.R (D.du S G.dual (D.φ S G.dual.dual m') m)) = 0 := by
        intro m'
        have h1 := hval k m hk m'
        rw [← hx, h0, mul_zero] at h1
        exact hπ.right_eq_zero_of_smul h1.symm
      let l1 : Module.Dual (Ainf p S.R) (D.Cov G.dual) :=
        { toFun := fun m' => phiInv p S.R (D.du S G.dual (D.φ S G.dual.dual m') m)
          map_add' := fun a b => by simp only [map_add, LinearMap.add_apply]
          map_smul' := fun a b => by
            simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, Dieudonne.phiInv_frobenius,
              RingHom.id_apply] }
      obtain ⟨l2, hl2⟩ := exists_smul_dual (xi_regular S) l1 fun m' => by
        have h1 : phiInv p S.R (D.du S G.dual (D.φ S G.dual.dual m') m) ∈ Ideal.span {xi S.ε} := by
          rw [← S.ker_eq]; exact hθ m'
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
        exact ⟨r, by rw [mul_comm]; exact hr⟩
      obtain ⟨n, hn⟩ := exists_du_eq D l2
      have hm : m = D.φ S G.dual n := by
        rw [← sub_eq_zero]
        refine eq_zero_of_du D _ fun y => (frobenius_xi_regular S).right_eq_zero_of_smul ?_
        obtain ⟨x', hx'⟩ := D.exists_φ_eq S G.dual.dual y
        rw [← LinearMap.smul_apply, ← map_smul, ← hx', map_sub, du_φ D c, hn]
        have h2 : D.du S G.dual (D.φ S G.dual.dual x') m = frobenius (xi S.ε * l2 x') := by
          rw [hl2]; exact (Dieudonne.frobenius_phiInv _).symm
        rw [h2, map_mul, sub_self]
      have hk' : k = coord D c n := by
        funext j
        apply Dieudonne.frobenius_injective
        have h3 := congrFun hk j
        rw [hm, coord_φ] at h3
        simpa using h3
      refine ⟨(u : S.R) • D.toLie G n, ?_⟩
      rw [map_smul, ← hb, hx, hk']
      rfl
    · rintro ⟨w, hw⟩ y
      obtain ⟨n, rfl⟩ := D.toLie_surjective G w
      obtain ⟨m', rfl⟩ := D.toLie_surjective G.dual y
      have h1 := unit_mul_apply_al D c u hb' m' (x : Fin G.height → S.R)
      have h3 : ∀ j, (u : S.R) * (x : Fin G.height → S.R) j = fontaineTheta S.R p (coord D c n j) := fun j => by
        rw [← b_apply, hb, Pi.smul_apply, smul_eq_mul, hw]
      have h2 : (u : S.R) * ∑ j, (x : Fin G.height → S.R) j * fontaineTheta S.R p (coord D c.dual m' j) = 0 := by
        rw [Finset.mul_sum]
        simp only [← mul_assoc, h3, ← map_mul]
        rw [← map_sum, sum_coord_mul D c, map_mul, theta_mu, zero_mul]
      rw [← h1] at h2
      exact u.isUnit.mul_right_eq_zero.1 (u.isUnit.mul_right_eq_zero.1 h2)
