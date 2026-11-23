import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BaseChangeClauseInhabited

set_option autoImplicit false

open CategoryTheory WittVector GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise

namespace GlobalTheory.PerfdLat.LatticeBaseChange

variable {p : ℕ} [Fact p.Prime]

theorem eq_zero_of_theta_phiInv (S : CycPerfd p) (a : Ainf p S.R)
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

theorem isSMulRegular_mu (S : CycPerfd p) : IsSMulRegular (Ainf p S.R) (Sandwich.mu S.ε) :=
  IsSMulRegular.of_right_eq_zero_of_smul fun a ha => eq_zero_of_theta_phiInv S a fun n => by
    have h : ∀ n, muN S n * (phiInv p S.R)^[n] a = 0 := fun n => by
      induction n with
      | zero => exact ha
      | succ n ih => rw [Function.iterate_succ_apply', ← phiInv_muN, ← map_mul, ih, map_zero]
    have h1 := congrArg (fontaineTheta S.R p) (h (n + 1))
    rw [map_mul, theta_muN, map_zero] at h1
    exact (isSMulRegular_zeta_sub_one S n).right_eq_zero_of_smul h1

theorem constHom_comp {O : Type} [CommRing O] {G H : PDivGroup p O} (t : G.Tate) (f : G ⟶ H) :
    constHom G t ≫ f = constHom H (tateMap G H O f t) := by
  rw [← LinearEquiv.symm_apply_eq, constHom_symm_apply, tateMap_comp, tateMap_constHom]

theorem constHom_bcTate {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O'] {G : PDivGroup p O} (t : G.Tate) :
    constHom _ (bcTate O' (constGen p O)) ≫ baseChangeMap O' (constHom G t) = constHom _ (bcTate O' t) := by
  rw [constHom_comp, tateMap_bcTate, tateMap_constHom]

variable (D : PrismData p) {S S' : CycPerfd p} [Algebra S.R S'.R] {α : Ainf p S.R →+* Ainf p S'.R}

theorem map_mu (h : S.Over S' α) : α (Sandwich.mu S.ε) = Sandwich.mu S'.ε :=
  (map_sub α (teichmuller p S.ε) 1).trans (by rw [h.2.2, map_one]; rfl)

theorem map_phiInv (h : S.Over S' α) (n : ℕ) (a : Ainf p S.R) :
    α ((phiInv p S.R)^[n] a) = (phiInv p S'.R)^[n] (α a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact Dieudonne.frobenius_injective (by rw [← h.2.1, Dieudonne.frobenius_phiInv, Dieudonne.frobenius_phiInv])

theorem tateMap_eps (h : S.Over S' α) (j : PDivGroup.mu p S'.R ⟶ (PDivGroup.mu p S.R).baseChange S'.R)
    (hj : ∀ n, j.app n (1 ⊗ₜ AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1) :
    tateMap _ _ S'.R j (eps S') = bcTate S'.R (eps S) :=
  TateOver.ext (funext fun n => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => by
    change (eps S').pt n (j.app n (1 ⊗ₜ a)) = 1 * algebraMap S.R S'.R ((eps S).pt n a)
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy, mul_add]
    | single k c =>
      have e : (AddMonoidAlgebra.single k c : AddMonoidAlgebra S.R (ZMod (p ^ n))) = c • PDiv.muT S.R _ ^ k.val := by
        rw [PDiv.muT_pow, ZMod.natCast_zmod_val]; simp
      have e1 : ((1 : S'.R) ⊗ₜ[S.R] (c • PDiv.muT S.R (p ^ n) ^ k.val)) =
          algebraMap S.R S'.R c • ((1 : S'.R) ⊗ₜ[S.R] PDiv.muT S.R (p ^ n)) ^ k.val := by
        rw [Algebra.TensorProduct.tmul_pow, one_pow, algebraMap_smul, TensorProduct.tmul_smul]
      have e2 : (eps S').pt n (j.app n ((1 : S'.R) ⊗ₜ[S.R] PDiv.muT S.R (p ^ n))) =
          algebraMap S.R S'.R ((eps S).pt n (PDiv.muT S.R (p ^ n))) :=
        (congrArg ((eps S').pt n) (hj n)).trans (muRoot_eps_of_over h n)
      have e3 := congrArg (fun x => (eps S').pt n (j.app n x)) e1
      rw [e]
      refine e3.trans ?_
      rw [map_smul, map_smul, map_pow, map_pow, e2, one_mul, ← map_pow, smul_eq_mul, ← map_mul]
      exact congrArg _ (((map_smul ((eps S).pt n) c _).trans (congrArg _ (map_pow _ _ _))).symm)))

theorem exists_bc (h : S.Over S' α) (G : PDivGroup p S.R) (c : ConstTate (eps S) G) :
    ∃ bc : D.Cov G →ₛₗ[α] D.Cov (G.baseChange S'.R), Submodule.span (Ainf p S'.R) (Set.range bc) = ⊤ ∧
      ∀ m j, coord D (c.baseChange S'.R (muRoot_eps_of_over h)) (bc m) j = α (coord D c m j) := by
  obtain ⟨bc, h1, h2, h3⟩ := D.baseChange S S' α h
  obtain ⟨j, hj⟩ := CycPerfd.Model.exists_muCompare (p := p) S.R S'.R
  have he : D.map S' _ _ (constHom _ (bcTate S'.R (constGen p S.R))) (bc _ (D.e S)) = D.e S' := by
    rw [← D.eCoord_smul (D.map S' _ _ _ _)]
    suffices hs : D.eCoord S' (D.map S' _ _ (constHom _ (bcTate S'.R (constGen p S.R))) (bc _ (D.e S))) = 1 by
      rw [hs, one_smul]
    apply isSMulRegular_mu S'
    have h4 := congrArg (D.map S' _ _ (constHom _ (bcTate S'.R (constGen p S.R))))
      (h2 _ _ (constHom _ (eps S)) (D.l S))
    rw [← LinearMap.comp_apply (D.map S' _ _ _) (D.map S' _ _ _), ← D.map_comp, constHom_bcTate, ← tateMap_eps h j hj,
      ← constHom_comp, D.map_comp, LinearMap.comp_apply, h3 j hj, constHom_eps, constHom_eps, D.map_eps, D.map_eps,
      map_smulₛₗ, map_smul, map_mu h] at h4
    have h5 := congrArg (D.eCoord S') h4
    rw [map_smul, D.eCoord_smul_e] at h5
    exact h5.trans (mul_one _).symm
  refine ⟨(D.map S' _ _ (dualBaseChange S'.R G).hom).comp (bc G.dual), ?_, fun m i => ?_⟩
  · rw [LinearMap.coe_comp, Set.range_comp, ← Submodule.map_span, (h1 _).1, Submodule.map_top, LinearMap.range_eq_top]
    intro x
    refine ⟨D.map S' _ _ (dualBaseChange S'.R G).inv x, ?_⟩
    rw [← LinearMap.comp_apply, ← D.map_comp, Iso.hom_inv_id, D.map_id, LinearMap.id_apply]
  · rw [coord_apply, LinearMap.comp_apply, ← LinearMap.comp_apply (D.map S' _ _ _) (D.map S' _ _ _), ← D.map_comp,
      constHom_comp]
    change D.eCoord S' (D.map S' _ _ (constHom _ (tateMap _ _ S'.R (dualBaseChange S'.R G).hom
      (bcChar S'.R (c.t' i)))) _) = _
    rw [tateMap_dualBaseChange, ← constHom_bcTate, D.map_comp, LinearMap.comp_apply, ← h2, coord_apply,
      ← D.eCoord_smul (D.map S _ _ _ m), map_smulₛₗ, map_smul, he, D.eCoord_smul_e, D.eCoord_smul_e]

theorem mem_H_iff {G : PDivGroup p S.R} (c : ConstTate (eps S) G) (n : ℕ) (u : S.R)
    (hu : zeta S.ε 1 - 1 = (zeta S.ε (n + 1) - 1) * u) (x : Fin G.height → S.R) :
    x ∈ H D c n ↔ ∃ m, ∀ j, u * fontaineTheta S.R p ((phiInv p S.R)^[n + 1] (coord D c m j)) = x j := by
  rw [mem_H]
  constructor
  · rintro ⟨k, hk, hx⟩
    obtain ⟨m, hm⟩ := (mem_K D c _ _).1 hk
    refine ⟨m, fun j => isSMulRegular_zeta_sub_one S n ?_⟩
    have h1 := congrFun hx j
    simp only [Pi.smul_apply, piMap_apply, smul_eq_mul] at h1 ⊢
    rw [← h1, hm, hu, mul_assoc]
  · rintro ⟨m, hm⟩
    refine ⟨_, (mem_K D c _ _).2 ⟨m, fun _ => rfl⟩, funext fun j => ?_⟩
    simp only [Pi.smul_apply, piMap_apply, smul_eq_mul]
    rw [← hm, hu, mul_assoc]

theorem baseChange_lattices : ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R) (h : S.Over S' α) (G : PDivGroup p S.R) (c : ConstTate (eps S) G), (∃ bc : D.Cov G →ₛₗ[α] D.Cov (G.baseChange S'.R), Submodule.span (Ainf p S'.R) (Set.range bc) = ⊤ ∧ ∀ m j, coord D (c.baseChange S'.R (muRoot_eps_of_over h)) (bc m) j = α (coord D c m j)) ∧ ∀ n, H D (c.baseChange S'.R (muRoot_eps_of_over h)) n = Submodule.span S'.R (piMap (algebraMap S.R S'.R) (Fin G.height) '' (H D c n : Set (Fin G.height → S.R))) := by
  intro p _ D S S' _ α h G c
  refine ⟨exists_bc D h G c, fun n => ?_⟩
  obtain ⟨bc, h1, h2⟩ := exists_bc D h G c
  obtain ⟨u, hu⟩ := zeta_sub_one_dvd S n
  have hz : ∀ k, zeta S'.ε k = algebraMap S.R S'.R (zeta S.ε k) := fun k => by
    simpa using muRoot_eps_of_over h k
  have hu' : zeta S'.ε 1 - 1 = (zeta S'.ε (n + 1) - 1) * algebraMap S.R S'.R u := by
    simpa [hz] using congrArg (algebraMap S.R S'.R) hu
  have hv : ∀ m j, algebraMap S.R S'.R u * fontaineTheta S'.R p ((phiInv p S'.R)^[n + 1]
      (coord D (c.baseChange S'.R (muRoot_eps_of_over h)) (bc m) j)) =
      algebraMap S.R S'.R (u * fontaineTheta S.R p ((phiInv p S.R)^[n + 1] (coord D c m j))) := fun m j => by
    rw [h2, ← map_phiInv h, h.1, map_mul]
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, hm⟩ := (mem_H_iff D _ n _ hu' x).1 hx
    obtain rfl := funext hm
    have hm' : m ∈ Submodule.span (Ainf p S'.R) (Set.range bc) := h1 ▸ Submodule.mem_top
    clear hx hm
    induction hm' using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨m, rfl⟩ := hm
      exact Submodule.subset_span ⟨_, (mem_H_iff D c n u hu _).2 ⟨m, fun _ => rfl⟩, funext fun j => (hv m j).symm⟩
    | zero =>
      convert Submodule.zero_mem _ using 1
      funext j
      rw [map_zero, Pi.zero_apply, ← RingHom.coe_pow, map_zero, map_zero, mul_zero, Pi.zero_apply]
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext j
      rw [map_add, Pi.add_apply, ← RingHom.coe_pow, map_add, map_add, mul_add, Pi.add_apply]
    | smul a x _ hx =>
      convert Submodule.smul_mem _ (fontaineTheta S'.R p ((phiInv p S'.R)^[n + 1] a)) hx using 1
      funext j
      rw [map_smul, Pi.smul_apply, smul_eq_mul, ← RingHom.coe_pow, map_mul, map_mul, Pi.smul_apply, smul_eq_mul,
        mul_left_comm]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hm⟩ := (mem_H_iff D c n u hu x).1 hx
    exact (mem_H_iff D _ n _ hu' _).2 ⟨bc m, fun j => (hv m j).trans (congrArg _ (hm j))⟩

end GlobalTheory.PerfdLat.LatticeBaseChange
