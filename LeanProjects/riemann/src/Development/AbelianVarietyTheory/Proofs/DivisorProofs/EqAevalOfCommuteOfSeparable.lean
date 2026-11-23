import Mathlib

open Polynomial
open scoped TensorProduct

namespace GlobalTheory.SepCentralizer

theorem exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective (aeval g p) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    by_contra hw0
    exact hcon w hw0 hw
  have hunit : IsUnit (aeval g p) :=
    (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let gL : Module.End L (L ⊗[K] V) := Module.End.baseChangeHom K L V g
  have hgL : gL = g.baseChange L := rfl
  have hroot : gL.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [hgL, LinearMap.charpoly_baseChange, IsRoot.def, eval_map_algebraMap]
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly gL _).2 hroot).exists_hasEigenvector
  have h1 : aeval gL (p.map (algebraMap K L)) v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hv, eval_map_algebraMap, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_self, zero_smul]
  have h2 : aeval gL (p.map (algebraMap K L)) = Module.End.baseChangeHom K L V (aeval g p) := by
    rw [aeval_map_algebraMap, ← aeval_algHom_apply]
  have h3 : IsUnit (Module.End.baseChangeHom K L V (aeval g p)) := hunit.map _
  rw [h2] at h1
  have h4 := ((Module.End.isUnit_iff _).1 h3).1
  exact hv.2 (h4 (by rw [h1, map_zero]))

theorem exists_annihilator_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  induction d using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 =>
    intro h
    exact absurd (zero_dvd_iff.1 h) g.charpoly_monic.ne_zero
  | h1 hx =>
    intro _
    exact ⟨0, map_zero _, fun q _ => hx.dvd⟩
  | hpr i hp =>
    rename_i p
    intro h
    rcases i with _ | _ | i
    · exact ⟨0, map_zero _, fun q _ => by simp⟩
    · rw [zero_add, pow_one] at h ⊢
      obtain ⟨w, hw0, hw⟩ := exists_ne_zero_aeval_eq_zero g p hp.irreducible h
      refine ⟨w, hw, fun q hq => ?_⟩
      by_contra hnd
      obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hnd
      apply hw0
      have := congrArg (fun r => aeval g r w) hab
      simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, hw, hq,
        map_zero, add_zero, Module.End.one_apply] at this
      exact this.symm
    · exfalso
      have h2 : p * p ∣ g.charpoly := by
        refine dvd_trans ?_ h
        exact ⟨p ^ i, by ring⟩
      exact hp.not_isUnit (hs.squarefree p h2)
  | hcp hxy hx hy =>
    rename_i x y
    intro h
    have hco : IsCoprime x y := hxy.isCoprime
    obtain ⟨e₁, h1, h1'⟩ := hx (dvd_trans (dvd_mul_right x y) h)
    obtain ⟨e₂, h2, h2'⟩ := hy (dvd_trans (dvd_mul_left y x) h)
    refine ⟨e₁ + e₂, ?_, fun q hq => ?_⟩
    · rw [map_add]
      have a1 : aeval g (x * y) e₁ = 0 := by
        rw [mul_comm, map_mul, Module.End.mul_apply, h1, map_zero]
      have a2 : aeval g (x * y) e₂ = 0 := by
        rw [map_mul, Module.End.mul_apply, h2, map_zero]
      rw [a1, a2, add_zero]
    · rw [map_add] at hq
      have b1 : x ∣ q := by
        have : aeval g (q * y) e₁ = 0 := by
          have c := congrArg (aeval g y) hq
          rw [map_add, map_zero, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
            mul_comm y q] at c
          have c2 : aeval g (q * y) e₂ = 0 := by
            rw [map_mul, Module.End.mul_apply, h2, map_zero]
          rwa [c2, add_zero] at c
        exact hco.dvd_of_dvd_mul_right (h1' _ this)
      have b2 : y ∣ q := by
        have : aeval g (q * x) e₂ = 0 := by
          have c := congrArg (aeval g x) hq
          rw [map_add, map_zero, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
            mul_comm x q] at c
          have c2 : aeval g (q * x) e₁ = 0 := by
            rw [map_mul, Module.End.mul_apply, h1, map_zero]
          rwa [c2, zero_add] at c
        exact hco.symm.dvd_of_dvd_mul_right (h2' _ this)
      exact hco.mul_dvd b1 b2

theorem exists_cyclic {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) :
    ∃ e : V, ∀ v : V, ∃ q : K[X], aeval g q e = v := by
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  refine ⟨e, ?_⟩
  let φ : K[X] →ₗ[K] V := (LinearMap.applyₗ e) ∘ₗ (aeval g).toLinearMap
  have hφ : ∀ p, φ p = aeval g p e := fun p => rfl
  let ψ : degreeLT K (Module.finrank K V) →ₗ[K] V := φ ∘ₗ (degreeLT K (Module.finrank K V)).subtype
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    have h1 : g.charpoly ∣ (q : K[X]) := he _ hq
    have h2 : (q : K[X]).degree < g.charpoly.degree := by
      rw [degree_eq_natDegree g.charpoly_monic.ne_zero, LinearMap.charpoly_natDegree]
      exact mem_degreeLT.1 q.2
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have hfin : Module.finrank K (degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(degreeLTEquiv K (Module.finrank K V)).finrank_eq, Module.finrank_fin_fun]
  have : FiniteDimensional K (degreeLT K (Module.finrank K V)) :=
    (degreeLTEquiv K (Module.finrank K V)).symm.finiteDimensional
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  intro v
  obtain ⟨q, hq⟩ := hsurj v
  exact ⟨q, hq⟩

theorem exists_eq_aeval_of_commute {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g c : Module.End K V) (hs : g.charpoly.Separable)
    (hc : c * g = g * c) : ∃ p : K[X], c = aeval g p := by
  obtain ⟨e, he⟩ := exists_cyclic g hs
  obtain ⟨p, hp⟩ := he (c e)
  refine ⟨p, LinearMap.ext fun v => ?_⟩
  obtain ⟨q, rfl⟩ := he v
  have hcq : Commute (aeval g q) c :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K g) hc).symm
  rw [← Module.End.mul_apply, ← hcq.eq, Module.End.mul_apply, ← hp, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem eq_aeval_of_commute_of_separable : ∀ (k : Type) [Field k] (n : ℕ)
    (Γ C : Matrix (Fin n) (Fin n) k) (u r : k[X]),
    u * Γ.charpoly + r * derivative Γ.charpoly = 1 → C * Γ = Γ * C →
    ∃ g : k[X], C = aeval Γ g := by
  intro k _ n Γ C u r h hC
  let e := (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
  have hs : (e Γ).charpoly.Separable := by
    rw [show e Γ = Matrix.toLin' Γ from rfl, Matrix.charpoly_toLin']
    exact ⟨u, r, h⟩
  have hc : e C * e Γ = e Γ * e C := by
    rw [← map_mul, ← map_mul, hC]
  obtain ⟨p, hp⟩ := exists_eq_aeval_of_commute _ _ hs hc
  refine ⟨p, e.injective ?_⟩
  rw [hp]
  exact aeval_algHom_apply e.toAlgHom Γ p

end GlobalTheory.SepCentralizer
