import Formalism.PadicSubsetSums.CentralIdempotents.SchurOrthogonalityCompact

open Polynomial
open scoped TensorProduct

namespace Formalism.IrreducibleCountingLemmas.Z

theorem exists_ne_zero_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (p : K[X]) (hp : Irreducible p)
    (hdvd : p ∣ g.charpoly) : ∃ w : V, w ≠ 0 ∧ aeval g p w = 0 := by
  classical
  by_contra hcon
  have hinj : Function.Injective (aeval g p) := by
    refine (injective_iff_map_eq_zero (aeval g p)).2 fun w hw => ?_
    by_contra hw0
    exact hcon ⟨w, hw0, hw⟩
  haveI : Fact (Irreducible p) := ⟨hp⟩
  have hunit : IsUnit (aeval g p) := by
    first
      | exact (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
      | exact (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)
  have hunitL := hunit.map (Module.End.baseChangeHom K (AdjoinRoot p) V)
  have hE : Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)
      = aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) := by
    rw [Polynomial.aeval_map_algebraMap, ← Polynomial.aeval_algHom_apply]
    rfl
  have hpr : Polynomial.eval (AdjoinRoot.root p) (p.map (algebraMap K (AdjoinRoot p))) = 0 := by
    rw [Polynomial.eval_map, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root p
  have hev : Module.End.HasEigenvalue (g.baseChange (AdjoinRoot p)) (AdjoinRoot.root p) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange]
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hpr
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h0 : aeval (g.baseChange (AdjoinRoot p)) (p.map (algebraMap K (AdjoinRoot p))) v = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hv, hpr, zero_smul]
  rw [← hE] at h0
  have hbij : Function.Injective (Module.End.baseChangeHom K (AdjoinRoot p) V (aeval g p)) := by
    first
      | exact ((Module.End.isUnit_iff _).1 hunitL).1
      | exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hunitL)
  exact hv.2 (hbij (h0.trans (map_zero _).symm))

theorem exists_annihilator_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hs : g.charpoly.Separable) (d : K[X]) :
    d ∣ g.charpoly → ∃ e : V, aeval g d e = 0 ∧ ∀ q : K[X], aeval g q e = 0 → d ∣ q := by
  classical
  have hm : ∀ (f h : Module.End K V) (x : V), (f * h) x = f (h x) := fun _ _ _ => rfl
  have hadd : ∀ (f h : Module.End K V) (x : V), (f + h) x = f x + h x := fun _ _ _ => rfl
  have hone : ∀ x : V, (1 : Module.End K V) x = x := fun _ => rfl
  have hkill : ∀ (s t : K[X]) (x : V), aeval g s x = 0 → aeval g (t * s) x = 0 := by
    intro s t x hx
    rw [map_mul, hm, hx, map_zero]
  have hsq : Squarefree g.charpoly := hs.squarefree
  refine WfDvdMonoid.induction_on_irreducible d ?_ ?_ ?_
  · intro h0
    exact absurd (zero_dvd_iff.1 h0) (LinearMap.charpoly_monic g).ne_zero
  · intro u hu _
    exact ⟨0, map_zero _, fun q _ => hu.dvd⟩
  · intro a i _ hi ih hdvd
    have ha : a ∣ g.charpoly := dvd_of_mul_left_dvd hdvd
    have hid : i ∣ g.charpoly := dvd_of_mul_right_dvd hdvd
    obtain ⟨ea, hea0, hea⟩ := ih ha
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_aeval_eq_zero g i hi hid
    have hcopOf : ∀ n : K[X], ¬ i ∣ n → IsCoprime i n := fun n h => by
      first
        | exact (Irreducible.coprime_iff_not_dvd hi).2 h
        | exact (Irreducible.isCoprime_iff_not_dvd hi).2 h
    have hcop : IsCoprime i a := hcopOf a fun hia =>
      hi.1 (hsq i (dvd_trans (mul_dvd_mul_left i hia) hdvd))
    refine ⟨ea + w, ?_, fun q hq => ?_⟩
    · rw [map_add, hkill a i ea hea0, mul_comm, hkill i a w hw, add_zero]
    · have hw' : aeval g (i * q) w = 0 := by
        rw [mul_comm]
        exact hkill i q w hw
      have hqi : aeval g (i * q) ea = 0 := by
        have h1 := hkill q i _ hq
        rwa [map_add, hw', add_zero] at h1
      have haq : a ∣ q := by
        have h2 : a ∣ i * q := hea _ hqi
        first
          | exact hcop.symm.dvd_of_dvd_mul_left h2
          | exact hcop.symm.dvd_of_dvd_mul_right (by rwa [mul_comm] at h2)
      have hea' : aeval g (a * q) ea = 0 := by
        rw [mul_comm]
        exact hkill a q ea hea0
      have hwq : aeval g (a * q) w = 0 := by
        have h1 := hkill q a _ hq
        rwa [map_add, hea', zero_add] at h1
      have hiaq : i ∣ a * q := by
        by_contra hn
        obtain ⟨u, t, hut⟩ := hcopOf _ hn
        apply hw0
        have h2 : aeval g (u * i + t * (a * q)) w = 0 := by
          rw [map_add, hadd, hkill i u w hw, hkill (a * q) t w hwq, add_zero]
        rwa [hut, map_one, hone] at h2
      have hiq : i ∣ q := by
        first
          | exact hcop.dvd_of_dvd_mul_left hiaq
          | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hiaq)
      exact hcop.mul_dvd hiq haq

theorem base_change_cyclic_vector : BCCyclicVector := by
  unfold BCCyclicVector
  intro K V _ _ _ _ g hs
  classical
  obtain ⟨e, -, he⟩ := exists_annihilator_eq g hs g.charpoly dvd_rfl
  let φ : K[X] →ₗ[K] V :=
    { toFun := fun q => aeval g q e
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let ψ : Polynomial.degreeLT K (Module.finrank K V) →ₗ[K] V :=
    φ.comp (Polynomial.degreeLT K (Module.finrank K V)).subtype
  have hdeg : g.charpoly.degree = (Module.finrank K V : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic g).ne_zero,
      LinearMap.charpoly_natDegree]
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun x hx => ?_
    have hmem := Polynomial.mem_degreeLT.1 x.2
    have hd : g.charpoly ∣ x.1 := he x.1 hx
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd (by rw [hdeg]; exact hmem))
  haveI : FiniteDimensional K (Polynomial.degreeLT K (Module.finrank K V)) :=
    LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv K (Module.finrank K V)).symm
  have hfr : Module.finrank K (Polynomial.degreeLT K (Module.finrank K V)) = Module.finrank K V := by
    rw [(Polynomial.degreeLTEquiv K (Module.finrank K V)).finrank_eq]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  refine ⟨e, fun v => ?_⟩
  obtain ⟨x, hx⟩ := hsurj v
  exact ⟨x.1, hx⟩

end Formalism.IrreducibleCountingLemmas.Z
