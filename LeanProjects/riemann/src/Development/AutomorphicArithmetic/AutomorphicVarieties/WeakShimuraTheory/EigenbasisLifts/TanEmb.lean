import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CotDer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dual_der (O R K : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra O R] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K]
    (y : R →ₐ[O] K) (hy : ∀ a ∈ maximalIdeal R, y a = 0) :
    ∃ (D : Fin (maximalIdeal R).spanFinrank → R →ₗ[O] K) (r : Fin (maximalIdeal R).spanFinrank → R),
      (∀ i, D i ∈ PtDer y K) ∧ ∀ i j, D i (r j) = if j = i then 1 else 0 := by
  classical
  let yb : ResidueField R →+* K :=
    Ideal.Quotient.lift (maximalIdeal R) y.toRingHom (fun a ha => hy a ha)
  have hyb : ∀ f : R, yb (algebraMap R (ResidueField R) f) = y f := fun f => rfl
  have h1 : ∀ c : O, yb (algebraMap O (ResidueField R) c) = algebraMap O K c := by
    intro c
    rw [← y.commutes c]
    rfl
  let ya : ResidueField R →ₐ[O] K := { yb with commutes' := h1 }
  have hyinj : Function.Injective yb := yb.injective
  have hinj : Function.Injective (algebraMap O (ResidueField R)) := by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective O K
    rw [← h1, ← h1, hab]
  have halg : Algebra.IsAlgebraic O (ResidueField R) :=
    Algebra.IsAlgebraic.of_injective ya hyinj
  obtain ⟨d, hd⟩ := UpperTheory.V.Ws.Eb.cotDer O R hinj halg
  have hn : Module.finrank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanFinrank :=
    (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R) hn
  have hsurj : ∀ j, ∃ a : maximalIdeal R, (maximalIdeal R).toCotangent a = b j :=
    fun j => (maximalIdeal R).toCotangent_surjective (b j)
  choose a ha using hsurj
  have hsm : ∀ (r : R) (v : CotangentSpace R) i,
      yb (b.coord i (r • v)) = y r * yb (b.coord i v) := by
    intro r v i
    rw [← algebraMap_smul (ResidueField R) r v, map_smul, smul_eq_mul, map_mul, hyb]
  let D : Fin (maximalIdeal R).spanFinrank → R →ₗ[O] K := fun i =>
    { toFun := fun f => yb (b.coord i (d f))
      map_add' := by
        intro f g
        simp only [map_add]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz, Derivation.map_algebraMap,
          smul_zero, add_zero, hsm, y.commutes, Algebra.smul_def] }
  refine ⟨D, fun j => (a j : R), ?_, ?_⟩
  · intro i
    intro f g
    show yb (b.coord i (d (f * g))) = y f • yb (b.coord i (d g)) + y g • yb (b.coord i (d f))
    rw [Derivation.leibniz, map_add, map_add, hsm, hsm, smul_eq_mul, smul_eq_mul]
  · intro i j
    show yb (b.coord i (d (a j : R))) = _
    rw [hd, ha, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.tanEmb :
    ∀ (O B K : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing B] [IsNoetherianRing B] [Algebra O B] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (x : B →ₐ[O] K) (p : Ideal B) [p.IsPrime], p = RingHom.ker x →
        ∀ N : ℕ, Module.rank K (PtDer x K) ≤ N → (maximalIdeal (Localization.AtPrime p)).spanFinrank ≤ N := by
  intro O B K _ _ _ _ _ _ _ _ _ _ x p _ hp N hN
  classical
  let R := Localization.AtPrime p
  have hker : ∀ b : B, b ∈ p ↔ x b = 0 := by
    intro b
    rw [hp]
    exact Iff.rfl
  have hunit : ∀ s : p.primeCompl, IsUnit (x s) := by
    intro s
    apply IsUnit.mk0
    intro h0
    exact s.2 ((hker s).2 h0)
  let y : R →ₐ[O] K := IsLocalization.liftAlgHom (M := p.primeCompl) (f := x) hunit
  have hyx : ∀ b : B, y (algebraMap B R b) = x b := fun b => IsLocalization.lift_eq _ _
  have hy : ∀ a ∈ maximalIdeal R, y a = 0 := by
    intro a ha
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
    have hb : b ∈ p := by
      rwa [IsLocalization.AtPrime.mk'_mem_maximal_iff R p] at ha
    have h1 := congrArg y (IsLocalization.mk'_spec R b s)
    rw [map_mul, hyx, hyx, (hker b).1 hb] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hunit s).ne_zero
  obtain ⟨D, r, hD, hDr⟩ := dual_der O R K y hy
  have hDl : ∀ i (u w : R), D i (u * w) = y u * D i w + y w * D i u := by
    intro i u w
    have := hD i u w
    rwa [smul_eq_mul, smul_eq_mul] at this
  let L : B →ₗ[O] R := (IsScalarTower.toAlgHom O B R).toLinearMap
  have hL : ∀ b, L b = algebraMap B R b := fun b => rfl
  have hmem : ∀ i, (D i).comp L ∈ PtDer x K := by
    intro i f g
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hL, hL, hL, map_mul,
      hDl, hyx, hyx, smul_eq_mul, smul_eq_mul]
  let v : Fin (maximalIdeal R).spanFinrank → PtDer x K := fun i => ⟨(D i).comp L, hmem i⟩
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let E : R → K := fun a => ∑ i, g i * D i a
    have hE : ∀ u w : R, E (u * w) = y u * E w + y w * E u := by
      intro u w
      simp only [E, hDl, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> ring
    have hB : ∀ b : B, E (algebraMap B R b) = 0 := by
      intro b
      have := congrArg (fun w : PtDer x K => (w : B →ₗ[O] K) b) hg
      simpa [v, E, hL] using this
    have hR : ∀ a : R, E a = 0 := by
      intro a
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
      have h1 := hB b
      rw [← IsLocalization.mk'_spec R b s, hE, hB, mul_zero, zero_add, hyx] at h1
      exact (mul_eq_zero.mp h1).resolve_left (hunit s).ne_zero
    intro j
    have := hR (r j)
    simpa [E, hDr] using this
  have hc := hli.cardinal_le_rank
  rw [Cardinal.mk_fintype, Fintype.card_fin] at hc
  exact_mod_cast hc.trans hN
