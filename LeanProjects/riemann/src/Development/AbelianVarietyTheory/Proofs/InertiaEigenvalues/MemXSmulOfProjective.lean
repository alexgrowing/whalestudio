import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.WachFree

theorem mem_X_smul_of_projective {D M : Type} [CommRing D] [IsDomain D] [AddCommGroup M]
    [Module D⟦X⟧ M] [Module.Projective D⟦X⟧ M] (c : D) (hc : c ≠ 0) (x y : M)
    (h : (C c : D⟦X⟧) • x = (X : D⟦X⟧) • y) : ∃ z : M, x = (X : D⟦X⟧) • z := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective D⟦X⟧ M›
  have hs' : ∀ m, Finsupp.linearCombination D⟦X⟧ id (s m) = m := fun m => LinearMap.congr_fun hs m
  have hd : ∀ m, (X : D⟦X⟧) ∣ s x m := by
    intro m
    have h1 := congrArg (fun w => constantCoeff (s w m)) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, constantCoeff_C,
      constantCoeff_X, zero_mul] at h1
    exact X_dvd_iff.mpr ((mul_eq_zero.mp h1).resolve_left hc)
  have : x ∈ LinearMap.range ((X : D⟦X⟧) • (LinearMap.id : M →ₗ[D⟦X⟧] M)) := by
    rw [← hs' x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    obtain ⟨d, hd⟩ := hd m
    exact ⟨d • m, by rw [hd, mul_smul]; rfl⟩
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by simpa using hz.symm⟩

theorem free_of_regular {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular M (X : O⟦X⟧))
    (h : ∀ x y : M, (C c : O⟦X⟧) • x = (X : O⟦X⟧) • y → ∃ z : M, x = (X : O⟦X⟧) • z) :
    Module.Free O⟦X⟧ M := by
  haveI : Module.FinitePresentation O⟦X⟧ M := Module.finitePresentation_of_finite _ _
  have hker : Ideal.span {(X : O⟦X⟧)} = RingHom.ker (constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, X_dvd_iff]
  let e : (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) ≃+* O :=
    (Ideal.quotEquivOfEq hker).trans
      (RingHom.quotientKerEquivOfSurjective (f := constantCoeff (R := O))
        fun a => ⟨C a, by simp⟩)
  haveI : IsDomain (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) := e.toMulEquiv.isDomain
  haveI : IsPrincipalIdealRing (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  have hpow : ∀ (k : ℕ) (x y : M), (C (c ^ k) : O⟦X⟧) • x = (X : O⟦X⟧) • y →
      ∃ z : M, x = (X : O⟦X⟧) • z := by
    intro k
    induction k with
    | zero => intro x y hxy; exact ⟨y, by simpa using hxy⟩
    | succ k ih =>
      intro x y hxy
      rw [pow_succ, map_mul, mul_smul] at hxy
      obtain ⟨z, hz⟩ := ih _ _ hxy
      exact h _ _ hz
  have hdvd : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ c ^ k := by
    intro a ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    have hj : j ≠ 0 := by
      rintro rfl
      exact hc' (by simp)
    refine ⟨k, ?_⟩
    rw [Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd (Dvd.dvd.mul_left (dvd_pow_self _ hj) _) _
  haveI := Module.Finite.of_restrictScalars_finite O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)})
    (QuotSMulTop (X : O⟦X⟧) M)
  haveI : Module.IsTorsionFree (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) (QuotSMulTop (X : O⟦X⟧) M) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    by_cases hr : constantCoeff r = 0
    · left
      rw [Ideal.Quotient.eq_zero_iff_mem, hker]
      exact hr
    right
    have h1 : (Submodule.Quotient.mk (r • m) : QuotSMulTop (X : O⟦X⟧) M) = 0 := hrm
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
    obtain ⟨y, -, hy⟩ := h1
    obtain ⟨k, b, hb⟩ := hdvd _ hr
    obtain ⟨d, hd⟩ : (X : O⟦X⟧) ∣ C (c ^ k) - C b * r := by
      rw [X_dvd_iff]
      simp [hb, mul_comm]
    obtain ⟨z, hz⟩ := hpow k m (d • m + (C b : O⟦X⟧) • y) (by
      rw [smul_add, smul_comm (X : O⟦X⟧) (C b : O⟦X⟧) y, hy, smul_smul, smul_smul, ← hd, ← add_smul,
        sub_add_cancel])
    exact ⟨z, trivial, hz.symm⟩
  refine (Module.free_quotSMulTop_iff_free O⟦X⟧ M ?_ hX).mp inferInstance
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_iff_constantCoeff]
  simp

theorem finrank_fibre {ι R N : Type} [DecidableEq ι] [CommRing R] [IsLocalRing R] [AddCommGroup N]
    [Module (ι → R) N] [Module.Finite (ι → R) N] [Module.Flat (ι → R) N] (i : ι) :
    ∃ r : ℕ, ∀ (S : Type) [CommRing S] [Nontrivial S] [Algebra (ι → R) S],
      algebraMap (ι → R) S (Pi.single i 1) = 1 → Module.finrank S (S ⊗[ι → R] N) = r := by
  letI : Algebra (ι → R) R := (Pi.evalRingHom (fun _ : ι => R) i).toAlgebra
  haveI : Module.Free R (R ⊗[ι → R] N) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.finrank R (R ⊗[ι → R] N), fun S _ _ _ hS => ?_⟩
  letI : Algebra R S := ((algebraMap (ι → R) S).comp (Pi.constRingHom ι R)).toAlgebra
  haveI : IsScalarTower (ι → R) R S := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap (ι → R) S a = algebraMap (ι → R) S (fun _ => a i)
    have : a * Pi.single i 1 = (fun _ => a i) * Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    have h2 := congrArg (algebraMap (ι → R) S) this
    rwa [map_mul, map_mul, hS, mul_one, mul_one] at h2
  rw [← (AlgebraTensorModule.cancelBaseChange (ι → R) R S S N).finrank_eq,
    Module.finrank_baseChange]

theorem basis_of_baseChange {ι R N E D : Type} [Finite ι] [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module (ι → R) N] [Module.Finite (ι → R) N] [Module R N]
    [IsScalarTower R (ι → R) N] [Module.Flat R N] [CommRing E] [Algebra (ι → R) E]
    (hE : Function.Injective (algebraMap (ι → R) E)) [AddCommGroup D] [Module E D]
    [Module (ι → R) D] [IsScalarTower (ι → R) E D] [Module.Free E D] (f : N →ₗ[ι → R] D)
    (hf : IsBaseChange E f) : Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → R) N) := by
  classical
  haveI := Fintype.ofFinite ι
  haveI : Module.Flat (ι → R) N := Algebra.FormallyUnramified.flat_of_restrictScalars R (ι → R) N
  haveI : Finite (MaximalSpectrum (ι → R)) := by
    haveI := (Algebra.QuasiFinite.finite_primesOver (S := ι → R)
      (IsLocalRing.maximalIdeal R)).to_subtype
    refine Finite.of_injective (fun n : MaximalSpectrum (ι → R) =>
      (⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
        (@Ideal.isMaximal_comap_of_isIntegral_of_isMaximal R _ _ _ _ _ n.asIdeal n.isMaximal)).symm⟩⟩ :
        (IsLocalRing.maximalIdeal R).primesOver (ι → R))) fun a b hab => ?_
    exact MaximalSpectrum.ext (congrArg Subtype.val hab)
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ _ fun P => ?_
  haveI := P.isMaximal
  have hee : ∀ i : ι, (Pi.single i 1 : ι → R) * (Pi.single i 1 - 1) = 0 := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  obtain ⟨i, hi⟩ : ∃ i : ι, (Pi.single i 1 : ι → R) ∉ P.asIdeal := by
    by_contra hcon
    push Not at hcon
    apply P.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← Finset.univ_sum_single (1 : ι → R)]
    exact Ideal.sum_mem _ fun j _ => hcon j
  have hi' : (Pi.single i 1 - 1 : ι → R) ∈ P.asIdeal :=
    (P.isMaximal.isPrime.mem_or_mem (by rw [hee i]; exact Ideal.zero_mem _)).resolve_left hi
  obtain ⟨r, hr⟩ := finrank_fibre (R := R) (N := N) i
  rw [hr ((ι → R) ⧸ P.asIdeal) (by
    rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq]
    exact hi')]
  let I : Ideal E := Ideal.span {algebraMap (ι → R) E (Pi.single i 1 - 1)}
  haveI : Nontrivial (E ⧸ I) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro hI
    rw [Ideal.span_singleton_eq_top] at hI
    apply hi
    have : algebraMap (ι → R) E (Pi.single i 1) = 0 := by
      rw [← hI.mul_left_eq_zero, ← map_mul, hee, map_zero]
    rw [hE (this.trans (map_zero _).symm)]
    exact Ideal.zero_mem _
  haveI : Nontrivial E := (algebraMap E (E ⧸ I)).domain_nontrivial
  rw [← hr (E ⧸ I) (by
    rw [IsScalarTower.algebraMap_apply (ι → R) E (E ⧸ I), Ideal.Quotient.algebraMap_eq,
      ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)),
    ← (AlgebraTensorModule.cancelBaseChange (ι → R) E (E ⧸ I) (E ⧸ I) N).finrank_eq,
    (AlgebraTensorModule.congr (LinearEquiv.refl (E ⧸ I) (E ⧸ I)) hf.equiv).finrank_eq,
    Module.finrank_baseChange]

theorem basis_of_regular {ι O N E D : Type} [Finite ι] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup N] [Module (ι → O⟦X⟧) N] [Module.Finite (ι → O⟦X⟧) N]
    [CommRing E] [Algebra (ι → O⟦X⟧) E]
    (hE : Function.Injective (algebraMap (ι → O⟦X⟧) E)) [AddCommGroup D] [Module E D]
    [Module (ι → O⟦X⟧) D] [IsScalarTower (ι → O⟦X⟧) E D] [Module.Free E D]
    (f : N →ₗ[ι → O⟦X⟧] D) (hf : IsBaseChange E f) (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular N (fun _ => X : ι → O⟦X⟧))
    (h : ∀ x y : N, (fun _ => C c : ι → O⟦X⟧) • x = (fun _ => X : ι → O⟦X⟧) • y →
      ∃ z : N, x = (fun _ => X : ι → O⟦X⟧) • z) :
    Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → O⟦X⟧) N) := by
  letI : Module O⟦X⟧ N := Module.compHom _ (algebraMap O⟦X⟧ (ι → O⟦X⟧))
  haveI : IsScalarTower O⟦X⟧ (ι → O⟦X⟧) N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O⟦X⟧ N := Module.Finite.trans (ι → O⟦X⟧) _
  haveI : Module.Free O⟦X⟧ N := free_of_regular c hc hc' hX h
  exact basis_of_baseChange hE f hf

set_option maxHeartbeats 1600000 in

theorem wach_free {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T))
      (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K s LL h).N T)) := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T
  generalize H.W K s LL h = W at hproj ⊢
  obtain ⟨hfree, hrk⟩ := W.DD_free T
  rw [← hrk]
  haveI : Module.Finite (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(W.N T) :=
    Module.Finite.iff_fg.mpr (W.N_fg T)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  refine basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (O := ↥(OL LL))
    (N := ↥(W.N T)) (E := W.EE) (D := W.DD T) W.EE_inj (W.N T).subtype (W.N_base T hT)
    ((l : ℕ) : ↥(OL LL)) hl0 hl ?_ ?_
  · intro x y hxy
    have h1 : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (x : W.DD T) =
        (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (y : W.DD T) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  · intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @mem_X_smul_of_projective ℤ_[l] ↥(W.N T) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x y (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y
        rw [e1, e2]
        exact hxy)
    refine ⟨z, ?_⟩
    change x = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    exact hz

end GlobalTheory.WachFree
