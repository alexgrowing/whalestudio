import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.TriangularOfReducibleRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ConstOfChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocGood

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section Gen

open UpperTheory.V.Alg

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]

private theorem gf_res_zpow {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (t : Rˣ) (ht : res O R t = 1) (j : ℤ) : res O R ((t ^ j : Rˣ) : R) = 1 := by
  have h1 : Units.map (res O R : R →* ResidueField O) t = 1 := Units.ext ht
  have h2 := map_zpow (Units.map (res O R : R →* ResidueField O)) t j
  rw [h1, _root_.one_zpow] at h2
  exact congrArg Units.val h2

private def gf_torLift [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R) (t : Rˣ)
    (ht : res O R t = 1) : GLift O η Ψ R where
  hom := conjBy (tor R t) r.hom
  cont a b N := by
    simp only [(conjBy_tor r.hom t).1, map_mul]
    exact (r.cont a b N).comp fun y => Ideal.Quotient.mk _ ((t ^ wt a b : Rˣ) : R) * y
  red g := by
    rw [← r.red g]
    refine SemidirectProduct.ext (Units.ext ?_) ((conjBy_tor r.hom t).2.1 g)
    ext a b
    show res O R ((conjBy (tor R t) r.hom g).mat a b) = res O R ((r.hom g).mat a b)
    rw [(conjBy_tor r.hom t).1, map_mul, gf_res_zpow t ht, one_mul]

private theorem gf_congOne {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (t : Rˣ) (ht : res O R t = 1) : CongOne (maximalIdeal R) (tor R t) := by
  intro a b
  rw [Matrix.sub_apply, tor_val]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ← res_eq_zero_iff O, map_sub, gf_res_zpow t ht, map_one,
      sub_self]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_self]
    exact zero_mem _

private theorem gf_bar (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (g : Γ) (a b : Fin 3) :
    (r0 η (barChar O Ψ) g).mat a b = residue O ((r0 η Ψ g).mat a b) := by
  simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply]
  split_ifs
  · exact (congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 a))).symm
  · simp

omit [IsLocalRing O] in
private theorem gf_off (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (g : Γ) (a b : Fin 3) (h : wt a b ≠ 0) :
    (r0 η Ψ g).mat a b = 0 := by
  simp only [GG.mat, unitaryThreeReflection_left, tor_val]
  exact Matrix.diagonal_apply_ne _ (by rintro rfl; exact h (sub_self _))

private theorem gf_pres [IsDomain O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [TopologicalSpace Γ]
    {H : Type} [Group H] [TopologicalSpace H] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ}
    {hι : Continuous ι} {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {c g₁ : Γ}
    (hI : ConjStable U I) (S : SRing N hι U I c g₁) :
    ∃ W : WPres O ℤ S.R, (∀ i, W.z i ∈ maximalIdeal S.R) ∧
      (∀ i, ∃ g a b, W.z i = (S.r.hom g).mat a b - algebraMap O _ ((r0 η Ψ g).mat a b) ∧ W.wt i = wt a b) ∧
      ∀ g a b, (S.r.hom g).mat a b ∈ W.part (wt a b) := by
  have hm : ∀ g a b, (S.r.hom g).mat a b - algebraMap O _ ((r0 η Ψ g).mat a b) ∈ maximalIdeal S.R := by
    intro g a b
    rw [← res_eq_zero_iff O, map_sub, AlgHom.commutes, sub_eq_zero]
    exact (congrArg (fun x => GG.mat x a b) (S.r.red g)).trans (gf_bar η Ψ g a b)
  obtain ⟨W, u, hu, he⟩ := coord_grading O ℤ S.R (Γ × Fin 3 × Fin 3)
    (fun s => (S.r.hom s.1).mat s.2.1 s.2.2 - algebraMap O _ ((r0 η Ψ s.1).mat s.2.1 s.2.2))
    (fun s => wt s.2.1 s.2.2) (fun s => hm _ _ _)
    (fun R' _ _ _ f f' h => by
      have h1 : S.r.map f = S.r.map f' := by
        refine GLift.ext (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl)
        ext a b
        have := h (g, a, b)
        simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
        exact this
      exact ((S.rep R').2 _ ((S.rep R').1 f')).unique h1 rfl)
    (fun R' _ _ _ f t ht => by
      obtain ⟨h1, h2, h3⟩ := (S.rep R').1 f
      obtain ⟨f', hf', -⟩ := (S.rep R').2 (gf_torLift (S.r.map f) (t (Multiplicative.ofAdd 1)) (ht _))
        ⟨(conjBy_tor _ _).2.2.1 c g₁ h1, fun g hg => by
          show MulAut.conj _ ((S.r.map f).hom g) = 1
          rw [h2 g hg, map_one],
          hI R' ((S.r.map f).comap ι hι) _ _ (gf_congOne _ (ht _)) rfl h3⟩
      have htj : ∀ j : ℤ, t (Multiplicative.ofAdd 1) ^ j = t (Multiplicative.ofAdd j) := fun j => by
        rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
      refine ⟨f', fun ⟨g, a, b⟩ => ?_⟩
      dsimp only
      have e := (conjBy_tor (S.r.map f).hom (t (Multiplicative.ofAdd 1))).1 g a b
      have e' : f' ((S.r.hom g).mat a b) = _ := (congrArg (fun x => (x.hom g).mat a b) hf').trans e
      rw [map_sub, map_sub f, AlgHom.commutes, AlgHom.commutes, e', htj, mul_sub]
      congr 1
      by_cases hab : wt a b = 0
      · simp [hab]
      · simp [gf_off η Ψ g a b hab])
  refine ⟨W, fun i => (hu i).1 ▸ hm _ _ _, fun i => ⟨(u i).1, (u i).2.1, (u i).2.2, hu i⟩, fun g a b => ?_⟩
  have h1 := he (g, a, b)
  have h2 : algebraMap O S.R ((r0 η Ψ g).mat a b) ∈ W.part (wt a b) := by
    by_cases hab : wt a b = 0
    · rw [hab, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : S.R) ∈ W.part 0)
    · rw [gf_off η Ψ g a b hab, map_zero]
      exact zero_mem _
  simpa only [sub_add_cancel] using add_mem h1 h2

omit [IsLocalRing O] in
private theorem gf_fin [IsNoetherianRing O] {R : Type} [CommRing R] [Algebra O R] (W : WPres O ℤ R)
    (r : Γ →* GG 3 R) (h : ∀ g a b, (r g).mat a b ∈ W.part (wt a b)) (hf : Module.Finite O (W.part 0)) :
    Module.Finite O (weightZeroSubalgebra O r) := by
  have h1 : ∀ L : List (Γ × Fin 3 × Fin 3),
      (L.map fun s => (r s.1).mat s.2.1 s.2.2).prod ∈ W.part (L.map fun s => wt s.2.1 s.2.2).sum := by
    intro L
    induction L with
    | nil => exact (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
    | cons s L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact SetLike.GradedMul.mul_mem (h _ _ _) ih
  let P : Subalgebra O R := (W.part 0).toSubalgebra (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
    fun x y hx hy => by simpa using (SetLike.GradedMul.mul_mem hx hy : x * y ∈ W.part (0 + 0))
  have h2 : weightZeroSubalgebra O r ≤ P := Algebra.adjoin_le (by
    rintro x ⟨L, hL, rfl⟩
    have := h1 L
    rw [hL] at this
    exact this)
  have h3 : (weightZeroSubalgebra O r).toSubmodule ≤ W.part 0 := h2
  exact Module.Finite.of_injective (Submodule.inclusion h3) (Submodule.inclusion_injective h3)

private theorem diag_eq_and_triangular_of_charpoly_eq [Finite (ResidueField O)] (h2 : IsUnit (2 : O)) {A : Type} [CommRing A] [IsDomain A]
    [IsLocalRing A] [Algebra O A] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O A a = 0) {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}
    {c g₁ : Γ} (hM : Marks η Ψ c g₁) (r : Γ →* GG 3 A) (hr : UnitaryThreeInertia.Red η Ψ r) (hN : Normalised c g₁ r)
    (U : Subgroup Γ) (hU : U.FiniteIndex)
    (hc : ∀ g ∈ U, η g = 1 → (r g).mat.charpoly = (((r0 η Ψ g).mat).map (algebraMap O A)).charpoly) :
    (∀ g a, (r g).mat a a = algebraMap O A ((r0 η Ψ g).mat a a)) ∧
      ((∀ g a b, wt a b < 0 → (r g).mat a b = 0) ∨ ∀ g a b, 0 < wt a b → (r g).mat a b = 0) := by
  letI : Algebra (ResidueField O) A := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O A) h0).toAlgebra
  have e : ∀ g a b, algebraMap (ResidueField O) A ((r0 η (barChar O Ψ) g).mat a b) =
      algebraMap O A ((r0 η Ψ g).mat a b) := fun g a b => by
    rw [gf_bar]
    rfl
  have e' : ∀ g, ((r0 η (barChar O Ψ) g).mat).map (algebraMap (ResidueField O) A) =
      ((r0 η Ψ g).mat).map (algebraMap O A) := fun g => Matrix.ext (e g)
  have h2' : (2 : ResidueField O) ≠ 0 := by
    have := (h2.map (residue O)).ne_zero
    rwa [map_ofNat] at this
  have hM' : Marks η (barChar O Ψ) c g₁ := by
    refine ⟨hM.csq, hM.ηc, ?_, hM.ηg, ?_⟩
    · show Units.map _ (Ψ c) = 1
      rw [hM.Ψc, map_one]
    · have := hM.Ψg.map (residue O)
      rw [map_sub, map_pow, map_one] at this
      exact this
  obtain ⟨hT, hd⟩ := constOfChar Γ (ResidueField O) A h2' η (barChar O Ψ) c g₁ hM' r hr.mult
    (fun g => e' g ▸ hr.red g) hN U hU fun g hg hη => e' g ▸ hc g hg hη
  have key : ∀ g, ∃ g' ∈ η.ker, (r g).mat = (r g').mat := by
    intro g
    rcases Int.units_eq_one_or (η g) with hg | hg
    · exact ⟨g, hg, rfl⟩
    · have hl : (r c).left = 1 := Units.ext hN.atc
      refine ⟨g * c, by rw [MonoidHom.mem_ker, map_mul, hg, hM.ηc]; rfl, ?_⟩
      rw [map_mul, GG.mat, GG.mat, SemidirectProduct.mul_left, hl, map_one, mul_one]
  refine ⟨fun g a => (hd g a).trans (e g a a), hT.imp (fun h g a b hab => ?_) fun h g a b hab => ?_⟩ <;>
  · obtain ⟨g', hg', e⟩ := key g
    rw [e]
    exact h g' hg' a b hab

end Gen

theorem UpperTheory.V.Pr.finA_of_end :
    Loc.LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ →
    ∀ (B : ValuationSubring Ω), (∀ x, x ∈ B ↔ ‖D.j x‖ ≤ 1) → FinEnd l D.η D.Ψ D.cc g₁ B → FinA D g₁ := by
  intro hP Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ hM B hB ⟨V, hV, hE⟩ U S
  obtain ⟨W, hz, hw, hp⟩ := gf_pres (Loc.locGood hP D.loc U).conj S
  refine gf_fin W _ hp (finCrit c.O S.R W hz fun A _ _ hA f hf h0 => ?_)
  haveI := hA.toIsDomain
  haveI := hA.toIsDiscreteValuationRing
  haveI := hA.complete
  have hO := ordPt_of_gd hP D g₁ hM U S B hB A f hf
  obtain ⟨hd, hT⟩ := diag_eq_and_triangular_of_charpoly_eq (dat_facts D).2.2.2.2.2.2.1 h0 hM _ hO.red hO.norm V hV (hE A h0 _ hO)
  refine ⟨fun i hi => ?_, hT.imp (fun h i hi => ?_) fun h i hi => ?_⟩
  · obtain ⟨g, a, b, e1, e2⟩ := hw i
    obtain rfl : a = b := by
      rw [e2] at hi
      revert hi
      fin_cases a <;> fin_cases b <;> decide
    rw [e1, map_sub, AlgHom.commutes, sub_eq_zero]
    exact hd g a
  · obtain ⟨g, a, b, e1, e2⟩ := hw i
    rw [e2] at hi
    rw [e1, gf_off _ _ g a b hi.ne, map_zero, sub_zero]
    exact h g a b hi
  · obtain ⟨g, a, b, e1, e2⟩ := hw i
    rw [e2] at hi
    rw [e1, gf_off _ _ g a b hi.ne', map_zero, sub_zero]
    exact h g a b hi
