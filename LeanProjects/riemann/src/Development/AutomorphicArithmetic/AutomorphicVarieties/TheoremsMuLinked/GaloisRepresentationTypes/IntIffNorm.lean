import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CharpolyPowTwoByTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AutKQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.FreePU
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.TriangularOfReducibleRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdEndOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GdEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ClsEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MemGalOfQuadraticOfFixesDiscrRootsOfUnity
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsUnitPowNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtFinFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure

section Factor

open IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.Base

private theorem int_iff_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem loc_of_int {O R A : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A]
    [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A] (f : R →ₐ[O] A) : IsLocalHom f := by
  let g : R →+* f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' g hg
  have hl : IsLocalHom g := IsLocalHom.of_surjective _ hg
  haveI : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)
  have h2 : IsLocalHom (algebraMap f.range A) := Algebra.IsIntegral.isLocalHom _ _
  exact ⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩

private theorem exists_fac {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    (f : R →ₐ[c.O] PadicAlgCl l) (hf : IsLocPt f) :
    ∃ (A : Subalgebra c.O (PadicAlgCl l)) (_ : IsDiscreteValuationRing A) (_ : Module.Finite c.O A), ∀ x, f x ∈ A := by
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI := (dvrFacts l c.O).2.2.2.1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
  have hE' : ∀ a, f a ∈ E.1 := fun a => (hE a).1
  haveI := E.2
  have hint : ∀ x, IsIntegral ℤ_[l] (f x) := fun x => by
    obtain ⟨a, ha⟩ := residue_surjective (res c.O R x)
    have hm : x - algebraMap c.O R a ∈ maximalIdeal R := by
      rw [← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, ← ha]
      exact sub_self _
    have h1 : IsIntegral ℤ_[l] (f (algebraMap c.O R a)) := by
      rw [f.commutes]
      exact (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom ℤ_[l] c.O (PadicAlgCl l))
    have h2 := ((int_iff_norm _).2 (hf _ hm).le).add h1
    rwa [← map_add, sub_add_cancel] at h2
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E.1
  let j : E.1 →ₐ[ℤ_[l]] PadicAlgCl l := E.1.val.restrictScalars ℤ_[l]
  have hj : Function.Injective j := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E.1).equivMapOfInjective j hj
  let B := (integralClosure ℤ_[l] E.1).map j
  have hB : ∀ x, f x ∈ B := fun x => ⟨⟨f x, hE' x⟩, (isIntegral_algHom_iff j hj).1 (hint x), rfl⟩
  let A : Subalgebra c.O (PadicAlgCl l) := { B.toSubsemiring with algebraMap_mem' := fun a => f.commutes a ▸ hB _ }
  have d1 : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have d2 : Module.Finite ℤ_[l] B := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Finite ℤ_[l] A := d2
  exact ⟨A, d1, Module.Finite.of_restrictScalars_finite ℤ_[l] c.O A, hB⟩

end Factor

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

open UpperTheory.V.Base in
theorem UpperTheory.V.Th.rigII :
    U3.CohInp → Af.HypothesesH → AdL → RigII := by
  intro hC hH hL Ω _ _ _ K _ _ _ _ l hl c N _ e ψ D U g₁ hM S f hf ι hII W hW hext hdet hmod
  have hpt := U3.isPt_push D hM S f hf
  have he := D.gd.e_pos
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨B, hB, -, -, -, hBj, -⟩ := U3.dat_loc D
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ D.η.ker →
      B'.valuation ((l * N * (discr K).natAbs : ℕ) : Ω) < 1 := by
    intro B' h
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have hd : B'.valuation ((discr K : ℤ) : Ω) < 1 := by
      by_contra h4
      refine h fun s hs => ?_
      rw [D.η_ker]
      have key := GlobalTheory.UnramDiscr.embedding_eq B' h4 ((s : Ω →+* Ω).comp (algebraMap K Ω)) (algebraMap K Ω) (fun x => by
        refine hs.2 _ ((B'.valuation_le_one_iff _).mpr (GlobalTheory.UnramDiscr.mem_of_isIntegral B' ?_))
        exact (RingOfIntegers.isIntegral_coe x).map (algebraMap K Ω).toIntAlgHom)
      exact fun x => DFunLike.congr_fun key x
    have hd' : B'.valuation (((discr K).natAbs : ℕ) : Ω) < 1 := by
      rcases Int.natAbs_eq (discr K) with h1 | h1
      · rw [h1, Int.cast_natCast] at hd; exact hd
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg] at hd; exact hd
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((B'.valuation_le_one_iff _).2 (natCast_mem B' _))) hd'
  have hd0 : (discr K).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero K)
  have hlink : Pr.LinkHyp c N e D.η D.cc B (l * N * (discr K).natAbs) :=
    ⟨he, dvd_mul_right _ _, mul_ne_zero (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) hd0, hram, hB, D.conj⟩
  have hN := hH.litN
  have hframe := Fr.gd_ex ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
    Ω K l c N e ψ D B hB
  obtain ⟨A, hA1, hA2, hfA⟩ := exists_fac f hf
  haveI : Module.Finite ℤ_[l] A := Module.Finite.trans c.O A
  haveI := (UpperTheory.V.abelian₂.dvr_finite l A).1
  have hord := Pr.ordPt_of_gd hC.loc D g₁ hM U S B hBj A (f.codRestrict A hfA) (loc_of_int _)
  have hpush : UnitaryThreeInertia.push A.val (U3.push (f.codRestrict A hfA) S.r.hom) = U3.push f S.r.hom := rfl
  have hM1 : 1 ≤ N * (discr K).natAbs := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (NeZero.ne N) hd0)
  have hm : StrictAnti ![(e : ℤ), -(e : ℤ)] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  have hlev := (U3.typeII_ord hC D hM hpt hII W hext hW hdet).1
  have hwt : Af.IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) := by
    have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
    refine ⟨(discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W, hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have h1 : s ∈ D.η.ker := D.η_ker ▸ UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd s hs
    have h2 := hdet s
    rw [show D.η s = 1 from h1] at h2
    simpa using h2
  have hcyc := U3.typeII_irr_cyc hC D hM hpt hII W hext
  have hirrK : Af.IsIrr (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    ⟨top_ne_bot, fun _ _ _ => trivial, fun X hX hs => hcyc.2.2 X hX fun g v hv => hs g v hv⟩
  obtain ⟨nf, hnf⟩ := hmod
  have hadm : ∃ θ, Af.IsCycWt l 0 θ ∧ Af.DualTw W θ :=
      ⟨_, hwt, Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => by
        have hd : ((Matrix.GeneralLinearGroup.det.comp W s : (Qbar l)ˣ) : Qbar l) = (W s).val.det := rfl
        rw [hd, Matrix.det_fin_two (W s).val]
        ext i j
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i <;> fin_cases j <;> simp <;> ring⟩
  have haut := autKQ hH K Ω D.gd.quad l ι 2 (by norm_num) W 0 hW
    (Af.newformAut hH.toClassicalTheorems _ (by omega) nf l Ω ι W _ hnf) hadm hirrK
  have hunl := (unlRes K Ω l 2 _ _ W hM1).2 (fun i j => by
    fin_cases i <;> fin_cases j <;> simp <;> omega) hlev
  have hres : Continuous (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) := (galEmbTop ℚ K Ω).1.continuous
  have hfree := freePU hH K Ω D.gd.quad l D.gd.l_odd ι 2 le_rfl _ _ _ hM1 hm (hW.comp hres) haut hunl
  obtain ⟨π, hreg, -, hatt⟩ := haut
  refine rigEnd2 hH hL Ω l ι c N e ψ D.η D.cc g₁ B _ hlink (U3.dat_facts D).2.2.1 hframe A _ hord hII
    (fun g hg => Subtype.ext ((U3.typeII_facts hC D hM hpt hII).1 g hg)) K D.gd.quad D.η_ker W hW hext.1 hdet
    ⟨π, hreg, hatt⟩ fun A' hA' => ?_
  obtain ⟨g, hg, hc, α, hα, hp⟩ := hfree A' hA'
  exact ⟨AlgEquiv.restrictScalarsHom ℚ g, hg, hc, α, hα, hp⟩
