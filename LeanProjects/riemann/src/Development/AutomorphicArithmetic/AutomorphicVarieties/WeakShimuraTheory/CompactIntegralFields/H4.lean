import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegCosetFour
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsMemPowerSeriesCharRatiosNotIsOfFinOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.IsClosedZeroLocusMvPolynomialEvalAdicContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsStabilizerIndexDvdOfNotIrreducibleRestrict
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.StabClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsSignTwistCharpolyOfNotIrreducibleRestricti
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.SignCharEqOneOfCyclotomicSubOneNotIsUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsSignTwistCharEqOfCharpolyTwistInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.PowSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.NonComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsMemOpenInterSubgroupOfCosetwiseFiniteIndex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.h4 :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l]
      (r : W.Resid F O 4) (x : W.Point r), Nonempty F.Vl → (∀ v i, Alg.AdicCont (maximalIdeal x.A) fun g => ((x.ψ v i g : x.Aˣ) : x.A)) →
      (∀ v i j, i ≠ j → ∃ g, F.φ v g ∈ F.G' ∧ r.psib v i g = r.psib v j g ∧ x.ψ v i g ≠ x.ψ v j g) →
      U3.MatIrr ⊤ (W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)) →
      (∀ η : F.G₀ →* (ResidueField O)ˣ, η ^ 2 = 1 → (F.eps O (ResidueField O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) →
      (∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (r.chib i / r.chib j) ^ n ≠ 1) → x.N1 ∧ x.TypeI ∧ x.N3 := by
  intro l _ hl F O _ _ _ _ _ r x ⟨v⟩ _ ha hb hc hd
  classical
  have hlp : l.Prime := Fact.out
  haveI : CharP x.K l := charP_of_injective_algebraMap (algebraMap (ResidueField O) x.K).injective l
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI hN : F.G'.Normal := MonoidHom.normal_ker _
  let j : x.A →+* x.Fb := (algebraMap x.Fr x.Fb).comp (algebraMap x.A x.Fr)
  have hj : Function.Injective j := (algebraMap x.Fr x.Fb).injective.comp (IsFractionRing.injective x.A x.Fr)
  let ρ : F.G₀ →* Matrix (Fin 4) (Fin 4) x.Fb := W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)
  have hρ : ∀ g, ρ g = (W.mat x.ρ g).map j := fun g => rfl
  have two : ∀ (k : Type) [Field k] [CharP k l], (2 : k) ≠ 0 := fun k _ _ h =>
    hl ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 ((CharP.cast_eq_zero_iff k l 2).1 (by exact_mod_cast h)))
  haveI : CharP x.Fb l := charP_of_injective_ringHom (j.comp (PowerSeries.C : x.K →+* x.A)).injective l
  obtain ⟨cpR, cpL⟩ := h4Cp l F O 4 r x

  obtain ⟨g, hg, hfree⟩ := exists_mem_powerSeries_char_ratios_not_isOfFinOrder l (F.Gv v) x.K 4 (x.ψ v) (F.G'.comap (F.φ v)) fun a b hab => by
    obtain ⟨s, h1, h2, h3⟩ := ha v a b hab
    refine ⟨s, h1, ?_, h3⟩
    have h4 : ∀ i, PowerSeries.constantCoeff (x.ψ v i s : PowerSeries x.K) =
        algebraMap (ResidueField O) x.K (r.psib v i s) := fun i =>
      congrArg Units.val (DFunLike.congr_fun (x.ψ_red v i) s)
    rw [h4, h4, h2]
  let a : Fin 4 → x.Fbˣ := fun i => Units.map (j : x.A →* x.Fb) (x.ψ v i g)
  have hu : (ρ (F.φ v g)).charpoly = ∏ i, (X - C (a i : x.Fb)) := by
    rw [hρ, Matrix.charpoly_map, cpL, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hfa : ∀ s t, s ≠ t → ¬ IsOfFinOrder (a s / a t) := fun s t hst h => hfree s t hst <| by
    rw [← _root_.map_div] at h
    exact (Function.Injective.isOfFinOrder_iff (Units.map_injective (f := (j : x.A →* x.Fb)) hj)).1 h
  have hsep := charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder _ 4 _ a hu hfa
  have hcomm : commutator F.G₀ ≤ F.G' := Abelianization.commutator_subset_ker _

  have hI : x.TypeI := by
    by_contra hI
    obtain ⟨V, S, hV0, hV1, hNS, hS, hSi⟩ := exists_stabilizer_index_dvd_of_not_irreducible_restriction x.Fb F.G₀ 4 ρ hb F.G' hcomm
      ⟨_, hg, by simpa using hsep 1 one_pos⟩ hI
    obtain ⟨η, hη, hSη, hcp⟩ := exists_sign_twist_charpoly_of_not_irreducible_restriction x.Fb F.G₀ (two _) ρ hb S (hcomm.trans hNS) hSi fun h =>
      (h V fun s hs => (hS s).1 hs).elim hV0 hV1
    haveI : S.FiniteIndex := ⟨fun h => by simp [h] at hSi⟩
    have hSo : IsOpen (S : Set F.G₀) := by
      refine S.isOpen_of_isClosed_of_finiteIndex ?_
      have h1 := isClosed_setOf_matrix_stabilizes_submodule F.G₀ x.Fb 4 _ (Pr.linClosedOfAdic F.G₀ x.A x.Fb j hj 4 (W.mat x.ρ) x.cont) V
      convert h1 using 1
      ext s
      exact hS s
    have hk := sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit l hl F.G₀ (F.ε.comp F.η.ker.subtype) (F.ε_cont.comp continuous_subtype_val) η
      (Subgroup.isOpen_mono hSη hSo) (hNS.trans hSη)
    have h1 := hc (W.pushCh (Int.castRingHom (ResidueField O)) η) ?_ ?_
      (exists_sign_twist_char_eq_of_charpoly_twist_invariant x.Fb (ResidueField O) x.K x.A F.G₀ 4 (W.mat x.ρ) j _ _ r.chib η hj cpR hcp)
    · refine hη (MonoidHom.ext fun s => ?_)
      rcases Int.units_eq_one_or (η s) with h | h
      · exact h
      · have h2 := congrArg Units.val (DFunLike.congr_fun h1 s)
        simp only [MonoidHom.comp_apply, h] at h2
        exact absurd (by simp at h2; linear_combination -h2) (two (ResidueField O))
    · ext s
      rcases Int.units_eq_one_or (η s) with h | h <;> simp [h]
    · intro s hs
      have h2 : η s = 1 := hk s fun h => by
        have h3 := h.map ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O))
        have h4 : ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O)) ((F.ε.comp F.η.ker.subtype) s : ℤ_[l]) = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.1 hs)
        rw [map_sub, h4, map_one, sub_self] at h3
        exact not_isUnit_zero h3
      simp [MonoidHom.mem_ker, h2]
  refine ⟨fun w => ⟨fun s t hst h => ?_, fun s t hst h => ?_⟩, hI, ?_⟩
  · obtain ⟨y, -, -, h3⟩ := ha w s t hst
    exact h3 (by rw [h])
  · obtain ⟨y, h1, -, h3⟩ := ha w s t hst.ne
    have h4 : (F.ε.comp F.η.ker.subtype) (F.φ w y) = 1 := h1
    refine h3 ?_
    rw [h, MonoidHom.mul_apply, MonoidHom.comp_apply, W.GFrame.eps, MonoidHom.comp_apply, h4, map_one, mul_one]
  · have hsp : Submodule.span x.Fb (Set.range (ρ.comp F.G'.subtype)) = ⊤ :=
      KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hI N fun s hs => hN ⟨s, hs⟩
    have hsp' : Submodule.span x.Fb (Set.range ρ) = ⊤ :=
      KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hb N fun s _ => hN s
    have hnc := exists_noncommuting_images_in_finiteIndex_normal_subgroup x.Fb x.K x.A F.G₀ ρ j PowerSeries.constantCoeff
      (fun i => W.pushCh (algebraMap (ResidueField O) x.K) (r.chib i)) hj
      (fun s => ⟨(W.mat x.ρ s).charpoly, by rw [hρ, Matrix.charpoly_map], cpR s⟩) hsp' (by
        obtain ⟨s, t, h⟩ := hd
        refine ⟨s, t, fun n h0 h4 he => h n h0 h4 (MonoidHom.ext fun y => ?_)⟩
        apply Units.map_injective (f := (algebraMap (ResidueField O) x.K : ResidueField O →* x.K)) (RingHom.injective _)
        simpa using DFunLike.congr_fun he y) F.G' _ hg hsep
    refine exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex F.G₀ F.G' (fun s => (W.mat x.ρF s).charpoly.Separable) fun V hV σ => ?_
    obtain ⟨y, hy, hs⟩ := AlgebraTools.regCosetFour x.Fb F.G' (two _) (ρ.comp F.G'.subtype)
      (fun f => (isClosed_zeroLocus_mvPolynomial_eval_adicContinuous F.G₀ x.A x.Fb (Fin 4 × Fin 4) j hj (fun p s => W.mat x.ρ s p.1 p.2) (fun p => x.cont p.1 p.2) f).preimage
        continuous_subtype_val) hsp ⟨⟨_, hg⟩, a, hu, hfa⟩ (fun N _ h2 h3 => hnc N h2 h3) V hV σ
    refine ⟨y, hy, (Polynomial.separable_map (algebraMap x.Fr x.Fb)).1 ?_⟩
    rw [← Matrix.charpoly_map]
    exact hs
