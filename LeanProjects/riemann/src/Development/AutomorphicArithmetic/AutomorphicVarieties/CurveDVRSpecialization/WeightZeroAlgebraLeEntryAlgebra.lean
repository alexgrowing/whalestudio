import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.TriangularOfReducibleRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure

section SlopeTestRemainingChoices

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

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

private theorem exists_dvr {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] {σ : Type} [Finite σ] (b : σ → PadicAlgCl l)
    (hb : ∀ i, ‖b i‖ ≤ 1) :
    ∃ (A : Subalgebra O (PadicAlgCl l)), IsDiscreteValuationRing A ∧ Module.Finite O A ∧ ∀ i, b i ∈ A := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  let S : Set (PadicAlgCl l) := Set.range b ∪ algebraMap O _ '' s
  haveI : Finite S := ((Set.finite_range b).union (s.finite_toSet.image _)).to_subtype
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] S
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  let B := (integralClosure ℤ_[l] K).map f
  have hB : ∀ x ∈ S, IsIntegral ℤ_[l] x → x ∈ B := fun x hx hi =>
    ⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩
  have hO : ∀ a : O, algebraMap O (PadicAlgCl l) a ∈ B := by
    intro a
    have ha : a ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx =>
      exact hB _ (Or.inr ⟨x, hx, rfl⟩)
        ((Algebra.IsIntegral.isIntegral x).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l)))
    | zero => simpa using B.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact B.add_mem hx hy
    | smul c x _ hx => rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]; exact B.mul_mem (B.algebraMap_mem c) hx
  let A : Subalgebra O (PadicAlgCl l) := { B.toSubsemiring with algebraMap_mem' := hO }
  have d1 : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have d2 : Module.Finite ℤ_[l] B := Module.Finite.equiv e.toLinearEquiv
  refine ⟨A, d1, ?_, fun i => hB _ (Or.inl ⟨i, rfl⟩) ((int_iff_norm _).2 (hb i))⟩
  haveI : Module.Finite ℤ_[l] A := d2
  exact Module.Finite.of_restrictScalars_finite ℤ_[l] O A

private theorem mem_range_of_approx {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (J : Ideal R)
    [IsHausdorff J R] (hl : (l : R) ∈ J) {k : ℕ} (φ : (Fin k → ℤ_[l]) →+ R) (y : R)
    (h : ∀ n : ℕ, ∃ v, y - φ v ∈ J ^ n) : ∃ v, φ v = y := by
  have hp : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hcl : ∀ n : ℕ, IsClosed {v | y - φ v ∈ J ^ n} := fun n => by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro v hv
    refine ⟨(l : ℝ) ^ (-n : ℤ), zpow_pos hp _, fun w hw hw' => hv ?_⟩
    have h1 : ∀ i, ∃ u : ℤ_[l], u * (l : ℤ_[l]) ^ n = w i - v i := fun i => by
      rw [← Ideal.mem_span_singleton', ← PadicInt.norm_le_pow_iff_mem_span_pow, ← dist_eq_norm]
      exact (dist_le_pi_dist w v i).trans (le_of_lt hw)
    choose u hu using h1
    have h2 : w = v + (l ^ n : ℕ) • u := by
      funext i
      have := hu i
      rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow]
      linear_combination -this
    have h3 : y - φ v = (y - φ w) + (l : R) ^ n * φ u := by
      rw [h2, map_add, map_nsmul, nsmul_eq_mul, Nat.cast_pow]
      ring
    show y - φ v ∈ J ^ n
    rw [h3]
    exact add_mem hw' (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl n))
  obtain ⟨v, hv⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => {v | y - φ v ∈ J ^ n}) (fun n v hv => Ideal.pow_le_pow_right (Nat.le_succ n) hv) h
    (hcl 0).isCompact hcl
  refine ⟨v, (sub_eq_zero.1 (IsHausdorff.haus (inferInstance : IsHausdorff J R) _ fun n => ?_)).symm⟩
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Set.mem_iInter.1 hv n

private theorem map_reducible_three_dim {O : Type} [CommRing O] [IsLocalRing O] {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ)
    (g : G) : GG.map (residue O) (r0 η Ψ g) = rbar O η Ψ g := by
  refine SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (residue O) = tor _ (barChar O Ψ g)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

private theorem res_zpow {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    (t : Rˣ) (ht : res O R t = 1) (j : ℤ) : res O R ((t ^ j : Rˣ) : R) = 1 := by
  have h1 : Units.map (res O R : R →* ResidueField O) t = 1 := Units.ext ht
  have h2 := map_zpow (Units.map (res O R : R →* ResidueField O)) t j
  rw [h1, _root_.one_zpow] at h2
  exact congrArg Units.val h2

private def torLift {O : Type} [CommRing O] [IsLocalRing O] {G : Type} [Group G] [TopologicalSpace G]
    {η : G →* ℤˣ} {Ψ : G →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R) (t : Rˣ)
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
    rw [(conjBy_tor r.hom t).1, map_mul, res_zpow t ht, one_mul]

private theorem congOne_tor {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    (t : Rˣ) (ht : res O R t = 1) : CongOne (maximalIdeal R) (tor R t) := by
  intro a b
  rw [Matrix.sub_apply, tor_val]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ← res_eq_zero_iff O, map_sub, res_zpow t ht, map_one, sub_self]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_self]
    exact zero_mem _

private theorem loc_of_int {O R A : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A]
    [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A] (f : R →ₐ[O] A) : IsLocalHom f := by
  let g : R →+* f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' g hg
  have hl : IsLocalHom g := IsLocalHom.of_surjective _ hg
  haveI : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)
  have h2 : IsLocalHom (algebraMap f.range A) := Algebra.IsIntegral.isLocalHom _ _
  exact ⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩

private theorem diagonal_rep_off_diagonal_zero {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G) {a b : Fin 3}
    (h : a ≠ b) : (r0 η Ψ g).mat a b = 0 := by
  simp [GG.mat, tor_val, Matrix.diagonal_apply_ne _ h]

set_option linter.overlappingInstances false in
private theorem exists_pres {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [Group H] [TopologicalSpace H]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
    {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁)
    (hL : ConjStable U I) :
    ∃ W : WPres O ℤ S.R, (∀ i, W.z i ∈ maximalIdeal S.R) ∧
      (∀ i, W.z i ∈ Submodule.span O (entMon S.r.hom (W.wt i))) ∧
      ∀ g a b, (S.r.hom g).mat a b ∈ W.part (wt a b) := by
  have hm : ∀ s : Γ × Fin 3 × Fin 3, (S.r.hom s.1).mat s.2.1 s.2.2 -
      algebraMap O S.R ((r0 η Ψ s.1).mat s.2.1 s.2.2) ∈ maximalIdeal S.R := fun ⟨g, a, b⟩ => by
    have h1 := congrArg (fun x : GG 3 (ResidueField O) => x.mat a b) ((S.r.red g).trans (map_reducible_three_dim η Ψ g).symm)
    rw [← res_eq_zero_iff O, map_sub, AlgHom.commutes, sub_eq_zero]
    exact h1
  obtain ⟨W, u, hu, he⟩ := coord_grading O ℤ S.R (Γ × Fin 3 × Fin 3)
    (fun s => (S.r.hom s.1).mat s.2.1 s.2.2 - algebraMap O S.R ((r0 η Ψ s.1).mat s.2.1 s.2.2))
    (fun s => wt s.2.1 s.2.2) hm
    (fun R' _ _ _ f f' h => by
      have h1 : S.r.map f = S.r.map f' := by
        refine GLift.ext (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl)
        ext a b
        have := h (g, a, b)
        simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
        exact this
      exact ((S.rep R').2 _ ((S.rep R').1 f')).unique h1 rfl)
    (fun R' _ _ _ f t ht => by
      obtain ⟨hn, hk, hI⟩ := (S.rep R').1 f
      obtain ⟨f', hf', -⟩ := (S.rep R').2 (torLift (S.r.map f) (t (Multiplicative.ofAdd 1)) (ht _))
        ⟨(conjBy_tor _ _).2.2.1 _ _ hn, fun g hg => by
          show MulAut.conj _ ((S.r.map f).hom g) = 1
          rw [hk g hg, map_one], hL R' ((S.r.map f).comap ι hι)
            ((torLift (S.r.map f) (t (Multiplicative.ofAdd 1)) (ht _)).comap ι hι) _ (congOne_tor _ (ht _))
            (MonoidHom.ext fun _ => rfl) hI⟩
      have htj : ∀ j : ℤ, t (Multiplicative.ofAdd 1) ^ j = t (Multiplicative.ofAdd j) := fun j => by
        rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
      refine ⟨f', fun ⟨g, a, b⟩ => ?_⟩
      dsimp only
      rw [map_sub, map_sub f, AlgHom.commutes, AlgHom.commutes, mul_sub, ← htj (wt a b)]
      congr 1
      · exact (congrArg (fun x : GLift O η Ψ R' => (x.hom g).mat a b) hf').trans
          ((conjBy_tor (S.r.map f).hom _).1 g a b)
      · by_cases hab : a = b
        · simp [hab, wt]
        · simp [diagonal_rep_off_diagonal_zero η Ψ g hab])
  refine ⟨W, fun i => (hu i).1 ▸ hm _, fun i => ?_, fun g a b => ?_⟩
  · rw [(hu i).1, (hu i).2]
    obtain ⟨g, a, b⟩ := u i
    refine sub_mem (Submodule.subset_span ⟨[(g, a, b)], by simp, by simp⟩) ?_
    by_cases hab : a = b
    · subst hab
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], by simp [wt], by simp⟩)
    · rw [diagonal_rep_off_diagonal_zero η Ψ g hab, map_zero]
      exact zero_mem _
  · have h1 := he (g, a, b)
    have h2 : algebraMap O S.R ((r0 η Ψ g).mat a b) ∈ W.part (wt a b) := by
      by_cases hab : a = b
      · rw [hab, wt, sub_self, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : S.R) ∈ W.part 0)
      · rw [diagonal_rep_off_diagonal_zero η Ψ g hab, map_zero]
        exact zero_mem _
    simpa only [sub_add_cancel] using add_mem h1 h2

private theorem span_le_ent {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] (r : Γ →* GG 3 R) (j : ℤ) :
    Submodule.span O (entMon r j) ≤ Subalgebra.toSubmodule (entAlg O r) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨L, -, rfl⟩
  refine Subalgebra.list_prod_mem (entAlg O r) fun y hy => ?_
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
  exact Algebra.subset_adjoin ⟨_, _, _, rfl⟩

private theorem weight_zero_algebra_le_entry_algebra {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] (r : Γ →* GG 3 R) :
    weightZeroSubalgebra O r ≤ entAlg O r :=
  Algebra.adjoin_le fun _ hx => span_le_ent r 0 (Submodule.subset_span hx)

private theorem part_zero_le {l : ℕ} [Fact l.Prime] {O Γ R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [Group Γ] [CommRing R] [Algebra O R] (J : Ideal R) [IsHausdorff J R] (hl : (l : R) ∈ J)
    (r : Γ →* GG 3 R) (W : WPres O ℤ R) (hz : ∀ i, W.z i ∈ J)
    (hs : ∀ i, W.z i ∈ Submodule.span O (entMon r (W.wt i))) (hfin : Module.Finite O (weightZeroSubalgebra O r)) :
    ∀ x ∈ W.part 0, x ∈ weightZeroSubalgebra O r := by
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O (weightZeroSubalgebra O r)
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' ℤ_[l] (Fin n → O)
  let φ : (Fin k → ℤ_[l]) →+ R :=
    ((weightZeroSubalgebra O r).val.toLinearMap.toAddMonoidHom.comp f.toAddMonoidHom).comp g.toAddMonoidHom
  obtain ⟨v, hv⟩ := mem_range_of_approx J hl φ (W.π F) fun m => by
    obtain ⟨y, hy, hy'⟩ := Mop.approx W.wt W.π J (fun j => Submodule.span O (entMon r j))
      (Submodule.subset_span ⟨[], by simp, by simp⟩) (fun i j a ha b hb => by
        have := Submodule.mul_mem_mul ha hb
        rw [Submodule.span_mul_span] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_, ⟨L, hL, rfl⟩, _, ⟨L', hL', rfl⟩, rfl⟩
        exact ⟨L ++ L', by simp [hL, hL'], by simp⟩) hz hs 0 F hF m
    obtain ⟨v, hv⟩ := (hf.comp hg) ⟨y, Algebra.span_le_adjoin _ _ hy⟩
    exact ⟨v, by rwa [show φ v = y from congrArg Subtype.val hv]⟩
  show W.π F ∈ weightZeroSubalgebra O r
  rw [← hv]
  exact (f (g v)).2

private theorem A_le {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) (T : Subalgebra O R)
    (hz : ∀ i, W.z i ∈ T) (h0 : ∀ x ∈ W.part 0, x ∈ T) : W.A ≤ T := by
  have hm : ∀ b : W.σ →₀ ℕ, W.π (MvPowerSeries.monomial b 1) ∈ T := fun b => by
    induction b using Finsupp.induction_linear with
    | zero => simpa using one_mem _
    | add a b ha hb =>
      have : (MvPowerSeries.monomial (a + b) 1 : MvPowerSeries W.σ O) =
          MvPowerSeries.monomial a 1 * MvPowerSeries.monomial b 1 := by
        rw [MvPowerSeries.monomial_mul_monomial, one_mul]
      rw [this, map_mul]
      exact mul_mem ha hb
    | single i k =>
      rw [← MvPowerSeries.X_pow_eq, map_pow]
      exact pow_mem (hz i) k
  have hle : ⨆ j, W.part j ≤ Subalgebra.toSubmodule T := by
    refine iSup_le fun j => ?_
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨μ, -, hd⟩ := part_span O R ℤ W {n | Finsupp.weight W.wt n = j} j fun _ h => h
    obtain ⟨b, hb, rfl⟩ := hd f hf
    show W.π _ ∈ T
    rw [map_sum]
    exact sum_mem fun m _ => by
      rw [map_mul]
      exact mul_mem (h0 _ ⟨_, hb m, rfl⟩) (hm m)
  exact fun x hx => hle hx

private theorem exists_range {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] {R : Type} [CommRing R] [Algebra O R]
    (Ξ : R →ₐ[O] PadicAlgCl l) (hf : Module.Finite O Ξ.range) :
    ∃ (A : Subalgebra O (PadicAlgCl l)) (h : IsDiscreteValuationRing A) (_ : Module.Finite O A) (f : R →ₐ[O] A),
      IsAdicComplete (@maximalIdeal A _ h.toIsLocalRing) A ∧ ∀ x, (f x : PadicAlgCl l) = Ξ x := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' O Ξ.range
  have hint : ∀ x : Ξ.range, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    (int_iff_norm _).1 (isIntegral_trans (A := O) _ ((Algebra.IsIntegral.isIntegral x).map Ξ.range.val))
  obtain ⟨A, hA1, hA2, hbA⟩ := exists_dvr (O := O) (fun i => (p (Pi.single i 1) : PadicAlgCl l)) fun i => hint _
  have hmem : ∀ x, Ξ x ∈ A := fun x => by
    obtain ⟨v, hv⟩ := hp ⟨Ξ x, x, rfl⟩
    have h1 : Ξ x = (p v : PadicAlgCl l) := (congrArg Subtype.val hv).symm
    rw [h1, LinearMap.pi_apply_eq_sum_univ, AddSubmonoidClass.coe_finset_sum]
    refine sum_mem fun i _ => A.smul_mem ?_ _
    convert hbA i using 3
    funext j
    simp [Pi.single_apply, eq_comm]
  haveI : Module.Finite ℤ_[l] A := Module.Finite.trans O A
  exact ⟨A, hA1, hA2, Ξ.codRestrict A hmem, (UpperTheory.V.abelian₂.dvr_finite l A).1, fun _ => rfl⟩

private theorem push_eq {O Γ R K : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (u : Γ →* GG 3 R) (W : WPres O ℤ R) (hent : ∀ g a b, (u g).mat a b ∈ W.part (wt a b)) {T : Subalgebra O R}
    (hA : W.A ≤ T) (ξ : T →ₐ[O] K) (r : Γ →* GG 3 K) (hr : IsPush ξ u r) (t : Multiplicative ℤ →* Kˣ) (Ξ : R →ₐ[O] K)
    (hΞ : Ξ.comp W.A.val = act W.gr t (ξ.comp (Subalgebra.inclusion hA))) (A : Subalgebra O K) (f : R →ₐ[O] A)
    (hf : ∀ x, (f x : K) = Ξ x) :
    push A.val (push f u) = conjBy (tor _ (t (Multiplicative.ofAdd 1))) r := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => ?_)) ?_
  · refine Eq.trans ?_ ((conjBy_tor r _).1 g a b).symm
    obtain ⟨h, e⟩ := (hr g).2 a b
    rw [e, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    have h1 : Ξ ((u g).mat a b) = _ := (DFunLike.congr_fun hΞ ⟨_, W.part_le_A (hent g a b)⟩).trans
      (act_of_mem W.gr t _ (j := wt a b) (hent g a b))
    exact (hf _).trans h1
  · rw [(conjBy_tor r _).2.1, (hr g).1]
    rfl

end SlopeTestRemainingChoices

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.V.Pr.exists_ordPt_of_point :
    Loc.LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ → ∀ (U : D.ULoc) (S : D.Ring U g₁),
    FinA D g₁ → ∀ (B : ValuationSubring Ω), (∀ x, x ∈ B ↔ ‖D.j x‖ ≤ 1) → ∀ (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l) (r : G ℚ Ω →* GG 3 (PadicAlgCl l)), U3.IsPush ξ S.r.hom r →
      ∃ (A : Subalgebra c.O (PadicAlgCl l)) (_ : IsDiscreteValuationRing A) (_ : Module.Finite c.O A) (t : (PadicAlgCl l)ˣ) (r' : G ℚ Ω →* GG 3 A), OrdPt l D.η D.Ψ D.cc g₁ B r' ∧ UnitaryThreeInertia.push A.val r' = conjBy (tor _ t) r := by
  intro hP Ω _ _ _ K _ _ _ l _ c N _ e ψ D g₁ hg U S hfin B hB ξ r hr
  obtain ⟨hc, -, hl, hinj, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    IsFractionRing.comap_isAlgebraic_iff.2 (inferInstance : Algebra.IsAlgebraic ℚ_[l] (PadicAlgCl l))
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.extendScalars hinj
  obtain ⟨W, hz, hs, hent⟩ := exists_pres S (Loc.locGood hP D.loc U).conj
  have hlS : (l : S.R) ∈ maximalIdeal S.R := fun h => by
    have h1 : IsUnit (algebraMap c.O S.R (l : c.O)) := by rwa [map_natCast]
    exact hl (IsLocalHom.map_nonunit _ h1)
  have h0 := part_zero_le _ hlS S.r.hom W hz hs (hfin U S)
  have hA : W.A ≤ entAlg c.O S.r.hom :=
    A_le W _ (fun i => span_le_ent _ _ (hs i)) fun x hx => weight_zero_algebra_le_entry_algebra _ (h0 x hx)
  haveI := hfin U S
  have hfg : ((W.gr 0).map (ξ.comp (Subalgebra.inclusion hA)).toLinearMap).FG := by
    refine ((Module.Finite.fg_top (R := c.O) (M := weightZeroSubalgebra c.O S.r.hom)).map
      (ξ.comp (Subalgebra.inclusion (weight_zero_algebra_le_entry_algebra S.r.hom))).toLinearMap).of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, h0 x hx⟩, trivial, rfl⟩
  obtain ⟨t, Ξ, hΞ, hr'⟩ := Alg.points_finite c.O ℤ S.R W hz (PadicAlgCl l) _ hfg
  obtain ⟨A, hA1, hA2, f, hA3, hf⟩ := exists_range Ξ hr'
  haveI : IsLocalRing A := hA1.toIsLocalRing
  exact ⟨A, hA1, hA2, t (Multiplicative.ofAdd 1), U3.push f S.r.hom,
    ordPt_of_gd hP D g₁ hg U S B hB A f (loc_of_int f), push_eq _ W hent hA ξ r hr t Ξ hΞ A f hf⟩
