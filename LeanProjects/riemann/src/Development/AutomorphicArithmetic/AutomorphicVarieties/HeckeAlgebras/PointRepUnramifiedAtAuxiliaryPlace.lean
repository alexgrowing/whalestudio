import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNontrivialCharacterPgroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial IsLocalRing UpperTheory.V UpperTheory.V.W Topology
open UpperTheory.V.HV (Coef)

private theorem jv_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have hcast : ((l : PadicAlgCl l)) = (((l : ℚ_[l]) : PadicAlgCl l)) := by
    simp
  have hlt : ‖((l : PadicAlgCl l))‖ < 1 := by
    rw [hcast, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hpos : (0:ℝ) < 1 / (|C| + 1) := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hlt
  refine ⟨N, ?_⟩
  rw [norm_pow]
  have h0 : 0 ≤ ‖((l : PadicAlgCl l))‖ ^ N := by positivity
  calc ‖((l : PadicAlgCl l))‖ ^ N * C ≤ ‖((l : PadicAlgCl l))‖ ^ N * |C| :=
        mul_le_mul_of_nonneg_left (le_abs_self C) h0
    _ ≤ 1 / (|C| + 1) * |C| := mul_le_mul_of_nonneg_right hN.le (abs_nonneg C)
    _ ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        linarith

private theorem isFractionRing_coef_of_mem_iff_norm_le_one {l : ℕ} [hl : Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l)
    (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1) [Algebra c.O E]
    (hφ : ∀ a : c.O, ((algebraMap c.O E a : E) : PadicAlgCl l) = a) : IsFractionRing c.O E := by
  have hinj : Function.Injective (algebraMap c.O E) := by
    intro a b hab
    apply Subtype.ext
    rw [← hφ a, ← hφ b, hab]
  have hlO : ((l : PadicAlgCl l)) ∈ c.O := by
    exact Subalgebra.natCast_mem _ _
  have hl0 : ((l : PadicAlgCl l)) ≠ 0 := by
    exact_mod_cast hl.out.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
    refine IsUnit.mk0 _ ?_
    intro h0
    apply hx0
    apply hinj
    rw [h0, map_zero]
  · intro z
    obtain ⟨N, hN⟩ := jv_small (l := l) ‖(z : PadicAlgCl l)‖
    have hmem : (l : PadicAlgCl l) ^ N * z ∈ c.O := by
      rw [hc]
      refine ⟨E.mul_mem (pow_mem (E.natCast_mem l) N) z.2, ?_⟩
      rw [norm_mul]
      exact hN
    have hs : (⟨(l : PadicAlgCl l) ^ N, c.O.pow_mem hlO N⟩ : c.O) ∈ nonZeroDivisors c.O := by
      apply mem_nonZeroDivisors_of_ne_zero
      intro h
      apply pow_ne_zero N hl0
      exact congrArg Subtype.val h
    refine ⟨⟨⟨_, hmem⟩, ⟨_, hs⟩⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, hφ]
    ring
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

private theorem jv_model {l : ℕ} [hl : Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {n : ℕ}
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (r : G →* GL (Fin n) (PadicAlgCl l)) (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j)
    (hE : ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ E) :
    ∃ (Q : GL (Fin n) (PadicAlgCl l)) (r₀ : G →* GL (Fin n) c.O),
      ∀ g, r g * Q = Q * pushRep (algebraMap c.O (PadicAlgCl l)) r₀ g := by
  classical
  letI : Algebra c.O E :=
    ((algebraMap c.O (PadicAlgCl l)).codRestrict E (fun a => ((hc a).1 a.2).1)).toAlgebra
  have hφ : ∀ a : c.O, ((algebraMap c.O E a : E) : PadicAlgCl l) = a := fun a => rfl
  haveI := isFractionRing_coef_of_mem_iff_norm_le_one E c hc hφ
  let ι : E →+* PadicAlgCl l := algebraMap E (PadicAlgCl l)
  have hι : ∀ e : E, ι e = (e : PadicAlgCl l) := fun e => rfl
  have hinjM : Function.Injective (ι.mapMatrix : Matrix (Fin n) (Fin n) E →+* _) := by
    intro A A' h
    ext i j
    have := congrFun (congrFun h i) j
    exact this
  let M : G →* Matrix (Fin n) (Fin n) E :=
    { toFun := fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j, hE g i j⟩
      map_one' := by
        apply hinjM
        ext i j
        simp [hι, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := by
        intro g h
        apply hinjM
        ext i j
        simp [hι, Matrix.mul_apply] }
  have hM : ∀ g, ι.mapMatrix (M g) = (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
    intro g
    ext i j
    rfl
  let rE : G →* GL (Fin n) E := M.toHomUnits
  have hb : ∀ i j, ∃ C : ℝ, ∀ g, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ C := by
    intro i j
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (isCompact_range (hr i j)).isBounded
    exact ⟨C, fun g => hC _ ⟨g, rfl⟩⟩
  choose C hC using hb
  obtain ⟨N, hN⟩ := jv_small (l := l) (∑ i, ∑ j, |C i j|)
  have hbd : ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ ∑ i, ∑ j, |C i j| := by
    intro g i j
    refine (hC i j g).trans ((le_abs_self _).trans ?_)
    refine (Finset.single_le_sum (f := fun j => |C i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans ?_
    exact Finset.single_le_sum (f := fun i => ∑ j, |C i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hlO : ((l : PadicAlgCl l)) ∈ c.O := Subalgebra.natCast_mem _ _
  have hl0 : ((l : PadicAlgCl l)) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  let d : c.O := ⟨(l : PadicAlgCl l) ^ N, c.O.pow_mem hlO N⟩
  have hd : d ≠ 0 := by
    intro h
    apply pow_ne_zero N hl0
    exact congrArg Subtype.val h
  have hint : ∀ g i j, ∃ a : c.O, algebraMap c.O E d * (rE g : Matrix (Fin n) (Fin n) E) i j = algebraMap c.O E a := by
    intro g i j
    have hmem : (l : PadicAlgCl l) ^ N * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ c.O := by
      rw [hc]
      refine ⟨E.mul_mem (pow_mem (E.natCast_mem l) N) (hE g i j), ?_⟩
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hbd g i j) (norm_nonneg _)).trans hN
    exact ⟨⟨_, hmem⟩, Subtype.ext rfl⟩
  obtain ⟨Q, r₀, hQ⟩ := Pa.Det.latInt rE d hd hint
  refine ⟨Matrix.GeneralLinearGroup.map ι Q, r₀, fun g => ?_⟩
  have key := congrArg (Matrix.GeneralLinearGroup.map ι) (hQ g)
  rw [map_mul, map_mul] at key
  have h1 : Matrix.GeneralLinearGroup.map ι (rE g) = r g := by
    ext i j
    rfl
  have h2 : Matrix.GeneralLinearGroup.map ι (pushRep (algebraMap c.O E) r₀ g) =
      pushRep (algebraMap c.O (PadicAlgCl l)) r₀ g := by
    ext i j
    rfl
  rw [h1, h2] at key
  exact key

private theorem jv_cont {l : ℕ} [hl : Fact l.Prime] {G : Type} [TopologicalSpace G]
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (f : G → c.O) (hf : Continuous fun g => (f g : PadicAlgCl l)) (N : ℕ) :
    IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal c.O ^ N) (f g) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hm : maximalIdeal c.O ^ N = Ideal.span {ϖ ^ N} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow]
  have hne : ((ϖ ^ N : c.O) : PadicAlgCl l) ≠ 0 := by
    have h0 : ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ.ne_zero
    exact fun h => h0 (Subtype.ext h)
  have hδ : 0 < ‖((ϖ ^ N : c.O) : PadicAlgCl l)‖ := norm_pos_iff.2 hne
  have key : ∀ z : c.O, ‖(z : PadicAlgCl l)‖ < ‖((ϖ ^ N : c.O) : PadicAlgCl l)‖ →
      z ∈ maximalIdeal c.O ^ N := by
    intro z hz
    rw [hm, Ideal.mem_span_singleton']
    have hq : (z : PadicAlgCl l) / ((ϖ ^ N : c.O) : PadicAlgCl l) ∈ c.O := by
      rw [hc]
      refine ⟨E.div_mem ((hc _).1 z.2).1 ((hc _).1 (ϖ ^ N).2).1, ?_⟩
      rw [norm_div, div_le_one hδ]
      exact hz.le
    refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
    show (z : PadicAlgCl l) / ((ϖ ^ N : c.O) : PadicAlgCl l) * ((ϖ ^ N : c.O) : PadicAlgCl l) = z
    exact div_mul_cancel₀ _ hne
  rw [IsLocallyConstant.iff_exists_open]
  intro g0
  refine ⟨(fun g => (f g : PadicAlgCl l)) ⁻¹' Metric.ball (f g0 : PadicAlgCl l) ‖((ϖ ^ N : c.O) : PadicAlgCl l)‖,
    Metric.isOpen_ball.preimage hf, Metric.mem_ball_self hδ, ?_⟩
  intro g hg
  rw [Ideal.Quotient.eq]
  apply key
  simpa [dist_eq_norm] using hg

private theorem norm_algebraMap_padicInt_padicAlgCl_le_one' {l : ℕ} [Fact l.Prime] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  simpa using a.norm_le_one

private theorem norm_coe_coef_integer_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := c.O)
  have hM : ∀ z : c.O, ‖(z : PadicAlgCl l)‖ ≤ 1 + ∑ t ∈ s, ‖(t : PadicAlgCl l)‖ := by
    intro z
    have hz : z ∈ Submodule.span ℤ_[l] (s : Set c.O) := by
      rw [hs]
      trivial
    induction hz using Submodule.span_induction with
    | mem t ht =>
      have : ‖(t : PadicAlgCl l)‖ ≤ ∑ t ∈ s, ‖(t : PadicAlgCl l)‖ :=
        Finset.single_le_sum (f := fun t : c.O => ‖(t : PadicAlgCl l)‖) (fun _ _ => norm_nonneg _) ht
      linarith
    | zero =>
      have : (0 : ℝ) ≤ ∑ t ∈ s, ‖(t : PadicAlgCl l)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      simp only [ZeroMemClass.coe_zero, norm_zero]
      linarith
    | add a b _ _ ha hb =>
      rw [Subalgebra.coe_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul a z _ hz =>
      rw [Subalgebra.coe_smul, Algebra.smul_def, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_padicInt_padicAlgCl_le_one' a)).trans hz
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 + ∑ t ∈ s, ‖(t : PadicAlgCl l)‖) h
  have := hM (x ^ k)
  rw [SubmonoidClass.coe_pow, norm_pow] at this
  linarith

private theorem exists_finiteDimensional_ge_forall_coef_integer_mem {l : ℕ} [Fact l.Prime] (c : Coef l)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ K ≤ E ∧
      ∀ x : c.O, (x : PadicAlgCl l) ∈ E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := c.O)
  set S : Set (PadicAlgCl l) := (fun t : c.O => (t : PadicAlgCl l)) '' (s : Set c.O)
  haveI : Finite S := Set.Finite.image _ s.finite_toSet
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨K ⊔ IntermediateField.adjoin ℚ_[l] S, inferInstance, le_sup_left, fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set c.O) := by
    rw [hs]
    trivial
  induction hx using Submodule.span_induction with
  | mem t ht =>
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] S ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨t, ht, rfl⟩)
  | zero => exact zero_mem _
  | add a b _ _ ha hb =>
    rw [Subalgebra.coe_add]
    exact add_mem ha hb
  | smul a z _ hz =>
    rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) hz

private theorem isLocalHom_inclusion_coef_of_le {l : ℕ} [Fact l.Prime] (c c' : Coef l) (hle : c.O ≤ c'.O) :
    IsLocalHom (Subalgebra.inclusion hle).toRingHom := by
  refine RingHom.IsIntegral.isLocalHom ?_ (Subalgebra.inclusion_injective hle)
  intro z
  obtain ⟨p, hp, hpz⟩ := (Algebra.IsIntegral.isIntegral z : IsIntegral ℤ_[l] z)
  refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  convert hpz
  exact RingHom.ext fun a => rfl

private theorem resid_h4_lemma_6 {l : ℕ} [Fact l.Prime] (c c' : Coef l) (hle : c.O ≤ c'.O)
    (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] (y : R →ₐ[c.O] PadicAlgCl l) (a : R) (t : c'.O)
    (ht : (t : PadicAlgCl l) = y a) :
    haveI := isLocalHom_inclusion_coef_of_le c c' hle
    residue c'.O t = ResidueField.map (Subalgebra.inclusion hle).toRingHom (Alg.res c.O R a) := by
  haveI := isLocalHom_inclusion_coef_of_le c c' hle
  obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (Alg.res c.O R a)
  have hres : ∀ x : R, ResidueField.map (algebraMap c.O R) (Alg.res c.O R x) = residue R x := by
    intro x
    simp only [Alg.res]
    exact (RingEquiv.ofBijective _ (Alg.resMap_bijective c.O R)).apply_symm_apply _
  have hm : a - algebraMap c.O R b ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, ← hres, map_sub, AlgHom.commutes, ResidueField.algebraMap_eq, hb, sub_self,
      map_zero]
  obtain ⟨-, a0, ha0, -, hbd⟩ := (GradeZeroInterpolatingElement.coPt c R).1 y
  have hn : ‖y (a - algebraMap c.O R b)‖ < 1 :=
    (hbd 1 _ (by rwa [pow_one])).trans_lt (by rwa [pow_one])
  have hy : y (a - algebraMap c.O R b) =
      ((t - (Subalgebra.inclusion hle).toRingHom b : c'.O) : PadicAlgCl l) := by
    rw [map_sub, AlgHom.commutes, ← ht]
    rfl
  have hmax : t - (Subalgebra.inclusion hle).toRingHom b ∈ maximalIdeal c'.O := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 := norm_coe_coef_integer_le_one c' (↑u⁻¹ : c'.O)
    have h2 : ((↑u : c'.O) : PadicAlgCl l) * ((↑u⁻¹ : c'.O) : PadicAlgCl l) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]
      rfl
    rw [hu, ← hy] at h2
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one] at h3
    have := mul_le_of_le_one_right (norm_nonneg (y (a - algebraMap c.O R b))) h1
    linarith
  have h0 := (residue_eq_zero_iff _).2 hmax
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, ← ResidueField.map_residue, hb]

private theorem jv_local {p l : ℕ} [Fact p.Prime] [hl : Fact l.Prime] (hpl : p ≠ l) {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (φ : G →* GQ p) (hφ : IsOpenEmbedding φ) (c : Coef l) (R : Type) [CommRing R]
    [Algebra c.O R] [Alg.IsCO c.O R] (y : R →ₐ[c.O] PadicAlgCl l) {n : ℕ} (ρ : G →* GL (Fin n) (PadicAlgCl l)) (hρ : Continuous ρ)
    (κ : G →* (ResidueField c.O)ˣ) (hκ : ∀ g, φ g ∈ Loc.Iq p → κ g = 1)
    (hω : ∃ g, residue c.O (algebraMap ℤ_[l] c.O (Loc.cyc p l (φ g) : ℤ_[l])) ≠ 1) (χ : G → R[X])
    (h1 : ∀ g, (χ g).map (y : R →+* PadicAlgCl l) = (mat ρ g).charpoly)
    (h2 : ∀ g, (χ g).map (Alg.res c.O R : R →+* ResidueField c.O) = (X - C (κ g : ResidueField c.O)) ^ n) :
    ∀ g, φ g ∈ Loc.Iq p → ρ g = 1 := by
  have hρe : ∀ i j, Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j :=
    fun i j => (Units.continuous_val.comp hρ).matrix_elem i j
  obtain ⟨K, hKfd, hK⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l G n ρ hρe
  obtain ⟨E, hEfd, hKE, hcE⟩ := exists_finiteDimensional_ge_forall_coef_integer_mem c K
  obtain ⟨c', hc'⟩ := X.So.coefOf l E
  have hle : c.O ≤ c'.O := fun x hx => (hc' x).2 ⟨hcE ⟨x, hx⟩, norm_coe_coef_integer_le_one c ⟨x, hx⟩⟩
  obtain ⟨Q, r₀, hQ⟩ := jv_model E c' hc' ρ hρe (fun g i j => hKE (hK g i j))
  obtain ⟨hcomp, hfin, hlmem, -, -, -⟩ := abelian₂.dvr_finite l c'.O
  haveI := hcomp
  haveI := hfin
  haveI : CharP (ResidueField c'.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c'.O)]
    exact (residue_eq_zero_iff _).2 hlmem)
  haveI := isLocalHom_inclusion_coef_of_le c c' hle
  have hconj : ∀ g, pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q := by
    intro g
    rw [mul_assoc, hQ g, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcont : ∀ i j, Continuous fun g => ((r₀ g : Matrix (Fin n) (Fin n) c'.O) i j : PadicAlgCl l) := by
    intro i j
    have e : (fun g => ((r₀ g : Matrix (Fin n) (Fin n) c'.O) i j : PadicAlgCl l)) = fun g =>
        (((Q⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) *
          (ρ g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) * (Q : Matrix (Fin n) (Fin n) (PadicAlgCl l))) i j := by
      funext g
      rw [← Units.val_mul, ← Units.val_mul, ← hconj g]
      rfl
    rw [e]
    exact ((continuous_const.matrix_mul (Units.continuous_val.comp hρ)).matrix_mul continuous_const).matrix_elem i j
  have hcp : ∀ g, ((r₀ g : Matrix (Fin n) (Fin n) c'.O).charpoly).map (algebraMap c'.O (PadicAlgCl l)) =
      (χ g).map (y : R →+* PadicAlgCl l) := by
    intro g
    rw [← Matrix.charpoly_map, h1 g]
    have e : (r₀ g : Matrix (Fin n) (Fin n) c'.O).map (algebraMap c'.O (PadicAlgCl l)) =
        ((Q : Matrix (Fin n) (Fin n) (PadicAlgCl l)))⁻¹ * (ρ g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) *
          (Q : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
      rw [← Matrix.coe_units_inv, ← Units.val_mul, ← Units.val_mul, ← hconj g]
      rfl
    rw [e, Matrix.charpoly_units_conj']
    rfl
  set ιr := ResidueField.map (Subalgebra.inclusion hle).toRingHom with hιr
  set κ' : G →* (ResidueField c'.O)ˣ := (Units.map ιr.toMonoidHom).comp κ with hκ'
  have hred : ∀ g, ((r₀ g : Matrix (Fin n) (Fin n) c'.O).map (residue c'.O)).charpoly =
      (X - C (κ' g : ResidueField c'.O)) ^ n := by
    intro g
    rw [Matrix.charpoly_map]
    have e : ((r₀ g : Matrix (Fin n) (Fin n) c'.O).charpoly).map (residue c'.O) =
        ((χ g).map (Alg.res c.O R : R →+* ResidueField c.O)).map ιr := by
      ext k
      rw [coeff_map, coeff_map, coeff_map]
      apply resid_h4_lemma_6 c c' hle R y
      have := congrArg (fun p => p.coeff k) (hcp g)
      simp only [coeff_map] at this
      exact this
    rw [e, h2 g]
    simp [hκ', Polynomial.map_pow]
  have hω' : ∃ g, residue c'.O ↑(Loc.cycA p l c'.O (φ g)) ≠ 1 := by
    obtain ⟨g, hg⟩ := hω
    refine ⟨g, fun h => hg ?_⟩
    have e : (↑(Loc.cycA p l c'.O (φ g)) : c'.O) =
        (Subalgebra.inclusion hle).toRingHom (algebraMap ℤ_[l] c.O (Loc.cyc p l (φ g) : ℤ_[l])) := rfl
    rw [e, ← ResidueField.map_residue] at h
    apply ιr.injective
    rw [h, map_one]
  have key := (Loc.v0b hpl φ hφ c'.O κ' (fun g hg => by simp [hκ', hκ g hg]) hω' r₀
    (fun N i j => jv_cont E c' hc' _ (hcont i j) N) hred).1
  intro g hg
  have hp1 : pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show algebraMap c'.O (PadicAlgCl l) ((r₀ g : Matrix (Fin n) (Fin n) c'.O) i j) = _
    rw [key g hg, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e := hQ g
  rw [hp1, mul_one] at e
  exact mul_right_cancel (e.trans (one_mul Q).symm)

theorem UpperTheory.V.Hi.point_rep_unramified_at_auxiliary_place {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} (hn : 1 ≤ n) {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)
    (h : r.V0ok) (x : B.B →ₐ[c.O] PadicAlgCl l) (ρ : V.frame.G₀ →* GL (Fin n) (PadicAlgCl l)) (hρ : Continuous ρ)
    (hx : B.u.D.map (x : B.B →+* PadicAlgCl l) = GDet.ofRep (mat ρ)) : ∀ g ∈ V.frame.I0, ρ g = 1 := by
  intro g hg
  change g ∈ Subgroup.map V.pr (Ine (s.A s.v0)) at hg
  obtain ⟨d, hd, rfl⟩ := hg
  haveI : Fact s.p.Prime := ⟨s.p_prime⟩
  have hpv : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    have hcard : Nat.card (𝓞 (Lp L) ⧸ s.v0.asIdeal) = s.p := s.norm_v0_eq_one
    haveI : Finite (𝓞 (Lp L) ⧸ s.v0.asIdeal) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact s.p_prime.ne_zero)
    letI := Fintype.ofFinite (𝓞 (Lp L) ⧸ s.v0.asIdeal)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨j, hj⟩ := (Loc.decEmb (F := Lp L) (Ω := Ω) (v := s.p)).1 (s.A s.v0) s.v0 (s.hA s.v0) hpv
  obtain ⟨-, φ, hφo, -, -, hIne, hcyc, -⟩ := (Loc.decEmb (F := Lp L) (Ω := Ω) (v := s.p)).2 j
  have hDr : Dec (Loc.placeJ j) ≤ (resP L Ω).range := hj ▸ s.19 s.v0 (Or.inr (Or.inr rfl))
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : ↥(Dec (Loc.placeJ j)) →* V.frame.G₀,
      ∀ x, (ψ0 x).1 = toGS Ω V.S' (x : G (Lp L) Ω) :=
    ⟨MonoidHom.codRestrict ((toGS Ω V.S').comp (Dec (Loc.placeJ j)).subtype) V.η.ker
      (fun x => (V.6 x).2 (hDr x.2)), fun _ => rfl⟩
  have hpr : ∀ x : ↥(Dec (Loc.placeJ j)), ∃ e : G L Ω, e ∈ Dec (s.A s.v0) ∧
      resP L Ω e = x ∧ ψ0 x = V.pr e := by
    intro x
    obtain ⟨e, he⟩ := hDr x.2
    refine ⟨e, ?_, he, ?_⟩
    · have hx := x.2
      rw [← he, hj] at hx
      exact hx
    · apply Subtype.ext
      rw [hψ0, ← he]
      rfl
  have hψc : Continuous ψ0 := by
    apply continuous_induced_rng.2
    exact ((continuous_toGS Ω V.S').comp continuous_subtype_val).congr (fun t => (hψ0 t).symm)
  haveI : CompactSpace ↥(Dec (Loc.placeJ j)) :=
    isCompact_iff_compactSpace.1 (isClosed_Dec (F := Lp L) (Loc.placeJ j)).isCompact
  have hD0 : ∀ x : ↥(Dec (Loc.placeJ j)), ψ0 x ∈ V.frame.D0 := by
    intro x
    obtain ⟨e, he, -, hx⟩ := hpr x
    rw [hx]
    exact Subgroup.mem_map_of_mem _ he
  have hIq : ∀ t : ↥(Dec (Loc.placeJ j)), φ t ∈ Loc.Iq s.p → ψ0 t ∈ V.frame.I0 := by
    intro t ht
    obtain ⟨e, -, he, hte⟩ := hpr t
    rw [hte]
    refine Subgroup.mem_map_of_mem _ ?_
    have h1 := (hIne t).1 ht
    rw [← he, hj] at h1
    exact h1
  delta Resid.V0ok at h
  obtain ⟨hI0, hDeq, g1, hg1, hg1e⟩ := h
  have i0 : Fin n := ⟨0, hn⟩
  have hκ : ∀ t, φ t ∈ Loc.Iq s.p → ((r.chib i0).comp ψ0) t = 1 := fun t ht => hI0 i0 (hIq t ht)
  change g1 ∈ Subgroup.map V.pr (Dec (s.A s.v0)) at hg1
  obtain ⟨e1, he1, rfl⟩ := hg1
  have hω : ∃ t, residue c.O (algebraMap ℤ_[l] c.O (Loc.cyc s.p l (φ t) : ℤ_[l])) ≠ 1 := by
    refine ⟨⟨resP L Ω e1, by rw [hj]; exact he1⟩, ?_⟩
    rw [hcyc l]
    intro hcon
    apply hg1e
    apply Units.ext
    delta GFrame.eps
    have hε1 : (V.frame.ε (V.pr e1).1 : ℤ_[l]ˣ) = cycZ (Lp L) Ω l (resP L Ω e1) :=
      DFunLike.congr_fun V.hε (resP L Ω e1)
    simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, Subgroup.coe_subtype, hε1,
      MonoidHom.coe_coe, RingHom.comp_apply, Units.val_one, IsLocalRing.ResidueField.algebraMap_eq]
    change ((residue c.O).comp (algebraMap ℤ_[l] c.O)) ((V.frame.ε (V.pr e1).1 : ℤ_[l]ˣ) : ℤ_[l]) = 1
    rw [hε1, RingHom.comp_apply]
    exact hcon
  have hs : ∀ (A' : Type) [CommRing A'] (f : B.B →+* A') (t : ↥(Dec (Loc.placeJ j))),
      MonoidAlgebra.mapRingHom V.frame.G₀ f (MonoidAlgebra.single (ψ0 t) 1) = MonoidAlgebra.single (ψ0 t) 1 := by
    intro A' _ f t
    simp [MonoidAlgebra.mapRingHom]
  have key := jv_local (p := s.p) (l := l) s.p_ne φ hφo c B.B x (ρ.comp ψ0) (hρ.comp hψc)
    ((r.chib i0).comp ψ0) hκ hω (fun t => B.u.D.chi (MonoidAlgebra.single (ψ0 t) 1)) ?_ ?_
  · have hdD : resP L Ω d ∈ Dec (Loc.placeJ j) := by
      rw [hj]
      exact Ine_le_Dec _ hd
    have hφt : φ ⟨resP L Ω d, hdD⟩ ∈ Loc.Iq s.p := by
      rw [hIne]
      show resP L Ω d ∈ Ine (Loc.placeJ j)
      rw [hj]
      exact hd
    have h0 := key _ hφt
    have hψt : ψ0 ⟨resP L Ω d, hdD⟩ = V.pr d := by
      apply Subtype.ext
      rw [hψ0]
      rfl
    rw [MonoidHom.comp_apply, hψt] at h0
    exact h0
  · intro t
    have e := (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* PadicAlgCl l)).1 (MonoidAlgebra.single (ψ0 t) 1)
    rw [hs, hx] at e
    rw [← e, (AlgebraTools.Det.repApi (mat ρ)).2.1]
    rfl
  · intro t
    have e := (AlgebraTools.Det.mapApi B.u.D (Alg.res c.O B.B : B.B →+* ResidueField c.O)).1
      (MonoidAlgebra.single (ψ0 t) 1)
    rw [hs, B.u.red] at e
    rw [← e]
    delta Resid.Dbar
    rw [(AlgebraTools.Det.repApi (diagRep r.chib)).2.1]
    change (Matrix.diagonal fun i => ((r.chib i (ψ0 t) : (ResidueField c.O)ˣ) : ResidueField c.O)).charpoly = _
    rw [Matrix.charpoly_diagonal]
    have hc : ∀ i, r.chib i (ψ0 t) = r.chib i0 (ψ0 t) := fun i => hDeq _ (hD0 t) i i0
    simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin, MonoidHom.comp_apply]
