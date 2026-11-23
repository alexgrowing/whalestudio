import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.LiesOver
import GroundTheory.LocalFields.ExtensionsOfDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Polynomial IsDedekindDomain NumberField IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal
  FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {v : HeightOneSpectrum (𝓞 K.1)}
  (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

section Surjective

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

theorem localDecompHom_surjective : Function.Surjective (localDecompHom ι F) := by
  intro τ
  let _ : Algebra ((placeOfEmbedding ι F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) := (completionEmbedding ι F).toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι F).1.adicCompletion F.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((completionEmbedding ι F).commutes a).symm
  let ψ := decompositionToLocal v (placeOfEmbedding ι F).1 τ
  refine ⟨ψ.liftNormal (AlgebraicClosure (v.adicCompletion K.1)), Subtype.ext ?_⟩
  rw [coe_localDecompHom, decompHom_eq_iff]
  intro x
  rw [embedLevel_apply, embedLevel_apply, ← completionEmbedding_algebraMap,
    ← completionEmbedding_algebraMap]
  change algebraMap _ (AlgebraicClosure (v.adicCompletion K.1))
      (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) (τ.1 x)) =
    (ψ.liftNormal (AlgebraicClosure (v.adicCompletion K.1))) (algebraMap _ _
      (algebraMap F.1 ((placeOfEmbedding ι F).1.adicCompletion F.1) x))
  rw [AlgEquiv.liftNormal_commutes, decompositionToLocal_algebraMap]

end Surjective

section Generic

variable {L : Type*} [NormedField L]

theorem exists_norm_coeff_le (a : L[X]) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i < a.natDegree, ‖a.coeff i‖ ≤ M := by
  refine ⟨1 + ∑ i ∈ Finset.range a.natDegree, ‖a.coeff i‖, ?_, fun i hi ↦ ?_⟩
  · have : 0 ≤ ∑ i ∈ Finset.range a.natDegree, ‖a.coeff i‖ :=
      Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    linarith
  · have := Finset.single_le_sum (f := fun j ↦ ‖a.coeff j‖) (fun j _ ↦ norm_nonneg _)
      (Finset.mem_range.2 hi)
    linarith

theorem norm_coeff_scaleRoots_le_one {a : L[X]} (ha : a.Monic) {M : ℝ} (hM : 1 ≤ M)
    (haM : ∀ i < a.natDegree, ‖a.coeff i‖ ≤ M) {c : L} (hc : ‖c‖ ≤ M⁻¹) (i : ℕ) :
    ‖(scaleRoots a c).coeff i‖ ≤ 1 := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hc1 : ‖c‖ ≤ 1 := hc.trans (inv_le_one_of_one_le₀ hM)
  rw [coeff_scaleRoots, norm_mul, norm_pow]
  by_cases hi : i < a.natDegree
  · have h2 : ‖c‖ ^ (a.natDegree - i) ≤ ‖c‖ := pow_le_of_le_one (norm_nonneg _) hc1 (by omega)
    have h3 : ‖a.coeff i‖ * ‖c‖ ≤ M * M⁻¹ :=
      mul_le_mul (haM i hi) hc (norm_nonneg _) hM0.le
    rw [mul_inv_cancel₀ hM0.ne'] at h3
    exact (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans h3
  · rw [Nat.sub_eq_zero_of_le (not_lt.1 hi), pow_zero, mul_one]
    rcases (not_lt.1 hi).eq_or_lt with h | h
    · rw [← h, ha.coeff_natDegree, norm_one]
    · rw [coeff_eq_zero_of_natDegree_lt h, norm_zero]
      exact zero_le_one

theorem map_monicOfCoeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (c : Fin n → R) :
    (GroundTheory.LocalField.monicOfCoeffs c).map φ = GroundTheory.LocalField.monicOfCoeffs (fun i ↦ φ (c i)) := by
  simp only [GroundTheory.LocalField.monicOfCoeffs, Polynomial.map_add, Polynomial.map_pow, map_X,
    Polynomial.map_sum, Polynomial.map_mul, map_C]

theorem exists_adjoin_eq_of_dense {k L : Type*} [Field k] [NontriviallyNormedField L] [CompleteSpace L]
    [IsUltrametricDist L] [Algebra k L] (hk : DenseRange (algebraMap k L)) {f : L[X]}
    (hfm : f.Monic) (hirr : Irreducible f) (hsep : f.Separable) (hfc : ∀ i, ‖f.coeff i‖ ≤ 1)
    (hpos : 0 < f.natDegree) (Ω : Type*) [Field Ω] [Algebra L Ω] [Algebra k Ω]
    [IsScalarTower k L Ω] [IsAlgClosed Ω] :
    ∃ g₀ : k[X], g₀.Monic ∧ ∃ β : Ω, aeval β g₀ = 0 ∧ ∃ α' : Ω, aeval α' f = 0 ∧
      IntermediateField.adjoin L {α'} = IntermediateField.adjoin L {β} := by
  obtain ⟨ε, hε, hK⟩ := GroundTheory.LocalField.exists_adjoin_eq_of_norm_coeff_sub_lt f hfm hirr hsep Ω
  obtain ⟨n, hn⟩ : ∃ n, f.natDegree = n := ⟨_, rfl⟩
  rw [hn] at hpos
  have happrox : ∀ i : Fin n, ∃ x : k,
      ‖algebraMap k L x - f.coeff i‖ < min ε 1 := fun i ↦ by
    obtain ⟨x, hx⟩ := hk.exists_dist_lt (f.coeff i) (lt_min hε one_pos)
    exact ⟨x, by rwa [dist_comm, dist_eq_norm] at hx⟩
  choose x hx using happrox
  have hg₀m : (GroundTheory.LocalField.monicOfCoeffs x).Monic := GroundTheory.LocalField.monic_monicOfCoeffs x
  have hdeg : (GroundTheory.LocalField.monicOfCoeffs x).degree ≠ 0 := by
    rw [degree_eq_natDegree hg₀m.ne_zero, GroundTheory.LocalField.natDegree_monicOfCoeffs]
    exact_mod_cast hpos.ne'
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_aeval_eq_zero Ω _ hdeg
  have hgc := map_monicOfCoeffs (algebraMap k L) x
  have hfc' : f = GroundTheory.LocalField.monicOfCoeffs (fun i : Fin n ↦ f.coeff i) :=
    GroundTheory.LocalField.eq_monicOfCoeffs hfm hn
  refine ⟨_, hg₀m, β, hβ, hK ((GroundTheory.LocalField.monicOfCoeffs x).map (algebraMap k L))
    (hg₀m.map _) ?_ ?_ ?_ β (by rw [aeval_map_algebraMap]; exact hβ)⟩
  · rw [hg₀m.natDegree_map, GroundTheory.LocalField.natDegree_monicOfCoeffs, hn]
  · intro i
    rw [hgc, GroundTheory.LocalField.monicOfCoeffs, coeff_add, coeff_X_pow,
      GroundTheory.LocalField.coeff_sum_fin_C_mul_X_pow]
    split_ifs with h1 h2 h2
    · omega
    · rw [add_zero, norm_one]
    · rw [zero_add]
      have := IsUltrametricDist.norm_add_le_max (algebraMap k L (x ⟨i, h2⟩) - f.coeff i) (f.coeff i)
      rw [sub_add_cancel] at this
      exact this.trans (max_le ((hx _).le.trans (min_le_right _ _)) (hfc i))
    · rw [add_zero, norm_zero]
      exact zero_le_one
  · intro i
    rw [← coeff_sub, hgc]
    conv_lhs => rw [hfc']
    rw [GroundTheory.LocalField.monicOfCoeffs_sub_monicOfCoeffs, GroundTheory.LocalField.coeff_sum_fin_C_mul_X_pow]
    split_ifs with h
    · exact (hx _).trans_le (min_le_left _ _)
    · rw [norm_zero]
      exact hε

end Generic

section Krasner

abbrev nontriviallyNormedFieldAdicCompletion :
    NontriviallyNormedField (v.adicCompletion K.1) where
  __ := (inferInstance : NormedField (v.adicCompletion K.1))
  non_trivial := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K.1)
    have h := normalizedAbv_of_irreducible v hϖ
    rw [normalizedAbv_apply] at h
    refine ⟨(ϖ : v.adicCompletion K.1)⁻¹, ?_⟩
    rw [norm_inv, h, inv_inv]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

attribute [local instance] nontriviallyNormedFieldAdicCompletion

theorem exists_norm_algebraMap_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ c : K.1, 0 < ‖algebraMap K.1 (v.adicCompletion K.1) c‖ ∧
      ‖algebraMap K.1 (v.adicCompletion K.1) c‖ < ε := by
  obtain ⟨x, hx0, hx⟩ := NormedField.exists_norm_lt (v.adicCompletion K.1) (half_pos hε)
  obtain ⟨c, hc⟩ := (HeightOneSpectrum.denseRange_algebraMap K.1 v).exists_dist_lt x hx0
  rw [dist_eq_norm] at hc
  refine ⟨c, ?_, ?_⟩
  · have := norm_sub_norm_le x (x - algebraMap K.1 _ c)
    rw [sub_sub_cancel] at this
    linarith
  · have := norm_le_insert' (algebraMap K.1 (v.adicCompletion K.1) c) x
    rw [← norm_neg (algebraMap K.1 _ c - x), neg_sub] at this
    linarith

theorem minpoly_algebraMap_mul {c : v.adicCompletion K.1} (hc : c ≠ 0)
    (α : AlgebraicClosure (v.adicCompletion K.1)) :
    minpoly (v.adicCompletion K.1) (algebraMap _ _ c * α) =
      scaleRoots (minpoly (v.adicCompletion K.1) α) c := by
  have hint : ∀ x : AlgebraicClosure (v.adicCompletion K.1), IsIntegral (v.adicCompletion K.1) x :=
    fun x ↦ Algebra.IsIntegral.isIntegral x
  have hdvd : ∀ (d : v.adicCompletion K.1) (x : AlgebraicClosure (v.adicCompletion K.1)),
      minpoly (v.adicCompletion K.1) (algebraMap _ _ d * x) ∣
        scaleRoots (minpoly (v.adicCompletion K.1) x) d :=
    fun d x ↦ minpoly.dvd _ _ (scaleRoots_aeval_eq_zero (minpoly.aeval _ x))
  have hmon : ∀ (d : v.adicCompletion K.1) (x : AlgebraicClosure (v.adicCompletion K.1)),
      (scaleRoots (minpoly (v.adicCompletion K.1) x) d).Monic :=
    fun d x ↦ (monic_scaleRoots_iff d).2 (minpoly.monic (hint x))
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hint _)) (hmon c α) (hdvd c α) ?_).symm
  rw [natDegree_scaleRoots]
  have h2 := natDegree_le_of_dvd (hdvd c⁻¹ (algebraMap _ _ c * α)) (hmon _ _).ne_zero
  rwa [natDegree_scaleRoots, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at h2

theorem exists_ι_eq_of_aeval_eq_zero {g : K.1[X]} (hg : g ≠ 0)
    {β : AlgebraicClosure (v.adicCompletion K.1)} (hβ : aeval β g = 0) : ∃ r : ℚ̄, ι r = β := by
  have hs : (g.map (algebraMap K.1 ℚ̄)).Splits := IsAlgClosed.splits _
  have hne : g.map (algebraMap K.1 ℚ̄) ≠ 0 := Polynomial.map_ne_zero hg
  have hroot : ((g.map (algebraMap K.1 ℚ̄)).map (ι : ℚ̄ →+* _)).IsRoot β := by
    rw [Polynomial.map_map, AlgHom.comp_algebraMap, IsRoot.def, eval_map, ← aeval_def]
    exact hβ
  obtain ⟨r, hr⟩ := hs.mem_range_of_isRoot hne hroot
  exact ⟨r, hr⟩

theorem exists_level_mem (r : ℚ̄) : ∃ p : GLevel K, r ∈ p.1.1 := by
  have : FiniteDimensional ℚ ℚ⟮r⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral r)
  obtain ⟨p, hp⟩ := GLevel.exists_le (K := K) ⟨ℚ⟮r⟯, this⟩
  exact ⟨p, (show ℚ⟮r⟯ ≤ p.1.1 from hp) (mem_adjoin_simple_self ℚ r)⟩

theorem exists_level_completionEmbedding_eq (α : AlgebraicClosure (v.adicCompletion K.1)) :
    ∃ (p : GLevel K) (y : (placeOfEmbedding ι p.1).1.adicCompletion p.1.1),
      completionEmbedding ι p.1 y = α := by
  have hint : ∀ x : AlgebraicClosure (v.adicCompletion K.1), IsIntegral (v.adicCompletion K.1) x :=
    fun x ↦ Algebra.IsIntegral.isIntegral x

  obtain ⟨M, hM, haM⟩ := exists_norm_coeff_le (minpoly (v.adicCompletion K.1) α)
  obtain ⟨c, hc0, hcM⟩ := exists_norm_algebraMap_lt (v := v) (ε := M⁻¹) (by positivity)
  have hc'0 : algebraMap K.1 (v.adicCompletion K.1) c ≠ 0 := norm_pos_iff.1 hc0
  have hfc := norm_coeff_scaleRoots_le_one (minpoly.monic (hint α)) hM haM hcM.le
  rw [← minpoly_algebraMap_mul hc'0 α] at hfc

  obtain ⟨g₀, hg₀m, β, hβ, α', hα', hadj⟩ := exists_adjoin_eq_of_dense
    (HeightOneSpectrum.denseRange_algebraMap K.1 v) (minpoly.monic (hint _))
    (minpoly.irreducible (hint _)) (minpoly.irreducible (hint _)).separable hfc
    (minpoly.natDegree_pos (hint _))
    (AlgebraicClosure (v.adicCompletion K.1))

  obtain ⟨r, hr⟩ := exists_ι_eq_of_aeval_eq_zero ι hg₀m.ne_zero hβ
  obtain ⟨p, hrp⟩ := exists_level_mem (K := K) r
  have hβmem : β ∈ (completionEmbedding ι p.1).fieldRange :=
    ⟨algebraMap p.1.1 _ ⟨r, hrp⟩, (completionEmbedding_algebraMap ι p.1 ⟨r, hrp⟩).trans hr⟩
  have hα'mem : α' ∈ (completionEmbedding ι p.1).fieldRange := by
    have : (v.adicCompletion K.1)⟮α'⟯ ≤ (completionEmbedding ι p.1).fieldRange := by
      rw [hadj, adjoin_simple_le_iff]
      exact hβmem
    exact this (mem_adjoin_simple_self _ α')
  obtain ⟨y', hy'⟩ := hα'mem

  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (hint _).isAlgebraic hα'
  refine ⟨p, algebraMap (v.adicCompletion K.1) _ (algebraMap K.1 (v.adicCompletion K.1) c)⁻¹ *
    (localDecompHom ι p.1 σ • y'), ?_⟩
  have e1 : completionEmbedding ι p.1 (localDecompHom ι p.1 σ • y') =
      algebraMap (v.adicCompletion K.1) _ (algebraMap K.1 (v.adicCompletion K.1) c) * α := by
    rw [completionEmbedding_smul]
    exact (congrArg σ hy').trans hσ
  have e2 := (completionEmbedding ι p.1).commutes (algebraMap K.1 (v.adicCompletion K.1) c)⁻¹
  refine ((map_mul (completionEmbedding ι p.1) _ _).trans ?_)
  rw [e1, e2, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc'0, map_one, one_mul]

theorem exists_completionEmbedding_eq_of_le {p q : GLevel K} (h : p ≤ q)
    (y : (placeOfEmbedding ι p.1).1.adicCompletion p.1.1) :
    ∃ z : (placeOfEmbedding ι q.1).1.adicCompletion q.1.1,
      completionEmbedding ι q.1 z = completionEmbedding ι p.1 y := by
  have : Fact (p.1 ≤ q.1) := ⟨h⟩
  exact ⟨_, completionEmbedding_completionMap ι y⟩

theorem exists_level_forall_mem (S : Finset (AlgebraicClosure (v.adicCompletion K.1))) :
    ∃ p : GLevel K, ∀ α ∈ S, ∃ y : (placeOfEmbedding ι p.1).1.adicCompletion p.1.1,
      completionEmbedding ι p.1 y = α := by
  classical
  choose lev y hy using fun α ↦ exists_level_completionEmbedding_eq ι α
  obtain ⟨p, hp⟩ := Finset.exists_le (S.image lev)
  refine ⟨p, fun α hα ↦ ?_⟩
  obtain ⟨z, hz⟩ := exists_completionEmbedding_eq_of_le ι (hp _ (Finset.mem_image_of_mem _ hα))
    (y α)
  exact ⟨z, hz.trans (hy α)⟩

theorem exists_level_le_fieldRange (E : IntermediateField (v.adicCompletion K.1)
    (AlgebraicClosure (v.adicCompletion K.1))) [FiniteDimensional (v.adicCompletion K.1) E] :
    ∃ p : GLevel K, E ≤ (completionEmbedding ι p.1).fieldRange := by
  classical
  let b := Module.finBasis (v.adicCompletion K.1) E
  obtain ⟨p, hp⟩ := exists_level_forall_mem ι (Finset.univ.image fun i ↦ (b i : AlgebraicClosure _))
  refine ⟨p, fun x hx ↦ ?_⟩
  have hsum : ∑ i, ((b.repr ⟨x, hx⟩ i • b i : E) : AlgebraicClosure (v.adicCompletion K.1)) = x := by
    rw [← IntermediateField.coe_sum, b.sum_repr]
  rw [← hsum]
  refine IntermediateField.sum_mem _ fun i _ ↦ ?_
  rw [IntermediateField.coe_smul]
  refine IntermediateField.smul_mem _ ?_
  obtain ⟨y, hy⟩ := hp _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact ⟨y, hy⟩

theorem apply_completionEmbedding_of_localDecompHom_eq_one (F : FiniteSubfield) [Fact (K ≤ F)]
    [F.1.fixingSubgroup.Normal]
    {σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)}
    (hσ : localDecompHom ι F σ = 1) (y : (placeOfEmbedding ι F).1.adicCompletion F.1) :
    σ (completionEmbedding ι F y) = completionEmbedding ι F y := by
  have : σ.toAlgHom.comp (completionEmbedding ι F) = completionEmbedding ι F :=
    algHom_ext_adicCompletion F fun x ↦ by
      change σ (completionEmbedding ι F (algebraMap F.1 _ x)) =
        completionEmbedding ι F (algebraMap F.1 _ x)
      rw [completionEmbedding_algebraMap, ← ι_localDecompHom_apply, hσ, OneMemClass.coe_one,
        AlgEquiv.one_apply]
  exact DFunLike.congr_fun this y

theorem exists_level_ker_le {U : Set Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)}
    (hU : U ∈ nhds 1) : ∃ p : GLevel K, ∀ σ, localDecompHom ι p.1 σ = 1 → σ ∈ U := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff _ _ U).1 hU
  obtain ⟨p, hp⟩ := exists_level_le_fieldRange ι E
  refine ⟨p, fun σ hσ ↦ hEU ((IntermediateField.mem_fixingSubgroup_iff E σ).2 fun x hx ↦ ?_)⟩
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 (hp hx)
  exact apply_completionEmbedding_of_localDecompHom_eq_one ι p.1 hσ y

end Krasner

end

end GroundTheory.ProfCoh
