import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Ired
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaMvpsCot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetCore
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem det_mem_annihilator_of_relations {B N ι : Type} [CommRing B] [AddCommGroup N] [Module B N] [Fintype ι] [DecidableEq ι]
    (z : Matrix ι ι B) (n : ι → N) (hspan : Submodule.span B (Set.range n) = ⊤)
    (hrel : ∀ i, ∑ j, z i j • n j = 0) : z.det ∈ Module.annihilator B N := by
  have h1 : ∀ k, z.det • n k = 0 := by
    intro k
    have h2 : ∑ i, z.adjugate k i • ∑ j, z i j • n j = 0 := by simp [hrel]
    have h3 : ∑ i, z.adjugate k i • ∑ j, z i j • n j = ∑ j, (z.adjugate * z) k j • n j := by
      simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, mul_smul]
      exact Finset.sum_comm
    rw [h3, Matrix.adjugate_mul] at h2
    simpa [Matrix.one_apply, ite_smul] using h2
  rw [Module.mem_annihilator]
  intro x
  have hx : x ∈ Submodule.span B (Set.range n) := hspan ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h1 k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

private theorem cotangent_independent_of_residues (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : Irreducible ϖ) (D0 g : ℕ) (c : Fin g × Fin g → Fin D0 → O)
    (hc : LinearIndependent (ResidueField O) (fun p a => residue O (c p a)))
    (w : Fin g × Fin g → MvPowerSeries (Fin D0 ⊕ Fin g) O)
    (hw : ∀ p, w p ∈ Ideal.span {(MvPowerSeries.C ϖ : MvPowerSeries (Fin D0 ⊕ Fin g) O)} ⊔ maximalIdeal _ ^ 2) :
    CotInd (MvPowerSeries (Fin D0 ⊕ Fin g) O)
      (Sum.elim (fun p : Fin g × Fin g =>
          (∑ a, MvPowerSeries.C (c p a) * MvPowerSeries.X (Sum.inl a)) - w p)
        (fun j : Fin g => MvPowerSeries.X (Sum.inr j))) := by
  obtain ⟨-, -, hx⟩ := mvPowerSeries_cotInd O ϖ hϖ (Fin D0 ⊕ Fin g)
  have hw' : ∀ p, ∃ u s, s ∈ maximalIdeal (MvPowerSeries (Fin D0 ⊕ Fin g) O) ^ 2 ∧
      w p = u * MvPowerSeries.C ϖ + s := by
    intro p
    obtain ⟨y, hy, s, hs, h⟩ := Submodule.mem_sup.1 (hw p)
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact ⟨u, s, hs, h.symm⟩
  choose u s hs hus using hw'
  refine ⟨?_, fun b hb => ?_⟩
  · rintro (p | j)
    · refine sub_mem (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hx.mem (some (Sum.inl a)))) ?_
      rw [hus]
      exact add_mem (Ideal.mul_mem_left _ _ (hx.mem none)) (Ideal.pow_le_self two_ne_zero (hs p))
    · exact hx.mem (some (Sum.inr j))
  · have h1 : ∑ p, b (Sum.inl p) * s p ∈ maximalIdeal (MvPowerSeries (Fin D0 ⊕ Fin g) O) ^ 2 :=
      Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (hs p)
    have h2 := hx.indep (fun o => o.elim (-∑ p, b (Sum.inl p) * u p)
      (Sum.elim (fun a => ∑ p, b (Sum.inl p) * MvPowerSeries.C (c p a)) (fun j => b (Sum.inr j)))) (by
        have h3 := add_mem hb h1
        convert h3 using 1
        simp only [Fintype.sum_option, Fintype.sum_sum_type, Option.elim, Sum.elim_inl, Sum.elim_inr, hus,
          Finset.sum_mul, mul_sub, mul_add, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          neg_mul, mul_assoc]
        rw [Finset.sum_comm]
        ring)
    rintro (p | j)
    · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, ← residue_eq_zero_iff]
      refine Fintype.linearIndependent_iff.1 hc
        (fun p => residue O (MvPowerSeries.constantCoeff (b (Sum.inl p)))) ?_ p
      funext a
      have h4 := h2 (some (Sum.inl a))
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, ← residue_eq_zero_iff] at h4
      simpa [Finset.sum_apply, map_sum, map_mul] using h4
    · exact h2 (some (Sum.inr j))

theorem UpperTheory.V.Pa.presOut1 :
    ∀ (O B A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] [CommRing A] [Algebra B A] [Module.Finite B A] (N : Submodule B A), Function.Injective (algebraMap B A) → _root_.IsCompl (1 : Submodule B A) N → (∀ a ∈ N, ∀ b ∈ N, ∃ c ∈ maximalIdeal B, a * b = algebraMap B A c) → ∀ (D0 g : ℕ) (X : Fin D0 → B) (m : Fin g → N) (c : Fin g × Fin g → Fin D0 → O), (∀ a, X a ∈ maximalIdeal B) → Submodule.span B (Set.range m) = ⊤ → LinearIndependent (ResidueField O) (fun p a => residue O (c p a)) → maximalIdeal B ≤ Ideal.span (Set.range X) ⊔ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2 ⊔ ired N) → (∀ i, ∑ j, (∑ a, algebraMap O B (c (i, j) a) * X a) • m j ∈ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2 ⊔ ired N) • (⊤ : Submodule B N)) → ∀ Z Q : Ideal B, Z.IsPrime → Q.IsPrime → ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Z) → ¬ ired N ≤ Z → (¬ ired N ≤ Q ∨ Module.annihilator B N ≤ Q) → Z ≤ Q := by
  intro O B A _ _ _ _ _ _ _ _ _ _ N hinj hcompl hmul D0 g X m c hX hm hc hg hr Z Q hZ hQ hd hZr hQr
  letI : Algebra O A := ((algebraMap B A).comp (algebraMap O B)).toAlgebra
  haveI : IsScalarTower O B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hA, hmA, hired⟩ := aaCO O B A N hinj hcompl hmul
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmO : maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  obtain ⟨hreg, hdim, hx⟩ := mvPowerSeries_cotInd O ϖ hϖ (Fin D0 ⊕ Fin g)
  haveI := co_mvps O O (Fin D0 ⊕ Fin g)
  have hBA : (maximalIdeal B).map (algebraMap B A) ≤ maximalIdeal A := fun a ha =>
    (hmA a).2 (Ideal.mem_sup_left ha)
  obtain ⟨F, ⟨hC, hF⟩, -⟩ := co_ev O O A (Fin D0 ⊕ Fin g) (Algebra.ofId O A)
    (Sum.elim (fun a => algebraMap B A (X a)) (fun j => (m j : A))) (by
      rintro (a | j)
      · exact hBA (Ideal.mem_map_of_mem _ (hX a))
      · exact (hmA _).2 (Ideal.mem_sup_right (Ideal.subset_span (m j).2)))
  have hC' : ∀ x, F (MvPowerSeries.C x) = algebraMap B A (algebraMap O B x) := hC
  have hF1 : ∀ a, F (MvPowerSeries.X (Sum.inl a)) = algebraMap B A (X a) := fun a => hF (Sum.inl a)
  have hF2 : ∀ j, F (MvPowerSeries.X (Sum.inr j)) = (m j : A) := fun j => hF (Sum.inr j)
  have hNI : ∀ I : Ideal A, (∀ j, (m j : A) ∈ I) → ∀ y ∈ N, y ∈ I := by
    intro I hI y hy
    have hy' : (⟨y, hy⟩ : N) ∈ Submodule.span B (Set.range m) := hm ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hy'
    have : y = ∑ j, b j • (m j : A) := by
      have := congrArg Subtype.val hb
      simpa using this.symm
    rw [this]
    exact Ideal.sum_mem _ fun j _ => by
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hI j)
  have hJ : ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2 ⊔ ired N).map (algebraMap B A) ≤
      (Ideal.span {(MvPowerSeries.C ϖ : MvPowerSeries (Fin D0 ⊕ Fin g) O)}).map F ⊔ maximalIdeal A ^ 2 := by
    rw [Ideal.map_sup, Ideal.map_sup]
    refine sup_le (sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)) (le_sup_of_le_right hired)
    · rw [hmO, Ideal.map_span, Ideal.map_span, Ideal.map_span]
      simp [hC']
    · rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hBA 2
  have hcot : maximalIdeal A ≤ (maximalIdeal (MvPowerSeries (Fin D0 ⊕ Fin g) O)).map F ⊔ maximalIdeal A ^ 2 := by
    refine le_trans (fun a ha => (hmA a).1 ha) (sup_le ?_ ?_)
    · refine (Ideal.map_mono hg).trans ?_
      rw [Ideal.map_sup]
      refine sup_le (le_sup_of_le_left ?_) (hJ.trans (sup_le_sup_right (Ideal.map_mono ?_) _))
      · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
        rintro _ ⟨a, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, ← hF1]
        exact Ideal.mem_map_of_mem _ (hx.mem (some (Sum.inl a)))
      · rw [Ideal.span_singleton_le_iff_mem]
        exact hx.mem none
    · refine le_sup_of_le_left (Ideal.span_le.2 fun y hy => hNI _ (fun j => ?_) y hy)
      rw [← hF2]
      exact Ideal.mem_map_of_mem _ (hx.mem (some (Sum.inr j)))
  have hsurj : Function.Surjective F := co_surj O _ A F hcot
  have hmP : maximalIdeal A ≤ (maximalIdeal (MvPowerSeries (Fin D0 ⊕ Fin g) O)).map F := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    rwa [smul_eq_mul, ← pow_two]
  have hw : ∀ i, ∃ w : Fin g → B,
      (∀ j, w j ∈ (maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2 ⊔ ired N) ∧
      ∑ j, w j • m j = ∑ j, (∑ a, algebraMap O B (c (i, j) a) * X a) • m j := by
    intro i
    have h := hr i
    rw [← hm, Submodule.mem_ideal_smul_span_iff_exists_sum] at h
    obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, ?_⟩
    rw [← h, Finsupp.sum_fintype _ _ (by simp)]
  choose w hwJ hwe using hw
  have hw2 : ∀ p : Fin g × Fin g, ∃ v ∈ Ideal.span {(MvPowerSeries.C ϖ : MvPowerSeries (Fin D0 ⊕ Fin g) O)} ⊔
      maximalIdeal _ ^ 2, F v = algebraMap B A (w p.1 p.2) := by
    intro p
    refine (Ideal.mem_map_iff_of_surjective F hsurj).1 ?_
    rw [Ideal.map_sup, Ideal.map_pow]
    exact sup_le_sup_left (Ideal.pow_right_mono hmP 2) _ (hJ (Ideal.mem_map_of_mem _ (hwJ p.1 p.2)))
  choose v hv hFv using hw2
  let ζ : Matrix (Fin g) (Fin g) B := Matrix.of fun i j => (∑ a, algebraMap O B (c (i, j) a) * X a) - w i j
  let z : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin D0 ⊕ Fin g) O) := Matrix.of fun i j =>
    (∑ a, MvPowerSeries.C (c (i, j) a) * MvPowerSeries.X (Sum.inl a)) - v (i, j)
  have hζ : ∀ i, ∑ j, ζ i j • m j = 0 := by
    intro i
    simp only [ζ, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib, hwe, sub_self]
  have hzζ : ∀ i j, F (z i j) = algebraMap B A (ζ i j) := by
    intro i j
    simp only [z, ζ, Matrix.of_apply, map_sub, map_sum, map_mul, hC', hF1, hFv]
  have hann := det_mem_annihilator_of_relations ζ m hm hζ
  have hdetQ : ζ.det ∈ Q := by
    rcases hQr with h | h
    · by_contra hn
      apply h
      rw [ired, Ideal.span_le]
      rintro b ⟨x, hx, y, hy, hxy⟩
      refine (hQ.mem_or_mem (x := ζ.det) ?_).resolve_left hn
      have h0 : ζ.det • x = 0 := congrArg Subtype.val (Module.mem_annihilator.1 hann ⟨x, hx⟩)
      have : ζ.det * b = 0 := hinj (by
        rw [map_mul, ← hxy, ← mul_assoc, ← Algebra.smul_def, h0, zero_mul, map_zero])
      rw [this]
      exact Q.zero_mem
    · exact h hann
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).2 hinj
  obtain ⟨Q', -, hQ', hQQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal A) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]
    exact Q.zero_mem)
  rw [← hQQ]
  refine under_le_of_det_mem _ (Fin g) z (fun j => MvPowerSeries.X (Sum.inr j))
    (cotangent_independent_of_residues O ϖ hϖ D0 g c hc v hv) B A (F : _ →+* A) hsurj ?_ Z hZ ?_ ?_ Q' hQ' ?_
  · rw [relIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show F (∑ j, z i j * MvPowerSeries.X (Sum.inr j)) = 0
    have := congrArg Subtype.val (hζ i)
    simp only [map_sum, map_mul, hzζ, hF2, ← Algebra.smul_def]
    simpa using this
  · rw [hdim]
    refine le_trans (le_of_eq ?_) (add_le_add_left hd _)
    simp only [Fintype.card_sum, Fintype.card_fin]
    rw [← Nat.cast_add]
    congr 1
    omega
  · intro Z' hZ' hZZ
    by_contra hn
    push Not at hn
    apply hZr
    rw [ired, Ideal.span_le]
    rintro b ⟨x, hx, y, hy, hxy⟩
    rw [← hZZ]
    show algebraMap B A b ∈ Z'
    rw [← hxy]
    exact Ideal.mul_mem_left _ _ (hNI Z' (fun j => hF2 j ▸ hn j) y hy)
  · have : (F : MvPowerSeries (Fin D0 ⊕ Fin g) O →+* A) z.det = algebraMap B A ζ.det := by
      rw [RingHom.map_det, RingHom.map_det]
      congr 1
      ext i j
      exact hzζ i j
    rw [this]
    rw [← hQQ] at hdetQ
    exact hdetQ
