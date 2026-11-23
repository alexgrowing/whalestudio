import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open AlgebraicGeometry CategoryTheory Topology

namespace LateralTheory.E.LeafFibreFieldPf

open Cardinal IntermediateField in
theorem alg_part (k K : Type) [Field k] [Field K] [Algebra k K] (S : Finset K)
    (hgen : IntermediateField.adjoin k (S : Set K) = ⊤) (d : ℕ) (hd : Algebra.trdeg k K = d + 1) :
    ∃ (F : IntermediateField k K) (s : Finset F) (t : K), s.card ≤ d ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
      FiniteDimensional (IntermediateField.adjoin F {t}) K := by
  classical
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k K
  have hcard : #B = ((d + 1 : ℕ) : Cardinal) := by
    rw [hB.cardinalMk_eq_trdeg, hd]; push_cast; rfl
  obtain ⟨T, hTB, hTc⟩ := Cardinal.mk_set_eq_nat_iff_finset.mp hcard
  obtain ⟨a, haT⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  set T' := T.erase a with hT'
  let F : IntermediateField k K := IntermediateField.adjoin k (T' : Set K)
  let sF : Finset F := T'.attach.image fun x => ⟨x.1, IntermediateField.subset_adjoin k _ x.2⟩
  have hsF : (F.val '' (sF : Set F)) = (T' : Set K) := by
    ext y; simp [sF]; intro h; exact IntermediateField.subset_adjoin k _ (Finset.mem_coe.mpr h)
  refine ⟨F, sF, a, ?_, ?_, ?_, ?_⟩
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_attach, Finset.card_erase_of_mem haT, hTc]; simp
  · have hmem : ∀ y : F, y ∈ IntermediateField.adjoin k (sF : Set F) := by
      intro y
      have : (y : K) ∈ (IntermediateField.adjoin k (sF : Set F)).map F.val := by
        rw [IntermediateField.adjoin_map, hsF]; exact y.2
      rw [← SetLike.mem_coe, IntermediateField.coe_map] at this
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    exact ⟨fun y => by
      have := isAlgebraic_algebraMap (R := IntermediateField.adjoin k (sF : Set F)) (A := F) ⟨y, hmem y⟩
      exact this⟩
  · have hind := hB.1
    have hnot : (⟨a, hTB ▸ haT⟩ : B) ∉ {i : B | (i : K) ≠ a} := by simp
    have htr := hind.transcendental_adjoin hnot
    have himg : (Subtype.val '' {i : B | (i : K) ≠ a}) = (T' : Set K) := by
      ext y; simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, hT', Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, ← hTB]
      tauto
    rw [himg, ← IntermediateField.transcendental_adjoin_iff] at htr
    exact htr
  ·
    set L := IntermediateField.adjoin F {a} with hL
    have hBT : (B : Set K) = (T : Set K) := hTB.symm
    have halgB := hB.isAlgebraic_field
    rw [Subtype.range_coe] at halgB
    set E := IntermediateField.adjoin k B with hE
    have hEL : ∀ x ∈ E, x ∈ L := by
      intro x hx
      have hle : E ≤ L.restrictScalars k := by
        rw [hE, IntermediateField.adjoin_le_iff]
        intro b hb
        rw [← hTB] at hb
        by_cases hba : b = a
        · subst hba; exact IntermediateField.mem_adjoin_simple_self F b
        · have hbF : b ∈ F := IntermediateField.subset_adjoin k _ (by simp [hT', hba, hb])
          exact (IntermediateField.algebraMap_mem L (⟨b, hbF⟩ : F))
      exact hle hx
    let g : E →+* L :=
      { toFun := fun x => ⟨x.1, hEL x.1 x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    let _ : Algebra E L := g.toAlgebra
    have : IsScalarTower E L K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint : ∀ x : K, IsIntegral L x := fun x =>
      ((halgB.isAlgebraic x).extendScalars g.injective).isIntegral
    have hfd := IntermediateField.finiteDimensional_adjoin (K := L) (S := (S : Set K)) (fun x _ => hint x)
    have htop : IntermediateField.adjoin L (S : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin k (S : Set K) := hgen ▸ trivial
      let M : IntermediateField k K :=
        { carrier := (IntermediateField.adjoin L (S : Set K) : Set K)
          mul_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).mul_mem ha hb
          add_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).add_mem ha hb
          inv_mem' := fun _ hx => (IntermediateField.adjoin L (S : Set K)).inv_mem hx
          algebraMap_mem' := fun c => by
            have h1 := IntermediateField.algebraMap_mem (IntermediateField.adjoin L (S : Set K))
              (⟨algebraMap F K (algebraMap k F c), IntermediateField.algebraMap_mem L _⟩ : L)
            rw [IsScalarTower.algebraMap_apply k F K]
            exact h1 }
      have hle : IntermediateField.adjoin k (S : Set K) ≤ M := by
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        show y ∈ (IntermediateField.adjoin L (S : Set K) : Set K)
        exact IntermediateField.subset_adjoin L _ hy
      exact (hle hx : x ∈ (IntermediateField.adjoin L (S : Set K) : Set K))
    rw [htop] at hfd
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := L) (E := K)).toLinearEquiv

theorem gen_top (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ S : Finset (FractionRing A), IntermediateField.adjoin k (S : Set (FractionRing A)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (‹Algebra.FiniteType k A›).out
  refine ⟨s.image (algebraMap A (FractionRing A)), ?_⟩
  have hA : ∀ a : A, algebraMap A (FractionRing A) a ∈
      IntermediateField.adjoin k ((s.image (algebraMap A (FractionRing A)) : Finset _) : Set (FractionRing A)) := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have h1 : algebraMap A (FractionRing A) a ∈ (Algebra.adjoin k (s : Set A)).map (IsScalarTower.toAlgHom k A (FractionRing A)) :=
      Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine IntermediateField.algebra_adjoin_le_adjoin k _ ?_
    simpa [Finset.coe_image] using h1
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  exact div_mem (hA a) (hA b)

theorem dimX_eq (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (e : ℕ)
    (he : letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
      Algebra.trdeg k X.functionField = e) :
    topologicalKrullDim X = e := by
  have h := GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen (Z := (Set.univ : Set X))
    ⟨genericPoint X, trivial⟩ (d := (e : WithBot ℕ∞)) (fun x _ => by
      obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p x
      refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
      rw [Set.inter_univ, GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
      have hA := GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans he)
      rw [← hA]
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)
  rw [← h]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (e := (id : X → X)) IsEmbedding.id (Set.range_id)).symm

theorem LeafFibreField_of : LateralTheory.E.LeafCurveVCut.LeafFibreField := by
  intro k _ X _ p _ hd
  letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
  obtain ⟨A, _, _, _, _, _, j, _, hx, hj, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p (genericPoint X)
  obtain ⟨e, -, he2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A
  have hdim := dimX_eq k p e (htr.symm.trans he2)
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := by
    cases e with
    | zero => rw [hdim] at hd; simp at hd
    | succ d => exact ⟨d, rfl⟩
  have : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have htrK : Algebra.trdeg k (FractionRing A) = d + 1 := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (FractionRing A), he2]; push_cast; rfl
  obtain ⟨S, hS⟩ := gen_top k A
  obtain ⟨F, s, t, hs, halg, ht, hfin⟩ := alg_part k (FractionRing A) S hS d htrK
  refine ⟨F, inferInstance, inferInstance, FractionRing A, inferInstance, inferInstance, d, s, t,
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ j, ?_, hs, halg, ht, hfin, ?_, ?_⟩
  · rw [hdim]; exact_mod_cast Nat.lt_succ_self d
  · rw [Category.assoc, hj, ← Spec.map_comp]
    congr 1
  · obtain ⟨q, hq⟩ := hx
    obtain ⟨pt⟩ : Nonempty (Spec (.of (FractionRing A))) := inferInstance
    refine ⟨pt, ?_⟩
    have hz : (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt ⤳ q := by
      refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
      show Ideal.comap (algebraMap A (FractionRing A)) pt.asIdeal ≤ q.asIdeal
      have hbot : pt.asIdeal = ⊥ := by
        rcases Ideal.eq_bot_or_top pt.asIdeal with h | h
        · exact h
        · exact absurd h pt.isPrime.ne_top
      intro a ha
      rw [Ideal.mem_comap, hbot, Ideal.mem_bot] at ha
      rw [(IsFractionRing.injective A (FractionRing A)) (ha.trans (map_zero _).symm)]
      exact zero_mem _
    have h1 := hz.map j.continuous
    rw [hq] at h1
    have h2 := (genericPoint_spec X).specializes
      (Set.mem_univ (j ((Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt)))
    rw [Scheme.Hom.comp_apply]
    exact (h1.antisymm h2).eq

end LateralTheory.E.LeafFibreFieldPf
