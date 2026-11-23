import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BlowOpen

theorem exists_specializes_of_dense {X : Type} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X] (S : Set X)
    (hSo : IsOpen S) (hSd : Dense S) (x : X) : ∃ w ∈ S, w ⤳ x := by
  classical
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_of_mem_irreducibleComponents _ hC
  have hη : IsGenericPoint hCi.genericPoint (irreducibleComponent x) := by
    simpa [hCc.closure_eq] using hCi.isGenericPoint_genericPoint_closure
  let F := ⋃ C' ∈ (irreducibleComponents X \ {irreducibleComponent x}), C'
  have hFc : IsClosed F := (NoetherianSpace.finite_irreducibleComponents.diff).isClosed_biUnion
    (fun C' h => isClosed_of_mem_irreducibleComponents C' h.1)
  have hηF : hCi.genericPoint ∉ F := by
    simp only [F, Set.mem_iUnion]
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hsub : irreducibleComponent x ⊆ C' := fun y hy =>
      (hη.specializes hy).mem_closed (isClosed_of_mem_irreducibleComponents C' hC') hηC'
    exact hne (Set.mem_singleton_iff.2 (hC.eq_of_le hC'.1 hsub).symm)
  obtain ⟨w, hwF, hwS⟩ := hSd.inter_open_nonempty Fᶜ hFc.isOpen_compl ⟨_, hηF⟩
  have hwC : w ∈ irreducibleComponent x := by
    by_contra h
    apply hwF
    simp only [F, Set.mem_iUnion]
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => h ?_⟩,
      mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.1 e]; exact mem_irreducibleComponent
  exact ⟨_, (hη.specializes hwC).mem_open hSo hwS, hη.specializes mem_irreducibleComponent⟩

theorem exists_specializes_of_dense_scheme (N : Scheme.{0}) [IsLocallyNoetherian N] (W : Set N) (hWo : IsOpen W)
    (hWd : Dense W) (n : N) : ∃ w ∈ W, w ⤳ n := by
  obtain ⟨_, ⟨O, hO, rfl⟩, hnO, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ n) isOpen_univ
  haveI : IsNoetherianRing Γ(N, O) := IsLocallyNoetherian.component_noetherian ⟨O, hO⟩
  obtain ⟨w, hw, hwn⟩ := @exists_specializes_of_dense (O : Set N) _ O.isOpen.isOpenEmbedding_subtypeVal.quasiSober
    (noetherianSpace_of_isAffineOpen O hO) (Subtype.val ⁻¹' W : Set (O : Set N)) (hWo.preimage continuous_subtype_val)
    (hWd.preimage O.isOpen.isOpenMap_subtype_val) ⟨n, hnO⟩
  exact ⟨w, hw, hwn.map continuous_subtype_val⟩

theorem mem_of_ι {X : Scheme.{0}} (U : X.Opens) (t : U.toScheme) : U.ι t ∈ U := by
  have := Set.mem_range_self (f := U.ι) t
  rwa [Scheme.Opens.range_ι] at this

theorem lift_of_isIso_over {S T Z N V : Scheme.{0}} (s : Z ⟶ S) (P : T ⟶ S) [Flat P] (f : N ⟶ Z) (g : N ⟶ S)
    (hg : f ≫ s = g) (U : Z.Opens) [IsIso (f ∣_ U)] [IsLocallyNoetherian N]
    (hW : Dense ((f ⁻¹ᵁ U : N.Opens) : Set N))
    (jV : V ⟶ pullback s P) [IsOpenImmersion jV] (hd : Dense (Set.range jV))
    (hU : ∀ v, pullback.fst s P (jV v) ∈ U)
    (r : pullback g P ⟶ pullback s P) (hr1 : r ≫ pullback.fst s P = pullback.fst g P ≫ f)
    (hr2 : r ≫ pullback.snd s P = pullback.snd g P) :
    ∃ jN : V ⟶ pullback g P, IsOpenImmersion jN ∧ Dense (Set.range jN) ∧ jN ≫ r = jV ∧
      r ⁻¹' Set.range jV = Set.range jN := by
  let UK : (pullback s P).Opens := pullback.fst s P ⁻¹ᵁ U
  let φ : U.toScheme ⟶ N := inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hφ : φ ≫ f = U.ι := by
    simp only [φ, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hret : ∀ {T' : Scheme.{0}} (x : T' ⟶ N) (y : T' ⟶ U.toScheme), y ≫ U.ι = x ≫ f → y ≫ φ = x := by
    intro T' x y hxy
    have hrange : Set.range x ⊆ Set.range (f ⁻¹ᵁ U).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← hxy, Scheme.Hom.comp_apply]
      exact mem_of_ι U _
    have hh : IsOpenImmersion.lift (f ⁻¹ᵁ U).ι x hrange ≫ (f ⁻¹ᵁ U).ι = x := IsOpenImmersion.lift_fac _ _ _
    have hh2 : IsOpenImmersion.lift (f ⁻¹ᵁ U).ι x hrange ≫ f ∣_ U = y := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hh, hxy]
    rw [← hh, ← hh2]
    simp only [φ, Category.assoc, IsIso.hom_inv_id_assoc]
  have hyK : (pullback.fst s P ∣_ U) ≫ U.ι = UK.ι ≫ pullback.fst s P := morphismRestrict_ι _ _
  let g' : UK.toScheme ⟶ pullback g P := pullback.lift ((pullback.fst s P ∣_ U) ≫ φ) (UK.ι ≫ pullback.snd s P)
    (by rw [← hg]; simp only [Category.assoc]; rw [reassoc_of% hφ, reassoc_of% hyK, pullback.condition])
  have hg'r : g' ≫ r = UK.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hr1, pullback.lift_fst_assoc, Category.assoc, hφ, hyK]
    · rw [Category.assoc, hr2, pullback.lift_snd]
  have he : (r ∣_ UK) ≫ UK.ι = (r ⁻¹ᵁ UK).ι ≫ r := morphismRestrict_ι _ _
  have hg'range : Set.range g' ⊆ Set.range (r ⁻¹ᵁ UK).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hg'r]
    exact mem_of_ι UK t
  have hk : IsOpenImmersion.lift (r ⁻¹ᵁ UK).ι g' hg'range ≫ (r ⁻¹ᵁ UK).ι = g' := IsOpenImmersion.lift_fac _ _ _
  haveI : IsIso (r ∣_ UK) := by
    refine ⟨⟨IsOpenImmersion.lift (r ⁻¹ᵁ UK).ι g' hg'range, ?_, ?_⟩⟩
    · rw [← cancel_mono (r ⁻¹ᵁ UK).ι, Category.assoc, hk, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc]
        apply hret
        rw [Category.assoc, hyK, ← Category.assoc, he, Category.assoc, hr1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, he, Category.assoc, hr2]
    · rw [← cancel_mono UK.ι, Category.assoc, he, ← Category.assoc, hk, hg'r, Category.id_comp]
  have hjVrange : Set.range jV ⊆ Set.range UK.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    exact hU v
  have hjV' : IsOpenImmersion.lift UK.ι jV hjVrange ≫ UK.ι = jV := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (IsOpenImmersion.lift UK.ι jV hjVrange) := by
    haveI : IsOpenImmersion (IsOpenImmersion.lift UK.ι jV hjVrange ≫ UK.ι) := by rw [hjV']; infer_instance
    exact IsOpenImmersion.of_comp _ UK.ι
  let jN : V ⟶ pullback g P := IsOpenImmersion.lift UK.ι jV hjVrange ≫ inv (r ∣_ UK) ≫ (r ⁻¹ᵁ UK).ι
  have hjNr : jN ≫ r = jV := by
    simp only [jN, Category.assoc, ← he, IsIso.inv_hom_id_assoc, hjV']
  have hrange : r ⁻¹' Set.range jV = Set.range jN := by
    ext p
    constructor
    · rintro ⟨v, hv⟩
      have hpU : p ∈ r ⁻¹ᵁ UK := by
        rw [Scheme.Hom.mem_preimage, ← hv]
        exact hU v
      obtain ⟨q, rfl⟩ : p ∈ Set.range (r ⁻¹ᵁ UK).ι := by rw [Scheme.Opens.range_ι]; exact hpU
      have hq : (r ∣_ UK) q = IsOpenImmersion.lift UK.ι jV hjVrange v := by
        apply UK.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply, ← hv, ← Scheme.Hom.comp_apply, hjV']
      refine ⟨v, ?_⟩
      simp only [jN, Scheme.Hom.comp_apply, ← hq]
      rw [show (inv (r ∣_ UK)) ((r ∣_ UK) q) = q from Scheme.hom_inv_apply (asIso (r ∣_ UK)) q]
    · rintro ⟨v, rfl⟩
      exact ⟨v, by rw [← Scheme.Hom.comp_apply, hjNr]⟩
  have hsub : ∀ p ∈ r ⁻¹ᵁ UK, p ∈ closure (Set.range jN) := by
    intro p hp
    obtain ⟨q, rfl⟩ : p ∈ Set.range (r ⁻¹ᵁ UK).ι := by rw [Scheme.Opens.range_ι]; exact hp
    rw [mem_closure_iff]
    intro O hO hqO
    have hS : IsOpen ((r ⁻¹ᵁ UK).ι ⁻¹' O) := hO.preimage (r ⁻¹ᵁ UK).ι.continuous
    have hT : IsOpen (UK.ι '' ((r ∣_ UK) '' ((r ⁻¹ᵁ UK).ι ⁻¹' O))) :=
      UK.ι.isOpenEmbedding.isOpenMap _ ((r ∣_ UK).isOpenEmbedding.isOpenMap _ hS)
    obtain ⟨_, ⟨_, ⟨s0, hs0, rfl⟩, rfl⟩, v, hv⟩ := hd.inter_open_nonempty _ hT ⟨_, ⟨_, ⟨q, hqO, rfl⟩, rfl⟩⟩
    refine ⟨(r ⁻¹ᵁ UK).ι s0, hs0, ?_⟩
    rw [← hrange]
    exact ⟨v, by rw [hv, ← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]⟩
  have hdense : Dense (Set.range jN) := by
    intro p
    obtain ⟨w, hwW, hwn⟩ := exists_specializes_of_dense_scheme N _ (f ⁻¹ᵁ U).isOpen hW (pullback.fst g P p)
    obtain ⟨p', hp'p, hp'w⟩ := Flat.generalizingMap (pullback.fst g P) hwn
    apply hp'p.mem_closed isClosed_closure
    apply hsub
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hr1, Scheme.Hom.comp_apply, hp'w]
    exact hwW
  exact ⟨jN, inferInstance, hdense, hjNr, hrange⟩

theorem lifts_to_normalisation : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (Z X' N V : Scheme.{0})
    (s : Z ⟶ Sp R) (b : X' ⟶ Z) (ν : N ⟶ X') (U : Z.Opens) (jV : V ⟶ pullback s (spMap (algebraMap R K))),
    IsLocallyNoetherian N → IsOpenImmersion jV → Dense (Set.range jV) →
    (∀ v, pullback.fst s (spMap (algebraMap R K)) (jV v) ∈ U) → IsIso (b ∣_ U) → IsIso (ν ∣_ (b ⁻¹ᵁ U)) →
    Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ U) : N.Opens) : Set N) →
    ∃ jN : V ⟶ pullback (ν ≫ b ≫ s) (spMap (algebraMap R K)), IsOpenImmersion jN ∧ Dense (Set.range jN) ∧
      jN ≫ pullback.map (ν ≫ b ≫ s) (spMap (algebraMap R K)) s (spMap (algebraMap R K)) (ν ≫ b) (𝟙 _) (𝟙 _)
        (by simp) (by simp) = jV ∧
      pullback.map (ν ≫ b ≫ s) (spMap (algebraMap R K)) s (spMap (algebraMap R K)) (ν ≫ b) (𝟙 _) (𝟙 _)
        (by simp) (by simp) ⁻¹' Set.range jV = Set.range jN := by
  intro R K _ _ _ _ _ Z X' N V s b ν U jV hN hjV hjVd hjVU hb hν hWd
  haveI := hN; haveI := hjV; haveI := hb; haveI := hν
  haveI : IsIso ((ν ≫ b) ∣_ U) := by rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hb
  haveI : Flat (spMap (algebraMap R K)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  exact lift_of_isIso_over s (spMap (algebraMap R K)) (ν ≫ b) (ν ≫ b ≫ s) (Category.assoc _ _ _) U hWd jV hjVd hjVU _
    (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans (Category.comp_id _))

end GlobalTheory.BlowOpen
