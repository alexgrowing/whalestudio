import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

private theorem ab_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G',
      ∀ g : G, F (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ (f g) := by
  have hc : (commutator G).topologicalClosure ≤ ((commutator G').topologicalClosure).comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact Subgroup.le_topologicalClosure _
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  exact ⟨QuotientGroup.map _ _ f hc, fun g => rfl⟩

private theorem map_prim {A B : Type} [CommGroup A] [CommGroup B] (l : ℕ) [Fact l.Prime] (F : A →* B) {x : A}
    (hx : x ∈ CommGroup.primaryComponent A l) : F x ∈ CommGroup.primaryComponent B l := by
  obtain ⟨k, hk⟩ := (Iff.rfl : x ∈ CommGroup.primaryComponent A l ↔ ∃ k : ℕ, x ^ l ^ k = 1).mp hx
  exact (Iff.rfl : F x ∈ CommGroup.primaryComponent B l ↔ ∃ k : ℕ, F x ^ l ^ k = 1).mpr
    ⟨k, by rw [← map_pow, hk, map_one]⟩

open UpperTheory.V.W in
private theorem locAb_transport (l : ℕ) [Fact l.Prime] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (e : G ≃* G') (he : Continuous e) (he' : Continuous e.symm)
    (I : Subgroup G) (I' : Subgroup G') (hI : ∀ g, e g ∈ I' ↔ g ∈ I) (d : ℕ) (A : LocAb l G' I' d) :
    Nonempty (LocAb l G I d) := by
  obtain ⟨Fe, hFe⟩ := ab_map e.toMonoidHom he
  obtain ⟨Fs, hFs⟩ := ab_map e.symm.toMonoidHom he'
  have mu1 : ∀ g, g ∈ muG l G → e g ∈ muG l G' := by
    intro g hg
    have h1 := map_prim l Fe (x := QuotientGroup.mk' (commutator G).topologicalClosure g) hg
    have h2 := hFe g
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [h2] at h1
    exact h1
  have mu2 : ∀ g', g' ∈ muG l G' → e.symm g' ∈ muG l G := by
    intro g hg
    have h1 := map_prim l Fs (x := QuotientGroup.mk' (commutator G').topologicalClosure g) hg
    have h2 := hFs g
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [h2] at h1
    exact h1
  let bm : CommGroup.primaryComponent (TopologicalAbelianization G') l →*
      CommGroup.primaryComponent (TopologicalAbelianization G) l :=
    MonoidHom.codRestrict (Fs.comp (CommGroup.primaryComponent _ l).subtype) _
      (fun x => map_prim l Fs x.2)
  refine ⟨LocAb.mk (A.a.comp e.toMonoidHom) (A.cont.comp he) (A.surj.comp e.surjective) ?_ ?_
    ((bm.comp A.b).comp e.toMonoidHom) ?_ ?_⟩
  · intro x
    rw [← A.inertia x]
    constructor
    · rintro ⟨g, hg, h⟩
      exact ⟨e g, (hI g).2 hg, h⟩
    · rintro ⟨g', hg', h⟩
      exact ⟨e.symm g', (hI _).1 (by simpa using hg'), by simpa using h⟩
  · intro C _ _ hC χ hχo hmu
    have key := A.univ C hC (χ.comp e.symm.toMonoidHom) (hχo.preimage he') (by
      intro g' hg'
      exact (MonoidHom.mem_ker).1 (hmu (mu2 g' hg')))
    intro g hg
    have h3 : e g ∈ (χ.comp e.symm.toMonoidHom).ker :=
      key (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hg))
    have h5 := MonoidHom.mem_ker.1 h3
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h5
    exact MonoidHom.mem_ker.2 h5
  · refine Subgroup.isOpen_mono (H₁ := A.b.ker.comap e.toMonoidHom) ?_ (A.b_open.preimage he)
    intro g hg
    rw [Subgroup.mem_comap, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_one]
  · intro g hg
    show Fs ((A.b (e g)) : TopologicalAbelianization G') = _
    rw [A.b_mu _ (mu1 g hg)]
    have h4 := hFs (e g)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h4
    exact h4

open Formalism.BasicNotions.Loc in
theorem UpperTheory.nonempty_localWeilData_decompositionGroup_of_mem_place :
    ∀ (l : ℕ) [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)), IsPlaceOver A w → ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Nonempty (UpperTheory.V.W.LocAb l (Dec (F := F) A) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) (locDeg w)) := by
  intro l _ F Ω _ _ _ _ _ _ A w hA hl
  obtain ⟨j, hj⟩ := (UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).1 A w hA hl
  subst hj
  obtain ⟨-, φ, hφ, -, hran, hin, -, hidx⟩ := (UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK : ∀ τ, τ ∈ GK K ↔ ∀ x : F, τ (j (algebraMap F Ω x)) = j (algebraMap F Ω x) :=
    GlobalTheory.PlaceBridge.mem_GK_iff (E := F) (Ω := Ω) K rfl
  have hR : φ.range = GK K := by
    ext τ
    rw [hran τ, hK τ]
  have hd : Module.finrank ℚ_[l] K.1 = locDeg w := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← hidx w hA, hR]
    rfl
  obtain ⟨B⟩ := UpperTheory.V.W.lam_local l K
  rw [hd] at B
  let e := (MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hR)
  refine locAb_transport l e ?_ ?_ _ _ ?_ _ B
  · exact continuous_induced_rng.2 hφ.continuous
  · refine hφ.toIsEmbedding.continuous_iff.2 ?_
    have h : (⇑φ ∘ ⇑e.symm) = Subtype.val := funext fun τ => congrArg Subtype.val (e.apply_symm_apply τ)
    rw [h]
    exact continuous_subtype_val
  · intro g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hin g
