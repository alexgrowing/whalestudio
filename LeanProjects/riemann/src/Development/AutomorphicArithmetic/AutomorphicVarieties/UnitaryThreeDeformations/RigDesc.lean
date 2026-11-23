import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E]

private def dualIncl (K : IntermediateField F E) : DualNumber ↥K →+* DualNumber E where
  toFun x := TrivSqZeroExt.inl ((x.fst : ↥K) : E) + TrivSqZeroExt.inr ((x.snd : ↥K) : E)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private theorem dualIncl_fst (K : IntermediateField F E) (x : DualNumber ↥K) :
    (dualIncl K x).fst = ((x.fst : ↥K) : E) := by simp [dualIncl]

private theorem dualIncl_snd (K : IntermediateField F E) (x : DualNumber ↥K) :
    (dualIncl K x).snd = ((x.snd : ↥K) : E) := by simp [dualIncl]

private theorem dualIncl_inj (K : IntermediateField F E) : Function.Injective (dualIncl K) := by
  intro x y h
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [dualIncl_fst, dualIncl_fst] at h1
  rw [dualIncl_snd, dualIncl_snd] at h2
  exact TrivSqZeroExt.ext (Subtype.ext h1) (Subtype.ext h2)

private theorem gl_desc (K : IntermediateField F E) (u : GL (Fin 3) (DualNumber E))
    (hu : ∀ a b, ((u : Matrix (Fin 3) (Fin 3) (DualNumber E)) a b).fst ∈ K ∧
      ((u : Matrix (Fin 3) (Fin 3) (DualNumber E)) a b).snd ∈ K) :
    ∃ v : GL (Fin 3) (DualNumber ↥K), Matrix.GeneralLinearGroup.map (dualIncl K) v = u := by
  let A : Matrix (Fin 3) (Fin 3) (DualNumber ↥K) := Matrix.of fun a b =>
    TrivSqZeroExt.inl (⟨_, (hu a b).1⟩ : ↥K) + TrivSqZeroExt.inr (⟨_, (hu a b).2⟩ : ↥K)
  have hA : A.map (dualIncl K) = (u : Matrix (Fin 3) (Fin 3) (DualNumber E)) := by
    refine Matrix.ext fun a b => ?_
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [Matrix.map_apply, dualIncl_fst]; simp [A]
    · rw [Matrix.map_apply, dualIncl_snd]; simp [A]
  have hd : IsUnit A.det := by
    have h1 : IsUnit (dualIncl K A.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hA]
      exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualIncl_fst, isUnit_iff_ne_zero] at h1
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
    intro h0
    exact h1 (by rw [h0]; rfl)
  exact ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, Units.ext hA⟩

private theorem gg_range_iff (K : IntermediateField F E) (x : GG 3 (DualNumber E)) :
    x ∈ (GG.map (m := 3) (dualIncl K)).range ↔
      ∀ a b, (x.mat a b).fst ∈ K ∧ (x.mat a b).snd ∈ K := by
  constructor
  · rintro ⟨y, rfl⟩ a b
    rw [GG.map_mat, Matrix.map_apply, dualIncl_fst, dualIncl_snd]
    exact ⟨SetLike.coe_mem _, SetLike.coe_mem _⟩
  · intro h
    obtain ⟨v, hv⟩ := gl_desc K x.left h
    exact ⟨⟨v, x.right⟩, SemidirectProduct.ext hv rfl⟩

private theorem ggmap_inj {C B : Type} [CommRing C] [CommRing B] (ι : C →+* B) (hι : Function.Injective ι) :
    Function.Injective (GG.map (m := 3) ι) := fun x y h => by
  refine SemidirectProduct.ext (Units.ext ?_) (congrArg SemidirectProduct.right h :)
  refine Matrix.ext fun a b => ?_
  exact hι (congrFun (congrFun (congrArg GG.mat h) a) b)

private def ents (A : Matrix (Fin 3) (Fin 3) (DualNumber E)) : Set E :=
  Set.range (fun p : Fin 3 × Fin 3 => (A p.1 p.2).fst) ∪
    Set.range (fun p : Fin 3 × Fin 3 => (A p.1 p.2).snd)

private theorem ents_finite (A : Matrix (Fin 3) (Fin 3) (DualNumber E)) : (ents A).Finite :=
  (Set.finite_range _).union (Set.finite_range _)

private theorem of_ents {A : Matrix (Fin 3) (Fin 3) (DualNumber E)} {K : IntermediateField F E}
    (h : ents A ⊆ K) (a b : Fin 3) : (A a b).fst ∈ K ∧ (A a b).snd ∈ K :=
  ⟨h (Or.inl ⟨(a, b), rfl⟩), h (Or.inr ⟨(a, b), rfl⟩)⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.rig_desc :
    ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (r' : Γ →* GG 3 (DualNumber (PadicAlgCl l))) (h : GL (Fin 3) (DualNumber (PadicAlgCl l))), (∀ a b, Continuous fun g => ((r' g).mat a b).fst) → (∀ a b, Continuous fun g => ((r' g).mat a b).snd) → ∃ (L : Formalism.BasicNotions.Loc.FinExt l) (f : DualNumber ↥L.1 →+* DualNumber (PadicAlgCl l)) (r₁ : Γ →* GG 3 (DualNumber ↥L.1)) (h₁ : GL (Fin 3) (DualNumber ↥L.1)), (∀ x, (f x).fst = ((x.fst : ↥L.1) : PadicAlgCl l) ∧ (f x).snd = ((x.snd : ↥L.1) : PadicAlgCl l)) ∧ (GG.map f).comp r₁ = r' ∧ Matrix.GeneralLinearGroup.map f h₁ = h := by
  intro l _ Γ _ _ _ _ _ r' h hc1 hc2
  obtain ⟨ι, _, K, hK, hcov⟩ := GlobalTheory.CompactRepField.exists_countable_family l
  let S : IntermediateField ℚ_[l] (PadicAlgCl l) → Subgroup Γ := fun M =>
    (GG.map (m := 3) (dualIncl M)).range.comap r'
  have hS : ∀ M g, g ∈ S M ↔ ∀ a b, ((r' g).mat a b).fst ∈ M ∧ ((r' g).mat a b).snd ∈ M :=
    fun M g => gg_range_iff M (r' g)
  have hKcl : ∀ m, IsClosed (K m : Set (PadicAlgCl l)) := fun m =>
    haveI : FiniteDimensional ℚ_[l] (K m).toSubalgebra.toSubmodule := hK m
    Submodule.closed_of_finiteDimensional (K m).toSubalgebra.toSubmodule
  have hcl : ∀ m, IsClosed (S (K m) : Set Γ) := fun m => by
    have : (S (K m) : Set Γ) = ⋂ a, ⋂ b,
        ((fun g => ((r' g).mat a b).fst) ⁻¹' (K m) ∩ (fun g => ((r' g).mat a b).snd) ⁻¹' (K m)) := by
      ext g
      simp only [Set.mem_iInter]
      exact hS _ g
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      ((hKcl m).preimage (hc1 a b)).inter ((hKcl m).preimage (hc2 a b))
  have hun : ⋃ m, (S (K m) : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨m, hm⟩ := hcov _ (ents_finite (r' g).mat)
    exact Set.mem_iUnion.2 ⟨m, (hS _ g).2 (of_ents hm)⟩
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (S (K m) : Set Γ) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (Γ ⧸ S (K m)) := Subgroup.quotient_finite_of_isOpen _ hop
  obtain ⟨n, hn⟩ := hcov (ents (h : Matrix (Fin 3) (Fin 3) (DualNumber (PadicAlgCl l))) ∪
      ⋃ q : Γ ⧸ S (K m), ents (r' q.out).mat)
    ((ents_finite _).union (Set.finite_iUnion fun q => ents_finite _))
  haveI := hK m
  haveI := hK n
  have hmono : ∀ M M', M ≤ M' → S M ≤ S M' := fun M M' hM g hg =>
    (hS _ g).2 fun a b => ⟨hM ((hS _ g).1 hg a b).1, hM ((hS _ g).1 hg a b).2⟩
  have hall : ∀ g, g ∈ S (K n ⊔ K m) := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (S (K m)) g
    have hg : g = (g : Γ ⧸ S (K m)).out * (k : Γ)⁻¹ := by
      rw [hk, mul_inv_cancel_right]
    rw [hg]
    refine mul_mem (hmono _ _ le_sup_left ?_) (hmono _ _ le_sup_right (inv_mem k.2))
    exact (hS _ _).2 (of_ents fun z hz => hn (Or.inr (Set.mem_iUnion.2 ⟨_, hz⟩)))
  obtain ⟨h₁, hh₁⟩ := gl_desc (K n ⊔ K m) h
    (of_ents fun z hz => (le_sup_left : K n ≤ K n ⊔ K m) (hn (Or.inl hz)))
  have hall' : ∀ g, ∃ y, GG.map (m := 3) (dualIncl (K n ⊔ K m)) y = r' g := hall
  choose u hu using hall'
  exact ⟨⟨K n ⊔ K m, inferInstance⟩, dualIncl (K n ⊔ K m),
    MonoidHom.mk' u fun g g' => ggmap_inj _ (dualIncl_inj _) (by rw [map_mul, hu, hu, hu, map_mul]),
    h₁, fun x => ⟨dualIncl_fst _ x, dualIncl_snd _ x⟩, MonoidHom.ext hu, hh₁⟩
