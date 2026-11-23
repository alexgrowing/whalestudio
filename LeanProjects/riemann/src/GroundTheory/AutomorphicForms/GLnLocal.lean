import Mathlib
import GroundTheory.AutomorphicForms.LocallyProfinite

noncomputable section

namespace GroundTheory.Automorphic

open ValuativeRel Topology Filter Set

namespace GLnLocal

variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)

section Algebraic

def integralMatrices : Subring (Matrix (Fin n) (Fin n) F) :=
  (RingHom.mapMatrix (𝒪[F]).subtype).range

theorem mem_integralMatrices {A : Matrix (Fin n) (Fin n) F} :
    A ∈ integralMatrices F n ↔ ∀ i j, A i j ∈ 𝒪[F] := by
  constructor
  · rintro ⟨B, rfl⟩ i j
    exact (B i j).2
  · intro h
    exact ⟨Matrix.of fun i j => ⟨A i j, h i j⟩, rfl⟩

def integralGLHom : GL (Fin n) 𝒪[F] →* GL (Fin n) F :=
  Units.map (RingHom.mapMatrix (𝒪[F]).subtype).toMonoidHom

@[simp]
theorem integralGLHom_apply (u : GL (Fin n) 𝒪[F]) (i j : Fin n) :
    integralGLHom F n u i j = (u i j : F) :=
  rfl

theorem integralGLHom_injective : Function.Injective (integralGLHom F n) := fun _ _ h =>
  Units.ext <| Matrix.ext fun i j => Subtype.ext (congrArg (fun g : GL (Fin n) F => g i j) h)

def integralGL : Subgroup (GL (Fin n) F) :=
  (integralGLHom F n).range

def integralGLEquiv : GL (Fin n) 𝒪[F] ≃* integralGL F n :=
  MonoidHom.ofInjective (integralGLHom_injective F n)

theorem mem_integralGL_iff {g : GL (Fin n) F} :
    g ∈ integralGL F n ↔ (∀ i j, g i j ∈ 𝒪[F]) ∧ ∀ i j, (g⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => (u i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((u⁻¹ : GL (Fin n) 𝒪[F]) i j).2
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨g i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) 𝒪[F] :=
      Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) F) i j, h2 i j⟩
    have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) (𝒪[F]).subtype) :=
      fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    have hA : RingHom.mapMatrix (𝒪[F]).subtype A = (g : Matrix (Fin n) (Fin n) F) := rfl
    have hB : RingHom.mapMatrix (𝒪[F]).subtype B =
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl
    have hAB : A * B = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
    have hBA : B * A = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

theorem integralGL_eq_units : integralGL F n = (integralMatrices F n).toSubmonoid.units := by
  ext g
  rw [mem_integralGL_iff, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Subring.mem_toSubmonoid, mem_integralMatrices, mem_integralMatrices]

end Algebraic

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

instance t2Space : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

section Uniformizer

def uniformizer : 𝒪[F] := (IsDiscreteValuationRing.exists_irreducible (R := 𝒪[F])).choose

theorem irreducible_uniformizer : Irreducible (uniformizer F) :=
  (IsDiscreteValuationRing.exists_irreducible (R := 𝒪[F])).choose_spec

theorem maximalIdeal_pow_eq (m : ℕ) :
    IsLocalRing.maximalIdeal 𝒪[F] ^ m = Ideal.span {uniformizer F ^ m} := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (irreducible_uniformizer F),
    Ideal.span_singleton_pow]

theorem mem_maximalIdeal_pow_iff {m : ℕ} {y : 𝒪[F]} :
    y ∈ IsLocalRing.maximalIdeal 𝒪[F] ^ m ↔
      valuation F (y : F) ≤ valuation F (uniformizer F : F) ^ m := by
  rw [maximalIdeal_pow_eq, Ideal.mem_span_singleton,
    (Valuation.integer.integers (valuation F)).dvd_iff_le]
  simp only [map_pow]
  exact Iff.rfl

theorem valuation_uniformizer_lt_one : valuation F (uniformizer F : F) < 1 := by
  have h1 : valuation F (uniformizer F : F) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).mp (uniformizer F).2
  refine lt_of_le_of_ne h1 fun h => (irreducible_uniformizer F).not_isUnit ?_
  exact (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.mpr h

theorem valuation_uniformizer_ne_zero : valuation F (uniformizer F : F) ≠ 0 := by
  rw [Valuation.ne_zero_iff]
  intro h
  exact (irreducible_uniformizer F).ne_zero (Subtype.ext h)

theorem eq_zero_of_forall_valuation_le {x : F}
    (h : ∀ m : ℕ, valuation F x ≤ valuation F (uniformizer F : F) ^ m) : x = 0 := by
  by_contra hx
  have hx' : valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hx')
  exact (h m).not_gt (by simpa using hm)

theorem isOpen_valuation_le {γ : ValueGroupWithZero F} (hγ : γ ≠ 0) :
    IsOpen {x : F | valuation F x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz => ?_⟩
  have hz' : valuation F (z - x) < γ := by simpa using hz
  have hx' : valuation F x ≤ γ := hx
  show valuation F z ≤ γ
  calc valuation F z = valuation F ((z - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation F (z - x)) (valuation F x) := Valuation.map_add _ _ _
    _ ≤ γ := max_le hz'.le hx'

end Uniformizer

instance locallyCompactSpace_matrix : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))

section IntegralGL

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem continuous_entry (i j : Fin n) : Continuous fun g : GL (Fin n) F => g i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_inv_entry (i j : Fin n) :
    Continuous fun g : GL (Fin n) F => (g⁻¹ : GL (Fin n) F) i j :=
  (continuous_entry F n i j).comp continuous_inv

theorem isOpen_integralGL : IsOpen (integralGL F n : Set (GL (Fin n) F)) := by
  have : (integralGL F n : Set (GL (Fin n) F)) = ⋂ i, ⋂ j,
      ((fun g : GL (Fin n) F => g i j) ⁻¹' (𝒪[F] : Set F) ∩
        (fun g : GL (Fin n) F => (g⁻¹ : GL (Fin n) F) i j) ⁻¹' (𝒪[F] : Set F)) := by
    ext g
    simp only [SetLike.mem_coe, mem_integralGL_iff, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage]
    exact ⟨fun h i j => ⟨h.1 i j, h.2 i j⟩, fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩⟩
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (Valuation.isOpen_integer.preimage (continuous_entry F n i j)).inter
      (Valuation.isOpen_integer.preimage (continuous_inv_entry F n i j))

theorem isCompact_integralGL : IsCompact (integralGL F n : Set (GL (Fin n) F)) := by
  rw [integralGL_eq_units]
  apply Submonoid.units_isCompact
  have : ((integralMatrices F n).toSubmonoid : Set (Matrix (Fin n) (Fin n) F)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (𝒪[F] : Set F) := by
    ext A
    change A ∈ integralMatrices F n ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, A i j ∈ (𝒪[F] : Set F)
    rw [mem_integralMatrices]
    simp
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))

end IntegralGL

section Congruence

def reduction (m : ℕ) :
    GL (Fin n) 𝒪[F] →* GL (Fin n) (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F] ^ m) :=
  Units.map (RingHom.mapMatrix (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F] ^ m))).toMonoidHom

def congruenceSubgroup (m : ℕ) : Subgroup (GL (Fin n) F) :=
  (reduction F n m).ker.map (integralGLHom F n)

theorem mem_ker_reduction_iff {m : ℕ} {u : GL (Fin n) 𝒪[F]} :
    u ∈ (reduction F n m).ker ↔ ∀ i j,
      valuation F ((u i j : F) - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F (uniformizer F : F) ^ m := by
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have h1 : (1 : Matrix (Fin n) (Fin n) (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F] ^ m)) i j =
      Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 : (((1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j : 𝒪[F]) : F) =
      (1 : Matrix (Fin n) (Fin n) F) i j := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1]
  change Ideal.Quotient.mk _ (u i j) = _ ↔ _
  rw [Ideal.Quotient.eq, mem_maximalIdeal_pow_iff, AddSubgroupClass.coe_sub, h2]

theorem mem_congruenceSubgroup_iff {m : ℕ} {g : GL (Fin n) F} :
    g ∈ congruenceSubgroup F n m ↔ g ∈ integralGL F n ∧ ∀ i j,
      valuation F (g i j - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F (uniformizer F : F) ^ m := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (mem_ker_reduction_iff F n).mp hu⟩
  · rintro ⟨⟨u, rfl⟩, h⟩
    exact ⟨u, (mem_ker_reduction_iff F n).mpr h, rfl⟩

theorem congruenceSubgroup_le (m : ℕ) : congruenceSubgroup F n m ≤ integralGL F n :=
  Subgroup.map_le_range _ _

theorem congruenceSubgroup_zero : congruenceSubgroup F n 0 = integralGL F n := by
  refine le_antisymm (congruenceSubgroup_le F n 0) fun g hg => ?_
  rw [mem_congruenceSubgroup_iff, pow_zero]
  refine ⟨hg, fun i j => ?_⟩
  have h0 := ((mem_integralGL_iff F n).mp hg).1 i j
  have h1 : (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  exact (Valuation.mem_integer_iff _ _).mp (Subring.sub_mem _ h0 h1)

theorem congruenceSubgroup_antitone : Antitone (congruenceSubgroup F n) := by
  intro m m' hmm' g hg
  rw [mem_congruenceSubgroup_iff] at hg ⊢
  exact ⟨hg.1, fun i j => (hg.2 i j).trans
    (pow_le_pow_right_of_le_one' (valuation_uniformizer_lt_one F).le hmm')⟩

theorem conj_mem_congruenceSubgroup {m : ℕ} {k x : GL (Fin n) F} (hk : k ∈ integralGL F n)
    (hx : x ∈ congruenceSubgroup F n m) : k * x * k⁻¹ ∈ congruenceSubgroup F n m := by
  obtain ⟨u, rfl⟩ := hk
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨u * y * u⁻¹, (reduction F n m).normal_ker.conj_mem y hy u, by simp [map_mul, map_inv]⟩

theorem congruenceSubgroup_normal (m : ℕ) :
    ((congruenceSubgroup F n m).subgroupOf (integralGL F n)).Normal :=
  ⟨fun x hx k => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using conj_mem_congruenceSubgroup F n k.2 hx⟩

theorem isOpen_congruenceSubgroup (m : ℕ) :
    IsOpen (congruenceSubgroup F n m : Set (GL (Fin n) F)) := by
  have : (congruenceSubgroup F n m : Set (GL (Fin n) F)) = (integralGL F n : Set _) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) F => g i j - (1 : Matrix (Fin n) (Fin n) F) i j) ⁻¹'
        {x | valuation F x ≤ valuation F (uniformizer F : F) ^ m} := by
    ext g
    simp only [SetLike.mem_coe, mem_congruenceSubgroup_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_ofPred_eq]
  rw [this]
  exact (isOpen_integralGL F n).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite
    fun j => (isOpen_valuation_le F (pow_ne_zero _ (valuation_uniformizer_ne_zero F))).preimage
      ((continuous_entry F n i j).sub continuous_const))

theorem isClosed_congruenceSubgroup (m : ℕ) :
    IsClosed (congruenceSubgroup F n m : Set (GL (Fin n) F)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_congruenceSubgroup F n m)

theorem isCompact_congruenceSubgroup (m : ℕ) :
    IsCompact (congruenceSubgroup F n m : Set (GL (Fin n) F)) :=
  (isCompact_integralGL F n).of_isClosed_subset (isClosed_congruenceSubgroup F n m)
    fun _ hx => congruenceSubgroup_le F n m hx

theorem iInf_congruenceSubgroup : ⨅ m, congruenceSubgroup F n m = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => ?_
  rw [Subgroup.mem_iInf] at hg
  rw [Subgroup.mem_bot]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := eq_zero_of_forall_valuation_le F fun m =>
    ((mem_congruenceSubgroup_iff F n).mp (hg m)).2 i j
  rw [sub_eq_zero] at this
  simpa using this

theorem hasBasis_nhds_one :
    (𝓝 (1 : GL (Fin n) F)).HasBasis (fun _ : ℕ => True)
      fun m => (congruenceSubgroup F n m : Set (GL (Fin n) F)) := by
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨m, _, hm⟩ => Filter.mem_of_superset
    ((isOpen_congruenceSubgroup F n m).mem_nhds (one_mem _)) hm⟩⟩
  have hclosed : ∀ m, IsClosed ((congruenceSubgroup F n m : Set (GL (Fin n) F)) ∩ (interior U)ᶜ) :=
    fun m => (isClosed_congruenceSubgroup F n m).inter isOpen_interior.isClosed_compl
  have hempty : (integralGL F n : Set (GL (Fin n) F)) ∩
      ⋂ m, ((congruenceSubgroup F n m : Set (GL (Fin n) F)) ∩ (interior U)ᶜ) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun g ⟨_, hg⟩ => ?_
    rw [Set.mem_iInter] at hg
    have h1 : g ∈ ⨅ m, congruenceSubgroup F n m := Subgroup.mem_iInf.mpr fun m => (hg m).1
    rw [iInf_congruenceSubgroup, Subgroup.mem_bot] at h1
    exact (hg 0).2 (by rw [h1]; exact mem_interior_iff_mem_nhds.mpr hU)
  have hanti : Antitone fun m => (congruenceSubgroup F n m : Set (GL (Fin n) F)) ∩ (interior U)ᶜ :=
    fun m m' h => Set.inter_subset_inter_left _
      (SetLike.coe_subset_coe.mpr (congruenceSubgroup_antitone F n h))
  obtain ⟨m, hm⟩ :=
    (isCompact_integralGL F n).elim_directed_family_closed _ hclosed hempty hanti.directed_ge
  refine ⟨m, trivial, fun g hg => interior_subset (by_contra fun h => ?_)⟩
  have : g ∈ (integralGL F n : Set (GL (Fin n) F)) ∩
      ((congruenceSubgroup F n m : Set (GL (Fin n) F)) ∩ (interior U)ᶜ) :=
    ⟨congruenceSubgroup_le F n m hg, hg, h⟩
  rw [hm] at this
  exact this

end Congruence

instance totallyDisconnectedSpace : TotallyDisconnectedSpace (GL (Fin n) F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.Subset.antisymm (fun g hg => ?_) (Set.singleton_subset_iff.mpr mem_connectedComponent)
  have : g ∈ ⨅ m, congruenceSubgroup F n m := Subgroup.mem_iInf.mpr fun m =>
    IsClopen.connectedComponent_subset
      ⟨isClosed_congruenceSubgroup F n m, isOpen_congruenceSubgroup F n m⟩ (one_mem _) hg
  rw [iInf_congruenceSubgroup, Subgroup.mem_bot] at this
  exact this

theorem isLocallyProfinite :
    IsTopologicalGroup (GL (Fin n) F) ∧ LocallyCompactSpace (GL (Fin n) F) ∧
      T2Space (GL (Fin n) F) ∧ TotallyDisconnectedSpace (GL (Fin n) F) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end GLnLocal

end GroundTheory.Automorphic
