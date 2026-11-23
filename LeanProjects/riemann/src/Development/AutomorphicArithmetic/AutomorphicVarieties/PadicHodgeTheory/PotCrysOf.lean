import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHost
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem cr_transport {l : ℕ} [Fact l.Prime] {G G' A V : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A G' V}
    (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : IsCr φ ρ → IsCr φ' ρ' := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  unfold IsCr
  rw [hr, hc]
  exact id

private theorem crys_of_isCr {l : ℕ} [Fact l.Prime] (K E' : FinExt l) {n : ℕ}
    (ρ : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1)) (h : IsCr (GK K).subtype ρ) :
    Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ := by
  have := E'.2
  have : IsModuleTopology ℚ_[l] (Fin n → ↥E'.1) := isModuleTopologyOfFiniteDimensional
  exact (isCrField K ρ).1.1 ((isCrIff K ρ).1.1 h)

private theorem ex_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j ∧
      Bw.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl, rfl⟩

theorem UpperTheory.V.Loc.potCrysOf :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ {n : ℕ} (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (E' : FinExt l) (r' : H →* GL (Fin n) ↥E'.1), (∀ h a b, (((r' h : Matrix (Fin n) (Fin n) ↥E'.1) a b : ↥E'.1) : Om l) = (r (ψ h) : Matrix (Fin n) (Fin n) (Qbar l)) a b) → IsCr φ (colRep r') → UpperTheory.V.Af.PotCrysAt r (placeJ j) := by
  intro F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hφψ n r hr E' r' hr' hcr
  have hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := fun x => by
    change Valued.v (j x) ≤ 1 ↔ _
    rw [PadicAlgCl.valuation_def]
    exact Iff.rfl
  obtain ⟨L, Bw, hBj, hK⟩ := ex_bridge (E := F) j hj
  refine ⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw, fun x => by rw [hBj]; exact hj x, ?_⟩
  haveI : CompactSpace ↥(GK Bw.Kw) := by
    haveI := Bw.Kw.2
    exact isCompact_iff_compactSpace.1 Bw.Kw.1.fixingSubgroup_isClosed.isCompact
  haveI : CompactSpace ↥(Dec (F := F) (placeJ j)) :=
    Bw.e.symm.surjective.compactSpace Bw.e_symm_cont
  haveI : T2Space ↥(Dec (F := F) (placeJ j)) := inferInstance
  let r₀ := r.comp (Dec (F := F) (placeJ j)).subtype
  have hc0 : Continuous fun g => ((r₀ g : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) :=
    Units.continuous_val.comp (hr.comp continuous_subtype_val)
  obtain ⟨LL, hL, hent⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l _ n r₀ hc0 (GlobalTheory.Pst.supExt Bw.LL E')
  obtain ⟨r₁, hr₁⟩ := GlobalTheory.CompactRepField.exists_hom_of_entries_mem r₀ LL.1 hent
  have l₁ : Bw.LL.1 ≤ LL.1 := le_trans le_sup_left hL
  have l₂ : E'.1 ≤ LL.1 := le_trans le_sup_right hL
  refine ⟨LL, r₁, ⟨l₁, ?_⟩, ?_⟩
  · ext g a b
    exact hr₁ g a b
  obtain ⟨K, e, -, -, he, hKr, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  have hle : GK K ≤ GK Bw.Kw := by
    rw [← hKr]
    rintro _ ⟨g, rfl⟩
    rw [GlobalTheory.PlaceBridge.mem_GK_iff Bw.Kw hK]
    intro x
    rw [hφψ, AlgEquiv.commutes]
  have h : Bw.Kw.1 ≤ K.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1]
    exact IntermediateField.fixedField_le hle
  refine ⟨K, h, ?_⟩
  let ρK : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1) := (colRep r').comp e.symm.toMonoidHom
  have t1 : IsCr (GK K).subtype ρK := cr_transport e e.surjective he' (fun g x => by simp [ρK]) hcr
  have t2 := crys_of_isCr K E' ρK t1
  let _ : Algebra ↥E'.1 ↥LL.1 := (IntermediateField.inclusion l₂).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥E'.1 ↥LL.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := LL.2
  have : FiniteDimensional ↥E'.1 ↥LL.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  refine (GlobalTheory.Pst.isCrys_ext_iff _ (ρ := ρK) fun g => ⟨r' (e.symm g), fun _ => rfl, fun x => ?_⟩).2 t2
  have hg : ((Bw.e.symm (Subgroup.inclusion (GK_le h) g) : ↥(Dec (F := F) (placeJ j))) : G F Ω) = ψ (e.symm g) := by
    apply AlgEquiv.ext
    intro y
    apply j.injective
    have h1 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) y
    rw [hBj, MulEquiv.apply_symm_apply] at h1
    rw [← h1, ← hφψ, ← he', MulEquiv.apply_symm_apply]
    rfl
  have hM : (r₁ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix (Fin n) (Fin n) ↥LL.1) =
      (r' (e.symm g) : Matrix (Fin n) (Fin n) ↥E'.1).map (algebraMap ↥E'.1 ↥LL.1) := by
    ext a b
    rw [hr₁]
    refine Eq.trans ?_ (hr' (e.symm g) a b).symm
    rw [← hg]
    rfl
  rw [← hM]
  rfl
