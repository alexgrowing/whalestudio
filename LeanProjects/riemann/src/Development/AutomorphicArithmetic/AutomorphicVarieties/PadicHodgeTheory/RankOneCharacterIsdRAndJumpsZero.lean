import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemIK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHost
import Formalism.AdmissibleDesigns.InvariantsEqBotIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem exists_ext {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ)
    (hκ : IsOpen {σ : ↥(Ine (F := F) A) | κ (Subgroup.inclusion (Ine_le_Dec A) σ) = 1})
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) :
    ∃ (K : FinExt l) (h : Bw.Kw.1 ≤ K.1), ∀ g ∈ IK K, κ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) = 1 := by
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hκ
  have h1 : (1 : G F Ω) ∈ U := by
    have : (1 : ↥(Ine (F := F) A)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      exact map_one (κ.comp (Subgroup.inclusion (Ine_le_Dec A)))
    exact this
  have hU1 : IsOpen {g : ↥(GK Bw.Kw) | ((Bw.e.symm g : ↥(Dec (F := F) A)) : G F Ω) ∈ U} :=
    hU.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U', hU', hUe'⟩ := isOpen_induced_iff.1 hU1
  have h1' : (1 : GQ l) ∈ U' := by
    have : (1 : ↥(GK Bw.Kw)) ∈ Subtype.val ⁻¹' U' := by
      rw [hUe']
      change ((Bw.e.symm 1 : ↥(Dec (F := F) A)) : G F Ω) ∈ U
      rw [map_one]
      exact h1
    exact this
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) U').1 (hU'.mem_nhds h1')
  refine ⟨GlobalTheory.Pst.supExt Bw.Kw ⟨E, hE⟩, le_sup_left, fun g hg => ?_⟩
  set g' : ↥(GK Bw.Kw) := Subgroup.inclusion (GK_le (K' := GlobalTheory.Pst.supExt Bw.Kw ⟨E, hE⟩) le_sup_left) g with hg'
  have hgU : g' ∈ Subtype.val ⁻¹' U' :=
    hEU (GK_le (K := ⟨E, hE⟩) (K' := GlobalTheory.Pst.supExt Bw.Kw ⟨E, hE⟩) le_sup_right g.2)
  rw [hUe'] at hgU
  have hI : ((Bw.e.symm g' : ↥(Dec (F := F) A)) : G F Ω) ∈ Ine (F := F) A := by
    refine ⟨(Bw.e.symm g').2, fun x hx => ?_⟩
    rw [hj.valuation_lt_one_iff, map_sub, ← Bw.e_comm, MulEquiv.apply_symm_apply]
    exact GlobalTheory.FrobGen.norm_sub_lt ((UpperTheory.V.Loc.memIK _ g).1 hg) _
      ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
  have h2 : (⟨_, hI⟩ : ↥(Ine (F := F) A)) ∈ Subtype.val ⁻¹' U := hgU
  rw [hUe] at h2
  exact h2

theorem UpperTheory.rankOne_character_isdR_and_jumps_zero :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → IsOpen {σ : ↥(Ine (F := F) A) | κ (Subgroup.inclusion (Ine_le_Dec A) σ) = 1} → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.IsdRAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 κ) ∧ ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), GlobalTheory.Pst.IsInduced Bw τ τ' → GlobalTheory.Pst.IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 κ) τ {0} := by
  intro F Ω _ _ _ _ _ l _ A κ hc hκ O _ _ _ Bw hj
  obtain ⟨K, h, hK⟩ := exists_ext κ hκ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  haveI : CompactSpace ↥(GK Bw.Kw) := GlobalTheory.UnramifiedCrys.compactSpace_GK _
  haveI : CompactSpace ↥(Dec (F := F) A) := Bw.e.symm.surjective.compactSpace Bw.e_symm_cont
  haveI : T2Space ↥(Dec (F := F) A) := inferInstance
  have hv : ∀ g a b, ((GlobalTheory.TripleGal.rk1 κ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) a b = κ g := by
    intro g a b
    rw [Subsingleton.elim a b]
    exact Matrix.diagonal_apply_eq _ _
  have hc0 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 κ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) :=
    continuous_pi fun a => continuous_pi fun b => by
      simp only [hv]
      exact Units.continuous_val.comp hc
  haveI := K.2
  let N : FinExt l := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
  obtain ⟨LL, hL, hent⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l _ 1 _ hc0 (GlobalTheory.Pst.supExt Bw.LL N)
  obtain ⟨r, hr⟩ := GlobalTheory.CompactRepField.exists_hom_of_entries_mem _ LL.1 hent
  have l₁ : Bw.LL.1 ≤ LL.1 := le_trans le_sup_left hL
  have l₂ : N.1 ≤ LL.1 := le_trans le_sup_right hL
  have hM : GlobalTheory.Pst.IsModel Bw (GlobalTheory.TripleGal.rk1 κ) LL r := ⟨l₁, by
    ext g a b
    exact hr g a b⟩
  let μ : ↥(GK K) →* (↥LL.1)ˣ := (Matrix.GeneralLinearGroup.det.comp r).comp
    (Bw.e.symm.toMonoidHom.comp (Subgroup.inclusion (GK_le h)))
  have hμr : ∀ g, ((μ g : (↥LL.1)ˣ) : ↥LL.1) =
      (r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 := fun g =>
    Matrix.det_fin_one _
  have hμ : ∀ g, (((μ g : (↥LL.1)ˣ) : ↥LL.1) : Om l) = κ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) := fun g => by
    rw [hμr, ← hv _ 0 0]
    exact hr _ 0 0
  have hμc : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun g : ↥(GK K) => ((κ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : (Qbar l)ˣ) : Qbar l) :=
      Units.continuous_val.comp (hc.comp (Bw.e_symm_cont.comp (continuous_inclusion (GK_le h))))
    exact this.congr fun g => (hμ g).symm
  obtain ⟨hcr, hm⟩ := GlobalTheory.UnramifiedChar.isCrys_and_multV_eq l _ _ T K LL μ hμc fun g hg => by
    apply Units.ext
    apply Subtype.ext
    rw [hμ, hK g hg]
    rfl
  let e : ↥LL.1 ≃ₗ[↥LL.1] (Fin 1 → ↥LL.1) := (LinearEquiv.funUnique (Fin 1) ↥LL.1 ↥LL.1).symm
  have he : ∀ g x, e (Formalism.WeaklyAdmissibleFiltrations.charRep μ g x) =
      ((Bw.repE LL r).comp (Subgroup.inclusion (GK_le h)) : Representation ↥LL.1 ↥(GK K) _) g (e x) := by
    intro g x
    funext a
    change ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x =
      Matrix.mulVec (r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix (Fin 1) (Fin 1) ↥LL.1) (fun _ => x) a
    rw [hμr, Subsingleton.elim a 0]
    simp [Matrix.mulVec, dotProduct]
  have hcr' := Formalism.MainNotions.N.K.Norm.isCrys_congr _ e he hcr
  have hd : Formalism.MainNotions.N.IsDR ((UpperTheory.V.Loc.PP l).PD Bw.Kw) (Bw.repE LL r) :=
    (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l _ _ T _ K LL h _ _).2.2
      (GlobalTheory.Per.CrisDR.isDR_of_isCrys l _ _ T K LL _ _ hcr').1
  have hD : Bw.IsdRE (UpperTheory.V.Loc.PP l) LL r := by
    unfold Formalism.MainNotions.N.IsDR at hd
    rw [Module.finrank_fin_fun] at hd
    exact hd
  refine ⟨⟨_, _, hM, hD⟩, fun τ LL' τ' hτ => ?_⟩
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ_[l]) (L := ↥Bw.Kw.1)
    (M := Om l) (E := Om l) (LL'.1.val.comp τ')
  let τ₂ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 := (σ.comp K.1.val).codRestrict LL.1.toSubalgebra fun x =>
    l₂ (AlgHom.fieldRange_le_normalClosure (σ.comp K.1.val) ⟨x, rfl⟩)
  refine ⟨LL, r, hM, hD, τ₂.comp (IntermediateField.inclusion h), fun x => ?_, fun n => ?_⟩
  · rw [hτ x]
    exact (AlgHom.congr_fun hσ _).symm
  · rw [LocBridge.multE, ← GlobalTheory.JumpRestrict.multV_restrict l _ _ T _ K LL h _ _ hd,
      ← Formalism.MainNotions.N.K.Norm.multV_congr _ e he, hm, Multiset.count_singleton]
    split_ifs <;> rfl
