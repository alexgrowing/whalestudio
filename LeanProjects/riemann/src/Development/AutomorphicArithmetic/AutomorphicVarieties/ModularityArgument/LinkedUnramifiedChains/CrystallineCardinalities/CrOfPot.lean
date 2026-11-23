import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PotCrysOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotMove

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Topology GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Loc

private theorem cr_pull {l : ℕ} [Fact l.Prime] {G G' A V : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A G' V}
    (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : IsCr φ' ρ' → IsCr φ ρ := by
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

private theorem isCr_of_crys {l : ℕ} [Fact l.Prime] (K E' : FinExt l) {n : ℕ}
    (ρ : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1)) (h : Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ) :
    IsCr (GK K).subtype ρ := by
  have := E'.2
  have : IsModuleTopology ℚ_[l] (Fin n → ↥E'.1) := isModuleTopologyOfFiniteDimensional
  exact (isCrIff K ρ).1.2 ((isCrField K ρ).1.2 h)

private theorem crys_res {l : ℕ} [Fact l.Prime] (K K' E' : FinExt l) (h : K.1 ≤ K'.1) {n : ℕ}
    (ρ : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1)) (hc : Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ) :
    Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K') (ρ.comp (incl h) : Representation ↥E'.1 ↥(GK K') (Fin n → ↥E'.1)) := by
  have := E'.2
  have : IsModuleTopology ℚ_[l] (Fin n → ↥E'.1) := isModuleTopologyOfFiniteDimensional
  obtain ⟨T⟩ := tiedP l
  exact (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K K' E' h _ ρ).1 hc

private theorem crys_up {l : ℕ} [Fact l.Prime] (K L₁ L₂ : FinExt l) (h : L₁.1 ≤ L₂.1) {n : ℕ}
    (ρ₁ : Representation ↥L₁.1 ↥(GK K) (Fin n → ↥L₁.1)) (ρ₂ : Representation ↥L₂.1 ↥(GK K) (Fin n → ↥L₂.1))
    (M₁ : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L₁.1) (M₂ : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L₂.1)
    (h₁ : ∀ g x, ρ₁ g x = (M₁ g).mulVec x) (h₂ : ∀ g x, ρ₂ g x = (M₂ g).mulVec x)
    (hM : ∀ g a b, ((M₂ g a b : ↥L₂.1) : Om l) = ((M₁ g a b : ↥L₁.1) : Om l)) :
    Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ₂ ↔ Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ₁ := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  refine GlobalTheory.Pst.isCrys_ext_iff _ fun g => ⟨M₁ g, h₁ g, fun x => ?_⟩
  have : M₂ g = (M₁ g).map (algebraMap ↥L₁.1 ↥L₂.1) := by
    ext a b
    exact hM g a b
  rw [← this, h₂]

private theorem crys_model {l : ℕ} [Fact l.Prime] (K L₁ L₂ : FinExt l) {n : ℕ}
    (ρ₁ : Representation ↥L₁.1 ↥(GK K) (Fin n → ↥L₁.1)) (r₂ : ↥(GK K) →* GL (Fin n) ↥L₂.1)
    (M₁ : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L₁.1)
    (h₁ : ∀ g x, ρ₁ g x = (M₁ g).mulVec x)
    (hM : ∀ g a b, (((r₂ g : Matrix (Fin n) (Fin n) ↥L₂.1) a b : ↥L₂.1) : Om l) = ((M₁ g a b : ↥L₁.1) : Om l))
    (hc : Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ₁) : Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) (colRep r₂) := by
  have l₁ : L₁.1 ≤ (GlobalTheory.Pst.supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (GlobalTheory.Pst.supExt L₁ L₂).1 := le_sup_right
  let r₃ : ↥(GK K) →* GL (Fin n) ↥(GlobalTheory.Pst.supExt L₁ L₂).1 :=
    Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom r₂
  refine (crys_up K L₂ _ l₂ (colRep r₂) (colRep r₃) (fun g => r₂ g) (fun g => r₃ g) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)).1 ?_
  exact (crys_up K L₁ _ l₁ ρ₁ (colRep r₃) M₁ (fun g => r₃ g) h₁ (fun _ _ => rfl) hM).2 hc

private theorem core_open {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    IsOpen (((GK K).normalCore : Subgroup (GQ l)) : Set (GQ l)) := by
  haveI := K.2
  have ho : IsOpen ((GK K : Subgroup (GQ l)) : Set (GQ l)) := K.1.fixingSubgroup_isOpen
  haveI : (GK K).FiniteIndex := by
    haveI : Finite (GQ l ⧸ GK K) := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
    (Subgroup.normalCore_isClosed _ K.1.fixingSubgroup_isClosed)

theorem UpperTheory.V.Z.J.crOfPot :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (A : ValuationSubring Ω) {n : ℕ} (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → UpperTheory.V.Af.PotCrysAt r A → ∃ j : Ω →+* Om l, placeJ j = A ∧ ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ (E' : FinExt l) (r' : H →* GL (Fin n) ↥E'.1), (∀ h a b, (((r' h : Matrix (Fin n) (Fin n) ↥E'.1) a b : ↥E'.1) : Om l) = (r (ψ h) : Matrix (Fin n) (Fin n) (Qbar l)) a b) → ∃ (U : Subgroup H) (_ : U.Normal), IsOpen (U : Set H) ∧ CrOn φ (colRep r') U := by
  intro F Ω _ _ _ _ _ _ l _ A n r _ hA
  obtain ⟨O, i1, i2, i3, Bw, hj, LL, r₁, ⟨-, hmap⟩, K', hK', hcr⟩ := hA
  refine ⟨Bw.j, ?_, ?_⟩
  · ext x
    refine Iff.trans ?_ (hj x).symm
    change Valued.v (Bw.j x) ≤ 1 ↔ _
    rw [PadicAlgCl.valuation_def]
    exact Iff.rfl
  intro H _ _ _ φ ψ hφ hφψ E' r' hr'
  let U : Subgroup H := (GK K').normalCore.comap φ
  have hU : IsOpen (U : Set H) := (core_open K').preimage hφ.continuous
  refine ⟨U, Subgroup.Normal.comap inferInstance φ, hU, ?_⟩
  have hφU : IsOpenEmbedding (φ.comp U.subtype) := hφ.comp hU.isOpenEmbedding_subtypeVal
  obtain ⟨K, e, -, -, he, hKr, -, -⟩ := openField (φ.comp U.subtype) hφU
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  have hle : GK K ≤ GK K' := by
    rw [← hKr]
    rintro _ ⟨g, rfl⟩
    exact (GK K').normalCore_le g.2
  have h : K'.1 ≤ K.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup K'.1]
    exact IntermediateField.fixedField_le hle
  have t1 := crys_res K' K LL h _ hcr
  let r₂ : ↥(GK K) →* GL (Fin n) ↥E'.1 := r'.comp (U.subtype.comp e.symm.toMonoidHom)
  have hg : ∀ g : ↥(GK K), ((Bw.e.symm (Subgroup.inclusion (GK_le hK') (incl h g)) : ↥(Dec (F := F) A)) : G F Ω) =
      ψ (e.symm g) := fun g => by
    apply AlgEquiv.ext
    intro y
    apply Bw.j.injective
    have h1 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le hK') (incl h g))) y
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1, ← hφψ, ← he', MulEquiv.apply_symm_apply]
    rfl
  have t2 := crys_model K LL E' _ r₂
    (fun g => r₁ (Bw.e.symm (Subgroup.inclusion (GK_le hK') (incl h g)))) (fun _ _ => rfl)
    (fun g a b => by
      refine (hr' (e.symm g) a b).trans ?_
      rw [← hg]
      exact (congrArg (fun s : GL (Fin n) (Om l) => (s : Matrix (Fin n) (Fin n) (Om l)) a b)
        (DFunLike.congr_fun hmap _)).symm) t1
  exact cr_pull e e.surjective he' (fun g x => by simp [r₂, colRep]) (isCr_of_crys K E' _ t2)
