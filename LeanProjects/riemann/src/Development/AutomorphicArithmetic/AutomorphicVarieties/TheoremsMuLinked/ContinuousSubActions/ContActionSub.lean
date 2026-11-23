import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Topology UpperTheory.V UpperTheory.V.Loc

namespace UpperTheory.V.Th.BkSub

private def extRep {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) :
    Representation A G (V × A) where
  toFun g := ((ρ g).comp (LinearMap.fst A V A) + (LinearMap.snd A V A).smulRight (c g)).prod (LinearMap.snd A V A)
  map_one' := by
    have h1 : c 1 = 0 := by simpa using hc 1 1
    refine LinearMap.ext fun x => ?_
    simp [h1]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [hc, add_assoc, add_comm, add_left_comm]

private theorem extRep_apply {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) (x : V × A) :
    extRep ρ c hc g x = (ρ g x.1 + x.2 • c g, x.2) := rfl

private theorem contAction_sub {G A V : Type} [Group G] [TopologicalSpace G] [CommRing A] [AddCommGroup V]
    [Module A V] [TopologicalSpace V] (ρ : Representation A G V) (h : ReciprocityTheory.Gal.ContAction ρ) (H : Subgroup G) :
    ReciprocityTheory.Gal.ContAction (ρ.comp H.subtype : Representation A H V) :=
  h.comp (f := fun p : H × V => ((p.1 : G), p.2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

section

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type} [Field A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A]
    [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] [IsTopologicalRing A]
    {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul A V]

private theorem cont_ext (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    {A : Type} [Field A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A]
    [TopologicalSpace A] [IsModuleTopology ℚ_[l] A]
    {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    (ρ : Representation A G V) (hρ : ReciprocityTheory.Gal.ContAction ρ) (c : G → V)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (cc : Continuous c) :
    ReciprocityTheory.Gal.ContAction (extRep ρ c hc) := by
  have hs : Continuous fun p : A × V => p.1 • p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left
      (Algebra.lsmul ℚ_[l] ℚ_[l] V : A →ₐ[ℚ_[l]] Module.End ℚ_[l] V).toLinearMap
  unfold ReciprocityTheory.Gal.ContAction
  simp only [extRep_apply]
  refine Continuous.prodMk (Continuous.add ?_ ?_) (continuous_snd.comp continuous_snd)
  · exact Continuous.comp (f := fun p : G × (V × A) => (p.1, p.2.1)) hρ (by fun_prop)
  · exact hs.comp ((continuous_snd.comp continuous_snd).prodMk (cc.comp continuous_fst))

private theorem ext_iff (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (ρ : Representation A G V)
    (hρ : ReciprocityTheory.Gal.ContAction ρ) (c : G → V) (hc : c ∈ Z1 ρ) (H : Subgroup G) [H.Normal]
    (hH : IsOpen (H : Set G)) (h : CrOn φ ρ H) :
    CrOn φ (extRep ρ c hc.2) H ↔ c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := by
  have hψ : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have cr1 : CrOn φ (chRep (1 : G →* Aˣ)) H :=
    crUnr (A := ℚ_[l]) (φ.comp H.subtype) hψ
      (resCoef ℚ_[l] ((chRep (1 : G →* Aˣ)).comp H.subtype : Representation A H A))
      (by
        unfold ReciprocityTheory.Gal.ContAction
        simpa [resCoef, chRep] using continuous_snd) 0
      (fun g _ x => by simp [resCoef, chRep])
  have htw : twist (1 : G →* Aˣ)⁻¹ ρ = ρ := by
    refine MonoidHom.ext fun g => ?_
    simp [twist]
  have := crExt φ hφ ρ (extRep ρ c hc.2) hρ (cont_ext l ρ hρ c hc.2 hc.1) 1 (LinearMap.inl A _ A)
    (LinearMap.snd A _ A) (0, 1) c LinearMap.inl_injective (Function.Exact.inl_snd) rfl
    (fun g x => by simp [extRep_apply]) (fun g => by simp [extRep_apply]) H hH h cr1
  rwa [htw] at this

end

end UpperTheory.V.Th.BkSub

open UpperTheory.V.Th.BkSub in
theorem UpperTheory.V.Th.z1fSub :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [Field A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] [IsTopologicalRing A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] (ρ : Representation A G V) (ρ' : Representation A G V'), ContAction ρ → ContAction ρ' → ∀ f : V →ₗ[A] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → Function.Injective f → ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → CrOn φ ρ' H → ∀ c ∈ Z1 ρ, (fun g => f (c g)) ∈ UpperTheory.V.Loc.finiteCocycles φ ρ' → c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' hρ hρ' f hf hi H _ hH h' c hc hz
  have hψ : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have hc' : (fun g => f (c g)) ∈ Z1 ρ' :=
    ⟨(IsModuleTopology.continuous_of_linearMap (f.restrictScalars ℚ_[l])).comp hc.1,
      fun g h => by simp only [hc.2 g h, map_add, hf]⟩
  have h : CrOn φ ρ H :=
    ((isCrys_isDR_sub_quot (φ.comp H.subtype) hψ _ _ (contAction_sub _ hρ H) (contAction_sub _ hρ' H)
      (f.restrictScalars ℚ_[l]) (fun g x => hf g x)).1 hi).1 h'
  refine (ext_iff φ hφ ρ hρ c hc H hH h).1 ?_
  have hE := (ext_iff φ hφ ρ' hρ' _ hc' H hH h').2 hz
  refine ((isCrys_isDR_sub_quot (φ.comp H.subtype) hψ _ _ (contAction_sub _ (cont_ext l ρ hρ c hc.2 hc.1) H)
    (contAction_sub _ (cont_ext l ρ' hρ' _ hc'.2 hc'.1) H)
    ((f.restrictScalars ℚ_[l]).prodMap LinearMap.id) (fun g x => ?_)).1 ?_).1 hE
  · change (f (ρ g x.1 + x.2 • c g), x.2) = (ρ' g (f x.1) + x.2 • f (c g), x.2)
    rw [map_add, map_smul, hf]
  · exact hi.prodMap Function.injective_id
