import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.CrExt

private theorem isCr_comp {l : ℕ} [Fact l.Prime] {G G' A V : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    (φ : G' →* GQ l) (ρ : Representation A G' V) (e : G →* G') (he : Function.Surjective e) :
    IsCr (φ.comp e) (ρ.comp e : Representation A G V) ↔ IsCr φ ρ := by
  have h1 : Dcr (φ.comp e) (resCoef ℚ_[l] (ρ.comp e : Representation A G V)) = Dcr φ (resCoef ℚ_[l] ρ) :=
    he.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  have h2 : (φ.comp e).range = φ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 he, ← MonoidHom.range_eq_map]
  unfold IsCr
  rw [h1, h2]

private theorem line {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] [AddCommGroup W] [Module ℚ_[l] W]
    (ρ : Representation ℚ_[l] G V) (ρ' : Representation ℚ_[l] G W) (i : V →ₗ[ℚ_[l]] W) (p : W →ₗ[ℚ_[l]] ℚ_[l])
    (h : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt ρ ρ' i p) (c : G → V) (hc : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsCocycleOf ρ' i p c)
    (hV : IsCr φ ρ) :
    IsCr φ ρ' ↔ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC φ ρ g x - x := by
  obtain ⟨K, e, -, -, rfl, -⟩ := openField φ hφ
  let σ : Representation ℚ_[l] (GK K) V := ρ.comp e.symm.toMonoidHom
  let σ' : Representation ℚ_[l] (GK K) W := ρ'.comp e.symm.toMonoidHom
  have e1 : ρ = σ.comp e.toMonoidHom := by ext g x; simp [σ]
  have e2 : ρ' = σ'.comp e.toMonoidHom := by ext g x; simp [σ']
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt σ σ' i p :=
    ⟨h.1, h.2.1, h.2.2.1, fun g => h.2.2.2.1 _, fun g => h.2.2.2.2 _⟩
  have hcσ : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsCocycleOf σ' i p (fun g => c (e.symm g)) := by
    obtain ⟨x, hx, hx'⟩ := hc
    exact ⟨x, hx, fun g => hx' _⟩
  rw [e1, isCr_comp _ _ _ e.surjective, (isCrIff K σ).1] at hV
  have hV' : IsCrys ((PP l).PD K) σ := hV
  have key := (GlobalTheory.CrysExt.isCrys_iff_surjective ((PP l).PD K) hV' hσ).trans
    ((GlobalTheory.CrysExt.lift_iff_surjective ((PP l).PD K) hσ).symm.trans
      (GlobalTheory.CrysExt.coboundary_iff_lift ((PP l).PD K) hσ hcσ).symm)
  rw [e2, isCr_comp _ _ _ e.surjective, (isCrIff K σ').1]
  refine key.trans (exists_congr fun x => ?_)
  rw [e.surjective.forall]
  refine forall_congr' fun g => ?_
  have : actVB ((PP l).PD K) σ (e g) x = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
    rw [e1]
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change σ (e g) v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB (e g) b = σ (e g) v ⊗ₜ[ℚ_[l]] (PP l).actQ (e g : GQ l) b
      rw [(PP l).PD_actB]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [this, e.symm_apply_apply]

private theorem isCr_trivial {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (X : Type) [AddCommGroup X] [Module ℚ_[l] X]
    [FiniteDimensional ℚ_[l] X] [TopologicalSpace X] [IsModuleTopology ℚ_[l] X] [IsTopologicalAddGroup X] :
    IsCr φ (Representation.trivial ℚ_[l] G X) :=
  crUnr φ hφ (Representation.trivial ℚ_[l] G X) continuous_snd 0 (fun g _ x => by simp)

private def ext0 {Q G V : Type} [CommRing Q] [Group G] [AddCommGroup V] [Module Q V] (ρ : Representation Q G V)
    (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) : Representation Q G (V × Q) where
  toFun g := ((ρ g).coprod (LinearMap.toSpanSingleton Q V (c g))).prod (LinearMap.snd Q V Q)
  map_one' := by
    have : c 1 = 0 := by simpa using hc 1 1
    refine LinearMap.ext fun x => ?_
    simp [this]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [hc]
    abel

private theorem triv {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A]
    [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] [IsTopologicalRing A]
    {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul A V]
    {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V']
    [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V']
    [ContinuousConstSMul A V']
    (ρ : Representation A G V) (ρ' : Representation A G V') (hρ : ReciprocityTheory.Gal.ContAction ρ) (hρ' : ReciprocityTheory.Gal.ContAction ρ')
    (f : V →ₗ[A] V') (p : V' →ₗ[A] A) (s : V') (c : G → V) (hf : Function.Injective f)
    (hex : Function.Exact f p) (hs : p s = 1) (hfρ : ∀ g x, f (ρ g x) = ρ' g (f x))
    (hc : ∀ g, ρ' g s = s + f (c g)) (hZ : c ∈ Z1 ρ) (hV : IsCr φ ρ) :
    IsCr φ ρ' ↔ c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := by
  let σ := ext0 (resCoef ℚ_[l] ρ) c hZ.2
  have hσ : ∀ g x, σ g x = (ρ g x.1 + x.2 • c g, x.2) := fun _ _ => rfl
  have hcont : ReciprocityTheory.Gal.ContAction σ := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hσ]
    exact ((hρ.comp (continuous_fst.prodMk continuous_snd.fst)).add
      (continuous_snd.snd.smul (hZ.1.comp continuous_fst))).prodMk continuous_snd.snd
  have hext : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt (resCoef ℚ_[l] ρ) σ (LinearMap.inl ℚ_[l] V ℚ_[l])
      (LinearMap.snd ℚ_[l] V ℚ_[l]) :=
    ⟨LinearMap.inl_injective, Function.Exact.inl_snd, LinearMap.snd_surjective,
      fun g x => by rw [hσ]; simp [resCoef], fun g x => rfl⟩
  have hco : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsCocycleOf σ (LinearMap.inl ℚ_[l] V ℚ_[l]) (LinearMap.snd ℚ_[l] V ℚ_[l]) c :=
    ⟨(0, 1), rfl, fun g => by rw [hσ]; simp⟩
  have key : IsCr φ σ ↔ c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ :=
    (line φ hφ (resCoef ℚ_[l] ρ) σ _ _ hext c hco hV).trans ⟨fun h => ⟨hZ, h⟩, fun h => h.2⟩
  let j : V × ℚ_[l] →ₗ[ℚ_[l]] V' := (f.restrictScalars ℚ_[l]).coprod (LinearMap.toSpanSingleton ℚ_[l] V' s)
  have hj : ∀ x, j x = f x.1 + x.2 • s := fun _ => rfl
  have hjρ : ∀ g x, j (σ g x) = ρ' g (j x) := by
    intro g x
    simp only [hj, hσ, map_add, LinearMap.map_smul_of_tower, hc, hfρ, smul_add]
    abel
  constructor
  · intro h
    rcases subsingleton_or_nontrivial A with hA | hA
    · haveI := Module.subsingleton A V
      rw [Subsingleton.elim c 0]
      exact zero_mem _
    · refine key.1 (((isCrys_isDR_sub_quot φ hφ σ ρ' hcont hρ' j hjρ).1 ?_).1 h)
      rw [injective_iff_map_eq_zero]
      rintro ⟨v, t⟩ hx
      have h1 := congrArg p hx
      rw [hj, map_add, hex.apply_apply_eq_zero, LinearMap.map_smul_of_tower, hs, zero_add, map_zero,
        smul_eq_zero] at h1
      obtain rfl : t = 0 := h1.resolve_right one_ne_zero
      rw [hj, zero_smul, add_zero, map_eq_zero_iff f hf] at hx
      exact Prod.ext hx rfl
  · intro h
    let b : A →ₗ[ℚ_[l]] V × ℚ_[l] →ₗ[ℚ_[l]] V' :=
      (Algebra.lsmul ℚ_[l] ℚ_[l] V' : A →ₐ[ℚ_[l]] Module.End ℚ_[l] V').toLinearMap.compl₂ j
    have hb : ∀ a x, b a x = a • j x := fun _ _ => rfl
    refine (admissible_of_bilinear_openSubgroup_galois φ hφ (Representation.trivial ℚ_[l] G A) σ (resCoef ℚ_[l] ρ') continuous_snd hcont hρ' b
      (fun g a x => ?_) ?_).1 (isCr_trivial φ hφ A) (key.2 h)
    · rw [hb, hb, hjρ]
      exact (map_smul (ρ' g) a _).symm
    · rw [eq_top_iff]
      intro y _
      obtain ⟨v, hv⟩ := (hex (y - p y • s)).1 (by simp [hs])
      have : y = b 1 (v, 0) + b (p y) (0, 1) := by simp [hb, hj, hv]
      rw [this]
      exact add_mem (Submodule.subset_span ⟨(1, (v, 0)), rfl⟩) (Submodule.subset_span ⟨(p y, (0, 1)), rfl⟩)

private theorem cont_smul (l : ℕ) [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A]
    [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] A V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] : Continuous fun p : A × V => p.1 • p.2 :=
  IsModuleTopology.continuous_bilinear_of_finite_left
    (Algebra.lsmul ℚ_[l] ℚ_[l] V : A →ₐ[ℚ_[l]] Module.End ℚ_[l] V).toLinearMap

private theorem cont_twist (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A]
    [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] A V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (κ : G →* Aˣ) (hκ : Continuous fun g => (κ g : A)) (ρ : Representation A G V)
    (hρ : ReciprocityTheory.Gal.ContAction ρ) : ReciprocityTheory.Gal.ContAction (twist κ ρ) :=
  (cont_smul l (A := A) (V := V)).comp ((hκ.comp continuous_fst).prodMk hρ)

section Twist

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A]
    [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] [IsTopologicalRing A]
    {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul A V]

omit [IsTopologicalGroup G] in
private theorem cont_chRep (κ : G →* Aˣ) (hκ : Continuous fun g => (κ g : A)) :
    ReciprocityTheory.Gal.ContAction (chRep κ) :=
  (hκ.comp continuous_fst).mul continuous_snd

omit [IsTopologicalRing A] in
private theorem cont_inv (κ : G →* Aˣ) (hκ : Continuous fun g => (κ g : A)) :
    Continuous fun g => ((κ⁻¹ g : Aˣ) : A) := by
  simpa only [MonoidHom.inv_apply, ← map_inv] using hκ.comp' continuous_inv

private theorem isCr_twist (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (κ : G →* Aˣ)
    (hκ : Continuous fun g => (κ g : A)) (ρ : Representation A G V) (hρ : ReciprocityTheory.Gal.ContAction ρ)
    (h1 : IsCr φ (chRep κ)) (h2 : IsCr φ ρ) : IsCr φ (twist κ ρ) := by
  refine (admissible_of_bilinear_openSubgroup_galois φ hφ (chRep κ) ρ (twist κ ρ) (cont_chRep κ hκ) hρ (cont_twist l κ hκ ρ hρ)
    (Algebra.lsmul ℚ_[l] ℚ_[l] V : A →ₐ[ℚ_[l]] Module.End ℚ_[l] V).toLinearMap (fun g a x => ?_) ?_).1 h1 h2
  · change ((κ g : A) * a) • ρ g x = (κ g : A) • ρ g (a • x)
    rw [map_smul, mul_smul]
  · rw [eq_top_iff]
    exact fun y _ => Submodule.subset_span ⟨(1, y), one_smul A y⟩

private theorem isCr_inv (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (κ : G →* Aˣ)
    (hκ : Continuous fun g => (κ g : A)) (h1 : IsCr φ (chRep κ)) : IsCr φ (chRep κ⁻¹) := by
  refine (isCrys_isDR_internalHom φ hφ (chRep κ) (Representation.trivial A G A) (chRep κ⁻¹) (cont_chRep κ hκ) continuous_snd
    (cont_chRep _ (cont_inv κ hκ)) (LinearMap.mul ℚ_[l] A) (fun g a x => ?_) ?_).1 h1 (isCr_trivial φ hφ A)
  · change (((κ g)⁻¹ : Aˣ) : A) * a * ((κ g : A) * x) = a * x
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  · intro a b h
    simpa using LinearMap.congr_fun h 1

end Twist

end UpperTheory.V.Loc.CrExt

open UpperTheory.V.Loc.CrExt in
theorem UpperTheory.V.Loc.crExt :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] [IsTopologicalRing A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] (ρ : Representation A G V) (ρ' : Representation A G V'), ContAction ρ → ContAction ρ' → ∀ (κ : G →* Aˣ) (f : V →ₗ[A] V') (p : V' →ₗ[A] A) (s : V') (c : G → V), Function.Injective f → Function.Exact f p → p s = 1 → (∀ g x, f (ρ g x) = ρ' g (f x)) → (∀ g, ρ' g s = (κ g : A) • (s + f (c g))) → ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → CrOn φ ρ H → CrOn φ (chRep κ) H → (CrOn φ ρ' H ↔ c ∈ UpperTheory.V.Loc.finiteCocycles φ (twist κ⁻¹ ρ)) := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' hρ hρ' κ f p s c hf hex hs hfρ
    hc H _ hH hV hκcr
  have hp : Continuous p := IsModuleTopology.continuous_of_linearMap (p.restrictScalars ℚ_[l])
  have hκ : Continuous fun g => (κ g : A) := by
    have : (fun g => (κ g : A)) = fun g => p (ρ' g s) := by
      funext g
      rw [hc, map_smul, map_add, hex.apply_apply_eq_zero, hs, add_zero, smul_eq_mul, mul_one]
    rw [this]
    exact hp.comp (hρ'.comp (continuous_id.prodMk continuous_const))
  have hκ' := cont_inv κ hκ
  have hτ := cont_twist l κ⁻¹ hκ' ρ hρ
  have hτ' := cont_twist l κ⁻¹ hκ' ρ' hρ'
  have hfτ : ∀ g x, f (twist κ⁻¹ ρ g x) = twist κ⁻¹ ρ' g (f x) := by
    intro g x
    change f (((κ⁻¹ g : Aˣ) : A) • ρ g x) = ((κ⁻¹ g : Aˣ) : A) • ρ' g (f x)
    rw [map_smul, hfρ]
  have hcτ : ∀ g, twist κ⁻¹ ρ' g s = s + f (c g) := by
    intro g
    change (((κ g)⁻¹ : Aˣ) : A) • ρ' g s = _
    rw [hc, smul_smul, Units.inv_mul, one_smul]
  have hZ : c ∈ Z1 (twist κ⁻¹ ρ) := by
    refine ⟨?_, fun g h => hf ?_⟩
    · obtain ⟨r, hr⟩ := (f.restrictScalars ℚ_[l]).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
      have : c = fun g => r (twist κ⁻¹ ρ' g s - s) := by
        funext g
        rw [hcτ, add_sub_cancel_left]
        exact (LinearMap.congr_fun hr (c g)).symm
      rw [this]
      exact (IsModuleTopology.continuous_of_linearMap r).comp
        ((hτ'.comp (continuous_id.prodMk continuous_const)).sub continuous_const)
    · have h1 := hcτ (g * h)
      rw [map_mul, Module.End.mul_apply, hcτ, map_add, hcτ, ← hfτ, add_assoc, add_right_inj] at h1
      rw [map_add, h1]
  haveI : H.FiniteIndex := by
    obtain ⟨K, e, -, he, -⟩ := openField φ hφ
    haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
    haveI : CompactSpace G := e.symm.surjective.compactSpace he
    haveI := H.quotient_finite_of_isOpen hH
    exact H.finiteIndex_of_finite_quotient
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have res : ∀ {X : Type} [AddCommGroup X] [Module A X] [TopologicalSpace X] (π : Representation A G X),
      ReciprocityTheory.Gal.ContAction π → ReciprocityTheory.Gal.ContAction (π.comp H.subtype : Representation A H X) :=
    fun π hπ => hπ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hκH : Continuous fun g : H => ((κ.comp H.subtype) g : A) := hκ.comp continuous_subtype_val
  have hκH' := cont_inv _ hκH
  have hκcr' : IsCr (φ.comp H.subtype) (chRep (κ.comp H.subtype)) := hκcr
  have hinv := isCr_inv _ hφH (κ.comp H.subtype) hκH hκcr'
  have tw : ∀ {X : Type} [AddCommGroup X] [Module A X] (π : Representation A G X),
      ((twist κ⁻¹ π).comp H.subtype : Representation A H X) =
        twist (κ.comp H.subtype)⁻¹ (π.comp H.subtype : Representation A H X) := fun π => by
    ext g x
    rfl
  have hVH : IsCr (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V) := hV
  have h1 : IsCr (φ.comp H.subtype) ((twist κ⁻¹ ρ).comp H.subtype : Representation A H V) := by
    rw [tw]
    exact isCr_twist _ hφH _ hκH' _ (res ρ hρ) hinv hVH
  have h2 : IsCr (φ.comp H.subtype) (ρ'.comp H.subtype : Representation A H V') ↔
      IsCr (φ.comp H.subtype) ((twist κ⁻¹ ρ').comp H.subtype : Representation A H V') := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [tw]
      exact isCr_twist _ hφH _ hκH' _ (res ρ' hρ') hinv h
    have h3 := isCr_twist _ hφH _ hκH _ (res _ hτ') hκcr' h
    have h4 : twist (κ.comp H.subtype) ((twist κ⁻¹ ρ').comp H.subtype : Representation A H V') =
        ρ'.comp H.subtype := by
      ext g x
      change (κ g : A) • (((κ g)⁻¹ : Aˣ) : A) • ρ' g x = ρ' g x
      rw [smul_smul, Units.mul_inv, one_smul]
    rwa [h4] at h3
  rw [CrOn, h2, z1fDesc φ (twist κ⁻¹ ρ) H c hZ]
  exact triv _ hφH _ _ (res _ hτ) (res _ hτ') f p s (fun h : H => c h) hf hex hs (fun g => hfτ g) (fun g => hcτ g)
    ⟨hZ.1.comp continuous_subtype_val, fun g h => hZ.2 g h⟩ h1
