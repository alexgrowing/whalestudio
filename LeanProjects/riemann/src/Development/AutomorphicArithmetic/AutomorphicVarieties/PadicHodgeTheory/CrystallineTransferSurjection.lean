import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SnocZeroLastCoordinateLast
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeformCr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem crystalline_transfer_surjection {l : ℕ} [Fact l.Prime] {G G' A A' V V' : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [CommRing A']
    [Algebra ℚ_[l] A'] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V']
    (φ : G →* GQ l) (e : G' →* G) (he : Function.Surjective e) (ρ : Representation A G V)
    (ρ' : Representation A' G' V') (f : V ≃ₗ[ℚ_[l]] V') (hf : ∀ g x, f (ρ (e g) x) = ρ' g (f x)) :
    IsCr φ ρ ↔ IsCr (φ.comp e) ρ' := by
  have hr : (φ.comp e).range = φ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 he, ← MonoidHom.range_eq_map]
  let F : V ⊗[ℚ_[l]] Bcr l ≃ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bcr l := TensorProduct.congr f (LinearEquiv.refl _ _)
  have hF : ∀ g x, F (actC φ (resCoef ℚ_[l] ρ) (e g) x) = actC (φ.comp e) (resCoef ℚ_[l] ρ') g (F x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v b => simp [F, actC, resCoef, hf]
  have hD : (Dcr φ (resCoef ℚ_[l] ρ)).map F.toLinearMap = Dcr (φ.comp e) (resCoef ℚ_[l] ρ') := by
    ext x
    obtain ⟨x, rfl⟩ := F.surjective x
    rw [Submodule.mem_map_equiv, F.symm_apply_apply]
    simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      ← hF, F.injective.eq_iff]
    exact he.forall
  unfold IsCr
  rw [hr, ← hD, LinearEquiv.finrank_map_eq, f.finrank_eq]

private theorem crystalline_iff_on_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    (φ : G →* GQ l) (ρ : Representation A G V) : IsCr φ ρ ↔ CrOn φ ρ ⊤ :=
  crystalline_transfer_surjection φ (⊤ : Subgroup G).subtype (fun g => ⟨⟨g, trivial⟩, rfl⟩) ρ _ (LinearEquiv.refl _ _)
    fun _ _ => rfl

private theorem crystalline_conj_invariant {l : ℕ} [Fact l.Prime] {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}
    (φ : G →* GQ l) (r : G →* GL (Fin n) A) (h : GL (Fin n) A) :
    IsCr φ (colRep r) ↔ IsCr φ (colRep (conjGL h r)) := by
  have := crystalline_transfer_surjection φ (MonoidHom.id G) Function.surjective_id (colRep r) (colRep (conjGL h r))
    ((Matrix.toLinearEquiv' (h : Matrix (Fin n) (Fin n) A) h.invertible).restrictScalars ℚ_[l]) fun g x => by
      simp [colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]
  simpa using this

private theorem continuous_dual_number_qcont {l : ℕ} [Fact l.Prime] {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] (f : X → DualNumber E) (hf : Continuous f) : QCont l f := by
  have h1 : Continuous fun x => (f x).fst := TrivSqZeroExt.continuous_fst.comp hf
  have h2 : Continuous fun x => (f x).snd := TrivSqZeroExt.continuous_snd.comp hf
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  unfold QCont
  clear hf
  letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] (DualNumber E)
  rw [e]
  exact ((IsModuleTopology.continuous_of_linearMap _).comp h1).add
    ((IsModuleTopology.continuous_of_linearMap _).comp h2)

private theorem open_subgroup_finite_index {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (H : Subgroup G) (hH : IsOpen (H : Set G)) : H.FiniteIndex := by
  have hc : IsClosed (φ.range : Set (GQ l)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
  haveI : CompactSpace G := (IsClosedEmbedding.mk hφ.isEmbedding hc).compactSpace
  haveI := H.quotient_finite_of_isOpen hH
  exact Subgroup.finiteIndex_of_finite_quotient

theorem UpperTheory.V.Loc.pr6 :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] {Y : Type} [AddCommGroup Y] [Module E Y] [Module ℚ_[l] Y] [IsScalarTower ℚ_[l] E Y] [FiniteDimensional ℚ_[l] Y] [TopologicalSpace Y] [IsModuleTopology ℚ_[l] Y] [IsTopologicalAddGroup Y] [ContinuousConstSMul E Y] (ρ : Representation E G Y), ContAction ρ → ∀ y ∈ Z1 ρ, ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → ∀ {n : ℕ} (r : H →* GL (Fin n) E), Continuous (fun g => (r g : Matrix (Fin n) (Fin n) E)) → ∀ (ι : Y →ₗ[E] Matrix (Fin n) (Fin n) E) (p : Matrix (Fin n) (Fin n) E →ₗ[E] Y), (∀ x, p (ι x) = x) → (∀ (g : H) x, ι (ρ g x) = adGL r g (ι x)) → (∀ (g : H) X, p (adGL r g X) = ρ g (p X)) → ∀ r' : H →* GL (Fin n) (DualNumber E), (∀ (g : H) i j, (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j = ⟨(r g : Matrix (Fin n) (Fin n) E) i j, (ι (y g) * (r g : Matrix (Fin n) (Fin n) E)) i j⟩) → ∀ (h : GL (Fin n) (DualNumber E)) (κ : Fin n → H →* (DualNumber E)ˣ) (w : Fin n → ℤ), UpperTri (conjGL h r') κ → StrictAnti w → (∀ i (g : H), φ g ∈ Iq l → κ i g = cycA l l (DualNumber E) (φ g) ^ w i) → (∀ i j, i < j → ∃ g : H, (κ i g : DualNumber E).fst ≠ (κ j g : DualNumber E).fst * (cycA l l E (φ g) : E)) → IsCr (φ.comp H.subtype) (colRep r) ∧ IsCr (φ.comp H.subtype) (colRep r') ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := by
  intro P l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ Y _ _ _ _ _ _ _ _ _ ρ hρ y hy H _ hH n r hr ι p hp hι hpe r' hr' h κ w
    hU hw hκ hne
  haveI := open_subgroup_finite_index φ hφ H hH
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hyc : Continuous fun g : H => ι (y g) :=
    (IsModuleTopology.continuous_of_linearMap (ι.restrictScalars ℚ_[l])).comp (hy.1.comp continuous_subtype_val)
  have hy' : (fun g : H => ι (y g)) ∈ Z1 (adGL r) := ⟨hyc, fun g k => by
    simp only []
    rw [Subgroup.coe_mul, hy.2, map_add, hι]⟩
  have hr'c : Continuous fun g => (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) := by
    refine continuous_matrix fun i j => ?_
    simp only [hr']
    exact Continuous.prodMk (hr.matrix_elem i j) ((hyc.matrix_mul hr).matrix_elem i j)
  have hcc : ∀ i j, QCont l fun g => (conjGL h r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j := fun i j =>
    continuous_dual_number_qcont _ (((continuous_const.matrix_mul hr'c).matrix_mul continuous_const).matrix_elem i j)
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  have h1 : IsCr (φ.comp H.subtype) (colRep r') :=
    (crystalline_conj_invariant _ r' h).2 (prC P _ hφH (TrivSqZeroExt.fstHom E E E)
      (fun a ha => ⟨2, by ext <;> simp_all [pow_two]⟩) (conjGL h r') hcc κ w hU hw hκ hne)
  obtain ⟨h2, h3⟩ := (deformCr _ hφH r hr _ hy' r' hr' ⊤ (by simp)).1 ((crystalline_iff_on_top _ _).1 h1)
  refine ⟨(crystalline_iff_on_top _ _).2 h2, h1, (z1fDesc φ ρ H y hy).2 ?_⟩
  have := (z1fMap (φ.comp H.subtype) (adGL r) (ρ.comp H.subtype : Representation E H Y)).2
    (p.restrictScalars ℚ_[l]) hpe _ h3
  simpa [hp] using this
