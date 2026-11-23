import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PiPtsHecke

open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Hi

private theorem isoPick_mod {R M : Type} {I : Type 1} [Ring R] [AddCommGroup M] [Module R M]
    (S : I → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, IsSimpleModule R (S i)]
    (y : M) (hy : y ≠ 0) (hmem : y ∈ ⨆ i, isotypicComponent R M (S i)) :
    ∃ i₀, y ∉ ⨆ i : {i // IsEmpty (S i₀ ≃ₗ[R] S i)}, isotypicComponent R M (S i.1) := by
  classical
  have hA : ∀ i, isotypicComponent R M (S i) = ⊥ ∨ isotypicComponent R M (S i) ∈ isotypicComponents R M := by
    intro i
    by_cases h : isotypicComponent R M (S i) = ⊥
    · exact Or.inl h
    · right
      obtain ⟨m, ⟨e⟩⟩ : ∃ m : Submodule R M, Nonempty (m ≃ₗ[R] S i) := by
        by_contra hcon
        push Not at hcon
        exact h (sSup_eq_bot.2 fun m ⟨e⟩ => ((hcon m).false e).elim)
      haveI : IsSimpleModule R m := IsSimpleModule.congr e
      exact ⟨m, ‹_›, (LinearEquiv.isotypicComponent_eq e).symm⟩
  let T : Set (Submodule R M) := isotypicComponents R M ∩ Set.range fun i => isotypicComponent R M (S i)
  have hind : iSupIndep (Subtype.val : T → Submodule R M) :=
    (sSupIndep_iff _).1 ((sSupIndep_isotypicComponents R M).mono Set.inter_subset_left)
  have hT : y ∈ ⨆ c : T, (c : Submodule R M) := by
    refine (show (⨆ i, isotypicComponent R M (S i)) ≤ _ from iSup_le fun i => ?_) hmem
    rcases hA i with h | h
    · rw [h]; exact bot_le
    · exact le_iSup (fun c : T => (c : Submodule R M)) ⟨_, h, i, rfl⟩
  obtain ⟨f, hf, hs⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hT
  obtain ⟨c, hc⟩ : f.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    exact hy (by simpa using hs.symm)
  obtain ⟨⟨m, hm, hcm⟩, i₀, hi₀⟩ := c.2
  refine ⟨i₀, fun hyC => ?_⟩
  have hCD : (⨆ i : {i // IsEmpty (S i₀ ≃ₗ[R] S i)}, isotypicComponent R M (S i.1)) ≤
      ⨆ (j : T) (_ : j ≠ c), (j : Submodule R M) := iSup_le fun ⟨i, hi⟩ => by
    rcases hA i with h | h
    · change isotypicComponent R M (S i) ≤ _
      rw [h]; exact bot_le
    · refine le_iSup₂_of_le (f := fun (j : T) (_ : j ≠ c) => (j : Submodule R M)) ⟨_, h, i, rfl⟩ (fun e => ?_) le_rfl
      have he : isotypicComponent R M (S i) = c.1 := congrArg Subtype.val e
      have hle : m ≤ c.1 := hcm ▸ m.le_isotypicComponent
      obtain ⟨e₁⟩ := isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M (S i₀)) m (hle.trans hi₀.ge)
      obtain ⟨e₂⟩ := isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M (S i)) m (hle.trans he.ge)
      exact hi.false (e₁.symm.trans e₂)
  rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hc] at hs
  have h2 : ∑ j ∈ f.support.erase c, f j ∈ ⨆ (j : T) (_ : j ≠ c), (j : Submodule R M) :=
    Submodule.sum_mem _ fun j hj =>
      (le_iSup₂_of_le (f := fun (j : T) (_ : j ≠ c) => (j : Submodule R M)) j (Finset.ne_of_mem_erase hj) le_rfl) (hf j)
  have h3 : f c ∈ ⨆ (j : T) (_ : j ≠ c), (j : Submodule R M) := by
    rw [eq_sub_of_add_eq hs]
    exact sub_mem (hCD hyC) h2
  exact Finsupp.mem_support_iff.1 hc (Submodule.disjoint_def.1 (hind c) _ (hf c) h3)

private theorem isoPick_range {H S Y : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ H S) (π : Representation ℂ H Y) (hσ : σ.IsIrreducible)
    (f : S →ₗ[ℂ] Y) (hf : ∀ g v, f (σ g v) = π g (f v)) (s : S) :
    π.asModuleEquiv.symm (f s) ∈ isotypicComponent (MonoidAlgebra ℂ H) π.asModule σ.asModule := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  let F : σ.asModule →ₗ[MonoidAlgebra ℂ H] π.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule σ π ⟨f, fun g => LinearMap.ext (hf g)⟩
  have : LinearMap.range F ≤ isotypicComponent (MonoidAlgebra ℂ H) π.asModule σ.asModule := by
    rcases LinearMap.injective_or_eq_zero F with hi | hz
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [hz, LinearMap.range_zero]; exact bot_le
  exact this ⟨σ.asModuleEquiv.symm s, rfl⟩

private theorem isoPick_sup {H Y : Type} {J : Sort*} [Group H] [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ H Y)
    (P : Submodule (MonoidAlgebra ℂ H) π.asModule) (A : J → Submodule ℂ Y)
    (h : ∀ j, ∀ v ∈ A j, π.asModuleEquiv.symm v ∈ P) (v : Y) (hv : v ∈ ⨆ j, A j) :
    π.asModuleEquiv.symm v ∈ P := by
  refine Submodule.iSup_induction _ (motive := fun z => π.asModuleEquiv.symm z ∈ P) hv h ?_ ?_
  · rw [map_zero]; exact zero_mem _
  · intro a b ha hb
    rw [map_add]; exact add_mem ha hb

private theorem isoPick_equiv {H S S' : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S']
    (σ : Representation ℂ H S) (σ' : Representation ℂ H S')
    (e : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ'.asModule) : Nonempty (σ.Equiv σ') := by
  let F := (Representation.IntertwiningMap.equivLinearMapAsModule σ σ').symm e.toLinearMap
  let F' := (Representation.IntertwiningMap.equivLinearMapAsModule σ' σ).symm e.symm.toLinearMap
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear F.toLinearMap F'.toLinearMap ?_ ?_) fun g => ?_⟩
  · ext v
    exact e.apply_symm_apply (σ'.asModuleEquiv.symm v)
  · ext v
    exact e.symm_apply_apply (σ.asModuleEquiv.symm v)
  · exact LinearMap.ext fun v => F.isIntertwining _ _ g v

private theorem isoPick_hr {H S Y : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ H S) (π : Representation ℂ H Y) (hσ : σ.IsIrreducible)
    (P : Submodule (MonoidAlgebra ℂ H) π.asModule)
    (hP : isotypicComponent (MonoidAlgebra ℂ H) π.asModule σ.asModule ≤ P) (v : Y)
    (hv : v ∈ ⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1) :
    π.asModuleEquiv.symm v ∈ P := by
  refine isoPick_sup π P _ (fun f w hw => ?_) v hv
  obtain ⟨s, rfl⟩ := hw
  exact hP (isoPick_range σ π hσ f.1 f.2 s)

private theorem mem_iSup_isotypicComponent_of_span {H Y : Type} {I : Type 1} [Group H] [AddCommGroup Y] [Module ℂ Y] (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ H (V i)) (hρ : ∀ i, (ρ i).IsIrreducible)
    (π : Representation ℂ H Y)
    (hspan : ∀ y, y ∈ ⨆ (i : I) (f : {f : V i →ₗ[ℂ] Y // ∀ g v, f (ρ i g v) = π g (f v)}), LinearMap.range f.1)
    (y : Y) : π.asModuleEquiv.symm y ∈ ⨆ i, isotypicComponent (MonoidAlgebra ℂ H) π.asModule (ρ i).asModule :=
  isoPick_sup π _ _ (fun i v hv => isoPick_hr (ρ i) π (hρ i) _
    (le_iSup (fun i => isotypicComponent (MonoidAlgebra ℂ H) π.asModule (ρ i).asModule) i) v hv) y (hspan y)

private theorem mem_iSup_isotypic_of_not_iso {H Y : Type} {I : Type 1} [Group H] [AddCommGroup Y] [Module ℂ Y] (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ H (V i)) (hρ : ∀ i, (ρ i).IsIrreducible)
    (π : Representation ℂ H Y) (i₀ : I) (y : Y)
    (hy : y ∈ ⨆ (i : {i : I // IsEmpty ((ρ i₀).Equiv (ρ i))}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ g v, f (ρ i.1 g v) = π g (f v)}), LinearMap.range f.1) :
    π.asModuleEquiv.symm y ∈ ⨆ i : {i // IsEmpty ((ρ i₀).asModule ≃ₗ[MonoidAlgebra ℂ H] (ρ i).asModule)},
      isotypicComponent (MonoidAlgebra ℂ H) π.asModule (ρ i.1).asModule := by
  refine isoPick_sup π _ _ (fun i v hv => isoPick_hr (ρ i.1) π (hρ i.1) _ ?_ v hv) y hy
  refine le_iSup (fun i : {i // IsEmpty ((ρ i₀).asModule ≃ₗ[MonoidAlgebra ℂ H] (ρ i).asModule)} =>
    isotypicComponent (MonoidAlgebra ℂ H) π.asModule (ρ i.1).asModule) ⟨i.1, ⟨fun e => ?_⟩⟩
  obtain ⟨e'⟩ := isoPick_equiv _ _ e
  exact i.2.false e'

private theorem isoPick_gen {H Y : Type} {I : Type 1} [Group H] [AddCommGroup Y] [Module ℂ Y] (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ H (V i)) (hρ : ∀ i, (ρ i).IsIrreducible)
    (π : Representation ℂ H Y)
    (hspan : ∀ y, y ∈ ⨆ (i : I) (f : {f : V i →ₗ[ℂ] Y // ∀ g v, f (ρ i g v) = π g (f v)}), LinearMap.range f.1)
    (y : Y) (hy : y ≠ 0) :
    ∃ i₀ : I, y ∉ ⨆ (i : {i : I // IsEmpty ((ρ i₀).Equiv (ρ i))}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ g v, f (ρ i.1 g v) = π g (f v)}), LinearMap.range f.1 := by
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ H) (ρ i).asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (hρ i)
  have hne : π.asModuleEquiv.symm y ≠ 0 := fun h => hy (by simpa using congrArg π.asModuleEquiv h)
  obtain ⟨i₀, h⟩ := isoPick_mod (fun i => (ρ i).asModule) (π.asModuleEquiv.symm y) hne (mem_iSup_isotypicComponent_of_span V ρ hρ π hspan y)
  exact ⟨i₀, fun hy' => h (mem_iSup_isotypic_of_not_iso V ρ hρ π i₀ y hy')⟩

theorem UpperTheory.GalN.V.isoPick :
    ∀ (H Y : Type) (I : Type 1) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup Y] [Module ℂ Y] (σ : I → SmIrr H) (π : Representation ℂ H Y), (∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) → ∀ y : Y, y ≠ 0 → ∃ i₀ : I, y ∉ ⨆ (i : {i : I // IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)}) (f : {f : (σ i.1).V →ₗ[ℂ] Y // ∀ g v, f ((σ i.1).ρ g v) = π g (f v)}), LinearMap.range f.1 := by
  intro H Y I _ _ _ _ _ σ π hspan y hy
  exact isoPick_gen (fun i => (σ i).V) (fun i => (σ i).ρ) (fun i => (σ i).irred) π hspan y hy
