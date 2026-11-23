import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact

noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.JHMatch

section Mod
variable {R : Type} [Ring R]

def HasFactors (M : Type) [AddCommGroup M] [Module R M] {ι : Type} (F : ι → ModuleCat.{0} R) : Prop :=
  ∃ r : CompositionSeries (Submodule R M), r.head = ⊥ ∧ r.last = ⊤ ∧
    ∃ e : ι ≃ Fin r.length, ∀ i, Nonempty (F i ≃ₗ[R] factor r (e i))

variable {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {ι κ : Type}

theorem HasFactors.finiteLength {F : ι → ModuleCat.{0} R} (h : HasFactors M F) : IsFiniteLength R M := by
  obtain ⟨r, h1, h2, -⟩ := h
  exact isFiniteLength_of_exists_compositionSeries ⟨r, h1, h2⟩

theorem HasFactors.of_same {F : ι → ModuleCat.{0} R} (h : HasFactors M F) (h' : SameFactors R M N) :
    HasFactors N F := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  obtain ⟨s, t, h3, h4, h5, h6, e', he'⟩ := h'
  obtain ⟨c, hc⟩ := CompositionSeries.jordan_holder r s (h1.trans h3.symm) (h2.trans h4.symm)
  refine ⟨t, h5, h6, (e.trans c).trans e', fun i => ?_⟩
  obtain ⟨f⟩ := he i
  obtain ⟨g⟩ := he' (c (e i))
  exact ⟨(f.trans (JordanHolderLattice.Iso.linearEquiv (hc (e i)))).trans g⟩

theorem HasFactors.of_equiv {F : ι → ModuleCat.{0} R} (h : HasFactors M F) (e : M ≃ₗ[R] N) :
    HasFactors N F := h.of_same (SameFactors.of_equiv h.finiteLength e)

theorem HasFactors.unique {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (h' : HasFactors M F') : ∃ e : ι ≃ κ, ∀ i, Nonempty (F i ≃ₗ[R] F' (e i)) := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  obtain ⟨s, h3, h4, e', he'⟩ := h'
  obtain ⟨c, hc⟩ := CompositionSeries.jordan_holder r s (h1.trans h3.symm) (h2.trans h4.symm)
  refine ⟨(e.trans c).trans e'.symm, fun i => ?_⟩
  obtain ⟨j, hj⟩ := e'.surjective (c (e i))
  have hj' : ((e.trans c).trans e'.symm) i = j := by
    simp [← hj]
  rw [hj']
  obtain ⟨f⟩ := he i
  obtain ⟨g⟩ := he' j
  rw [hj] at g
  exact ⟨(f.trans (JordanHolderLattice.Iso.linearEquiv (hc (e i)))).trans g.symm⟩

theorem HasFactors.reindex {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (c : ι ≃ κ) (hc : ∀ i, F' (c i) = F i) : HasFactors M F' := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  refine ⟨r, h1, h2, c.symm.trans e, fun j => ?_⟩
  obtain ⟨i, rfl⟩ := c.surjective j
  rw [hc, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact he i

theorem HasFactors.simple [IsSimpleModule R M] : HasFactors M (fun _ : Unit => ModuleCat.of R M) := by
  let r : CompositionSeries (Submodule R M) :=
    { length := 1
      toFun := ![⊥, ⊤]
      step := fun i => by
        fin_cases i
        exact bot_covBy_top }
  refine ⟨r, rfl, rfl, Equiv.ofUnique Unit (Fin 1), fun i => ⟨?_⟩⟩
  change M ≃ₗ[R] (↥(⊤ : Submodule R M) ⧸ (⊥ : Submodule R M).comap (⊤ : Submodule R M).subtype)
  exact Submodule.topEquiv.symm.trans (Submodule.quotEquivOfEqBot _ (by simp)).symm

theorem HasFactors.prod {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (h' : HasFactors N F') : HasFactors (M × N) (Sum.elim F F') := by
  obtain ⟨t, h1, h2, a, ha⟩ := h
  obtain ⟨s, h3, h4, c, hc⟩ := h'
  obtain ⟨r, h5, h6, e, he1, he2⟩ := exists_series_of_exact (R := R) (A := M) (C := N)
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd t h1 h2 s h3 h4
  refine ⟨r, h5, h6, (a.sumCongr c).trans e, ?_⟩
  rintro (i | j)
  · obtain ⟨u⟩ := ha i
    obtain ⟨v⟩ := he1 (a i)
    exact ⟨u.trans v⟩
  · obtain ⟨u⟩ := hc j
    obtain ⟨v⟩ := he2 (c j)
    exact ⟨u.trans v⟩

theorem HasFactors.zero [Subsingleton M] [IsEmpty ι] (F : ι → ModuleCat.{0} R) : HasFactors M F := by
  refine ⟨RelSeries.singleton _ ⊥, rfl, Subsingleton.elim _ _, Equiv.equivOfIsEmpty ι (Fin 0), fun i => ?_⟩
  exact isEmptyElim i

def succEquiv (m : ℕ) (ι : Type) : ι ⊕ (Fin m × ι) ≃ Fin (m + 1) × ι where
  toFun := Sum.elim (fun i => (0, i)) (fun p => (p.1.succ, p.2))
  invFun := fun p => Fin.cases (motive := fun _ => ι ⊕ (Fin m × ι)) (Sum.inl p.2) (fun j => Sum.inr (j, p.2)) p.1
  left_inv := by rintro (i | ⟨j, i⟩) <;> simp
  right_inv := by
    rintro ⟨j, i⟩
    induction j using Fin.cases <;> simp

theorem HasFactors.pi : ∀ {m : ℕ} {N : Fin m → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    {F : Fin m → ι → ModuleCat.{0} R}, (∀ j, HasFactors (N j) (F j)) →
    HasFactors (∀ j, N j) (fun p : Fin m × ι => F p.1 p.2)
  | 0, _, _, _, _, _ => HasFactors.zero _
  | m + 1, N, _, _, F, h =>
    (((h 0).prod (HasFactors.pi (F := fun j => F j.succ) fun j => h (Fin.succ j))).of_equiv
      (Fin.consLinearEquiv R N)).reindex (succEquiv m ι) (by rintro (i | ⟨j, i⟩) <;> rfl)

end Mod

section Rep
variable {k G : Type} [Field k] [Group G]

theorem equivariant_of_linear {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {π : Representation k G M} {π' : Representation k G N}
    (f : π.asModule →ₗ[MonoidAlgebra k G] π'.asModule) :
    ∃ f' : M →ₗ[k] N, (∀ g x, f' (π g x) = π' g (f' x)) ∧
      ∀ x, f' (π.asModuleEquiv x) = π'.asModuleEquiv (f x) := by
  let u := (Representation.IntertwiningMap.equivLinearMapAsModule π π').symm f
  exact ⟨u.toLinearMap, fun g x => LinearMap.congr_fun (u.isIntertwining' g) x, fun _ => rfl⟩

theorem chr_simple (χ : G →* kˣ) : IsSimpleModule (MonoidAlgebra k G) (chr χ).ρ.asModule := by
  have h : IsSimpleModule k (chr χ).ρ.asModule := by
    rw [isSimpleModule_iff_finrank_eq_one, (chr χ).ρ.asModuleEquiv.finrank_eq]
    simp
  have := IsSimpleModule.nontrivial k (chr χ).ρ.asModule
  refine { eq_bot_or_eq_top := fun S => ?_ }
  rcases eq_bot_or_eq_top (S.restrictScalars k) with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

def prodAsModule {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (π : Representation k G M) (π' : Representation k G N) :
    (π.prod π').asModule ≃ₗ[MonoidAlgebra k G] π.asModule × π'.asModule :=
  LinearEquiv.ofBijective
    (LinearMap.prod (asModuleMap (π := π.prod π') (π' := π) (LinearMap.fst k M N) fun _ _ => rfl)
      (asModuleMap (π := π.prod π') (π' := π') (LinearMap.snd k M N) fun _ _ => rfl))
    (Function.bijective_id (α := M × N))

theorem exists_subquot (T C : Ob k G) (Y : Submodule (MonoidAlgebra k G) T.ρ.asModule)
    (q : Y →ₗ[MonoidAlgebra k G] C.ρ.asModule) (hq : Function.Surjective q) :
    ∃ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom A₁ T j ∧ Function.Injective j ∧ IsHom A₁ C p ∧ Function.Surjective p := by
  have : Module.Finite k T.ρ.asModule := Module.Finite.equiv T.ρ.asModuleEquiv.symm
  have : Module.Finite k Y :=
    Module.Finite.of_injective (Y.subtype.restrictScalars k) Y.subtype_injective
  obtain ⟨A, e, he⟩ := exists_ob (Representation.ofModule' (k := k) (G := G) Y)
  have key : ∀ g x, e.symm (A.ρ g x) = MonoidAlgebra.of k G g • e.symm x := fun g x => by
    apply e.injective
    rw [e.apply_symm_apply]
    have := he g (e.symm x)
    rw [e.apply_symm_apply] at this
    rw [← this]
    congr 1
  refine ⟨A, T.ρ.asModuleEquiv.toLinearMap ∘ₗ Y.subtype.restrictScalars k ∘ₗ e.symm.toLinearMap,
    C.ρ.asModuleEquiv.toLinearMap ∘ₗ q.restrictScalars k ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    T.ρ.asModuleEquiv.injective.comp (Y.subtype_injective.comp e.symm.injective), fun g x => ?_,
    C.ρ.asModuleEquiv.surjective.comp (hq.comp e.symm.surjective)⟩
  · simp [key, Representation.asModuleEquiv_map_smul]
    rfl
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.restrictScalars_apply, key, map_smul]
    simp [Representation.asModuleEquiv_map_smul]
    rfl

theorem jh_match : ∀ {k G : Type} [Field k] [Group G] (T : Ob k G) (ω : G →* kˣ) (t μ s : ℕ) (C : Fin s → Ob k G), (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) → SameSS (piRep fun a => (C a).ρ) (piRep fun _ : Fin μ => refSum T ω t) → ∃ c : Fin s → Option (Fin t), (∀ a e, c a = some e → ∃ f, IsHom (C a) (chr (ω ^ (-(e.val : ℤ)))) f ∧ Function.Bijective f) ∧ (∀ a, c a = none → ∃ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin (C a).m → k)), IsHom A₁ T j ∧ Function.Injective j ∧ IsHom A₁ (C a) p ∧ Function.Surjective p) ∧ ∀ e, (Finset.univ.filter fun a => c a = some e).card = μ := by
  intro k G _ _ T ω t μ s C hC h
  have hT : IsFiniteLength (MonoidAlgebra k G) T.ρ.asModule :=
    finiteLength_asModule T.ρ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  obtain ⟨r, hr1, hr2⟩ := isFiniteLength_iff_exists_compositionSeries.mp hT
  have fT : HasFactors T.ρ.asModule (fun i : Fin r.length => ModuleCat.of (MonoidAlgebra k G) (factor r i)) :=
    ⟨r, hr1, hr2, Equiv.refl _, fun _ => ⟨LinearEquiv.refl _ _⟩⟩
  have fL := (HasFactors.pi (N := fun e : Fin t => (chr (ω ^ (-(e.val : ℤ)))).ρ.asModule) fun e =>
    @HasFactors.simple _ _ _ _ _ (chr_simple (ω ^ (-(e.val : ℤ))))).of_equiv
      (piAsModule fun e : Fin t => (chr (ω ^ (-(e.val : ℤ)))).ρ).symm
  have fR := (fT.prod fL).of_equiv (prodAsModule _ _).symm
  have fS := (HasFactors.pi (N := fun _ : Fin μ => (refSum T ω t).asModule) fun _ => fR).of_equiv
    (piAsModule fun _ : Fin μ => refSum T ω t).symm
  have fC := ((HasFactors.pi (N := fun a => (C a).ρ.asModule) fun a =>
    @HasFactors.simple _ _ _ _ _ (hC a)).of_equiv (piAsModule fun a => (C a).ρ).symm).of_same h
  obtain ⟨e, he⟩ := fC.unique fS
  refine ⟨fun a => Sum.elim (fun _ => none) (fun p => some p.1) (e (a, ())).2, fun a x hx => ?_,
    fun a hx => ?_, fun x => ?_⟩
  · obtain ⟨u⟩ := he (a, ())
    beta_reduce at hx
    generalize e (a, ()) = z at hx u
    rcases z with ⟨b, i | ⟨y, w⟩⟩
    · simp at hx
    · obtain rfl : y = x := by simpa using hx
      obtain ⟨f, hf1, hf2⟩ := equivariant_of_linear (π := (C a).ρ) (π' := (chr (ω ^ (-(y.val : ℤ)))).ρ) u.toLinearMap
      refine ⟨f, hf1, ?_⟩
      have : ⇑f ∘ (C a).ρ.asModuleEquiv = (chr (ω ^ (-(y.val : ℤ)))).ρ.asModuleEquiv ∘ u := funext hf2
      rw [← Function.Bijective.of_comp_iff _ (C a).ρ.asModuleEquiv.bijective, this]
      exact (LinearEquiv.bijective _).comp u.bijective
  · obtain ⟨u⟩ := he (a, ())
    beta_reduce at hx
    generalize e (a, ()) = z at hx u
    rcases z with ⟨b, i | ⟨y, w⟩⟩
    · let u' : (C a).ρ.asModule ≃ₗ[MonoidAlgebra k G] factor r i := u
      exact exists_subquot T (C a) (r i.succ) (u'.symm.toLinearMap ∘ₗ Submodule.mkQ _)
        (u'.symm.surjective.comp (Submodule.mkQ_surjective _))
    · simp at hx
  · refine Eq.trans ?_ (Finset.card_fin μ)
    symm
    refine Finset.card_bij (fun b _ => (e.symm (b, Sum.inr (x, ()))).1) (fun b _ => ?_) (fun b _ b' _ hb => ?_)
      (fun a ha => ?_)
    · have : ((e.symm (b, Sum.inr (x, ()))).1, ()) = e.symm (b, Sum.inr (x, ())) := rfl
      simp [this]
    · have : e.symm (b, Sum.inr (x, ())) = e.symm (b', Sum.inr (x, ())) := Prod.ext hb rfl
      simpa using this
    · refine ⟨(e (a, ())).1, Finset.mem_univ _, ?_⟩
      have h2 : (e (a, ())).2 = Sum.inr (x, ()) := by
        have := (Finset.mem_filter.mp ha).2
        beta_reduce at this
        generalize (e (a, ())).2 = z at this
        rcases z with i | ⟨y, w⟩
        · simp at this
        · simpa using this
      rw [← h2]
      simp

end Rep
end GlobalTheory.JHMatch
