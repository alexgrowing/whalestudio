import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle

noncomputable section

namespace GlobalTheory.AdmLoc

section Ss

variable {R : Type} [Ring R]
variable {M M' A A' C C' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']

theorem subquot_map {f : A →ₗ[R] M} (hf : Function.Injective f) (X Y : Submodule R A) {X' Y' : Submodule R M}
    (hX : X' = X.map f) (hY : Y' = Y.map f) :
    Nonempty ((↥Y ⧸ X.comap Y.subtype) ≃ₗ[R] (↥Y' ⧸ X'.comap Y'.subtype)) := by
  subst hX hY
  refine ⟨Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Y) ?_⟩
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hxx⟩ := hy
    obtain rfl : x' = x := hf hxx
    exact ⟨⟨x', hx'⟩, hx, rfl⟩

theorem subquot_comap {g : M →ₗ[R] C} (hg : Function.Surjective g) (X Y : Submodule R C) {X' Y' : Submodule R M}
    (hX : X' = X.comap g) (hY : Y' = Y.comap g) :
    Nonempty ((↥Y ⧸ X.comap Y.subtype) ≃ₗ[R] (↥Y' ⧸ X'.comap Y'.subtype)) := by
  subst hX hY
  let p : ↥(Y.comap g) →ₗ[R] ↥Y := g.restrict (fun _ h => h)
  let q : ↥(Y.comap g) →ₗ[R] (↥Y ⧸ X.comap Y.subtype) := (Submodule.mkQ _).comp p
  have hp : Function.Surjective p := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp hp
  have hk : (X.comap g).comap (Y.comap g).subtype = LinearMap.ker q := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero (X.comap Y.subtype) (x := p x)).symm
  exact ⟨((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm⟩

theorem exists_series_of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g)
    (t : CompositionSeries (Submodule R A)) (ht₁ : t.head = ⊥) (ht₂ : t.last = ⊤)
    (s : CompositionSeries (Submodule R C)) (hs₁ : s.head = ⊥) (hs₂ : s.last = ⊤) :
    ∃ r : CompositionSeries (Submodule R M), r.head = ⊥ ∧ r.last = ⊤ ∧
      ∃ e : Fin t.length ⊕ Fin s.length ≃ Fin r.length,
        (∀ i, Nonempty (factor t i ≃ₗ[R] factor r (e (Sum.inl i)))) ∧
        ∀ j, Nonempty (factor s j ≃ₗ[R] factor r (e (Sum.inr j))) := by
  let s' : CompositionSeries (Submodule R M) :=
    { length := s.length
      toFun := fun i => (s i).comap g
      step := fun i => Submodule.comap_covBy_of_surjective hg (s.step i) }
  let t' : CompositionSeries (Submodule R M) :=
    { length := t.length
      toFun := fun i => (t i).map f
      step := fun i => Submodule.map_covBy_of_injective hf (t.step i) }
  have hc : t'.last = s'.head := by
    change t.last.map f = s.head.comap g
    rw [ht₂, hs₁, Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
  refine ⟨t'.smash s' hc, ?_, ?_, finSumFinEquiv, fun i => ?_, fun j => ?_⟩
  · rw [RelSeries.head_smash]
    change t.head.map f = ⊥
    rw [ht₁, Submodule.map_bot]
  · rw [RelSeries.last_smash]
    change s.last.comap g = ⊤
    rw [hs₂, Submodule.comap_top]
  · exact subquot_map hf _ _ (RelSeries.smash_castAdd hc i) (RelSeries.smash_succ_castAdd hc i)
  · exact subquot_comap hg _ _ (RelSeries.smash_natAdd hc j) (RelSeries.smash_succ_natAdd hc j)

theorem SameFactors.finiteLength_left (h : SameFactors R M M') : IsFiniteLength R M := by
  obtain ⟨s, -, h1, h2, -⟩ := h
  exact isFiniteLength_of_exists_compositionSeries ⟨s, h1, h2⟩

theorem SameFactors.finiteLength_right (h : SameFactors R M M') : IsFiniteLength R M' :=
  h.symm.finiteLength_left

theorem SameFactors.of_exact_of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g)
    {f' : A' →ₗ[R] M'} {g' : M' →ₗ[R] C'} (hf' : Function.Injective f')
    (hg' : Function.Surjective g') (H' : Function.Exact f' g')
    (hA : SameFactors R A A') (hC : SameFactors R C C') : SameFactors R M M' := by
  obtain ⟨t, t', ht1, ht2, ht3, ht4, a, ha⟩ := hA
  obtain ⟨s, s', hs1, hs2, hs3, hs4, c, hc⟩ := hC
  obtain ⟨r, hr1, hr2, e, he1, he2⟩ := exists_series_of_exact hf hg H t ht1 ht2 s hs1 hs2
  obtain ⟨r', hr3, hr4, e', he3, he4⟩ := exists_series_of_exact hf' hg' H' t' ht3 ht4 s' hs3 hs4
  refine ⟨r, r', hr1, hr2, hr3, hr4, e.symm.trans ((a.sumCongr c).trans e'), fun k => ?_⟩
  obtain ⟨k, rfl⟩ := e.surjective k
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rcases k with i | j
  · obtain ⟨u⟩ := he1 i
    obtain ⟨v⟩ := ha i
    obtain ⟨w⟩ := he3 (a i)
    exact ⟨(u.symm.trans v).trans w⟩
  · obtain ⟨u⟩ := he2 j
    obtain ⟨v⟩ := hc j
    obtain ⟨w⟩ := he4 (c j)
    exact ⟨(u.symm.trans v).trans w⟩

theorem SameFactors.of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g) (h : IsFiniteLength R M) :
    SameFactors R M (A × C) :=
  SameFactors.of_exact_of_exact hf hg H LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (SameFactors.refl (h.of_injective hf)) (SameFactors.refl (h.of_surjective hg))

theorem SameFactors.sub_prod_quot (h : IsFiniteLength R M) (S : Submodule R M) :
    SameFactors R M (↥S × (M ⧸ S)) :=
  SameFactors.of_exact S.subtype_injective S.mkQ_surjective (LinearMap.exact_subtype_mkQ S) h

theorem SameFactors.prod (hA : SameFactors R A A') (hC : SameFactors R C C') :
    SameFactors R (A × C) (A' × C') :=
  SameFactors.of_exact_of_exact LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd hA hC

theorem SameFactors.congr (h : SameFactors R A A') (e : A ≃ₗ[R] C) (e' : A' ≃ₗ[R] C') : SameFactors R C C' :=
  ((SameFactors.of_equiv h.finiteLength_left e).symm.trans h).trans (SameFactors.of_equiv h.finiteLength_right e')

theorem SameFactors.of_subsingleton [Subsingleton A] [Subsingleton A'] : SameFactors R A A' :=
  SameFactors.of_equiv IsFiniteLength.of_subsingleton (LinearEquiv.ofSubsingleton _ _)

theorem SameFactors.pi_fin : ∀ {m : ℕ} {N N' : Fin m → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)], (∀ j, SameFactors R (N j) (N' j)) →
    SameFactors R (∀ j, N j) (∀ j, N' j)
  | 0, _, _, _, _, _, _, _ => SameFactors.of_subsingleton
  | _ + 1, N, N', _, _, _, _, h =>
    ((h 0).prod (SameFactors.pi_fin fun j => h (Fin.succ j))).congr
      (Fin.consLinearEquiv R N) (Fin.consLinearEquiv R N')

theorem SameFactors.pi {ι : Type} [Finite ι] {N N' : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)] (h : ∀ j, SameFactors R (N j) (N' j)) :
    SameFactors R (∀ j, N j) (∀ j, N' j) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact (SameFactors.pi_fin (N := fun j => N (e.symm j)) (N' := fun j => N' (e.symm j))
    fun j => h (e.symm j)).congr (LinearEquiv.piCongrLeft R N e.symm) (LinearEquiv.piCongrLeft R N' e.symm)

theorem SameFactors.prod_comm (hA : IsFiniteLength R A) (hC : IsFiniteLength R C) :
    SameFactors R (A × C) (C × A) :=
  ((SameFactors.refl hA).prod (SameFactors.refl hC)).congr (LinearEquiv.refl _ _) (LinearEquiv.prodComm R A C)

end Ss

section Rep

variable {O G : Type} [CommRing O] [Group G]
variable {M M' A A' C C' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
  [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
  [AddCommGroup C] [Module O C] [AddCommGroup C'] [Module O C']

def asModuleMap {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M')
    (hf : ∀ g x, f (π g x) = π' g (f x)) : π.asModule →ₗ[MonoidAlgebra O G] π'.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule π π'
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }

theorem asModuleMap_apply {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M')
    (hf : ∀ g x, f (π g x) = π' g (f x)) (x : π.asModule) :
    π'.asModuleEquiv (asModuleMap f hf x) = f (π.asModuleEquiv x) := rfl

def equivAsModule {π : Representation O G M} {π' : Representation O G M'} (e : M ≃ₗ[O] M')
    (he : ∀ g x, e (π g x) = π' g (e x)) : π.asModule ≃ₗ[MonoidAlgebra O G] π'.asModule :=
  LinearEquiv.ofBijective (asModuleMap e.toLinearMap he) e.bijective

def piAsModule {ι : Type} {N : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    (π : ∀ j, Representation O G (N j)) :
    (piRep π).asModule ≃ₗ[MonoidAlgebra O G] ∀ j, (π j).asModule :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun j => asModuleMap (π := piRep π) (π' := π j) (LinearMap.proj j) fun _ _ => rfl)
    (Function.bijective_id (α := ∀ j, N j))

theorem finiteLength_asModule (π : Representation O G M) (h : IsFiniteLength O M) :
    IsFiniteLength (MonoidAlgebra O G) π.asModule := by
  have h' : IsFiniteLength O π.asModule := h.of_injective (f := π.asModuleEquiv.toLinearMap) π.asModuleEquiv.injective
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h' ⊢
  exact ⟨isNoetherian_of_tower O h'.1, isArtinian_of_tower O h'.2⟩

variable {π : Representation O G M} {π' : Representation O G M'} {α : Representation O G A}
  {α' : Representation O G A'} {γ : Representation O G C} {γ' : Representation O G C'}

theorem SameSS.refl' (h : IsFiniteLength (MonoidAlgebra O G) π.asModule) : SameSS π π := SameFactors.refl h

theorem SameSS.refl (π : Representation O G M) (h : IsFiniteLength O M) : SameSS π π :=
  SameFactors.refl (finiteLength_asModule π h)

theorem SameSS.symm (h : SameSS π π') : SameSS π' π := SameFactors.symm h

theorem SameSS.trans (h : SameSS π π') (h' : SameSS π' α) : SameSS π α := SameFactors.trans h h'

theorem SameSS.of_equiv (h : IsFiniteLength O M) (e : M ≃ₗ[O] M') (he : ∀ g x, e (π g x) = π' g (e x)) :
    SameSS π π' :=
  SameFactors.of_equiv (finiteLength_asModule π h) (equivAsModule e he)

theorem SameSS.congr (h : SameSS α α') (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x))
    (e' : A' ≃ₗ[O] C') (he' : ∀ g x, e' (α' g x) = γ' g (e' x)) : SameSS γ γ' :=
  SameFactors.congr h (equivAsModule e he) (equivAsModule e' he')

theorem SameSS.congr_left (h : SameSS α π) (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x)) : SameSS γ π :=
  h.congr e he (LinearEquiv.refl O M) fun _ _ => rfl

theorem SameSS.congr_right (h : SameSS π α) (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x)) : SameSS π γ :=
  h.congr (LinearEquiv.refl O M) (fun _ _ => rfl) e he

theorem SameSS.of_exact_of_exact {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    {f' : A' →ₗ[O] M'} {p' : M' →ₗ[O] C'}
    (ef' : ∀ g x, f' (α' g x) = π' g (f' x)) (ep' : ∀ g x, p' (π' g x) = γ' g (p' x))
    (hf' : Function.Injective f') (hp' : Function.Surjective p') (H' : Function.Exact f' p')
    (hA : SameSS α α') (hC : SameSS γ γ') : SameSS π π' :=
  SameFactors.of_exact_of_exact (R := MonoidAlgebra O G) (M := π.asModule) (M' := π'.asModule)
    (A := α.asModule) (A' := α'.asModule) (C := γ.asModule) (C' := γ'.asModule)
    (f := asModuleMap f ef) (g := asModuleMap p ep) hf hp H
    (f' := asModuleMap f' ef') (g' := asModuleMap p' ep') hf' hp' H' hA hC

theorem SameSS.of_exact' {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    (h : IsFiniteLength (MonoidAlgebra O G) π.asModule) : SameSS π (α.prod γ) :=
  SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inl O A C) (p' := LinearMap.snd O A C)
    (α' := α) (γ' := γ) (fun g x => by simp) (fun g x => by simp)
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (SameSS.refl' (IsFiniteLength.of_injective (M := α.asModule) (N := π.asModule) (f := asModuleMap f ef) h hf))
    (SameSS.refl' (IsFiniteLength.of_surjective (M := π.asModule) (N := γ.asModule) (f := asModuleMap p ep) h hp))

theorem SameSS.of_exact {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    (h : IsFiniteLength O M) : SameSS π (α.prod γ) :=
  SameSS.of_exact' ef ep hf hp H (finiteLength_asModule π h)

theorem SameSS.prod (hA : SameSS α α') (hC : SameSS γ γ') : SameSS (α.prod γ) (α'.prod γ') :=
  SameSS.of_exact_of_exact (f := LinearMap.inl O A C) (p := LinearMap.snd O A C)
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (f' := LinearMap.inl O A' C') (p' := LinearMap.snd O A' C')
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd hA hC

theorem SameSS.piRep {ι : Type} [Finite ι] {N N' : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module O (N' j)] {σ : ∀ j, Representation O G (N j)}
    {σ' : ∀ j, Representation O G (N' j)} (h : ∀ j, SameSS (σ j) (σ' j)) : SameSS (piRep σ) (piRep σ') :=
  (SameFactors.pi (N := fun j => (σ j).asModule) (N' := fun j => (σ' j).asModule) h).congr
    (piAsModule σ).symm (piAsModule σ').symm

end Rep

end GlobalTheory.AdmLoc
