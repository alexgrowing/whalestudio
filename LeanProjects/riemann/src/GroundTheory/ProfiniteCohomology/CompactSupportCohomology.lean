import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConeMap
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomologyMapPiLiftPiHomologyIsoHom
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section PiMap

variable {k : Type u} [CommRing k] {ι : Type u}

noncomputable def piMap {K K' : ι → CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, K v ⟶ K' v) :
    piComplex K ⟶ piComplex K' :=
  piLift fun v => piProj K v ≫ g v

@[reassoc (attr := simp)]
theorem piLift_piMap {M : CochainComplex (ModuleCat.{u} k) ℕ}
    {K K' : ι → CochainComplex (ModuleCat.{u} k) ℕ} (h : ∀ v, M ⟶ K v) (g : ∀ v, K v ⟶ K' v) :
    piLift h ≫ piMap g = piLift fun v => h v ≫ g v :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[reassoc (attr := simp)]
theorem piMap_piProj {K K' : ι → CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, K v ⟶ K' v)
    (v : ι) : piMap g ≫ piProj K' v = piProj K v ≫ g v :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem homologyMap_piMap_piHomologyIso_hom {K K' : ι → CochainComplex (ModuleCat.{u} k) ℕ}
    (g : ∀ v, K v ⟶ K' v) (n : ℕ) :
    HomologicalComplex.homologyMap (piMap g) n ≫ (piHomologyIso K' n).hom =
      (piHomologyIso K n).hom ≫ ModuleCat.ofHom (LinearMap.pi fun v =>
        (HomologicalComplex.homologyMap (g v) n).hom.comp (LinearMap.proj v)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun h => funext fun v => ?_)
  change (HomologicalComplex.homologyMap (piProj K' v) n).hom
      ((HomologicalComplex.homologyMap (piMap g) n).hom h) =
    (HomologicalComplex.homologyMap (g v) n).hom
      ((HomologicalComplex.homologyMap (piProj K v) n).hom h)
  rw [hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm h,
    hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm h, piMap_piProj]

noncomputable def piShortComplex (S : ι → ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (piMap fun v => (S v).f) (piMap fun v => (S v).g)
    (HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x =>
      funext fun v => hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) (S v).zero) (x v)))

theorem piShortComplex_shortExact {S : ι → ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)}
    (hS : ∀ v, (S v).ShortExact) : (piShortComplex S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    have h := fun v => (HomologicalComplex.shortExact_iff_degreewise_shortExact (S v)).1 (hS v) n
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro (x : ∀ v, (S v).X₂.X n) hx
      have e : ∀ v, ∃ y : (S v).X₁.X n, ((S v).f.f n).hom y = x v := fun v => by
        have ev := (h v).exact
        rw [ShortComplex.moduleCat_exact_iff] at ev
        exact ev (x v) (congrFun hx v)
      choose y hy using e
      exact ⟨show ∀ v, (S v).X₁.X n from y, funext hy⟩
    · exact (ModuleCat.mono_iff_injective _).2 fun (x x' : ∀ v, (S v).X₁.X n) hxx =>
        funext fun v => (ModuleCat.mono_iff_injective _).1 (h v).mono_f (congrFun hxx v)
    · refine (ModuleCat.epi_iff_surjective _).2 fun (z : ∀ v, (S v).X₃.X n) => ?_
      have e : ∀ v, ∃ y : (S v).X₂.X n, ((S v).g.f n).hom y = z v := fun v =>
        (ModuleCat.epi_iff_surjective _).1 (h v).epi_g (z v)
      choose y hy using e
      exact ⟨show ∀ v, (S v).X₂.X n from y, funext hy⟩

end PiMap

section CompactSupport

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)

section LongExactSequence

variable (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)

noncomputable def compactToGlobal (n : ℕ) : compactCohomology φ A Aᵥ a n ⟶ cohomology A n :=
  HomologicalComplex.homologyMap (mappingCoconeNat.fst (localRes φ A Aᵥ a)) n

noncomputable def globalToLocal (n : ℕ) :
    cohomology A n ⟶ ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) :=
  ModuleCat.ofHom (LinearMap.pi fun v =>
    (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (a v) n).hom)

noncomputable abbrev localCohomologyIso (n : ℕ) :
    (piComplex fun v => cochainsComplex (Aᵥ v)).homology n ≅
      ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) :=
  piHomologyIso _ n

theorem homologyMap_localRes_localCohomologyIso_hom (n : ℕ) :
    HomologicalComplex.homologyMap (localRes φ A Aᵥ a) n ≫ (localCohomologyIso Aᵥ n).hom =
      globalToLocal φ A Aᵥ a n :=
  homologyMap_piLift_piHomologyIso_hom _ _ n

noncomputable def localToCompact (n : ℕ) :
    ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) ⟶ compactCohomology φ A Aᵥ a (n + 1) :=
  (localCohomologyIso Aᵥ n).inv ≫ mappingCoconeNat.homologyδ (localRes φ A Aᵥ a) n

@[reassoc (attr := simp)]
theorem compactToGlobal_globalToLocal (n : ℕ) :
    compactToGlobal φ A Aᵥ a n ≫ globalToLocal φ A Aᵥ a n = 0 := by
  have h := mappingCoconeNat.homologyMap_fst_homologyMap_assoc (localRes φ A Aᵥ a) n
    (localCohomologyIso Aᵥ n).hom
  rw [homologyMap_localRes_localCohomologyIso_hom, zero_comp] at h
  exact h

@[reassoc (attr := simp)]
theorem globalToLocal_localToCompact (n : ℕ) :
    globalToLocal φ A Aᵥ a n ≫ localToCompact φ A Aᵥ a n = 0 := by
  have h := mappingCoconeNat.homologyMap_homologyδ (localRes φ A Aᵥ a) n
  rw [← Iso.hom_inv_id_assoc (localCohomologyIso Aᵥ n) (mappingCoconeNat.homologyδ _ n),
    ← Category.assoc, homologyMap_localRes_localCohomologyIso_hom] at h
  exact h

@[reassoc (attr := simp)]
theorem localToCompact_compactToGlobal (n : ℕ) :
    localToCompact φ A Aᵥ a n ≫ compactToGlobal φ A Aᵥ a (n + 1) = 0 := by
  have h := congrArg ((localCohomologyIso Aᵥ n).inv ≫ ·)
    (mappingCoconeNat.homologyδ_homologyMap_fst (localRes φ A Aᵥ a) n)
  simp only [comp_zero, ← Category.assoc] at h
  exact h

theorem compactCohomology_exact_global (n : ℕ) :
    (ShortComplex.mk _ _ (compactToGlobal_globalToLocal φ A Aᵥ a n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₃ (localRes φ A Aᵥ a) n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (localCohomologyIso Aᵥ n)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (homologyMap_localRes_localCohomologyIso_hom φ A Aᵥ a n).symm)

theorem compactCohomology_exact_local (n : ℕ) :
    (ShortComplex.mk _ _ (globalToLocal_localToCompact φ A Aᵥ a n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₁ (localRes φ A Aᵥ a) n)
  exact ShortComplex.isoMk (Iso.refl _) (localCohomologyIso Aᵥ n) (Iso.refl _)
    ((Category.id_comp _).trans (homologyMap_localRes_localCohomologyIso_hom φ A Aᵥ a n).symm)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)

theorem compactCohomology_exact_compact (n : ℕ) :
    (ShortComplex.mk _ _ (localToCompact_compactToGlobal φ A Aᵥ a n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (mappingCoconeNat.homology_exact₂ (localRes φ A Aᵥ a) n)
  exact ShortComplex.isoMk (localCohomologyIso Aᵥ n) (Iso.refl _) (Iso.refl _)
    ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem mono_compactToGlobal_zero : Mono (compactToGlobal φ A Aᵥ a 0) :=
  mappingCoconeNat.mono_homologyMap_fst_zero _

end LongExactSequence

section Functoriality

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Bᵥ v)]
  [∀ v, IsDiscreteRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}

theorem cochainsMapAlong_comp_cochainsMap {H' : Type u} [Group H'] [TopologicalSpace H']
    [IsTopologicalGroup H'] (ψ : H' →* G) (hψ : Continuous ψ)
    {A' B' : Rep.{u} k H'} [IsDiscreteRep A'] [IsDiscreteRep B'] (a' : Rep.res ψ A ⟶ A')
    (b' : Rep.res ψ B ⟶ B') (g : A ⟶ B) (g' : A' ⟶ B')
    (hg : a' ≫ g' = (Rep.resFunctor ψ).map g ≫ b') :
    cochainsMapAlong ψ hψ a' ≫ cochainsMap g' = cochainsMap g ≫ cochainsMapAlong ψ hψ b' := by
  ext n x : 3
  apply Subtype.ext
  funext σ
  exact congrArg (fun F : Rep.res ψ A ⟶ B' => F.hom (x.1 (⇑ψ ∘ σ))) hg

theorem localRes_naturality (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ b v) :
    localRes φ A Aᵥ a ≫ piMap (fun v => cochainsMap (gᵥ v)) =
      cochainsMap g ≫ localRes φ B Bᵥ b := by
  rw [localRes, localRes, piLift_piMap]
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x =>
    funext fun v => ?_)
  exact hom_apply_hom_apply_eq_of_comp_eq (congrArg (·.f n)
    (cochainsMapAlong_comp_cochainsMap _ (continuous_toMonoidHom (φ v)) (a v) (b v) g (gᵥ v)
      (hg v))) x

noncomputable def compactCochainsMap (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ b v) :
    compactCochains φ A Aᵥ a ⟶ compactCochains φ B Bᵥ b :=
  mappingCoconeNat.map (cochainsMap g) (piMap fun v => cochainsMap (gᵥ v))
    (localRes_naturality φ g gᵥ hg)

noncomputable def compactCohomologyMap (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ b v) (n : ℕ) :
    compactCohomology φ A Aᵥ a n ⟶ compactCohomology φ B Bᵥ b n :=
  HomologicalComplex.homologyMap (compactCochainsMap φ g gᵥ hg) n

omit [∀ v, IsDiscreteRep (Bᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)] [IsDiscreteRep B] [IsDiscreteRep C] in
@[simp]
theorem compactCohomologyMap_id (n : ℕ) :
    compactCohomologyMap φ (𝟙 A) (fun v => 𝟙 (Aᵥ v)) (a := a) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) n = 𝟙 _ := by
  have h : compactCochainsMap φ (𝟙 A) (fun v => 𝟙 (Aᵥ v)) (a := a) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) = 𝟙 _ := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochainsComplex A).X n ×
      shiftNegOneX (piComplex fun v => cochainsComplex (Aᵥ v)) n) => Prod.ext rfl ?_)
    cases n with
    | zero => rfl
    | succ n => rfl
  exact (congrArg (HomologicalComplex.homologyMap · n) h).trans
    (HomologicalComplex.homologyMap_id _ n)

variable (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v)
  (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ b v)

theorem compactCohomologyMap_comp (g' : B ⟶ C) (gᵥ' : ∀ v, Bᵥ v ⟶ Cᵥ v)
    (hg' : ∀ v, b v ≫ gᵥ' v = (Rep.resFunctor (φ v).toMonoidHom).map g' ≫ c v) (n : ℕ) :
    compactCohomologyMap φ (g ≫ g') (fun v => gᵥ v ≫ gᵥ' v)
        (fun v => by rw [reassoc_of% hg v, hg' v, Functor.map_comp, Category.assoc]) n =
      compactCohomologyMap φ g gᵥ hg n ≫ compactCohomologyMap φ g' gᵥ' hg' n := by
  have h : compactCochainsMap φ (g ≫ g') (fun v => gᵥ v ≫ gᵥ' v)
      (fun v => by rw [reassoc_of% hg v, hg' v, Functor.map_comp, Category.assoc]) =
      compactCochainsMap φ g gᵥ hg ≫ compactCochainsMap φ g' gᵥ' hg' := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochainsComplex A).X n ×
      shiftNegOneX (piComplex fun v => cochainsComplex (Aᵥ v)) n) => Prod.ext rfl ?_)
    cases n with
    | zero => rfl
    | succ n => rfl
  exact (congrArg (HomologicalComplex.homologyMap · n) h).trans
    (HomologicalComplex.homologyMap_comp _ _ n)

include hg in

theorem cohomologyMap_globalToLocal (n : ℕ) :
    cohomologyMap g n ≫ globalToLocal φ B Bᵥ b n =
      globalToLocal φ A Aᵥ a n ≫ ModuleCat.ofHom (LinearMap.pi fun v =>
        (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)) := by
  have h := congrArg (fun F => HomologicalComplex.homologyMap F n ≫ (localCohomologyIso Bᵥ n).hom)
    (localRes_naturality φ g gᵥ hg)
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc] at h
  have e1 : HomologicalComplex.homologyMap (localRes φ A Aᵥ a) n ≫
      HomologicalComplex.homologyMap (piMap fun v => cochainsMap (gᵥ v)) n ≫
        (localCohomologyIso Bᵥ n).hom =
      (HomologicalComplex.homologyMap (localRes φ A Aᵥ a) n ≫ (localCohomologyIso Aᵥ n).hom) ≫
        ModuleCat.ofHom (LinearMap.pi fun v =>
          (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)) := by
    exact (congrArg (HomologicalComplex.homologyMap (localRes φ A Aᵥ a) n ≫ ·)
      (homologyMap_piMap_piHomologyIso_hom (fun v => cochainsMap (gᵥ v)) n)).trans
      (Category.assoc _ _ _).symm
  exact (congrArg (cohomologyMap g n ≫ ·)
    (homologyMap_localRes_localCohomologyIso_hom φ B Bᵥ b n).symm).trans (h.symm.trans (e1.trans
      (congrArg (· ≫ ModuleCat.ofHom (LinearMap.pi fun v =>
          (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)))
        (homologyMap_localRes_localCohomologyIso_hom φ A Aᵥ a n))))

theorem localToCompact_compactCohomologyMap (n : ℕ) :
    localToCompact φ A Aᵥ a n ≫ compactCohomologyMap φ g gᵥ hg (n + 1) =
      ModuleCat.ofHom (LinearMap.pi fun v => (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)) ≫
        localToCompact φ B Bᵥ b n := by
  have h2 : (localCohomologyIso Aᵥ n).inv ≫
      HomologicalComplex.homologyMap (piMap fun v => cochainsMap (gᵥ v)) n =
      ModuleCat.ofHom (LinearMap.pi fun v => (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)) ≫
        (localCohomologyIso Bᵥ n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact homologyMap_piMap_piHomologyIso_hom _ n
  have h := congrArg ((localCohomologyIso Aᵥ n).inv ≫ ·)
    (mappingCoconeNat.homologyδ_naturality (cochainsMap g) (piMap fun v => cochainsMap (gᵥ v))
      (localRes_naturality φ g gᵥ hg) n)
  simp only [← Category.assoc] at h
  rw [h2, Category.assoc] at h
  exact h

end Functoriality

section CoefficientSequence

variable (S : ShortComplex (Rep.{u} k G)) [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] (Sᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))) [∀ v, IsDiscreteRep (Sᵥ v).X₁]
  [∀ v, IsDiscreteRep (Sᵥ v).X₂] [∀ v, IsDiscreteRep (Sᵥ v).X₃]
  (s : ∀ v, S.map (Rep.resFunctor (φ v).toMonoidHom) ⟶ Sᵥ v)

noncomputable def localResShortComplex :
    cochainsShortComplex S ⟶ piShortComplex fun v => cochainsShortComplex (Sᵥ v) where
  τ₁ := localRes φ S.X₁ (fun v => (Sᵥ v).X₁) fun v => (s v).τ₁
  τ₂ := localRes φ S.X₂ (fun v => (Sᵥ v).X₂) fun v => (s v).τ₂
  τ₃ := localRes φ S.X₃ (fun v => (Sᵥ v).X₃) fun v => (s v).τ₃
  comm₁₂ := localRes_naturality φ S.f (fun v => (Sᵥ v).f) fun v => (s v).comm₁₂
  comm₂₃ := localRes_naturality φ S.g (fun v => (Sᵥ v).g) fun v => (s v).comm₂₃

theorem compactCohomologyMap_f_g (n : ℕ) :
    compactCohomologyMap φ S.f (fun v => (Sᵥ v).f) (fun v => (s v).comm₁₂) n ≫
      compactCohomologyMap φ S.g (fun v => (Sᵥ v).g) (fun v => (s v).comm₂₃) n = 0 :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n)
      (mappingCoconeNat.mapShortComplex (localResShortComplex φ S Sᵥ s)).zero).trans
      (HomologicalComplex.homologyMap_zero _ _ n))

variable {S Sᵥ}

theorem compactCochains_shortExact (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact) :
    (mappingCoconeNat.mapShortComplex (localResShortComplex φ S Sᵥ s)).ShortExact :=
  mappingCoconeNat.shortExact_mapShortComplex _ (cochainsShortComplex_shortExact hS)
    (piShortComplex_shortExact fun v => cochainsShortComplex_shortExact (hSᵥ v))

variable (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact)

noncomputable def compactδ (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact) (n : ℕ) :
    compactCohomology φ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) n ⟶
      compactCohomology φ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁) (n + 1) :=
  (compactCochains_shortExact φ s hS hSᵥ).δ n (n + 1) rfl

include hS hSᵥ in

theorem compactCohomology_exact₂ (n : ℕ) :
    (ShortComplex.mk (compactCohomologyMap φ S.f (fun v => (Sᵥ v).f) (fun v => (s v).comm₁₂) n)
      (compactCohomologyMap φ S.g (fun v => (Sᵥ v).g) (fun v => (s v).comm₂₃) n)
      (compactCohomologyMap_f_g φ S Sᵥ s n)).Exact :=
  (compactCochains_shortExact φ s hS hSᵥ).homology_exact₂ n

theorem compactCohomology_exact₃ (n : ℕ) :
    (ShortComplex.mk (compactCohomologyMap φ S.g (fun v => (Sᵥ v).g) (fun v => (s v).comm₂₃) n)
      (compactδ φ s hS hSᵥ n)
      ((compactCochains_shortExact φ s hS hSᵥ).comp_δ n (n + 1) rfl)).Exact :=
  (compactCochains_shortExact φ s hS hSᵥ).homology_exact₃ n (n + 1) rfl

theorem compactCohomology_exact₁ (n : ℕ) :
    (ShortComplex.mk (compactδ φ s hS hSᵥ n)
      (compactCohomologyMap φ S.f (fun v => (Sᵥ v).f) (fun v => (s v).comm₁₂) (n + 1))
      ((compactCochains_shortExact φ s hS hSᵥ).δ_comp n (n + 1) rfl)).Exact :=
  (compactCochains_shortExact φ s hS hSᵥ).homology_exact₁ n (n + 1) rfl

end CoefficientSequence

end CompactSupport

end GroundTheory.ProfCoh
