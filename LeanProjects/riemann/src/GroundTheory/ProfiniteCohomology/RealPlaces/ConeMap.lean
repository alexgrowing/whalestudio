import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalCohomologyIsoHomologyMapNormCochains
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Complexes

variable {k : Type u} [CommRing k]

noncomputable def degZeroMapF {E E' : ModuleCat.{u} k} (f : E ⟶ E') :
    ∀ n, (degZeroComplex E).X n ⟶ (degZeroComplex E').X n
  | 0 => f
  | _ + 1 => 0

noncomputable def degZeroMap {E E' : ModuleCat.{u} k} (f : E ⟶ E') :
    degZeroComplex E ⟶ degZeroComplex E' :=
  CochainComplex.ofHom (degZeroMapF f) fun n => by
    rw [degZeroComplex_d, degZeroComplex_d, comp_zero, zero_comp]

theorem degZeroMap_f_zero_apply {E E' : ModuleCat.{u} k} (f : E ⟶ E') (e : (degZeroComplex E).X 0) :
    ((degZeroMap f).f 0).hom e = f.hom e :=
  rfl

theorem degZeroMap_id (E : ModuleCat.{u} k) : degZeroMap (𝟙 E) = 𝟙 _ := by
  ext n : 1
  cases n with
  | zero => rfl
  | succ n => exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

theorem degZeroMap_comp {E E' E'' : ModuleCat.{u} k} (f : E ⟶ E') (f' : E' ⟶ E'') :
    degZeroMap (f ≫ f') = degZeroMap f ≫ degZeroMap f' := by
  ext n : 1
  cases n with
  | zero => rfl
  | succ n => exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

noncomputable def degZeroShortComplex (S : ShortComplex (ModuleCat.{u} k)) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (degZeroMap S.f) (degZeroMap S.g) (by rw [← degZeroMap_comp, S.zero]; ext n : 1; cases n <;> rfl)

theorem degZeroShortComplex_shortExact {S : ShortComplex (ModuleCat.{u} k)} (hS : S.ShortExact) :
    (degZeroShortComplex S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    cases n with
    | zero => exact hS
    | succ n =>
      have h0 : IsZero ((degZeroComplex S.X₂).X (n + 1)) := ModuleCat.isZero_of_subsingleton _
      exact { exact := ShortComplex.exact_of_isZero_X₂ _ h0
              mono_f := (ModuleCat.mono_iff_injective _).2 fun x y _ =>
                Subsingleton.elim (α := PUnit) x y
              epi_g := (ModuleCat.epi_iff_surjective _).2 fun y =>
                ⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ y⟩ }

noncomputable def prodShortComplex (S T : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (prodMapCx S.f T.f) (prodMapCx S.g T.g)
    (HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext
      (hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) S.zero) x.1)
      (hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) T.zero) x.2)))

theorem prodShortComplex_shortExact {S T : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)}
    (hS : S.ShortExact) (hT : T.ShortExact) : (prodShortComplex S T).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    have h1 := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
    have h2 := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hT n
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro (x : S.X₂.X n × T.X₂.X n) hx
      have e1 := h1.exact
      have e2 := h2.exact
      rw [ShortComplex.moduleCat_exact_iff] at e1 e2
      obtain ⟨y1, hy1⟩ := e1 x.1 (congrArg Prod.fst hx)
      obtain ⟨y2, hy2⟩ := e2 x.2 (congrArg Prod.snd hx)
      exact ⟨(show (prodComplex S.X₁ T.X₁).X n from (y1, y2)), Prod.ext hy1 hy2⟩
    · exact (ModuleCat.mono_iff_injective _).2 fun (x x' : S.X₁.X n × T.X₁.X n) hxx =>
        Prod.ext ((ModuleCat.mono_iff_injective _).1 h1.mono_f (congrArg Prod.fst hxx))
          ((ModuleCat.mono_iff_injective _).1 h2.mono_f (congrArg Prod.snd hxx))
    · refine (ModuleCat.epi_iff_surjective _).2 fun (z : S.X₃.X n × T.X₃.X n) => ?_
      obtain ⟨y1, hy1⟩ := (ModuleCat.epi_iff_surjective _).1 h1.epi_g z.1
      obtain ⟨y2, hy2⟩ := (ModuleCat.epi_iff_surjective _).1 h2.epi_g z.2
      exact ⟨(show (prodComplex S.X₂ T.X₂).X n from (y1, y2)), Prod.ext hy1 hy2⟩

theorem homologyMap_prodMapCx_prodHomologyIso_hom {M N M' N' : CochainComplex (ModuleCat.{u} k) ℕ}
    (f : M ⟶ M') (g : N ⟶ N') (n : ℕ) :
    HomologicalComplex.homologyMap (prodMapCx f g) n ≫ (prodHomologyIso M' N' n).hom =
      (prodHomologyIso M N n).hom ≫ ModuleCat.ofHom
        ((HomologicalComplex.homologyMap f n).hom.prodMap (HomologicalComplex.homologyMap g n).hom) := by
  have e1 : prodMapCx f g ≫ prodFst M' N' = prodFst M N ≫ f := prodLift_prodFst _ _
  have e2 : prodMapCx f g ≫ prodSnd M' N' = prodSnd M N ≫ g := prodLift_prodSnd _ _
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (by
      rw [← HomologicalComplex.homologyMap_comp, e1, HomologicalComplex.homologyMap_comp]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)) z
  · exact hom_apply_hom_apply_eq_of_comp_eq (by
      rw [← HomologicalComplex.homologyMap_comp, e2, HomologicalComplex.homologyMap_comp]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)) z

end Complexes

section RepProducts

variable {k : Type u} [CommRing k] {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)]

noncomputable def piRepHom {Aᵣ Bᵣ : ∀ w, Rep.{u} k (F w)} (g : ∀ w, Aᵣ w ⟶ Bᵣ w) :
    ModuleCat.of k (∀ w, Aᵣ w) ⟶ ModuleCat.of k (∀ w, Bᵣ w) :=
  ModuleCat.ofHom (LinearMap.pi fun w => (g w).hom.toLinearMap.comp (LinearMap.proj w))

theorem piRepHom_apply {Aᵣ Bᵣ : ∀ w, Rep.{u} k (F w)} (g : ∀ w, Aᵣ w ⟶ Bᵣ w)
    (e : ∀ w, Aᵣ w) (w : κ) : (piRepHom g).hom e w = (g w).hom (e w) :=
  rfl

noncomputable def piRepShortComplex (S : ∀ w, ShortComplex (Rep.{u} k (F w))) :
    ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (piRepHom fun w => (S w).f) (piRepHom fun w => (S w).g)
    (ModuleCat.hom_ext (LinearMap.ext fun e => funext fun w =>
      congrArg (fun φ => Rep.Hom.hom φ (e w)) (S w).zero))

theorem piRepShortComplex_shortExact {S : ∀ w, ShortComplex (Rep.{u} k (F w))}
    (hS : ∀ w, (S w).ShortExact) : (piRepShortComplex S).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro (x : ∀ w, (S w).X₂) hx
    have e : ∀ w, ∃ y : (S w).X₁, (S w).f.hom y = x w := fun w => by
      have ev := (hS w).exact.map (forget₂ (Rep.{u} k (F w)) (ModuleCat k))
      rw [ShortComplex.moduleCat_exact_iff] at ev
      exact ev (x w) (congrFun hx w)
    choose y hy using e
    exact ⟨show ∀ w, (S w).X₁ from y, funext hy⟩
  · exact (ModuleCat.mono_iff_injective _).2 fun (x x' : ∀ w, (S w).X₁) hxx => funext fun w =>
      (Rep.mono_iff_injective _).1 (hS w).mono_f (congrFun hxx w)
  · refine (ModuleCat.epi_iff_surjective _).2 fun (z : ∀ w, (S w).X₃) => ?_
    have e : ∀ w, ∃ y : (S w).X₂, (S w).g.hom y = z w := fun w =>
      (Rep.epi_iff_surjective _).1 (hS w).epi_g (z w)
    choose y hy using e
    exact ⟨show ∀ w, (S w).X₂ from y, funext hy⟩

end RepProducts

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section Functoriality

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Bᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Bᵥ v)]
  [∀ v, IsDiscreteRep (Cᵥ v)] {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v}
  {b : ∀ v, Rep.res (φ v).toMonoidHom B ⟶ Bᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Bᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Bᵣ w)]
  [∀ w, IsDiscreteRep (Cᵣ w)] {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w}
  {br : ∀ w, Rep.res (ψ w).toMonoidHom B ⟶ Bᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}

omit [IsTopologicalGroup G] in

theorem normCochains_naturality (gᵣ : ∀ w, Aᵣ w ⟶ Bᵣ w) :
    normCochains Aᵣ ≫ piMap (fun w => cochainsMap (gᵣ w)) =
      degZeroMap (piRepHom gᵣ) ≫ normCochains Bᵣ := by
  ext n : 1
  cases n with
  | zero =>
    refine ModuleCat.hom_ext (LinearMap.ext fun e => funext fun w => ?_)
    apply cochainOf_injective
    funext σ
    change (gᵣ w).hom ((Aᵣ w).ρ.norm (e w)) = (Bᵣ w).ρ.norm ((gᵣ w).hom (e w))
    exact (congrArg (fun f => Rep.Hom.hom f (e w)) (Rep.norm_comm (gᵣ w))).symm
  | succ n =>
    change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    rw [zero_comp, comp_zero]

variable (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v) (gᵣ : ∀ w, Aᵣ w ⟶ Bᵣ w)
  (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ b v)
  (hgr : ∀ w, ar w ≫ gᵣ w = (Rep.resFunctor (ψ w).toMonoidHom).map g ≫ br w)

noncomputable abbrev tateGlobalMap : tateGlobalComplex A Aᵣ ⟶ tateGlobalComplex B Bᵣ :=
  prodMapCx (cochainsMap g) (degZeroMap (piRepHom gᵣ))

noncomputable abbrev tateLocalMap : tateLocalComplex Aᵥ Aᵣ ⟶ tateLocalComplex Bᵥ Bᵣ :=
  prodMapCx (piMap fun v => cochainsMap (gᵥ v)) (piMap fun w => cochainsMap (gᵣ w))

include hg hgr in

theorem tateCompactRes_naturality :
    tateCompactRes φ ψ A Aᵥ a Aᵣ ar ≫ tateLocalMap gᵥ gᵣ =
      tateGlobalMap g gᵣ ≫ tateCompactRes φ ψ B Bᵥ b Bᵣ br := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (congrArg (·.f n) (localRes_naturality φ g gᵥ hg)) x.1
  · change ((piMap fun w => cochainsMap (gᵣ w)).f n).hom
        (((localRes ψ A Aᵣ ar).f n).hom x.1 + ((normCochains Aᵣ).f n).hom x.2) =
      ((localRes ψ B Bᵣ br).f n).hom (((cochainsMap g).f n).hom x.1) +
        ((normCochains Bᵣ).f n).hom (((degZeroMap (piRepHom gᵣ)).f n).hom x.2)
    rw [map_add]
    exact congrArg₂ (· + ·)
      (hom_apply_hom_apply_eq_of_comp_eq (congrArg (·.f n) (localRes_naturality ψ g gᵣ hgr)) x.1)
      (hom_apply_hom_apply_eq_of_comp_eq (congrArg (·.f n) (normCochains_naturality gᵣ)) x.2)

noncomputable def tateCompactCochainsMap :
    tateCompactCochains φ ψ A Aᵥ a Aᵣ ar ⟶ tateCompactCochains φ ψ B Bᵥ b Bᵣ br :=
  mappingCoconeNat.map (tateGlobalMap g gᵣ) (tateLocalMap gᵥ gᵣ)
    (tateCompactRes_naturality φ ψ g gᵥ gᵣ hg hgr)

noncomputable def tateCompactCohomologyMap (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar n ⟶ tateCompactCohomology φ ψ B Bᵥ b Bᵣ br n :=
  HomologicalComplex.homologyMap (tateCompactCochainsMap φ ψ g gᵥ gᵣ hg hgr) n

omit [∀ v, IsDiscreteRep (Bᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)] [IsDiscreteRep B] [IsDiscreteRep C]
  [∀ w, IsDiscreteRep (Bᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)] in
@[simp]
theorem tateCompactCohomologyMap_id (n : ℕ) :
    tateCompactCohomologyMap φ ψ (𝟙 A) (fun v => 𝟙 (Aᵥ v)) (fun w => 𝟙 (Aᵣ w)) (a := a) (ar := ar)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) n = 𝟙 _ := by
  have h : tateCompactCochainsMap φ ψ (𝟙 A) (fun v => 𝟙 (Aᵥ v)) (fun w => 𝟙 (Aᵣ w)) (a := a)
      (ar := ar) (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) = 𝟙 _ := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A Aᵣ).X n ×
      shiftNegOneX (tateLocalComplex Aᵥ Aᵣ) n) => Prod.ext (Prod.ext rfl ?_) ?_)
    · cases n with
      | zero => rfl
      | succ n => exact Subsingleton.elim _ _
    · cases n with
      | zero => rfl
      | succ n => rfl
  exact (congrArg (HomologicalComplex.homologyMap · n) h).trans
    (HomologicalComplex.homologyMap_id _ n)

theorem tateCompactCohomologyMap_comp (g' : B ⟶ C) (gᵥ' : ∀ v, Bᵥ v ⟶ Cᵥ v)
    (gᵣ' : ∀ w, Bᵣ w ⟶ Cᵣ w)
    (hg' : ∀ v, b v ≫ gᵥ' v = (Rep.resFunctor (φ v).toMonoidHom).map g' ≫ c v)
    (hgr' : ∀ w, br w ≫ gᵣ' w = (Rep.resFunctor (ψ w).toMonoidHom).map g' ≫ cr w) (n : ℕ) :
    tateCompactCohomologyMap φ ψ (g ≫ g') (fun v => gᵥ v ≫ gᵥ' v) (fun w => gᵣ w ≫ gᵣ' w)
        (fun v => by rw [reassoc_of% hg v, hg' v, Functor.map_comp, Category.assoc])
        (fun w => by rw [reassoc_of% hgr w, hgr' w, Functor.map_comp, Category.assoc]) n =
      tateCompactCohomologyMap φ ψ g gᵥ gᵣ hg hgr n ≫
        tateCompactCohomologyMap φ ψ g' gᵥ' gᵣ' hg' hgr' n := by
  have h : tateCompactCochainsMap φ ψ (g ≫ g') (fun v => gᵥ v ≫ gᵥ' v) (fun w => gᵣ w ≫ gᵣ' w)
      (fun v => by rw [reassoc_of% hg v, hg' v, Functor.map_comp, Category.assoc])
      (fun w => by rw [reassoc_of% hgr w, hgr' w, Functor.map_comp, Category.assoc]) =
      tateCompactCochainsMap φ ψ g gᵥ gᵣ hg hgr ≫ tateCompactCochainsMap φ ψ g' gᵥ' gᵣ' hg' hgr' := by
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A Aᵣ).X n ×
      shiftNegOneX (tateLocalComplex Aᵥ Aᵣ) n) => Prod.ext (Prod.ext rfl ?_) ?_)
    · cases n with
      | zero => rfl
      | succ n => exact Subsingleton.elim _ _
    · cases n with
      | zero => rfl
      | succ n => rfl
  exact (congrArg (HomologicalComplex.homologyMap · n) h).trans
    (HomologicalComplex.homologyMap_comp _ _ n)

theorem tateCompactCohomologyMap_tateToGlobal (n : ℕ) :
    tateCompactCohomologyMap φ ψ g gᵥ gᵣ hg hgr n ≫ tateToGlobal φ ψ B Bᵥ b Bᵣ br n =
      tateToGlobal φ ψ A Aᵥ a Aᵣ ar n ≫ cohomologyMap g n := by
  have e : tateCompactCochainsMap φ ψ g gᵥ gᵣ hg hgr ≫
      (mappingCoconeNat.fst (tateCompactRes φ ψ B Bᵥ b Bᵣ br) ≫ prodFst _ _) =
      (mappingCoconeNat.fst (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) ≫ prodFst _ _) ≫ cochainsMap g :=
    HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  exact (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n) e).trans
      (HomologicalComplex.homologyMap_comp _ _ _))

omit [∀ w, Fintype (F w)] in
include hg hgr in

theorem cohomologyMap_tateGlobalToLocal (n : ℕ) :
    cohomologyMap g n ≫ tateGlobalToLocal φ ψ B Bᵥ b Bᵣ br n =
      tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n ≫ ModuleCat.ofHom
        ((LinearMap.pi fun v => (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)).prodMap
          (LinearMap.pi fun w => (cohomologyMap (gᵣ w) n).hom.comp (LinearMap.proj w))) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (cohomologyMap_globalToLocal φ g gᵥ hg n) x
  · exact hom_apply_hom_apply_eq_of_comp_eq (cohomologyMap_globalToLocal ψ g gᵣ hgr n) x

omit [∀ w, Fintype (F w)] in

theorem homologyMap_tateLocalMap_tateLocalCohomologyIso_hom (n : ℕ) :
    HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n ≫ (tateLocalCohomologyIso Bᵥ Bᵣ n).hom =
      (tateLocalCohomologyIso Aᵥ Aᵣ n).hom ≫ ModuleCat.ofHom
        ((LinearMap.pi fun v => (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)).prodMap
          (LinearMap.pi fun w => (cohomologyMap (gᵣ w) n).hom.comp (LinearMap.proj w))) := by
  have e1 := homologyMap_prodMapCx_prodHomologyIso_hom (piMap fun v => cochainsMap (gᵥ v))
    (piMap fun w => cochainsMap (gᵣ w)) n
  have e2 := homologyMap_piMap_piHomologyIso_hom (fun v => cochainsMap (gᵥ v)) n
  have e3 := homologyMap_piMap_piHomologyIso_hom (fun w => cochainsMap (gᵣ w)) n
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Prod.ext ?_ ?_)
  · have h1 := congrArg Prod.fst (hom_apply_hom_apply_eq_of_comp_eq e1 z)
    change (localCohomologyIso Bᵥ n).hom.hom (HomologicalComplex.homologyMap (prodFst _ _) n |>.hom
        ((HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n).hom z)) = _
    rw [show (HomologicalComplex.homologyMap (prodFst _ _) n).hom
        ((HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n).hom z) = _ from h1]
    exact hom_apply_hom_apply_eq_of_comp_eq e2 _
  · have h2 := congrArg Prod.snd (hom_apply_hom_apply_eq_of_comp_eq e1 z)
    change (localCohomologyIso Bᵣ n).hom.hom (HomologicalComplex.homologyMap (prodSnd _ _) n |>.hom
        ((HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n).hom z)) = _
    rw [show (HomologicalComplex.homologyMap (prodSnd _ _) n).hom
        ((HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n).hom z) = _ from h2]
    exact hom_apply_hom_apply_eq_of_comp_eq e3 _

theorem tateLocalToCompact_tateCompactCohomologyMap (n : ℕ) :
    tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n ≫ tateCompactCohomologyMap φ ψ g gᵥ gᵣ hg hgr (n + 1) =
      ModuleCat.ofHom
          ((LinearMap.pi fun v => (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)).prodMap
            (LinearMap.pi fun w => (cohomologyMap (gᵣ w) n).hom.comp (LinearMap.proj w))) ≫
        tateLocalToCompact φ ψ B Bᵥ b Bᵣ br n := by
  have h2 : (tateLocalCohomologyIso Aᵥ Aᵣ n).inv ≫
      HomologicalComplex.homologyMap (tateLocalMap gᵥ gᵣ) n =
      ModuleCat.ofHom
          ((LinearMap.pi fun v => (cohomologyMap (gᵥ v) n).hom.comp (LinearMap.proj v)).prodMap
            (LinearMap.pi fun w => (cohomologyMap (gᵣ w) n).hom.comp (LinearMap.proj w))) ≫
        (tateLocalCohomologyIso Bᵥ Bᵣ n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact homologyMap_tateLocalMap_tateLocalCohomologyIso_hom gᵥ gᵣ n
  have h := congrArg ((tateLocalCohomologyIso Aᵥ Aᵣ n).inv ≫ ·)
    (mappingCoconeNat.homologyδ_naturality (tateGlobalMap g gᵣ) (tateLocalMap gᵥ gᵣ)
      (tateCompactRes_naturality φ ψ g gᵥ gᵣ hg hgr) n)
  simp only [← Category.assoc] at h
  rw [h2, Category.assoc] at h
  exact h

end Functoriality

section CoefficientSequence

variable (S : ShortComplex (Rep.{u} k G)) [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] (Sᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))) [∀ v, IsDiscreteRep (Sᵥ v).X₁]
  [∀ v, IsDiscreteRep (Sᵥ v).X₂] [∀ v, IsDiscreteRep (Sᵥ v).X₃]
  (s : ∀ v, S.map (Rep.resFunctor (φ v).toMonoidHom) ⟶ Sᵥ v)
  (Sᵣ : ∀ w, ShortComplex (Rep.{u} k (F w))) [∀ w, IsDiscreteRep (Sᵣ w).X₁]
  [∀ w, IsDiscreteRep (Sᵣ w).X₂] [∀ w, IsDiscreteRep (Sᵣ w).X₃]
  (sr : ∀ w, S.map (Rep.resFunctor (ψ w).toMonoidHom) ⟶ Sᵣ w)

noncomputable abbrev tateGlobalShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  prodShortComplex (cochainsShortComplex S) (degZeroShortComplex (piRepShortComplex Sᵣ))

noncomputable abbrev tateLocalShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  prodShortComplex (piShortComplex fun v => cochainsShortComplex (Sᵥ v))
    (piShortComplex fun w => cochainsShortComplex (Sᵣ w))

noncomputable def tateResShortComplex : tateGlobalShortComplex S Sᵣ ⟶ tateLocalShortComplex Sᵥ Sᵣ where
  τ₁ := tateCompactRes φ ψ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁) (fun w => (Sᵣ w).X₁)
    (fun w => (sr w).τ₁)
  τ₂ := tateCompactRes φ ψ S.X₂ (fun v => (Sᵥ v).X₂) (fun v => (s v).τ₂) (fun w => (Sᵣ w).X₂)
    (fun w => (sr w).τ₂)
  τ₃ := tateCompactRes φ ψ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) (fun w => (Sᵣ w).X₃)
    (fun w => (sr w).τ₃)
  comm₁₂ := tateCompactRes_naturality φ ψ S.f (fun v => (Sᵥ v).f) (fun w => (Sᵣ w).f)
    (fun v => (s v).comm₁₂) (fun w => (sr w).comm₁₂)
  comm₂₃ := tateCompactRes_naturality φ ψ S.g (fun v => (Sᵥ v).g) (fun w => (Sᵣ w).g)
    (fun v => (s v).comm₂₃) (fun w => (sr w).comm₂₃)

noncomputable abbrev tateCompactCochainsMap₁₂ :=
  tateCompactCochainsMap φ ψ (A := S.X₁) (B := S.X₂) (Aᵥ := fun v => (Sᵥ v).X₁)
      (Bᵥ := fun v => (Sᵥ v).X₂) (a := fun v => (s v).τ₁) (b := fun v => (s v).τ₂)
      (Aᵣ := fun w => (Sᵣ w).X₁) (Bᵣ := fun w => (Sᵣ w).X₂) (ar := fun w => (sr w).τ₁)
      (br := fun w => (sr w).τ₂)
    S.f (fun v => (Sᵥ v).f) (fun w => (Sᵣ w).f) (fun v => (s v).comm₁₂) (fun w => (sr w).comm₁₂)

noncomputable abbrev tateCompactCochainsMap₂₃ :=
  tateCompactCochainsMap φ ψ (A := S.X₂) (B := S.X₃) (Aᵥ := fun v => (Sᵥ v).X₂)
      (Bᵥ := fun v => (Sᵥ v).X₃) (a := fun v => (s v).τ₂) (b := fun v => (s v).τ₃)
      (Aᵣ := fun w => (Sᵣ w).X₂) (Bᵣ := fun w => (Sᵣ w).X₃) (ar := fun w => (sr w).τ₂)
      (br := fun w => (sr w).τ₃)
    S.g (fun v => (Sᵥ v).g) (fun w => (Sᵣ w).g) (fun v => (s v).comm₂₃) (fun w => (sr w).comm₂₃)

noncomputable abbrev tateCompactCohomologyMap₁₂ (n : ℕ) :=
  tateCompactCohomologyMap φ ψ (A := S.X₁) (B := S.X₂) (Aᵥ := fun v => (Sᵥ v).X₁)
      (Bᵥ := fun v => (Sᵥ v).X₂) (a := fun v => (s v).τ₁) (b := fun v => (s v).τ₂)
      (Aᵣ := fun w => (Sᵣ w).X₁) (Bᵣ := fun w => (Sᵣ w).X₂) (ar := fun w => (sr w).τ₁)
      (br := fun w => (sr w).τ₂)
    S.f (fun v => (Sᵥ v).f) (fun w => (Sᵣ w).f) (fun v => (s v).comm₁₂) (fun w => (sr w).comm₁₂) n

noncomputable abbrev tateCompactCohomologyMap₂₃ (n : ℕ) :=
  tateCompactCohomologyMap φ ψ (A := S.X₂) (B := S.X₃) (Aᵥ := fun v => (Sᵥ v).X₂)
      (Bᵥ := fun v => (Sᵥ v).X₃) (a := fun v => (s v).τ₂) (b := fun v => (s v).τ₃)
      (Aᵣ := fun w => (Sᵣ w).X₂) (Bᵣ := fun w => (Sᵣ w).X₃) (ar := fun w => (sr w).τ₂)
      (br := fun w => (sr w).τ₃)
    S.g (fun v => (Sᵥ v).g) (fun w => (Sᵣ w).g) (fun v => (s v).comm₂₃) (fun w => (sr w).comm₂₃) n

theorem tateCompactCochainsMap₁₂_₂₃ :
    tateCompactCochainsMap₁₂ φ ψ S Sᵥ s Sᵣ sr ≫ tateCompactCochainsMap₂₃ φ ψ S Sᵥ s Sᵣ sr = 0 := by
  have hK := (tateGlobalShortComplex S Sᵣ).zero
  have hL := (tateLocalShortComplex Sᵥ Sᵣ).zero
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex S.X₁ fun w => (Sᵣ w).X₁).X n ×
    shiftNegOneX (tateLocalComplex (fun v => (Sᵥ v).X₁) fun w => (Sᵣ w).X₁) n) => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) hK) p.1
  · cases n with
    | zero => rfl
    | succ n => exact hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) hL) p.2

theorem tateCompactCohomologyMap_f_g (n : ℕ) :
    tateCompactCohomologyMap₁₂ φ ψ S Sᵥ s Sᵣ sr n ≫ tateCompactCohomologyMap₂₃ φ ψ S Sᵥ s Sᵣ sr n = 0 :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n)
      (tateCompactCochainsMap₁₂_₂₃ φ ψ S Sᵥ s Sᵣ sr)).trans
      (HomologicalComplex.homologyMap_zero _ _ n))

theorem mapShortComplex_tateResShortComplex_f :
    (mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ S Sᵥ s Sᵣ sr)).f =
      tateCompactCochainsMap₁₂ φ ψ S Sᵥ s Sᵣ sr := by
  ext n : 1
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem mapShortComplex_tateResShortComplex_g :
    (mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ S Sᵥ s Sᵣ sr)).g =
      tateCompactCochainsMap₂₃ φ ψ S Sᵥ s Sᵣ sr := by
  ext n : 1
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

variable {S Sᵥ Sᵣ}

theorem tateCompactCochains_shortExact (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact)
    (hSᵣ : ∀ w, (Sᵣ w).ShortExact) :
    (mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ S Sᵥ s Sᵣ sr)).ShortExact :=
  mappingCoconeNat.shortExact_mapShortComplex _
    (prodShortComplex_shortExact (cochainsShortComplex_shortExact hS)
      (degZeroShortComplex_shortExact (piRepShortComplex_shortExact hSᵣ)))
    (prodShortComplex_shortExact
      (piShortComplex_shortExact fun v => cochainsShortComplex_shortExact (hSᵥ v))
      (piShortComplex_shortExact fun w => cochainsShortComplex_shortExact (hSᵣ w)))

noncomputable def tateCompactδ (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact)
    (hSᵣ : ∀ w, (Sᵣ w).ShortExact) (n : ℕ) :
    tateCompactCohomology φ ψ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) (fun w => (Sᵣ w).X₃)
        (fun w => (sr w).τ₃) n ⟶
      tateCompactCohomology φ ψ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁)
        (fun w => (Sᵣ w).X₁) (fun w => (sr w).τ₁) (n + 1) :=
  (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).δ n (n + 1) rfl

variable (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact) (hSᵣ : ∀ w, (Sᵣ w).ShortExact)

theorem tateCompactCohomologyMap₂₃_tateCompactδ (n : ℕ) :
    tateCompactCohomologyMap₂₃ φ ψ S Sᵥ s Sᵣ sr n ≫ tateCompactδ φ ψ s sr hS hSᵥ hSᵣ n = 0 := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).comp_δ n (n + 1) rfl
  rw [mapShortComplex_tateResShortComplex_g] at h
  exact h

theorem tateCompactδ_tateCompactCohomologyMap₁₂ (n : ℕ) :
    tateCompactδ φ ψ s sr hS hSᵥ hSᵣ n ≫ tateCompactCohomologyMap₁₂ φ ψ S Sᵥ s Sᵣ sr (n + 1) = 0 := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).δ_comp n (n + 1) rfl
  rw [mapShortComplex_tateResShortComplex_f] at h
  exact h

include hS hSᵥ hSᵣ in

theorem tateCompactCohomology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (tateCompactCohomologyMap_f_g φ ψ S Sᵥ s Sᵣ sr n)).Exact := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).homology_exact₂ n
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((congrArg (HomologicalComplex.homologyMap · _)
      (mapShortComplex_tateResShortComplex_f φ ψ S Sᵥ s Sᵣ sr)).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((congrArg (HomologicalComplex.homologyMap · _)
      (mapShortComplex_tateResShortComplex_g φ ψ S Sᵥ s Sᵣ sr)).symm.trans (Category.comp_id _).symm))

theorem tateCompactCohomology_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (tateCompactCohomologyMap₂₃_tateCompactδ φ ψ s sr hS hSᵥ hSᵣ n)).Exact := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).homology_exact₃ n (n + 1) rfl
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((congrArg (HomologicalComplex.homologyMap · _)
      (mapShortComplex_tateResShortComplex_g φ ψ S Sᵥ s Sᵣ sr)).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem tateCompactCohomology_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (tateCompactδ_tateCompactCohomologyMap₁₂ φ ψ s sr hS hSᵥ hSᵣ n)).Exact := by
  have h := (tateCompactCochains_shortExact φ ψ s sr hS hSᵥ hSᵣ).homology_exact₁ n (n + 1) rfl
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans ((congrArg (HomologicalComplex.homologyMap · _)
      (mapShortComplex_tateResShortComplex_f φ ψ S Sᵥ s Sᵣ sr)).symm.trans (Category.comp_id _).symm))

end CoefficientSequence

end Tate

end GroundTheory.ProfCoh
