import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe w w' u

section Transport

variable {Y X : TopCat.{u}} {κ : Type w} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
  {P' : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}}

lemma cechAcyclic_of_transport (φ : Opens Y → Opens X) (hφ : Monotone φ)
    (e : ∀ W, P'.obj (op W) ≃+ P.obj (op (φ W)))
    (he : ∀ {V W : Opens Y} (h : V ≤ W) (x : P'.obj (op W)),
      e V (res P' h x) = res P (hφ h) (e W x))
    (U : κ → Opens Y) (hinter : ∀ {n : ℕ} (i : Fin (n + 1) → κ), φ (inter U i) = inter (φ ∘ U) i)
    (hU : CechAcyclic P' U) : CechAcyclic P (φ ∘ U) := by
  let E : ∀ n, Cochain P' U n → Cochain P (φ ∘ U) n := fun n σ i =>
    res P (hinter i).ge (e _ (σ i))
  let E' : ∀ n, Cochain P (φ ∘ U) n → Cochain P' U n := fun n σ i =>
    (e _).symm (res P (hinter i).le (σ i))
  have hEE' : ∀ n σ, E n (E' n σ) = σ := fun n σ => funext fun i => by
    simp only [E, E', AddEquiv.apply_symm_apply, res_res, res_refl]
  have hE'E : ∀ n σ, E' n (E n σ) = σ := fun n σ => funext fun i => by
    simp only [E, E', res_res, res_refl, AddEquiv.symm_apply_apply]
  have hE'0 : ∀ n, E' n 0 = 0 := fun n => funext fun i => by
    simp only [E', Pi.zero_apply, map_zero]
  have hEd : ∀ n σ, E (n + 1) (d P' U n σ) = d P (φ ∘ U) n (E n σ) := fun n σ => funext fun i => by
    simp only [E, d_apply, map_sum, map_zsmul, he, res_res]
  intro n σ hσ
  have hσ' : d P' U (n + 1) (E' (n + 1) σ) = 0 := by
    rw [← hE'E (n + 2) (d P' U (n + 1) _), hEd, hEE', hσ, hE'0]
  obtain ⟨τ, hτ⟩ := hU n _ hσ'
  exact ⟨E n τ, by rw [← hEd, hτ, hEE']⟩

end Transport

section Scheme

variable {X : Scheme.{u}}

noncomputable abbrev modulesAb (F : X.Modules) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj F

def IsBasicCover (V : X.Opens) {κ : Type u} (U : κ → X.Opens) : Prop :=
  IsAffineOpen V ∧ ∃ h : κ → Γ(X, V), (∀ a, U a = X.basicOpen (h a)) ∧ iSup U = V

lemma inter_basicOpen {V : X.Opens} {κ : Type u} (h : κ → Γ(X, V)) :
    ∀ {n : ℕ} (i : Fin (n + 1) → κ),
      inter (X := X.toTopCat) (fun a => X.basicOpen (h a)) i = X.basicOpen (∏ a, h (i a))
  | 0, i => by
    rw [Fin.prod_univ_one]
    apply le_antisymm (inter_le _ i 0)
    intro x hx
    rw [mem_inter_iff]
    intro a
    rwa [Fin.fin_one_eq_zero a]
  | n + 1, i => by
    rw [inter_succ, inter_basicOpen h (i ∘ Fin.succ), Fin.prod_univ_succ (fun a => h (i a)),
      Scheme.basicOpen_mul]
    rfl

lemma isCoverSystem_isBasicCover :
    IsCoverSystem (X := X.toTopCat) IsAffineOpen (fun {κ} V U => IsBasicCover (κ := κ) V U) where
  iSup_eq V κ U hU := hU.2.choose_spec.2
  inter_mem V κ U hU n i := by
    obtain ⟨hV, h, hUh, -⟩ := hU
    have : U = fun a => X.basicOpen (h a) := funext hUh
    subst this
    rw [inter_basicOpen h i]
    exact hV.basicOpen _
  exists_refinement V hV O hO := by
    choose f hfO hxf using fun x : V => hV.exists_basicOpen_le (V := O x) ⟨x.1, hO x⟩ x.2
    obtain ⟨fs, hfs⟩ := hV.isCompact.elim_finite_subcover
      (fun x : V => (X.basicOpen (f x) : Set X)) (fun x => (X.basicOpen (f x)).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxf _⟩)
    refine ⟨{x // x ∈ fs}, inferInstance, fun a => X.basicOpen (f a.1),
      ⟨hV, fun a => f a.1, fun a => rfl, ?_⟩, fun a => ⟨a.1, hfO a.1⟩⟩
    refine le_antisymm (iSup_le fun a => X.basicOpen_le _) ?_
    intro y hy
    have := hfs hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyx⟩

lemma image_inter {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] {κ : Type w}
    (U : κ → Y.Opens) {n : ℕ} (i : Fin (n + 1) → κ) :
    g ''ᵁ inter (X := Y.toTopCat) U i = inter (X := X.toTopCat) (fun a => g ''ᵁ U a) i := by
  have key : ∀ (W : Y.Opens) (x : X), x ∈ g ''ᵁ W ↔ ∃ y ∈ W, g y = x := fun W x => by
    rw [← SetLike.mem_coe, Scheme.Hom.coe_image]
    rfl
  refine SetLike.ext fun x => ?_
  rw [mem_inter_iff, key]
  constructor
  · rintro ⟨y, hy, rfl⟩ a
    exact (key _ _).2 ⟨y, (mem_inter_iff U i y).1 hy a, rfl⟩
  · intro hx
    choose y hy hyx using fun a => (key _ x).1 (hx a)
    refine ⟨y 0, (mem_inter_iff U i (y 0)).2 fun a => ?_, hyx 0⟩
    have : y a = y 0 := g.isOpenEmbedding.injective ((hyx a).trans (hyx 0).symm)
    rw [← this]
    exact hy a

theorem cechAcyclic_of_isBasicCover (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    {κ : Type u} [Finite κ] {U : κ → X.Opens} (hU : IsBasicCover V U) :
    CechAcyclic (modulesAb F).obj U := by
  obtain ⟨hV, h, hUh, hsup⟩ := hU
  have hUeq : U = fun a => X.basicOpen (h a) := funext hUh
  subst hUeq
  let F' : (Spec Γ(X, V)).Modules := F.restrict hV.fromSpec
  let M := (modulesSpecToSheaf.obj F').presheaf.obj (op ⊤)
  let U' : κ → Opens (Spec Γ(X, V)).toTopCat := fun a => PrimeSpectrum.basicOpen (h a)
  have hsup' : iSup U' = ⊤ := by
    have h1 : hV.fromSpec ⁻¹ᵁ (⨆ a, X.basicOpen (h a)) = ⊤ := by
      rw [hsup]
      exact hV.fromSpec_preimage_self
    rw [Scheme.Hom.preimage_iSup] at h1
    simpa only [hV.fromSpec_preimage_basicOpen] using h1
  have hM : CechAcyclic (tildeAb M).obj U' :=
    cechCondition_tilde M ⊤ ⟨1, PrimeSpectrum.basicOpen_one.symm⟩ κ U' (fun a => ⟨h a, rfl⟩)
      hsup'
  have : F'.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor hV.fromSpec F
  have hiso : IsIso F'.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F'
  let e : tildeAb M ≅ modulesAb F' :=
    (SheafOfModules.toSheaf _).mapIso (@asIso _ _ _ _ F'.fromTildeΓ hiso)
  have hF' : CechAcyclic (modulesAb F').obj U' :=
    CechAcyclic.of_retract U' e.inv.hom e.hom.hom (congrArg (fun f => f.hom) e.inv_hom_id) hM
  have key := cechAcyclic_of_transport (P := (modulesAb F).obj) (P' := (modulesAb F').obj)
    (fun W => hV.fromSpec ''ᵁ W) (fun _ _ hle => hV.fromSpec.image_mono hle)
    (fun W => AddEquiv.refl _) (fun _ _ => rfl) U' (fun i => image_inter hV.fromSpec U' i) hF'
  convert key using 1
  funext a
  exact (hV.fromSpec_image_basicOpen (h a)).symm

lemma goodAcyclic_modulesAb (F : X.Modules) [F.IsQuasicoherent] :
    GoodAcyclic (X := X.toTopCat) IsAffineOpen (fun {κ} V U => IsBasicCover (κ := κ) V U)
      (modulesAb F) :=
  fun _ _ _ _ _ hU => cechAcyclic_of_isBasicCover F hU

lemma inter_eq_iInf {ι : Type w} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    inter (X := X.toTopCat) U i = ⨅ a, U (i a) :=
  SetLike.ext fun x => by
    rw [mem_inter_iff, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    rfl

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

theorem nonempty_cechH_equiv_H (F : X.Modules) [F.IsQuasicoherent] {ι : Type w}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (n : ℕ) :
    Nonempty (cechH (modulesAb F).obj U n ≃+ Sheaf.H.{w'} (modulesAb F) n) :=
  nonempty_cechH_equiv isCoverSystem_isBasicCover U hU
    (fun i => by rw [inter_eq_iInf]; exact hUaff _ i) n (modulesAb F) (goodAcyclic_modulesAb F)

end Scheme

end GroundTheory.Arith.SchemeCoh
