import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericGerm
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsHeightOneSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace BundlesAgree

variable {X : Scheme.{0}} [IsIntegral X]

lemma section_eq_zero (E : X.Modules) {U : X.Opens} (hU : genericPoint X ∉ U) (s : Γ(E, U)) :
    s = 0 := by
  have hU' : U = ⊥ := by
    by_contra h
    obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty U).mp h
    exact hU (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩)
  have ht := TopCat.Sheaf.isTerminalOfEqEmpty ⟨E.presheaf, E.isSheaf⟩ hU'
  have h0 : (𝟙 (E.presheaf.obj (op U))) = 0 := ht.hom_ext _ _
  simpa using ConcreteCategory.congr_hom h0 s

lemma section_ext (E : X.Modules)
    (hE : ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E.presheaf.germ U (genericPoint X) hU))
    {U : X.Opens} {a b : Γ(E, U)}
    (h : ∀ hU : genericPoint X ∈ U,
      E.presheaf.germ U (genericPoint X) hU a = E.presheaf.germ U (genericPoint X) hU b) :
    a = b := by
  by_cases hU : genericPoint X ∈ U
  · exact hE U hU (h hU)
  · rw [section_eq_zero E hU a, section_eq_zero E hU b]

omit [IsIntegral X] in

lemma germ_smul' (E : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U) (r : Γ(X, U)) (s : Γ(E, U)) :
    E.presheaf.germ U x hx (r • s) = X.presheaf.germ U x hx r • E.presheaf.germ U x hx s :=
  PresheafOfModules.germ_smul (R := X.presheaf) (M := E.val) x U hx r s

def lift (E E' : X.Modules)
    (φ : E.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X))
    (hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
      E'.presheaf.germ U (genericPoint X) hU t = φ (E.presheaf.germ U (genericPoint X) hU s))
    (U : X.Opens) (s : Γ(E, U)) : Γ(E', U) :=
  haveI := Classical.dec (genericPoint X ∈ U)
  if hU : genericPoint X ∈ U then (hex U hU s).choose else 0

variable (E E' : X.Modules)
  (φ : E.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
    E'.presheaf.stalk (genericPoint X))
  (hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
    E'.presheaf.germ U (genericPoint X) hU t = φ (E.presheaf.germ U (genericPoint X) hU s))
  (hE' : ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E'.presheaf.germ U (genericPoint X) hU))

lemma germ_lift (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U (genericPoint X) hU (lift E E' φ hex U s) =
      φ (E.presheaf.germ U (genericPoint X) hU s) := by
  rw [lift, dif_pos hU]
  exact (hex U hU s).choose_spec

include hE' in
lemma lift_add (U : X.Opens) (a b : Γ(E, U)) :
    lift E E' φ hex U (a + b) = lift E E' φ hex U a + lift E E' φ hex U b :=
  section_ext E' hE' fun hU => by
    rw [map_add, germ_lift, germ_lift, germ_lift, map_add, map_add]

include hE' in
lemma lift_zero (U : X.Opens) : lift E E' φ hex U 0 = 0 :=
  section_ext E' hE' fun hU => by
    rw [germ_lift, map_zero, map_zero, map_zero]

include hE' in
lemma lift_smul (U : X.Opens) (r : Γ(X, U)) (s : Γ(E, U)) :
    lift E E' φ hex U (r • s) = r • lift E E' φ hex U s :=
  section_ext E' hE' fun hU => by
    rw [germ_lift, germ_smul', germ_smul', map_smul, germ_lift]

include hE' in
lemma lift_res {U V : X.Opens} (i : V ⟶ U) (s : Γ(E, U)) :
    lift E E' φ hex V (E.presheaf.map i.op s) = E'.presheaf.map i.op (lift E E' φ hex U s) :=
  section_ext E' hE' fun hV => by
    rw [germ_lift, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, germ_lift]

include hE' in

def homOfGeneric : E ⟶ E' :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := lift E E' φ hex U.unop
          map_zero' := lift_zero E E' φ hex hE' U.unop
          map_add' := lift_add E E' φ hex hE' U.unop }
      naturality := fun U V i => by
        ext s
        exact lift_res E E' φ hex hE' i.unop s }
    (fun U r s => lift_smul E E' φ hex hE' U.unop r s)

include hE' in
lemma germ_homOfGeneric_app (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U (genericPoint X) hU ((homOfGeneric E E' φ hex hE').app U s) =
      φ (E.presheaf.germ U (genericPoint X) hU s) :=
  germ_lift E E' φ hex U hU s

include hE' in

lemma hom_ext_of_germ {f g : E ⟶ E'}
    (h : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      E'.presheaf.germ U (genericPoint X) hU (f.app U s) =
        E'.presheaf.germ U (genericPoint X) hU (g.app U s)) : f = g :=
  Scheme.Modules.hom_ext f g fun U => by
    ext s
    exact section_ext E' hE' fun hU => h U hU s

omit [IsIntegral X] in

lemma germ_app_eq_stalk (f : E ⟶ E') (U : X.Opens) (x : X) (hU : x ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U x hU (f.app U s) =
      ((TopCat.Presheaf.stalkFunctor Ab x).map (Scheme.Modules.Hom.mapPresheaf f)).hom
        (E.presheaf.germ U x hU s) := by
  have := TopCat.Presheaf.stalkFunctor_map_germ_apply (F := E.presheaf) (G := E'.presheaf) U x hU
    (Scheme.Modules.Hom.mapPresheaf f) s
  exact this.symm

end BundlesAgree

open BundlesAgree in

theorem BundlesAgree.proof (h₁ : GenericGermInjective.Statement)
    (h₂ : HeightOneSections.Statement) : BundlesAgree.Statement := by
  intro X _ _ hN E E' hE hE' φ hφ
  have inj := h₁ X E hE
  have inj' := h₁ X E' hE'
  have mem : ∀ (F : X.Modules) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(F, U)) (x : X)
      (hx : x ∈ U), F.presheaf.germ U (genericPoint X) hU s ∈ genericImage F x :=
    fun F U hU s x hx => ⟨F.presheaf.germ U x hx s,
      TopCat.Presheaf.germ_stalkSpecializes_apply F.presheaf hx (genericPoint_specializes x) s⟩
  have hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
      E'.presheaf.germ U (genericPoint X) hU t = φ.toLinearMap (E.presheaf.germ U _ hU s) :=
    fun U hU s => h₂ X hN E' hE' U hU _ fun x hx hx1 => by
      rw [← hφ x hx1]
      exact AddSubgroup.mem_map.mpr ⟨_, mem E U hU s x hx, rfl⟩
  have hex' : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E', U)), ∃ t : Γ(E, U),
      E.presheaf.germ U (genericPoint X) hU t = φ.symm.toLinearMap (E'.presheaf.germ U _ hU s) :=
    fun U hU s => h₂ X hN E hE U hU _ fun x hx hx1 => by
      have h := mem E' U hU s x hx
      rw [← hφ x hx1] at h
      obtain ⟨a, ha, he⟩ := AddSubgroup.mem_map.mp h
      have : φ.symm (E'.presheaf.germ U (genericPoint X) hU s) = a := by
        rw [← he]
        exact φ.symm_apply_apply a
      exact this ▸ ha
  let f := homOfGeneric E E' φ.toLinearMap hex inj'
  let g := homOfGeneric E' E φ.symm.toLinearMap hex' inj
  have hf := germ_homOfGeneric_app E E' φ.toLinearMap hex inj'
  have hg := germ_homOfGeneric_app E' E φ.symm.toLinearMap hex' inj
  refine ⟨⟨f, g, ?_, ?_⟩, ?_, ?_⟩
  · refine hom_ext_of_germ E E inj fun U hU s => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply, hg,
      hf]
    simp
  · refine hom_ext_of_germ E' E' inj' fun U hU s => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply, hf,
      hg]
    simp
  · intro v
    obtain ⟨U, hU, s, rfl⟩ := E.presheaf.exists_germ_eq v
    rw [← germ_app_eq_stalk]
    exact hf U hU s
  · intro ψ hψ
    refine Iso.ext (hom_ext_of_germ E E' inj' fun U hU s => ?_)
    rw [germ_app_eq_stalk]
    exact (hψ _).trans (hf U hU s).symm

end

end GroundTheory.Heights₂.Heights.Model
