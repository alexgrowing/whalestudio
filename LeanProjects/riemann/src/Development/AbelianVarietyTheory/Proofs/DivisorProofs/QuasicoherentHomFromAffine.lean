import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

namespace GlobalTheory.Glue

variable {T : Scheme.{0}} {F G : T.Modules}

theorem le_iSup_affine (U : T.Opens) :
    U ≤ ⨆ k : {W : T.Opens // IsAffineOpen W ∧ W ≤ U}, k.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hx
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hxW⟩

variable (j : ∀ V : T.Opens, IsAffineOpen V → Γ(F, V) →ₗ[Γ(T, V)] Γ(G, V))
  (hj : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s : Γ(F, V)), j V' hV' (GlobalTheory.Twist.resM F h s) = GlobalTheory.Twist.resM G h (j V hV s))

include hj in

theorem agree {U W W' V : T.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWU : W ≤ U)
    (hW'U : W' ≤ U) (h₁ : V ≤ W) (h₂ : V ≤ W') (s : Γ(F, U)) :
    GlobalTheory.Twist.resM G h₁ (j W hW (GlobalTheory.Twist.resM F hWU s)) =
      GlobalTheory.Twist.resM G h₂ (j W' hW' (GlobalTheory.Twist.resM F hW'U s)) := by
  refine GlobalTheory.Twist.sec_ext_of_cover (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ V} => k.1)
    (fun k => k.2.2) (le_iSup_affine V) fun k => ?_
  rw [GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM, ← hj _ _ hW k.2.1, ← hj _ _ hW' k.2.1,
    GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM]

include hj in
theorem exists_glue (U : T.Opens) (s : Γ(F, U)) :
    ∃ t : Γ(G, U), ∀ (W : T.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U),
      GlobalTheory.Twist.resM G hWU t = j W hW (GlobalTheory.Twist.resM F hWU s) := by
  obtain ⟨t, ht⟩ := GlobalTheory.Twist.exists_sec_of_cover
    (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ U} => k.1) (fun k => k.2.2) (le_iSup_affine U)
    (fun k => j k.1 k.2.1 (GlobalTheory.Twist.resM F k.2.2 s))
    fun k l => agree j hj k.2.1 l.2.1 k.2.2 l.2.2 _ _ s
  exact ⟨t, fun W hW hWU => ht ⟨W, hW, hWU⟩⟩

def glue (U : T.Opens) (s : Γ(F, U)) : Γ(G, U) := Classical.choose (exists_glue j hj U s)

theorem glue_spec (U : T.Opens) (s : Γ(F, U)) (W : T.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U) :
    GlobalTheory.Twist.resM G hWU (glue j hj U s) = j W hW (GlobalTheory.Twist.resM F hWU s) :=
  Classical.choose_spec (exists_glue j hj U s) W hW hWU

theorem ext_affine {U : T.Opens} {t t' : Γ(G, U)}
    (h : ∀ (W : T.Opens) (_ : IsAffineOpen W) (hWU : W ≤ U),
      GlobalTheory.Twist.resM G hWU t = GlobalTheory.Twist.resM G hWU t') : t = t' :=
  GlobalTheory.Twist.sec_ext_of_cover (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ U} => k.1)
    (fun k => k.2.2) (le_iSup_affine U) fun k => h k.1 k.2.1 k.2.2

def glueLinear (U : T.Opens) : Γ(F, U) →ₗ[Γ(T, U)] Γ(G, U) where
  toFun := glue j hj U
  map_add' s s' := ext_affine fun W hW hWU => by
    rw [map_add, glue_spec j hj _ _ W hW, glue_spec j hj _ _ W hW, glue_spec j hj _ _ W hW, map_add,
      map_add]
  map_smul' a s := ext_affine fun W hW hWU => by
    rw [RingHom.id_apply, GlobalTheory.Twist.resM_smul, glue_spec j hj _ _ W hW, glue_spec j hj _ _ W hW,
      GlobalTheory.Twist.resM_smul, map_smul]

theorem glueLinear_res {U V : T.Opens} (h : V ≤ U) (s : Γ(F, U)) :
    glueLinear j hj V (GlobalTheory.Twist.resM F h s) = GlobalTheory.Twist.resM G h (glueLinear j hj U s) :=
  ext_affine fun W hW hWV => by
    change GlobalTheory.Twist.resM G hWV (glue j hj V _) = GlobalTheory.Twist.resM G hWV
      (GlobalTheory.Twist.resM G h (glue j hj U s))
    rw [glue_spec j hj V _ W hW hWV, GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM,
      glue_spec j hj U s W hW]

include hj in

theorem exists_hom_of_affine :
    ∃ i : F ⟶ G, ∀ (V : T.Opens) (hV : IsAffineOpen V), GlobalTheory.QCoh.appLinear i V = j V hV := by
  refine ⟨GlobalTheory.LB.homOfLinear (glueLinear j hj) fun h s => glueLinear_res j hj h s, fun V hV => ?_⟩
  ext s
  rw [GlobalTheory.QCoh.appLinear_apply, GlobalTheory.LB.homOfLinear_app]
  change glue j hj V s = j V hV s
  exact ext_affine fun W hW hWV => by rw [glue_spec j hj V s W hW hWV, hj V W hV hW hWV]

end GlobalTheory.Glue

theorem GlobalTheory.hom_of_affine_compatible : ∀ (T : Scheme.{0}) (F G : T.Modules)
    (j : ∀ V : T.Opens, IsAffineOpen V → Γ(F, V) →ₗ[Γ(T, V)] Γ(G, V)),
    (∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) (s : Γ(F, V)),
      j V' hV' (GlobalTheory.Twist.resM F h s) = GlobalTheory.Twist.resM G h (j V hV s)) →
    ∃ i : F ⟶ G, ∀ (V : T.Opens) (hV : IsAffineOpen V), GlobalTheory.QCoh.appLinear i V = j V hV :=
  fun _ _ _ j hj => GlobalTheory.Glue.exists_hom_of_affine j hj
