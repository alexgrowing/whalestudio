import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul sec_ext_of_cover exists_sec_of_cover)

namespace GlobalTheory.CoverHom

variable {X : Scheme.{0}} {F G : X.Modules}

section Basis

variable {P : X.Opens → Prop} (hP : ∀ U : X.Opens, U ≤ ⨆ k : {W : X.Opens // P W ∧ W ≤ U}, k.1)
  (j : ∀ W : X.Opens, P W → Γ(F, W) →ₗ[Γ(X, W)] Γ(G, W))
  (hj : ∀ (W W' : X.Opens) (hW : P W) (hW' : P W') (h : W' ≤ W) (s : Γ(F, W)),
    j W' hW' (resM F h s) = resM G h (j W hW s))

include hP in

theorem ext_basis {U : X.Opens} {t t' : Γ(G, U)}
    (h : ∀ (W : X.Opens) (_ : P W) (hWU : W ≤ U), resM G hWU t = resM G hWU t') : t = t' :=
  sec_ext_of_cover (fun k : {Z : X.Opens // P Z ∧ Z ≤ U} => k.1) (fun k => k.2.2) (hP U)
    fun k => h k.1 k.2.1 k.2.2

include hP hj in

theorem exists_glue (U : X.Opens) (s : Γ(F, U)) :
    ∃ t : Γ(G, U), ∀ (W : X.Opens) (hW : P W) (hWU : W ≤ U), resM G hWU t = j W hW (resM F hWU s) := by
  obtain ⟨t, ht⟩ := exists_sec_of_cover (fun k : {Z : X.Opens // P Z ∧ Z ≤ U} => k.1) (fun k => k.2.2) (hP U)
    (fun k => j k.1 k.2.1 (resM F k.2.2 s)) fun k l => ext_basis hP fun Z hZ hZU => by
      rw [resM_resM, resM_resM, ← hj _ _ k.2.1 hZ, ← hj _ _ l.2.1 hZ, resM_resM, resM_resM]
  exact ⟨t, fun W hW hWU => ht ⟨W, hW, hWU⟩⟩

include hP hj in

theorem exists_hom_of_basis : ∃ u : F ⟶ G, ∀ (W : X.Opens) (hW : P W) (s : Γ(F, W)), u.app W s = j W hW s := by
  choose g hg using exists_glue hP j hj
  let l : ∀ U : X.Opens, Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) := fun U =>
    { toFun := g U
      map_add' := fun s s' => ext_basis hP fun W hW hWU => by
        rw [map_add, hg _ _ W hW, hg _ _ W hW, hg _ _ W hW, map_add, map_add]
      map_smul' := fun a s => ext_basis hP fun W hW hWU => by
        rw [RingHom.id_apply, resM_smul, hg _ _ W hW, hg _ _ W hW, resM_smul, map_smul] }
  have hl : ∀ {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)), l V (resM F h s) = resM G h (l U s) :=
    fun {U V} h s => ext_basis hP fun W hW hWV => by
      change resM G hWV (g V _) = resM G hWV (resM G h (g U s))
      rw [hg V _ W hW hWV, resM_resM, resM_resM, hg U s W hW]
  refine ⟨GlobalTheory.LB.homOfLinear l fun h s => hl h s, fun V hV s => ?_⟩
  rw [GlobalTheory.LB.homOfLinear_app]
  change g V s = j V hV s
  exact ext_basis hP fun W hW hWV => by rw [hg V s W hW hWV, hj V W hV hW hWV]

end Basis

section Lift

variable [F.IsQuasicoherent] {U W W' : X.Opens}

theorem induction_res (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) (p : Γ(F, W) → Prop)
    (h₁ : ∀ s, p (resM F h s)) (h₂ : ∀ (a : Γ(X, W)) s, p s → p (a • s)) (h₃ : ∀ s t, p s → p t → p (s + t))
    (s : Γ(F, W)) : p s := by
  letI := GlobalTheory.QCoh.resAlgebra h
  letI := GlobalTheory.QCoh.resModule F h
  haveI := GlobalTheory.QCoh.res_isScalarTower F h
  refine (GlobalTheory.QCoh.isBaseChange_resLinear F hU hW h).inductionOn s p ?_ h₁ h₂ h₃
  simpa using h₁ 0

theorem exists_lift (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) (φ : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U)) :
    ∃ l : Γ(F, W) →ₗ[Γ(X, W)] Γ(G, W), ∀ s, l (resM F h s) = resM G h (φ s) := by
  letI := GlobalTheory.QCoh.resAlgebra h
  letI := GlobalTheory.QCoh.resModule F h
  haveI := GlobalTheory.QCoh.res_isScalarTower F h
  letI := GlobalTheory.QCoh.resModule G h
  haveI := GlobalTheory.QCoh.res_isScalarTower G h
  exact ⟨(GlobalTheory.QCoh.isBaseChange_resLinear F hU hW h).lift (GlobalTheory.QCoh.resLinear G h ∘ₗ φ),
    fun s => (GlobalTheory.QCoh.isBaseChange_resLinear F hU hW h).lift_eq _ s⟩

theorem lift_res (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) (h' : W' ≤ W)
    {φ : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U)} {l : Γ(F, W) →ₗ[Γ(X, W)] Γ(G, W)} {l' : Γ(F, W') →ₗ[Γ(X, W')] Γ(G, W')}
    (hl : ∀ s, l (resM F h s) = resM G h (φ s))
    (hl' : ∀ s, l' (resM F (h'.trans h) s) = resM G (h'.trans h) (φ s)) (s : Γ(F, W)) :
    l' (resM F h' s) = resM G h' (l s) := by
  refine induction_res hU hW h (fun s => l' (resM F h' s) = resM G h' (l s)) (fun s => ?_) (fun a s e => ?_)
    (fun s t e e' => ?_) s
  · rw [resM_resM, hl, hl', resM_resM]
  · rw [resM_smul, map_smul, map_smul, resM_smul, e]
  · rw [map_add, map_add, map_add, map_add, e, e']

end Lift

theorem exists_hom_of_cover [F.IsQuasicoherent] {ι : Type} (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hc : iSup V = ⊤) (hVV : ∀ i k, IsAffineOpen (V i ⊓ V k)) (φ : ∀ i, Γ(F, V i) →ₗ[Γ(X, V i)] Γ(G, V i))
    (hφ : ∀ i k, ∃ ψ : Γ(F, V i ⊓ V k) →ₗ[Γ(X, V i ⊓ V k)] Γ(G, V i ⊓ V k),
      (∀ s, ψ (resM F inf_le_left s) = resM G inf_le_left (φ i s)) ∧
        ∀ s, ψ (resM F inf_le_right s) = resM G inf_le_right (φ k s)) :
    ∃ u : F ⟶ G, ∀ i s, u.app (V i) s = φ i s := by
  let P : X.Opens → Prop := fun W => IsAffineOpen W ∧ ∃ i, W ≤ V i
  have hP : ∀ U : X.Opens, U ≤ ⨆ k : {W : X.Opens // P W ∧ W ≤ U}, k.1 := fun U x hx => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ x))
    obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ U ⊓ V i from ⟨hx, hi⟩)
    exact Opens.mem_iSup.2 ⟨⟨W, ⟨hW, i, hWU.trans inf_le_right⟩, hWU.trans inf_le_left⟩, hxW⟩
  have key : ∀ W : X.Opens, P W → ∃ l : Γ(F, W) →ₗ[Γ(X, W)] Γ(G, W),
      ∀ (k : ι) (h : W ≤ V k) (s : Γ(F, V k)), l (resM F h s) = resM G h (φ k s) := by
    rintro W ⟨hW, i, hi⟩
    obtain ⟨l, hl⟩ := exists_lift (hV i) hW hi (φ i)
    refine ⟨l, fun k h s => ?_⟩
    obtain ⟨ψ, h₁, h₂⟩ := hφ i k
    have e := lift_res (hV i) (hVV i k) inf_le_left (le_inf hi h) h₁ hl (resM F inf_le_right s)
    rwa [h₂, resM_resM, resM_resM] at e
  choose j hj using key
  obtain ⟨u, hu⟩ := exists_hom_of_basis hP j fun W W' hW hW' h s => by
    obtain ⟨i, hi⟩ := hW.2
    exact lift_res (hV i) hW.1 hi h (hj W hW i hi) (hj W' hW' i _) s
  refine ⟨u, fun i s => ?_⟩
  have e := hj (V i) ⟨hV i, i, le_rfl⟩ i le_rfl s
  rw [resM_self, resM_self] at e
  rw [hu _ ⟨hV i, i, le_rfl⟩, e]

theorem hom_on_affineCover : ∀ (X : Scheme.{0}) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (ι : Type) (V : ι → X.Opens), (∀ i, IsAffineOpen (V i)) → iSup V = ⊤ → ((∀ i j, IsAffineOpen (V i ⊓ V j)) → ∀ φ : ∀ i, Γ(F, V i) →ₗ[Γ(X, V i)] Γ(G, V i), (∀ i j, ∃ ψ : Γ(F, V i ⊓ V j) →ₗ[Γ(X, V i ⊓ V j)] Γ(G, V i ⊓ V j), (∀ s, ψ (resM F inf_le_left s) = resM G inf_le_left (φ i s)) ∧ ∀ s, ψ (resM F inf_le_right s) = resM G inf_le_right (φ j s)) → ∃ u : F ⟶ G, ∀ i s, u.app (V i) s = φ i s) ∧ (∀ u v : F ⟶ G, (∀ i s, u.app (V i) s = v.app (V i) s) → u = v) ∧ (∀ u : F ⟶ G, (∀ i, Function.Surjective (u.app (V i))) → Epi u) ∧ (∀ u : F ⟶ G, (∀ i, Function.Injective (u.app (V i))) → Mono u) ∧ (∀ u : F ⟶ G, (∀ i, Function.Bijective (u.app (V i))) → IsIso u) ∧ ∀ u : F ⟶ G, (cokernel u).IsQuasicoherent ∧ ∀ W : X.Opens, IsAffineOpen W → Function.Surjective ((cokernel.π u).app W) ∧ ∀ t, (cokernel.π u).app W t = 0 ↔ ∃ s, u.app W s = t := by
  intro X F G _ _ ι V hV hc
  have hcov : IsOpenCover V := hc
  refine ⟨fun hVV φ hφ => exists_hom_of_cover V hV hc hVV φ hφ, fun u v h => ?_,
    fun u h => (GlobalTheory.QCoh.epi_iff_affineCover V hcov hV u).2 h, fun u h => (GlobalTheory.QCoh.mono_iff_affineCover V hcov hV u).2 h,
    fun u h => (GlobalTheory.QCoh.isIso_iff_affineCover V hcov hV u).2 h, fun u => ⟨inferInstance, fun W hW =>
      ⟨GlobalTheory.QCoh.surjective_cokernel_π_app u hW, fun t => GlobalTheory.QCoh.exact_cokernel_π_app u hW t⟩⟩⟩
  refine sub_eq_zero.1 ((GlobalTheory.QCoh.hom_eq_zero_iff_affineCover V hcov hV (u - v)).2 fun i s => ?_)
  have e : (u - v).app (V i) s + v.app (V i) s = u.app (V i) s := by
    change GlobalTheory.QCoh.appLinear (u - v) (V i) s + GlobalTheory.QCoh.appLinear v (V i) s = GlobalTheory.QCoh.appLinear u (V i) s
    rw [← LinearMap.add_apply, ← GlobalTheory.QCoh.appLinear_add, sub_add_cancel]
  rw [h i s] at e
  exact add_eq_right.1 e

end GlobalTheory.CoverHom

end
