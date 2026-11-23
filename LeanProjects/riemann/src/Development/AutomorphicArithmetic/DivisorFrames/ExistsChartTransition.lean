import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem frame_mul {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {n : Type} [Fintype n]
    [DecidableEq n] {e : n → Γ(F, U)} (he : VB.IsFrame e) (M : Matrix n n Γ(X, U)) (hM : IsUnit M) :
    VB.IsFrame fun j => ∑ i, M i j • e i := by
  intro V h
  have hM' : IsUnit ((resG X h).mapMatrix M) := hM.map _
  have hb : Function.Bijective ((resG X h).mapMatrix M).mulVec :=
    ⟨Matrix.mulVec_injective_of_isUnit hM', Matrix.mulVec_surjective_iff_isUnit.2 hM'⟩
  have key : ⇑(Fintype.linearCombination Γ(X, V) fun j => GlobalTheory.Twist.resM F h (∑ i, M i j • e i)) =
      (Fintype.linearCombination Γ(X, V) fun i => GlobalTheory.Twist.resM F h (e i)) ∘
        ((resG X h).mapMatrix M).mulVec := by
    funext a
    simp only [Function.comp_apply, Fintype.linearCombination_apply, map_sum, GlobalTheory.Twist.resM_smul,
      Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [key]
  exact (he V h).comp hb

private theorem stalk_pre {X : Scheme.{0}} {x : X} {U : X.Opens} (h : x ∈ U) : ⊤ ≤ (X.fromSpecStalk x) ⁻¹ᵁ U :=
  fun p _ => by
    have h₁ : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at h₁
    exact h₁.mem_open U.isOpen h

private theorem evalPt_stalk {X : Scheme.{0}} {x : X} {U : X.Opens} (h : x ∈ U)
    (h' : ⊤ ≤ (X.fromSpecStalk x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    evalPt (R := X.presheaf.stalk x) (X.fromSpecStalk x) U h' s = X.presheaf.germ U x h s := by
  have e : (X.fromSpecStalk x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom = X.presheaf.germ U x h := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app h]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    rw [show (homOfLE (le_top : _ ≤ (⊤ : (Spec (X.presheaf.stalk x)).Opens))).op ≫ (homOfLE h').op = 𝟙 _ from Subsingleton.elim _ _]
    simp
  exact congrArg (fun φ => φ.hom s) e

private theorem exists_lift {X : Scheme.{0}} {x : X} {U : X.Opens} (h : x ∈ U) {ι : Type} [Finite ι]
    (t : ι → X.presheaf.stalk x) :
    ∃ (W : X.Opens) (hW : x ∈ W), W ≤ U ∧ ∃ s : ι → Γ(X, W), ∀ i, X.presheaf.germ W x hW (s i) = t i := by
  choose V hV s hs using fun i => X.presheaf.germ_exist (t i)
  have hx : x ∈ U ⊓ ⨅ i, V i := by
    refine ⟨h, ?_⟩
    change x ∈ ((⨅ i, V i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.2 hV
  refine ⟨U ⊓ ⨅ i, V i, hx, inf_le_left,
    fun i => X.presheaf.map (homOfLE (inf_le_right.trans (iInf_le V i))).op (s i), fun i => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply, hs]

theorem UpperTheory.exists_chart_transition :
    ∀ (X : Scheme.{0}) (M : X.Modules) (r : ℕ) (ch : Chart M r) (x : X), x ∈ ch.U → ∀ T : Matrix (Fin r) (Fin r) (X.presheaf.stalk x), IsUnit T.det → ∃ ch' : Chart M r, x ∈ ch'.U ∧ trAt (K := X.presheaf.stalk x) (X.fromSpecStalk x) ch ch' = T := by
  intro X M r ch x hx T hT
  obtain ⟨W, hW, hWU, s, hs⟩ := exists_lift hx (fun p : Fin r × Fin r => T p.1 p.2)
  let S : Matrix (Fin r) (Fin r) Γ(X, W) := Matrix.of fun a b => s (a, b)
  have hS : (X.presheaf.germ W x hW).hom.mapMatrix S = T := by
    ext a b; exact hs (a, b)
  have hxV : x ∈ X.basicOpen S.det := by
    rw [Scheme.mem_basicOpen X S.det x hW, RingHom.map_det, hS]
    exact hT
  have hVW : X.basicOpen S.det ≤ W := X.basicOpen_le _
  have hVU := hVW.trans hWU
  let S' : Matrix (Fin r) (Fin r) Γ(X, X.basicOpen S.det) := (resG X hVW).mapMatrix S
  have hS' : IsUnit S' := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det]
    exact X.toRingedSpace.isUnit_res_basicOpen S.det
  refine ⟨⟨X.basicOpen S.det, _, frame_mul (ch.isFrame.res hVU) S' hS'⟩, hxV, ?_⟩
  ext a b
  refine (trAt_apply (K := X.presheaf.stalk x) (x := X.fromSpecStalk x) ch
    ⟨X.basicOpen S.det, _, frame_mul (ch.isFrame.res hVU) S' hS'⟩ hVU le_rfl (stalk_pre hxV) a b).trans ?_
  refine (evalPt_stalk hxV _ _).trans ?_
  have : ((ch.isFrame.basis hVU).repr (GlobalTheory.Twist.resM M le_rfl (∑ i, S' i b • GlobalTheory.Twist.resM M hVU (ch.e i)))) a = S' a b := by
    have e : GlobalTheory.Twist.resM M le_rfl (∑ i, S' i b • GlobalTheory.Twist.resM M hVU (ch.e i)) =
        ∑ i, S' i b • ch.isFrame.basis hVU i := by
      simp only [map_sum, GlobalTheory.Twist.resM_smul, GlobalTheory.Twist.resM_resM, IsFrame.basis_apply]
      simp [resG]
    rw [e, Module.Basis.repr_sum_self]
  refine (congrArg _ this).trans ?_
  exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) x hxV (s (a, b))).trans (hs (a, b))
