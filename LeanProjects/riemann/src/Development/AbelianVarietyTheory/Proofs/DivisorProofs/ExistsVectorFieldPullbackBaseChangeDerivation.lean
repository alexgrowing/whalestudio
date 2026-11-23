import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecVectorFieldOfDualNumberSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldAffineOpenTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFibreProductAffineCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductAffineOpenClosureLegsEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldsEqOnSubopensOfEqAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldGluedOpenCoverStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FieldBC

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
    (hd : IsField W₀ d) (h : W₁ ≤ W₀) : IsField W₁ d :=
  ⟨fun W hW => hd.1 W (hW.trans h), fun W hW => hd.2.1 W (hW.trans h),
    fun W W' h' hW => hd.2.2 W W' h' (hW.trans h)⟩

def derivOf {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    (V : Z.Opens) (hV : V ≤ W₀) : Derivation ℤ Γ(Z, V) Γ(Z, V) :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' (d V) (hd.1 V hV)))
    (fun a b => by simp [hd.2.1 V hV a b, smul_eq_mul])

theorem exists_field_of_deriv {Z : Scheme.{0}} (V : Z.Opens) (hV : IsAffineOpen V)
    (δ : Derivation ℤ Γ(Z, V) Γ(Z, V)) :
    ∃ e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField V e ∧ ∀ a, e V a = δ a := by
  let σ : Γ(Z, V) →+* DualNumber Γ(Z, V) :=
    { toFun := fun a => TrivSqZeroExt.inl a + TrivSqZeroExt.inr (δ a)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        ext
        · simp
        · simp [δ.leibniz, smul_eq_mul]; ring
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring }
  obtain ⟨d', hd', hd'v⟩ := GlobalTheory.SpecField.exists_isField Γ(Z, V) σ (fun a => by simp [σ])
  exact GlobalTheory.FieldTransport.exists_isField_transport Z V hV (fun a => δ a) d' hd'
    (fun a => by
      refine (hd'v a).trans ?_
      simp only [σ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      rfl)

theorem sec_ext {Z : Scheme.{0}} (V : Z.Opens) (s t : Γ(Z, V))
    (h : ∀ x ∈ V, ∃ V' : Z.Opens, ∃ hV' : V' ≤ V, x ∈ V' ∧ resG Z hV' s = resG Z hV' t) : s = t := by
  refine TopCat.Presheaf.section_ext Z.sheaf V s t fun x hx => ?_
  obtain ⟨V', hV', hx', e⟩ := h x hx
  have := congrArg (Z.presheaf.germ V' x hx').hom e
  simp only [resG, TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem appLE_res {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (h : V' ≤ V) (r : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom r) = (f.appLE U V' (h.trans e)).hom r := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U U' : Y.Opens) (V : X.Opens) (h : U' ≤ U)
    (e : V ≤ f ⁻¹ᵁ U') (r : Γ(Y, U)) :
    (f.appLE U' V e).hom (resG Y h r) = (f.appLE U V (e.trans (f.preimage_mono h))).hom r := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem deriv_eq_zero_of_closure {B : Type} [CommRing B] (Δ : Derivation ℤ B B) (S : Set B)
    (hS : Subring.closure S = ⊤) (h : ∀ x ∈ S, Δ x = 0) (x : B) : Δ x = 0 := by
  have hx : x ∈ Subring.closure S := hS ▸ Subring.mem_top x
  induction hx using Subring.closure_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]
  | mul x y _ _ hx hy => simp [Derivation.leibniz, hx, hy]

theorem exists_field_pullback : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (W : Z.Opens) (hW : W ≤ p ⁻¹ᵁ U.1) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W d → (∀ r, d W ((p.appLE U.1 W hW).hom r) = (p.appLE U.1 W hW).hom (D r)) → ∃ d' : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O), IsField (φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1) d' ∧ (∀ (O' : Z'.Opens) (h' : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ φ ⁻¹ᵁ W → ∀ r, d' O' ((p'.appLE U'.1 O' h').hom r) = (p'.appLE U'.1 O' h').hom (D' r)) ∧ ∀ (O : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O), O ≤ W → O' ≤ p' ⁻¹ᵁ U'.1 → ∀ f, d' O' ((φ.appLE O O' h).hom f) = (φ.appLE O O' h).hom (d O f) := by
  intro Z Z' X X' p p' φ g hpb U U' hU D D' hD' W hW d hd hdD
  classical
  let A := {O : Z.affineOpens // O.1 ≤ W}
  have hOp : ∀ O : A, O.1.1 ≤ p ⁻¹ᵁ U.1 := fun O => O.2.trans hW
  let O' : A → Z'.Opens := fun O => φ ⁻¹ᵁ O.1.1 ⊓ p' ⁻¹ᵁ U'.1
  have hO'aff : ∀ O : A, IsAffineOpen (O' O) := fun O =>
    (GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU O.1 (hOp O)).1
  have hgen : ∀ O : A, Subring.closure (Set.range (φ.appLE O.1.1 (O' O) inf_le_left).hom ∪
      Set.range (p'.appLE U'.1 (O' O) inf_le_right).hom) = ⊤ := fun O =>
    (GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU O.1 (hOp O)).2
  let δ : ∀ O : A, Derivation ℤ Γ(Z, O.1.1) Γ(Z, O.1.1) := fun O => derivOf hd O.1.1 O.2
  have hδ : ∀ (O : A) r, δ O ((p.appLE U.1 O.1.1 (hOp O)).hom r) =
      (p.appLE U.1 O.1.1 (hOp O)).hom (D r) := by
    intro O r
    show d O.1.1 _ = _
    rw [← appLE_res p U.1 W O.1.1 hW O.2, hd.2.2 W O.1.1 O.2 le_rfl, hdD, appLE_res]
  choose δ' hδ'1 hδ'2 using fun O : A =>
    GlobalTheory.T.exists_derivation_fibreProduct_affine_compatible Z Z' X X' p p' φ g hpb U U' hU D D' hD' O.1 (hOp O) (δ O) (hδ O)
  choose e he1 he2 using fun O : A => exists_field_of_deriv (O' O) (hO'aff O) (δ' O)

  have hT : ∀ (O : A) (V : Z'.Opens) (hV : V ≤ O' O) (b : Γ(Z, O.1.1)),
      e O V ((φ.appLE O.1.1 V (hV.trans inf_le_left)).hom b) =
        (φ.appLE O.1.1 V (hV.trans inf_le_left)).hom (d O.1.1 b) := by
    intro O V hV b
    rw [← appLE_res φ O.1.1 (O' O) V inf_le_left hV, (he1 O).2.2 (O' O) V hV le_rfl, he2, hδ'2,
      appLE_res]
    rfl
  have hP : ∀ (O : A) (V : Z'.Opens) (hV : V ≤ O' O) (r : Γ(X', U'.1)),
      e O V ((p'.appLE U'.1 V (hV.trans inf_le_right)).hom r) =
        (p'.appLE U'.1 V (hV.trans inf_le_right)).hom (D' r) := by
    intro O V hV r
    rw [← appLE_res p' U'.1 (O' O) V inf_le_right hV, (he1 O).2.2 (O' O) V hV le_rfl, he2, hδ'1,
      appLE_res]

  let bas : (O : A) → Γ(Z, O.1.1) → A := fun O s =>
    ⟨⟨Z.basicOpen s, O.1.2.basicOpen s⟩, (Z.basicOpen_le s).trans O.2⟩
  have hKB : ∀ (O : A) (s : Γ(Z, O.1.1)) (V : Z'.Opens), V ≤ O' (bas O s) → ∀ f,
      e O V f = e (bas O s) V f := by
    intro O s
    have hle : O' (bas O s) ≤ O' O := inf_le_inf_right _ (φ.preimage_mono (Z.basicOpen_le s))
    refine GlobalTheory.T.vectorFields_eq_on_subopens_of_eq_affine Z' (O' (bas O s)) (hO'aff (bas O s)) (e O) (e (bas O s))
      (isField_mono (he1 O) hle) (he1 (bas O s)) ?_
    intro a
    rw [he2 (bas O s)]
    let Δ := derivOf (he1 O) (O' (bas O s)) hle - δ' (bas O s)
    have hΔ : ∀ x, Δ x = e O (O' (bas O s)) x - δ' (bas O s) x := fun x => rfl
    suffices key : ∀ x, Δ x = 0 by
      have := key a
      rwa [hΔ, sub_eq_zero] at this
    refine deriv_eq_zero_of_closure Δ _ (hgen (bas O s)) ?_
    rintro x (⟨c, rfl⟩ | ⟨r, rfl⟩)
    · let ψ := (φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
      have hres : ∀ b : Γ(Z, O.1.1), Δ (ψ (resG Z (Z.basicOpen_le s) b)) = 0 := by
        intro b
        rw [hΔ, sub_eq_zero]
        show e O (O' (bas O s)) ((φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
          (resG Z (Z.basicOpen_le s) b)) = δ' (bas O s) ((φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom
          (resG Z (Z.basicOpen_le s) b))
        rw [hδ'2 (bas O s)]
        show _ = (φ.appLE (Z.basicOpen s) (O' (bas O s)) inf_le_left).hom (d (Z.basicOpen s) (resG Z (Z.basicOpen_le s) b))
        rw [res_appLE, hT O _ hle, hd.2.2 O.1.1 (Z.basicOpen s) (Z.basicOpen_le s) O.2, res_appLE]
      haveI := O.1.2.isLocalization_basicOpen s
      obtain ⟨⟨a₀, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) c
      change c * resG Z (Z.basicOpen_le s) m = resG Z (Z.basicOpen_le s) a₀ at hm
      have hunit : IsUnit (ψ (resG Z (Z.basicOpen_le s) m)) := by
        obtain ⟨n, hn⟩ := m.2
        rw [← hn, map_pow]
        exact ((RingedSpace.isUnit_res_basicOpen Z.toRingedSpace s).pow n).map ψ
      have h1 := congrArg (fun y => Δ (ψ y)) hm
      simp only [map_mul, Derivation.leibniz, hres, smul_zero, zero_add, smul_eq_mul, mul_zero] at h1
      exact (hunit.mul_right_eq_zero).1 h1
    · rw [hΔ, sub_eq_zero, hP O _ hle, hδ'1]
  have hcomp : ∀ (O₁ O₂ : A) (V : Z'.Opens), V ≤ O' O₁ → V ≤ O' O₂ → ∀ f, e O₁ V f = e O₂ V f := by
    intro O₁ O₂ V h1 h2 f
    apply sec_ext V
    intro x hx
    have hx1 : φ.base x ∈ O₁.1.1 ⊓ O₂.1.1 := ⟨(h1 hx).1, (h2 hx).1⟩
    obtain ⟨f₁, f₂, hf, hxf⟩ := exists_basicOpen_le_affine_inter O₁.1.2 O₂.1.2 _ hx1
    have hA : bas O₁ f₁ = bas O₂ f₂ := Subtype.ext (Subtype.ext hf)
    have hV1 : V ⊓ O' (bas O₁ f₁) ≤ O' (bas O₁ f₁) := inf_le_right
    have hV2 : V ⊓ O' (bas O₁ f₁) ≤ O' (bas O₂ f₂) := le_of_le_of_eq inf_le_right (congrArg O' hA)
    refine ⟨V ⊓ O' (bas O₁ f₁), inf_le_left, ⟨hx, hxf, (h1 hx).2⟩, ?_⟩
    rw [← (he1 O₁).2.2 V _ inf_le_left h1, ← (he1 O₂).2.2 V _ inf_le_left h2,
      hKB O₁ f₁ _ hV1, hKB O₂ f₂ _ hV2]
    exact congrArg (fun B => e B (V ⊓ O' (bas O₁ f₁)) (resG Z' inf_le_left f)) hA
  obtain ⟨d', hd'1, hd'2⟩ := GlobalTheory.T.exists_vectorField_glued_openCover Z' A O' e he1 hcomp
  have hcov : φ ⁻¹ᵁ W ⊓ p' ⁻¹ᵁ U'.1 ≤ ⨆ O : A, O' O := by
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ W from hx.1)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨O₀, hO₀⟩, hle⟩, hx0, hx.2⟩
  refine ⟨d', isField_mono hd'1 hcov, ?_, ?_⟩
  · intro V hV hVW r
    have hVc : V ≤ ⨆ O : A, O' O := (le_inf hVW hV).trans hcov
    apply sec_ext V
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ W from hVW hx)
    let B : A := ⟨⟨O₀, hO₀⟩, hle⟩
    refine ⟨V ⊓ O' B, inf_le_left, ⟨hx, hx0, hV hx⟩, ?_⟩
    rw [← hd'1.2.2 V _ inf_le_left hVc, appLE_res, appLE_res, hd'2 B _ inf_le_right,
      hP B _ inf_le_right]
  · intro O V h hOW hV f
    have hVc : V ≤ ⨆ O : A, O' O :=
      (le_inf (h.trans (φ.preimage_mono hOW)) hV).trans hcov
    apply sec_ext V
    intro x hx
    obtain ⟨O₀, hO₀, hx0, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
      (show φ.base x ∈ O from h hx)
    let B : A := ⟨⟨O₀, hO₀⟩, hle.trans hOW⟩
    refine ⟨V ⊓ O' B, inf_le_left, ⟨hx, hx0, hV hx⟩, ?_⟩
    rw [← hd'1.2.2 V _ inf_le_left hVc, appLE_res, appLE_res, hd'2 B _ inf_le_right,
      ← res_appLE φ O O₀ (V ⊓ O' B) hle (inf_le_right.trans inf_le_left) f,
      hT B _ inf_le_right, hd.2.2 O O₀ hle hOW, res_appLE]

end GlobalTheory.FieldBC
