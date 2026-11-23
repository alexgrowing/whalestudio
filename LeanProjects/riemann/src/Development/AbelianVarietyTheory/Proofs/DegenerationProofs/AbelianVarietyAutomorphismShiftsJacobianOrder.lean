import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.OrdTwist

theorem det_cross {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Type} [Fintype I] [DecidableEq I]
    (b : Module.Basis I B Ω[B⁄K]) (D D' : I → Derivation K B B) (t u : I → B) :
    (Matrix.of fun i j => D' i (t j)).det * (Matrix.of fun i j => D i (u j)).det =
      (Matrix.of fun i j => D' i (u j)).det * (Matrix.of fun i j => D i (t j)).det := by
  have key : ∀ (E : I → Derivation K B B) (v : I → B), (Matrix.of fun i j => E i (v j)).det =
      (Matrix.of fun i k => (E i).liftKaehlerDifferential (b k)).det *
        (Matrix.of fun k j => b.repr (KaehlerDifferential.D K B (v j)) k).det := by
    intro E v
    rw [← Matrix.det_mul]
    congr 1
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, ← Derivation.liftKaehlerDifferential_comp_D (E i) (v j)]
    conv_lhs => rw [← b.sum_repr (KaehlerDifferential.D K B (v j))]
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.of_apply, mul_comm]
  rw [key D' t, key D u, key D' u, key D t]
  ring

variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]

abbrev rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    rs h' (rs h a) = rs (h'.trans h) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem rs_jac (D : I → VF A) {U V : A.left.Opens} (h : V ≤ U) (t : I → Γ(A.left, U)) :
    rs h (jac D U t) = jac D V (fun i => rs h (t i)) := by
  unfold jac
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact ((D i).res U V h (t j)).symm

theorem rs_cstK {U V : A.left.Opens} (h : V ≤ U) (c : K) : rs h (cstK A U c) = cstK A V c := by
  exact congr($(Scheme.Hom.appLE_map A.hom (U := ⊤) (V := U) le_top (homOfLE h).op)
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))

theorem eq_of_locally {X : Scheme.{0}} {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (e : V ≤ U), x ∈ V ∧ rs e a = rs e b) : a = b := by
  choose V e hx hV using h
  refine X.sheaf.eq_of_locally_eq' (fun x : U => V x.1 x.2) U (fun x => homOfLE (e x.1 x.2)) ?_ a b
    (fun x => hV x.1 x.2)
  intro x hxU
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩

theorem exists_std {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) (U : A.left.Opens) (x : A.left) (hx : x ∈ U) :
    ∃ V : A.left.Opens, V ≤ U ∧ x ∈ V ∧ (cstK A V).IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨W, -, V, hV, hxV, e, hf⟩ := hA.exists_isStandardSmoothOfRelativeDimension x
  obtain rfl : W = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = A.hom x := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact e hxV
  obtain ⟨g, hgU, hxg⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨A.left.basicOpen g, hgU, hxg, ?_⟩
  have := hV.isLocalization_basicOpen g
  have h1 : (algebraMap Γ(A.left, V) Γ(A.left, A.left.basicOpen g)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g
  have h2 : (cstK A V).IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv hf
  have h3 := h1.comp h2
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact (rs_cstK _ c).symm

def toDer (D : VF A) (V : A.left.Opens) :
    letI := (cstK A V).toAlgebra
    Derivation K Γ(A.left, V) Γ(A.left, V) :=
  letI := (cstK A V).toAlgebra
  Derivation.mk'
    { toFun := D.D V
      map_add' := map_add _
      map_smul' := fun c a => by
        show D.D V (cstK A V c * a) = cstK A V c * D.D V a
        rw [D.leibniz, D.const, mul_zero, add_zero] }
    (fun a b => D.leibniz V a b)

theorem jac_cross (hA : SmoothOfRelativeDimension (Fintype.card I) A.hom) (D D' : I → VF A)
    (U : A.left.Opens) (t u : I → Γ(A.left, U)) :
    jac D' U t * jac D U u = jac D' U u * jac D U t := by
  refine eq_of_locally _ _ fun x hx => ?_
  obtain ⟨V, e, hxV, hs⟩ := exists_std hA U x hx
  refine ⟨V, e, hxV, ?_⟩
  simp only [map_mul, rs_jac]
  letI := (cstK A V).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card I) K Γ(A.left, V) := hs
  have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (Fintype.card I) (R := K) (S := Γ(A.left, V))
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Module.finrank Γ(A.left, V) Ω[Γ(A.left, V)⁄K] = Fintype.card I := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (Fintype.card I)]
    simp
  exact det_cross ((Module.finBasisOfFinrankEq _ _ this).reindex (Fintype.equivFin I).symm) (fun i => toDer (D i) V) (fun i => toDer (D' i) V) _ _

theorem exists_ratio (D D' : I → VF A) (hD : IsFrame D) :
    ∃ h : Γ(A.left, ⊤), ∀ (U : A.left.Opens) (t : I → Γ(A.left, U)), jac D' U t = rs le_top h * jac D U t := by
  obtain ⟨hA, hD⟩ := hD
  choose V u hx hu using hD
  have hu' : ∀ x, ∃ w, jac D (V x) (u x) * w = 1 := fun x => (hu x).exists_right_inv
  choose w hw using hu'
  have key : ∀ x (U : A.left.Opens) (e : U ≤ V x) (t : I → Γ(A.left, U)),
      jac D' U t = rs e (jac D' (V x) (u x) * w x) * jac D U t := by
    intro x U e t
    have h1 := congrArg (rs e) (hw x)
    have h2 := jac_cross hA D D' U t (fun i => rs e (u x i))
    simp only [map_mul, map_one, rs_jac] at h1 ⊢
    linear_combination (rs e (w x)) * h2 - jac D' U t * h1
  obtain ⟨h, hh, -⟩ := A.left.sheaf.existsUnique_gluing' V ⊤ (fun x => homOfLE le_top)
    (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩) (fun x => jac D' (V x) (u x) * w x) (by
      intro x y
      show rs (inf_le_left : V x ⊓ V y ≤ V x) _ = rs (inf_le_right : V x ⊓ V y ≤ V y) _
      have h1 := key x (V x ⊓ V y) inf_le_left (fun i => rs inf_le_right (u y i))
      have h2 := congrArg (rs (inf_le_right : V x ⊓ V y ≤ V y)) (hw y)
      generalize rs (inf_le_left : V x ⊓ V y ≤ V x) (jac D' (V x) (u x) * w x) = z at h1 ⊢
      simp only [map_mul, map_one, rs_jac] at h2 ⊢
      rw [h1, _root_.mul_assoc, h2, _root_.mul_one])
  revert hh
  change Γ(A.left, ⊤) at h
  intro hh
  refine ⟨h, fun U t => eq_of_locally _ _ fun x hxU => ⟨U ⊓ V x, inf_le_left, ⟨hxU, hx x⟩, ?_⟩⟩
  have h3 : rs (le_top : V x ≤ ⊤) h = jac D' (V x) (u x) * w x := hh x
  rw [map_mul, rs_jac, rs_jac, key x _ inf_le_right, ← h3, rs_rs, rs_rs]

section Pull
variable {A' : Over (Sp K)} (g : A ⟶ A')

theorem app_rs {X Y : Scheme.{0}} (g : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    (g.app V).hom (rs h a) = rs (g.preimage_mono h) ((g.app U).hom a) :=
  congr($(g.naturality (homOfLE h).op) a)

theorem app_cstK (V : A'.left.Opens) (c : K) : (g.left.app V).hom (cstK A' V c) = cstK A _ c := by
  have h : A'.hom.appLE ⊤ V le_top ≫ g.left.app V = A.hom.appLE ⊤ (g.left ⁻¹ᵁ V) le_top := by
    rw [Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE g.left A'.hom ⊤ V _ le_top le_rfl).trans ?_
    simp only [Over.w g]
  exact congr($h ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))

variable [IsIso g.left]

def appE (V : A'.left.Opens) : Γ(A'.left, V) ≃+* Γ(A.left, g.left ⁻¹ᵁ V) :=
  (asIso (g.left.app V)).commRingCatIsoToRingEquiv

theorem appE_apply (V : A'.left.Opens) (a : Γ(A'.left, V)) : appE g V a = (g.left.app V).hom a := rfl

theorem app_symm (V : A'.left.Opens) (a : Γ(A.left, g.left ⁻¹ᵁ V)) :
    (g.left.app V).hom ((appE g V).symm a) = a := (appE g V).apply_symm_apply a

def transport (D : VF A) : VF A' where
  D V := (appE g V).symm.toAddMonoidHom.comp ((D.D _).comp (appE g V).toAddMonoidHom)
  leibniz V a b := by
    apply (appE g V).injective
    simp [D.leibniz]
  const V c := by
    show (appE g V).symm (D.D _ ((g.left.app V).hom (cstK A' V c))) = 0
    rw [app_cstK, D.const, map_zero]
  res U V h a := by
    apply (appE g V).injective
    show (g.left.app V).hom ((appE g V).symm (D.D _ ((g.left.app V).hom (rs h a)))) =
      (g.left.app V).hom (rs h ((appE g U).symm (D.D _ ((g.left.app U).hom a))))
    rw [app_symm, app_rs, app_rs, app_symm]
    exact D.res _ _ _ _

theorem app_jac (D : I → VF A) (V : A'.left.Opens) (t : I → Γ(A'.left, V)) :
    (g.left.app V).hom (jac (fun i => transport g (D i)) V t) =
      jac D _ (fun i => (g.left.app V).hom (t i)) := by
  unfold jac
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact app_symm g V _

end Pull

theorem exists_const [GrpObj A] (hA : IsAbelianScheme A) (D : I → VF A) (hD : IsFrame D) (f : A ≅ A) :
    ∃ c : K, c ≠ 0 ∧ ∀ (V : A.left.Opens) (t : I → Γ(A.left, V)),
      jac D _ (fun i => (f.inv.left.app V).hom (t i)) = cstK A _ c * (f.inv.left.app V).hom (jac D V t) := by
  have : IsIso f.inv.left := inferInstanceAs (IsIso ((Over.forget _).map f.inv))
  obtain ⟨h, hh⟩ := exists_ratio D (fun i => transport f.inv (D i)) hD
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsIso A.hom.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_field A.hom
  obtain ⟨c', rfl⟩ := (ConcreteCategory.bijective_of_isIso A.hom.appTop).2 h
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 c'
  have key : ∀ (V : A.left.Opens) (t : I → Γ(A.left, V)),
      jac D _ (fun i => (f.inv.left.app V).hom (t i)) = cstK A _ c * (f.inv.left.app V).hom (jac D V t) := by
    intro V t
    rw [← app_jac, hh, map_mul, ← app_cstK f.inv V c]
    rfl
  refine ⟨c, ?_, key⟩
  rintro rfl
  obtain ⟨x⟩ : Nonempty A.left := inferInstance
  obtain ⟨U, t, hx, hu⟩ := hD.2 x
  have e : f.inv.left ⁻¹ᵁ (f.hom.left ⁻¹ᵁ U) = U := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, f.inv_hom_id]; rfl
  have h1 := key (f.hom.left ⁻¹ᵁ U) (fun i => (appE f.inv _).symm (rs e.le (t i)))
  simp only [app_symm, map_zero, zero_mul] at h1
  have h2 := hu.map (rs e.le)
  rw [rs_jac, h1] at h2
  have : Nonempty (f.inv.left ⁻¹ᵁ (f.hom.left ⁻¹ᵁ U) : A.left.Opens) := ⟨⟨x, e.ge hx⟩⟩
  exact not_isUnit_zero h2

def cstR {R : Type} [CommRing R] [Algebra R K] (M : Model R A) (U : M.Y.left.Opens) : R →+* Γ(M.Y.left, U) :=
  (M.Y.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem app_cstR {R : Type} [CommRing R] [Algebra R K] (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cstR M U r) = cstK A _ (algebraMap R K r) := by
  have h : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U =
      (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE M.j M.Y.hom ⊤ U _ le_top le_rfl).trans ?_
    simp only [M.j_hom]
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  refine Eq.trans congr($h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) ?_
  exact congrArg (A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top).hom e.symm

theorem main : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ f : A ≅ A, ∃ c : ℤ, ∀ (M : Model R A) (n : ℤ), HasOrd M D π n → HasOrd (M.twist f) D π (n + c) := by
  intro R K _ _ _ _ _ _ π hπ A _ hA I _ _ D hD f
  obtain ⟨c₀, hc₀, key⟩ := exists_const hA D hD f
  obtain ⟨c, u, hc⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hc₀
  have hπ0 : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  refine ⟨c, fun M n hM => ?_⟩
  have step : ∀ (j : A.left ⟶ M.Y.left), j = f.inv.left ≫ M.j → ∀ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U))
      (s : Γ(M.Y.left, U)),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s →
      jac D (j ⁻¹ᵁ U) (fun i => (j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ (n + c)) * (j.app U).hom (cstR M U u * s) := by
    rintro j rfl U t s h
    have h1 := key (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i))
    rw [h, map_mul, app_cstK] at h1
    refine Eq.trans h1 ?_
    show _ = cstK A (f.inv.left ⁻¹ᵁ M.j ⁻¹ᵁ U) _ * (f.inv.left.app (M.j ⁻¹ᵁ U)).hom ((M.j.app U).hom (cstR M U u * s))
    rw [map_mul, map_mul, app_cstR, app_cstK, hc, zpow_add₀ hπ0, Units.smul_def, Algebra.smul_def]
    simp only [map_mul]
    ring
  have hj : (M.twist f).j = f.inv.left ≫ M.j := by simp [Model.j, Model.twist]
  refine ⟨fun U t => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hM.1 U t
    exact ⟨_, step _ hj U t s hs⟩
  · obtain ⟨U, t, s, hU, hs, h⟩ := hM.2
    exact ⟨U, t, _, hU, (u.isUnit.map _).mul hs, step _ hj U t s h⟩

end GlobalTheory.SS.OrdTwist
end
