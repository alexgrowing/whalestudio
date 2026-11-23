import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorsFunctionsInvertibleDerivs

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.TangentOrigin
open scoped CategoryTheory.Obj

namespace GlobalTheory.TanPt

theorem exists_coords_derivs' {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ (x : Fin D → A) (d : Fin D → A →+ A),
      (∀ c a b, d c (a * b) = a * d c b + b * d c a) ∧
      (∀ a c, d c (x a) = if a = c then 1 else 0) ∧ ∀ c r, d c (α r) = 0 := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ιv, σv, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ιv
  letI := Fintype.ofFinite σv
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ιv) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  let B := P.basisKaehler.reindex e
  have hB : ∀ i, KaehlerDifferential.D k A (P.val (e.symm i)) = B i := fun i => by
    simp [B]
  refine ⟨fun i => P.val (e.symm i), fun c =>
    { toFun := fun s => B.coord c (KaehlerDifferential.D k A s)
      map_zero' := by simp
      map_add' := fun s t => by simp }, fun c a b => ?_, fun a c => ?_, fun c r => ?_⟩
  · change B.coord c (KaehlerDifferential.D k A (a * b)) =
      a * B.coord c (KaehlerDifferential.D k A b) + b * B.coord c (KaehlerDifferential.D k A a)
    rw [Derivation.leibniz, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · change B.coord c (KaehlerDifferential.D k A (P.val (e.symm a))) = _
    rw [hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  · change B.coord c (KaehlerDifferential.D k A (algebraMap k A r)) = 0
    rw [Derivation.map_algebraMap, map_zero]

def jetVec {A K : Type} [CommRing A] [Field K] {D : ℕ} (φ : A →+* K) (d : Fin D → A →+ A)
    (hd : ∀ c a b, d c (a * b) = a * d c b + b * d c a) : A →+* TrivSqZeroExt K (Fin D → K) where
  toFun s := (φ s, fun c => φ (d c s))
  map_one' := by
    refine TrivSqZeroExt.ext (map_one φ) ?_
    funext c
    have h1 : d c 1 = 0 := by simpa using hd c 1 1
    change φ (d c 1) = 0
    rw [h1, map_zero]
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero φ) ?_
    funext c
    change φ (d c 0) = 0
    rw [map_zero, map_zero]
  map_add' s t := by
    refine TrivSqZeroExt.ext (map_add φ s t) ?_
    funext c
    change φ (d c (s + t)) = φ (d c s) + φ (d c t)
    rw [map_add, map_add]
  map_mul' s t := by
    refine TrivSqZeroExt.ext (map_mul φ s t) ?_
    refine Eq.trans ?_ (TrivSqZeroExt.snd_mul _ _).symm
    funext c
    show φ (d c (s * t)) = (φ s • (fun c => φ (d c t)) + MulOpposite.op (φ t) • (fun c => φ (d c s))) c
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, hd c, map_add, map_mul, map_mul, mul_comm (φ (d c s))]

theorem evalPt_congr {R : Type} [CommRing R] {X : Scheme.{0}} {x y : Sp R ⟶ X} (e : x = y) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) : evalPt x U hx f = evalPt y U hy f := by
  subst e; rfl

end GlobalTheory.TanPt

namespace GlobalTheory.TanPt

theorem exists_tangent_point : ∀ {o : Type} [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (K : Type) [Field K] (β : o →+* K) (x₀ : Sp K ⟶ X), x₀ ≫ s = spMap β → ∃ y : Sp (TrivSqZeroExt K (Fin D → K)) ⟶ X, spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ y = x₀ ∧ y ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin D → K))).comp β) ∧ ∀ mu : (Fin D → K) →ₗ[K] K, spMap (dirMap mu) ≫ y = constPt (spMap (dirMap mu) ≫ y) → mu = 0 := by
  intro o _ Y p D hsm K _ β z hz
  haveI := hsm
  obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (GlobalTheory.Adelic.ptOf z))
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨S, hS, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (S : Set Γ(Y, V)), GlobalTheory.Adelic.ptOf z ∈ Y.basicOpen (t : Γ(Y, V)) :=
    TopologicalSpace.Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hS).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨x, d, hl, hd, h0⟩ := exists_coords_derivs' h₂
  have hO : IsAffineOpen (Y.basicOpen (t : Γ(Y, V))) := IsAffineOpen.basicOpen hV _
  have hzO : ⊤ ≤ z ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := (GlobalTheory.Adelic.le_iff_ptOf_mem z _).2 hxt
  obtain ⟨w, hw, he⟩ := exists_evalPt_eq hO (jetVec (evalPt z _ hzO) d hl)
  refine ⟨w, ?_, ?_, fun mu hmu => ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ w) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    refine ext_evalPt hO h' hzO (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ w _ hw h' f).trans ?_
    rw [he]
    rfl
  · refine eq_spMap_of_evalPt _ _ fun a => ?_
    rw [← evalPt_constFn p w _ hw a, he]
    have hza : evalPt z _ hzO (constFn p (Y.basicOpen (t : Γ(Y, V))) a) = β a := by
      rw [evalPt_constFn]
      exact (evalPt_congr hz (⊤ : (Sp o).Opens) _ le_rfl _).trans (evalPt_spMap β a)
    refine TrivSqZeroExt.ext ?_ ?_
    · exact hza
    · funext c
      change evalPt z _ hzO (d c (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p _ a)) = _
      rw [h0 c a, map_zero]
      rfl
  · refine (Pi.basisFun K (Fin D)).ext fun a => ?_
    have h1 : ⊤ ≤ (spMap (dirMap mu) ≫ w) ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    have h2 : ⊤ ≤ (constPt (spMap (dirMap mu) ≫ w)) ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) :=
      fun q _ => hw (Set.mem_univ _)
    have h3 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap mu) ≫ w) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    have e := congrArg TrivSqZeroExt.snd (evalPt_congr hmu _ h1 h2 (x a))
    have e2 : (evalPt (constPt (spMap (dirMap mu) ≫ w)) _ h2 (x a)).snd = 0 := by
      rw [evalPt_congr (show constPt (spMap (dirMap mu) ≫ w) = spMap (algebraMap K (DualNumber K)) ≫
        (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap mu) ≫ w) from rfl) _ h2 h2,
        evalPt_spMap_comp _ _ _ h3 h2]
      rfl
    rw [e2, evalPt_spMap_comp _ w _ hw h1, he] at e
    have hv : (fun c => evalPt z _ hzO (d c (x a))) = Pi.basisFun K (Fin D) a := by
      funext c
      rw [hd, Pi.basisFun_apply]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Pi.single_apply, Ne.symm hac]
    rw [LinearMap.zero_apply, ← hv]
    rw [dirMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.snd_map] at e
    exact e

end GlobalTheory.TanPt
