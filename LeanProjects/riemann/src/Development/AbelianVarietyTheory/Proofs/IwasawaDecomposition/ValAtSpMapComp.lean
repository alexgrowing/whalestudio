import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuativeExtensionPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePlacesLgNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HtIndep

section Values

variable {K : Type} [Field K] {Z : Scheme.{0}}

theorem below_spMap_comp (ψ : K →+* K) (y : Sp K ⟶ Z) : below (spMap ψ ≫ y) = below y := by
  have h : (spMap ψ) (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint K :=
    Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg y h)

variable [IsIntegral Z]

theorem valAt_of_factor (x : Z) (y : Sp K ⟶ Z) (hy : below y = x)
    (φ : Z.presheaf.stalk x ⟶ CommRingCat.of K) (h : Spec.map φ ≫ Z.fromSpecStalk x = y)
    (a : Z.presheaf.stalk x) : valAt y (algebraMap _ Z.functionField a) = φ.hom a := by
  subst hy
  have e : φ = Scheme.stalkClosedPointTo y := by
    apply Spec.map_injective
    rw [← cancel_mono (Z.fromSpecStalk _), h, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  rw [e, Base.valAt_stalk]

theorem valAt_spMap_comp (ψ : K →+* K) (y : Sp K ⟶ Z) (f : Z.functionField) :
    valAt (spMap ψ ≫ y) f = ψ (valAt y f) := by
  by_cases h : RegAt (below y) f
  · obtain ⟨a, rfl⟩ := h
    rw [Base.valAt_stalk y]
    refine valAt_of_factor (below y) _ (below_spMap_comp ψ y)
      (Scheme.stalkClosedPointTo y ≫ CommRingCat.ofHom ψ) ?_ a
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · have h' : ¬ RegAt (below (spMap ψ ≫ y)) f := by rwa [below_spMap_comp]
    rw [valAt, dif_neg h', valAt, dif_neg h, map_zero]

end Values

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def act (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (y : AlgPt Y) : AlgPt Y :=
  ⟨spMap (g : AlgebraicClosure F →+* AlgebraicClosure F) ≫ y.1, by
    have e : (g : AlgebraicClosure F →+* AlgebraicClosure F).comp (algebraMap F (AlgebraicClosure F)) =
        algebraMap F (AlgebraicClosure F) := RingHom.ext g.commutes
    rw [Category.assoc, y.2, ← Spec.map_comp]
    exact congrArg (fun ρ => spMap ρ) e⟩

theorem act_symm_act (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (y : AlgPt Y) :
    act g.symm (act g y) = y := by
  refine Subtype.ext ?_
  change spMap (g.symm : AlgebraicClosure F →+* AlgebraicClosure F) ≫
    spMap (g : AlgebraicClosure F →+* AlgebraicClosure F) ≫ y.1 = y.1
  rw [← Category.assoc, ← Spec.map_comp]
  have e' : Spec.map (CommRingCat.ofHom (g : AlgebraicClosure F →+* AlgebraicClosure F) ≫
      CommRingCat.ofHom (g.symm : AlgebraicClosure F →+* AlgebraicClosure F)) = 𝟙 _ := by
    have e : CommRingCat.ofHom (g : AlgebraicClosure F →+* AlgebraicClosure F) ≫
        CommRingCat.ofHom (g.symm : AlgebraicClosure F →+* AlgebraicClosure F) = 𝟙 _ :=
      CommRingCat.hom_ext (RingHom.ext g.symm_apply_apply)
    rw [e, Spec.map_id]
  rw [e', Category.id_comp]

def actEquiv (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) : AlgPt Y ≃ AlgPt Y where
  toFun := act g
  invFun := act g.symm
  left_inv := act_symm_act g
  right_inv := act_symm_act g.symm

variable {C : CxSt F} {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
  {cf : HeightOneSpectrum (𝓞 F) → ℝ}

theorem lg_act (hI : A.Induced M L k cf) {v : HeightOneSpectrum (𝓞 F)} (e e' : Ext v)
    (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (hg : ∀ x, e'.w x = e.w (g x)) (y : AlgPt Y) :
    A.lg v e (act g y) = A.lg v e' y := by
  obtain ⟨-, r, -, -, hfin⟩ := hI
  obtain ⟨yt, hyt, hU⟩ := exists_valuationRing_point F Y M v e' y
  have hx : yt (IsLocalRing.closedPoint e'.O) ∈ (⨆ i, L.B.U i : M.X.Opens) := by
    rw [L.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let gO : e'.O →+* e.O :=
    ((g : AlgebraicClosure F →+* AlgebraicClosure F).comp e'.O.subtype).codRestrict e.O.toSubring
      fun x => (e.mem_O _).2 (by
        have := (e'.mem_O _).1 x.2
        rw [hg] at this
        exact this)
  have hc : spMap e.O.subtype ≫ spMap gO =
      spMap (g : AlgebraicClosure F →+* AlgebraicClosure F) ≫ spMap e'.O.subtype := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hyt₂ : spMap e.O.subtype ≫ spMap gO ≫ yt = (act g y).1 ≫ M.j := by
    rw [← Category.assoc, hc, Category.assoc, hyt]
    exact (Category.assoc _ _ _).symm
  have h' := hfin v e' y yt (fun _ => i) hyt (hU _ hi).1
  have h := hfin v e (act g y) (spMap gO ≫ yt) (fun _ => i) hyt₂
    (fun x _ => (hU _ hi).1 (x := spMap gO x) trivial)
  have hb : below (act g y).1 = below y.1 := below_spMap_comp _ _
  have hv (u : Y.Fn) : e.w (valAt (act g y).1 u) = e'.w (valAt y.1 u) := by
    rw [hg]
    exact congrArg e.w (valAt_spMap_comp _ y.1 u)
  rw [hb, hv, ← h'] at h
  exact mul_left_cancel₀ (by exact_mod_cast k.ne_zero) h

theorem main : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y), A.IsModel → ∀ x : Y.X, IsClosed ({x} : Set Y.X) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v), ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v e y = ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v e' y) ∧ {v : HeightOneSpectrum (𝓞 F) | ∃ (e : Ext v) (y : AlgPt Y), below y.1 = x ∧ A.lg v e y ≠ 0}.Finite := by
  intro F _ _ C Y A hA x hx
  obtain ⟨M, L, k, cf, hI⟩ := hA
  refine ⟨fun v e e' => ?_, ?_⟩
  · obtain ⟨g, hg⟩ := ExtConj.conj v e e'
    refine (finsum_comp_equiv (actEquiv g)
      (f := fun y : AlgPt Y => ∑ᶠ (_ : below y.1 = x), A.lg v e y)).symm.trans (finsum_congr fun y => ?_)
    have hb : below (act g y).1 = below y.1 := below_spMap_comp _ _
    change ∑ᶠ (_ : below (act g y).1 = x), A.lg v e (act g y) = _
    rw [hb, lg_act hI e e' g hg y]
  · have hP : {y : AlgPt Y | below y.1 = x}.Finite :=
      Set.finite_coe_iff.1 (ExtConj.pts Y x hx).2
    refine (hP.biUnion fun y _ => finite_places_lg_ne_zero F C Y A M L k cf hI y).subset ?_
    rintro v ⟨e, y, hy, h⟩
    exact Set.mem_iUnion₂.2 ⟨y, hy, e, h⟩

end GlobalTheory.TrueGeo.HtIndep
