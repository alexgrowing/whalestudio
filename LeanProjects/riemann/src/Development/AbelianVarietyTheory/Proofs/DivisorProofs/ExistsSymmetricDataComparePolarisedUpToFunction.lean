import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionConstantPeriodRatioPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HalfEx

theorem kappa_unique (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (κ κ' : (TK R').left ⟶ (TK R).left) (h : κ ≫ jK R = jK R' ≫ spMap ρ) (h' : κ' ≫ jK R = jK R' ≫ spMap ρ) :
    κ = κ' := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective κ
  obtain ⟨φ', rfl⟩ := Spec.map_surjective κ'
  have e : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ φ) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ φ') := by
    rw [Spec.map_comp, Spec.map_comp]; exact h.trans h'.symm
  have e' := Spec.map_injective e
  congr 1
  ext x
  have := IsLocalization.ringHom_ext (nonZeroDivisors R) (j := φ.hom) (k := φ'.hom)
    (congrArg CommRingCat.Hom.hom e')
  exact congrArg (fun q => q x) this

theorem half_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), Function.Injective ρ → IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → ∃ (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Half Q ρ D e f := by
  intro R _ _ R' _ _ _ _ Q ρ P β β₂ hρ hpb hsq hiso
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (GlobalTheory.T.all_six_abelian_scheme_laws_hold.1.cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P
  have hF := hpb.1
  obtain ⟨c, hc⟩ : ∃ c : Q.X → (𝟙_ (Over (Sp R')) ⟶ P.A), ∀ x,
      (c x).left ≫ β = spMap ρ ≫ (Q.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (spMap ρ ≫ (Q.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap ρ))).left = spMap ρ :=
      Category.id_comp _
    have m := hpb.2 _ (c a) (c b) (toUnit _ ≫ Q.c a) (toUnit _ ≫ Q.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, Q.c_add]
    exact m
  choose psi hpsi using fun x : Q.X => GlobalTheory.SS.HtForm.gen_field _
    (DVR.linComb_isLB P.L P.isLB (K := PUnit) (fun _ => ptK (c x)) (fun _ => -1))
  let D : DegPre R' :=
    { P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := Q.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.exists_mumfordBundleIso_value_one_origin_polarised R R' Q ρ P β β₂ hpb hsq hiso
  have hR := GlobalTheory.T.exists_fraction_constant_period_ratio_polarised R R' Q ρ D (AddEquiv.refl _) β β₂ w hpb hsq hw hc
  classical
  let f : D.X → D.X → (FractionRing R')ˣ := fun a b =>
    if h : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ then
      (hR h.choose h.choose_spec a b).choose else 1
  refine ⟨D, AddEquiv.refl _, f, β, β₂, w, hpb, hsq, hw, hw1, hc, ?_⟩
  intro κ hκ a b z J J' hJ hJ'
  have h : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := ⟨κ, hκ⟩
  have e := kappa_unique R R' ρ _ _ h.choose_spec hκ
  have := (hR h.choose h.choose_spec a b).choose_spec z J J' hJ hJ'
  simp only [f, dif_pos h]
  rw [← e]
  exact this

end GlobalTheory.HalfEx
