import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerLink

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def W (U : A.left.Opens) : Opens (Tot Empty g) := ⟨{p | p.2 ∈ pre u.ex U}, (u.hol U 0).1.preimage continuous_snd⟩

theorem an (U : A.left.Opens) (b : Γ(A.left, U)) :
    AnalyticOnNhd ℂ (fun p : Tot Empty g => val u.ex U b p.2) (W u U) :=
  GlobalTheory.SCV.analyticOnNhd_of_differentiableOn (W u U).isOpen ((u.hol U b).2.comp differentiableOn_snd fun _ h => h)

def valHom (U : A.left.Opens) : Sec (str A) U →ₐ[ℂ] Hol (W u U) where
  toFun b := Hol.mk _ (an u U b)
  map_one' := Subtype.ext (funext fun p => valAt'_one _ p.2)
  map_mul' a b := Subtype.ext (funext fun p => valAt'_mul _ _ a b)
  map_zero' := Subtype.ext (funext fun p => valAt'_zero _ _)
  map_add' a b := Subtype.ext (funext fun p => valAt'_add _ _ a b)
  commutes' c := Subtype.ext (funext fun p => by
    obtain ⟨e, he⟩ := (GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.2.2.2.2.1 U p.1.2 p.2
    exact (he _).trans (e.commutes c))

theorem fn_valHom (U : A.left.Opens) (b : Sec (str A) U) {p : Tot Empty g} (hp : p ∈ W u U) :
    (valHom u U b).fn p = val u.ex U b p.2 := Hol.fn_mk _ (an u U b) hp

@[reducible] def ch : Charts (fibFam u) where
  K := A.left.affineOpens
  W U := W u U.1
  base _ _ _ := trivial
  le _ U' U := U' ≤ U
  le_refl _ := le_rfl
  le_trans h h' := h'.trans h
  maps {l U U'} h p hp := ((GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.1 U.1 l p.2).2 ((GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.1 U.1 U'.1 h hp)

theorem sh_valHom {l : u.Λ} {U V : A.left.affineOpens} (h : (ch u).le l V U) (b : Sec (str A) U.1) :
    Charts.sh h (valHom u U.1 b) = valHom u V.1 (Sec.res (str A) h b) :=
  Hol.ext_fn fun p hp => by
    rw [Charts.fn_sh h _ hp, fn_valHom u _ _ ((ch u).maps h p hp), fn_valHom u _ _ hp,
      (GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.2.2.2.1 U.1 V.1 h b p.2 hp]
    exact (GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.1 U.1 b l p.2

def rl : Real (ch u) (str A) (algebraMap ℂ (Hol (fibFam u).V)) where
  x U := spMap (valHom u U.1 : Sec (str A) U.1 →+* Hol (W u U.1)) ≫ affPt (str A) U
  w U := by
    rw [Category.assoc, affPt_w, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun c => (valHom u U.1).commutes c
  compat {l U V} h := by
    rw [← affPt_res (str A) (U := U) (V := V) h, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext (sh_valHom u h)

theorem spMap_valAtHom {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    spMap (valAtHom x U h) ≫ hU.fromSpec = x := by
  change Spec.map (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hU (isAffineOpen_top _) h,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem isFor : (rl u).IsFor (fibUnif u) := by
  intro U p hp
  change spMap _ ≫ spMap _ ≫ U.2.fromSpec = (u.ex p.2).left
  have e : (Hol.ev p hp).toRingHom.comp (valHom u U.1 : Sec (str A) U.1 →+* Hol (W u U.1)) =
      valAtHom (u.ex p.2).left U.1 hp := RingHom.ext fun b =>
    (Hol.ev_apply p hp _).trans ((fn_valHom u _ b hp).trans (valAt'_eq_valAtHom _ hp b))
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.2.fromSpec) ((Cris.spMap_comp _ _).symm.trans (congrArg spMap e))).trans ?_)
  exact spMap_valAtHom _ U.2 hp

abbrev TU (U : A.left.affineOpens) : Thick (dp0 ℂ) (str A) := Thick.triv (Sec (str A) U.1) (affPt (str A) U) (affPt_w _ U)

def al (U : A.left.affineOpens) : TU U ⟶ (rl u).obj ((ch u).triv U) :=
  Thick.trivHom { (valHom u U.1 : Sec (str A) U.1 →+* Hol (W u U.1)) with commutes' := (valHom u U.1).commutes } (by
    change spMap ((Ideal.Quotient.mk ⊥).comp (valHom u U.1 : Sec (str A) U.1 →+* Hol (W u U.1))) ≫ _ =
      spMap ((Ideal.Quotient.mk ⊥).comp (RingHom.id _)) ≫ spMap _ ≫ _
    rw [← Category.assoc, ← Cris.spMap_comp, RingHom.comp_id])

def evc (f : Z1 (O (dp0 ℂ) (str A))) {T T' : (ch u).Obj} (φ : T ⟶ T') : T'.C := ev f ((rl u).functor.map φ)

def eva (f : Z1 (O (dp0 ℂ) (str A))) (U : A.left.affineOpens) : Hol (W u U.1) := ev f (al u U)

theorem exists_lift {B O : Type} [CommRing B] [Algebra ℂ B] [CommRing O] [Algebra ℂ O] (α : B →ₐ[ℂ] O)
    (d : Fin g → Derivation ℂ O O) : ∃ ℓ : Ω[B⁄ℂ] →+ (Fin g → O),
      (∀ (b : B) ω, ℓ (b • ω) = α b • ℓ ω) ∧ ∀ b a, ℓ (KaehlerDifferential.D ℂ B b) a = d a (α b) := by
  letI : Algebra B O := α.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ B O := IsScalarTower.of_algebraMap_eq fun c => (α.commutes c).symm
  refine ⟨(LinearMap.pi fun a => ((d a).compAlgebraMap B).liftKaehlerDifferential).toAddMonoidHom, fun b ω => ?_, fun b a => ?_⟩
  · funext a
    simp only [LinearMap.toAddMonoidHom_coe, map_smul, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
    rfl
  · simp only [LinearMap.toAddMonoidHom_coe, LinearMap.pi_apply, Derivation.liftKaehlerDifferential_comp_D]
    rfl

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

def phi {B O : Type} [CommRing B] [Algebra ℂ B] [CommRing O] [Algebra ℂ O] (α : B →ₐ[ℂ] O) (ℓ : Ω[B⁄ℂ] →+ (Fin g → O))
    (h : ∀ (b : B) ω, ℓ (b • ω) = α b • ℓ ω) : TrivSqZeroExt B Ω[B⁄ℂ] →+* TrivSqZeroExt O (Fin g → O) where
  toFun c := TrivSqZeroExt.inl (α c.fst) + TrivSqZeroExt.inr (ℓ c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    have : (a * b).snd = a.fst • b.snd + b.fst • a.snd := TrivSqZeroExt.snd_mul a b
    rw [TrivSqZeroExt.snd_mul]
    simp [this, h]

theorem fst_phi {B O : Type} [CommRing B] [Algebra ℂ B] [CommRing O] [Algebra ℂ O] (α : B →ₐ[ℂ] O) (ℓ : Ω[B⁄ℂ] →+ (Fin g → O))
    (h : ∀ (b : B) ω, ℓ (b • ω) = α b • ℓ ω) (c : TrivSqZeroExt B Ω[B⁄ℂ]) : (phi α ℓ h c).fst = α c.fst := add_zero _

theorem snd_phi {B O : Type} [CommRing B] [Algebra ℂ B] [CommRing O] [Algebra ℂ O] (α : B →ₐ[ℂ] O) (ℓ : Ω[B⁄ℂ] →+ (Fin g → O))
    (h : ∀ (b : B) ω, ℓ (b • ω) = α b • ℓ ω) (c : TrivSqZeroExt B Ω[B⁄ℂ]) : (phi α ℓ h c).snd = ℓ c.snd := zero_add _

set_option maxHeartbeats 1600000 in

def Phi (U : A.left.affineOpens) (ℓ : Ω[Sec (str A) U.1⁄ℂ] →+ (Fin g → Hol (W u U.1)))
    (h : ∀ b ω, ℓ (b • ω) = valHom u U.1 b • ℓ ω) :
    (diagExt ℂ (Sec (str A) U.1)).thick (affPt (str A) U) (affPt_w _ U) ⟶ (rl u).obj ((ch u).jet U) where
  φ := { phi (valHom u U.1) ℓ h with
    commutes' := fun c => TrivSqZeroExt.ext ((fst_phi _ ℓ h _).trans ((valHom u U.1).commutes c))
      ((snd_phi _ ℓ h _).trans (map_zero ℓ)) }
  φ₀ := (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom ℂ (Hol (W u U.1)) (Fin g → Hol (W u U.1))).toRingHom)).comp
    ((TrivSqZeroExt.inlHom (Hol (W u U.1)) (Fin g → Hol (W u U.1))).comp (valHom u U.1 : Sec (str A) U.1 →+* Hol (W u U.1)))
  comm c := Ideal.Quotient.eq.2 (by
    change (TrivSqZeroExt.inl (valHom u U.1 c.fst) - phi (valHom u U.1) ℓ h c).fst = 0
    rw [TrivSqZeroExt.fst_sub, fst_phi, TrivSqZeroExt.fst_inl, sub_self])
  dp := by
    letI := ((ch u).jet U).ratAlg
    refine isDPMorphism_of_rat _ ((ch u).jet U).δ (phi (valHom u U.1) ℓ h) fun c hc => ?_
    have h0 : c.fst = 0 := hc
    change (phi (valHom u U.1) ℓ h c).fst = 0
    rw [fst_phi, h0, map_zero]
  pt := by
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ affPt (str A) U) (Cris.spMap_comp (valHom u U.1 : Sec (str A) U.1 →+* Hol (W u U.1))
      ((Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom ℂ (Hol (W u U.1)) (Fin g → Hol (W u U.1))).toRingHom)).comp
        (TrivSqZeroExt.inlHom (Hol (W u U.1)) (Fin g → Hol (W u U.1))))).symm)).symm

abbrev sec0 (U : A.left.affineOpens) : TU U ⟶ (diagExt ℂ (Sec (str A) U.1)).thick (affPt (str A) U) (affPt_w _ U) :=
  (diagExt ℂ (Sec (str A) U.1)).secHom (affPt_w _ U) (diagExt ℂ _).i fun _ => rfl

abbrev sec1 (U : A.left.affineOpens) : TU U ⟶ (diagExt ℂ (Sec (str A) U.1)).thick (affPt (str A) U) (affPt_w _ U) :=
  (diagExt ℂ (Sec (str A) U.1)).secHom (affPt_w _ U) (diagSec ℂ _) (fst_derSec _)

def i0 (U : A.left.affineOpens) : Hol (W u U.1) →+* TrivSqZeroExt (Hol (W u U.1)) (Fin g → Hol (W u U.1)) :=
  (TrivSqZeroExt.inlHom _ _).comp (Charts.sh (K := ch u) (l := 0) (k := U) (k' := U) le_rfl)

theorem sq0 (U : A.left.affineOpens) (ℓ : Ω[Sec (str A) U.1⁄ℂ] →+ (Fin g → Hol (W u U.1)))
    (h : ∀ b ω, ℓ (b • ω) = valHom u U.1 b • ℓ ω) (b : Sec (str A) U.1) :
    i0 u U (valHom u U.1 b) = phi (valHom u U.1) ℓ h (TrivSqZeroExt.inl b) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_phi]
    exact Charts.sh_refl (K := ch u) (k := U) le_rfl _
  · rw [snd_phi, TrivSqZeroExt.snd_inl, map_zero]
    rfl

theorem sq1 (U : A.left.affineOpens) (ℓ : Ω[Sec (str A) U.1⁄ℂ] →+ (Fin g → Hol (W u U.1)))
    (h : ∀ b ω, ℓ (b • ω) = valHom u U.1 b • ℓ ω)
    (hD : ∀ b a, ℓ (KaehlerDifferential.D ℂ _ b) a = dw a (valHom u U.1 b)) (b : Sec (str A) U.1) :
    Charts.tszeSec dw (valHom u U.1 b) = phi (valHom u U.1) ℓ h (diagSec ℂ _ b) := by
  refine TrivSqZeroExt.ext ?_ (funext fun a => ?_)
  · rw [fst_phi, Charts.fst_tszeSec, fst_derSec]
  · rw [snd_phi, Charts.snd_tszeSec, snd_derSec, hD]

theorem ev0 (f : Z1 (O (dp0 ℂ) (str A))) (U : A.left.affineOpens) (ℓ : Ω[Sec (str A) U.1⁄ℂ] →+ (Fin g → Hol (W u U.1)))
    (h : ∀ b ω, ℓ (b • ω) = valHom u U.1 b • ℓ ω) :
    i0 u U (eva u f U) + (show TrivSqZeroExt (Hol (W u U.1)) (Fin g → Hol (W u U.1)) from evc u f (Charts.jet0 (K := ch u) U)) =
      phi (valHom u U.1) ℓ h (ev f (sec0 U)) + (show TrivSqZeroExt (Hol (W u U.1)) (Fin g → Hol (W u U.1)) from ev f (Phi u U ℓ h)) :=
  ev_sq f (al u U) ((rl u).functor.map (Charts.jet0 (K := ch u) U)) (sec0 U) (Phi u U ℓ h) (sq0 u U ℓ h)

theorem ev1 (f : Z1 (O (dp0 ℂ) (str A))) (U : A.left.affineOpens) (ℓ : Ω[Sec (str A) U.1⁄ℂ] →+ (Fin g → Hol (W u U.1)))
    (h : ∀ b ω, ℓ (b • ω) = valHom u U.1 b • ℓ ω)
    (hD : ∀ b a, ℓ (KaehlerDifferential.D ℂ _ b) a = dw a (valHom u U.1 b)) :
    Charts.tszeSec dw (eva u f U) + (show TrivSqZeroExt (Hol (W u U.1)) (Fin g → Hol (W u U.1)) from evc u f (Charts.jet1 (K := ch u) U)) =
      phi (valHom u U.1) ℓ h (ev f (sec1 U)) + (show TrivSqZeroExt (Hol (W u U.1)) (Fin g → Hol (W u U.1)) from ev f (Phi u U ℓ h)) :=
  ev_sq f (al u U) ((rl u).functor.map (Charts.jet1 (K := ch u) U)) (sec1 U) (Phi u U ℓ h) (sq1 u U ℓ h hD)

theorem grp {M : Type} [AddCommGroup M] {a0 a1 y0 y1 x0 x1 y G g0 g1 κ : M} (s0 : a0 + y0 = x0 + y) (s1 : a1 + y1 = x1 + y)
    (j0 : G - g0 = y0 - κ) (j1 : G - g1 = y1 - κ) : x0 - x1 = g1 - a1 - (g0 - a0) := by
  linear_combination (norm := abel1) s1 - s0 - j0 + j1

theorem jet_alg {B O : Type} [CommRing B] [Algebra ℂ B] [CommRing O] [Algebra ℂ O] (α : B →ₐ[ℂ] O) (ℓ : Ω[B⁄ℂ] →+ (Fin g → O))
    (h : ∀ (b : B) ω, ℓ (b • ω) = α b • ℓ ω) (d : Fin g → Derivation ℂ O O) (i : O →+* TrivSqZeroExt O (Fin g → O))
    (hi : ∀ x, (i x).snd = 0) {x0 x1 : TrivSqZeroExt B Ω[B⁄ℂ]} {y y0 y1 Gj κ : TrivSqZeroExt O (Fin g → O)} {G0 a0 : O}
    (s0 : i a0 + y0 = phi α ℓ h x0 + y) (s1 : Charts.tszeSec d a0 + y1 = phi α ℓ h x1 + y)
    (j0 : Gj - i G0 = y0 - κ) (j1 : Gj - Charts.tszeSec d G0 = y1 - κ) (a : Fin g) :
    ℓ (x0 - x1).snd a = d a (G0 - a0) := by
  have z : phi α ℓ h (x0 - x1) = Charts.tszeSec d (G0 - a0) - i (G0 - a0) := by
    rw [map_sub, map_sub, map_sub]
    exact grp s0 s1 j0 j1
  have z2 := congrFun (congrArg TrivSqZeroExt.snd z) a
  rw [snd_phi, TrivSqZeroExt.snd_sub (Charts.tszeSec d _), Pi.sub_apply, Charts.snd_tszeSec, hi] at z2
  exact z2.trans (sub_zero _)

set_option maxHeartbeats 1600000 in

theorem jet_eq (f : Z1 (O (dp0 ℂ) (str A))) (U : A.left.affineOpens) (ℓ : Ω[Sec (str A) U.1⁄ℂ] →+ (Fin g → Hol (W u U.1)))
    (h : ∀ b ω, ℓ (b • ω) = valHom u U.1 b • ℓ ω)
    (hD : ∀ b a, ℓ (KaehlerDifferential.D ℂ _ b) a = dw a (valHom u U.1 b)) (G0 : Hol (W u U.1)) (Gj κ : TrivSqZeroExt (Hol (W u U.1)) (Fin g → Hol (W u U.1)))
    (j0 : Gj - i0 u U G0 = (show TrivSqZeroExt (Hol (W u U.1)) (Fin g → Hol (W u U.1)) from evc u f (Charts.jet0 (K := ch u) U)) - κ)
    (j1 : Gj - Charts.tszeSec dw G0 = (show TrivSqZeroExt (Hol (W u U.1)) (Fin g → Hol (W u U.1)) from evc u f (Charts.jet1 (K := ch u) U)) - κ) (a : Fin g) :
    ℓ (connForm f (affPt (str A) U) (affPt_w _ U)) a = dw a (G0 - eva u f U) := by
  exact jet_alg (valHom u U.1) ℓ h dw (i0 u U) (fun _ => rfl) (ev0 u f U ℓ h) (ev1 u f U ℓ h hD) j0 j1 a

theorem lift_fn (U : A.left.Opens) (ℓ : Ω[Sec (str A) U⁄ℂ] →+ (Fin g → Hol (W u U)))
    (h : ∀ b ω, ℓ (b • ω) = valHom u U b • ℓ ω)
    (hD : ∀ b a, ℓ (KaehlerDifferential.D ℂ _ b) a = dw a (valHom u U b)) (a : Fin g) {p : Tot Empty g} (hp : p ∈ W u U)
    (ω : Ω[Sec (str A) U⁄ℂ]) : (ℓ ω a).fn p = evForm u.ex U p.2 ω (Pi.single a 1) := by
  obtain ⟨-, e2, e3⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U p.2 hp
  have hm : ω ∈ Submodule.span (Sec (str A) U) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [hD, e3, dw, Hol.fn_der _ _ hp, Hol.fderiv_fn_congr _ (F := val u.ex U b ∘ Prod.snd) (fun q hq => fn_valHom u U b hq) hp,
      fderiv_comp p (g := val u.ex U b) (((u.hol U b).2.differentiableAt ((u.hol U b).1.mem_nhds hp))) differentiableAt_snd, fderiv_snd]
    rfl
  | zero =>
    rw [map_zero, map_zero, Pi.zero_apply, ← Hol.ev_apply p hp, map_zero]; rfl
  | add x y _ _ hx hy => rw [map_add, map_add, Pi.add_apply, Hol.fn_add _ _ hp, hx, hy]; rfl
  | smul b x _ hx => rw [h, e2, Pi.smul_apply, smul_eq_mul, Hol.fn_mul _ _ hp, hx, fn_valHom u U b hp]; rfl

set_option maxHeartbeats 800000 in

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : FirstDeRham (str A)) (q : u.Λ →+ ℂ) (per : u.Λ →+ Hol (fibFam u).V), (∀ l, per l = algebraMap ℂ _ (q l)) → IsPeriod (fibUnif u) c per → IsPer u.ex u.Λ (cmp1 (str A) c) q := by
  intro A _ g L u c q per hper hP
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have h1 := hP (ch u) (rl u) (isFor u)
  rw [CoefMap.pullCohomologyOne_class, Charts.perCl, H1.mk_eq_mk] at h1
  obtain ⟨G₀, hG⟩ := h1
  let G : ∀ T : (ch u).Obj, T.C := G₀
  have hG' : ∀ {T T' : (ch u).Obj} (φ : T ⟶ T'), G T' - φ.φ (G T) =
      evc u f φ - @algebraMap _ _ _ _ T'.alg (per φ.deg) := fun {T T'} φ =>
    congrFun (congrFun (congrFun hG T) T') φ
  let H : ∀ U : A.left.affineOpens, Hol (W u U.1) := fun U => (G ((ch u).triv U) : Hol (W u U.1)) - eva u f U
  let pt : (Fin g → ℂ) → Tot Empty g := fun z => (0, z)
  have key : ∀ (l : u.Λ) (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V), ∀ z ∈ pre u.ex V.1,
      (H V).fn (pt z) + q l = (H U).fn (pt (z + l)) + val u.ex V.1 ((cmpZZ (str A) f).1.1 _ _ a) z := by
    intro l U V a z hz
    have hle : (ch u).le l V U := leOfHom a.unop
    have hz' : pt z ∈ W u V.1 := hz
    have k1 := hG' (Charts.ptHom ((ch u).triv V) hle)
    have k2 := ev_sq f (al u U) ((rl u).functor.map (Charts.ptHom ((ch u).triv V) hle))
      (Thick.trivHom (hx := affPt_w (str A) U) (T := TU V) (Sec.res (str A) (leOfHom a.unop))
        (affPt_res (str A) (leOfHom a.unop))) (al u V) (fun b => sh_valHom u hle b)
    have k3 : H V + (ch u).cst V (per l) = Charts.sh hle (H U) + valHom u V.1 ((cmpZZ (str A) f).1.1 _ _ a) := by
      have k1' : (G ((ch u).triv V) : Hol (W u V.1)) - Charts.sh hle (G ((ch u).triv U)) =
        evc u f (Charts.ptHom ((ch u).triv V) hle) - (ch u).cst V (per l) := k1
      have k2' : Charts.sh hle (eva u f U) + evc u f (Charts.ptHom ((ch u).triv V) hle) =
        valHom u V.1 ((cmpZZ (str A) f).1.1 _ _ a) + eva u f V := k2
      simp only [H, map_sub]
      linear_combination k1' + k2'
    have k4 := congrArg (fun x : Hol (W u V.1) => x.fn (pt z)) k3
    simp only [Hol.fn_add _ _ hz'] at k4
    rw [Charts.fn_cst _ _ _ hz', Charts.fn_sh hle _ hz', fn_valHom u _ _ hz', hper, Hol.fn_algebraMap (W := ⊤) _ (Opens.mem_top _)] at k4
    exact k4
  have hd : ∀ U : A.left.affineOpens, ∀ z ∈ pre u.ex U.1, HasFDerivAt (fun z => (H U).fn (pt z))
      ((fderiv ℂ (H U).fn (pt z)).comp (ContinuousLinearMap.inr ℂ _ _)) z := fun U z hz =>
    ((H U).analytic (pt z) hz).differentiableAt.hasFDerivAt.comp z (hasFDerivAt_prodMk_right 0 z)
  refine ⟨cmpZZ (str A) f, fun U z => (H U).fn (pt z), rfl, ⟨fun U z hz => (hd U z hz).differentiableAt.differentiableWithinAt,
    fun U V a z hz => ?_, fun U z hz => ?_⟩, fun U l z hz => ?_⟩
  · have := key 0 U V a z hz
    simpa using this
  · obtain ⟨ℓ, h, hD⟩ := exists_lift (valHom u U.1) (dw (W := W u U.1))
    have hz' : pt z ∈ W u U.1 := hz
    have m := jet_eq u f U ℓ h hD (G ((ch u).triv U)) (G ((ch u).jet U)) _ (hG' (Charts.jet0 (K := ch u) U)) (hG' (Charts.jet1 (K := ch u) U))
    rw [(hd U z hz).fderiv]
    refine ContinuousLinearMap.coe_injective (LinearMap.pi_ext' fun a => LinearMap.ext_ring ?_)
    have := lift_fn u U.1 ℓ h hD a hz' (connForm f (affPt (str A) U) (affPt_w _ U))
    rw [m, dw, Hol.fn_der _ _ hz'] at this
    simp only [LinearMap.comp_apply, LinearMap.single_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
    exact this
  · have := key l U U (𝟙 _) z hz
    have h0 : (cmpZZ (str A) f).1.1 _ _ (𝟙 (Opposite.op U)) = 0 := Z1.id ⟨_, (mem_cechDeRhamTotalCocyclesOne_iff.1 (cmpZZ (str A) f).2).1⟩ _
    rw [h0] at this
    have v0 : val u.ex U.1 (0 : Γ(A.left, U.1)) z = 0 := valAt'_zero _ _
    exact (this.trans (by rw [add_eq_left]; exact v0)).symm

end GlobalTheory.PerLink
