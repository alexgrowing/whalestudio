import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyField
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.OrthoMetric

open GlobalTheory.ArchMetricCompare

section Lift

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A]
  {φ : A.left ⟶ G.left} (h : IsGrpPullback A G y φ)

def liftPt (p : Over.mk y ⟶ G) : 𝟙_ (Over (Sp ℂ)) ⟶ A :=
  Over.homMk (h.1.lift (show Sp ℂ ⟶ _ from p.left) (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
    (h.1.lift_snd _ _ _)

theorem liftPt_comp (p : Over.mk y ⟶ G) : (liftPt h p).left ≫ φ = p.left :=
  h.1.lift_fst _ _ _

include h in
theorem pt_ext {a b : 𝟙_ (Over (Sp ℂ)) ⟶ A} (e : a.left ≫ φ = b.left ≫ φ) : a = b :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w, Over.w]))

theorem liftPt_mul (a b : Over.mk y ⟶ G) : liftPt h (a * b) = liftPt h a * liftPt h b := by
  let k : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ y) ⟶ Over.mk y :=
    Over.homMk (𝟙 _) rfl
  refine pt_ext h ((liftPt_comp h _).trans ?_)
  rw [← h.2 _ (liftPt h a) (liftPt h b) (k ≫ a) (k ≫ b)
    ((Category.id_comp _).trans (liftPt_comp h a).symm) ((Category.id_comp _).trans (liftPt_comp h b).symm),
    ← MonObj.comp_mul]
  exact (Category.id_comp _).symm

theorem liftPt_injective : Function.Injective (liftPt h) := fun a b e =>
  Over.OverMorphism.ext ((liftPt_comp h a).symm.trans ((congrArg (·.left ≫ φ) e).trans (liftPt_comp h b)))

theorem liftPt_surjective : Function.Surjective (liftPt h) := fun q => by
  refine ⟨Over.homMk ((show Sp ℂ ⟶ _ from q.left) ≫ φ) ?_, pt_ext h (liftPt_comp h _)⟩
  rw [Category.assoc, h.1.w, ← Category.assoc,
    show (show Sp ℂ ⟶ _ from q.left) ≫ A.hom = 𝟙 _ from Over.w q]
  exact Category.id_comp _

theorem liftPt_one : liftPt h 1 = 1 := by
  have := liftPt_mul h 1 1
  rw [_root_.mul_one] at this
  exact left_eq_mul.1 this

theorem lift_le {L : LB G.left} (p : Over.mk y ⟶ G) (j : (L.pull φ).ι) :
    ⊤ ≤ (liftPt h p).left ⁻¹ᵁ (L.pull φ).U j ↔ ⊤ ≤ p.left ⁻¹ᵁ L.U (j PUnit.unit) := by
  refine (le_pull_iff L _ _ j).trans ?_
  rw [liftPt_comp]

def fibreUnif {L : LB G.left} {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (Λ : AddSubgroup (Fin g → ℂ))
    (fr : L.ι → (Fin g → ℂ) → ℂ) (add : ∀ z w, e (z + w) = e z * e w) (onto : Function.Surjective e)
    (ker : ∀ z, e z = 1 ↔ z ∈ Λ) (disc : DiscreteTopology Λ)
    (full : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (hol : IsHolTo Set.univ fun z => (e z).left)
    (c₁ : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ L.U j})
    (c₂ : ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (c₃ : ∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (e z).left (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) : HolUnif A (L.pull φ) g where
  ex z := liftPt h (e z)
  ex_add z w := by rw [add, liftPt_mul]
  ex_onto := (liftPt_surjective h).comp onto
  Λ := Λ.toIntSubmodule
  ker z := by
    rw [← liftPt_one h, (liftPt_injective h).eq_iff, ker]
    rfl
  discrete := disc
  full := full
  hol U f := by
    have : IsHolTo Set.univ fun z => (show Sp ℂ ⟶ _ from (liftPt h (e z)).left) := by
      refine HolFibre.isHolTo_of_isPullback h.1 ?_ ?_
      · exact (funext fun z => liftPt_comp h (e z) :
          (fun z => (show Sp ℂ ⟶ _ from (liftPt h (e z)).left) ≫ φ) = fun z => (e z).left) ▸ hol
      · exact (funext fun z => Over.w (liftPt h (e z)) :
          (fun z => (show Sp ℂ ⟶ _ from (liftPt h (e z)).left) ≫ A.hom) = fun _ => 𝟙 _) ▸
            HolFibre.isHolTo_const isOpen_univ _
    simpa only [Set.mem_univ, true_and] using this U f
  fr j := fr (j PUnit.unit)
  fr_hol j := by
    have e' : {z | ⊤ ≤ (liftPt h (e z)).left ⁻¹ᵁ (L.pull φ).U j} = {z | ⊤ ≤ (e z).left ⁻¹ᵁ L.U (j PUnit.unit)} :=
      Set.ext fun z => lift_le h _ j
    rw [e']
    exact c₁ _
  fr_ne j z hz := c₂ _ z ((lift_le h _ j).1 hz)
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [val_pull_g L _ _ j j' hz, c₃ _ _ z
      ((top_le_preimage_inf _ _ _).2 ⟨(lift_le h _ j).1 hj, (lift_le h _ j').1 hj'⟩)]
    exact congrArg (fun q => valAt' q _ _ * _) (liftPt_comp h (e z)).symm

end Lift

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem val_tie {y : Sp ℂ ⟶ Xo.X} {t' : SAB H (Sp ℂ)} (m : SABMap t' Xo.univ.t y) {th : LB.Sec t'.PP.L}
    {s : LB.Sec (PPx y)} (ht : SecTie m th s) :
    ∃ w : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m.φ), RigIso m w ∧
      ∀ (p : Sp ℂ ⟶ t'.G.left), p ≫ t'.G.hom = 𝟙 _ → ∃ pt : Sp ℂ ⟶ Gx y, pt ≫ gxFst y = p ≫ m.φ ∧
        pt ≫ gxSnd y = 𝟙 _ ∧ ∀ j i, ⊤ ≤ p ⁻¹ᵁ ((Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ⊓ t'.PP.L.U i) →
          valAt' pt ((PPx y).U fun _ => j) (s.f fun _ => j) =
            valAt' p ((Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ⊓ t'.PP.L.U i) (w.s (fun _ => j, i)).val *
              valAt' p (t'.PP.L.U i) (th.f i) := by
  obtain ⟨w, s1, hw, hm, hs⟩ := ht
  let k : t'.G.left ⟶ Gx y := pullback.lift (f := y) (g := Xo.univ.t.G.hom) t'.G.hom m.φ m.cart.1.w.symm
  have k₁ : k ≫ gxFst y = m.φ := pullback.lift_snd _ _ _
  have k₂ : k ≫ gxSnd y = t'.G.hom := pullback.lift_fst _ _ _
  refine ⟨w, hw, fun p hp => ⟨p ≫ k, by rw [Category.assoc, k₁], by rw [Category.assoc, k₂, hp], fun j i hz => ?_⟩⟩
  have le : (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ≤ k ⁻¹ᵁ (PPx y).U (fun _ => j) := fun q hq =>
    Set.mem_iInter.2 fun _ => by
      have := mem_pull.1 hq
      rw [← k₁] at this
      exact this
  have e := congrArg (valAt' p _) (hm (fun _ => j) i)
  rw [valAt'_map _ _ _ hz, valAt'_mul, valAt'_map _ _ _ hz, hs k k₁ k₂ _ le,
    valAt'_appLE _ _ _ _ _ _ (top_le_preimage_mono _ inf_le_left hz)] at e
  exact e

theorem isDerivAt0_comp {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {Y : Scheme.{0}}
    (φ : A.left ⟶ Y) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    (he : ∀ z, (u.ex z).left ≫ φ = e z) (hv : IsTangent v) (hd : u.IsDiff w v) :
    IsDerivAt0 e w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := by
  obtain rfl : (fun z => (show Sp ℂ ⟶ _ from (u.ex z).left) ≫ φ) = e := funext he
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc]
    refine congrArg (· ≫ φ) (hv.trans ?_)
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  · have := hd (φ ⁻¹ᵁ U) hU ((φ.app U).hom f)
    simp only [valAt'_comp] at this
    rw [← this, Scheme.Hom.comp_appLE]
    rfl

theorem isHolTo_exp {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n)
    {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) :
    IsHolTo Set.univ fun z => (F.ex i P z).left := fun U f => by
  have h := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 U f
  have hd : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  refine ⟨?_, h.2.comp (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) hd.differentiableOn
    fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩⟩
  have e : {b ∈ Set.univ | ⊤ ≤ (F.ex i P b).left ⁻¹ᵁ U} =
      (fun z : Fin g → ℂ => ((0, z) : (Fin 0 → ℂ) × (Fin g → ℂ))) ⁻¹'
        {b ∈ Set.univ ×ˢ Set.univ | ⊤ ≤ (F.ex i P b.2).left ⁻¹ᵁ U} := by
    ext z
    exact ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩
  exact e ▸ h.1.preimage hd.continuous

theorem eq_of_isDerivAt0 {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n)
    {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) {w : Fin g → ℂ}
    {v v' : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left}
    (o : v ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ F.u i P)
    (o' : v' ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ F.u i P)
    (d : IsDerivAt0 (fun z => (F.ex i P z).left) w v) (d' : IsDerivAt0 (fun z => (F.ex i P z).left) w v') : v = v' := by
  let a : epsPt (F.u i P) ⟶ Xo.univ.t.G := Over.homMk v o
  let a' : epsPt (F.u i P) ⟶ Xo.univ.t.G := Over.homMk v' o'
  have e : a = a' := ((F.ex_diff i P hP).1 w).unique d d'
  exact congrArg (·.left) e

theorem exists_unif {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n)
    {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) {y : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P)
    {s : LB.Sec (PPx y)} (Φ : FibKey Xo ℂ y) (ht : SecTie Φ.m Φ.th s) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {χl θ : (Fin g → ℂ) → ℂ} {fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ}
    (herm : Hm.IsHermitian) (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (c₁ : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (c₂ : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (c₃ : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (c₄ : ∀ j, ⊤ ≤ (F.ex i P 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (c₅ : ∀ a j z, ‖χl (P a)‖ = 1 ∧ (⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (P a) * Complex.exp (Real.pi * hermForm Hm z (P a) +
      Real.pi / 2 * hermForm Hm (P a) (P a)) * fr j (z + P a)))
    (c₆ : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (F.ex i P z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ (u : HolUnif Φ.key.P.A Φ.key.P.L g) (χ : u.Λ → ℂ), u.Λ = P.range.toIntSubmodule ∧ u.IsAH Hm χ ∧
      u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧ g = Φ.key.P.g ∧
      ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsTanAt y v →
        IsDerivAt0 (fun z => (F.ex i P z).left) w v →
        ∃ v' : epsR ℂ ⟶ Φ.key.P.A, v'.left ≫ Φ.m.φ = v ∧ u.IsDiff w v' := by
  subst hy
  obtain ⟨w, ⟨hw, hrig⟩, hth⟩ := val_tie Φ.m ht
  obtain ⟨w', hw', hinv⟩ := ConjUnif.exists_inv w hw
  have hL := Φ.T.t.PP.isLB
  have hM := pull_isLB Xo.univ.t.PP.isLB Φ.m.φ
  have hol := isHolTo_exp F i hP
  let u₁ := fibreUnif Φ.m.cart (F.ex i P) P.range fr (F.ex_add i P hP) (F.ex_onto i P hP) (F.ex_ker i P hP)
    hP.2.2.1 hP.2.2.2.1 hol c₁ c₂ c₃
  have hex : ∀ z, (u₁.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := fun z => liftPt_comp Φ.m.cart _
  have hle : ∀ z j, ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.pull Φ.m.φ).U j →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j PUnit.unit) := fun z j => (lift_le Φ.m.cart _ j).1
  have hfr : ∀ (j : Xo.univ.t.PP.L.ι) (k : Φ.T.t.PP.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k) →
      valAt' (u₁.ex z).left ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k)
        (w.s (fun _ => j, k)).val * (carry u₁ hM hL hw').fr k z = fr j z := by
    intro j k z hz
    obtain ⟨hj, hk⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hM hL hw' k (fun _ => j) z hk hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, k))) _
  have hA₁ : u₁.IsAH Hm fun a => χl a := by
    refine ⟨herm, pos, ?_, ?_⟩
    · rintro ⟨_, a, rfl⟩
      obtain ⟨j, -⟩ := exists_chart_at hM (u₁.ex 0).left
      exact (c₅ a (j PUnit.unit) 0).1
    · rintro ⟨_, a, rfl⟩ j z hj
      exact (c₅ a _ z).2 (hle z j hj)
  have hA := carry_isAH hM hL hw' hA₁
  obtain ⟨-, -, -, hg, -, htan, -⟩ := AHWeil.tangent_and_weil_of_isAH thetaUnifAV_all Φ.key.P g _ Hm _ hA
  refine ⟨carry u₁ hM hL hw', _, rfl, hA, ?_, ?_, hg, fun a v hv hd => ?_⟩
  · intro k hk
    have h0 : (u₁.ex 0).left = eSec Φ.T.t.G := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex 0).left
    have hk' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ Φ.T.t.PP.L.U (k PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hk hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk'⟩
    have e := hfr (j PUnit.unit) (k PUnit.unit) 0 hz
    rw [c₄ _ (hle 0 j hj), h0] at e
    rw [h0] at hz
    have e' := val_rig Φ.m.cm.e_comm w Φ.T.t.PP.rig Xo.univ.t.PP.rig hrig (j PUnit.unit) (k PUnit.unit) hz
    rw [Φ.m.base] at e'
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _) (e.trans e')
  · intro k z hk
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk⟩
    obtain ⟨pt, p₁, p₂, hpt⟩ := hth (u₁.ex z).left (Over.w _)
    have e := hfr (j PUnit.unit) k z hz
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, k))) ?_
    have e₁ := hpt (j PUnit.unit) k hz
    have e₂ := c₆ (j PUnit.unit) z pt (p₁.trans (hex z)) p₂ (hle z j hj)
    rw [← e] at e₂
    exact e₁.symm.trans (e₂.trans (mul_left_comm _ _ _))
  · obtain ⟨v', ⟨t', d'⟩, -⟩ := htan a
    refine ⟨v', ?_, d'⟩
    have d := isDerivAt0_comp _ Φ.m.φ (e := fun z => (F.ex i P z).left) hex t' d'
    have o : ((show Sp (DualNumber ℂ) ⟶ _ from v'.left) ≫ Φ.m.φ) ≫ Xo.univ.t.G.hom =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ F.u i P := by
      rw [Category.assoc, Φ.m.cart.1.w, ← Category.assoc]
      exact congrArg (· ≫ _) (Over.w v')
    exact eq_of_isDerivAt0 F i hP o hv.1 d hd

theorem isMetricAt_of {y : Sp ℂ ⟶ Xo.X} {s : LB.Sec (PPx y)}
    {uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)} {N : ℝ}
    {Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ} (Φ : FibKey Xo ℂ y) {g : ℕ}
    (hg : g = Φ.key.P.g) (u : HolUnif Φ.key.P.A Φ.key.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (w : ∀ b : E →+* ℂ, Fin (Dw.mult b) → (epsR ℂ ⟶ Φ.key.P.A))
    (W : ∀ b : E →+* ℂ, Fin (Dw.mult b) → Fin g → ℂ)
    (h : SecTie Φ.m Φ.th s ∧ u.IsAH Hm χ ∧ u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧
      IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧
      (∀ b i, (w b i).left ≫ Φ.m.φ = uu b i ∧ u.IsDiff (W b i) (w b i)) ∧
      ∀ b i k, Gr b i k = Real.pi * hermForm Hm (W b k) (W b i)) : IsMetricAt y s uu N Gr := by
  subst hg
  exact ⟨Φ, u, Hm, χ, θ, Fd, w, W, h⟩

end Fibre

theorem isMetric_of_isOrtho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (ξ : ℝ), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (x : (U.X k).dom), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ) → (U.X k).IsOrtho x.1 → IsMetric (U.un k x) 1 (fun _ => ((2 * Real.pi * ξ : ℝ) : ℂ) • 1) := by
  intro E _ _ _ H Dw l Xo c σ r U ξ hσ hU hpq k x hξ hx
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := OrthoHerm.hm_eq_smul_one E H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2 Wu.c3 Wu.c4
    Wu.c5 Wu.c6 Wu.c7
  choose w hw using fun τ i => hD _ _ ((U.un k x).tan τ i) (W.der τ i)
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have hN := Wu.c9.symm
  have hG : ∀ (b : E →+* ℂ) (i j : Fin (Dw.mult b)),
      (((2 * Real.pi * ξ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) i j =
        Real.pi * hermForm Wu.Hm (Pi.single (W.e.symm ⟨b, j⟩) 1) (Pi.single (W.e.symm ⟨b, i⟩) 1) := by
    intro b i j
    rw [hH]
    simp [hermForm, Matrix.smul_mulVec, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all <;> ring
  exact isMetricAt_of Φ hg u Wu.Hm χ Wu.θ Wu.Fd w (fun b i => Pi.single (W.e.symm ⟨b, i⟩) 1)
    ⟨ht, hA, hR, hF, hFd, hN, hw, hG⟩

end GlobalTheory.OrthoMetric
