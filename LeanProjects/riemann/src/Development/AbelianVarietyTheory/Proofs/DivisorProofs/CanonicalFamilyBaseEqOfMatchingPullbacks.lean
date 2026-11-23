import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfActionCompatibleMatchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointsCorrespondMatchedPullbacksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointLiftZeroFirstCoordinate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowLeftOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.UCanon.PairBase.spMap_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : B →+* C') (g : A →+* B) :
    spMap (f.comp g) = spMap f ≫ spMap g := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

namespace GlobalTheory.UCanon.PairBase

theorem comp_pow {S : Scheme.{0}} {X Y M : Over S} [MonObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem c_pow {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R)) (y : D.X) (n : ℕ)
    (u v : T ⟶ D.P.A) (hu : u.left = T.hom ≫ (D.c y).left) (hv : v.left = T.hom ≫ (D.c (n • y)).left) : u ^ n = v := by
  have eu : u = toUnit T ≫ D.c y := Over.OverMorphism.ext (by rw [hu, Over.comp_left, Over.toUnit_left])
  have ev : v = toUnit T ≫ D.c (n • y) := Over.OverMorphism.ext (by rw [hv, Over.comp_left, Over.toUnit_left])
  rw [eu, ev, GlobalTheory.UCanon.LevLift.degPre_cocharPoint_nsmul_eq_pow_levelLift, comp_pow]

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} (L : LowBase D' c) (T : Over (Sp L.W)) (a : D'.La) (u : T ⟶ L.D.P.A)
    (hu : u.left = T.hom ≫ (L.o.etaA a).left ≫ L.φB) : u ^ l.M' = 1 := by
  have h0 : L.o.etaA 0 = 1 := by
    have h := L.o.etaA_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := L.o.etaA 0) (by rw [_root_.mul_one]; exact h.symm)
  have hn : ∀ n : ℕ, L.o.etaA (n • a) = L.o.etaA a ^ n := by
    intro n
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, L.o.etaA_add, ih, pow_succ]
  have hη : L.o.etaA a ^ l.M' = 1 := by
    rw [← hn]
    exact L.o.etaA_ker a
  let x : T ⟶ L.o.t.G := toUnit T ≫ L.o.etaA a
  have hx : x ^ l.M' = 1 := by
    rw [← comp_pow, hη, MonObj.comp_one]
  have hw : (x.left ≫ L.φB) ≫ L.D.P.A.hom = (Over.mk (T.hom ≫ 𝟙 _)).hom := by
    rw [Category.assoc, L.ab.1.1.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ 𝟙 _) ⟶ L.D.P.A := Over.homMk (x.left ≫ L.φB) hw
  have hp := GlobalTheory.FamTorsion.pow_left_of_isGrpPullback L.ab.1 x x₀ rfl l.M'
  have hx₀ : x₀ ^ l.M' = 1 := Over.OverMorphism.ext (by
    rw [hp, hx, GlobalTheory.FamTorsion.one_left_of_isGrpPullback L.ab.1 T])
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 _) := Over.homMk (𝟙 _) (by simp)
  have hue : u = e ≫ x₀ := Over.OverMorphism.ext (by
    rw [hu, Over.comp_left]
    simp [e, x₀, x, Over.toUnit_left])
  rw [hue, ← comp_pow, hx₀, MonObj.comp_one]

end GlobalTheory.UCanon.PairBase

theorem GlobalTheory.UCanon.PairBase.base_eq_of_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → (∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → f₁.comp C.b = f₂.comp C.b → f₁.comp (Cn.ψ.comp MvPolynomial.C) = f₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C Cn V _ _ _ _ hV f₁ f₂ hi₁ hi₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' hE₁ hE₂ hM hpts hact hφ hb
  obtain ⟨g, hD, hg, hxe, hoa⟩ := Cn.data
  have hβ : IsGrpPullback C.P.D.toPre.P.A Cn.L.D.P.A (spMap (Cn.ψ.comp MvPolynomial.C))
      (hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C))) := pull_grp hD
  set β : C.P.D.toPre.P.A.left ⟶ Cn.L.D.P.A.left := hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C)) with hβdef
  set π₁ : D₁.toPre.P.A.left ⟶ Cn.L.D.P.A.left := prj hD₁ ≫ β with hπ₁
  set π₂ : D₁.toPre.P.A.left ⟶ Cn.L.D.P.A.left := b.left ≫ prj hD₂ ≫ β with hπ₂
  have hp₁ : IsGrpPullback D₁.toPre.P.A Cn.L.D.P.A (spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C))) π₁ :=
    ((pull_grp hD₁).comp hβ).congr (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm rfl
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  have hp₂ : IsGrpPullback D₁.toPre.P.A Cn.L.D.P.A (spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C))) π₂ :=
    ((isGrpPullback_of_iso (asIso b)).comp ((pull_grp hD₂).comp hβ)).congr (by rw [Category.id_comp]; exact (GlobalTheory.UCanon.PairBase.spMap_comp f₂ _).symm) (by rw [hπ₂, asIso_hom])

  letI := H.starRing
  have hsq : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {θ : R →+* R'} {D' : DegPre R'} (h : IsPullDeg θ C.P.D.toPre D')
      (f : C.P.D.toPre.P.A ⟶ C.P.D.toPre.P.A) (f' : D'.P.A ⟶ D'.P.A),
      f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf θ)).map f → f'.left ≫ prj h = prj h ≫ f.left :=
    fun h f f' e => (GlobalTheory.PullDegTop.main.2.1 h f f').1 e
  have hoa' : letI := H.starRing; ∀ x, (C.P.oD.onB.act x).left ≫ β = β ≫ (Cn.L.oa.onB.act x).left :=
    fun x => (hoa x).trans (Category.assoc _ _ _).symm

  have hLB0 := GlobalTheory.T.lineBundleIso_of_action_compatible_match Xo c φ R hR C Cn V hV f₁ f₂ hi₁ hi₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' hE₁ hE₂ hM hact
  have hβL : LBIso C.P.D.toPre.P.L (Cn.L.D.P.L.pull β) := ⟨hD.w, hD.w_gen⟩
  have hC := C.P.D.toPre.P.isLB
  have hLD := Cn.L.D.P.isLB
  have hW₁ : LBIso D₁.toPre.P.L (Cn.L.D.P.L.pull π₁) :=
    LBIso.trans D₁.toPre.P.isLB (pull_isLB hC _) (pull_isLB hLD _) ⟨hD₁.w, hD₁.w_gen⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp hβL (prj hD₁) rfl)
  have hW₂ : LBIso D₂.toPre.P.L (Cn.L.D.P.L.pull (prj hD₂ ≫ β)) :=
    LBIso.trans D₂.toPre.P.isLB (pull_isLB hC _) (pull_isLB hLD _) ⟨hD₂.w, hD₂.w_gen⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp hβL (prj hD₂) rfl)
  have hLB : LBIso (Cn.L.D.P.L.pull π₁) (Cn.L.D.P.L.pull π₂) :=
    LBIso.trans (pull_isLB hLD _) D₁.toPre.P.isLB (pull_isLB hLD _) hW₁.symm
      (LBIso.trans D₁.toPre.P.isLB (pull_isLB D₂.toPre.P.isLB _) (pull_isLB hLD _) hLB0
        (GlobalTheory.PolDeg.lbIso_pull_comp hW₂ b.left hπ₂))
  choose a₁ a₂ ha₁ ha₂ hab using hact
  have hA₁ : letI := H.starRing; ∀ x, (a₁ x).left ≫ π₁ = π₁ ≫ (Cn.L.oa.onB.act x).left := by
    intro x
    have e1 := hsq hD₁ _ _ (ha₁ x)
    calc (a₁ x).left ≫ π₁ = ((a₁ x).left ≫ prj hD₁) ≫ β := (Category.assoc _ _ _).symm
      _ = prj hD₁ ≫ ((C.P.oD.onB.act x).left ≫ β) := by rw [e1, Category.assoc]
      _ = π₁ ≫ (Cn.L.oa.onB.act x).left := by rw [hoa' x, ← Category.assoc]
  have hA₂ : letI := H.starRing; ∀ x, (a₁ x).left ≫ π₂ = π₂ ≫ (Cn.L.oa.onB.act x).left := by
    intro x
    have e1 := hsq hD₂ _ _ (ha₂ x)
    have e3 : (a₁ x).left ≫ b.left = b.left ≫ (a₂ x).left := by rw [← Over.comp_left, hab x, Over.comp_left]
    have e3r : ∀ {Z : Scheme.{0}} (k : D₂.toPre.P.A.left ⟶ Z), (a₁ x).left ≫ b.left ≫ k = b.left ≫ (a₂ x).left ≫ k :=
      fun k => by rw [← Category.assoc, e3, Category.assoc]
    have e1r : ∀ {Z : Scheme.{0}} (k : C.P.D.toPre.P.A.left ⟶ Z), (a₂ x).left ≫ prj hD₂ ≫ k = prj hD₂ ≫ (C.P.oD.onB.act x).left ≫ k :=
      fun k => by rw [← Category.assoc, e1, Category.assoc]
    rw [hπ₂, e3r, e1r, hoa' x]
    simp only [Category.assoc]
  have hA₀ : ∀ x, (a₁ x).left ≫ D₁.toPre.P.A.hom = D₁.toPre.P.A.hom := fun x => Over.w (a₁ x)

  have hM1 : 1 ≤ l.M' := (GlobalTheory.LowDat.lowLevel l).A_pos
  let F₀ := AlgebraicClosure (FractionRing R)
  let F := AlgebraicClosure (FractionRing V)
  let j : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hTF : (TF (R := V) F).hom = spMap j := (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm
  have hExt : ∀ (fi : R →+* V) (ji : F₀ →+* F), TInj.Ext fi ji →
      spMap ji ≫ (TF (R := R) F₀).hom = spMap j ≫ spMap fi := by
    intro fi ji hE
    have e : ji.comp ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) = j.comp fi :=
      RingHom.ext fun r => hE r
    have e1 : (TF (R := R) F₀).hom = spMap ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) :=
      (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm
    rw [e1, ← GlobalTheory.UCanon.PairBase.spMap_comp, e, GlobalTheory.UCanon.PairBase.spMap_comp]
  have hz : ∀ (y' : C.P.D.toPre.X) (x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A) (u : Sp R ⟶ Cn.L.D.P.A.left),
      x ^ l.M' = DegPre.cF C.P.D.toPre F₀ y' → x.left ≫ β = (TF (R := R) F₀).hom ≫ u →
      ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ u ∧
        z ≫ π₂ = spMap j ≫ spMap f₂ ≫ u := by
    intro y' x u hx hxu
    obtain ⟨z, hz₁, hz₂⟩ := GlobalTheory.T.divisionPoints_correspond_matched_pullbacks R V C.P.D.toPre D₁.toPre D₂.toPre C.P.D.tau_bimult D₂.tau_bimult f₁ f₂ hD₁ hD₂
      F₀ F j₁ j₂ b φ' l.M' hM1 hpts hφ y' x hx
    have hz₁' : z.left ≫ prj hD₁ = spMap j₁ ≫ x.left := hz₁
    have hz₂' : z.left ≫ b.left ≫ prj hD₂ = spMap j₂ ≫ x.left := hz₂
    refine ⟨z.left, by rw [Over.w z, hTF], ?_, ?_⟩
    · calc z.left ≫ π₁ = (z.left ≫ prj hD₁) ≫ β := by rw [hπ₁]; simp only [Category.assoc]
        _ = (spMap j₁ ≫ (TF (R := R) F₀).hom) ≫ u := by rw [hz₁', Category.assoc, hxu, Category.assoc]
        _ = spMap j ≫ spMap f₁ ≫ u := by rw [hExt f₁ j₁ hE₁, Category.assoc]
    · calc z.left ≫ π₂ = (z.left ≫ b.left ≫ prj hD₂) ≫ β := by rw [hπ₂]; simp only [Category.assoc]
        _ = (spMap j₂ ≫ (TF (R := R) F₀).hom) ≫ u := by rw [hz₂', Category.assoc, hxu, Category.assoc]
        _ = spMap j ≫ spMap f₂ ≫ u := by rw [hExt f₂ j₂ hE₂, Category.assoc]

  have hlift : ∀ (y' : C.P.D.toPre.X) (u : Sp R ⟶ Cn.L.D.P.A.left),
      u ≫ Cn.L.D.P.A.hom = spMap (Cn.ψ.comp MvPolynomial.C) →
      (∀ w w' : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A,
        w.left = (TF (R := R) F₀).hom ≫ u →
        w'.left = (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left →
        w ^ l.M' = w') →
      ∃ x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A, x ^ l.M' = DegPre.cF C.P.D.toPre F₀ y' ∧
        x.left ≫ β = (TF (R := R) F₀).hom ≫ u := by
    intro y' u hu H'
    have hw0 : ((TF (R := R) F₀).hom ≫ u) ≫ Cn.L.D.P.A.hom =
        (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) := by rw [Category.assoc, hu]
    let x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A := Over.homMk (hβ.1.lift _ _ hw0) (hβ.1.lift_snd _ _ _)
    have hxβ : x.left ≫ β = (TF (R := R) F₀).hom ≫ u := hβ.1.lift_fst _ _ _
    refine ⟨x, ?_, hxβ⟩
    let w : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A :=
      Over.homMk ((TF (R := R) F₀).hom ≫ u) hw0
    have hc0 : ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left) ≫
        Cn.L.D.P.A.hom = (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) := by
      simp only [Category.assoc]
      erw [Over.w (Cn.L.D.c (l.M' • Cn.e y'))]
      simp
    let w' : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A := Over.homMk _ hc0
    have hw := H' w w' rfl rfl
    have hpow := GlobalTheory.FamTorsion.pow_left_of_isGrpPullback hβ x w hxβ.symm l.M'
    apply Over.OverMorphism.ext
    apply hβ.1.hom_ext
    · rw [← hpow, hw]
      have hcp := hD.c_pr y'
      show (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left =
        (toUnit (TF (R := R) F₀) ≫ C.P.D.toPre.c y').left ≫ β
      rw [Over.comp_left, Over.toUnit_left, Category.assoc]
      erw [hcp]
      rw [hxe]
      rfl
    · rw [Over.w, Over.w]
  have hEta : ∀ a, ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧
      z ≫ π₁ = spMap j ≫ spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB ∧
      z ≫ π₂ = spMap j ≫ spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB := by
    intro a
    have hu : (spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB) ≫ Cn.L.D.P.A.hom =
        spMap (Cn.ψ.comp MvPolynomial.C) := by
      rw [Category.assoc, Category.assoc, Cn.L.ab.1.1.w, Category.comp_id, Over.w (Cn.L.o.etaA a)]
      simp
    obtain ⟨x, hx, hxu⟩ := hlift 0 _ hu (fun w w' hw hw' => by
      have e1 : w ^ l.M' = 1 := GlobalTheory.UCanon.PairBase.etaA_pow Cn.L _ a w (by rw [hw]; simp only [Over.mk_hom, Category.assoc])
      have h0 : w'.left = (Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C))).hom ≫ (Cn.L.D.c 0).left := by
        rw [hw', map_zero, smul_zero]; simp only [Over.mk_hom, Category.assoc]
      have e2 := GlobalTheory.UCanon.PairBase.c_pow Cn.L.D _ 0 0 w' w' h0 (by rw [h0, zero_smul])
      rw [pow_zero] at e2
      rw [e1, e2])
    obtain ⟨z, hz0, hz1, hz2⟩ := hz 0 x _ hx hxu
    refine ⟨z, hz0, ?_, ?_⟩
    · rw [hz1, GlobalTheory.UCanon.PairBase.spMap_comp f₁ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
    · rw [hz2, GlobalTheory.UCanon.PairBase.spMap_comp f₂ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
  have hCp : ∀ y, ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧
      z ≫ π₁ = spMap j ≫ spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left ∧
      z ≫ π₂ = spMap j ≫ spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left := by
    intro y
    have hu : (spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c y).left) ≫ Cn.L.D.P.A.hom =
        spMap (Cn.ψ.comp MvPolynomial.C) := by
      rw [Category.assoc, Over.w (Cn.L.D.c y)]
      simp
    obtain ⟨x, hx, hxu⟩ := hlift (Cn.e.symm y) _ hu (fun w w' hw hw' =>
      GlobalTheory.UCanon.PairBase.c_pow Cn.L.D _ y l.M' w w' (by rw [hw]; simp only [Over.mk_hom, Category.assoc])
        (by rw [hw', Cn.e.apply_symm_apply]; simp only [Over.mk_hom, Category.assoc]))
    obtain ⟨z, hz0, hz1, hz2⟩ := hz _ x _ hx hxu
    refine ⟨z, hz0, ?_, ?_⟩
    · rw [hz1, GlobalTheory.UCanon.PairBase.spMap_comp f₁ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
    · rw [hz2, GlobalTheory.UCanon.PairBase.spMap_comp f₂ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
  have hbase : (f₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = (f₂.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b := by
    have e : ∀ f : R →+* V, (f.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = f.comp C.b := fun f => by
      rw [← Cn.base]; rfl
    rw [e, e, hb]
  exact (GlobalTheory.UCanon.FineAgree.main Cn.L V _ _ hbase D₁.toPre.P.A π₁ π₂ (fun x => (a₁ x).left) hp₁ hp₂ hA₁ hA₂ hA₀ hLB F j hj
    hEta hCp).1
