import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushHomBijective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraTail
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.TorsExtend

theorem exists_section_of_isFinite {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ Sp R) [IsFinite p] (y : Sp K ⟶ Z)
    (h : y ≫ p = spMap (algebraMap R K)) : ∃ x : Sp R ⟶ Z, spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 _ := by
  first
  | exact @_root_.GlobalTheory.FactorAndSection.exists_section
  | exact _root_.GlobalTheory.FactorAndSection.exists_section
  | (apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorAndSection.exists_section <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorAndSection.exists_section ..)

theorem pow_eq_one_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (z : T ⟶ G) :
    z ^ n = 1 ↔ z.left ≫ (mulA G n).left = T.hom ≫ (η[G]).left := by
  have e : (1 : T ⟶ G).left = T.hom ≫ (η[G]).left := by
    rw [Hom.one_def]; simp
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, ← e]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩

theorem exists_torsion_section (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n)
    {s : Sp K ⟶ Sp R} (hs : s = spMap (algebraMap R K)) (y : Over.mk s ⟶ P.A) (hy : y ^ n = 1) :
    ∃ x : baseOver (Sp R) ⟶ P.A, x ^ n = 1 ∧ spMap (algebraMap R K) ≫ x.left = y.left := by
  subst hs
  haveI := (hL.mulN _ P n hn).1
  let e : Sp R ⟶ P.A.left := (η[P.A]).left
  have he : e ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  obtain ⟨x, h₁, h₂⟩ := exists_section_of_isFinite (pullback.snd (mulA P.A n).left e)
    (pullback.lift y.left (spMap (algebraMap R K)) ((pow_eq_one_iff _ _ _).1 hy)) (pullback.lift_snd _ _ _)
  have h₃ : (x ≫ pullback.fst (mulA P.A n).left e) ≫ (mulA P.A n).left = e := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]
  refine ⟨Over.homMk (x ≫ pullback.fst _ _) ?_, (pow_eq_one_iff _ _ _).2 (h₃.trans (Category.id_comp _).symm), ?_⟩
  · rw [← Over.w (mulA P.A n), ← Category.assoc, h₃]
    exact he
  · show _ ≫ x ≫ pullback.fst _ _ = _
    rw [← Category.assoc, h₁, pullback.lift_fst]

theorem torsion_section_eq (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K]
    (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R)) {x y : baseOver (Sp R) ⟶ P.A} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (s : Sp K ⟶ Sp R) (h : s ≫ x.left = s ≫ y.left) : x = y := by
  haveI := (hL.mulN _ P n hn).1
  haveI := (hL.mulN _ P n hn).2.2.2.1 (by simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  haveI : PreconnectedSpace (Sp R) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
  exact Over.OverMorphism.ext (eq_of_preconnected_of_unramified (T := Sp R) (mulA P.A n).left
    (((pow_eq_one_iff _ _ _).1 hx).trans ((pow_eq_one_iff _ _ _).1 hy).symm) s h)

theorem exists_labelled (hL : Laws) {R R₀ Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] [CommRing R₀] (j₀ : R₀ →+* Ω)
    (P : PolAV (Sp R₀)) (P' : PolAV (Sp R)) (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left)
    (ha : IsGrpPullback P₀.A P.A (spMap j₀) a) (ha' : IsGrpPullback P₀.A P'.A (spMap (algebraMap R Ω)) a')
    (hl : LBIso P₀.L (P.L.pull a)) (hl' : LBIso P₀.L (P'.L.pull a')) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R))
    {M : Type} [AddCommGroup M] (hM : ∀ x : M, n • x = 0) (pt : M → (baseOver (Sp R₀) ⟶ P.A))
    (add : ∀ x y, pt (x + y) = pt x * pt y)
    (bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R₀) (z : Over.mk x ⟶ P.A), z ^ n = 1 →
      ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₀)) ≫ pt c = z) :
    ∃ pt' : M → (baseOver (Sp R) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P'.A), z ^ n = 1 →
        ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt' c = z) ∧
      (∀ x y (c₀ : R₀ˣ) (c : Rˣ), j₀ c₀ = algebraMap R Ω c → WeilIs P.A P.L n (pt x) (pt y) (unitOn c₀) →
        WeilIs P'.A P'.L n (pt' x) (pt' y) (unitOn c)) ∧
      ∀ x, ∃ w0 : Sp Ω ⟶ P₀.A.left, w0 ≫ a = spMap j₀ ≫ (pt x).left ∧
        w0 ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := by
  haveI := P₀.isAb.comm
  haveI := P'.isAb.proper
  have hi := IsFractionRing.injective R Ω
  have hb := GenericKTriv.pushHom_bijective ha (baseOver (Sp Ω))
  have hb' := GenericKTriv.pushHom_bijective ha' (baseOver (Sp Ω))
  let h₀ : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (spMap j₀) (by simp)
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap (algebraMap R Ω)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R Ω)) (by simp)
  have zero : pt 0 = 1 := by
    have := add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have smul : ∀ (k : ℕ) x, pt (k • x) = pt x ^ k := fun k x => by
    induction k with
    | zero => rw [zero_smul, zero, pow_zero]
    | succ k ih => rw [succ_nsmul, add, ih, pow_succ]
  have tor : ∀ x, pt x ^ n = 1 := fun x => by rw [← smul, hM, zero]
  choose w hw using fun x => hb.2 (h₀ ≫ pt x)
  have torw : ∀ x, w x ^ n = 1 := fun x => hb.1 (by
    rw [map_pow, hw, map_one, ← MonObj.comp_pow, tor, MonObj.comp_one])
  have addw : ∀ x y, w (x + y) = w x * w y := fun x y => hb.1 (by
    rw [map_mul, hw, hw, hw, add, MonObj.comp_mul])
  choose pt' tor' hpt' using fun x => exists_torsion_section hL P' hn (Category.id_comp _)
    (pushHom ha' (baseOver (Sp Ω)) (w x)) (by rw [← map_pow, torw, map_one])
  have hpt : ∀ x, h ≫ pt' x = pushHom ha' (baseOver (Sp Ω)) (w x) := fun x => Over.OverMorphism.ext (hpt' x)
  have e₀ : ∀ x, (w x).left ≫ a = spMap j₀ ≫ (pt x).left := fun x => congrArg (fun q => q.left) (hw x)
  have e₁ : ∀ x, (w x).left ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := fun x => (hpt' x).symm
  let F := AlgebraicClosure Ω
  let t : Sp F ⟶ Sp Ω := spMap (algebraMap Ω F)
  let g : Over.mk (t ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (t ≫ spMap j₀) (by simp)
  have torg : ∀ x, (g ≫ pt x) ^ n = 1 := fun x => by rw [← MonObj.comp_pow, tor, MonObj.comp_one]
  have inj : Function.Injective pt' := fun x y e => by
    have e₂ : w x = w y := hb'.1 (by rw [← hpt, ← hpt, e])
    refine (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (Over.OverMorphism.ext ?_) rfl
    show (t ≫ spMap j₀) ≫ (pt x).left = (t ≫ spMap j₀) ≫ (pt y).left
    rw [Category.assoc, Category.assoc, ← e₀, ← e₀, e₂]
  have ne : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R), (n : K) ≠ 0 := fun K _ s => by
    have := hu.map (Spec.preimage s).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have card : Nat.card M = n ^ (2 * P'.g) := by
    rw [← (hL.mulN _ P' n hn).2.2.2.2 F (t ≫ spMap (algebraMap R Ω)) (ne F (t ≫ spMap (algebraMap R Ω))),
      GenericKTriv.card_torsion ha' t rfl, ← GenericKTriv.card_torsion ha t rfl]
    refine Nat.card_eq_of_bijective (fun x => ⟨g ≫ pt x, torg x⟩) ⟨fun x y e => ?_, fun z => ?_⟩
    · exact (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (congrArg Subtype.val e) rfl
    · obtain ⟨c, hc, -⟩ := bij F (t ≫ spMap j₀) z.1 z.2
      exact ⟨c, Subtype.ext hc⟩
  refine ⟨pt', fun x y => ?_, fun K _ _ s z hz => ?_, fun x y c₀ c hc H => ?_, fun x => ⟨(w x).left, e₀ x, e₁ x⟩⟩
  · have e : h ≫ pt' (x + y) = h ≫ (pt' x * pt' y) := by
      rw [MonObj.comp_mul, hpt, hpt, hpt, addw, map_mul]
    exact over_points_ext_of_injective _ P'.A R Ω _ hi _ _ _ (congrArg (fun q => q.left) e)
  · have hc := (hL.mulN _ P' n hn).2.2.2.2 K s (ne K s)
    let Φ : M → {x : Over.mk s ⟶ P'.A // x ^ n = 1} := fun c =>
      ⟨(Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ pt' c, by
        rw [← MonObj.comp_pow, tor', MonObj.comp_one]⟩
    have hΦ : Function.Injective Φ := fun c c' e =>
      inj (torsion_section_eq hL P' hn hu (tor' c) (tor' c') s (congrArg (fun q => q.1.left) e))
    have : Finite {x : Over.mk s ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    obtain ⟨c, e⟩ := (hΦ.bijective_of_nat_card_le (by rw [hc, card])).2 ⟨z, hz⟩
    exact ⟨c, congrArg Subtype.val e, fun c' e' => hΦ ((Subtype.ext e').trans e.symm)⟩
  · refine MumPair.weilIs_of_spread Ω R _ hi P₀ P' a' ha' hl' n (w x) (w y) _ _ c hn (e₁ x) (e₁ y) (tor' x) (tor' y) ?_
    have H₁ := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h₀ H
    have H₂ := (weilIs_grpPullback_of_comm' (Sp R₀) (Sp Ω) P.A P₀.A (spMap j₀) a P.L P₀.L P.isLB P₀.isLB ha hl
      (baseOver (Sp Ω)) n (w x) (w y) (h₀ ≫ pt x) (h₀ ≫ pt y) _ (e₀ x).symm (e₀ y).symm).2 H₁
    have e := SpreadLevel.appTop_unitOn j₀ c₀ (Units.map (algebraMap R Ω).toMonoidHom c) hc
    exact e ▸ H₂

theorem isIntegrallyClosed_ringOn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) :
    IsIntegrallyClosed (M.ringOn U) := by
  haveI := RatModel.isFractionRing_ringOn hU hne
  refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => ?_⟩, rfl⟩
  have := RatModel.isIntegrallyClosed_O hM z
  letI : Algebra (M.ringOn U) (M.O z) := (Subalgebra.inclusion (RatModel.ringOn_le_O hz)).toRingHom.toAlgebra
  haveI : IsScalarTower (M.ringOn U) (M.O z) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := M.O z))
  exact hy ▸ y.2

theorem exists_labelled_on_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  intro g n F W Z i X₁ U P' P₀ a a' hU hne ha ha' hl hl'
  obtain ⟨⟨hL, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI := RatModel.isFractionRing_ringOn hU hne
  haveI := isIntegrallyClosed_ringOn X₁.M ((isNormalScheme_iff_pred _).1 X₁.normal) hU hne
  haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  haveI : IsNoetherianRing (X₁.M.ringOn U) := isNoetherianRing_of_fg (fg_ringOn_of_isAffineOpen _ _ X₁.M U hU hne)
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (le_trans one_le_two X₁.S.N_ge)
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : X₁.M.ringOn U) := by
    have := X₁.S.unit.map (algebraMap X₁.o₁ (X₁.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', h₁, h₂, h₃, h₄⟩ := exists_labelled hL X₁.S.R.val.toRingHom X₁.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X₁.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.pt_bij
  refine ⟨pt', h₁, h₂, fun x y c hc => ?_, h₄⟩
  obtain ⟨c₀, hc₀⟩ := ((X₁.S.prim.isUnit (by positivity)).pow (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)).map
    (algebraMap X₁.o₁ X₁.S.R)
  refine h₃ x y c₀ c ?_ (X₁.ρ.weil x y c₀ hc₀)
  rw [hc₀, hc]
  rfl

end GlobalTheory.Poinc.TorsExtend
