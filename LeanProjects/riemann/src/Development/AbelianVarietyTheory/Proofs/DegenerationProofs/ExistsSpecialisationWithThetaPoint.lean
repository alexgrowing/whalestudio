import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationExtendsOverDvrGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.Specialise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem exists_pat (h₁ : Laws) (h₂ : Laws2) {C : Type} [NormedField C] (o : Full D C) (M : Mdl o)
    (hp : IsProper M.t.G.hom) : letI := H.starRing
    ∃ (T : CM.PAT H (Sp M.W)) (φ : o.P.A.left ⟶ T.t.G.left),
      IsGrpPullback o.P.A T.t.G (jFK (R := M.W) C ≫ jK M.W) φ ∧ LBIso o.P.L (T.t.PP.L.pull φ) ∧
      ∀ a, (o.oa.act a).left ≫ φ = φ ≫ (T.t.act.act a).left := by
  letI := H.starRing
  have hA : IsAbelianScheme M.t.G := ⟨inferInstance, M.t.semi.smooth, hp, M.t.semi.geomConnected⟩
  haveI : IsDiscreteValuationRing M.W := M.cdv.1
  haveI := M.P.U.gen_hom
  haveI : IsMonHom M.P.U.gen.symm.hom := inferInstanceAs (IsMonHom M.P.U.gen.inv)
  let ψ : M.P.A.A.left ⟶ M.t.G.left := M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W)
  have hψ : IsGrpPullback M.P.A.A M.t.G (jK M.W) ψ :=
    ((isGrpPullback_of_iso M.P.U.gen.symm).comp (isGrpPullback_pullback M.t.G (jK M.W))).congr (Category.id_comp _) rfl
  have hi : M.P.U.gen.inv.left ≫ M.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hL : LBIso M.P.A.L (M.t.PP.L.pull ψ) := by
    have e : LBIso (M.P.A.L.pull M.P.U.gen.hom.left) (M.t.PP.L.pull (pullback.fst M.t.G.hom (jK M.W))) := by
      rw [← M.P.bundle]; exact M.P.U.ext
    exact LBIso.chartPull (chartPullSec _ _ _ hi) (chartPullSame _ _ _ _ _ fun _ => rfl) e
  obtain ⟨N, hN⟩ := AbPackage.exists_cp h₁.globalFns hA M.t.PP ⟨M.t.cub.t, M.t.cub.isGen⟩ (by
    rw [← M.P.bundle]; exact ⟨M.P.U.symG, M.P.U.symG_gen⟩)
  obtain ⟨ha, hk⟩ := GlobalTheory.T.polarisation_extends_over_dvr_goodReduction h₁ h₂ M.W (FractionRing M.W) M.P.A M.t.G N ψ hA hψ (by rw [hN]; exact hL)
  rw [hN] at ha hk
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim M.W M.t.G hA
  have hs : Out.Sym M.t.G M.t.PP.L := by
    obtain ⟨-, w, hw, -⟩ := M.t.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  refine ⟨⟨M.t, hA, g, hg, hs, ha, hk⟩, M.φ ≫ ψ, M.cart.comp hψ, ?_, fun a => ?_⟩
  · exact M.lb.trans o.P.isLB (pull_isLB M.P.A.isLB _) (pull_isLB M.t.PP.isLB _)
      (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSame _ _ _ _ _ fun _ => rfl) hL)
  · have e : M.P.oA.act a ≫ M.P.U.gen.inv = M.P.U.gen.inv ≫ (Over.pullback (jK M.W)).map (M.t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact (Iso.eq_inv_comp _).2 (M.P.lin.ext a).symm
    have e' := congrArg (fun q => q.left ≫ pullback.fst M.t.G.hom (jK M.W)) e
    have e₂ : ((Over.pullback (jK M.W)).map (M.t.act.act a)).left ≫ pullback.fst M.t.G.hom (jK M.W) =
      pullback.fst M.t.G.hom (jK M.W) ≫ (M.t.act.act a).left := pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc] at e'
    rw [← Category.assoc, M.act, Category.assoc, Category.assoc]
    exact congrArg (M.φ ≫ ·) (e'.trans ((congrArg (_ ≫ ·) e₂).trans (Category.assoc _ _ _).symm))

theorem pushHom_bijective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) :=
  ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm)),
    fun y => ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem preHom_bijective {B : Scheme.{0}} (G : Over B) [GrpObj G] [IsProper G.hom] {C : Type} [Field C]
    (S : ValuationSubring C) {s : Sp S ⟶ B} {x : Sp C ⟶ B} (hx : spMap S.subtype ≫ s = x) :
    Function.Bijective (preHom (G := G) (Over.homMk (spMap S.subtype) hx : Over.mk x ⟶ Over.mk s)) := by
  constructor
  · intro a b e
    have e' : spMap S.subtype ≫ a.left = spMap S.subtype ≫ b.left := congrArg (fun q => q.left) e
    let Q : ValuativeCommSq G.hom :=
      { R := S, K := C, i₁ := spMap S.subtype ≫ a.left, i₂ := s,
        commSq := ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w a))⟩ }
    have := (IsSeparated.valuativeCriterion G.hom Q).elim ⟨a.left, rfl, Over.w a⟩ ⟨b.left, e'.symm, Over.w b⟩
    exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)
  · intro y
    have hE : ValuativeCriterion.Existence G.hom := by
      have h : UniversallyClosed G.hom := inferInstance
      rw [UniversallyClosed.eq_valuativeCriterion] at h
      exact h.1
    let Q : ValuativeCommSq G.hom :=
      { R := S, K := C, i₁ := y.left, i₂ := s, commSq := ⟨(Over.w y).trans hx.symm⟩ }
    obtain ⟨⟨l, h1, h2⟩⟩ := hE Q
    exact ⟨Over.homMk l h2, Over.OverMorphism.ext h1⟩

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom (c : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_bijective {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem exists_root {C κ : Type} [Field C] [Field κ] [CharZero κ] (S : ValuationSubring C) (res : S →+* κ) {n : ℕ}
    (hn : 0 < n) {z : Cˣ} (hz : IsPrimitiveRoot z n) :
    ∃ u : Sˣ, Units.map S.subtype.toMonoidHom u = z ∧ IsPrimitiveRoot (Units.map res.toMonoidHom u) n := by
  have h₁ : (z : C) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz.pow_eq_one, Units.val_one]
  have hm : (z : C) ∈ S := by
    rcases S.mem_or_inv_mem z with h | h
    · exact h
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      have : (z : C) = (z : C)⁻¹ ^ k := by
        rw [inv_pow]
        exact eq_inv_of_mul_eq_one_right (by rw [← pow_succ, h₁])
      rw [this]
      exact pow_mem h k
  have h₂ : IsPrimitiveRoot (⟨z, hm⟩ : S) n :=
    IsPrimitiveRoot.of_map_of_injective (f := S.subtype) (IsPrimitiveRoot.coe_units_iff.2 hz) Subtype.val_injective
  haveI : NeZero (n : κ) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  refine ⟨(h₂.isUnit hn.ne').unit, Units.ext rfl, IsPrimitiveRoot.coe_units_iff.1 ?_⟩
  have h₃ := (h₂.isRoot_cyclotomic hn).map (f := res)
  rw [Polynomial.map_cyclotomic] at h₃
  exact Polynomial.isRoot_cyclotomic_iff.1 h₃

theorem exists_eq_smul_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) {a : D.La} (h : ∀ b, (n : ℤ) ∣ D.EF a b) :
    ∃ b, a = n • b := by
  choose k hk using h
  have h₀ : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  let f : D.La →+ ℤ := AddMonoidHom.mk' k fun b c => mul_left_cancel₀ h₀ (by rw [← hk, map_add, hk, hk, mul_add])
  obtain ⟨b, hb⟩ := D.unimod.2 f.toIntLinearMap
  refine ⟨b, D.unimod.1 (LinearMap.ext fun c => ?_)⟩
  rw [map_nsmul, LinearMap.smul_apply, hb, hk, nsmul_eq_mul]
  rfl

theorem exists_tateIso (h₁ : Laws) {B : Scheme.{0}} [IsLocallyNoetherian B] (P : PolAV B) (act : 𝓞 E → (P.A ⟶ P.A))
    {C κ : Type} [Field C] [IsAlgClosed C] [Field κ] [IsAlgClosed κ] [CharZero κ] (S : ValuationSubring C)
    (res : S →+* κ) {s : Sp S ⟶ B} {x : Sp C ⟶ B} {y : Sp κ ⟶ B} (hx : spMap S.subtype ≫ s = x)
    (hy : spMap res ≫ s = y)
    (I : TateIso D C (Over.mk x ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => WeilIs P.A P.L n g g' (unitOn c))) :
    ∃ (I' : TateIso D κ (Over.mk y ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => WeilIs P.A P.L n g g' (unitOn c)))
      (ev : ℕ → D.La → (Over.mk s ⟶ P.A)),
      (∀ n a, (Over.homMk (spMap S.subtype) hx : Over.mk x ⟶ Over.mk s) ≫ ev n a = I.ev n a) ∧
      (∀ n a, (Over.homMk (spMap res) hy : Over.mk y ⟶ Over.mk s) ≫ ev n a = I'.ev n a) ∧
      ∀ n, 0 < n → ∀ z : S, (z : C) = I.ζ n → (I'.ζ n : κ) = res z := by
  haveI := P.isAb.proper
  haveI : CharZero C := charZero_of_isPrimitiveRoot I.ζ_prim
  let jx : Over.mk x ⟶ Over.mk s := Over.homMk (spMap S.subtype) hx
  let jy : Over.mk y ⟶ Over.mk s := Over.homMk (spMap res) hy
  let e : (Over.mk s ⟶ P.A) ≃* (Over.mk x ⟶ P.A) := MulEquiv.ofBijective _ (preHom_bijective P.A S hx)
  have he : ∀ a, e a = jx ≫ a := fun _ => rfl
  let r : (Over.mk s ⟶ P.A) →* (Over.mk y ⟶ P.A) := preHom jy
  let F : (Over.mk x ⟶ P.A) →* (Over.mk y ⟶ P.A) := r.comp e.symm.toMonoidHom
  have hF : ∀ a, F (e a) = jy ≫ a := fun a => congrArg r (e.symm_apply_apply a)
  have hz : ∀ n : ℕ, ∃ u : Sˣ, 0 < n → Units.map S.subtype.toMonoidHom u = I.ζ n ∧
      IsPrimitiveRoot (Units.map res.toMonoidHom u) n := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨u, hu⟩ := exists_root S res hn (I.ζ_prim n hn)
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hn⟩
  choose ζ hζ using hz
  have hi : Function.Injective (Units.map S.subtype.toMonoidHom) := Units.map_injective Subtype.val_injective
  have hw : ∀ (n : ℕ) a b (c : Sˣ), a ^ n = 1 → b ^ n = 1 →
      WeilIs P.A P.L n a b (unitOn (Units.map S.subtype.toMonoidHom c)) →
      WeilIs P.A P.L n (F a) (F b) (unitOn (Units.map res.toMonoidHom c)) := fun n a b c ha hb H => by
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    obtain ⟨d, hd, -⟩ := (h₁.weil B P n (Over.mk s)).1 a b (e.injective (by rw [map_pow, ha, map_one]))
      (e.injective (by rw [map_pow, hb, map_one]))
    obtain ⟨u, rfl⟩ := unitOn_bijective.2 d
    have q := CommPairing.weilIs_pull h₁.globalFns P.isAb P.isLB jx hd
    have q' := CommPairing.weilIs_pull h₁.globalFns P.isAb P.isLB jy hd
    have e₁ := ((h₁.weil B P n (Over.mk x)).1 _ _ ha hb).unique q H
    obtain rfl : u = c := hi (unitOn_bijective.1 ((map_unitOn _ _).symm.trans e₁))
    rw [hF, hF, ← map_unitOn]
    exact q'
  have ht : ∀ n, 0 < n → ∀ a, I.ev n a ^ n = 1 := fun n hn a => (I.onto n hn _).2 ⟨a, rfl⟩
  have ht' : ∀ n, 0 < n → ∀ a, F (I.ev n a) ^ n = 1 := fun n hn a => by rw [← map_pow, ht n hn, map_one]
  have hiso : ∀ n : ℕ, 0 < n → ∀ a b, WeilIs P.A P.L n (F (I.ev n a)) (F (I.ev n b))
      (unitOn (Units.map res.toMonoidHom (ζ n) ^ D.EF a b)) := fun n hn a b => by
    rw [← map_zpow]
    refine hw n _ _ _ (ht n hn a) (ht n hn b) ?_
    rw [map_zpow, (hζ n hn).1]
    exact I.isom n hn a b
  have hker : ∀ n, 0 < n → ∀ a, F (I.ev n a) = 1 → ∃ b, a = n • b := fun n hn a ha =>
    exists_eq_smul_of_dvd D hn fun b => by
      have q := hiso n hn a b
      rw [ha] at q
      have q₂ := (h₁.weil B P n (Over.mk y)).2.1 _ _ _ _ _ q q
      rw [_root_.mul_one] at q₂
      have q₃ := ((h₁.weil B P n (Over.mk y)).1 _ _ (one_pow n) (ht' n hn b)).unique q₂ q
      have q₄ := mul_eq_left.1 q₃
      exact ((hζ n hn).2.zpow_eq_one_iff_dvd _).1 (unitOn_bijective.1 (q₄.trans (map_one _).symm))
  refine ⟨{ ζ := fun n => Units.map res.toMonoidHom (ζ n)
            ζ_prim := fun n hn => (hζ n hn).2
            ζ_pow := fun n m hn hm => ?_
            ev := fun n a => F (I.ev n a)
            add := fun n a b => by rw [I.add, map_mul]
            lin := fun n c a => ?_
            ker := fun n hn a => ⟨hker n hn a, fun h => by rw [(I.ker n hn a).2 h, map_one]⟩
            onto := fun n hn z => ⟨fun hz => ?_, fun ⟨a, ha⟩ => ha ▸ ht' n hn a⟩
            tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm]
            isom := hiso }, fun n a => e.symm (I.ev n a), fun n a => e.apply_symm_apply _, fun _ _ => rfl,
    fun n hn z hz => ?_⟩
  · rw [← map_pow]
    congr 1
    apply hi
    rw [map_pow, (hζ _ (Nat.mul_pos hn hm)).1, (hζ n hn).1, I.ζ_pow n m hn hm]
  · rw [I.lin]
    obtain ⟨g, hg⟩ := e.surjective (I.ev n a)
    rw [← hg, hF, he, Category.assoc, ← he, hF, Category.assoc]
  · have c₁ := (h₁.mulN B P n hn).2.2.2.2 C x (Nat.cast_ne_zero.2 hn.ne')
    have c₂ := (h₁.mulN B P n hn).2.2.2.2 κ y (Nat.cast_ne_zero.2 hn.ne')
    let f : {g : Over.mk x ⟶ P.A // g ^ n = 1} → {g : Over.mk y ⟶ P.A // g ^ n = 1} :=
      fun g => ⟨F g.1, by rw [← map_pow, g.2, map_one]⟩
    have hf : Function.Injective f := fun a b h => by
      have h' : F a.1 = F b.1 := congrArg Subtype.val h
      obtain ⟨c, hc⟩ := (I.onto n hn (a.1 / b.1)).1 (by rw [div_pow, a.2, b.2, div_one])
      have := (I.ker n hn c).2 (hker n hn c (by rw [hc, map_div, h', div_self']))
      exact Subtype.ext (div_eq_one.1 (hc.symm.trans this))
    haveI : Finite {g : Over.mk y ⟶ P.A // g ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
    obtain ⟨g, hg⟩ := (hf.bijective_of_nat_card_le (by rw [c₁, c₂])).2 ⟨z, hz⟩
    obtain ⟨a, ha⟩ := (I.onto n hn g.1).1 g.2
    exact ⟨a, (congrArg F ha).trans (congrArg Subtype.val hg)⟩
  · have : z = ζ n := Subtype.ext (hz.trans (congrArg Units.val (hζ n hn).1).symm)
    rw [this]
    rfl

theorem exists_isThetaPt_local (h₁ : Laws) (h₂ : Laws2) {B : Scheme.{0}} [IsLocallyNoetherian B] (P : PolAV B)
    {R : Type} [CommRing R] [IsLocalRing R] (s : Sp R ⟶ B) {k : ℕ} (hk : Odd k) (hu : IsUnit (k : R)) {J : Type}
    (x : J → (Over.mk s ⟶ P.A)) (hx : ∀ i, x i ^ k ^ 2 = 1) :
    ∃ w : J → R, IsThetaPt P k x fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i) := by
  have hG := h₁.globalFns
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨α₀, hα₀⟩ := h₁.mulPull B P k
  obtain ⟨V, hV, b, hb⟩ := h₂.secBaseChangeAny B P 1 le_rfl (s (IsLocalRing.closedPoint R))
  obtain ⟨t, rfl⟩ : ∃ t : Sp R ⟶ (overRes (T := baseOver B) V).left, t ≫ (overRes (T := baseOver B) V).hom = s :=
    ⟨IsOpenImmersion.lift V.ι s (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact (IsLocalRing.specializes_closedPoint (R := R) p).mem_open (s ⁻¹ᵁ V).isOpen hV),
      (congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th, hth⟩ := ThetaLocal.exists_generator _ hsp
  obtain ⟨v, hv⟩ := ThetaLocal.exists_isThetaPt P k hk α₀ hα₀ (T := baseAt t) (by
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      rwa [map_natCast] at this) x th hth fun i => by
    obtain ⟨U, hU, θ, hθ⟩ := (sym B P (k ^ 2) hk.pow (baseAt t) (x i) (hx i)).1 (IsLocalRing.closedPoint R)
    obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
    let h : baseAt t ⟶ overRes (T := baseAt t) ⊤ := Over.homMk (Sp R).topIso.inv (by
      show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ _ = _
      rw [Scheme.toIso_inv_ι_assoc])
    have hh : h ≫ overResι ⊤ = 𝟙 _ := Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB h hθ
    rw [← Category.assoc, hh, Category.id_comp] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v i), ?_⟩
  convert hv using 2 with a
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (v a)

theorem isThetaPt_map (h₂ : Laws2) {B : Scheme.{0}} (P : PolAV B) {R K : Type} [CommRing R] [CommRing K] (j : R →+* K)
    {s : Sp R ⟶ B} {x : Sp K ⟶ B} (hx : spMap j ≫ s = x) {k : ℕ} {J : Type} {p : J → (Over.mk s ⟶ P.A)} {w : J → R}
    (H : IsThetaPt P k p fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i)) :
    IsThetaPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (j (w i)) := by
  have : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  have Q := ThetaBaseChange.isThetaPt_pull P h₂.secBaseChangeAny (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) H
  convert Q using 2 with a
  exact congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

theorem isThetaPt_mul {B : Scheme.{0}} (P : PolAV B) {K : Type} [Field K] {x : Sp K ⟶ B} {k : ℕ} {J : Type}
    {p : J → (Over.mk x ⟶ P.A)} {w : J → K} (H : IsThetaPt P k p fun i => fnOf (w i)) {c : K} (hc : c ≠ 0) :
    IsThetaPt P k p fun i => fnOf (c * w i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun q => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w', u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 q
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((overRes (T := Over.mk x) V).left, ⊤)ˣ, u'.val = V.ι.appTop.hom (fnOf c) :=
    ((IsUnit.mk0 c hc).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w', u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e1 : V.ι.appTop.hom (fnOf (c * w i)) = V.ι.appTop.hom (fnOf c) * V.ι.appTop.hom (fnOf (w i)) :=
    (congrArg V.ι.appTop.hom (map_mul _ _ _)).trans (map_mul _ _ _)
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom (fnOf c) * y) (k8 i)

theorem exists_res_eq_mul {C κ J : Type} [Field C] [Field κ] (S : ValuationSubring C) (res : S →+* κ) {v w : J → S}
    {c : Cˣ} (h : ∀ i, (v i : C) = c * w i) (hv : ∃ i, res (v i) ≠ 0) (hw : ∃ i, res (w i) ≠ 0) :
    ∃ d : κ, d ≠ 0 ∧ ∀ i, res (v i) = d * res (w i) := by
  obtain ⟨a, ha⟩ := hv
  obtain ⟨b, hb⟩ := hw
  rcases S.mem_or_inv_mem c with hc | hc
  · have e : ∀ i, res (v i) = res ⟨c, hc⟩ * res (w i) := fun i => by
      rw [← map_mul]; exact congrArg res (Subtype.ext (h i))
    exact ⟨_, left_ne_zero_of_mul (e a ▸ ha), e⟩
  · have e : ∀ i, res (w i) = res ⟨_, hc⟩ * res (v i) := fun i => by
      rw [← map_mul]
      refine congrArg res (Subtype.ext ?_)
      change (w i : C) = (c : C)⁻¹ * v i
      rw [h, inv_mul_cancel_left₀ c.ne_zero]
    have h₀ : res ⟨_, hc⟩ ≠ 0 := left_ne_zero_of_mul (e b ▸ hb)
    exact ⟨_, inv_ne_zero h₀, fun i => by rw [e, inv_mul_cancel_left₀ h₀]⟩

theorem isThetaPt_reduce (h₁ : Laws) (h₂ : Laws2) {B : Scheme.{0}} [IsLocallyNoetherian B] (P : PolAV B)
    {C κ : Type} [Field C] [Field κ] [IsAlgClosed κ] (S : ValuationSubring C) (res : S →+* κ)
    {s : Sp S ⟶ B} {x : Sp C ⟶ B} {y : Sp κ ⟶ B} (hx : spMap S.subtype ≫ s = x) (hy : spMap res ≫ s = y)
    {m : ℕ} (hm : 2 ≤ m) (hu : IsUnit (m : S)) {J : Type} (p : J → (Over.mk s ⟶ P.A)) (hp : ∀ i, p i ^ m ^ 2 = 1)
    (ho : ∀ z : Over.mk y ⟶ P.A, z ^ m = 1 →
      ∃ i, ((Over.homMk (spMap res) hy : Over.mk y ⟶ Over.mk s) ≫ p i) ^ m = z) (v : J → S)
    (H : IsThetaPt P m (fun i => (Over.homMk (spMap S.subtype) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      fun i => fnOf (v i : C)) (hv : ∃ i, res (v i) ≠ 0) :
    IsThetaPt P m (fun i => (Over.homMk (spMap res) hy : Over.mk y ⟶ Over.mk s) ≫ p i) fun i => fnOf (res (v i)) := by
  obtain ⟨w, hw⟩ := exists_isThetaPt_local h₁ h₂ P s H.1 hu p hp
  have hC := isThetaPt_map h₂ P S.subtype hx hw
  have hκ := isThetaPt_map h₂ P res hy hw
  let e : Γ(Sp C, ⊤) ≃+* C := (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := e.symm.isLocalRing
  obtain ⟨u, hu'⟩ := ThetaUniq.exists_unit_over h₁.globalFns P H.1 (ThetaUniq.isThetaPtOver_of_local _ x hC)
    (ThetaUniq.isThetaPtOver_of_local _ x H)
  have hc : ∀ i, (v i : C) = (Units.map e.toMonoidHom u : Cˣ) * w i := fun i =>
    (e.apply_symm_apply (v i : C)).symm.trans (((congrArg e (hu' i)).trans (map_mul e _ _)).trans
      (congrArg (_ * ·) (e.apply_symm_apply (w i : C))))
  obtain ⟨z, hz, hne⟩ := ThetaCoset.exists_ne_zero_over h₁ h₂ P y hm (by
    have := hu.map res
    rw [map_natCast] at this
    exact this.ne_zero) (ThetaUniq.isThetaPtOver_of_local _ y hκ) 1
  obtain ⟨i, hi⟩ := ho z hz
  obtain ⟨d, hd, hd'⟩ := exists_res_eq_mul S res hc hv ⟨i, fun h => hne i (by rw [_root_.one_mul]; exact hi) (by
    rw [h]; exact map_zero _)⟩
  simp only [hd']
  exact isThetaPt_mul P hκ hd

theorem detCond_reduce {B : Scheme.{0}} (T : CM.PAT H B) {C κ : Type} [Field C] [IsAlgClosed C] [CharZero C] [Field κ]
    [IsAlgClosed κ] [CharZero κ] (S : ValuationSubring C) (res : S →+* κ) (s : Sp S ⟶ B) (r : S)
    (hr : r ^ 2 = -(H.d : S)) (h : DetCond D T.t.act (spMap S.subtype ≫ s) (r : C)) :
    DetCond D T.t.act (spMap res ≫ s) (res r) := by
  obtain ⟨T', n, -⟩ := CM.PAT.exists_pullback E H _ _ s T
  have key : ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp S) (ρ : K), DetCond D T'.t.act x ρ ↔ DetCond D T.t.act (x ≫ s) ρ :=
    fun K _ x ρ => forall_congr' fun τ => by
      rw [LiePull.lieMult_pull _ _ _ _ _ s n.φ T.t.act T'.t.act n.cart n.act,
        LiePull.lieMult_pull _ _ _ _ _ s n.φ T.t.act T'.t.act n.cart n.act]
  haveI : IsReduced (Sp S) := inferInstanceAs (IsReduced (Spec (CommRingCat.of S)))
  refine (key _ _ _).1 (DetSpread.detCond_of_dense E H D (Sp S) T'.t.G T'.g T'.t.act S (𝟙 _) r T'.dim hr ?_ κ _ res
    (Category.comp_id _))
  have hd : DenseRange (spMap S.subtype) := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2
    (by rw [(RingHom.injective_iff_ker_eq_bot S.subtype).1 Subtype.val_injective]; exact bot_le)
  exact hd.mono fun q hq => ⟨C, inferInstance, inferInstance, inferInstance, _, S.subtype, hq, Category.comp_id _,
    (key _ _ _).2 h⟩

theorem exists_specialisation : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C], (∀ n : ℕ, 0 < n → ‖(n : C)‖ = 1) → ∀ (o : Full D C) (M : Mdl o), IsProper M.t.G.hom → ∀ (S : ValuationSubring C), (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (res : S →+* κ), (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) → ∀ (m : ℕ) (v : D.La → S), Odd m → 3 ≤ m → o.Theta m (fun x => v x) → (∃ x, res (v x) ≠ 0) → ∃ o' : Full D κ, (∀ r : S, (r : C) = o.ρ → o'.ρ = res r) ∧ (∀ n, 0 < n → ∀ z : S, (z : C) = o.I.ζ n → (o'.I.ζ n : κ) = res z) ∧ o'.Theta m fun x => res (v x) := by
  intro hV _ _ _ _ _ _ E _ _ _ H D C _ _ _ _ _ hn o M hp S hS κ _ _ res _ m v _ hm hth hv
  letI := H.starRing
  have h₁ : Laws := hV.1.1
  have h₂ : Laws2 := hV.1.2.1
  haveI : IsDiscreteValuationRing M.W := M.cdv.1
  have hu : ∀ n : ℕ, 0 < n → IsUnit (n : S) := fun n h => by
    have h₀ : (n : C) ≠ 0 := Nat.cast_ne_zero.2 h.ne'
    refine IsUnit.of_mul_eq_one ⟨(n : C)⁻¹, (hS _).2 (by rw [norm_inv, hn n h, inv_one])⟩ (Subtype.ext ?_)
    exact (congrArg (· * (n : C)⁻¹) (map_natCast S.subtype n)).trans (mul_inv_cancel₀ h₀)
  haveI : CharZero κ := charZero_of_inj_zero fun n h => by
    by_contra h₀
    have := (hu n (Nat.pos_of_ne_zero h₀)).map res
    rw [map_natCast] at this
    exact this.ne_zero h
  obtain ⟨T, φ, hφ, hL, ha⟩ := exists_pat h₁ h₂ o M hp
  let g : M.W →+* S := ((algebraMap (FractionRing M.W) C).comp (algebraMap M.W _)).codRestrict S
    fun w => (hS _).2 (M.ext.1 w)
  let s : Sp S ⟶ Sp M.W := spMap g
  have hs : spMap S.subtype ≫ s = jFK (R := M.W) C ≫ jK M.W := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hx : spMap S.subtype ≫ s = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C ≫ jK M.W :=
    hs.trans (Category.id_comp _).symm
  have hy : spMap res ≫ s = (baseOver (Sp κ)).hom ≫ spMap res ≫ s := (Category.id_comp _).symm
  obtain ⟨T', n, -⟩ := CM.PAT.exists_pullback E H _ _ (spMap res ≫ s) T
  have hL' : LBIso T'.t.PP.L (T.t.PP.L.pull n.φ) := (CM.PAT.exists_of_sabMap E H _ _ _ T _ n).2.symm
  have b₁ := pushHom_bijective hφ (baseOver (Sp C))
  have b₂ := pushHom_bijective n.cart (baseOver (Sp κ))
  have onto : ∀ {Q Q' : Type} [Group Q] [Group Q'] {f : Q →* Q'}, Function.Bijective f → ∀ k, 0 < k → ∀ z : Q',
      z ^ k = 1 → ∃ y : Q, y ^ k = 1 ∧ f y = z := fun {Q Q'} _ _ {f} hf k _ z hz => by
    obtain ⟨y, rfl⟩ := hf.2 z
    exact ⟨y, hf.1 (by rw [map_pow, hz, map_one]), rfl⟩
  obtain ⟨I₁, e₁⟩ := TateIsoFieldExt.up D (RingHom.id C) (pushHom hφ (baseOver (Sp C)))
    (act' := fun a g => g ≫ T.t.act.act a) (e' := fun k g g' c => WeilIs T.t.G T.t.PP.L k g g' (unitOn c))
    b₁.1 (onto b₁) (fun c y => Over.OverMorphism.ext (by
      change (y.left ≫ (o.oa.act c).left) ≫ φ = (y.left ≫ φ) ≫ (T.t.act.act c).left
      rw [Category.assoc, ha, Category.assoc]))
    (fun k y y' c => (weilIs_grpPullback_of_comm _ _ _ _ _ φ _ _ T.t.PP.isLB o.P.isLB hφ hL _ k y y' _ _ _ rfl rfl).symm)
    o.I
  obtain ⟨I₂, ev, e₂, e₃, e₄⟩ := exists_tateIso h₁ T.pol (fun a => T.t.act.act a) S res hx hy I₁
  obtain ⟨I₃, e₅⟩ := TateIsoFieldExt.down D (RingHom.id κ) (pushHom n.cart (baseOver (Sp κ)))
    (act := fun a g => g ≫ T'.t.act.act a) (e := fun k g g' c => WeilIs T'.t.G T'.t.PP.L k g g' (unitOn c))
    b₂.1 (onto b₂) (fun c y => Over.OverMorphism.ext (by
      change (y.left ≫ (T'.t.act.act c).left) ≫ n.φ = (y.left ≫ n.φ) ≫ (T.t.act.act c).left
      rw [Category.assoc, n.act, Category.assoc]))
    (fun c => by haveI := T'.t.act.hom c; exact MonObj.one_comp _)
    (fun k y y' c =>
      (weilIs_grpPullback_of_comm _ _ _ _ _ n.φ _ _ T.t.PP.isLB T'.t.PP.isLB n.cart hL' _ k y y' _ _ _ rfl rfl).symm)
    I₂
  have hρ : o.ρ ∈ S := (hS _).2 (by
    have := congrArg norm o.ρ_sq
    rw [norm_pow, norm_neg, hn _ H.d_prime.pos] at this
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this).le)
  have hr : (⟨o.ρ, hρ⟩ : S) ^ 2 = -(H.d : S) := Subtype.val_injective (o.ρ_sq.trans
    ((map_neg S.subtype _).trans (congrArg Neg.neg (map_natCast S.subtype _))).symm)
  have d₁ : DetCond D T.t.act (spMap S.subtype ≫ s) o.ρ := fun τ => by
    have := o.det τ
    rw [LiePull.lieMult_pull _ _ _ _ _ _ φ T.t.act _ hφ ha, LiePull.lieMult_pull _ _ _ _ _ _ φ T.t.act _ hφ ha] at this
    rw [hx]
    exact this
  have d₂ := detCond_reduce T S res s ⟨o.ρ, hρ⟩ hr d₁
  have d₃ : DetCond D T'.t.act (𝟙 _) (res ⟨o.ρ, hρ⟩) := fun τ => by
    rw [LiePull.lieMult_pull _ _ _ _ _ _ n.φ T.t.act _ n.cart n.act,
      LiePull.lieMult_pull _ _ _ _ _ _ n.φ T.t.act _ n.cart n.act, Category.id_comp]
    exact d₂ τ
  let oa : T'.pol.OAct (𝓞 E) :=
    { T'.t.act.toRingAct with
      rosati := fun a _ => ⟨⊤, trivial, by
        obtain ⟨u, hu⟩ := GlobalTheory.NormRos.exists_gen_rosati T'.t.PP.isLB _ _ (T'.t.adj a)
        exact ⟨_, DVR.pullGen_isGen _ _ _ _ hu _⟩⟩ }
  have m₀ : 0 < m := by omega
  have m₂ : 0 < m ^ 2 := pow_pos m₀ 2
  refine ⟨⟨T'.pol, oa, T'.t.prim, res ⟨o.ρ, hρ⟩, by rw [← map_pow, hr, map_neg, map_natCast], d₃, I₃, ‹_›⟩,
    fun r h => congrArg res (Subtype.ext h.symm),
    fun k hk z hz => (e₅ k hk).1.symm.trans (e₄ k hk z (hz.trans (e₁ k hk).1.symm)), ?_⟩
  refine (ThetaPtUp.isThetaPt_iff (P₀ := T.pol) (P := T'.pol) (T := baseOver (Sp κ)) n.cart hL'
    (fun a => congrArg (fun q => q.left) ((e₃ _ a).trans ((e₅ _ m₂).2 a)))
    (fun a => (I₃.onto _ m₂ _).2 ⟨a, rfl⟩) _).2 ?_
  refine isThetaPt_reduce h₁ h₂ T.pol S res hx hy (by omega) (hu m m₀) (ev (m ^ 2)) (fun a => ?_) (fun z hz => ?_) v ?_ hv
  · haveI := T.ab.proper
    apply (preHom_bijective T.t.G S hx).1
    rw [map_pow, map_one]
    exact (congrArg (· ^ m ^ 2) (e₂ _ a)).trans ((I₁.onto _ m₂ _).2 ⟨a, rfl⟩)
  · obtain ⟨a, rfl⟩ := (I₂.onto m m₀ z).1 hz
    refine ⟨a, (congrArg (· ^ m) (e₃ _ a)).trans ?_⟩
    rw [pow_two]
    exact I₂.tower m m m₀ m₀ a
  · exact (ThetaPtUp.isThetaPt_iff (P₀ := T.pol) (P := o.P) (T := baseOver (Sp C)) hφ hL
      (fun a => congrArg (fun q => q.left) ((e₂ _ a).trans ((e₁ _ m₂).2 a)))
      (fun a => (o.I.onto _ m₂ _).2 ⟨a, rfl⟩) _).1 hth

end GlobalTheory.Ex.Specialise
end
