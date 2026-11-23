import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantConditionSpreadsFromGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryOfPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModN
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ObjSpread

theorem map_nsmul_of_add {L Q : Type} [AddCommGroup L] [Group Q] {f : L → Q} (h : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f (n • a) = f a ^ n := by
  let φ : L →+ Additive Q := AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) fun a c => congrArg Additive.ofMul (h a c)
  exact congrArg Additive.toMul (map_nsmul φ n a)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Tate

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem card_torsion (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    Nat.card {x : Q // x ^ n = 1} = n ^ Module.finrank ℤ D.La := by
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let f : D.La →+ Additive Q :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev n a)) fun a b => congrArg Additive.ofMul (I.add n a b)
  have hk : f.ker = (nsmulAddMonoidHom n : D.La →+ D.La).range := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact (I.ker n hn a).trans ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩
  rw [← AddSubgroup.index_range_nsmul, ← hk, AddSubgroup.index_ker]
  exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun u => I.onto n hn u)

theorem ev_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) (a : D.La) :
    I.ev N ((N / n) • a) = I.ev n a := by
  obtain ⟨d, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hN
  have hd : 0 < d := Nat.pos_of_mul_pos_left hN
  rw [Nat.mul_div_cancel_left d hn, map_nsmul_of_add (I.add _), I.tower n d hn hd]

theorem zeta_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) :
    (I.ζ N : k) ^ (N / n) = I.ζ n := by
  obtain ⟨d, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hN
  have hd : 0 < d := Nat.pos_of_mul_pos_left hN
  rw [Nat.mul_div_cancel_left d hn, ← Units.val_pow_eq_pow_val, I.ζ_pow n d hn hd]

end Tate

variable {l : Geo.Tor.Level H}

theorem level_pos (l : Geo.Tor.Level H) : 0 < l.M' :=
  Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

section Tors

variable {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem eta_pow (o : Obj D l b s) (a : D.La) : o.eta a ^ l.M' = 1 := by
  obtain ⟨d, hd⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    refine Ideal.mul_le_left (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ?_
    rw [l.prod]
    exact Ideal.subset_span rfl
  rw [hd, pow_mul, ← map_nsmul_of_add o.eta_add, o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM trivial), one_pow]

theorem etaA_pow (o : Obj D l b s) (a : D.La) : o.etaA a ^ l.M' = 1 := by
  obtain ⟨d, hd⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  rw [hd, pow_mul, ← map_nsmul_of_add o.etaA_add, o.etaA_ker, one_pow]

theorem geom_push (o : Obj D l b s) {X : Scheme.{0}} {t : SAB H X} {f : S ⟶ X} (m : SABMap o.t t f)
    (σ σA : D.La → (𝟙_ (Over X) ⟶ t.G)) (hσ : ∀ a, (o.eta a).left ≫ m.cm.F = f ≫ (σ a).left)
    (hσA : ∀ a, (o.etaA a).left ≫ m.cm.F = f ≫ (σA a).left) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (y : Sp k ⟶ X) (hy : y = x ≫ f) :
    DetCond D t.act y (β b.ρ) ∧
    ∃ I : TateIso D k (Over.mk y ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ l.A : k) = β b.ζ ∧ (∀ a, toUnit _ ≫ σA a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ σ a = I.ev l.M a := by
  subst hy
  have hL : LBIso o.t.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k x β hx
  have push : ∀ (u : 𝟙_ (Over S) ⟶ o.t.G) (v : 𝟙_ (Over X) ⟶ t.G), u.left ≫ m.cm.F = f ≫ v.left →
      toUnit (Over.mk (x ≫ f)) ≫ v = ObjPull.pushEquiv m.cart (Over.mk x) (toUnit _ ≫ u) := fun u v h => by
    apply Over.OverMorphism.ext
    rw [ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, h,
      ObjPull.toUnit_left', ObjPull.toUnit_left']
    exact Category.assoc _ _ _
  refine ⟨fun τ => ?_, ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x)).symm (fun c z => ?_)
    (fun n z z' c hz => ?_) I, hI, fun a => ?_, fun a ha => ?_⟩
  · rw [← LiePull.lieMult_pull _ _ _ t.G o.t.G f m.cm.F t.act o.t.act m.cart m.act k x τ,
      ← LiePull.lieMult_pull _ _ _ t.G o.t.G f m.cm.F t.act o.t.act m.cart m.act k x τ]
    exact hdet τ
  · obtain ⟨z, rfl⟩ := (ObjPull.pushEquiv m.cart (Over.mk x)).surjective z
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_apply]
    apply Over.OverMorphism.ext
    show (z.left ≫ _) ≫ _ = (z.left ≫ _) ≫ _
    rw [Category.assoc, ← m.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm _ _ t.G o.t.G f m.cm.F t.PP.L o.t.PP.L t.PP.isLB o.t.PP.isLB m.cart hL
      (Over.mk x) n _ _ z z' _ (ObjPull.pushEquiv_symm_left m.cart (Over.mk x) z).symm
      (ObjPull.pushEquiv_symm_left m.cart (Over.mk x) z').symm).1 hz
  · exact (push _ _ (hσA a)).trans (congrArg _ (hA a))
  · exact (push _ _ (hσ a)).trans (congrArg _ (hM a ha))

end Tors

theorem exists_sections {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G) {n : ℕ} (hn : IsUnit (n : A))
    (hT : GlobalTheory.TChart.TorsRat G n) {K : Type} [Field K] {f : Sp K ⟶ Sp A} {G' : Over (Sp K)} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) {L : Type} [Add L] (u : L → (𝟙_ (Over (Sp K)) ⟶ G'))
    (hu : ∀ a, u a ^ n = 1) (hadd : ∀ a c, u (a + c) = u a * u c) :
    ∃ σ : L → (𝟙_ (Over (Sp A)) ⟶ G), (∀ a, σ a ^ n = 1) ∧ (∀ a c, σ (a + c) = σ a * σ c) ∧
      (∀ a, u a = 1 → σ a = 1) ∧ ∀ a, (u a).left ≫ φ = f ≫ (σ a).left := by
  have hnΓ : IsUnit (n : Γ(Sp A, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    rwa [map_natCast] at this
  let Φ := ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  have hxa : ∀ a, (Φ (u a)) ^ n = 1 := fun a => by rw [← map_pow, hu, map_one]
  choose σ hσn hσx using fun a => LevSpread.l2 A G n hG hn hT K _ (Φ (u a)) (hxa a)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp A))).left := inferInstanceAs (PreconnectedSpace (Sp A))
  haveI : Nonempty (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ f)).left := inferInstanceAs (Nonempty (Sp K))
  have inj : ∀ (s s' : 𝟙_ (Over (Sp A)) ⟶ G), s ^ n = 1 → s' ^ n = 1 →
      toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ f)) ≫ s = toUnit _ ≫ s' → s = s' := fun s s' hs hs' h =>
    LevSpread.eq_of_comp_eq G hG hnΓ (𝟙_ _) s s' hs hs' _ (toUnit _) h
  refine ⟨σ, hσn, fun a c => inj _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, hadd, map_mul]),
    fun a ha => inj _ _ (hσn a) (one_pow n) (by rw [hσx, ha, map_one, MonObj.comp_one]), fun a => ?_⟩
  have e := congrArg (fun w => w.left) (hσx a)
  simp only [Over.comp_left, ObjPull.toUnit_left'] at e
  rw [← ObjPull.pushEquiv_left hφ, ← e]
  exact congrArg (· ≫ (σ a).left) (Category.id_comp _)

theorem exists_tateIso {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (hQ : Nonempty (ℚ →+* A))
    (P : Out.PolAV (Sp A)) (act : 𝓞 E → (P.A ⟶ P.A)) (hact : ∀ a, IsMonHom (act a)) (z : A) {κ : Type}
    (lam : κ → D.La) (pt : κ → (𝟙_ (Over (Sp A)) ⟶ P.A)) {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1)
    (hpt : ∀ i, pt i ^ N = 1) {K₀ : Type} [Field K₀] [IsAlgClosed K₀] (g₀ : A →+* K₀)
    (I₀ : TateIso D K₀ (Over.mk (spMap g₀) ⟶ P.A) (fun a g => g ≫ act a)
      (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)))
    (h₁ : (I₀.ζ N : K₀) = g₀ z) (h₂ : ∀ i, I₀.ev N (lam i) = toUnit _ ≫ pt i)
    (K : Type) [Field K] [IsAlgClosed K] (g : A →+* K) :
    ∃ I : TateIso D K (Over.mk (spMap g) ⟶ P.A) (fun a g => g ≫ act a)
      (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
      (I.ζ N : K) = g z ∧ ∀ i, I.ev N (lam i) = toUnit _ ≫ pt i := by
  have hL : Out.Laws := allSixLaws.1
  obtain ⟨q⟩ := hQ
  have : CharZero K := (g.comp q).charZero_iff (g.comp q).injective |>.1 inferInstance
  have : CharZero K₀ := (g₀.comp q).charZero_iff (g₀.comp q).injective |>.1 inferInstance
  have hcard : ∀ n, 0 < n → Nat.card {y : Over.mk (spMap g) ⟶ P.A // y ^ n = 1} = n ^ Module.finrank ℤ D.La :=
    fun n hn => by
      rw [← card_torsion I₀ hn]
      exact ((hL.mulN _ P n hn).2.2.2.2 K (spMap g) (Nat.cast_ne_zero.2 hn.ne')).trans
        ((hL.mulN _ P n hn).2.2.2.2 K₀ (spMap g₀) (Nat.cast_ne_zero.2 hn.ne')).symm
  have hu : ∀ (F : Type) [Field F] (β : A →+* F) (i : κ),
      (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫
        (pt i : Out.baseOver (Sp A) ⟶ P.A) = toUnit (Over.mk (spMap β)) ≫ pt i := fun F _ β i =>
    congrArg (· ≫ pt i) (toUnit_unique _ _)
  refine TateTower.tateIso_of_levels E H D K (Over.mk (spMap g) ⟶ P.A) (fun c y => y ≫ act c)
    (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)) N (g z) _ lam (fun i => toUnit _ ≫ pt i) hN
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m y y' c hn hm hy hy' h => ?_) (fun m hm => ?_)
  · have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
    have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
    have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rw [map_natCast] at u'
    rw [e]
    exact PELFamily.weilIs_lower P hL.weil hm u' hy hy' h
  · have hn := Nat.mul_pos hN hm
    obtain ⟨ζ, ev, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := GlobalTheory.T.exists_levelIsometry_of_point_alt E H D A P act z κ lam pt (N * m) m N hn hN ⟨q⟩ hz hpt
      hact ⟨K₀, inferInstance, g₀, I₀.ζ (N * m), I₀.ev (N * m), I₀.ζ_prim _ hn, I₀.add _,
        fun v => (I₀.onto _ hn _).2 ⟨v, rfl⟩, I₀.lin _, I₀.isom _ hn,
        by rw [← h₁, ← I₀.ζ_pow N m hN hm, Units.val_pow_eq_pow_val],
        fun i => ((I₀.tower N m hN hm _).trans (h₂ i)).trans (hu K₀ g₀ i).symm⟩ K g
    obtain ⟨k₈, k₉⟩ := TorsIsometry.ker_and_onto E H D K (Over.mk (spMap g) ⟶ P.A)
      (fun y y' c => Out.WeilIs P.A P.L (N * m : ℕ) y y' (unitOn c)) (N * m) ζ ev hn (hcard _ hn)
      (fun _ _ _ h => PELFamily.eq_one_of_weilIs_one P hL.weil h) k₁ k₂ k₃ k₅
    exact ⟨ζ, ev, k₁, k₂, k₄, k₈, k₉, k₅, k₆, fun i => (k₇ i).trans (hu K g i)⟩

theorem exists_obj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (b : c.F →+* A) (t : SAB H (Sp A)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → GlobalTheory.TChart.TorsRat t.G l.M' → ∀ (K : Type) [Field K] (g : A →+* K) (sK : Sp K ⟶ Sp (KA l)) (oK : Obj D l (baseKA l) sK), sK = spMap g ≫ spMap (b.comp (IntermediateField.inclusion c.le).toRingHom) → SABMap oK.t t (spMap g) → ∃ o : Obj D l (baseKA l) (spMap (b.comp (IntermediateField.inclusion c.le).toRingHom)), o.t = t ∧ Nonempty (ObjMap oK o (spMap g)) := by
  intro E _ _ _ H D l c A _ _ _ _ b t hp ha hk hT K _ g sK oK hsK m
  generalize (IntermediateField.inclusion c.le).toRingHom = j at hsK ⊢
  have hN := level_pos l
  have hdA : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  have hdM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hQ : Nonempty (ℚ →+* A) := ⟨b.comp (algebraMap ℚ c.F)⟩
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  have hu : IsUnit (l.M' : A) := by
    simpa using (IsUnit.mk0 (l.M' : c.F) (Nat.cast_ne_zero.2 hN.ne')).map b
  obtain ⟨σ, σn, σadd, σker, σc⟩ := exists_sections t.G hab hu hT m.cart oK.eta (eta_pow oK) oK.eta_add
  obtain ⟨τ, τn, τadd, τker, τc⟩ := exists_sections t.G hab hu hT m.cart oK.etaA (etaA_pow oK) oK.etaA_add
  refine ⟨{ t := t, proper := hp, ample := ha, ktriv := hk
            eta := σ, eta_add := σadd, eta_ker := fun a h => σker a (oK.eta_ker a h)
            etaA := τ, etaA_add := τadd, etaA_ker := fun a => τker _ (oK.etaA_ker a)
            geom := fun k _ _ x β hx => ?_ }, rfl, ⟨⟨m, σc, τc⟩⟩⟩
  obtain ⟨ρ, rfl⟩ : ∃ ρ : A →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  obtain rfl : β = ρ.comp (b.comp j) := by
    have e : spMap (ρ.comp (b.comp j)) = spMap β := (spMap_comp _ _).trans hx
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  let i : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let g₀ : A →+* AlgebraicClosure K := i.comp g
  obtain ⟨hdet, I₀, hζ, hτ, hσ⟩ := geom_push oK m σ τ σc τc (AlgebraicClosure K) (spMap i) (g₀.comp (b.comp j))
    (by rw [hsK, ← Category.assoc, ← spMap_comp g i, ← spMap_comp]) (spMap g₀) (spMap_comp _ _)
  refine ⟨GlobalTheory.T.determinantCondition_spreads_from_geometricPoint D A t.G t.act (b (j (baseKA l).ρ)) hab
    (by rw [← map_pow, ← map_pow, (baseKA l).ρ_sq, map_neg, map_neg, map_natCast, map_natCast]) hQ _ g₀ hdet k ρ, ?_⟩
  have : ConnectedSpace (Sp A) := inferInstanceAs (ConnectedSpace (PrimeSpectrum A))
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp A) :=
    { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk, isAb := hab
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }

  let w : c.F := ⟨zeta l.M', c.zeta_mem⟩
  have hw : IsPrimitiveRoot w l.M' := IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
    (Complex.isPrimitiveRoot_exp l.M' hN.ne') Subtype.val_injective
  have : NeZero l.M' := ⟨hN.ne'⟩
  obtain ⟨r, -, hr⟩ := (hw.map_of_injective (g₀.comp b).injective).eq_pow_of_pow_eq_one
    (ξ := (I₀.ζ l.M' : AlgebraicClosure K))
    (by rw [← Units.val_pow_eq_pow_val, (I₀.ζ_prim _ hN).pow_eq_one, Units.val_one])
  rw [← map_pow] at hr
  have hwA : (w ^ r) ^ (l.M' / l.A) = j (baseKA l).ζ := (g₀.comp b).injective (by
    rw [map_pow, hr, zeta_div I₀ hN hdA, hζ]; rfl)
  let Λ := {a : D.La // a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)}
  obtain ⟨I, e₁, e₂⟩ := exists_tateIso (D := D) hQ P t.act.act t.act.hom (b (w ^ r)) (κ := D.La ⊕ Λ)
    (Sum.elim (fun a => (l.M' / l.A) • a) fun a => (l.M' / l.M) • a.1) (Sum.elim τ fun a => σ a.1) hN
    (by rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow, map_one])
    (by rintro (a | a); exacts [τn a, σn a.1]) g₀ I₀ hr.symm
    (by rintro (a | a); exacts [(ev_div I₀ hN hdA a).trans (hτ a).symm, (ev_div I₀ hN hdM a.1).trans (hσ a.1 a.2).symm])
    k ρ
  refine ⟨I, ?_, fun a => (e₂ (.inl a)).symm.trans (ev_div I hN hdA a),
    fun a h => (e₂ (.inr ⟨a, h⟩)).symm.trans (ev_div I hN hdM a)⟩
  rw [← zeta_div I hN hdA, e₁, ← map_pow, ← map_pow, hwA]
  rfl

end GlobalTheory.ObjSpread
