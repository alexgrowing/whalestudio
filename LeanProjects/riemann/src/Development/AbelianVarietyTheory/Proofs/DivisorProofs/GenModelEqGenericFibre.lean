import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussFieldIsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsAdditiveParametrizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRootsUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsLevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionOfBirigidifiedBundleTrivialOnSliceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCocycleUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPPowerLevelFromPrimesAbovePStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPairingEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimePowerRoots
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.GenCmp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) : ∃ β : A →+* B, u = spMap β :=
  ⟨(Spec.preimage u).hom, by simp [spMap]⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap φ = spMap (β.comp φ) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {β β' : A →+* B} (h : spMap β = spMap β') : β = β' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

def baseOf (gb : GBase D.toG R') : Base D R' where
  unit k hk := by
    have hk0 : (k : ℚ) ≠ 0 := by
      rintro h
      have : k = 0 := by exact_mod_cast h
      subst this
      exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).1 hk)
    simpa using (IsUnit.mk0 _ hk0).map (algebraMap ℚ R')
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have h : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have := ((IsUnit.mk0 _ h).map (β.comp (algebraMap ℚ R'))).ne_zero
    simp at this

def GeomFull {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (t : S ⟶ Sp R') : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R' →+* k), x ≫ t = spMap β →
    ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ o.eta y = I.ev N y

def KerP {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) : Prop :=
  ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
    (∃ u : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, u.IsGen) → x ^ e = 1

variable {b : Base D R} {gb : GBase D.toG R'} {N : ℕ} {φ : R →+* R'}

def rebase (hρ : gb.ρ = φ b.ρ) (ht : ∀ i, gb.t i = φ.comp (b.t i)) {t : S ⟶ Sp R'} {s : S ⟶ Sp R}
    (hs : s = t ≫ spMap φ) (o : Obj b N s) : Obj (baseOf gb) N t where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie R₁ _ β x hx v hv := by
    have h := o.lie R₁ (β.comp φ) x (by rw [hs, ← Category.assoc, hx, spMap_comp']) v
      (by simpa [baseOf, hρ] using hv)
    obtain ⟨w, hw, hvw⟩ := h
    exact ⟨w, fun i c => (congrArg (fun z => IsTanScal o.act x (algebraMap (𝓞 D.F) D.O c) (β z) (w i))
      (DFunLike.congr_fun (ht i) c)).mpr (hw i c), hvw⟩
  lieRank k _ _ x β hx i :=
    (congrArg (fun z => LieMult (o.act.toF D) x (β.comp z) D.m) (ht i)).mpr
      (o.lieRank k x (β.comp φ) (by rw [hs, ← Category.assoc, hx, spMap_comp']) i)
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β hx := o.geom k x (β.comp φ) (by rw [hs, ← Category.assoc, hx, spMap_comp'])

def toGObj {t : S ⟶ Sp R'} (o : Obj (baseOf gb) N t) (h : GeomFull o t) : GObj gb N t where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := h

def tateRestrict {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso D.toG k Q act e) : TateIsoO D k Q act e where
  ζ := I.ζ
  ζ_prim n hn _ := I.ζ_prim n hn
  ζ_pow n m hn hm _ := I.ζ_pow n m hn hm
  ev := I.ev
  add := I.add
  lin := I.lin
  ker n hn _ := I.ker n hn
  onto n hn _ := I.onto n hn
  tower n m hn hm _ := I.tower n m hn hm
  isom n hn _ := I.isom n hn

def toObj (hρ : gb.ρ = φ b.ρ) (ht : ∀ i, gb.t i = φ.comp (b.t i)) {t : S ⟶ Sp R'} (o : GObj gb N t)
    (h : KerP o) : Obj b N (t ≫ spMap φ) where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := h
  rosati := o.rosati
  lie R₁ _ β x hx v hv := by
    obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ t)
    obtain rfl : β = β'.comp φ := spMap_inj (by rw [← hx, ← Category.assoc, hβ', spMap_comp'])
    obtain ⟨w, hw, hvw⟩ := o.lie R₁ β' x hβ' v (by rw [hρ]; exact hv)
    exact ⟨w, fun i c => (congrArg (fun z => IsTanScal o.act x (algebraMap (𝓞 D.F) D.O c) (β' z) (w i))
      (DFunLike.congr_fun (ht i) c)).mp (hw i c), hvw⟩
  lieRank k _ _ x β hx i := by
    obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ t)
    obtain rfl : β = β'.comp φ := spMap_inj (by rw [← hx, ← Category.assoc, hβ', spMap_comp'])
    exact (congrArg (fun z => LieMult (actF o.act) x (β'.comp z) D.m) (ht i)).mp (o.lieRank k x β' hβ' i)
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β hx := by
    obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ t)
    obtain ⟨I, hI⟩ := o.geom k x β' hβ'
    exact ⟨tateRestrict I, hI⟩

theorem cmp_of (hρ : gb.ρ = φ b.ρ) (ht : ∀ i, gb.t i = φ.comp (b.t i))
    (hA : ∀ (S : Scheme.{0}) (t : S ⟶ Sp R') (o : Obj (baseOf gb) N t), GeomFull o t)
    (hB : ∀ (S : Scheme.{0}) (t : S ⟶ Sp R') (o : GObj gb N t), KerP o) (M : Model b N) (X : GenModel gb N) :
    ∃ j : X.X ⟶ pullback M.s (spMap φ), IsIso j ∧ j ≫ pullback.snd _ _ = X.s ∧
      IsGPull X.univ M.univ (j ≫ pullback.fst _ _) := by
  obtain ⟨oS, ⟨m₀⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N _ _ M.s (pullback.fst M.s (spMap φ)) M.univ
  have hs : pullback.fst M.s (spMap φ) ≫ M.s = pullback.snd M.s (spMap φ) ≫ spMap φ := pullback.condition
  let gS : GObj gb N (pullback.snd M.s (spMap φ)) := toGObj (rebase hρ ht hs oS) (hA _ _ _)
  let oX : Obj b N (X.s ≫ spMap φ) := toObj hρ ht X.univ (hB _ _ _)
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := X.rep _ _ gS
  obtain ⟨g, ⟨hg, ⟨mg⟩⟩, -⟩ := M.rep _ _ oX
  let j : X.X ⟶ pullback M.s (spMap φ) := pullback.lift g X.s hg
  have j₁ : j ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  have j₂ : j ≫ pullback.snd _ _ = X.s := pullback.lift_snd _ _ _
  have mf' : ObjMap oS oX f := ⟨mf.φ, mf.φ₂, mf.cart, mf.sq, mf.act, mf.pol, mf.eta⟩
  have e₁ : f ≫ g = pullback.fst _ _ := (M.rep _ _ oS).unique
    ⟨by rw [Category.assoc, hg, ← Category.assoc, hf, hs], objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ mf' mg⟩
    ⟨rfl, ⟨m₀⟩⟩
  obtain ⟨mj⟩ := PullFactor.objMap_factor p D R b N _ _ _ _ _ _ M.univ oS oX _ j m₀ (j₁.symm ▸ mg)
  obtain ⟨me⟩ := objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ mj mf'
  obtain ⟨mi⟩ := RepFamModel.objMap_refl oX
  have e₂ : j ≫ f = 𝟙 _ := (X.rep _ _ X.univ).unique
    ⟨by rw [Category.assoc, hf, j₂], ⟨⟨me.φ, me.φ₂, me.cart, me.sq, me.act, me.pol, me.eta⟩⟩⟩
    ⟨Category.id_comp _, ⟨⟨mi.φ, mi.φ₂, mi.cart, mi.sq, mi.act, mi.pol, mi.eta⟩⟩⟩
  have e₃ : f ≫ j = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, j₁, e₁, Category.id_comp]
    · rw [Category.assoc, j₂, hf, Category.id_comp]
  refine ⟨j, ⟨f, e₂, e₃⟩, j₂, ?_⟩
  rw [j₁]
  exact ⟨mg.φ, mg.φ₂, mg.cart, mg.sq, mg.act, ⟨mg.pol⟩, mg.eta⟩

end GlobalTheory.UPel.HT.GenCmp

namespace GlobalTheory.UPel.HT.GenCmp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R' : Type} [CommRing R'] [Algebra ℚ R'] {S : Scheme.{0}}

theorem charZero_of_hom {k : Type} [Field k] (β : R' →+* k) : CharZero k :=
  charZero_of_injective_ringHom (β.comp (algebraMap ℚ R')).injective

theorem pow_eq_one_geom {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) (e : ℕ)
    (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S)
    (g : Over.mk x₀ ⟶ o.A) (M : ℕ) (hM : 0 < M) (hn : g ^ M = 1)
    (hg : ∃ u : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, u.IsGen) :
    g ^ e = 1 := by
  obtain ⟨β, hβ⟩ := exists_spMap (x₀ ≫ t)
  haveI := charZero_of_hom β
  obtain ⟨I, -⟩ := o.geom k x₀ β hβ
  obtain ⟨y, hy⟩ : ∃ y : D.La, I.ev M y = g := (I.onto M hM g).1 hn
  have key : ∀ z : D.La, (M : ℤ) ∣ D.EF y z := by
    intro z
    have hm : 0 < M * 2 := by omega
    have ha : I.ev (M * 2) y ^ 2 = g := by rw [I.tower M 2 hM two_pos y, hy]
    have hc := GlobalTheory.WeilSqKer.weilIs_eq_one S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ (M * 2)
      (Nat.cast_ne_zero.2 hm.ne') _ _ ((I.onto _ hm _).2 ⟨y, rfl⟩) ((I.onto _ hm _).2 ⟨z, rfl⟩) (ha ▸ hg) _
      (I.isom _ hm y z)
    have h1 : I.ζ (M * 2) ^ (2 * D.EF y z) = 1 :=
      GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hc.trans (map_one _).symm)
    have h3 := ((I.ζ_prim (M * 2) hm).zpow_eq_one_iff_dvd _).1 h1
    have h4 : (M : ℤ) * 2 ∣ D.EF y z * 2 := by
      rw [mul_comm (D.EF y z)]; exact_mod_cast h3
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / M
      map_add' := fun u v => by
        rw [map_add, Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (M : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = M • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev M y ^ e := by rw [hy]
    _ = I.ev M (e • y) := (KerBy.ev_nsmul (La := D.La) _ (I.add M) e y).symm
    _ = 1 := (I.ker M hM _).2 ⟨w, hyw⟩

theorem genericObject_kernelCondition {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) : KerP o := by
  obtain ⟨e, he, hEF⟩ := D.perfP
  refine ⟨e, he, fun T x hx => ?_⟩
  apply Over.OverMorphism.ext
  refine T.left.affineCover.hom_ext _ _ fun i => ?_
  obtain ⟨B, ⟨u⟩⟩ : ∃ B : CommRingCat.{0}, Nonempty (T.left.affineCover.X i ≅ Spec B) :=
    ⟨_, ⟨(T.left.affineCover.X i).isoSpec⟩⟩
  rw [← cancel_epi u.inv]
  let a : Sp B ⟶ T.left := u.inv ≫ T.left.affineCover.f i
  let a' : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  have hx' := KerBy.gen_comp S o.A o.P T _ a' x hx
  obtain ⟨M, hM, hxM⟩ := GlobalTheory.T.isTorsion_of_birigidified_bundle_trivial_on_slice S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ o.symm o.ample B (a ≫ T.hom) _ hx'
  have hu : IsUnit ((M : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((M : ℕ) : R') := by
      simpa using (IsUnit.mk0 (M : ℚ) (Nat.cast_ne_zero.2 hM.ne')).map (algebraMap ℚ R')
    simpa using (h0.map (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom).map t.appTop.hom
  have h := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points S o.A o.ab M hu _ _ hxM e fun k _ _ ξ =>
    pow_eq_one_geom o e hEF k _ _ M hM (by rw [← MonObj.comp_pow, hxM, MonObj.comp_one])
      (KerBy.gen_comp S o.A o.P _ _ _ _ hx')
  have h' : a' ≫ x ^ e = a' ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have h'' : a ≫ (x ^ e).left = a ≫ (1 : T ⟶ o.A).left := congrArg (fun z => z.left) h'
  exact (Category.assoc _ _ _).symm.trans (h''.trans (Category.assoc _ _ _))

theorem geomFull {b : Base D R'} {N : ℕ} (hN : N.Coprime p) {t : S ⟶ Sp R'} (o : Obj b N t) : GeomFull o t := by
  intro k _ _ x β hβ
  have hp : p.Prime := Fact.out
  haveI := charZero_of_hom β
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h => hp.one_lt.ne' ((Nat.coprime_zero_left p).1 (h ▸ hN))
  have hB : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab
  have ub := GlobalTheory.Ex.Specialise.unitOn_bijective (R := k)
  let Q := Over.mk x ⟶ o.A
  let act : D.O → Q → Q := fun c g => g ≫ o.act.act c
  let E : ℕ → Q → Q → kˣ → Prop := fun n g g' z =>
    Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)
  have amul : ∀ c a b, act c (a * b) = act c a * act c b := fun c a b => by
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have apow : ∀ c (a : Q) n, a ^ n = 1 → act c a ^ n = 1 := fun c a n h => by
    haveI := o.act.hom c
    show (a ≫ _) ^ n = 1
    rw [← MonObj.pow_comp, h, MonObj.one_comp]
  have powl : ∀ (n : ℕ) (a b : Q), (lift a b) ^ n = lift (a ^ n) (b ^ n) := by
    intro n a b
    ext <;> simp [MonObj.pow_comp]
  have ex : ∀ (n : ℕ) (a b : Q), ∃ c : kˣ, 0 < n → a ^ n = 1 → b ^ n = 1 →
      Out.WeilIs (G2 o.A) o.P n (lift a 1) (lift 1 b) (unitOn c) := fun n a b => by
    by_cases h : 0 < n ∧ a ^ n = 1 ∧ b ^ n = 1
    · obtain ⟨c, -, hc⟩ := GlobalTheory.ProdPairing.exists_weilIs_prod_root S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.ample n h.1 _
        (lift a 1) (lift 1 b) (by rw [powl, h.2.1, one_pow]; ext <;> simp) (by rw [powl, h.2.2, one_pow]; ext <;> simp)
      obtain ⟨c, rfl⟩ := ub.2 c
      exact ⟨c, fun _ _ _ => hc⟩
    · exact ⟨1, fun h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ h⟩
  choose W hW using ex
  have uq : ∀ {n : ℤ} {X Y : Over.mk x ⟶ G2 o.A} {c c' : kˣ}, Out.WeilIs (G2 o.A) o.P n X Y (unitOn c) →
      Out.WeilIs (G2 o.A) o.P n X Y (unitOn c') → c = c' := fun h h' =>
    ub.1 (CommutatorPairing.weilIs_unique hG hB o.isLB h h')
  have uqE : ∀ n, 0 < n → ∀ (a b : Q) (c c' : kˣ), E n a b c → E n a b c' → c = c' := fun n _ a b c c' h h' =>
    ub.1 (CommutatorPairing.weilIs_unique hG o.ab (pull_isLB o.isLB _) h h')
  have upow : ∀ (c : kˣ) (m : ℕ), unitOn (c ^ m) = unitOn c ^ m := fun c m => map_pow _ _ _
  have umul : ∀ c c' : kˣ, unitOn (c * c') = unitOn c * unitOn c' := fun c m => map_mul _ _ _
  have uone : unitOn (1 : kˣ) = 1 := map_one _
  have hE : ∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → E n a b (W n a b ^ 2) := fun n hn a b ha hb => by
    have h := GlobalTheory.DiagSqAxes.weilIs_diag_sq S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm k x n hn
      (Nat.cast_ne_zero.2 hn.ne') a b ha hb _ (hW n a b hn ha hb)
    rw [← upow] at h
    exact h
  have lev : ∀ n m, 0 < n → 0 < m → ∀ a b : Q, a ^ (n * m) = 1 → b ^ (n * m) = 1 →
      W n (a ^ m) (b ^ m) = W (n * m) a b ^ m := fun n m hn hm a b ha hb => by
    have h := GlobalTheory.LevelChangePairing.weilIs_levelChange S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ k x n m hn hm
      (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne') a b ha hb _ (hW (n * m) a b (Nat.mul_pos hn hm) ha hb)
    rw [← upow] at h
    exact uq (hW n _ _ hn (by rw [← pow_mul, mul_comm, ha]) (by rw [← pow_mul, mul_comm, hb])) h
  have wmul : ∀ n, 0 < n → ∀ a a' b : Q, a ^ n = 1 → a' ^ n = 1 → b ^ n = 1 →
      W n (a * a') b = W n a b * W n a' b := fun n hn a a' b ha ha' hb => by
    have h := GlobalTheory.SiegelTypings.weilIs_mul hB o.isLB (hW n a b hn ha hb) (hW n a' b hn ha' hb)
    have e : lift a (1 : Q) * lift a' 1 = lift (a * a') 1 := by ext <;> simp [MonObj.mul_comp]
    rw [← umul, e] at h
    exact uq (hW n _ _ hn (by rw [mul_pow, ha, ha', _root_.mul_one]) hb) h
  have wskew : ∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → W n a b * W n b a = 1 := fun n hn a b ha hb => by
    have h := GlobalTheory.SwapPairing.weilIs_swap_eq S o.A o.P o.ab o.isLB o.symm n _ a b _ _
      (CommPairing.weilIs_symm o.isLB (hW n b a hn hb ha)) (hW n a b hn ha hb)
    apply ub.1
    rw [umul, ← h, uone, inv_mul_cancel]
  have wadj : ∀ n, 0 < n → ∀ (c : D.O) (a b : Q), a ^ n = 1 → b ^ n = 1 →
      W n (act c a) b = W n a (act (D.star c).unop b) := fun n hn c a b ha hb =>
    ub.1 (GlobalTheory.T.commutatorPairing_adjoint_eq_of_pullback_iso S o.A o.P o.ab o.isLB _ _ (o.act.hom c) (o.act.hom _) (o.rosati c) n _ a b _ _
      (hW n _ b hn (apow c a n ha) hb) (hW n a _ hn ha (apow _ b n hb)))
  have wnd : ∀ r, ∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W (p ^ r) a b = 1) → a = 1 := by
    intro r a ha h
    have hq : 0 < p ^ r := pow_pos hp.pos r
    obtain ⟨e, he, hk⟩ := o.kerP
    have h1 := hk _ a (GlobalTheory.T.lineBundle_slice_trivial_of_weilPairing_one_torsion S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ k x (p ^ r) (Nat.cast_ne_zero.2 hq.ne') a ha
      fun b hb => by
        have := hW _ a b hq ha hb
        rwa [h b hb, uone] at this)
    have h2 := pow_gcd_eq_one.2 ⟨h1, ha⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right r he), pow_one] at h2
  have hpu : IsUnit (p : R') := by
    simpa using (IsUnit.mk0 (p : ℚ) (Nat.cast_ne_zero.2 hp.ne_zero)).map (algebraMap ℚ R')
  have aone : ∀ a, act 1 a = a := fun a => by simp [act, o.act.one]
  have amul' : ∀ b c a, act (b * c) a = act b (act c a) := fun b c a => by simp [act, o.act.mul]
  have aadd : ∀ b c a, act (b + c) a = act b a * act c a := fun b c a => by
    simp [act, o.act.add, MonObj.comp_mul]
  have lin := GlobalTheory.T.exists_pPower_level_from_primes_above_p p D Q act amul aone amul' aadd fun w r hw hpw => by
    obtain ⟨f, f₁, f₂, f₃, f₄⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R' b N w r (isEtPlace_of_isUnit b hpu w hw hpw) S t o k x
    exact GlobalTheory.T.exists_morita_lattice_quotient_torsion p D w r hw hpw Q act amul aone amul' aadd f f₁ f₂ f₃ f₄
  obtain ⟨ζ, hζ, hζ'⟩ := GlobalTheory.T.exists_compatible_prime_power_roots p k
  obtain ⟨ev, hev, hev'⟩ := GlobalTheory.T.exists_compatible_similitude_level_tower p D k Q act (fun r => W (p ^ r)) ζ amul hζ'
    (fun r a b ha hb => lev (p ^ r) p (pow_pos hp.pos r) hp.pos a b ha hb) fun r => by
      obtain ⟨f, hf⟩ := lin r
      have hq : 0 < p ^ r := pow_pos hp.pos r
      exact GlobalTheory.T.exists_level_pairing_eq_alt p D k Q act r (W (p ^ r)) (ζ r) (hζ r) (wmul _ hq) (wskew _ hq) (wadj _ hq) (wnd r) f hf
  obtain ⟨I, hI⟩ := o.geom k x β hβ
  obtain ⟨J, hJ⟩ := GlobalTheory.T.weil_pairing_cocycle_uniqueness p D k Q act E amul (fun n hn a b ha hb => ⟨_, hE n hn a b ha hb⟩) uqE
    (fun n m hn hm a b c ha hb h => by
      have e := uqE _ (Nat.mul_pos hn hm) a b _ _ h (hE _ (Nat.mul_pos hn hm) a b ha hb)
      have h' := hE n hn (a ^ m) (b ^ m) (by rw [← pow_mul, mul_comm, ha]) (by rw [← pow_mul, mul_comm, hb])
      rw [lev n m hn hm a b ha hb, ← pow_mul, mul_comm m 2, pow_mul, ← e] at h'
      exact h')
    I ζ ev hζ hζ' (fun r => (hev r).1) hev' fun r y z => by
      have hq : 0 < p ^ r := pow_pos hp.pos r
      have h := hE _ hq (ev r y) (ev r z) (((hev r).1.2.2.2 _).2 ⟨y, rfl⟩) (((hev r).1.2.2.2 _).2 ⟨z, rfl⟩)
      have e := (hev r).2 y z
      rw [e, ← zpow_natCast, ← zpow_mul, mul_comm] at h
      exact h
  exact ⟨J, fun y => (hI y).trans (hJ N hN0 hN y).symm⟩

end GlobalTheory.UPel.HT.GenCmp

namespace GlobalTheory.UPel.HT.GenCmp

theorem genModel_eq_genericFibre : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _) := by
  intro p _ D R _ _ b R' _ _ φ gb hρ ht N _ hN M X
  obtain ⟨j, hj, h₁, h₂⟩ := cmp_of hρ ht (fun S t o => geomFull hN o) (fun S t o => genericObject_kernelCondition o) M X
  exact ⟨j, inferInstance, inferInstance, h₁, h₂⟩

end GlobalTheory.UPel.HT.GenCmp
