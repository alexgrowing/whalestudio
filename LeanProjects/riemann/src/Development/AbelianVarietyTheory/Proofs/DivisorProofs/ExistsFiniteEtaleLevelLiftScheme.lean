import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenOfSpecializesIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPointsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.LevCover

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def TateAt {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) {k : Type} [Field k] (x : Sp k ⟶ S)
    (l : D.La → (Over.mk x ⟶ o.A)) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ y, l y = I.ev N' y

theorem tateAt_congr {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) {k : Type} [Field k]
    {x x' : Sp k ⟶ S} (e : x = x') (l : D.La → (Over.mk x ⟶ o.A)) (l' : D.La → (Over.mk x' ⟶ o.A))
    (h : ∀ a, (Over.homMk (𝟙 _) (by simp [e]) : Over.mk x' ⟶ Over.mk x) ≫ l a = l' a) :
    TateAt o N' x l → TateAt o N' x' l' := by
  subst e
  have h' : ∀ a, l a = l' a := fun a => by
    rw [← h a]
    have : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := by ext; simp
    rw [this, Category.id_comp]
  rintro ⟨I, hI⟩
  exact ⟨I, fun a => (h' a).symm.trans (hI a)⟩

theorem comp_actN_nsmul {A : Over S} [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) {T : Over S}
    (x : T ⟶ A) (n : ℕ) (c : D.O) : x ≫ act.act (n • c) = (x ^ n) ≫ act.act c := by
  have := act.hom c
  rw [add_map_nsmul act.add, MonObj.comp_pow, MonObj.pow_comp]

theorem exists_liftHom {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) (hc : N'.Coprime p)
    (hd : N ∣ N') :
    ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧
      (∀ a, et (N' • a) = 1) ∧ (∀ (c : D.O) a, et (c • a) = et a ≫ o.act.act c) ∧
      (∀ a, et ((N' / N) • a) = toUnit Z ≫ o.eta a) ∧
      ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N' • a) = 1) →
        (∀ (c : D.O) a, lv (c • a) = lv a ≫ o.act.act c) → (∀ a, lv ((N' / N) • a) = toUnit T ≫ o.eta a) →
          ∃! h : T ⟶ Z, ∀ a, h ≫ et a = lv a := by
  have hN' := levelPos_of_coprime hc
  have hNS : IsUnit (N' : Γ(S, ⊤)) := by
    have := (b.unit N' hc).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨Z, y, hfin, het, yadd, ypow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S o.A N' D.La o.ab hNS
  have R : RepTors o.A N' D.La Z y := ⟨hfin, het, yadd, ypow, huniv⟩
  haveI := hfin
  haveI := het
  have ymod : ∀ a c, y (a + N' • c) = y a := fun a c => by
    rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have etaN : ∀ a, o.eta (N' • a) = 1 := fun a => by
    rw [← Nat.mul_div_cancel' hd, mul_smul, o.eta_ker]
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod D.O hN'
  have c1 : ClopenCond Z fun _ h => ∀ (c : D.O) a, h ≫ y (c • a) = h ≫ y a ≫ o.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := o.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ o.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := o.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, o.act.add, MonObj.comp_mul, comp_actN_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond Z fun _ h => ∀ a, h ≫ y ((N' / N) • a) = h ≫ (toUnit Z ≫ o.eta a) :=
    R.clopenCond (fun a => y ((N' / N) • a)) (fun a => toUnit Z ≫ o.eta a) (fun a a' => by rw [smul_add, yadd])
      (fun a => ypow _) (fun a a' => by rw [o.eta_add, MonObj.comp_mul]) fun a => by
        rw [← MonObj.comp_pow, ← add_map_nsmul o.eta_add, etaN, MonObj.comp_one]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, hmono, Hi⟩ := exists_sub U hU
  have hi := (HU W i).2 ((Hi W i).2 ⟨𝟙 W, Category.id_comp i⟩)
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [add_map_nsmul yadd, ypow, MonObj.comp_one],
    fun c a => by beta_reduce; rw [hi.1, Category.assoc], fun a => ?_, fun T lv hadd hker hlin hlev => ?_⟩
  · beta_reduce
    rw [hi.2, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have hpow : ∀ a, lv a ^ N' = 1 := fun a => by rw [← add_map_nsmul hadd, hker]
  obtain ⟨h, hh, -⟩ := huniv T lv hadd hpow
  have hP1 : ∀ (c : D.O) a, h ≫ y (c • a) = h ≫ y a ≫ o.act.act c := fun c a => by
    rw [hh, hlin, ← hh a, Category.assoc]
  have hP2 : ∀ a, h ≫ y ((N' / N) • a) = h ≫ (toUnit Z ≫ o.eta a) := fun a => by
    rw [hh, hlev, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  obtain ⟨h', hh'⟩ := (Hi T h).1 ((HU T h).1 ⟨hP1, hP2⟩)
  refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hh], fun g hg => ?_⟩
  have : g ≫ i = h' ≫ i := R.ext fun a => by
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hh]
  exact (cancel_mono i).1 this

theorem exists_liftScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → N ∣ N' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (ηu : D.La → (Y ⟶ o.A)), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (IsLift o N' T lv → ∃! f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) ∧ ((∃ f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) → IsLift o N' T lv) := by
  intro p _ D R _ b N N' hc hd S _ s o
  obtain ⟨Z, et, hZf, hZe, eadd, eker, elin, elev, huniv⟩ := exists_liftHom o N' hc hd
  haveI := hZf
  haveI := hZe
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hsp : ∀ {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ Z.left)
      (x' : Sp k' ⟶ Z.left) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u →
      (TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a) ↔
        TateAt o N' (x' ≫ Z.hom) (fun a => (Over.homMk x' rfl : Over.mk (x' ≫ Z.hom) ⟶ Z) ≫ et a)) :=
    fun x x' u u' h => GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points p D R b N N' hc S s o Z et eadd eker elin x x' u u' h
  let U : Set Z.left := {z | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ Z.left),
    z ∈ Set.range x.base ∧
      TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a)}
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z.left),
      TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a) ↔
        Set.range x.base ⊆ U := by
    intro k _ _ x
    refine ⟨fun hG z hz => ⟨k, inferInstance, inferInstance, x, hz, hG⟩, fun hx => ?_⟩
    let pt : Sp k := (⊥ : PrimeSpectrum k)
    obtain ⟨k', _, _, x', ⟨u', hu'⟩, hG'⟩ := hx ⟨pt, rfl⟩
    exact (hsp x x' pt u' (hu' ▸ specializes_rfl)).2 hG'
  have hclo : IsClopen U := by
    refine GlobalTheory.SpecGenClopen.isClopen_of_specializes_iff Z.left U fun z w hzw => ?_
    constructor
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := FinEt.exists_algClosed_point Z.left w
      obtain ⟨u', hu'⟩ : w ∈ Set.range x'.base := by rw [show Set.range x'.base = {w} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩, (hsp x' x u' u ?_).2 hG⟩
      rw [hu, hu']
      exact hzw
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := FinEt.exists_algClosed_point Z.left z
      obtain ⟨u', hu'⟩ : z ∈ Set.range x'.base := by rw [show Set.range x'.base = {z} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩, (hsp x x' u u' ?_).1 hG⟩
      rw [hu, hu']
      exact hzw
  let U' : Z.left.Opens := ⟨U, hclo.isOpen⟩
  obtain ⟨V, i, hV1, hV2, hmono, Hi⟩ := exists_sub U' hclo.isClosed
  refine ⟨V, fun a => i ≫ et a, hV1, hV2, fun T lv => ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · obtain ⟨hadd, hker, hlin, hlev, hgeo⟩ := hL
    obtain ⟨h, hh, hu⟩ := huniv T lv hadd hker hlin hlev
    have hr : Set.range h.left ⊆ U' := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := FinEt.exists_algClosed_point T.left t
      obtain ⟨u, hu⟩ : t ∈ Set.range x.base := by rw [show Set.range x.base = {t} from hx]; rfl
      have hG := tateAt_congr o N' (x' := (x ≫ h.left) ≫ Z.hom)
        (by rw [Category.assoc, Over.w h]) _
        (fun a => (Over.homMk (x ≫ h.left) rfl : Over.mk ((x ≫ h.left) ≫ Z.hom) ⟶ Z) ≫ et a)
        (fun a => by rw [← hh a, ← Category.assoc, ← Category.assoc]; congr 1; try (ext; simp)) (hgeo k x)
      refine (key k (x ≫ h.left)).1 hG ⟨u, ?_⟩
      rw [Scheme.Hom.comp_apply, hu]
    obtain ⟨h', hh'⟩ := (Hi T h).1 hr
    refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hh], fun g hg => ?_⟩
    have : g ≫ i = h := hu _ fun a => by rw [Category.assoc]; exact hg a
    exact (cancel_mono i).1 (this.trans hh'.symm)
  · obtain ⟨f, hf⟩ := hex
    have hf' : ∀ a, lv a = (f ≫ i) ≫ et a := fun a => by rw [Category.assoc]; exact (hf a).symm
    refine ⟨fun a c => by rw [hf', hf', hf', eadd, MonObj.comp_mul], fun a => by rw [hf', eker, MonObj.comp_one],
      fun c a => by rw [hf', hf', elin]; simp only [Category.assoc], fun a => ?_, fun k _ _ x => ?_⟩
    · rw [hf', elev, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    have hr : Set.range (f ≫ i).left ⊆ U' := (Hi T (f ≫ i)).2 ⟨f, rfl⟩
    have hG := (key k (x ≫ (f ≫ i).left)).2 fun z ⟨u, hu⟩ => hr ⟨x.base u, by rw [← hu, Scheme.Hom.comp_apply]⟩
    refine tateAt_congr o N' (by rw [Category.assoc, Over.w (f ≫ i)]) _ _ ?_ hG
    intro a
    rw [hf' a]
    simp only [← Category.assoc]
    congr 1
    try (ext; simp)

end GlobalTheory.UPel.HT
