import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FullPoint

theorem hasGen_of_point {X Y : Scheme.{0}} {k : Type} [Field k] (p : Y ⟶ Sp k) {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {U : (Sp k).Opens} {s : Sp k} (hs : s ∈ U) {ψ : K → ((p ⁻¹ᵁ U).toScheme ⟶ X)}
    (hψ : ∀ i, ψ i = (p ⁻¹ᵁ U).ι ≫ φ i) (h : MulPull.HasGen L ψ ε) : MulPull.HasGen L φ ε := by
  obtain rfl : U = ⊤ := eq_top_iff.2 fun x _ => by
    rwa [Subsingleton.elim (α := PrimeSpectrum k) x s]
  have e : φ = fun i => Y.topIso.inv ≫ ψ i := funext fun i => by
    rw [hψ]
    exact ((Y.topIso.inv_hom_id_assoc _)).symm
  rw [e]
  exact MulPull.HasGen.pull h _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem lbIso_of_rosatiAdj {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) {f g : A ⟶ A} (h : RosatiAdj A L f g) :
    LBIso (cubeLB A ![fst A A ≫ f, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ g] L) := by
  obtain ⟨U, hU, h⟩ := h (default : PrimeSpectrum k)
  have e := (PrimNorm.hasGen_iff hL _ _).1 (hasGen_of_point (A ⊗ A).hom hU (fun _ => rfl) h)
  refine (PrimNorm.lbIso_iff hL _ _ _ _).2 ((PrimNorm.prod_square_id _ _ (PrimNorm.cls L)).trans
    (Eq.trans ?_ (PrimNorm.prod_square_id _ _ (PrimNorm.cls L)).symm))
  rw [Fin.prod_univ_six] at e
  let m : ((A ⊗ A) ⟶ A) → PrimNorm.PullClass L (A ⊗ A).left := fun q => PrimNorm.cls L q.left
  have e' : m ((fst A A ≫ f) * snd A A) ^ (1 : ℤ) * m (fst A A ≫ f) ^ (-1 : ℤ) * m (snd A A) ^ (-1 : ℤ) *
      m (fst A A * (snd A A ≫ g)) ^ (-1 : ℤ) * m (fst A A) ^ (1 : ℤ) * m (snd A A ≫ g) ^ (1 : ℤ) = 1 := e
  show PrimNorm.diff₂ m _ _ = PrimNorm.diff₂ m _ _
  rw [← mul_inv_eq_one, ← e', PrimNorm.diff₂, PrimNorm.diff₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, zpow_neg, zpow_one]
  abel

theorem exists_tateIso_up (laws : Laws) {S : Scheme.{0}} (P : PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) {K Ω : Type}
    [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S}
    (u : Over.mk x' ⟶ Over.mk x) (hu : u.left = spMap i)
    (I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D Ω (Over.mk x' ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => WeilIs P.A P.L n y y' (unitOn c)),
      (∀ n, (I'.ζ n : Ω) = i (I.ζ n)) ∧ ∀ n v, I'.ev n v = u ≫ I.ev n v := by
  have : CharZero Ω := (RingHom.charZero_iff i.injective).1 ‹_›
  let f : (Over.mk x ⟶ P.A) →* (Over.mk x' ⟶ P.A) := MonoidHom.mk' (u ≫ ·) (MonObj.comp_mul u)
  have hinj : Function.Injective f := TorsionFieldExt.comp_injective u P.A
  have hu' : ∀ c : Kˣ, unitOn (Units.map i.toMonoidHom c) = Units.map u.left.appTop.hom.toMonoidHom (unitOn c) :=
    fun c => by
      rw [hu]
      exact Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)))
  refine ⟨{ ζ := fun n => Units.map i.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (Units.map_injective i.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n v => f (I.ev n v)
            add := fun n a b => by rw [I.add, map_mul]
            lin := fun n c a => by rw [I.lin]; exact (Category.assoc u (I.ev n a) (act c)).symm
            ker := fun n hn a => by rw [← I.ker n hn a, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm]
            isom := fun n hn a b => by
              rw [← map_zpow, hu']
              exact CommPairing.weilIs_pull laws.globalFns P.isAb P.isLB u (I.isom n hn a b) },
    fun _ => rfl, fun _ _ => rfl⟩
  · obtain ⟨y, hy, rfl⟩ := TorsionFieldExt.exists_of_isAlgClosed laws P u (Nat.cast_ne_zero.2 hn.ne')
      (Nat.cast_ne_zero.2 hn.ne') z hz
    obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]

theorem exists_eq_nsmul (l : Geo.Tor.Level H) {J J' : Ideal (𝓞 E)}
    (hJ : J * J' = Ideal.span {(l.M : 𝓞 E)}) {e : 𝓞 E} (he : e ∈ J) {a : D.La}
    (ha : a ∈ J' • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c, e • a = l.M • c := by
  have h1 : e • a ∈ (J * J') • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he ha
  rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨c, -, hc⟩ := h1
  exact ⟨c, by rw [← hc, Nat.cast_smul_eq_nsmul]⟩

theorem exists_sab (laws : Laws) {K : Type} [Field K] (o : Full D K) :
    letI := H.starRing
    ∃ (PP : RigLB o.P.A) (_ : CubicalStr o.P.A PP), PP.L = o.P.L ∧ PP.IsSymmetric := by
  obtain ⟨rig, hrig⟩ := o.P.rigid
  let PP : RigLB o.P.A := ⟨o.P.L, rig, o.P.isLB, hrig⟩
  obtain ⟨cub⟩ := (laws.cube _ o.P PP rfl).1
  obtain ⟨U, hU, h⟩ := o.P.sym (default : PrimeSpectrum K)
  refine ⟨PP, cub, rfl, PrimNorm.isSymmetric_of_hasGen PP (hasGen_of_point o.P.A.hom hU (fun i => ?_) h)⟩
  fin_cases i
  · rfl
  · exact (Category.comp_id _).symm

theorem eta_smul {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) {e : 𝓞 E} (he : 1 - e ∈ l.Mb) (v : D.La) : o.eta (e • v) = o.eta v := by
  have h : v = e • v + (1 - e) • v := by rw [← add_smul, add_sub_cancel, one_smul]
  conv_rhs => rw [h]
  rw [o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul he trivial), _root_.mul_one]

def IsFibre {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (ob : Obj D l b s) {K : Type} [Field K] (y : Sp K ⟶ S) (o : Full D K) : Prop :=
  letI := H.starRing
  ∃ φ : o.P.A.left ⟶ ob.t.G.left, IsGrpPullback o.P.A ob.t.G y φ ∧ LBIso o.P.L (ob.t.PP.L.pull φ) ∧
    (∀ x, (o.oa.act x).left ≫ φ = φ ≫ (ob.t.act.act x).left) ∧
    (∀ v, (o.I.ev l.A v).left ≫ φ = y ≫ (ob.etaA v).left) ∧
    ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), (o.I.ev l.M v).left ≫ φ = y ≫ (ob.eta v).left

theorem exists_obj (laws : Laws) (l : Geo.Tor.Level H) {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (o : Full D K)
    (b : Base l K) (hρ : b.ρ = o.ρ) (hζ : b.ζ = o.I.ζ l.A) :
    ∃ ob : Obj D l b (𝟙 (Sp K)), ∀ {B : Type} [CommRing B] {b' : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
      (ob' : Obj D l b' s) (y : Sp K ⟶ S), Nonempty (ObjMap ob ob' y) ↔ IsFibre ob' y o := by
  letI := H.starRing
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨⟨L, rig, hL, hrig⟩, cub, rfl, sym⟩ := exists_sab laws o
  obtain ⟨f, hf, e, he, hfe⟩ : ∃ f ∈ l.Mb, ∃ e ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), f + e = 1 :=
    Submodule.mem_sup.1 (by rw [l.coprime]; trivial)
  have h2 : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      o.I.ev l.M a = o.I.ev l.M (e • a) := fun a ha => by
    obtain ⟨c, hc⟩ := exists_eq_nsmul l l.prod hf ha
    have h1 : a = e • a + l.M • c := by rw [← hc, ← add_smul, add_comm, hfe, one_smul]
    conv_lhs => rw [h1]
    rw [o.I.add, (o.I.ker _ hM _).2 ⟨c, rfl⟩, _root_.mul_one]
  let t : SAB H (Sp K) :=
    { G := o.P.A, semi := isSemiAbelian_of_isAbelianScheme _ o.P.isAb, act := ofRingAct o.oa.toRingAct
      PP := ⟨o.P.L, rig, hL, hrig⟩, cub := cub, sym := sym
      adj := fun a => lbIso_of_rosatiAdj o.P.isLB (o.oa.rosati a), prim := o.prim }
  refine ⟨{ t := t, proper := o.P.isAb.proper, ample := o.P.ample, ktriv := o.P.ktriv
            eta := fun a => o.I.ev l.M (e • a)
            eta_add := fun a c => by rw [smul_add]; exact o.I.add _ _ _
            eta_ker := fun a ha => (o.I.ker _ hM _).2
              (exists_eq_nsmul l (by rw [mul_comm]; exact l.prod) he ha)
            etaA := o.I.ev l.A
            etaA_add := o.I.add _
            etaA_ker := fun a => (o.I.ker _ l.A_pos _).2 ⟨a, rfl⟩
            geom := ?_ }, fun ob' y => ⟨?_, ?_⟩⟩
  · intro k _ _ x β hx
    obtain rfl : x = spMap β := (Category.comp_id x).symm.trans hx
    have := o.P.isAb.smooth
    refine ⟨by rw [hρ]; exact LieExt.detCond_extend D β o.P.A _ o.det, ?_⟩
    obtain ⟨I', hζ', hev⟩ := exists_tateIso_up laws o.P o.oa.act β (x := 𝟙 _) (x' := spMap β) (toUnit _)
      (ObjPull.toUnit_left' _) o.I
    refine ⟨I', by rw [hζ', hζ], fun a => (hev _ _).symm, fun a ha => Eq.trans ?_ (hev _ _).symm⟩
    rw [h2 a ha]
  · rintro ⟨m⟩
    obtain ⟨w, hw, -⟩ := m.lin
    refine ⟨m.cm.F, m.cart, ⟨w, hw⟩, m.act, m.etaA, fun v hv => ?_⟩
    rw [h2 v hv]
    exact m.eta v
  · rintro ⟨φ, h₁, h₂, h₃, h₄, h₅⟩
    obtain ⟨m, rfl⟩ := exists_sabMap_of_isProper_of_lbIso laws.globalFns E H _ _ ob'.t t y φ ob'.proper h₁ h₂ h₃
    refine ⟨⟨m, fun v => ?_, h₄⟩⟩
    rw [← eta_smul ob' (e := e) (by rw [← hfe, add_sub_cancel_right]; exact hf) v]
    exact h₅ _ (Submodule.smul_mem_smul he trivial)

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_isFibre {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (ob : Obj D l b s) {K : Type} [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) :
    ∃ o : Full D K, IsFibre ob y o ∧
      ∀ f : B →+* K, y ≫ s = spMap f → o.ρ = f b.ρ ∧ (o.I.ζ l.A : K) = f b.ζ := by
  letI := H.starRing
  obtain ⟨o', ⟨m⟩⟩ := ObjPull.objPull_of_pol (PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally)
    E H D l B B b b (RingHom.id B) S (Sp K) s (y ≫ s) y rfl rfl
    (by rw [show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]) ob
  let β : B →+* K := (Spec.preimage (y ≫ s)).hom
  obtain ⟨hdet, I, hI, hA, hM⟩ := o'.geom K (𝟙 _) β ((Category.id_comp _).trans (Spec.map_preimage (y ≫ s)).symm)
  obtain ⟨w, hw, -⟩ := m.lin
  have u : (toUnit (Over.mk (𝟙 (Sp K)))).left = 𝟙 _ := ObjPull.toUnit_left' _
  refine ⟨{ P := Obj.toPolAV o', oa := ⟨o'.t.act.toRingAct, o'.t.rosatiAdj⟩, prim := o'.t.prim, ρ := β b.ρ
            ρ_sq := by rw [← map_pow, b.ρ_sq, map_neg, map_natCast]
            det := hdet, I := I, closed := ‹_› },
    ⟨m.cm.F, m.cart, ⟨w, hw⟩, m.act, fun v => ?_, fun v hv => ?_⟩, fun f hf => ?_⟩
  · refine Eq.trans (congrArg (fun q => q.left ≫ m.cm.F) (hA v)).symm ?_
    rw [Over.comp_left, u]
    exact (congrArg (· ≫ m.cm.F) (Category.id_comp _)).trans (m.etaA v)
  · refine Eq.trans (congrArg (fun q => q.left ≫ m.cm.F) (hM v hv)).symm ?_
    rw [Over.comp_left, u]
    exact (congrArg (· ≫ m.cm.F) (Category.id_comp _)).trans (m.eta v)
  · obtain rfl : β = f := spMap_inj ((Spec.map_preimage (y ≫ s)).trans hf)
    exact ⟨rfl, hI⟩

theorem IsFibre.ext {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    {ob : Obj D l b s} {K K' : Type} [Field K] [Field K'] (f : K →+* K') {y : Sp K ⟶ S} {o : Full D K}
    {o' : Full D K'} (h : IsFibre ob y o) (ψ : o'.P.A.left ⟶ o.P.A.left)
    (g₁ : IsGrpPullback o'.P.A o.P.A (spMap f) ψ) (g₂ : LBIso o'.P.L (o.P.L.pull ψ))
    (g₃ : letI := H.starRing; ∀ x, (o'.oa.act x).left ≫ ψ = ψ ≫ (o.oa.act x).left)
    (g₄ : ∀ n v, 0 < n → (o'.I.ev n v).left ≫ ψ = spMap f ≫ (o.I.ev n v).left) : IsFibre ob (spMap f ≫ y) o' := by
  obtain ⟨φ, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨ψ ≫ φ, g₁.comp h₁, LBIso.trans o'.P.isLB (pull_isLB o.P.isLB _) (pull_isLB ob.t.PP.isLB _) g₂
    (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (chartPullSame ob.t.PP.L (fun _ : PUnit => ψ ≫ φ) (fun _ => φ) (fun _ => 1) ψ fun _ => rfl) h₂),
    fun x => ?_, fun v => ?_, fun v hv => ?_⟩
  · rw [← Category.assoc, g₃, Category.assoc, h₃, Category.assoc]
  · refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) (g₄ _ v l.A_pos))).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (h₄ v)).trans (Category.assoc _ _ _).symm)
  · refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) (g₄ _ v hM))).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (h₅ v hv)).trans (Category.assoc _ _ _).symm)

theorem existsUnique_point (laws : Laws) {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K] [IsAlgClosed K] (bF : c.F →+* K) (o : Full D K)
    (hρ : ∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) (hζ : ∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) :
    ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ IsFibre Y.oF y o := by
  have : CharZero K := (RingHom.charZero_iff bF.injective).1 inferInstance
  let b : Base l K :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne'), ρ := o.ρ, ρ_sq := o.ρ_sq, ζ := o.I.ζ l.A
      ζ_prim := (o.I.ζ_prim _ l.A_pos).map_of_injective (f := Units.coeHom K) Units.val_injective }
  obtain ⟨ob, hob⟩ := exists_obj laws l o b rfl rfl
  let i : KA l →+* c.F := (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo K b (bF.comp i) (Sp K) (𝟙 _) ob
    inferInstance (hρ _ rfl).symm (hζ _ rfl).symm
  rw [Category.id_comp, spMap_comp] at hf
  let y : Sp K ⟶ Xo.XF c := pullback.lift f (spMap bF) hf
  have hy : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  refine ⟨y, ⟨pullback.lift_snd _ _ _, (hob _ _).1 ?_⟩, fun y' ⟨h₁, h₂⟩ => ?_⟩
  · rw [← hy] at m
    obtain ⟨m', -⟩ := ObjComp.objMap_cancel Y.m0 m
    exact ⟨m'⟩
  · obtain ⟨m'⟩ := (hob _ _).2 h₂
    obtain ⟨m'', -⟩ := ObjComp.objMap_comp Y.m0 m'
    refine pullback.hom_ext ((hu _ ⟨?_, ⟨m''⟩⟩).trans hy.symm) (h₁.trans (pullback.lift_snd _ _ _).symm)
    rw [Category.id_comp, spMap_comp, Category.assoc, pullback.condition, ← Category.assoc, h₁]

end GlobalTheory.FullPoint
end
