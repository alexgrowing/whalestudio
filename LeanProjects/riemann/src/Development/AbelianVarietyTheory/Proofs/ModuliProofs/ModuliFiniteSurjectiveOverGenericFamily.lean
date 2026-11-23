import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabMapCubical
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjOfObj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdealStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ModFam

open GlobalTheory.LevCover GlobalTheory.ObjPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {S S' : Scheme.{0}}

theorem exists_tate_of_lin (hc : l.A.Coprime l.M) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) (α : D.La → Q)
    (hadd : ∀ a c, α (a + c) = α a * α c) (hker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), α a = 1)
    (hlin : ∀ c a, α (c • a) = act c (α a)) (hinj : ∀ a, α a = 1 → a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ I' : TateIso D k Q act e, I'.ζ l.A = I.ζ l.A ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La), α a = I'.ev l.M a := by
  have hN := M_pos l
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpq
  · have := D.fin
    have := D.proj
    have : Module.IsTorsionFree (𝓞 E) D.La := inferInstance
    have : Subsingleton D.La := Module.finrank_zero_iff.1 (D.rank.trans h0)
    refine ⟨I, rfl, fun _ => rfl, fun a _ => ?_⟩
    rw [Subsingleton.elim a 0, add_map_zero hadd, add_map_zero (I.add _)]
  have hpow : ∀ a, α a ^ l.M = 1 := fun a => by rw [← add_map_nsmul hadd, hker _ (nsmul_M_mem l a)]
  obtain ⟨f, hf⟩ : ∃ f : D.La →ₗ[𝓞 E] D.La, ∀ a, α a = I.ev l.M (f a) := by
    have hs : ∀ a, ∃ b, I.ev l.M b = α a := fun a => (I.onto _ hN _).1 (hpow a)
    choose s hs using hs
    let P : Submodule (𝓞 E) D.La := LinearMap.range (l.M • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
    have hP : ∀ a b : D.La, P.mkQ a = P.mkQ b ↔ I.ev l.M a = I.ev l.M b := by
      intro a b
      rw [tateIso_ev_eq_iff I hN, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
    let φ : D.La →ₗ[𝓞 E] D.La ⧸ P :=
      { toFun := fun a => P.mkQ (s a)
        map_add' := fun a b => by rw [← map_add, hP, I.add, hs, hs, hs, hadd]
        map_smul' := fun c a => by rw [RingHom.id_apply, ← map_smul, hP, I.lin, hs, hs, hlin] }
    haveI := D.proj
    obtain ⟨f, hf⟩ := Module.projective_lifting_property P.mkQ φ P.mkQ_surjective
    refine ⟨f, fun a => ?_⟩
    have h : P.mkQ (f a) = P.mkQ (s a) := LinearMap.congr_fun hf a
    rw [(hP _ _).1 h, hs]
  obtain ⟨ε, he, he'⟩ := exists_idem l
  obtain ⟨g, g1, g2, g3⟩ := GlobalTheory.T.exists_similitude_of_aut_mod_levelIdeal E H D l l.A f hpq l.A_pos hc fun x hx => by
    have h1 : ε • x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := hinj _ (by
      rw [hf, map_smul]; exact (I.ker _ hN _).2 (modN_smul_Mb l he hx))
    have h2 : x = ε • x + (1 - ε) • x := by rw [← add_smul, add_sub_cancel, one_smul]
    rw [h2]
    exact Submodule.add_mem _ h1 (Submodule.smul_mem_smul he' Submodule.mem_top)
  refine ⟨LevelTwist.twist I g ((SimAlg.sim_group E H D hpq).1 g), ?_, fun a => LevelTwist.ev_congr I l.A_pos (g2 a),
    fun a ha => ?_⟩
  · rw [LevelTwist.twist_ζ, LevelTwist.zeta_zpow_congr I l.A_pos g3, zpow_one]
  · rw [hf]
    exact (LevelTwist.ev_congr I hN (modN_of_mem_both l (g1 a)
      (Submodule.sub_mem _ (LevelTwist.map_mem_smul_top _ _ ha) (LevelTwist.map_mem_smul_top _ _ ha)))).symm

theorem fullObj_pull {n N : ℕ} {s : S ⟶ Sp (RZ H n N)} {t : SAB H S} {lev : D.La → (𝟙_ (Over S) ⟶ t.G)}
    (o : FullObj D s t lev) {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) :
    FullObj D (f ≫ s) t' fun a => ObjPull.secPull m.cart (lev a) := by
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  obtain ⟨-, hamp, hk⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S' t.G t'.G f m.cm.F
    t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB (AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi) m.cart hL
  refine ⟨MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr, hamp o.ample, hk o.ktriv,
    fun a c => by rw [o.add, map_mul], fun a => by rw [o.ker a, map_one], fun k _ _ _ x β hx => ?_⟩
  obtain ⟨hdet, I, hI, hA⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
  refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
    hI, fun a => ?_⟩
  · rw [GlobalTheory.LiePull.lieMult_pull _ S S' t.G t'.G f m.cm.F t.act t'.act m.cart m.act k x τ,
      GlobalTheory.LiePull.lieMult_pull _ S S' t.G t'.G f m.cm.F t.act t'.act m.cart m.act k x τ]
    exact hdet τ
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
  · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))

structure IsLev (l : Level H) (t : SAB H S) (T : Over S) (χ : D.La → (T ⟶ t.G)) : Prop where
  add : ∀ a c, χ (a + c) = χ a * χ c
  ker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), χ a = 1
  lin : ∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ T.left) c a,
    z ≫ (χ (c • a)).left = z ≫ (χ a ≫ t.act.act c).left
  inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ T.left) a,
    z ≫ (χ a).left = z ≫ (1 : T ⟶ t.G).left → a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)

theorem toUnit_comp_left {T G : Over S} (σ : 𝟙_ (Over S) ⟶ G) : (toUnit T ≫ σ).left = T.hom ≫ σ.left := by
  rw [Over.comp_left, toUnit_left']

theorem mem_of_idem {ε : 𝓞 E} (he' : 1 - ε ∈ l.Mb) {x : D.La} (h : D.ModN l.M (ε • x)) :
    x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, hb⟩ := h
  have h2 : x = ε • x + (1 - ε) • x := by rw [← add_smul, add_sub_cancel, one_smul]
  rw [h2, hb]
  exact Submodule.add_mem _ (nsmul_M_mem l b) (Submodule.smul_mem_smul he' Submodule.mem_top)

theorem isLev_obj {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s) :
    IsLev l o.t (𝟙_ (Over S)) o.eta := by
  obtain ⟨ε, he, he'⟩ := exists_idem l
  have hidem : ∀ a, o.eta (ε • a) = o.eta a := fun a => by
    have : a = ε • a + (1 - ε) • a := by rw [← add_smul, add_sub_cancel, one_smul]
    conv_rhs => rw [this, o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul he' Submodule.mem_top), _root_.mul_one]
  refine ⟨o.eta_add, o.eta_ker, fun k _ _ z c a => ?_, fun k _ _ z a h => ?_⟩
  · obtain ⟨-, I, -, -, hI⟩ := o.geom k z (Spec.preimage (z ≫ s)).hom (Spec.map_preimage _).symm
    have h : toUnit (Over.mk z) ≫ o.eta (c • a) = toUnit (Over.mk z) ≫ o.eta a ≫ o.t.act.act c := by
      rw [← hidem, ← hidem a, ← Category.assoc, hI _ (Submodule.smul_mem_smul he Submodule.mem_top),
        hI _ (Submodule.smul_mem_smul he Submodule.mem_top), smul_comm, I.lin]
    exact (toUnit_comp_left _).symm.trans ((congrArg (·.left) h).trans (toUnit_comp_left _))
  · obtain ⟨-, I, -, -, hI⟩ := o.geom k z (Spec.preimage (z ≫ s)).hom (Spec.map_preimage _).symm
    have h' : toUnit (Over.mk z) ≫ o.eta a = toUnit (Over.mk z) ≫ 1 :=
      Over.OverMorphism.ext ((toUnit_comp_left _).trans (h.trans (toUnit_comp_left (T := Over.mk z) _).symm))
    rw [MonObj.comp_one, ← hidem, hI _ (Submodule.smul_mem_smul he Submodule.mem_top), I.ker _ (M_pos l)] at h'
    exact mem_of_idem he' h'

def objOfFull (hc : l.A.Coprime l.M) {n : ℕ} {β : RZ H n l.A →+* KA l}
    (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) {s : S ⟶ Sp (KA l)} {t : SAB H S}
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} (o : FullObj D (s ≫ spMap β) t lev) {χ : D.La → (𝟙_ (Over S) ⟶ t.G)}
    (hχ : IsLev l t (𝟙_ (Over S)) χ) : Obj D l (baseKA l) s where
  t := t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta := χ
  eta_add := hχ.add
  eta_ker := hχ.ker
  etaA := lev
  etaA_add := o.add
  etaA_ker := o.ker
  geom k _ _ x δ hx := by
    have : CharZero k := (RingHom.charZero_iff δ.injective).1 inferInstance
    have hρ : β (RZ.rt H n l.A) = (baseKA l).ρ := Subtype.ext ((hβ _).trans (RZ.rt_coe _ _))
    have hζ : β (RZ.ze H n l.A) = (baseKA l).ζ := Subtype.ext (hβ _)
    obtain ⟨hd, I, hz, ha⟩ := o.geom k x (δ.comp β) (by rw [← Category.assoc, hx, spMap_comp])
    rw [RingHom.comp_apply, hρ] at hd
    rw [RingHom.comp_apply, hζ] at hz
    obtain ⟨I', h1, h2, h3⟩ := exists_tate_of_lin hc I (fun a => toUnit (Over.mk x) ≫ χ a)
      (fun a c => by rw [hχ.add, MonObj.comp_mul]) (fun a ha => by rw [hχ.ker a ha, MonObj.comp_one])
      (fun c a => Over.OverMorphism.ext ((toUnit_comp_left _).trans ((hχ.lin k x c a).trans
        ((toUnit_comp_left (T := Over.mk x) _).symm.trans (congrArg Over.Hom.left (Category.assoc _ _ _).symm)))))
      (fun a h => hχ.inj k x a ((toUnit_comp_left (T := Over.mk x) _).symm.trans
        ((congrArg (·.left) (h.trans (MonObj.comp_one _).symm)).trans (toUnit_comp_left _))))
    exact ⟨hd, I', by rw [h1, hz], fun a => (ha a).trans (h2 a).symm, h3⟩

theorem exists_secEquiv {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) :
    ∃ Ψ : (𝟙_ (Over S') ⟶ t'.G) ≃* (Over.mk f ⟶ t.G), (∀ σ, (Ψ σ).left = σ.left ≫ m.φ) ∧
      (∀ σ c, Ψ (σ ≫ t'.act.act c) = Ψ σ ≫ t.act.act c) ∧
      ∀ (X : Scheme.{0}) (z : X ⟶ S') σ σ', z ≫ (Ψ σ).left = z ≫ (Ψ σ').left ↔ z ≫ σ.left = z ≫ σ'.left := by
  have key : ∀ z : S' ⟶ S, (𝟙_ (Over S')).hom ≫ f = z →
      ∃ Ψ : (𝟙_ (Over S') ⟶ t'.G) ≃* (Over.mk z ⟶ t.G), ∀ σ, (Ψ σ).left = σ.left ≫ m.φ := by
    rintro _ rfl
    exact ⟨pushEquiv m.cart _, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ := key f (Category.id_comp f)
  refine ⟨Ψ, hΨ, fun σ c => Over.OverMorphism.ext ?_, fun X z σ σ' => ?_⟩
  · rw [hΨ, Over.comp_left, Over.comp_left, hΨ, Category.assoc, Category.assoc]
    exact congrArg _ (m.act c)
  · rw [hΨ, hΨ]
    refine ⟨fun h => m.cart.1.hom_ext ?_ ?_, fun h => ?_⟩
    · exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) ((Over.w σ).trans (Over.w σ').symm)).trans
        (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.φ) h).trans (Category.assoc _ _ _))

theorem IsLev.push {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {χ : D.La → (𝟙_ (Over S') ⟶ t'.G)} (h : IsLev l t' _ χ) :
    ∃ χ' : D.La → (Over.mk f ⟶ t.G), IsLev l t _ χ' ∧ ∀ a, (χ' a).left = (χ a).left ≫ m.φ := by
  obtain ⟨Ψ, h1, h2, h3⟩ := exists_secEquiv m
  refine ⟨fun a => Ψ (χ a), ⟨fun a c => by rw [h.add, map_mul], fun a ha => by rw [h.ker a ha, map_one],
    fun k _ _ z c a => ?_, fun k _ _ z a e => ?_⟩, fun a => h1 _⟩
  · rw [← h2]
    exact (h3 _ z _ _).2 (h.lin k z c a)
  · rw [← map_one Ψ] at e
    exact h.inj k z a ((h3 _ z _ _).1 e)

theorem IsLev.pull {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {χ' : D.La → (Over.mk f ⟶ t.G)} (h : IsLev l t _ χ') :
    ∃ χ : D.La → (𝟙_ (Over S') ⟶ t'.G), IsLev l t' _ χ ∧ ∀ a, (χ' a).left = (χ a).left ≫ m.φ := by
  obtain ⟨Ψ, h1, h2, h3⟩ := exists_secEquiv m
  refine ⟨fun a => Ψ.symm (χ' a), ⟨fun a c => by rw [h.add, map_mul], fun a ha => by rw [h.ker a ha, map_one],
    fun k _ _ z c a => (h3 _ z _ _).1 ?_, fun k _ _ z a e => h.inj k z a ?_⟩, fun a => ?_⟩
  · rw [h2, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact h.lin k z c a
  · have := (h3 _ z _ _).2 e
    rwa [map_one, MulEquiv.apply_symm_apply] at this
  · rw [← h1, MulEquiv.apply_symm_apply]

theorem clopenCond_pt (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) {T : Over S} (x y : T ⟶ G) (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ClopenCond T fun _ h => h ≫ x = h ≫ y := by
  obtain ⟨Z, et, R⟩ := exists_finiteEtale_latticeTorsionHom S G n ℤ hG hn
  refine (RepTors.clopenCond (et := et) R (fun a : ℤ => x ^ a) (fun a : ℤ => y ^ a) (fun a c => zpow_add _ _ _)
    (fun a => by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow])
    (fun a c => zpow_add _ _ _)
    (fun a => by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow])).congr
    fun T' h => ⟨fun e a => ?_, fun e => by simpa using e 1⟩
  exact (map_zpow (preHom h) x a).trans ((congrArg (· ^ a) e).trans (map_zpow (preHom h) y a).symm)

theorem IsLev.closure {t : SAB H S} (hG : IsAbelianScheme t.G) (hn : IsUnit (l.M : Γ(S, ⊤))) {T Z V : Over S}
    {et : D.La → (Z ⟶ t.G)} (hadd : ∀ a c, et (a + c) = et a * et c) (hpow : ∀ a, et a ^ l.M = 1) (h : T ⟶ Z)
    (hh : IsLev l t T fun a => h ≫ et a) (i : V ⟶ Z) (hi : Set.range i.left ⊆ closure (Set.range h.left)) :
    IsLev l t V fun a => i ≫ et a := by
  refine ⟨fun a c => by rw [hadd, MonObj.comp_mul], fun a ha => ?_, fun k _ _ z c a => ?_, fun k _ _ z a e => ?_⟩
  · obtain ⟨U, hU, HU⟩ := clopenCond_pt t.G hG hn (et a) 1 (hpow a) (one_pow _)
    have := (HU V i).2 (hi.trans (closure_minimal
      ((HU T h).1 ((hh.ker a ha).trans (MonObj.comp_one _).symm)) hU))
    exact this.trans (MonObj.comp_one _)
  · have := t.act.hom c
    obtain ⟨U, hU, HU⟩ := clopenCond_pt t.G hG hn (et (c • a)) (et a ≫ t.act.act c) (hpow _)
      (by rw [← MonObj.pow_comp, hpow, MonObj.one_comp])
    have := (HU V i).2 (hi.trans (closure_minimal (range_subset_of_geom h U fun k _ _ x y =>
      (HU _ _).1 (Over.OverMorphism.ext (by simpa using hh.lin k y.left c a))) hU))
    beta_reduce at this ⊢
    rw [this, Category.assoc]
  · by_contra ha
    obtain ⟨U, -, HU⟩ := clopenCond_pt t.G hG hn (et a) 1 (hpow a) (one_pow _)
    have h1 : Set.range h.left ⊆ (U : Set Z.left)ᶜ := range_subset_of_geom h _ fun k _ _ x y => by
      rintro _ ⟨p, rfl⟩ hp
      have := (HU _ (y ≫ h)).2 (by
        rintro _ ⟨q, rfl⟩
        rwa [Subsingleton.elim (α := PrimeSpectrum k) q p])
      refine ha (hh.inj k y.left a ?_)
      beta_reduce at this
      rw [MonObj.comp_one, Category.assoc, ← MonObj.comp_one y] at this
      exact congrArg (·.left) this
    let y : Over.mk (z ≫ V.hom) ⟶ V := Over.homMk z rfl
    have h2 := (HU _ (y ≫ i)).1 (by
      beta_reduce
      rw [MonObj.comp_one, Category.assoc, ← MonObj.comp_one y]
      exact Over.OverMorphism.ext e)
    let p : Sp k := (default : PrimeSpectrum k)
    exact closure_minimal h1 U.isOpen.isClosed_compl (hi ⟨z p, rfl⟩) (h2 ⟨p, by simp [y]⟩)

theorem exists_closure {T Z : Scheme.{0}} [IsReduced T] (h : T ⟶ Z) :
    ∃ (V : Scheme.{0}) (i : V ⟶ Z) (j : T ⟶ V), IsReduced V ∧ IsClosedImmersion i ∧ j ≫ i = h ∧
      Set.range i ⊆ closure (Set.range h) := by
  let W : TopologicalSpace.Closeds Z := ⟨closure (Set.range h), isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal W
  have h2 : I.subschemeι.ker ≤ h.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ReducedSubgroup.vanishingIdeal_le_ker h W subset_closure
  refine ⟨_, I.subschemeι, IsClosedImmersion.lift _ h h2, ReducedSubgroup.isReduced_subscheme_vanishingIdeal W,
    inferInstance, IsClosedImmersion.lift_fac _ _ _, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact subset_rfl

theorem exists_sabPull (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem exists_cancel {S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {u : S'' ⟶ S} (e : g ≫ f = u) (m : SABMap t' t f) (n : SABMap t'' t u) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n

theorem sec_cancel {S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m : SABMap t' t f) (m' : SABMap t'' t' g) (σ' : 𝟙_ (Over S') ⟶ t'.G) (σ'' : 𝟙_ (Over S'') ⟶ t''.G)
    (h : σ''.left ≫ m'.φ ≫ m.φ = g ≫ σ'.left ≫ m.φ) : σ''.left ≫ m'.φ = g ≫ σ'.left := by
  apply m.cart.1.hom_ext
  · exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  · rw [Category.assoc, Category.assoc, m'.cart.1.w, ← Category.assoc, Over.w, Over.w]
    exact (Category.id_comp g).trans (Category.comp_id g).symm

theorem isFinite_of_full (hc : l.A.Coprime l.M) {n : ℕ} {β : RZ H n l.A →+* KA l}
    (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) (Xo : Moduli D l) {s : S ⟶ Sp (KA l)} [IsSeparated s]
    {t : SAB H S} {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} (o : FullObj D (s ≫ spMap β) t lev) (a : Xo.X ⟶ S)
    (ha : a ≫ s = Xo.s) (ν : SABMap Xo.univ.t t a) (hν : ∀ x, (Xo.univ.etaA x).left ≫ ν.φ = a ≫ (lev x).left) :
    IsFinite a := by
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hred : IsReduced Xo.X := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).1
  have := o.proper
  have hG : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hn : IsUnit (l.M : Γ(S, ⊤)) := by
    simpa using ((baseKA l).unit _ (M_pos l)).map ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
  obtain ⟨_, _⟩ := datum_free D
  obtain ⟨Z, et, _, -, hadd, hpow, huniv⟩ := exists_finiteEtale_latticeTorsionHom S t.G l.M D.La hG hn
  obtain ⟨χ, hχ, eχ⟩ := (isLev_obj Xo.univ).push ν
  obtain ⟨h, hh, -⟩ := huniv _ χ hχ.add fun x => by rw [← add_map_nsmul hχ.add, hχ.ker _ (nsmul_M_mem l x)]
  obtain ⟨V, i, j, _, _, hj, hi⟩ := exists_closure (T := Xo.X) h.left
  have hja : j ≫ i ≫ Z.hom = a := by rw [← Category.assoc, hj]; exact Over.w h
  let i' : Over.mk (i ≫ Z.hom) ⟶ Z := Over.homMk i rfl
  have hV := IsLev.closure hG hn hadd hpow h (by simpa only [hh] using hχ) i' hi
  obtain ⟨tV, ⟨m⟩⟩ := exists_sabPull (i ≫ Z.hom) t
  obtain ⟨χV, hχV, eV⟩ := hV.pull m
  have oV : FullObj D (((i ≫ Z.hom) ≫ s) ≫ spMap β) tV _ :=
    (Category.assoc (i ≫ Z.hom) s (spMap β)).symm ▸ fullObj_pull o m
  obtain ⟨g, ⟨hg, ⟨p⟩⟩, -⟩ := Xo.rep V _ inferInstance (objOfFull hc hβ oV hχV)
  obtain ⟨q, hq⟩ := exists_cancel hja m ν
  have q1 : ∀ x, (Xo.univ.eta x).left ≫ q.φ = j ≫ (χV x).left := fun x => sec_cancel m q _ _ (by
    rw [← hq, ← eχ, ← eV, ← hh, Over.comp_left, Over.comp_left, ← hj]
    exact Category.assoc _ _ _)
  have q2 : ∀ x, (Xo.univ.etaA x).left ≫ q.φ = j ≫ (ObjPull.secPull m.cart (lev x)).left := fun x =>
    sec_cancel m q _ _ (by
      rw [← hq, hν, ← hja]
      exact (Category.assoc _ _ _).trans (congrArg (j ≫ ·) (secPull_left m.cart _).symm))
  obtain ⟨r, hr⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ p.toSABMap q
  have hjg : j ≫ g = 𝟙 _ := (Xo.rep _ _ hred Xo.univ).unique
    ⟨by rw [Category.assoc, hg, ← Category.assoc, hja, ha], ⟨⟨r, fun x => by
        refine (congrArg _ hr).trans (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (q1 x))).trans ?_)
        exact (Category.assoc _ _ _).trans ((congrArg (j ≫ ·) (p.eta x)).trans (Category.assoc _ _ _).symm), fun x => by
        refine (congrArg _ hr).trans (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (q2 x))).trans ?_)
        exact (Category.assoc _ _ _).trans ((congrArg (j ≫ ·) (p.etaA x)).trans (Category.assoc _ _ _).symm)⟩⟩⟩
    ⟨Category.id_comp _, ⟨⟨LevelTwist.sabMapId _, fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
      fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩⟩⟩
  have : IsSeparated (g ≫ Xo.s) := by rw [hg]; infer_instance
  have : IsSeparated g := IsSeparated.of_comp g Xo.s
  have : IsClosedImmersion (j ≫ g) := by rw [hjg]; infer_instance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j g
  rw [← hja]
  infer_instance

theorem exists_isLev {n N : ℕ} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {s : Sp k ⟶ Sp (RZ H n N)}
    {t : SAB H (Sp k)} {lev : D.La → (𝟙_ (Over (Sp k)) ⟶ t.G)} (o : FullObj D s t lev) (l : Level H) :
    ∃ χ : D.La → (𝟙_ (Over (Sp k)) ⟶ t.G), IsLev l t _ χ := by
  obtain ⟨-, I, -⟩ := o.geom k (𝟙 _) (Spec.preimage s).hom ((Category.id_comp _).trans (Spec.map_preimage _).symm)
  obtain ⟨ε, he, he'⟩ := exists_idem l
  refine ⟨fun a => I.ev l.M (ε • a), fun a c => ?_, fun a ha => (I.ker _ (M_pos l) _).2 (modN_smul_Mb l he ha),
    fun k' _ _ z c a => ?_, fun k' _ _ z a e => ?_⟩
  · rw [smul_add]
    exact I.add _ _ _
  · beta_reduce
    rw [smul_comm, I.lin]
  · have : Epi (show Sp k' ⟶ Sp k from z) := Flat.epi_of_flat_of_surjective _
    exact mem_of_idem he' ((I.ker _ (M_pos l) _).1 (Over.OverMorphism.ext
      ((cancel_epi (show Sp k' ⟶ Sp k from z)).1 e)))

end GlobalTheory.ModFam

open GlobalTheory.ModFam in

theorem GlobalTheory.moduli_finite_surjective_over_family : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (l : Level H) (Xo : Moduli D l) (β : RZ H n N →+* KA l), l.A = N → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → N.Coprime l.M → IsInc (RZ H n N).subtype (KA l).val.toRingHom β → FamCore D sM tM lev → ∃ (a : Xo.X ⟶ MM) (ν : SABMap Xo.univ.t tM a) (h : a ≫ sM = Xo.s ≫ spMap β), (∀ x, (Xo.univ.etaA x).left ≫ ν.φ = a ≫ (lev x).left) ∧ IsFinite (pullback.lift a _ h) ∧ Surjective (pullback.lift a _ h) := by
  intro _ _ E _ _ _ H D n N MM sM tM lev l Xo β hA hn _ ⟨j, _, hj⟩ hc hβ F
  subst hA
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨hred, -, hnoe⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm
  have hfl : Flat (spMap β) := by
    obtain ⟨-, -, hfr⟩ := (GlobalTheory.BaseRing.isDedFrac_RZ E H l n j hn.pos hj.dvd).2.2 β hβ
    letI := β.toAlgebra
    exact Flat.SpecMap_iff.2 (IsLocalization.flat (KA l) (nonZeroDivisors (RZ H n l.A)))
  obtain ⟨a, ⟨h, ν, hν⟩, -⟩ := F.rep Xo.X (Xo.s ≫ spMap β) Xo.univ.t Xo.univ.etaA hred hnoe inferInstance
    (fullObj_of_obj Xo.s Xo.univ β hβ)
  refine ⟨a, ν, h, hν, ?_, ⟨fun y => ?_⟩⟩
  · obtain ⟨tY, ⟨m⟩⟩ := exists_sabPull (pullback.fst sM (spMap β)) tM
    have oY : FullObj D (pullback.snd sM (spMap β) ≫ spMap β) tY _ :=
      (pullback.condition (f := sM) (g := spMap β)) ▸ fullObj_pull F.obj m
    obtain ⟨q, hq⟩ := exists_cancel (pullback.lift_fst a _ h) m ν
    have : IsSeparated sM := by
      obtain ⟨N, i, hi, -, rfl⟩ := F.qproj
      have : IsSeparated (PSpace.str (RZ H n l.A) N) := by
        unfold PSpace.str
        infer_instance
      infer_instance
    refine isFinite_of_full hc hβ Xo oY _ (pullback.lift_snd _ _ _) q fun x => sec_cancel m q _ _ ?_
    rw [← hq, hν]
    exact ((congrArg (_ ≫ ·) (GlobalTheory.ObjPull.secPull_left m.cart _)).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (pullback.lift_fst _ _ _)))).symm
  · obtain ⟨k, _, _, z, hz⟩ := GlobalTheory.FinEt.exists_algClosed_point _ y
    have : CharZero k :=
      (RingHom.charZero_iff (Spec.preimage (z ≫ pullback.snd sM (spMap β))).hom.injective).1 inferInstance
    obtain ⟨t, ⟨m⟩⟩ := exists_sabPull (z ≫ pullback.fst sM (spMap β)) tM
    have e : (z ≫ pullback.fst sM (spMap β)) ≫ sM = (z ≫ pullback.snd sM (spMap β)) ≫ spMap β := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have o : FullObj D ((z ≫ pullback.snd sM (spMap β)) ≫ spMap β) t _ := e ▸ fullObj_pull F.obj m
    obtain ⟨χ, hχ⟩ := exists_isLev o l
    obtain ⟨f, ⟨hf, ⟨p⟩⟩, -⟩ := Xo.rep (Sp k) _ inferInstance (objOfFull hc hβ o hχ)
    obtain ⟨r, hr⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν p.toSABMap
    have e₁ : f ≫ a = z ≫ pullback.fst sM (spMap β) :=
      (F.rep (Sp k) _ t _ inferInstance inferInstance inferInstance o).unique
        ⟨by rw [Category.assoc, h, ← Category.assoc, hf], r, fun x => by
          refine (congrArg _ hr).trans (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (p.etaA x))).trans ?_)
          rw [Category.assoc, Category.assoc]
          exact congrArg _ (hν x)⟩
        ⟨e, m, fun x => GlobalTheory.ObjPull.secPull_left m.cart _⟩
    have e₂ : f ≫ pullback.lift a _ h = z := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, e₁]
      · rw [Category.assoc, pullback.lift_snd, hf]
    obtain ⟨u, hu⟩ : y ∈ Set.range z := by rw [hz]; rfl
    exact ⟨f u, by rw [← Scheme.Hom.comp_apply, e₂, hu]⟩
