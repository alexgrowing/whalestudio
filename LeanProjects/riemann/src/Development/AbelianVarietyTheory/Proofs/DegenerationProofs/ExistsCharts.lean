import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTateIsoZetaEq

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ThetaCharts
open GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}

theorem exists_full_over (t : SAB H S) {B L : Type} [Field B] [CharZero B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (s : S ⟶ Sp B) {N : ℕ} (hN : 0 < N) {ξ : Lˣ} (hξ : ξ ^ N = 1)
    {Z : Over S} {et : D.La → (Z ⟶ t.G)} (R : RepTors t.G N D.La Z et)
    (hW : ∀ (T : Over S) (x y : T ⟶ t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
      c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs t.G t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c)) :
    ∃ (W : Over S) (α : D.La → (W ⟶ t.G)) (g : W.left ⟶ Sp L), IsFinite W.hom ∧
      g ≫ spMap (algebraMap B L) = W.hom ≫ s ∧ (∀ a c, α (a + c) = α a * α c) ∧
      (∀ a, α a ^ N = 1) ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (β' : L →+* k), x ≫ s = spMap (β'.comp (algebraMap B L)) →
        ∀ α' : D.La → (Over.mk x ⟶ t.G), (∀ a c, α' (a + c) = α' a * α' c) → (∀ a, α' a ^ N = 1) →
          ((∃ w : Over.mk x ⟶ W, w.left ≫ g = spMap β' ∧ ∀ a, w ≫ α a = α' a) ↔
            (∀ (c : 𝓞 E) a, α' (c • a) = α' a ≫ t.act.act c) ∧
            ∀ a b, Out.WeilIs t.G t.PP.L N (α' a) (α' b) (unitOn (Units.map β'.toMonoidHom ξ ^ D.EF a b))) := by
  obtain ⟨hfree, hfin⟩ := datum_free D
  have hLf : IsFinite (spMap (algebraMap B L)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hLe : Etale (spMap (algebraMap B L)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isSeparable B L
    have : Algebra.FinitePresentation B L := Algebra.FinitePresentation.of_finiteType.1 inferInstance
    exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  let C : Over S := Over.mk (pullback.fst s (spMap (algebraMap B L)))
  have hC1 : IsFinite C.hom := inferInstanceAs (IsFinite (pullback.fst s (spMap (algebraMap B L))))
  have hC2 : Etale C.hom := inferInstanceAs (Etale (pullback.fst s (spMap (algebraMap B L))))
  have := R.1
  have := R.2.1
  obtain ⟨hY1, hY2⟩ := finiteEtale_tensor Z C
  let g : (Z ⊗ C).left ⟶ Sp L := (snd Z C).left ≫ pullback.snd s (spMap (algebraMap B L))
  have hg : g ≫ spMap (algebraMap B L) = (Z ⊗ C).hom ≫ s := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ s) (Over.w (snd Z C))
  let y : D.La → (Z ⊗ C ⟶ t.G) := fun a => fst Z C ≫ et a
  have yadd : ∀ a c, y (a + c) = y a * y c := fun a c => by simp only [y, R.2.2.1, MonObj.comp_mul]
  have ypow : ∀ a, y a ^ N = 1 := fun a => by simp only [y]; rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one]
  have ymod : ∀ a c, y (a + N • c) = y a := fun a c => by rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap B L).injective
  have hu : IsUnit (N : Γ((Z ⊗ C).left, ⊤)) := by
    have := (IsUnit.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')).map (fnOn g)
    rwa [map_natCast] at this
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod D.La hN
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod (𝓞 E) hN
  have c1 : ClopenCond (Z ⊗ C) fun _ h => ∀ (c : 𝓞 E) a, h ≫ y (c • a) = h ≫ y a ≫ t.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := t.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ t.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := t.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, t.act.add, MonObj.comp_mul, act_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond (Z ⊗ C) fun _ h => ∀ p : D.La × D.La, Out.WeilIs t.G t.PP.L N (h ≫ y p.1) (h ≫ y p.2)
      (Units.map (h.left.appTop).hom.toMonoidHom (Units.map (fnOn g).toMonoidHom (ξ ^ D.EF p.1 p.2))) := by
    refine ClopenCond.forall_of_finite (Prod.map q q) (fun p => hW _ _ _ _ hu (ypow _) (ypow _) ?_)
      fun p p' e T' h Hc => ?_
    · rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow, map_one]
    · obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := p'
      obtain ⟨c, rfl⟩ := hq a a' (congrArg Prod.fst e)
      obtain ⟨d, rfl⟩ := hq b b' (congrArg Prod.snd e)
      have : ξ ^ D.EF (a + N • c) (b + N • d) = ξ ^ D.EF a b := by
        have : D.EF (a + N • c) (b + N • d) = D.EF a b + N * (D.EF a d + D.EF c (b + N • d)) := by
          simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
          ring
        rw [this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, _root_.mul_one]
      dsimp only at Hc ⊢
      rwa [ymod, ymod, this]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, -, Hi⟩ := exists_sub U hU
  refine ⟨W, fun a => i ≫ y a, i.left ≫ g, hW1, ?_, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, ypow, MonObj.comp_one], fun k _ x β' hx α' hadd hpow => ⟨?_, ?_⟩⟩
  · rw [Category.assoc, hg, ← Category.assoc]
    exact congrArg (· ≫ s) (Over.w i)
  · rintro ⟨w, hβ₀, hw⟩
    obtain ⟨h1, h2⟩ := (HU _ (w ≫ i)).2 ((Hi _ _).2 ⟨w, rfl⟩)
    have hβ' : (w ≫ i).left ≫ g = spMap β' := (Category.assoc _ _ _).trans hβ₀
    refine ⟨fun c a => ?_, fun a b => ?_⟩
    · rw [← hw, ← hw, ← Category.assoc, h1]
      simp only [Category.assoc]
    · have := h2 (a, b)
      rw [map_fnOn g _ β' hβ', map_zpow, Category.assoc, Category.assoc, hw, hw] at this
      exact this
  · rintro ⟨h1, h2⟩
    obtain ⟨z, hz, -⟩ := R.2.2.2.2 _ α' hadd hpow
    let c : Over.mk x ⟶ C := Over.homMk (pullback.lift x (spMap β') (by rw [hx, spMap_comp'']))
      (pullback.lift_fst _ _ _)
    have hy : ∀ a, lift z c ≫ y a = α' a := fun a => by simp only [y]; rw [lift_fst_assoc, hz]
    have hg' : (lift z c).left ≫ g = spMap β' := by
      simp only [g]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact pullback.lift_snd _ _ _
    obtain ⟨w, hw⟩ := (Hi _ (lift z c)).1 ((HU _ _).1 ⟨fun c a => by rw [hy, ← Category.assoc, hy, h1], fun p => by
      rw [map_fnOn g _ β' hg', map_zpow, hy, hy]
      exact h2 _ _⟩)
    exact ⟨w, by rw [← Category.assoc, ← Over.comp_left, hw, hg'], fun a => by rw [← Category.assoc, hw, hy]⟩

open ThetaPtExist GlobalTheory.ZM GlobalTheory.ThetaLocal in

theorem exists_affine_theta (hG : GlobalFnsSt) (hB : SecBaseChangeAnySt) (P : PolAV S) (k : ℕ)
    (hk : Odd k) {T : Over S} (hu : IsUnit (k : Γ(T.left, ⊤))) {I : Type} [Finite I] (y : I → (T ⟶ P.A))
    (hy : ∀ i, y i ^ (k ^ 2) = 1) (p : T.left) :
    ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ T.left) (x' : Sp R ⟶ S) (e : x ≫ T.hom = x'),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧
      ∃ v, IsThetaPt P k (T := Over.mk x') (fun a => (Over.homMk x e : Over.mk x' ⟶ T) ≫ y a) v := by
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 S P k
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V₀, hV₀, b, hb⟩ := hB S P 1 le_rfl (T.hom p)
  choose V hV θ hθ using fun i => (sym S P (k ^ 2) hk.pow T (y i) (hy i)).1 p
  let O : T.left.Opens := T.hom ⁻¹ᵁ V₀ ⊓ ⟨⋂ i, (V i).carrier, isOpen_iInter_of_finite fun i => (V i).2⟩
  have hO : p ∈ O := ⟨hV₀, Set.mem_iInter.2 hV⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWO⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open hO O.2
  have hW' : IsAffineOpen W := hW
  let x₀ : Sp Γ(T.left, W) ⟶ T.left := hW'.fromSpec
  have hx₀ : Set.range x₀ = W := hW'.range_fromSpec
  have hl : ∀ U : T.left.Opens, O ≤ U → ∃ t : Sp Γ(T.left, W) ⟶ U.toScheme, t ≫ U.ι = x₀ := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι x₀ (by
      rw [hx₀, Scheme.Opens.range_ι]; exact hWO.trans hU), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨t, ht⟩ : ∃ t : Sp Γ(T.left, W) ⟶ V₀.toScheme, t ≫ V₀.ι = x₀ ≫ T.hom :=
    ⟨IsOpenImmersion.lift V₀.ι (x₀ ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact (hWO (hx₀.le ⟨z, rfl⟩)).1), IsOpenImmersion.lift_fac _ _ _⟩
  have ex : t ≫ (overRes (T := baseOver S) V₀).hom = x₀ ≫ T.hom := (congrArg (t ≫ ·) (Category.comp_id _)).trans ht
  refine ⟨Γ(T.left, W), inferInstance, x₀, t ≫ (overRes (T := baseOver S) V₀).hom, ex.symm,
    inferInstanceAs (IsOpenImmersion hW'.fromSpec), by rw [hx₀]; exact hpW, ?_⟩
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th, hth⟩ := exists_generator _ hsp
  refine exists_isThetaPt P k hk α₀ hα₀ (T := baseAt t) ?_ _ th hth fun i => ?_
  · simpa using hu.map x₀.appTop.hom
  · obtain ⟨u, hu'⟩ := hl (V i) (inf_le_right.trans fun q hq => Set.mem_iInter.1 hq i)
    let r : baseAt t ⟶ overRes (T := T) (V i) := Over.homMk u
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ T.hom) hu')).trans ex.symm)
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB r (hθ i)
    have e : r ≫ overResι (V i) = (Over.homMk x₀ ex.symm : baseAt t ⟶ T) :=
      Over.OverMorphism.ext hu'
    rw [← Category.assoc, e] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩

theorem isThetaPt_comp {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (h : IsThetaPt P k x v) (q : I' → I) : IsThetaPt P k (fun a => x (q a)) (fun a => v (q a)) := by
  refine ⟨h.1, h.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun a => U (q a), fun a => s2 (q a), fun a => w (q a), u, h1, h2, h3, h4,
    fun a => h5 _, fun a => h6 _, fun a => h7 _, fun a => h8 _⟩

theorem exists_tateIso_of_level {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} {N : ℕ} (he : ∀ x y c c', e N x y c → e N x y c' → c = c')
    (I : TateIso D k Q act e) (hN : 0 < N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N) (α : D.La → Q)
    (hadd : ∀ a c, α (a + c) = α a * α c) (hpow : ∀ a, α a ^ N = 1) (hlin : ∀ c a, α (c • a) = act c (α a))
    (hiso : ∀ a b, e N (α a) (α b) (ξ ^ D.EF a b)) (l : Geo.Tor.Level H) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ ∀ a, I'.ev N a = α a := by
  by_cases hpq : 1 ≤ D.p + D.q
  · exact exists_of_level (GlobalTheory.SimAlg.sim_group E H D hpq).1 N (GlobalTheory.exists_sim_lift E H D N) he I hN hξ α hadd hpow
      hlin hiso
  · have := D.fin
    have := D.proj
    have : Subsingleton D.La := Module.finrank_zero_iff.1 (D.rank.trans (by norm_cast; omega))
    obtain ⟨I', hI'⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l k Q act e I N ξ hN (IsPrimitiveRoot.coe_units_iff.2 hξ)
    refine ⟨I', Units.ext hI', fun a => ?_⟩
    rw [Subsingleton.elim a 0, add_map_zero (I'.add N), add_map_zero hadd]

def IsFibre (t : SAB H S) {K : Type} [Field K] (y : Sp K ⟶ S) (o : Full D K) (φ : o.P.A.left ⟶ t.G.left) : Prop :=
  letI := H.starRing
  IsGrpPullback o.P.A t.G y φ ∧ LBIso o.P.L (t.PP.L.pull φ) ∧ ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (t.act.act x).left

theorem fnOf_map {R K : Type} [CommRing R] [Field K] (f : R →+* K) (v : Γ(Sp R, ⊤)) :
    (spMap f).appTop.hom v = fnOf (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom v)) := by
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom v)) h2
  refine Eq.trans ?_ h3.symm
  exact congrArg (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply v).symm

variable {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {s₀ : S ⟶ Sp B}

theorem theta_of_chart (hB : SecBaseChangeAnySt) (o₀ : Obj D l b s₀) {m : ℕ} (hm : Odd m) {R : Type} [CommRing R]
    {x' : Sp R ⟶ S} {z : D.La → (Over.mk x' ⟶ o₀.t.G)} {v : D.La → Γ(Sp R, ⊤)}
    (hv : IsThetaPt (objPolAV o₀) m (T := Over.mk x') z v) {K : Type} [Field K] {y : Sp K ⟶ S} {o : Full D K}
    {φ : o.P.A.left ⟶ o₀.t.G.left} (h : IsFibre o₀.t y o φ) (f : R →+* K) (hf : spMap f ≫ x' = y)
    (hz : ∀ a, spMap f ≫ (z a).left = (o.I.ev (m ^ 2) a).left ≫ φ) :
    o.Theta m fun a => f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v a)) := by
  let j : Over.mk ((baseOver (Sp K)).hom ≫ y) ⟶ Over.mk x' := Over.homMk (spMap f) (hf.trans (Category.id_comp _).symm)
  haveI : IsAffine (Over.mk ((baseOver (Sp K)).hom ≫ y)).left := inferInstanceAs (IsAffine (Sp K))
  haveI : IsAffine (Over.mk x').left := inferInstanceAs (IsAffine (Sp R))
  have Q := GlobalTheory.ThetaBaseChange.isThetaPt_pull (objPolAV o₀) hB j hv
  have Q' := (GlobalTheory.ThetaPtUp.isThetaPt_iff (P₀ := objPolAV o₀) (P := o.P) (T := baseOver (Sp K)) h.1 h.2.1
    (x := o.I.ev (m ^ 2)) (fun a => hz a) (fun a => (o.I.onto _ (pow_pos hm.pos 2) _).2 ⟨a, rfl⟩) _).2 Q
  unfold Full.Theta
  convert Q' using 2 with a
  exact (fnOf_map f (v a)).symm

theorem exists_charts (hL : Laws) (hL2 : Laws2) (o₀ : Obj D l b s₀) {F L : Type} [Field F] [CharZero F] [Field L]
    [Algebra F L] [FiniteDimensional F L] (s : S ⟶ Sp F) [QuasiCompact s] [LocallyOfFiniteType s] {m : ℕ} (hm : Odd m)
    {ξ : Lˣ} (hξ : IsPrimitiveRoot ξ (m ^ 2)) :
    ∃ (Ix : Type) (_ : Finite Ix) (A : Ix → Type) (_ : ∀ i, CommRing (A i)) (x : ∀ i, Sp (A i) ⟶ S) (gam : ∀ i, L →+* A i)
      (J : Type) (_ : Finite J) (q : D.La → J) (w : ∀ i, J → A i), Function.Surjective q ∧
      (∀ i, ((gam i).comp (algebraMap F L)).FiniteType) ∧ (∀ i, x i ≫ s = spMap ((gam i).comp (algebraMap F L))) ∧
      (∀ (K : Type) [Field K] (y : Sp K ⟶ S) (o : Full D K) (φ : o.P.A.left ⟶ o₀.t.G.left) (β : L →+* K),
        IsFibre o₀.t y o φ → y ≫ s = spMap (β.comp (algebraMap F L)) → (o.I.ζ (m ^ 2) : K) = β ξ →
        ∃ (i : Ix) (f : A i →+* K), f.comp (gam i) = β ∧ o.Theta m fun a => f (w i (q a))) ∧
      ∀ (i : Ix) (K : Type) [Field K] (f : A i →+* K) (o : Full D K) (φ : o.P.A.left ⟶ o₀.t.G.left),
        IsFibre o₀.t (spMap f ≫ x i) o φ → ∃ I', (I'.ζ (m ^ 2) : K) = f (gam i ξ) ∧
          Full.Theta { o with I := I' } m fun a => f (w i (q a)) := by
  letI := H.starRing
  have hN : 0 < m ^ 2 := pow_pos hm.pos 2
  obtain ⟨hfree, hfin⟩ := datum_free D
  have hunit : ∀ (T : Scheme.{0}) (g : T ⟶ Sp F) (n : ℕ), 0 < n → IsUnit (n : Γ(T, ⊤)) := fun T g n hn => by
    have := (IsUnit.mk0 (n : F) (Nat.cast_ne_zero.2 hn.ne')).map (fnOn g)
    rwa [map_natCast] at this
  obtain ⟨Z, et, R⟩ := @GlobalTheory.exists_finiteEtale_latticeTorsionHom S o₀.t.G _ o₀.t.comm (m ^ 2) D.La _ _ _ (objPolAV o₀).isAb
    (hunit S s _ hN)
  obtain ⟨W, α, g, hW, hg, hadd, hpow, HW⟩ := exists_full_over (D := D) o₀.t s hN hξ.pow_eq_one R
    (fun T x y c hu hx hy hc => GlobalTheory.exists_clopen_weilIs_iff hL S (objPolAV o₀) _ T x y c hN hu hx hy hc)
  obtain ⟨κ, _, q₀, hq₀⟩ := exists_finite_mod D.La hN
  let q : D.La → Set.range q₀ := Set.rangeFactorization q₀
  have hq : Function.Surjective q := Set.rangeFactorization_surjective
  let r := Function.surjInv hq
  have hr : ∀ a, α (r (q a)) = α a := fun a => by
    obtain ⟨c, hc⟩ := hq₀ a (r (q a)) (congrArg Subtype.val (Function.surjInv_eq hq (q a))).symm
    rw [hc, hadd, add_map_nsmul hadd, hpow, _root_.mul_one]
  choose A _ x x' e hx hp v hv using fun p : W.left => exists_affine_theta hL.globalFns hL2.secBaseChangeAny
    (objPolAV o₀) m hm (T := W) (hunit _ (W.hom ≫ s) m hm.pos) (fun j => α (r j)) (fun j => hpow _) p
  have hv' : ∀ p, IsThetaPt (objPolAV o₀) m (T := Over.mk (x' p))
      (fun a => (Over.homMk (x p) (e p) : Over.mk (x' p) ⟶ W) ≫ α a) (fun a => v p (q a)) := fun p => by
    have := isThetaPt_comp (hv p) q
    simpa only [hr] using this
  haveI : CompactSpace W.left := by
    have : QuasiCompact (W.hom ≫ s) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (W.hom ≫ s)
  obtain ⟨Ix, hJ₀⟩ := isCompact_univ.elim_finite_subcover (fun p : W.left => Set.range (x p))
    (fun p => (x p).isOpenEmbedding.isOpen_range) (fun p _ => Set.mem_iUnion.2 ⟨p, hp p⟩)
  choose gam hgam using fun p => exists_spMap (x p ≫ g)
  have hs : ∀ p, x' p ≫ s = spMap ((gam p).comp (algebraMap F L)) := fun p => by
    rw [← spMap_comp'', ← hgam, Category.assoc, hg, ← e, Category.assoc]
  have hwe : ∀ (K : Type) [Field K] (y : Sp K ⟶ S) (o : Full D K) (φ : o.P.A.left ⟶ o₀.t.G.left)
      (h : IsFibre o₀.t y o φ) (n : ℤ) (z z' : baseOver (Sp K) ⟶ o.P.A) (c : Kˣ),
      WeilIs o.P.A o.P.L n z z' (unitOn c) ↔ WeilIs o₀.t.G o₀.t.PP.L n (ObjPull.pushEquiv h.1 _ z)
        (ObjPull.pushEquiv h.1 _ z') (unitOn c) := fun K _ y o φ h n z z' c =>
    weilIs_grpPullback_of_comm _ _ o₀.t.G o.P.A y φ o₀.t.PP.L o.P.L o₀.t.PP.isLB o.P.isLB h.1 h.2.1 _ n z z' _ _ _
      rfl rfl
  have hact : ∀ (K : Type) [Field K] (y : Sp K ⟶ S) (o : Full D K) (φ : o.P.A.left ⟶ o₀.t.G.left)
      (h : IsFibre o₀.t y o φ) (c : 𝓞 E) (z : baseOver (Sp K) ⟶ o.P.A),
      ObjPull.pushEquiv h.1 _ (z ≫ o.oa.act c) = ObjPull.pushEquiv h.1 _ z ≫ o₀.t.act.act c :=
    fun K _ y o φ h c z => by
      apply Over.OverMorphism.ext
      show (z.left ≫ _) ≫ _ = (z.left ≫ _) ≫ _
      rw [Category.assoc, h.2.2, Category.assoc]
  refine ⟨Ix, inferInstance, fun i => A i, inferInstance, fun i => x' i, fun i => gam i, Set.range q₀, inferInstance, q,
    fun i j => (Scheme.ΓSpecIso (CommRingCat.of (A i))).hom.hom (v i j), hq, fun i => ?_, fun i => hs i,
    fun K _ y o φ β h hy hζ => ?_, fun i K _ f o φ h => ?_⟩
  · have : LocallyOfFiniteType (spMap ((gam i).comp (algebraMap F L))) := by
      rw [← hs, ← e]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  · have hζ' : o.I.ζ (m ^ 2) = Units.map β.toMonoidHom ξ := Units.ext hζ
    obtain ⟨w, hw, hw'⟩ := (HW K ((baseOver (Sp K)).hom ≫ y) β ((congrArg (· ≫ s) (Category.id_comp y)).trans hy)
      (fun a => ObjPull.pushEquiv h.1 _ (o.I.ev (m ^ 2) a)) (fun a c => by rw [o.I.add, map_mul])
      (fun a => by rw [← map_pow, (o.I.onto _ hN _).2 ⟨a, rfl⟩, map_one])).2
      ⟨fun c a => by rw [o.I.lin, hact K y o φ h], fun a c => by
        rw [← hζ']; exact (hwe K y o φ h _ _ _ _).1 (o.I.isom _ hN a c)⟩
    let pt : Sp K := (⊥ : PrimeSpectrum K)
    obtain ⟨i, hi, hp⟩ := Set.mem_iUnion₂.1 (hJ₀ (Set.mem_univ (w.left pt)))
    haveI := hx i
    have hsub : Set.range w.left ⊆ Set.range (x i) := by
      rintro _ ⟨z, rfl⟩
      rwa [Subsingleton.elim (α := PrimeSpectrum K) z pt]
    obtain ⟨f, hf⟩ := exists_spMap (A := K) (IsOpenImmersion.lift (x i) w.left hsub)
    have hf' : spMap f ≫ x i = w.left := by rw [← hf, IsOpenImmersion.lift_fac]
    refine ⟨⟨i, hi⟩, f, spMap_inj' ?_, theta_of_chart hL2.secBaseChangeAny o₀ hm (hv' i) h f ?_ fun a => ?_⟩
    · rw [← spMap_comp'', ← hgam, ← Category.assoc, hf', hw]
    · rw [← e, ← Category.assoc, hf']
      exact (Over.w w).trans (Category.id_comp _)
    · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (α a).left) hf')).trans
        (congrArg CommaMorphism.left (hw' a))
  · let w : Over.mk ((baseOver (Sp K)).hom ≫ spMap f ≫ x' i) ⟶ W := Over.homMk (spMap f ≫ x i) (by
      rw [Category.assoc, e]; exact (Category.id_comp _).symm)
    have a1 : ∀ a c, w ≫ α (a + c) = w ≫ α a * w ≫ α c := fun a c => by rw [hadd, MonObj.comp_mul]
    have p1 : ∀ a, (w ≫ α a) ^ m ^ 2 = 1 := fun a => by rw [← MonObj.comp_pow, hpow, MonObj.comp_one]
    obtain ⟨h1, h2⟩ := (HW K _ (f.comp (gam i)) ((congrArg (· ≫ s) (Category.id_comp _)).trans (by
      rw [Category.assoc, hs, spMap_comp'', RingHom.comp_assoc])) (fun a => w ≫ α a) a1 p1).1
      ⟨w, ((Category.assoc _ _ _).trans (congrArg (spMap f ≫ ·) (hgam i))).trans (spMap_comp'' _ _), fun _ => rfl⟩
    let Φ := ObjPull.pushEquiv h.1 (baseOver (Sp K))
    obtain ⟨I', hI, hI'⟩ := exists_tateIso_of_level
      (fun y y' c c' => weilIs_unique_fieldPoint _ _ _ o.P.isLB K (𝟙 _) (m ^ 2 : ℕ) y y' c c') o.I hN
      (hξ.map_of_injective (f := Units.map (f.comp (gam i)).toMonoidHom) (Units.map_injective (f.comp (gam i)).injective))
      (fun a => Φ.symm (w ≫ α a)) (fun a c => by rw [a1, map_mul]) (fun a => by rw [← map_pow, p1, map_one])
      (fun c a => by
        rw [MulEquiv.symm_apply_eq, hact K _ o φ h, MulEquiv.apply_symm_apply]; exact h1 c a)
      (fun a c => (hwe K _ o φ h _ _ _ _).2 (by
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h2 a c)) l
    refine ⟨I', congrArg Units.val hI, theta_of_chart (o := { o with I := I' }) (φ := φ) hL2.secBaseChangeAny o₀ hm
      (hv' i) h f rfl fun a => ?_⟩
    change _ = (I'.ev (m ^ 2) a).left ≫ φ
    rw [hI', ObjPull.pushEquiv_symm_left]
    exact (Category.assoc _ _ _).symm

end GlobalTheory.ThetaCharts
end
