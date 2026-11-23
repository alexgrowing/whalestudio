import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfValR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.AbConst

open GlobalTheory.KS.GlueDer

theorem valR_appLE {S : Type} [CommRing S] {Z X : Scheme.{0}} (g : Sp S ⟶ Z) (m : Z ⟶ X) (U : X.Opens) (W : Z.Opens)
    (h : W ≤ m ⁻¹ᵁ U) (hg : ⊤ ≤ g ⁻¹ᵁ W) (f : Γ(X, U)) : valR g W ((m.appLE U W h).hom f) = valR (g ≫ m) U f := by
  rw [WtAlg.valR_eq' _ _ hg, WtAlg.valR_eq' (g ≫ m) U (fun p hp => h (hg hp)),
    ← Scheme.Hom.appLE_comp_appLE g m U W ⊤ h hg]
  rfl

theorem isField_one {Z : Scheme.{0}} {W O : Z.Opens} {d : Fld Z} (hd : IsField W d) (hO : O ≤ W) : d O 1 = 0 := by
  simpa using InteriorKS.isField_intCast hd hO 1

theorem lift_agree {R : Type} [CommRing R] {G : Over (Sp R)} {n : ℕ} {X : Scheme.{0}} {m : G.left ⟶ X} {L : LB X}
    {dd : Fin n → Fld G.left} {D : R → R} (h : Heat G m L dd D) (hdd : ∀ a, IsField ⊤ (dd a)) (i i' : h.J)
    (O : G.left.Opens) (hO : O ≤ h.W i ⊓ h.W i') {A : Type} [CommRing A] (π : Γ(G.left, O) →+* A) (h2 : IsUnit (2 : A))
    (hΘ : ∀ a b, π (constFn G.hom O (h.Θ a b)) = 0) (f : Γ(G.left, O)) : π (h.d i O f) = π (h.d i' O f) := by
  have hi : O ≤ h.W i := hO.trans inf_le_left
  have hi' : O ≤ h.W i' := hO.trans inf_le_right
  have hle : O ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i')) := fun p hp => ⟨h.le i (hi hp), h.le i' (hi' hp)⟩
  have hg : IsUnit (pbT m (L.g (h.j i) (h.j i')).val O) := by
    rw [pbT, dif_pos hle]
    exact (Units.isUnit _).map _
  have e₁ := congrArg π (h.glue 1 i i' O hO f)
  have e₀ := congrArg π (h.glue 1 i i' O hO 1)
  generalize pbT m (L.g (h.j i) (h.j i')).val O = g at hg e₁ e₀
  have hs : ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O (g * f)) =
      π g * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O f) + π f * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O g) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.1 O le_top, map_add, map_mul, map_mul]
    ring
  simp only [op, pow_one, _root_.mul_one, Nat.cast_one, one_pow, map_add, map_sub, map_mul, map_sum, hΘ, zero_mul,
    Finset.sum_const_zero, sub_zero, map_ofNat, isField_one (hdd _) le_top, isField_one (h.lift i').1 hi', map_zero,
    mul_zero, map_one] at e₁ e₀
  rw [hs, (h.lift i).1.2.1 O hi, map_add, map_mul, map_mul] at e₁
  refine (h2.mul (hg.map π)).mul_left_cancel ?_
  linear_combination e₁ - π f * e₀

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem surjective_q : Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_surj
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  exact ⟨inferInstance, inferInstance⟩

theorem exists_ratio {T : Over (Sp R)} (x x' : T ⟶ Y.H) (hq : x' ≫ Y.q = x ≫ Y.q) :
    ∃ u : Q.X → Γ(T.left, ⊤)ˣ, ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ x).s χ) (𝟙 _) y J := by
  have := Y.q_linear.isMonHom
  have w : (x⁻¹ * x') ≫ Y.q = toUnit T ≫ η[Q.P.A] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq, inv_mul_cancel]
    rfl
  let t := Y.isKernel.lift _ _ w
  have ht : x * (t ≫ Y.i) = x' := by
    rw [Y.isKernel.lift_fst, mul_inv_cancel_left]
  let u : Multiplicative Q.X →* Γ(T.left, ⊤) :=
    { toFun := fun χ => (Rosenlicht.coord t).hom (AddMonoidAlgebra.single χ.toAdd 1)
      map_one' := Diag.coord_single_zero t
      map_mul' := fun a b => Diag.coord_single_add t _ _ }
  refine ⟨fun χ => u.toHomUnits (Multiplicative.ofAdd χ), fun χ y J hJ => ?_⟩
  have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x (t ≫ Y.i))).2 χ y J hJ
  have C : IsCub (DVR.th Q (T := T) y J) := isCub_cubV Q.cub hJ
  rw [(Y.Φ_i t).1, C.face₃, _root_.mul_one, ht] at h1
  refine h1.trans ((_root_.mul_comm _ _).trans (congrArg (· * _) (Units.ext ?_)))
  exact ((Y.Φ_i t).2 χ y J hJ).trans (gs_unit (𝟙 _) y ⊤ trivial (u.toHomUnits (Multiplicative.ofAdd χ)))

theorem valR_eq_of_isWt {V : Y.H.left.Opens} {f : Γ(Y.H.left, V)} (hf : IsWt Y 0 V f) {S : Type} [CommRing S]
    (a a' : Sp S ⟶ Y.H.left) (h : ⊤ ≤ a ⁻¹ᵁ V) (h' : ⊤ ≤ a' ⁻¹ᵁ V) (e : a' ≫ Y.q.left = a ≫ Y.q.left) :
    valR a' V f = valR a V f := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+* S, spMap φ = a ≫ Y.H.hom := ⟨(Spec.preimage (a ≫ Y.H.hom)).hom, Spec.map_preimage _⟩
  let x : Over.mk (spMap φ) ⟶ Y.H := Over.homMk a hφ.symm
  let x' : Over.mk (spMap φ) ⟶ Y.H := Over.homMk a' (by
    show a' ≫ Y.H.hom = spMap φ
    rw [hφ, ← Over.w Y.q, reassoc_of% e])
  have hq : x' ≫ Y.q = x ≫ Y.q := Over.OverMorphism.ext e
  obtain ⟨u, hu⟩ := exists_ratio Y x x' hq
  let c : Q.X → Sˣ := fun χ => Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom (u χ)
  have hc : ∀ χ, unitOn (c χ) = u χ := fun χ =>
    Units.ext (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of S)) _)
  have hc' : ∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J =
      gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J := fun χ y J hJ => by
    rw [hc]; exact hu χ y J hJ
  rw [hf S φ x x' c a a' rfl rfl h h' hq hc', WtAlg.c_zero x x' c hc', Units.val_one, _root_.one_mul]

theorem exists_app_eq {V : Q.P.A.left.Opens} {f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)} (hf : IsWt Y 0 _ f) :
    ∃ a, (Y.q.left.app V).hom a = f := by
  have := Y.smooth_q
  have := (surjective_q Y).1
  have := (surjective_q Y).2
  refine FunDescent.exists_app_eq Y.q.left V f fun Z g₁ g₂ h₁ h₂ e => ?_
  rw [← sub_eq_zero]
  refine InteriorKS.app_eq_zero_of_valR (𝟙 Z) ⊤ _ fun Ω _ => ?_
  have key : ∀ (g : Z ⟶ Y.H.left) (h : ⊤ ≤ g ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)),
      valR (chart Ω ≫ 𝟙 Z) ⊤ ((g.appLE _ ⊤ h).hom f) = valR (chart Ω ≫ g) _ f := fun g h => by
    rw [Category.comp_id, valR_appLE _ _ _ _ _ le_top]
  refine (WtAlg.valR_sub' (chart Ω ≫ 𝟙 Z) ⊤ le_top _ _).trans ?_
  rw [key, key, sub_eq_zero]
  exact valR_eq_of_isWt Y hf _ _ (fun p _ => h₂ (Set.mem_univ (chart Ω p))) (fun p _ => h₁ (Set.mem_univ (chart Ω p)))
    (by rw [Category.assoc, Category.assoc, e])

theorem isWt_app (V : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V)) : IsWt Y 0 _ ((Y.q.left.app V).hom f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  have key : ∀ (g : Sp S ⟶ Y.H.left) (h : ⊤ ≤ g ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)),
      valR g _ ((Y.q.left.app V).hom f) = valR (g ≫ Y.q.left) V f := fun g h => by
    rw [Scheme.Hom.app_eq_appLE, valR_appLE _ _ _ _ _ h]
  rw [key _ hV, key _ hV', WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul]
  exact congrArg (fun z => valR z V f) (congrArg (·.left) hq)

theorem exists_desc (V : Q.P.A.left.Opens) (d : Fld Y.H.left) (D : R → R) (hd : IsLift Y.H D (Y.q.left ⁻¹ᵁ V) d)
    (hw : ∀ V' : Q.P.A.left.Opens, V' ≤ V → ∀ f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V') f → IsWt Y 0 (Y.q.left ⁻¹ᵁ V') (d _ f)) :
    ∃ e : Fld Q.P.A.left, IsLift Q.P.A D V e ∧
      ∀ V', V' ≤ V → ∀ f, (Y.q.left.app V').hom (e V' f) = d _ ((Y.q.left.app V').hom f) := by
  have := Y.smooth_q
  have := (surjective_q Y).1
  have ex : ∀ (V' : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, V')), ∃ a, V' ≤ V →
      (Y.q.left.app V').hom a = d _ ((Y.q.left.app V').hom f) := fun V' f => by
    by_cases hV : V' ≤ V
    · exact (exists_app_eq Y (hw V' hV _ (isWt_app Y V' f))).imp fun a ha _ => ha
    · exact ⟨0, fun h => absurd h hV⟩
  choose e he using ex
  have inj := FunDescent.app_injective Y.q.left
  have hc : ∀ (V' : Q.P.A.left.Opens) r, (Y.q.left.app V').hom (constFn Q.P.A.hom V' r) = constFn Y.H.hom _ r :=
    fun V' r => app_const (RingHom.id R) Q.P.A.hom Y.H.hom Y.q.left
      ((Over.w Y.q).trans ((Category.comp_id _).symm.trans (congrArg (Y.H.hom ≫ ·) (Spec.map_id _).symm))) V' r
  refine ⟨e, ⟨⟨fun W hW f f' => inj W ?_, fun W hW f f' => inj W ?_, fun W W' h hW f => inj W' ?_⟩,
    fun W hW r => inj W ?_⟩, fun V' hV f => he V' f hV⟩
  · rw [map_add, he _ _ hW, he _ _ hW, he _ _ hW, map_add, hd.1.1 _ (pre_mono _ hW)]
  · rw [map_add, map_mul, map_mul, he _ _ hW, he _ _ hW, he _ _ hW, map_mul, hd.1.2.1 _ (pre_mono _ hW)]
  · rw [he _ _ (h.trans hW), ← res_app _ h (pre_mono _ h), ← res_app _ h (pre_mono _ h), he _ _ hW,
      hd.1.2.2 _ _ _ (pre_mono _ hW)]
  · rw [he _ _ hW, hc, hc, hd.2 _ (pre_mono _ hW)]

variable {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem exists_locDerK (hdd : ∀ a, IsField ⊤ (dd a)) (hB : IsBasic Y h) {K : Type} [Field K] [CharZero K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) : ∃ d, KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) ⊤ d := by
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  choose V hV using fun i => (hB i).1
  choose e he hq using fun i => exists_desc Y (V i) (h.d i) D (hV i ▸ h.lift i)
    fun V' hV' => (hB i).2.2.2 0 V' ((pre_mono _ hV').trans (hV i).ge)
  refine (InteriorKS.glue_along p Q.P.A.hom m _ V (fun y => ?_) (fun i W f => (m.app W).hom (e i W f))
    (fun i => ?_) fun i i' W hW f => ?_).imp fun _ hd => hd.1
  · obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact ⟨i, hx ▸ hi⟩
  · refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(he i).1.1 W hW, map_add]
    · rw [(he i).1.2.1 W hW, map_add, map_mul, map_mul]
    · rw [(he i).1.2.2 W W' h' hW, rsT_eq (pre_mono m h'), res_app m h']
    · rw [(he i).2 W hW, app_const φ _ p m hm]
  · let a := pullback.fst Y.q.left m
    let b := pullback.snd Y.q.left m
    have w : a ≫ Y.q.left = b ≫ m := pullback.condition
    have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
    let π := (a.appLE _ _ hle).hom
    have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
      have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
          (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
        rintro _ rfl hc
        rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
        rfl
      rw [k _ w hle]
      exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
    have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
      rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
        rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
      rfl
    refine FunDescent.app_injective b _ ?_
    show (b.app _).hom ((m.app W).hom _) = (b.app _).hom ((m.app W).hom _)
    rw [key, key, hq i W (hW.trans inf_le_left), hq i' W (hW.trans inf_le_right)]
    refine lift_agree h hdd i i' _ (le_inf ((pre_mono _ (hW.trans inf_le_left)).trans (hV i).ge)
      ((pre_mono _ (hW.trans inf_le_right)).trans (hV i').ge)) π ?_ (fun a b => ?_) _
    · have := (two_ne_zero (α := K)).isUnit.map ((((b ≫ p).appLE ⊤ (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (fun _ _ => trivial)).hom).comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      rwa [map_ofNat] at this
    · rw [hc, hΘ, constFn, map_zero, map_zero]

theorem exists_const (hdd : ∀ a, IsField ⊤ (dd a)) (hB : IsBasic Y h) {K : Type} [Field K] [CharZero K]
    (ρ : R →+* DualNumber K) (hρ : ∀ r, (ρ r).snd = (ρ (D r)).fst) (hΘ : ∀ a b, (ρ (h.Θ a b)).fst = 0) :
    ∃ (B' : Over (Sp (DualNumber K))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left),
      IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp K),
        x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → x ≫ π₁ = x ≫ π₂ := by
  obtain ⟨B', _, ψ, hψ⟩ := FlagTan.exists_isGrpPullback Q.P.A (spMap ρ)
  obtain ⟨B₀, _, j, hj⟩ : ∃ (B₀ : Over (Sp K)) (_ : GrpObj B₀) (j : B₀.left ⟶ B'.left),
      IsGrpPullback B₀ B' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j :=
    ⟨_, _, _, isGrpPullback_pullback _ _⟩
  have h' := PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb hψ
  have h₀ := PolPull.isAbelianScheme_of_isGrpPullback h' hj
  let φ : R →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom.comp ρ
  have hφ : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap ρ = spMap φ := (Spec.map_comp _ _).symm
  obtain ⟨d, hd⟩ := exists_locDerK Y h hdd hB φ hΘ B₀.hom (j ≫ ψ) (by rw [← hφ]; exact (hj.comp hψ).1.w)
  obtain ⟨σ, hσ, -, hjσ⟩ := KS.exists_isConstK_of_locDerK GlobalTheory.abelianSchemeLaws_all.1 K B₀ R ρ Q.P.A B' ψ j d h₀ h' hψ hj
    (by rw [funext hρ]; exact hd)
  refine ⟨B', inferInstance, ψ, σ ≫ j ≫ ψ, hψ, (hσ.comp (hj.comp hψ)).congr ?_ rfl, fun Z x y hx => ?_⟩
  · rw [hφ]
    exact (Spec.map_comp _ _).symm
  · rw [← hj.1.lift_fst x y hx, Category.assoc, Category.assoc, reassoc_of% hjσ]

end Ray

theorem abelian_part_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _
  letI := H.starRing
  intro Y n' v' dd hdd D q _ h hB _ hΘ ρ hρ
  refine exists_const Y h (fun a => (hdd a).1) hB ρ (fun r => by simp [hρ]) fun a b => ?_
  have h0 : MvPowerSeries.constantCoeff (h.Θ a b) = 0 := by
    by_contra hne
    exact hΘ a b (MvPowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne))
  simp [hρ, h0]

end GlobalTheory.Heat.AbConst
