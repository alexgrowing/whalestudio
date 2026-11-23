import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart.SepBModel

theorem fromBase_id {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) (h : ∀ a b, (τ₀ a b).IsGen) :
    FromBase Q τ₀ (RingHom.id V) := by
  have hs : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  refine ⟨Q.P.A, inferInstance, Q.P.L, cpt Q, τ₀, 𝟙 _, GlobalTheory.PolDeg.Wit.idPull _, Q.P.isAb, Q.P.isLB, ?_,
    GlobalTheory.PolDeg.Wit.idPull_isGen Q.P.isLB, fun a => ?_, h, fun a b z J J₀ hJ hJ₀ => ?_⟩
  · rw [hs]; exact GlobalTheory.PolDeg.Wit.grpPullback_id Q.P.A
  · rw [hs]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [hs]
    refine (gen_trans (h a b) (𝟙 _) z (hJ.mem _ _) (hJ₀.mem _ _)).trans (congrArg (· * _) ?_)
    have e : ∀ q : Sp V ⟶ Q.P.A.left, gm q z _ ((GlobalTheory.PolDeg.Wit.idPull Q.P.L).s (fun _ => J₀ (q ≫ 𝟙 _), J q)) =
        (gm q z _ (Q.P.L.g (J q) (J₀ q)))⁻¹ := fun q => by
      have h0 : q z ∈ Q.P.L.U (J₀ (q ≫ 𝟙 _)) := by rw [Category.comp_id]; exact hJ₀ q
      refine (GlobalTheory.PolDeg.Wit.gw_idPull Q.P.L q z _ _ h0 (hJ q)).trans ?_
      rw [Category.comp_id]
      exact eq_inv_of_mul_eq_one_left ((gm_cocycle Q.P.isLB q z (hJ₀ q) (hJ q) (hJ₀ q)).trans
        (gm_self Q.P.isLB q z (hJ₀ q)))
    rw [e, e, e, e]
    let F : (Sp V ⟶ Q.P.A.left) → ((Sp V).presheaf.stalk z)ˣ := fun q => gm q z _ (Q.P.L.g (J q) (J₀ q))
    show ∏ k : Fin 4, F (𝟙 _ ≫ ![cpt Q (a + b), cpt Q a, cpt Q b, cpt Q 0] k) ^ (![-1, 1, 1, -1] : Fin 4 → ℤ) k =
      (F _)⁻¹ * ((F _)⁻¹)⁻¹ * ((F _)⁻¹)⁻¹ * (F _)⁻¹
    simp only [Category.id_comp, Fin.prod_univ_four]
    simp

theorem gm_field {W : Type} [Field W] {Z : Scheme.{0}} (r : Z ⟶ Sp W) (z : Z) (U : (Sp W).Opens) (h : r z ∈ U)
    (a : Γ(Sp W, U)ˣ) : ∃ x : Wˣ, gm r z U a = gm r z ⊤ (unitOn x) := by
  obtain rfl : U = ⊤ := top_unique fun y _ => by rwa [Subsingleton.elim y (r z)]
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
  exact ((Scheme.ΓSpecIso (CommRingCat.of W)).hom_inv_id_apply a.val).symm

theorem gm_spMap {W V : Type} [CommRing W] [CommRing V] (f : W →+* V) (z : Sp V) (x : Wˣ) :
    gm (spMap f) z ⊤ (unitOn x) = gm (𝟙 (Sp V)) z ⊤ (unitOn (Units.map f.toMonoidHom x)) := by
  have e : unitOn (Units.map f.toMonoidHom x) = pullU (spMap f) ⊤ (unitOn x) := by
    apply Units.ext
    exact congrArg (fun q => q.hom (x : W)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  rw [e]
  exact (gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn x)).symm

theorem gm_unitOn_inj {V : Type} [CommRing V] [IsDomain V] (z : Sp V) {x y : Vˣ}
    (h : gm (𝟙 (Sp V)) z ⊤ (unitOn x) = gm (𝟙 (Sp V)) z ⊤ (unitOn y)) : x = y := by
  have h1 := congrArg Units.val h
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at h1
  have h2 := germ_injective_of_isIntegral (Sp V) (U := ⊤) z trivial h1
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1 h2)

open InhTate in

def tGens (u : ℤ → ℤ → InhTate.Rˣ) : Gens tatePre := fun a b => cg _ _ (unitOn (u a b))

open InhTate in

theorem mem_range_of_fromBase {W : Type} [Field W] (ιb : W →+* InhTate.R) (u : ℤ → ℤ → InhTate.Rˣ)
    (h : FromBase tatePre (tGens u) ιb) (a b : ℤ) : (u a b : InhTate.R) ∈ ιb.range := by
  obtain ⟨B₀, _, M₀, c₀, τ₁, β, w, -, hM, -, -, -, -, hv⟩ := h
  let z : Sp InhTate.R := closedPoint _
  choose J₀ hJ₀ using fun χ : Sp InhTate.R ⟶ B₀.left => exists_chart hM (χ z)
  have hJ : Good tatePre.P.L z (fun _ => PUnit.unit) := fun _ => trivial
  have := hv a b z (fun _ => PUnit.unit) J₀ hJ hJ₀
  obtain ⟨x, hx⟩ := gm_field (spMap ιb) z _ (Good.mem hJ₀ ![c₀ (a + b), c₀ a, c₀ b, c₀ (0 : ℤ)] (spMap ιb))
    ((τ₁ a b).s _)
  have e₁ : val (tGens u a b) (𝟙 _) z (fun _ => PUnit.unit) = gm (𝟙 _) z ⊤ (unitOn (u a b)) :=
    gm_res _ z le_top (hJ.mem _ _) _
  let t := gm (cpt tatePre (0 : ℤ)) z _ (w.s (fun _ => J₀ (cpt tatePre (0 : ℤ) ≫ β), PUnit.unit))
  have e₂ : gm (𝟙 _) z ⊤ (unitOn (u a b)) = t * t⁻¹ * t⁻¹ * t * gm (spMap ιb) z ⊤ (unitOn x) :=
    e₁.symm.trans (this.trans (congrArg _ hx))
  rw [mul_inv_cancel, _root_.one_mul, inv_mul_cancel, _root_.one_mul, gm_spMap] at e₂
  exact ⟨x, (congrArg Units.val (gm_unitOn_inj z e₂)).symm⟩

open InhTate in

theorem fromBase_tate_rat (x : ℤ → ℤ → ℚˣ) :
    FromBase tatePre (tGens fun a b => Units.map (algebraMap ℚ InhTate.R).toMonoidHom (x a b)) (algebraMap ℚ InhTate.R) := by
  refine ⟨(Inh.zeroPolAV (Sp ℚ)).A, inferInstance, Inh.trivLB _, fun _ => 𝟙 _, fun a b => cg _ _ (unitOn (x a b)),
    spMap (algebraMap ℚ InhTate.R), ⟨fun _ => 1⟩, (Inh.zeroPolAV _).isAb, Inh.trivLB_isLB _, ⟨?_, ?_⟩, ?_, fun a => ?_,
    fun a b => cg_isGen _ _ _, fun a b z J J₀ hJ hJ₀ => ?_⟩
  · show IsPullback (spMap (algebraMap ℚ InhTate.R)) (𝟙 _) (𝟙 _) _
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  · intro T p q p₀ q₀ _ _
    have h₀ : (p₀ * q₀).left ≫ 𝟙 _ = T.hom ≫ spMap (algebraMap ℚ InhTate.R) := Over.w (p₀ * q₀)
    have h₁ : (p * q).left ≫ 𝟙 _ = T.hom := Over.w (p * q)
    rw [Category.comp_id] at h₀ h₁
    rw [h₀, h₁]; rfl
  · intro i j
    show res _ 1 = res _ ((LB.LinComb _ _ _).g _ _) * (res _ 1)⁻¹ * res _ 1
    erw [Inh.linComb_triv_g]
    simp only [map_one, inv_one, _root_.mul_one]
    exact (_root_.mul_one _).symm
  · have h₁ : cpt tatePre a ≫ 𝟙 _ = 𝟙 _ := Over.w (tatePre.c a)
    rw [Category.comp_id] at h₁
    rw [h₁]; exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e₁ := gm_res (𝟙 (Sp InhTate.R)) z le_top
      (hJ.mem ![cpt tatePre (a + b), cpt tatePre a, cpt tatePre b, cpt tatePre 0] (𝟙 _))
      (unitOn (Units.map (algebraMap ℚ InhTate.R).toMonoidHom (x a b)))
    have e₂ := gm_res (spMap (algebraMap ℚ InhTate.R)) z le_top
      (hJ₀.mem (fun k : Fin 4 => ![𝟙 (Sp ℚ), 𝟙 _, 𝟙 _, 𝟙 _] k) (spMap (algebraMap ℚ InhTate.R))) (unitOn (x a b))
    refine e₁.trans ((gm_spMap _ z _).symm.trans (e₂.symm.trans ?_))
    simp only [map_one, inv_one, _root_.one_mul]
    rfl

def onePlus : InhTate.Rˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.2 (by simp) : IsUnit (1 + PowerSeries.X : InhTate.R)).unit

open InhTate in

theorem not_fromBase_tate : ¬ FromBase tatePre (tGens fun _ _ => onePlus) (algebraMap ℚ InhTate.R) := fun h => by
  obtain ⟨x, hx⟩ := mem_range_of_fromBase _ _ h 0 0
  have := congrArg (PowerSeries.coeff 1) hx
  simp [onePlus, PowerSeries.coeff_C, PowerSeries.coeff_one] at this

theorem lbIso_two {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : Y ⟶ X) (r : Z ⟶ Y) :
    LBIso (L.pull (r ≫ φ)) ((L.pull φ).pull r) := by
  have h : LBIso L L := by
    refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
    refine (gm_res (𝟙 X) y _ hy _).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res (𝟙 X) y _ hy _))).trans ?_
    have e := (gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2).trans (gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2).symm
    exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul e)
  exact (LBIso.chartPull (Geo.Tor.chartPullPull L φ φ rfl) (Geo.Tor.chartPullPull L φ φ rfl) h).chartPull
    (chartPullSame L (fun _ => r ≫ φ) (fun _ => φ) _ r fun _ => rfl) (Geo.Tor.chartPullPull (L.pull φ) r r rfl)

theorem sepAtB_iff_of_range {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) {m N : ℕ}
    (s : Fin m ⊕ Fin N → V) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) (h : ∀ v, ev v ∈ k₀) :
    SepAtB Q τ₀ s ev k₀ ↔ ∀ i, ev (s (.inl i)) = 0 := by
  refine ⟨fun H => H.1, fun H => ⟨H, ?_, fun _ _ _ _ _ _ => h _⟩⟩
  let g : Sp k₀ ⟶ Sp V := spMap (ev.codRestrict k₀ h)
  let i : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  have hg : i ≫ g = spMap ev := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl
  let B₀ := (Over.pullback g).obj Q.P.A
  let B' := (Over.pullback i).obj B₀
  have hA := Q.P.isAb
  have hB : IsAbelianScheme B₀ :=
    { comm := inferInstance
      smooth := by haveI := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by haveI := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by haveI := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  obtain ⟨w, hw⟩ := lbIso_two Q.P.isLB (pullback.fst Q.P.A.hom g) (pullback.fst B₀.hom i)
  have hc : ∀ a, (g ≫ (Q.c a).left) ≫ Q.P.A.hom = 𝟙 _ ≫ g := fun a => by
    rw [Category.assoc, Over.w]; simp
  let c₀ : Q.X → (Sp k₀ ⟶ B₀.left) := fun a => pullback.lift _ _ (hc a)
  have hc' : ∀ a, (i ≫ c₀ a) ≫ B₀.hom = 𝟙 _ ≫ i := fun a => by
    have : c₀ a ≫ B₀.hom = 𝟙 _ := pullback.lift_snd _ _ _
    rw [Category.assoc, this]; simp
  refine ⟨B₀, inferInstance, inferInstance, Q.P.L.pull (pullback.fst Q.P.A.hom g), c₀, B', inferInstance,
    pullback.fst B₀.hom i ≫ pullback.fst Q.P.A.hom g, pullback.fst B₀.hom i, w, fun a => pullback.lift _ _ (hc' a),
    hB, DVR.linComb_isLB _ Q.P.isLB _ _,
    ((isGrpPullback_pullback B₀ i).comp (isGrpPullback_pullback Q.P.A g)).congr hg rfl, isGrpPullback_pullback B₀ i, hw,
    fun a => ⟨pullback.lift_snd _ _ _, ?_, pullback.lift_fst _ _ _⟩⟩
  have e₁ : pullback.lift _ _ (hc' a) ≫ pullback.fst B₀.hom i = i ≫ c₀ a := pullback.lift_fst _ _ _
  have e₂ : c₀ a ≫ pullback.fst Q.P.A.hom g = g ≫ (Q.c a).left := pullback.lift_fst _ _ _
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans ((Category.assoc _ _ _).trans ?_))
  exact (congrArg (i ≫ ·) e₂).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hg))

open InhTate in

theorem sepAtB_tate (τ₀ : Gens tatePre) :
    SepAtB tatePre τ₀ (Sum.elim ![PowerSeries.X] ![onePlus.val]) (PowerSeries.constantCoeff (R := ℚ)) ⊤ ∧
      ¬ SepAtB tatePre τ₀ (Sum.elim ![PowerSeries.X] ![onePlus.val])
        (algebraMap InhTate.R (FractionRing InhTate.R)) ⊤ := by
  refine ⟨(sepAtB_iff_of_range _ _ _ _ ⊤ fun _ => Subfield.mem_top _).2 fun i => by fin_cases i; simp, fun h => ?_⟩
  have := h.1 0
  simp at this

open InhTate in

theorem torus_mem_of_sepAtB_tate (x : ℤ → ℤ → ℚˣ) {m N : ℕ} (s : Fin m ⊕ Fin N → InhTate.R) {K : Type} [Field K] [CharZero K]
    (ev : InhTate.R →+* K) (k₀ : Subfield K)
    (h : SepAtB tatePre (tGens fun a b => Units.map (algebraMap ℚ InhTate.R).toMonoidHom (x a b)) s ev k₀) (i : Fin N) :
    ev (s (.inr i)) ∈ k₀ :=
  h.2.2 ℚ _ (fromBase_tate_rat x) (fun a => by
    rw [← RingHom.comp_apply, eq_ratCast]; exact SubfieldClass.ratCast_mem k₀ a) i

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem sepB_two_of_sep {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {S : Scheme.{0}} {j : Xo.XF c ⟶ S}
    (h : Sep Xo c φ j) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (C : MonoFam Xo c φ V) (hV : GlobalTheory.Mum.Base V)
    (ξ : Sp V ⟶ S) (hξ : C.y ≫ j = jK V ≫ ξ) (τ₀ : Gens C.P.D.toPre) (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K)
    (k₀ : Subfield K) (hk : IsAlgClosed k₀) (hc : ∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) (hd : DefOver k₀ (spMap ev ≫ ξ)) :
    SepAtB C.P.D.toPre τ₀ (N := 0) (Sum.elim C.s ![]) ev k₀ := by
  obtain ⟨h0, B₀, _, _, M₀, c₀, B', _, π₁, π₀, w, c', -, h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := h V C hV ξ hξ K ev k₀ hk hc hd
  exact ⟨h0, ⟨B₀, _, inferInstance, M₀, c₀, B', _, π₁, π₀, w, c', h₁, h₂, h₃, h₄, h₅, h₆⟩, fun _ _ _ _ _ i => i.elim0⟩

theorem uPoinStX_of_uStB (h : UStB) : GlobalTheory.UPoinc.UPoinStX := fun E _ _ _ H Dw hpq φ h₁ h₂ l Xo c => by
  obtain ⟨Z, zs, i, OZ, N, d, J, S, π, j, BD, hP, -⟩ := h E H Dw hpq φ h₁ h₂ l Xo c
  exact ⟨Z, zs, i, OZ, N, d, J, S, π, j, BD, hP⟩

theorem stalkMap_gm {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm f (r z) U a) = gm (r ≫ f) z U a := by
  apply Units.ext
  rw [gm_val (r ≫ f) z U h]
  show (r.stalkMap z).hom (gm f (r z) U a).val = _
  rw [gm_val f (r z) U h]
  exact Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _

open InhTate in

theorem mem_of_fromBase {W : Type} [CommRing W] (ιb : W →+* InhTate.R) (u : ℤ → ℤ → InhTate.Rˣ)
    (h : FromBase tatePre (tGens u) ιb) {K : Type} [Field K] (ev : InhTate.R →+* K) (k₀ : Subfield K)
    (hk : ∀ a, ev (ιb a) ∈ k₀) (a b : ℤ) : ev (u a b) ∈ k₀ := by
  obtain ⟨B₀, _, M₀, c₀, τ₁, β, w, -, hM, -, -, -, -, hv⟩ := h
  let p : Sp K := closedPoint _
  let z : Sp InhTate.R := spMap ev p
  choose J₀ hJ₀ using fun χ : Sp InhTate.R ⟶ B₀.left => exists_chart hM (χ z)
  have hJ : Good tatePre.P.L z (fun _ => PUnit.unit) := fun _ => trivial
  have := hv a b z (fun _ => PUnit.unit) J₀ hJ hJ₀
  have e₁ : val (tGens u a b) (𝟙 _) z (fun _ => PUnit.unit) = gm (𝟙 _) z ⊤ (unitOn (u a b)) :=
    gm_res _ z le_top (hJ.mem _ _) _
  let t := gm (cpt tatePre (0 : ℤ)) z _ (w.s (fun _ => J₀ (cpt tatePre (0 : ℤ) ≫ β), PUnit.unit))
  have e₂ : gm (𝟙 _) z ⊤ (unitOn (u a b)) = t * t⁻¹ * t⁻¹ * t * val (τ₁ a b) (spMap ιb) z J₀ := e₁.symm.trans this
  rw [mul_inv_cancel, _root_.one_mul, inv_mul_cancel, _root_.one_mul] at e₂
  have hm := Good.mem hJ₀ ![c₀ (a + b), c₀ a, c₀ b, c₀ (0 : ℤ)] (spMap ιb)
  have e₃ := congrArg (Units.map ((spMap ev).stalkMap p).hom.toMonoidHom) e₂
  let e₀ : W →+* k₀ := (ev.comp ιb).codRestrict k₀ hk
  have hc : spMap ev ≫ spMap ιb = spMap k₀.subtype ≫ spMap e₀ :=
    (Spec.map_comp _ _).symm.trans (Spec.map_comp (CommRingCat.ofHom e₀) (CommRingCat.ofHom k₀.subtype))
  have hp : spMap ιb z = spMap e₀ (spMap k₀.subtype p) := congrArg (fun q : Sp K ⟶ Sp W => q p) hc
  have hm' := Eq.mp (congrArg (· ∈ _) hp) hm
  have e₄ := (stalkMap_gm (spMap ev) (𝟙 _) p ⊤ trivial _).symm.trans (e₃.trans (stalkMap_gm (spMap ev) (spMap ιb) p _ hm _))
  rw [hc, Category.comp_id, gm_spMap] at e₄
  replace e₄ := e₄.trans (gm_pull _ _ p _ hm' _).symm
  obtain ⟨x, hx⟩ := gm_field (spMap k₀.subtype) p _ hm' (pullU (spMap e₀) _ ((τ₁ a b).s _))
  replace e₄ := e₄.trans (hx.trans (gm_spMap _ p x))
  have e₅ : ev (u a b) = (x : k₀) := congrArg Units.val (gm_unitOn_inj p e₄)
  rw [e₅]; exact x.1.2

theorem exists_coords {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] (C : MonoFam Xo c φ V) :
    ∃ (N : ℕ) (s : Fin C.m ⊕ Fin N → V) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X))
      (τ₀ : Gens C.P.D.toPre), (∀ i, s (.inl i) = C.s i) ∧ (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) ∧
      (∀ k, IsUnit (s (.inr k))) ∧
      TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) := by
  obtain ⟨N, ε, hε⟩ := C.cone.basis
  obtain ⟨τ₀, hτ⟩ := C.exists_tauIn
  have hε' : ∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i := fun i => by rw [hε]
  refine ⟨N, Sum.elim C.s fun _ => 1, ε, τ₀, fun _ => rfl, hε', fun _ => isUnit_one, fun a b => ?_⟩
  obtain ⟨h₁, k, hk, h₂⟩ := hτ a b
  refine ⟨h₁, k, ?_, h₂⟩
  rw [hk]
  refine Eq.symm ((finSumFinEquiv.symm.prod_comp fun k => algebraMap V (FractionRing V) (Sum.elim C.s (fun _ => 1) k) ^
    ((l.M' : ℤ) • (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b).trans ?_)
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, map_one, one_zpow, Finset.prod_const_one, _root_.mul_one, hε']

theorem not_sepB_point {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] (C : MonoFam Xo c φ V) (hV : GlobalTheory.Mum.Base V) (hm : 1 ≤ C.m) :
    ¬ SepB Xo c φ (S := Sp c.F) (pullback.snd _ _) := fun h => by
  obtain ⟨N, s, ε, τ₀, h₁, h₂, h₃, h₄⟩ := exists_coords C
  let K := AlgebraicClosure (FractionRing V)
  let ev : V →+* K := (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V))
  have hev : Function.Injective ev :=
    (algebraMap (FractionRing V) K).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hs : Subsingleton (Sp c.F) := inferInstanceAs (Subsingleton (PrimeSpectrum c.F))
  have hk : IsAlgClosed (⊤ : Subfield K) := IsAlgClosed.of_ringEquiv K _ Subfield.topEquiv.symm
  have hd : DefOver (⊤ : Subfield K) (spMap ev ≫ spMap C.b) :=
    ⟨spMap (ev.codRestrict (⊤ : Subfield K) fun _ => Subfield.mem_top _) ≫ spMap C.b, by
      rw [← Category.assoc]; congr 1; exact (Spec.map_comp _ _).symm⟩
  have := (h V C hV (spMap C.b) C.y_over N s ε τ₀ h₁ h₂ h₃ h₄ K ev ⊤ hk (fun p => Subsingleton.elim _ _) hd).1 ⟨0, hm⟩
  rw [h₁, map_eq_zero_iff _ hev] at this
  exact C.s_ne_zero _ this

theorem exists_not_sepB : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)),
    IsPolFan H.bar (min Dw.p Dw.q) φ ∧ NoSelfInt H.bar (min Dw.p Dw.q) φ ∧
      ¬ SepB Xo c φ (S := Sp c.F) (pullback.snd _ _) := by
  obtain ⟨E, _, _, _, H, Dw, l, Xo, c, φ, C, h₁, h₂, h₃, -, h₅⟩ := exists_monoFam_nontrivial
  exact ⟨E, _, _, _, H, Dw, l, Xo, c, φ, h₁, h₂, not_sepB_point C h₃ h₅⟩

theorem sepAtB_closed {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] (C : MonoFam Xo c φ V) {N : ℕ} (s : Fin C.m ⊕ Fin N → V) (τ₀ : Gens C.P.D.toPre)
    (hs : ∀ i, s (.inl i) = C.s i) : SepAtB C.P.D.toPre τ₀ s (residue V) ⊤ :=
  (sepAtB_iff_of_range _ _ _ _ ⊤ fun _ => Subfield.mem_top _).2 fun i => by
    rw [hs]; exact (residue_eq_zero_iff _).2 (C.s_mem i)

end GlobalTheory.UChart.SepBModel
