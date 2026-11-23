import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GenRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique
open scoped LaurentSeries

theorem cstMul {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) (a b : V) :
    Geo.Tor.cst q z (a * b) = Geo.Tor.cst q z a * Geo.Tor.cst q z b := by rw [Geo.Tor.cst, map_mul, gs_mul q z ⊤ trivial]; rfl

theorem cstOne {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : Geo.Tor.cst q z 1 = 1 := by
  rw [Geo.Tor.cst, gs_eq q z ⊤ trivial, map_one, map_one, map_one]

theorem gs_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} (h : IsoMaps w σ s) (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
    (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem rigIso_eq (hG : Out.GlobalFnsSt) {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)}
    {B : Scheme.{0}} {t : SAB H B} {f : Sp V ⟶ B} (m2 : SABMap G t f)
    {w w' : LB.Iso G.PP.L (t.PP.L.pull m2.φ)} (m1 : SABMap G Xo.univ.t x)
    (h : RigIso m2 w) (h' : RigIso m2 w') : w = w' := by
  have hp : IsProper G.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  have hab : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hp, G.semi.geomConnected⟩
  exact GlobalTheory.iso_eq_of_maps_along_section (S := Sp V) (exists_chart G.PP.isLB)
    (fun y => (exists_chart t.PP.isLB (m2.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    G.G.hom (eSec G.G) (Over.w η[G.G]) (hG _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem gs_scal' {T : Type} [CommRing T] (x : Sp T ⟶ Xo.X) (a : T) (i : (PPx x).ι) {Z : Scheme.{0}} (g : Z ⟶ Gx x)
    (p : Z) (hp : g p ∈ (PPx x).U i) :
    gs g p _ (scal x a i) = Geo.Tor.cst (g ≫ (fst (Over.mk x) Xo.univ.t.G).left) p a :=
  gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ g p hp a

variable (Y : Model Xo c β) (V : Y.X.Opens) (s₀ : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j))
  (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ))

def Cut {T : Type} [CommRing T] (z : Sp T ⟶ Xo.XF c) (x : Sp T ⟶ Xo.X) (a : T) (s : LB.Sec (PPx x)) : Prop :=
  ∀ (Z : Scheme.{0}) (g : Z ⟶ Gx x) (f : Z ⟶ Y.oF.t.G.left) (p : Z) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι)
    (j₀ : Xo.univ.t.PP.L.ι), f ≫ Y.m0.toSABMap.φ = g ≫ (snd (Over.mk x) Xo.univ.t.G).left →
    f ≫ Y.oF.t.G.hom = g ≫ (fst (Over.mk x) Xo.univ.t.G).left ≫ z →
    Y.m.φ (f p) ∈ Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j → f p ∈ Y.oF.t.PP.L.U k →
    Y.m0.toSABMap.φ (f p) ∈ Xo.univ.t.PP.L.U j₀ →
    (gw w₀ f p j₀ k).val * gs (f ≫ Y.m.φ) p _ (s₀ j) =
      (gw w₁ f p j k).val * (Geo.Tor.cst (g ≫ (fst (Over.mk x) Xo.univ.t.G).left) p a * gs g p _ (s.f (fun _ => j₀)))

variable {Y V s₀ w₀ w₁}

theorem mem_chart {T : Type} [CommRing T] {x : Sp T ⟶ Xo.X} {Z : Scheme.{0}} {g : Z ⟶ Gx x} {f : Z ⟶ Y.oF.t.G.left}
    (e : f ≫ Y.m0.toSABMap.φ = g ≫ (snd (Over.mk x) Xo.univ.t.G).left) (p : Z) (j₀ : Xo.univ.t.PP.L.ι) :
    g p ∈ (PPx x).U (fun _ => j₀) ↔ Y.m0.toSABMap.φ (f p) ∈ Xo.univ.t.PP.L.U j₀ :=
  ⟨fun h => (congrArg (fun q => q p ∈ Xo.univ.t.PP.L.U j₀) e).mpr (Set.mem_iInter.1 h 0),
    fun h => Set.mem_iInter.2 fun _ => (congrArg (fun q => q p ∈ Xo.univ.t.PP.L.U j₀) e).mp h⟩

theorem Cut.pull {T T' : Type} [CommRing T] [CommRing T'] (φ : T →+* T') {z : Sp T ⟶ Xo.XF c} {x : Sp T ⟶ Xo.X}
    {x' : Sp T' ⟶ Xo.X} {a b : T} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (h : Cut Y V s₀ w₀ w₁ z x (a * b) s)
    (hs : SecBC φ b x x' s s') : Cut Y V s₀ w₀ w₁ (spMap φ ≫ z) x' (φ a) s' := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := hs
  intro Z g f p j k j₀ e₁ e₂ m₁ m₂ m₃
  have mg := (mem_chart e₁ p j₀).2 m₃
  have hle := FramedBaseChange.chart_le pm h₁ (fun _ => j₀)
  have e := h Z (g ≫ pm) f p j k j₀ (by rw [Category.assoc, h₁]; exact e₁)
    (by rw [e₂, Category.assoc, reassoc_of% h₂]) m₁ m₂ m₃
  rw [e, ← h₃ _ hle, gs_appLE pm _ _ hle g p mg, gs_mul (g ≫ pm) p _ (hle mg), gs_scal' x b _ (g ≫ pm) p (hle mg),
    cstMul, _root_.mul_assoc, Category.assoc, h₂, ← Category.assoc, cst_comp]

theorem Cut.chg {T : Type} [CommRing T] {z : Sp T ⟶ Xo.XF c} {x x' : Sp T ⟶ Xo.X}
    {a b : T} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (hx : x' = x) (h : Cut Y V s₀ w₀ w₁ z x' a s')
    (hs : SecBC (RingHom.id T) b x x' s s') : Cut Y V s₀ w₀ w₁ z x (a * b) s := by
  subst hx
  obtain ⟨pm, h₁, h₂, h₃⟩ := hs
  obtain rfl : pm = 𝟙 _ := by
    apply FramedBaseChange.pulledGroup_hom_ext
    · rw [h₁, Category.id_comp]
    · rw [h₂, Category.id_comp]
      exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
  intro Z g f p j k j₀ e₁ e₂ m₁ m₂ m₃
  have mg := (mem_chart e₁ p j₀).2 m₃
  have e := h Z g f p j k j₀ e₁ e₂ m₁ m₂ m₃
  have hle := FramedBaseChange.chart_le (𝟙 _) h₁ (fun _ => j₀)
  rw [e, ← h₃ _ hle, gs_appLE (𝟙 _) _ _ hle g p mg, Category.comp_id, gs_mul g p _ mg, gs_scal' x' b _ g p mg,
    cstMul, _root_.mul_assoc]

theorem exists_lift' {T : Type} [CommRing T] (z : Sp T ⟶ Xo.XF c) {x : Sp T ⟶ Xo.X} (hx : z ≫ pullback.fst _ _ = x)
    {Z : Scheme.{0}} (g : Z ⟶ Gx x) : ∃ f : Z ⟶ Y.oF.t.G.left,
      f ≫ Y.m0.toSABMap.φ = g ≫ (snd (Over.mk x) Xo.univ.t.G).left ∧
      f ≫ Y.oF.t.G.hom = g ≫ (fst (Over.mk x) Xo.univ.t.G).left ≫ z := by
  have cond : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  have cond' : (g ≫ (snd (Over.mk x) Xo.univ.t.G).left) ≫ Xo.univ.t.G.hom =
      (g ≫ (fst (Over.mk x) Xo.univ.t.G).left ≫ z) ≫ pullback.fst _ _ := by
    rw [Category.assoc, cond, Category.assoc, Category.assoc, hx]
  exact ⟨Y.m0.toSABMap.cart.1.lift _ _ cond', Y.m0.toSABMap.cart.1.lift_fst _ _ cond',
    Y.m0.toSABMap.cart.1.lift_snd _ _ cond'⟩

theorem mem_over {T : Type} [CommRing T] {z : Sp T ⟶ Xo.XF c} (hV : ⊤ ≤ (z ≫ Y.j) ⁻¹ᵁ V) {Z : Scheme.{0}}
    {f : Z ⟶ Y.oF.t.G.left} {q : Z ⟶ Sp T} (e : f ≫ Y.oF.t.G.hom = q ≫ z) (p : Z) :
    Y.m.φ (f p) ∈ Y.t.G.hom ⁻¹ᵁ V := by
  have : (f ≫ Y.m.φ) ≫ Y.t.G.hom = q ≫ z ≫ Y.j := by
    rw [Category.assoc, Y.m.cart.1.w, reassoc_of% e]; rfl
  exact (congrArg (fun u => u p ∈ V) this).mpr (hV (x := q p) trivial)

theorem Cut.eq {T : Type} [CommRing T] {z : Sp T ⟶ Xo.XF c} {x : Sp T ⟶ Xo.X} (hx : z ≫ pullback.fst _ _ = x)
    (hV : ⊤ ≤ (z ≫ Y.j) ⁻¹ᵁ V) {a a' : T} {s s' : LB.Sec (PPx x)} (h : Cut Y V s₀ w₀ w₁ z x a s)
    (h' : Cut Y V s₀ w₀ w₁ z x a' s') (i : (PPx x).ι) : scal x a i * s.f i = scal x a' i * s'.f i := by
  obtain ⟨j₀, rfl⟩ : ∃ j₀ : Xo.univ.t.PP.L.ι, i = fun _ => j₀ :=
    ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
  obtain ⟨f, e₁, e₂⟩ := exists_lift' (Y := Y) z hx (𝟙 _)
  refine fn_ext fun p hp => ?_
  obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (Y.m.φ (f p))
  obtain ⟨k, hk⟩ := exists_chart Y.oF.t.PP.isLB (f p)
  have hm : Y.m.φ (f p) ∈ Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j :=
    ⟨mem_over hV (e₂.trans (Category.assoc _ _ _).symm) p, hj⟩
  have h0 := (mem_chart e₁ p j₀).1 hp
  have e := (h _ _ f p j k j₀ e₁ e₂ hm hk h0).symm.trans (h' _ _ f p j k j₀ e₁ e₂ hm hk h0)
  rw [gs_mul _ p _ hp, gs_mul _ p _ hp, gs_scal' x a _ (𝟙 _) p hp, gs_scal' x a' _ (𝟙 _) p hp]
  exact (Units.mul_right_inj _).1 e

theorem exists_cut (h₀ : RigIso Y.m0.toSABMap w₀) (h₁ : RigIso Y.m w₁)
    (hs : s₀ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V)) {T : Type} [CommRing T] {z : Sp T ⟶ Xo.XF c} {x : Sp T ⟶ Xo.X}
    (hx : z ≫ pullback.fst _ _ = x) (hV : ⊤ ≤ (z ≫ Y.j) ⁻¹ᵁ V) : ∃ S, Cut Y V s₀ w₀ w₁ z x 1 S := by
  obtain ⟨t', ⟨n⟩⟩ : ∃ t' : SAB H (Sp T), Nonempty (SABMap t' Y.oF.t z) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull z Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨wn, rn⟩ := exists_rigIso n
  obtain ⟨m1, e1, w1, r1, T1⟩ := exists_comp_rig Y.m0.toSABMap n x hx.symm h₀ rn
  obtain ⟨m2, e2, w2, r2, T2⟩ := exists_comp_rig Y.m n _ rfl h₁ rn
  have hm : ∀ p, m2.φ p ∈ Y.t.G.hom ⁻¹ᵁ V := fun p =>
    (congrArg (fun q => q p ∈ Y.t.G.hom ⁻¹ᵁ V) e2).mpr (mem_over hV n.cart.1.w p)
  have le : ∀ j, m2.φ ⁻¹ᵁ Y.t.PP.L.U j ≤ m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j) := fun j p hp => ⟨hm p, hp⟩
  obtain ⟨τ, hτ⟩ := sec_down ((isGen_iff w2).1 r2.1) Y.t.PP.isLB t'.PP.isLB
    (fun j => (m2.φ.appLE _ _ (le j)).hom (s₀ j)) (fun y j j' a b => by
      rw [gs_appLE m2.φ _ _ (le j) (𝟙 _) y a, gs_appLE m2.φ _ _ (le j') (𝟙 _) y b, Category.id_comp]
      exact GlobalTheory.ThetaUnit.gs_secOn hs m2.φ y (hm y) a b)
  obtain ⟨S, hS⟩ := exists_up m1 ((isGen_iff w1).1 r1.1) τ
  obtain ⟨h, hφ, hh, -, h0g⟩ := exists_inv m1
  refine ⟨S, fun Z g f p j k j₀ a₁ a₂ b₁ b₂ b₃ => ?_⟩
  have ef : (g ≫ h) ≫ n.φ = f := by
    apply Y.m0.toSABMap.cart.1.hom_ext
    · refine Eq.trans ?_ a₁.symm
      rw [Category.assoc, Category.assoc, ← hφ, e1]
    · rw [a₂, Category.assoc, n.cart.1.w, Category.assoc, reassoc_of% hh]
  subst ef
  obtain ⟨k', hk'⟩ := exists_chart t'.PP.isLB ((g ≫ h) p)
  have c₁ : m1.φ ((g ≫ h) p) ∈ Xo.univ.t.PP.L.U j₀ :=
    (congrArg (fun q => q ((g ≫ h) p) ∈ Xo.univ.t.PP.L.U j₀) e1).mpr b₃
  have c₂ : m2.φ ((g ≫ h) p) ∈ Y.t.PP.L.U j :=
    (congrArg (fun q => q ((g ≫ h) p) ∈ Y.t.PP.L.U j) e2).mpr b₁.2
  have u₁ := hS Z (g ≫ h) p j₀ k' c₁ hk'
  have u₂ := hτ Z (g ≫ h) p j k' c₂ hk'
  rw [gs_appLE m2.φ _ _ (le j) (g ≫ h) p c₂, T2 Z _ p j k k' b₁.2 b₂ hk'] at u₂
  rw [Category.assoc, h0g, Category.comp_id, T1 Z _ p j₀ k k' b₃ b₂ hk'] at u₁
  have eg : ((g ≫ h) ≫ n.φ) ≫ Y.m.φ = (g ≫ h) ≫ m2.φ := by rw [e2, Category.assoc]
  rw [eg, u₁, u₂, cstOne, Units.val_mul, Units.val_mul]
  ring

theorem exists_cut_gen (h₀ : RigIso Y.m0.toSABMap w₀) (h₁ : RigIso Y.m w₁)
    (hs : s₀ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V)) {T : Type} [CommRing T] {z : Sp T ⟶ Xo.XF c} {x : Sp T ⟶ Xo.X}
    (hx : z ≫ pullback.fst _ _ = x) (hV : ⊤ ≤ (z ≫ Y.j) ⁻¹ᵁ V) {s : LB.Sec (PPx x)} (hg : SecGen x s) :
    ∃! a, Cut Y V s₀ w₀ w₁ z x a s := by
  obtain ⟨S, hS⟩ := exists_cut h₀ h₁ hs hx hV
  obtain ⟨a, ha, hu⟩ := hg S
  have one : ∀ i, scal x 1 i * S.f i = S.f i := fun i => fn_ext fun p hp => by
    rw [gs_mul _ p _ hp, gs_scal' x 1 _ (𝟙 _) p hp, cstOne, _root_.one_mul]
  refine ⟨a, ?_, fun a' h' => hu a' fun i => (one i).symm.trans (hS.eq hx hV h' i)⟩
  intro Z g f p j k j₀ e₁ e₂ m₁ m₂ m₃
  have mg := (mem_chart e₁ p j₀).2 m₃
  rw [hS Z g f p j k j₀ e₁ e₂ m₁ m₂ m₃, cstOne, _root_.one_mul, ha (fun _ => j₀), gs_mul g p _ mg, gs_scal' x a _ g p mg]

theorem pullsToMul_gs {A : Type} [CommRing A] {χ : Sp A ⟶ Y.X} {t : SAB H (Sp A)} (m : SABMap t Y.t χ)
    (L : RigLB t.G) (hL : L = t.PP) (w₂ : LB.Iso L.L (Y.t.PP.L.pull m.φ)) (hw : IsRigIso m.cm L Y.t.PP w₂)
    (σ : Out.H0 L.L 1) (θ' : LB.Sec L.L) (θ : LB.Sec t.PP.L) (hσ : SectionOfLineBundleOne σ θ') (hθ : HEq θ θ') (r : A)
    (h : GlobalTheory.ThetaUnit.PullsToMul t.G.hom m.φ w₂ (Y.t.G.hom ⁻¹ᵁ V) s₀ r σ) :
    ∃ w, RigIso m w ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ t.G.left) (p : Z) j k,
      m.φ (q p) ∈ Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j → q p ∈ t.PP.L.U k →
      gs (q ≫ m.φ) p _ (s₀ j) = (gw w q p j k).val * (Geo.Tor.cst (q ≫ t.G.hom) p r * gs q p _ (θ.f k)) := by
  subst hL
  obtain rfl := eq_of_heq hθ
  refine ⟨w₂, hw, fun Z q p j k a b => ?_⟩
  have c₂ : q p ∈ (LB.div (Y.t.PP.L.pull m.φ) t.PP.L).U (fun _ => j, k) := ⟨mem_pull.2 a.2, b⟩
  have c₃ : q p ∈ LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k) := Set.mem_iInter.2 fun _ => b
  have hp : q p ∈ m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j) ⊓
      ((LB.div (Y.t.PP.L.pull m.φ) t.PP.L).U (fun _ => j, k) ⊓
        LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) := ⟨a, c₂, c₃⟩
  have e := congrArg (gs q p _) (h j k _ inf_le_left (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
  have le : LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k) ≤ t.PP.L.U k :=
    fun y hy => Set.mem_iInter.1 hy 0
  rw [gs_appLE m.φ _ _ _ q p hp, gs_mul q p _ hp, gs_mul q p _ hp, gs_constFn _ _ q p hp, _root_.mul_assoc] at e
  refine e.trans (congrArg₂ (· * ·) ((gs_res q p _ hp _).trans (gs_unit q p _ c₂ _))
    (congrArg _ ((gs_res q p _ hp _).trans ?_)))
  exact (congrArg (gs q p _) (hσ (fun _ => k) le)).trans (gs_res q p _ c₃ _)

theorem cut_arc (hG : Out.GlobalFnsSt) (h₀ : RigIso Y.m0.toSABMap w₀) (h₁ : RigIso Y.m w₁)
    {A S : Type} [CommRing A] [CommRing S] (io : A →+* S) {χ : Sp A ⟶ Y.X} {t : SAB H (Sp A)} (m : SABMap t Y.t χ)
    (θ : LB.Sec t.PP.L) (r : A) (w : LB.Iso t.PP.L (Y.t.PP.L.pull m.φ)) (hw : RigIso m w)
    (hθ : ∀ (Z : Scheme.{0}) (q : Z ⟶ t.G.left) (p : Z) j k,
      m.φ (q p) ∈ Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j → q p ∈ t.PP.L.U k →
      gs (q ≫ m.φ) p _ (s₀ j) = (gw w q p j k).val * (Geo.Tor.cst (q ≫ t.G.hom) p r * gs q p _ (θ.f k)))
    {z : Sp S ⟶ Xo.XF c} {x : Sp S ⟶ Xo.X} (s : LB.Sec (PPx x)) {t' : SAB H (Sp S)} (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' t (spMap io)) (φ : t'.G.left ⟶ Y.oF.t.G.left) (zj : z ≫ Y.j = spMap io ≫ χ)
    (zx : z ≫ pullback.fst _ _ = x) (φb : φ ≫ Y.oF.t.G.hom = t'.G.hom ≫ z) (φ1 : φ ≫ Y.m0.toSABMap.φ = m1.φ)
    (φ2 : φ ≫ Y.m.φ = m2.φ ≫ m.φ) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ))
    (w2 : LB.Iso t'.PP.L (t.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ))
    (θ2 : LB.Sec (t.PP.L.pull m2.φ)) (r1 : RigIso m1 w1) (r2 : RigIso m2 w2) (i1 : IsoMaps w1 σ' s1)
    (i2 : IsoMaps w2 σ' θ2) (ps : PullSec m2.φ θ θ2)
    (hc : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) :
    Cut Y V s₀ w₀ w₁ z x (io r) s := by
  subst zx
  obtain ⟨n, en⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' _ z Y.m0.toSABMap m1
  have en' : m1.φ = n.φ ≫ Y.m0.toSABMap.φ := en
  obtain rfl : φ = n.φ := by
    apply Y.m0.toSABMap.cart.1.hom_ext
    · exact φ1.trans en'
    · rw [φb, n.cart.1.w]
  obtain ⟨wn, rn⟩ := exists_rigIso n
  obtain ⟨w1', r1', T1⟩ := cube_rig_comp Y.m0.toSABMap.cm n.cm m1.cm en'
    (by rw [m1.base, n.base, Y.m0.toSABMap.base]) _ _ _ w₀ wn h₀ rn
  obtain rfl : w1' = w1 := rigIso_eq hG m1 m1 r1' r1
  obtain ⟨N, eN, wN, rN, TN⟩ := exists_comp_rig m m2 _ zj hw r2
  obtain ⟨wN', rN', TN'⟩ := cube_rig_comp Y.m.cm n.cm N.cm (eN.trans φ2.symm)
    (by rw [N.base, n.base, Y.m.base]; rfl) _ _ _ w₁ wn h₁ rn
  obtain rfl : wN' = wN := rigIso_eq hG N m1 rN' rN
  obtain ⟨h, hφ, hh, -, h0g⟩ := exists_inv m1
  intro Z g f p j k j₀ a₁ a₂ b₁ b₂ b₃
  have ef : (g ≫ h) ≫ n.φ = f := by
    apply Y.m0.toSABMap.cart.1.hom_ext
    · refine Eq.trans ?_ a₁.symm
      rw [Category.assoc, Category.assoc, ← hφ, en']
    · rw [a₂, Category.assoc, n.cart.1.w, Category.assoc, reassoc_of% hh]
  subst ef
  obtain ⟨k', hk'⟩ := exists_chart t'.PP.isLB ((g ≫ h) p)
  obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (m2.φ ((g ≫ h) p))
  have c₁ : m1.φ ((g ≫ h) p) ∈ Xo.univ.t.PP.L.U j₀ :=
    (congrArg (fun q => q ((g ≫ h) p) ∈ Xo.univ.t.PP.L.U j₀) en').mpr b₃
  have c₂ : m.φ (m2.φ ((g ≫ h) p)) ∈ Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j :=
    (congrArg (fun q => q ((g ≫ h) p) ∈ Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j) φ2).mp b₁
  have c₃ : N.φ ((g ≫ h) p) ∈ Y.t.PP.L.U j :=
    (congrArg (fun q => q ((g ≫ h) p) ∈ Y.t.PP.L.U j) eN).mpr c₂.2
  have le₁ : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => j₀) ≤ toGx m1 ⁻¹ᵁ (PPx _).U (fun _ => j₀) :=
    fun q hq => le_toGx m1 j₀ (mem_pull.1 hq)
  have le₂ : (t.PP.L.pull m2.φ).U (fun _ => i) ≤ m2.φ ⁻¹ᵁ t.PP.L.U i := fun q hq => mem_pull.1 hq
  have u₁ := gs_of_isoMaps i1 Z (g ≫ h) p j₀ k' c₁ hk'
  have u₂ := gs_of_isoMaps i2 Z (g ≫ h) p i k' hi hk'
  rw [hc (toGx m1) (toGx_snd m1) (toGx_fst m1) (fun _ => j₀) le₁,
    gs_appLE (toGx m1) _ _ le₁ (g ≫ h) p (mem_pull.2 c₁), Category.assoc, h0g, Category.comp_id,
    T1 Z _ p j₀ k k' c₁ b₂ hk'] at u₁
  rw [ps (fun _ => i) le₂, gs_appLE m2.φ _ _ le₂ (g ≫ h) p (mem_pull.2 hi)] at u₂
  have u₃ := hθ Z ((g ≫ h) ≫ m2.φ) p j i c₂ hi
  have u₄ := congrArg Units.val ((TN Z (g ≫ h) p j i k' c₂.2 hi hk').symm.trans (TN' Z (g ≫ h) p j k k' c₃ b₂ hk'))
  have eg : ((g ≫ h) ≫ n.φ) ≫ Y.m.φ = ((g ≫ h) ≫ m2.φ) ≫ m.φ := by rw [Category.assoc, φ2, Category.assoc _ m2.φ]
  have ec : ((g ≫ h) ≫ m2.φ) ≫ t.G.hom = (g ≫ (fst (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left) ≫ spMap io := by
    rw [Category.assoc, m2.cart.1.w, Category.assoc, reassoc_of% hh, Category.assoc]
  rw [ec, cst_comp, u₂] at u₃
  rw [Units.val_mul, Units.val_mul] at u₄
  rw [eg, u₃, u₁, Units.val_mul]
  linear_combination ((gw w₀ ((g ≫ h) ≫ n.φ) p j₀ k).val * Geo.Tor.cst (g ≫ (fst (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left) p (io r) * gs (g ≫ h) p _ (σ'.f k')) * u₄

theorem cut_complex (hT : Out.SecTwistSt) {z : Sp ℂ ⟶ Xo.XF c} {x : Sp ℂ ⟶ Xo.X} (hx : z ≫ pullback.fst _ _ = x)
    (hV : ⊤ ≤ (z ≫ Y.j) ⁻¹ᵁ V) {s : LB.Sec (PPx x)} (hg : SecGen x s) {a : ℂ} (hc : Cut Y V s₀ w₀ w₁ z x a s) (b : ℂ)
    (hb : ∀ (pt : Sp ℂ ⟶ Gx x) (f : Sp ℂ ⟶ Y.oF.t.G.left) j k j₀, pt ≫ Formalism.L2.PjFree.gxSnd x = 𝟙 _ →
      f ≫ Y.m0.toSABMap.φ = pt ≫ Formalism.L2.PjFree.gxFst x → f ≫ Y.oF.t.G.hom = z →
      ⊤ ≤ f ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) →
      ⊤ ≤ f ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) →
      valAt' f _ (w₀.s (fun _ => j₀, k)).val * valAt' (f ≫ Y.m.φ) _ (s₀ j) =
        valAt' f _ (w₁.s (fun _ => j, k)).val * (b * valAt' pt ((PPx x).U (fun _ => j₀)) (s.f (fun _ => j₀)))) :
    a = b := by
  obtain ⟨i, pt, hpt, hne⟩ := (GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo x s).2.1.1 hg
  obtain ⟨j₀, rfl⟩ : ∃ j₀ : Xo.univ.t.PP.L.ι, i = fun _ => j₀ :=
    ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
  have hpt' : pt ≫ (fst (Over.mk x) Xo.univ.t.G).left = 𝟙 _ := hpt
  have hU : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U (fun _ => j₀) := by
    by_contra h
    exact hne (dif_neg h)
  obtain ⟨f, e₁, e₂⟩ := exists_lift' (Y := Y) z hx pt
  have e₃ : f ≫ Y.oF.t.G.hom = z := by rw [e₂, reassoc_of% hpt']
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have all : ∀ {X : Scheme.{0}} (u : Sp ℂ ⟶ X) (U : X.Opens), u p ∈ U → ⊤ ≤ u ⁻¹ᵁ U := fun u U h q _ =>
    (Subsingleton.elim (α := PrimeSpectrum ℂ) p q) ▸ h
  obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (Y.m.φ (f p))
  obtain ⟨k, hk⟩ := exists_chart Y.oF.t.PP.isLB (f p)
  have hm : Y.m.φ (f p) ∈ Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U j :=
    ⟨mem_over hV (e₂.trans (Category.assoc _ _ _).symm) p, hj⟩
  have h0 := (mem_chart e₁ p j₀).1 (hU (x := p) trivial)
  have c₁ : f p ∈ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) := ⟨mem_pull.2 hj, hk⟩
  have c₀ : f p ∈ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) :=
    ⟨mem_pull.2 h0, hk⟩
  have e := hc _ pt f p j k j₀ e₁ e₂ hm hk h0
  have e' := congrArg (TorusExt.stalkConst p) (hb pt f j k j₀ hpt e₁ e₃ (all f _ c₁) (all f _ c₀))
  have v₀ : TorusExt.stalkConst p (valAt' f _ (w₀.s (fun _ => j₀, k)).val) = (gw w₀ f p j₀ k).val :=
    (TorusExt.gs_eq_stalkConst f p (all f _ c₀) _).symm.trans (gs_unit f p _ c₀ _)
  have v₁ : TorusExt.stalkConst p (valAt' f _ (w₁.s (fun _ => j, k)).val) = (gw w₁ f p j k).val :=
    (TorusExt.gs_eq_stalkConst f p (all f _ c₁) _).symm.trans (gs_unit f p _ c₁ _)
  have v₂ : TorusExt.stalkConst p (valAt' (f ≫ Y.m.φ) _ (s₀ j)) = gs (f ≫ Y.m.φ) p _ (s₀ j) :=
    (TorusExt.gs_eq_stalkConst (f ≫ Y.m.φ) p (all (f ≫ Y.m.φ) _ hm) _).symm
  have v₃ : TorusExt.stalkConst p (valAt' pt ((PPx x).U (fun _ => j₀)) (s.f (fun _ => j₀))) =
      gs pt p _ (s.f (fun _ => j₀)) := (TorusExt.gs_eq_stalkConst pt p hU _).symm
  have v₄ : Geo.Tor.cst (𝟙 (Sp ℂ)) p a = TorusExt.stalkConst p a := gs_eq _ p ⊤ trivial _
  rw [map_mul, map_mul, v₀, v₁, v₂, e, Units.mul_right_inj, hpt', v₄, ← v₃, ← map_mul] at e'
  exact mul_right_cancel₀ hne ((TorusExt.stalkConst p).injective e')

theorem const_eq {g : ℕ} {D₀ : Out.DegPre ℂ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ D₀.P.A.left)} (he : IsHolTo Set.univ e)
    {th : D₀.P.L.Sec} {θ : (Fin g → ℂ) → ℂ} {κ κ' : ℂ} (h : IsFnInRigFrame D₀ e th (fun z => κ * θ z))
    (h' : IsFnInRigFrame D₀ e th (fun z => κ' * θ z)) (z₀ : Fin g → ℂ) (j : D₀.P.L.ι)
    (hne : valAt' (e z₀) (D₀.P.L.U j) (th.f j) ≠ 0) : κ = κ' := by
  obtain ⟨fr, d, n, t, r, v⟩ := h
  obtain ⟨fr', d', n', t', r', v'⟩ := h'
  have ex : ∀ z, ∃ i, ⊤ ≤ e z ⁻¹ᵁ D₀.P.L.U i := fun z => by
    obtain ⟨i, hi⟩ := exists_chart D₀.P.isLB (e z (IsLocalRing.closedPoint ℂ))
    exact ⟨i, fun q _ => (Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) q) ▸ hi⟩
  choose J hJ using ex
  have op : ∀ i, IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ D₀.P.L.U i} := fun i => by simpa using (he _ (th.f i)).1
  let ρ : (Fin g → ℂ) → ℂ := fun z => fr (J z) z / fr' (J z) z
  have hρ : ∀ i z, ⊤ ≤ e z ⁻¹ᵁ D₀.P.L.U i → ρ z = fr i z / fr' i z := fun i z hi => by
    have hm : ⊤ ≤ e z ⁻¹ᵁ (D₀.P.L.U (J z) ⊓ D₀.P.L.U i) := fun q hq => ⟨hJ z hq, hi hq⟩
    have a := t _ _ z hm
    have a' := t' _ _ z hm
    have hg := left_ne_zero_of_mul (a ▸ n _ z (hJ z))
    show fr (J z) z / fr' (J z) z = _
    rw [a, a', mul_div_mul_left _ _ hg]
  have dρ : Differentiable ℂ ρ := fun z => by
    have hn := (op (J z)).mem_nhds (hJ z)
    refine (((d _).differentiableAt hn).mul
      (((d' _).differentiableAt hn).inv (n' _ z (hJ z)))).congr_of_eventuallyEq ?_
    filter_upwards [hn] with u hu using (hρ _ u hu).trans (div_eq_mul_inv _ _)
  have hU : ⊤ ≤ e z₀ ⁻¹ᵁ D₀.P.L.U j := by
    by_contra h
    exact hne (dif_neg h)
  have hn := (op j).mem_nhds hU
  have cv : ContinuousAt (fun z => valAt' (e z) (D₀.P.L.U j) (th.f j)) z₀ :=
    ((he _ (th.f j)).2.differentiableAt (by simpa using hn)).continuousAt
  have ev : ∀ᶠ z in nhds z₀, κ * ρ z = κ' := by
    filter_upwards [hn, cv.eventually_ne hne] with u hu hv
    have a : _ = κ * θ u * _ := v j u hu
    have a' : _ = κ' * θ u * _ := v' j u hu
    have hθ : θ u ≠ 0 := fun h0 => hv (by rw [a, h0]; ring)
    rw [hρ j u hu, ← mul_div_assoc, div_eq_iff (n' j u hu)]
    apply mul_left_cancel₀ hθ
    linear_combination a' - a
  have dl : Differentiable ℂ (fun s : ℂ => s • z₀) := differentiable_id.smul_const z₀
  have an : AnalyticOnNhd ℂ (fun s : ℂ => κ * ρ (s • z₀)) Set.univ := fun s _ =>
    (((dρ.comp dl).const_mul κ).analyticAt s)
  have ev' : (fun s : ℂ => κ * ρ (s • z₀)) =ᶠ[nhds 1] fun _ => κ' := by
    have : Filter.Tendsto (fun s : ℂ => s • z₀) (nhds 1) (nhds z₀) := by
      simpa using dl.continuous.tendsto 1
    exact this.eventually ev
  have := congrFun (an.eq_of_eventuallyEq analyticOnNhd_const ev') 0
  have r1 : ρ 0 = 1 := by
    show fr (J 0) 0 / fr' (J 0) 0 = 1
    rw [r _ (hJ 0), ← r' _ (hJ 0), div_self (n' _ 0 (hJ 0))]
  simpa [r1] using this

theorem exists_val_ne [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {D₀ : Out.DegPre ℂ}
    {th : D₀.P.L.Sec} (h : ThNZ th) : ∃ (u : Out.GtPtF D₀ ℂ) (j : D₀.P.L.ι),
      valAt' (show Sp ℂ ⟶ _ from u.b.left) (D₀.P.L.U j) (th.f j) ≠ 0 := by
  obtain ⟨x, -, hx⟩ := h (IsLocalRing.closedPoint ℂ)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  haveI := D₀.P.isAb.proper
  have : JacobsonSpace D₀.P.A.left := LocallyOfFiniteType.jacobsonSpace D₀.P.A.hom
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints (Z := (D₀.P.A.left.basicOpen (th.f j) : Set _)) ⟨x, hj⟩
    (D₀.P.A.left.basicOpen (th.f j)).isOpen.isLocallyClosed
  have hb : pointOfClosedPoint (K := ℂ) D₀.P.A.hom y hc ≫ D₀.P.A.hom = (Out.TF (R := ℂ) ℂ).hom := by
    refine (pointOfClosedPoint_comp (K := ℂ) D₀.P.A.hom y hc).trans ?_
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact (Spec.map_id _).symm
  obtain ⟨u, hu⟩ := TorusExt.exists_lift (D := D₀) (F := ℂ) (Over.homMk _ hb)
  refine ⟨u, j, ?_⟩
  rw [hu]
  show valAt' (pointOfClosedPoint (K := ℂ) D₀.P.A.hom y hc) _ _ ≠ 0
  have hq : ∀ q, pointOfClosedPoint (K := ℂ) D₀.P.A.hom y hc q = y := pointOfClosedPoint_apply (K := ℂ) _ y hc
  generalize pointOfClosedPoint (K := ℂ) D₀.P.A.hom y hc = b at hq
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hm : b p ∈ D₀.P.A.left.basicOpen (th.f j) := (hq p).symm ▸ hy
  have hU : ⊤ ≤ b ⁻¹ᵁ D₀.P.L.U j := fun q _ => D₀.P.A.left.basicOpen_le _ (show b q ∈ _ from (hq q).symm ▸ hy)
  have hun := ((GlobalTheory.ThetaUnit.mem_basicOpen_iff_gs (th.f j) (x := b p) (hU (x := p) trivial)).1 hm).map (b.stalkMap p).hom
  rw [← gs_stalkMap b p _ (hU (x := p) trivial), TorusExt.gs_eq_stalkConst b p hU] at hun
  intro h0
  rw [show valF b _ (th.f j) = 0 from h0, map_zero] at hun
  exact not_isUnit_zero hun

open GlobalTheory.Conv in

theorem exists_hasSum_div {A B R s : ℂ⸨X⸩} (n : ℕ) (hA : A ∈ convLaurent) (hB : B ∈ convLaurent) (hR : R ∈ convLaurent)
    (hB0 : B ≠ 0) (hR0 : R ≠ 0) (h : A = B ^ n * (R * s)) : ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ a b r : ℂ,
      HasSum (fun m : ℤ => A.coeff m * eTwoPi w ^ m) a → HasSum (fun m : ℤ => B.coeff m * eTwoPi w ^ m) b →
      HasSum (fun m : ℤ => R.coeff m * eTwoPi w ^ m) r →
      b ≠ 0 ∧ ∀ x : ℂ, a = b ^ n * (r * x) → HasSum (fun m : ℤ => s.coeff m * eTwoPi w ^ m) x := by
  have hs : s ∈ convLaurent := by
    have : s = A / (B ^ n * R) := by rw [h]; field_simp
    rw [this]
    exact div_mem hA (mul_mem (pow_mem hB n) hR)
  obtain ⟨T, hT⟩ := exists_forall_mem_halfRing (S := {A, B, R, s}) (Set.toFinite _) (by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption)
  let A' : halfRing T := ⟨A, hT A (by simp)⟩
  let B' : halfRing T := ⟨B, hT B (by simp)⟩
  let R' : halfRing T := ⟨R, hT R (by simp)⟩
  let s' : halfRing T := ⟨s, hT s (by simp)⟩
  have h' : A' = B' ^ n * (R' * s') := Subtype.ext h
  obtain ⟨T₁, h₁, hb⟩ := exists_ev_ne_zero (s := B') fun e => hB0 (congrArg Subtype.val e)
  obtain ⟨T₂, h₂, hr⟩ := exists_ev_ne_zero (s := R') fun e => hR0 (congrArg Subtype.val e)
  refine ⟨max T₁ T₂, fun w hw a b r ha' hb' hr' => ?_⟩
  have w₁ := (le_max_left _ _).trans_lt hw
  have w₂ := (le_max_right _ _).trans_lt hw
  have w₀ := h₁.trans_lt w₁
  obtain rfl := ev_eq_of_hasSum w₀ A' ha'
  obtain rfl := ev_eq_of_hasSum w₀ B' hb'
  obtain rfl := ev_eq_of_hasSum w₀ R' hr'
  refine ⟨hb w w₀ w₁, fun x hx => ?_⟩
  rw [h', map_mul, map_mul, map_pow] at hx
  obtain rfl := mul_left_cancel₀ (hr w w₀ w₂) (mul_left_cancel₀ (pow_ne_zero n (hb w w₀ w₁)) hx)
  exact hasSum_ev w₀ s'

theorem secBC_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {y' : FrPt Xo c T} (h : FrMap φ y y') : SecBC φ.toRingHom 1 y.x y'.x y.s y'.s := by
  obtain ⟨-, -, pm, h₁, h₂, h₃⟩ := h
  refine ⟨pm, h₁, h₂, fun i hi => Eq.trans (congrArg _ (fn_ext fun p hp => ?_)) (h₃ i hi)⟩
  rw [gs_mul _ p _ hp, gs_scal' y.x 1 _ (𝟙 _) p hp, cstOne, _root_.one_mul]

theorem exists_ratio (hB : Out.SecBaseChangeSt) (h₀ : RigIso Y.m0.toSABMap w₀) (h₁ : RigIso Y.m w₁)
    (hs : s₀ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V)) {R : Type} [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c)
    (y₀ : FrPt Xo c R) (hj : j ≫ pullback.fst _ _ = y₀.x) (h : R)
    (hh : PrimeSpectrum.basicOpen h ≤ (j ≫ Y.j) ⁻¹ᵁ V) : ∃ (a : R) (n : ℕ),
    ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ : R →ₐ[c.F] T), IsUnit (ψ h) →
      ⊤ ≤ ((spMap ψ.toRingHom ≫ j) ≫ Y.j) ⁻¹ᵁ V ∧
      ∀ (y₁ y : FrPt Xo c T) G (s b : T), FrMap ψ y₀ y₁ → FrChg G s y₁ y →
        Cut Y V s₀ w₀ w₁ (spMap ψ.toRingHom ≫ j) y.x b y.s → ψ a = ψ h ^ n * (b * s) := by
  have hV : ∀ (T : Type) [CommRing T] (ψ : R →+* T), IsUnit (ψ h) → ⊤ ≤ ((spMap ψ ≫ j) ≫ Y.j) ⁻¹ᵁ V :=
    fun T _ ψ hu q _ => hh (x := spMap ψ q) fun hq => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)
  let π : R →ₐ[c.F] Localization.Away h := IsScalarTower.toAlgHom _ _ _
  obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ π y₀
  have hx' : (spMap π.toRingHom ≫ j) ≫ pullback.fst _ _ = y'.x := by rw [Category.assoc, hj, hy'.1]
  obtain ⟨q, hq, -⟩ := exists_cut_gen h₀ h₁ hs hx' (hV _ π.toRingHom (IsLocalization.Away.algebraMap_isUnit h)) y'.gen
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h q
  refine ⟨a, n, fun T _ _ ψ hu => ⟨hV T ψ.toRingHom hu, fun y₁ y G s b hm hc hb => ?_⟩⟩
  let ψ' : Localization.Away h →ₐ[c.F] T := IsLocalization.liftAlgHom (M := Submonoid.powers h) (f := ψ) (by
    rintro ⟨_, k, rfl⟩
    simpa using hu.pow k)
  have e : ∀ r, ψ' (algebraMap R _ r) = ψ r := fun r => by simp [ψ']
  have e' : ψ'.comp π = ψ := AlgHom.ext e
  have hm' : FrMap ψ' y' y₁ := FramedBaseChange.cancel π ψ' hy' (e' ▸ hm)
  have c₁ := Cut.pull ψ'.toRingHom (a := q) (b := 1) ((_root_.mul_one q).symm ▸ hq) (secBC_of_frMap hm')
  have ez : spMap ψ'.toRingHom ≫ spMap π.toRingHom ≫ j = spMap ψ.toRingHom ≫ j := by
    rw [← Category.assoc, ← FramedBaseChange.spec_comp, ← e']; rfl
  rw [ez] at c₁
  have c₂ := hb.chg hc.1 hc.2.2
  have hx₁ : (spMap ψ.toRingHom ≫ j) ≫ pullback.fst _ _ = y₁.x := by rw [Category.assoc, hj, hm.1]
  have := (exists_cut_gen h₀ h₁ hs hx₁ (hV T ψ.toRingHom hu) y₁.gen).unique c₁ c₂
  rw [← this, ← e a, ← ha, map_mul, map_pow, e, mul_comm]
  rfl

end GlobalTheory.GenRatio

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open GlobalTheory.GenRatio

theorem hasSum_generator_ratio : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (φ : p.R →ₐ[c.F] ℂ⸨X⸩) (y₁ : FrPt Xo c ℂ⸨X⸩) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → OpenChart j y₀ → FrMap φ y₀ y₁ → FrChg G s y₁ y → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ yw : FrPt Xo c (CAt σ)) (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ), (∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (toC (ψ f))) → FrMap ψ y₀ yw₁ → yw.x = Fu.u Ha.i (Ha.Pw w) → AnGen Fu Ha.i (Ha.Pw w) yw (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) Θ.κ → FrChg Gw sw yw₁ yw → HasSum (fun m : ℤ => (s).coeff m * eTwoPi w ^ m) (toC sw) := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ y e th Θ p j y₀ φ y₁ G s hal hχ hmono hPI hth harc hj
    hφ hchg
  by_cases hne : ∃ (w : ℂ) (ψ : p.R →ₐ[c.F] CAt σ),
      ∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (toC (ψ f))
  swap
  · exact ⟨0, fun w _ ψ _ _ _ _ h => (hne ⟨w, ψ, h⟩).elim⟩
  obtain ⟨v, ψ₀, hv⟩ := hne
  have conv : ∀ f, φ f ∈ Conv.convLaurent := fun f =>
    Conv.mem_convLaurent_of_summable (Conv.eTwoPi_ne_zero v) (hv f).summable
  obtain ⟨z, t', m1, m2, φG, zj, zx, φb, φ1, φ2, -, θ, w1, w2, σ', s1, θ2, ⟨σ0, fam, θ', hexp, hpull, hH0, hHEq⟩,
    r1, r2, i1, i2, ps, hc⟩ := harc
  obtain ⟨hA, hB⟩ := GlobalTheory.theta_generates_along_arc hL.globalFns hL.secBaseChange Y a χ W
  obtain ⟨σ1, -, -, -, -, huniq, -, -, ⟨w₂, hw₂⟩, hrest⟩ := hA (fam 0) ((hB th).2 (fam 0) hpull hth _)
  obtain rfl : σ0 = σ1 := huniq σ0 fam rfl hexp
  obtain ⟨⟨V, s₀, hV, hgen⟩, hr⟩ := (hrest w₂ hw₂.1).2 hPI
  obtain ⟨r, hr⟩ := hr V s₀ hV hgen
  obtain ⟨w₀, h₀⟩ := Reg.ChartInhab.exists_rigIso Y.m0.toSABMap
  obtain ⟨w₁, h₁⟩ := Reg.ChartInhab.exists_rigIso Y.m
  obtain ⟨u, ju, hu⟩ := exists_val_ne hth
  obtain ⟨z₀, rfl⟩ := Ha.onto u
  have hw0 : Ha.T < ((Ha.T + 1 : ℝ) * Complex.I : ℂ).im := by simp
  obtain ⟨fr₀, hfr₀⟩ := Θ.frame _ hw0
  obtain ⟨κ, -, -, onB, hmain⟩ := Ha.theta th σ0 fam Θ.bas Θ.S Θ.h Θ.τ Θ.c₁ Θ.c₂ w₂ w₁ w₀
    ⟨ju, fun h0 => hu (by
      rw [h0]
      by_cases h : ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ z₀).b.left) ⁻¹ᵁ a.D₀.P.L.U ju
      · exact (dif_pos h).trans ((congrArg _ (map_zero _)).trans (map_zero _))
      · exact dif_neg h)⟩
    hexp hpull Θ.sympl Θ.ker Θ.per Θ.half₁ Θ.half₂ hw₂ h₁ h₀ ⟨_, fr₀, hw0, hfr₀⟩
  obtain rfl : κ = Θ.κ := const_eq Ha.hol_b (onB _ hw0) (Θ.onB _ hw0) z₀ ju hu
  obtain ⟨T', hT'⟩ := hmain V s₀ r.val hV hgen.1 hr
  obtain ⟨w, hw, hθ⟩ := pullsToMul_gs W.m W.P.U.LG W.P.bundle w₂ hw₂ σ0 θ' θ hH0 hHEq r.val hr
  have cK := cut_arc hL.globalFns h₀ h₁ _ W.m θ r.val w hw hθ y.s m1 m2 φG zj zx φb φ1 φ2 w1 w2 σ' s1 θ2 r1 r2 i1 i2 ps hc
  have hz : z = spMap φ.toRingHom ≫ j := by
    apply pullback.hom_ext
    · rw [zx, Category.assoc, hj.2.1, hchg.1, hφ.1]
    · rw [← cancel_mono (spMap β), Category.assoc, Category.assoc, Category.assoc, reassoc_of% hj.2.2]
      have e₁ : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
        rw [Model.j, Category.assoc, pullback.condition, reassoc_of% Y.jQ_over]
      rw [← e₁, reassoc_of% zj, hχ, ← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp,
        ← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp]
      congr 1
      exact RingHom.ext fun x => (hal (β x)).symm.trans (φ.commutes (β x)).symm
  subst hz
  have hpt : spMap φ.toRingHom (IsLocalRing.closedPoint ℂ⸨X⸩) ∈ (j ≫ Y.j) ⁻¹ᵁ V :=
    (congrArg (fun q => q (IsLocalRing.closedPoint ℂ⸨X⸩) ∈ V) zj).mpr (hV (x := spMap _ _) trivial)
  obtain ⟨_, ⟨h, rfl⟩, hh, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 PrimeSpectrum.isBasis_basic_opens hpt
  have hh0 : φ h ≠ 0 := fun h0 => hh (show φ h ∈ IsLocalRing.maximalIdeal _ from h0 ▸ zero_mem _)
  obtain ⟨b, n, hb⟩ := exists_ratio hL.secBaseChange h₀ h₁ hgen.1 j y₀ hj.2.1 h hle
  have eK := (hb _ φ hh0.isUnit).2 y₁ y G s _ hφ hchg cK
  have hrc : (HahnSeries.ofPowerSeries ℤ ℂ r.val : ℂ⸨X⸩) ∈ Conv.convLaurent := by
    obtain ⟨x, hx, -⟩ := hT' ((T' + 1 : ℝ) * Complex.I) (by simp)
    exact Conv.mem_convLaurent_of_summable (Conv.eTwoPi_ne_zero _) (Conv.sumsAt_iff.1 hx).summable
  obtain ⟨T, hT⟩ := exists_hasSum_div n (conv b) (conv h) hrc hh0
    (r.isUnit.map (HahnSeries.ofPowerSeries ℤ ℂ)).ne_zero eK
  refine ⟨max T (max T' Ha.T), fun ω hω ψ yw₁ yw Gw sw hψ hm hx hgenw hcw => ?_⟩
  simp only [max_lt_iff] at hω
  obtain ⟨ρ, hρ, hval⟩ := hT' ω hω.2.1
  obtain ⟨hψh, hfin⟩ := hT ω hω.1 _ _ _ (hψ b) (hψ h) (Conv.sumsAt_iff.1 hρ)
  obtain ⟨hVw, hbw⟩ := hb _ ψ (IsUnit.mk0 (toC (ψ h)) hψh)
  have hxw : (spMap ψ.toRingHom ≫ j) ≫ pullback.fst _ _ = yw.x := by rw [Category.assoc, hj.2.1, hcw.1, hm.1]
  obtain ⟨a', ha', -⟩ := exists_cut_gen h₀ h₁ hgen.1 hxw hVw yw.gen
  obtain ⟨fr, hfr, hs⟩ := hgenw
  have hsn : (spMap ψ.toRingHom ≫ j) ≫ pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
    rw [Category.assoc, hj.2.2, ← FramedBaseChange.spec_comp]
    congr 1
    exact RingHom.ext fun x => ψ.commutes x
  have ea : toC a' = ρ := by
    refine cut_complex hL2.secTwist (z := spMap ψ.toRingHom ≫ j) (x := yw.x) hxw hVw yw.gen ha' ρ ?_
    intro pt f k₁ k k₀ a₁ a₂ a₃ a₄ a₅
    have ov : (f ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = Fu.u Ha.i (Ha.Pw ω) := by
      rw [Category.assoc, Y.m0.toSABMap.cart.1.w, reassoc_of% a₃]
      exact (Category.assoc _ _ _).symm.trans (hxw.trans hx)
    obtain ⟨ζ, hζ⟩ := Fu.ex_onto Ha.i _ (Ha.period ω hω.2.2) (Over.homMk _ ov)
    have hζ' : f ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw ω) ζ).left := (congrArg (fun q => q.left) hζ).symm
    have hU : ⊤ ≤ (Fu.ex Ha.i (Ha.Pw ω) ζ).left ⁻¹ᵁ Xo.univ.t.PP.L.U k₀ := by
      rw [← hζ']
      exact fun q hq => mem_pull.1 (a₅ hq).1
    refine (hval fr hfr ζ f k₁ k k₀ hζ' (by rw [reassoc_of% a₃]; exact hsn) a₄ a₅).trans (congrArg _ ?_)
    refine Eq.trans ?_ (congrArg (ρ * ·) (hs k₀ ζ pt (a₂.symm.trans hζ') a₁ hU)).symm
    ring
  refine hfin _ ?_
  rw [← ea]
  exact hbw yw₁ yw Gw sw a' hm hcw ha'

end GlobalTheory.ArcQ
