import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PointDataQ
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosIdSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteSublevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtGermCompare

theorem surjective_cube {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom := by
  have hG := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have s₂ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg G) s₁
  rw [Over.w (snd G G)] at s₂
  have s₃ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg (G ⊗ G)) s₂
  rw [Over.w (snd G (G ⊗ G))] at s₃
  exact s₃

theorem cubical_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  let e : 𝟙_ (Over S) ⟶ G3 G := lift 1 (lift 1 1)
  have h : c.t.s = c'.t.s := JetSer.gen_ext_val L.isLB (φ := thφ G (x3 G)) (ε := thε) c.isGen c'.isGen fun y J hJ =>
    gen_unique L.isLB (φ := thφ G (x3 G)) (ε := thε) (G3 G).hom e.left (Over.w e) sj c.isGen c'.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm) _ _ y J hJ
  obtain ⟨⟨t⟩, _⟩ := c
  obtain ⟨⟨t'⟩, _⟩ := c'
  obtain rfl : t = t' := h
  rfl

theorem cub_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) : HEq P.U.cubG t.cub := by
  have key : ∀ (L L' : RigLB t.G) (_ : L = L') (c : CubicalStr t.G L) (c' : CubicalStr t.G L'), HEq c c' := by
    rintro L _ rfl c c'
    exact heq_of_eq (cubical_unique (surjective_cube P.U.toUnifPre) c c')
  exact key _ _ P.bundle _ _

section Scale
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}

def constUnit (G : Over (Spec (CommRingCat.of R))) (c : Rˣ) : Γ(G.left, ⊤)ˣ :=
  Units.map (G.hom.appTop.hom : _ →* _) (unitOn c)

def constMul {M : LB G.left} (c : Rˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top (constUnit G c) * t.s j⟩

theorem constMul_isGen {M : LB G.left} (c : Rˣ) {t : LB.Gen M} (ht : t.IsGen) : (constMul c t).IsGen := by
  intro i j
  have e : ∀ {U W : G.left.Opens} (h : W ≤ U) (a : Γ(G.left, ⊤)ˣ), res h (res le_top a) = res le_top a :=
    fun h a => Units.ext (SecOps.resTop_res h a.val)
  simp only [constMul, map_mul, e]
  rw [ht i j, mul_left_comm]

end Scale

section Bound
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

end Bound

section Cast
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {L L' : RigLB G}

def castIdx (h : L = L') (j : L.L.ι) : L'.L.ι := Eq.rec (motive := fun M _ => M.L.ι) j h

def castGen (h : L = L') {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ G.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L.L φ ε)) : LB.Gen (LB.LinComb L'.L φ ε) :=
  Eq.rec (motive := fun M _ => LB.Gen (LB.LinComb M.L φ ε)) t h

theorem castIdx_castIdx (h : L = L') (h' : L' = L) (j : L.L.ι) : castIdx h' (castIdx h j) = j := by subst h; rfl

theorem castGen_castGen (h : L = L') (h' : L' = L) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ G.left)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L.L φ ε)) : castGen h' (castGen h t) = t := by subst h; rfl

theorem cast_unit (h : L = L') {j : L.L.ι} (hj : ⊤ ≤ η[G].left ⁻¹ᵁ L.L.U j) :
    ⊤ ≤ η[G].left ⁻¹ᵁ L'.L.U (castIdx h j) := by subst h; exact hj

theorem cast_isGen (h : L = L') {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ G.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L.L φ ε)} (ht : t.IsGen) : (castGen h t).IsGen := by subst h; exact ht

theorem cast_normRos (h : L = L') {f g : G ⟶ G} {u : LB.Gen (LB.LinComb L.L (rosatiφ G f g) rosatiε)}
    (hu : JetSer.IsNormRos L.L f g u) : JetSer.IsNormRos L'.L f g (castGen h u) := by subst h; exact hu

theorem cast_rig (h : L = L') {w : G ⟶ G} {ρ : LB.Gen (LB.LinComb L.L (JetSer.primφ w) JetSer.primε)}
    (hρ : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ ρ (eSec G)) L.rig) :
    LB.Gen.Corr L'.L _ _ _ _ (LB.pullGen L'.L _ _ (castGen h ρ) (eSec G)) L'.rig := by subst h; exact hρ

theorem cast_isFBOf (h : L = L') {c : CubicalStr G L} {c' : CubicalStr G L'} (hc : HEq c c') {O : Type} [CommRing O]
    [StarRing O] {act : OAct O G}
    {u : ∀ a : O, LB.Gen (LB.LinComb L.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)} {d : ℕ}
    {x : JetSer.Fam G (Fin d)} {j : L.L.ι} {B : FB R d O} (hB : JetSer.IsFBOf L c act u x j B) :
    JetSer.IsFBOf L' c' act (fun a => castGen h (u a)) x (castIdx h j) B := by
  subst h; cases hc; exact hB

end Cast

open GlobalTheory.FamGerm GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData

section Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [Algebra (FractionRing V) F]

def Rigid (y : Pt1 E H V F) : Prop :=
  LB.Gen.Corr y.P.U.LG.L _ _ _ _ (LB.pullGen y.P.U.LG.L _ _ y.ρ (eSec y.t.G)) y.P.U.LG.rig

def rescale (y : Pt1 E H V F) (c : Vˣ) : Pt1 E H V F :=
  { y with ρ := constMul c y.ρ, hρ := constMul_isGen c y.hρ }

variable [CharZero F]

def toPt {t : SAB H (Sp V)} {P : PELUnif (maximalIdeal V) t} (D : PtData P F) : Pt1 E H V F where
  ϖ := D.ϖ
  hϖ := D.irr
  complete := D.complete
  t := t
  P := P
  tors := D.tors
  Q := D.Q_vw
  hQ := D.isQ
  v := D.v_vw
  hv := D.valOver
  d := D.d
  x := D.x
  hx := D.chart
  j := castIdx P.bundle.symm D.j
  hj := cast_unit _ D.hj
  u := fun a => castGen P.bundle.symm (D.u a)
  hu := fun a => cast_normRos _ (D.u_norm a)
  B := D.B
  hB := letI := H.starRing; cast_isFBOf P.bundle.symm (cub_heq P).symm D.isFB
  ρ := castGen P.bundle.symm D.ρ
  hρ := cast_isGen _ D.ρ_gen

theorem rigid_toPt {t : SAB H (Sp V)} {P : PELUnif (maximalIdeal V) t} (D : PtData P F) : Rigid (toPt D) :=
  cast_rig P.bundle.symm D.ρ_rig

def ofPt (hF : IsAlgClosed F) (y : Pt1 E H V F) (hy : Rigid y) : PtData y.P F where
  complete := y.complete
  tors := y.tors
  ϖ := y.ϖ
  irr := y.hϖ
  Q_vw := y.Q
  isQ := y.hQ
  algClosed := hF
  v_vw := y.v
  valOver := y.hv
  d := y.d
  x := y.x
  chart := y.hx
  j := castIdx y.P.bundle y.j
  hj := cast_unit _ y.hj
  u := fun a => castGen y.P.bundle (y.u a)
  u_norm := fun a => cast_normRos _ (y.hu a)
  ρ := castGen y.P.bundle y.ρ
  ρ_gen := cast_isGen _ y.hρ
  ρ_rig := cast_rig y.P.bundle hy
  B := y.B
  isFB := letI := H.starRing; cast_isFBOf y.P.bundle (cub_heq y.P) y.hB

theorem ofPt_toPt (hF : IsAlgClosed F) {t : SAB H (Sp V)} {P : PELUnif (maximalIdeal V) t} (D : PtData P F) :
    ofPt hF (toPt D) (rigid_toPt D) = D := by
  cases D
  dsimp only [ofPt, toPt]
  congr 1
  exacts [castIdx_castIdx _ _ _, funext fun a => castGen_castGen _ _ _, castGen_castGen _ _ _]

theorem toPt_ofPt (hF : IsAlgClosed F) (y : Pt1 E H V F) (hy : Rigid y) : toPt (ofPt hF y hy) = y := by
  cases y
  simp only [ofPt, toPt, castIdx_castIdx, castGen_castGen]

def ptEquiv (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F]
    [Algebra (FractionRing V) F] [CharZero F] (hF : IsAlgClosed F) :
    (Σ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), PtData P F) ≃ {y : Pt1 E H V F // Rigid y} where
  toFun X := ⟨toPt X.2.2, rigid_toPt _⟩
  invFun y := ⟨y.1.t, y.1.P, ofPt hF y.1 y.2⟩
  left_inv X := congrArg (fun D => (⟨X.1, X.2.1, D⟩ : Σ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), PtData P F))
    (ofPt_toPt hF X.2.2)
  right_inv y := Subtype.ext (toPt_ofPt hF y.1 y.2)

end Data

section Statements

def GermValMinSt_vw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F] (D : PtData P F) (q : ℕ), 1 ≤ q →
    ∀ (s : Fam P.D.toPre F q) (f : PS F 1 D.d), D.IsGerm q s f → ∀ r : ℚ,
      ((∀ χ, VGe P.D F D.v_vw q χ (s.s χ) r) →
        ∀ a, ((r : ℚ) : WithTop ℚ) ≤ D.v_vw (MvPowerSeries.coeff a f)) ∧
      ∀ (χ₀ : P.D.toPre.X) (y : F), Val0 P.D F q χ₀ (s.s χ₀) y →
        (∀ χ, χ ≠ χ₀ → ∃ r' : ℚ, r < r' ∧ VGe P.D F D.v_vw q χ (s.s χ) r') →
          D.v_vw y = ((r : ℚ) : WithTop ℚ) → D.v_vw (MvPowerSeries.constantCoeff f) = ((r : ℚ) : WithTop ℚ)

def GermCongrSt_vw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F] (D : PtData P F) (q : ℕ), 1 ≤ q →
    ∀ (s : Fam P.D.toPre F q) (f : PS F 1 D.d), D.IsGerm q s f → ∀ r : ℚ,
      ∀ (χ₀ : P.D.toPre.X) (y : F), Val0 P.D F q χ₀ (s.s χ₀) y →
        (∀ χ, χ ≠ χ₀ → ∃ r' : ℚ, r < r' ∧ VGe P.D F D.v_vw q χ (s.s χ) r') →
        ((r : ℚ) : WithTop ℚ) < D.v_vw (MvPowerSeries.constantCoeff f - y)

def PtExCharZeroSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (F : Type) [Field F]
    [Algebra (FractionRing V) F] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ v : AddValuation F (WithTop ℚ), ValOver ϖ F v →
    ∃ y : Pt1 E H V F, y.t = t ∧ HEq y.P P ∧ y.v = v ∧ y.ϖ = ϖ

end Statements

end GlobalTheory.PtGermCompare
