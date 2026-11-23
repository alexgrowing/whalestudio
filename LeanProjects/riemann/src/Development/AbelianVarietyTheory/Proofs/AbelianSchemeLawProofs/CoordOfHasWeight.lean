import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackPullbackMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section

namespace GlobalTheory

namespace GtBaseChange

section Chart

variable {Y Y' Z : Scheme.{0}}

def genPull {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (t : LB.Gen A) : LB.Gen A' :=
  ⟨fun i => res (a.le i) (pullU h _ (t.s (a.idx i)))⟩

theorem gm_res_pullU (r : Z ⟶ Y') (h : Y' ⟶ Y) (z : Z) {U : Y.Opens} {V : Y'.Opens} (le : V ≤ h ⁻¹ᵁ U)
    (hz : r z ∈ V) (a : Γ(Y, U)ˣ) : gm r z V (res le (pullU h U a)) = gm (r ≫ h) z U a :=
  (gm_res r z le hz _).trans (gm_pull r h z U (le hz) a)

theorem gm_res_pullU' (h : Y' ⟶ Y) (z : Y') {U : Y.Opens} {V : Y'.Opens} (le : V ≤ h ⁻¹ᵁ U)
    (hz : z ∈ V) (a : Γ(Y, U)ˣ) : gm (𝟙 Y') z V (res le (pullU h U a)) = gm h z U a :=
  (gm_res_pullU (𝟙 Y') h z le hz a).trans (by rw [Category.id_comp])

theorem genPull_isGen {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) {t : LB.Gen A}
    (ht : t.IsGen) : (genPull a t).IsGen := fun p q => unit_ext fun y hy => by
  have hm : h y ∈ A.U (a.idx p) ⊓ A.U (a.idx q) := ⟨a.le _ hy.1, a.le _ hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx p) ⊓ A.U (a.idx q))) (ht (a.idx p) (a.idx q))
  rw [map_mul, gm_res h y _ hm, gm_res h y _ hm] at e
  rw [map_mul, gm_res (𝟙 Y') y _ hy, gm_res (𝟙 Y') y _ hy, a.g y p q hy.1 hy.2]
  exact (gm_res_pullU' h y (a.le p) hy.1 _).trans
    (e.trans (congrArg _ (gm_res_pullU' h y (a.le q) hy.2 _).symm))

def chartPullDiv {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (b : ChartPull B' B h) (a : ChartPull A' A h) :
    ChartPull (LB.div B' A') (LB.div B A) h where
  idx p := (b.idx p.1, a.idx p.2)
  le p y hy := ⟨b.le _ hy.1, a.le _ hy.2⟩
  g y p q hp hq := by
    refine (gm_div A' B' (𝟙 Y') y p q ⟨hp, hq⟩).trans (Eq.trans ?_
      (gm_div A B h y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2)
        ⟨⟨b.le _ hp.1, a.le _ hp.2⟩, b.le _ hq.1, a.le _ hq.2⟩).symm)
    rw [a.g y _ _ hp.2 hq.2, b.g y _ _ hp.1 hq.1]

theorem lbIso_refl {A : LB Y} (hA : A.IsLB) : LBIso A A := by
  refine ⟨⟨fun p => A.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res (𝟙 Y) y _ hy _).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A A (𝟙 Y) y p q hy) (gm_res (𝟙 Y) y _ hy _))).trans ?_
  have e := (gm_cocycle hA (𝟙 Y) y hy.1.1 hy.2.1 hy.2.2).trans (gm_cocycle hA (𝟙 Y) y hy.1.1 hy.1.2 hy.2.2).symm
  exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul e)

end Chart

section Ext

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem eSec_fst (G : Over S) [GrpObj G] :
    eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f =
      (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) ≫ eSec G := by
  have h := isGrpPullback_pullback G f
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G) = η[(Over.pullback f).obj G] := by
    rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

def rigChart (B : Over S) [GrpObj B] (L : LB B.left) :
    ChartPull ((L.pull (pullback.fst B.hom f)).pull (eSec ((Over.pullback f).obj B))) (L.pull (eSec B))
      (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) :=
  chartPullLinComb L _ _ _ _ _ fun _ => eSec_fst f B

def rigBC (B : Over S) [GrpObj B] (L : RigLB B) : RigLB ((Over.pullback f).obj B) where
  L := L.L.pull (pullback.fst B.hom f)
  rig := genPull (rigChart f B L.L) L.rig
  isLB := pull_isLB L.isLB _
  rigGen := genPull_isGen _ L.rigGen

theorem exists_lamChart (B : Over S) [GrpObj B] [IsCommMonObj B] (L : LB B.left) :
    ∃ U, Nonempty (ChartPull (abelian₂ ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f))) (abelian₂ B L) U) := by
  have : IsCommMonObj ((Over.pullback f).obj B) := Functor.isCommMonObj_obj
  have h := isGrpPullback_pullback B f
  let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj B) ((Over.pullback f).obj B)))
    (pushPt h.1.w (snd ((Over.pullback f).obj B) ((Over.pullback f).obj B)))
  refine ⟨U.left, ⟨chartPullLinComb L _ _ _ _ U.left
    fun I => psum_push h (x2 _) (x2 B) U (fun i => ?_) I.down⟩⟩
  fin_cases i <;> simp [U, x2]

def extBC (E : SplitExt S) : SplitExt S' where
  B := (Over.pullback f).obj E.B
  isAbelian := Out.TLinPf.isAb_pullback f E.B E.isAbelian
  X := E.X
  O χ := rigBC f E.B (E.O χ)
  addIso χ χ' := LBIso.chartPull (chartPullPull _ _ _ rfl)
    (chartPullDiv (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl)) (E.addIso χ χ')
  zeroTriv := by
    obtain ⟨t, ht⟩ := E.zeroTriv
    exact ⟨_, genPull_isGen (chartPullPull _ _ _ rfl) ht⟩
  primitive χ := by
    obtain ⟨t, ht⟩ := E.primitive χ
    have := E.isAbelian.comm
    obtain ⟨U, ⟨a⟩⟩ := exists_lamChart f E.B (E.O χ).L
    exact ⟨_, genPull_isGen a ht⟩

end Ext

section Weight

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]

def HasWeight (i : splitTorus S X ⟶ G) (U : G.left.Opens) (u : Γ(G.left, U)ˣ) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ U →
    gm ((t ≫ i) * g).left z U u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z U u

theorem translate_comp (q : G ⟶ B) (i : splitTorus S X ⟶ G) [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ i) * g) ≫ q = g ≫ q := by
  have hiq : (t ≫ i) ≫ q = 1 := by
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  rw [MonObj.mul_comp, hiq, _root_.one_mul]

theorem translate_mem (q : G ⟶ B) (i : splitTorus S X ⟶ G) [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
    (W : B.left.Opens) (z : Z.left) (hz : g.left z ∈ q.left ⁻¹ᵁ W) :
    ((t ≫ i) * g).left z ∈ q.left ⁻¹ᵁ W := by
  change (((t ≫ i) * g) ≫ q).left z ∈ W
  rw [translate_comp q i hk]
  exact hz

theorem hasWeight_iff (i : splitTorus S X ⟶ G) (U : G.left.Opens) (u : Γ(G.left, U)ˣ) (χ : X)
    (hle : (snd (splitTorus S X) G).left ⁻¹ᵁ U ≤
      (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left ⁻¹ᵁ U)
    (hT : (snd (splitTorus S X) G).left ⁻¹ᵁ U ≤ (fst (splitTorus S X) G).left ⁻¹ᵁ ⊤) :
    HasWeight i U u χ ↔
      res hle (pullU (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left _ u) =
        res hT (pullU (fst (splitTorus S X) G).left ⊤ (charUnit S X χ)) *
        pullU (snd (splitTorus S X) G).left _ u := by
  constructor
  · intro h
    refine unit_ext fun y hy => ?_
    rw [map_mul, gm_res_pullU' _ y hle hy, gm_res_pullU' _ y _ hy, gm_pull (𝟙 _) _ y U hy, Category.id_comp]
    exact h _ _ _ y hy
  · intro h Z t g z hz
    have e₁ : (lift t g).left ≫ (fst (splitTorus S X) G).left = t.left := by
      rw [← Over.comp_left, lift_fst]
    have e₂ : (lift t g).left ≫ (snd (splitTorus S X) G).left = g.left := by
      rw [← Over.comp_left, lift_snd]
    have e₃ : (lift t g).left ≫ (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left =
        ((t ≫ i) * g).left := by
      rw [← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, Hom.mul_def]
    have hm : (lift t g).left z ∈ (snd (splitTorus S X) G).left ⁻¹ᵁ U := by
      change ((lift t g).left ≫ (snd (splitTorus S X) G).left) z ∈ U
      rw [e₂]; exact hz
    have e := congrArg (gm (lift t g).left z _) h
    rwa [map_mul, gm_res_pullU _ _ z hle hm, gm_res_pullU _ _ z _ hm, gm_pull _ _ z U hm, e₁, e₂, e₃] at e

theorem coord_of_hasWeight {K : Type} (b : Module.Basis K ℤ X) (q : G ⟶ B) (i : splitTorus S X ⟶ G)
    [hq : IsMonHom q] [hi : IsMonHom i] (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q η[B]) (W : B.left.Opens) (u : K → Γ(G.left, q.left ⁻¹ᵁ W)ˣ)
    (hu : ∀ k, HasWeight i _ (u k) (b k)) (V : B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ W) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
        ((Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
          (b.constr ℤ (fun k => Additive.ofMul
            (res (Scheme.Hom.preimage_mono q.left h) (u k)))).toAddMonoidHom))
        (fun _ _ => Commute.all _ _)) := by
  refine (isAffineOpen_and_bijective_of_weight_units S X G B q i hq hi hf hs inferInstance hk V hV _ ?_).2
  intro χ Z t g h₁ h₂
  set v := AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun k => Additive.ofMul (res (Scheme.Hom.preimage_mono q.left h) (u k)))).toAddMonoidHom with hv
  let A : Multiplicative X →* Γ(Z.left, ⊤)ˣ := ((res h₁).comp (pullU ((t ≫ i) * g).left _)).comp v
  let C : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
    splitTorusPointsEquiv S X Z t * ((res h₂).comp (pullU g.left _)).comp v
  have hAC : (MonoidHom.toAdditiveRight A).toIntLinearMap = (MonoidHom.toAdditiveRight C).toIntLinearMap := by
    refine b.ext fun k => ?_
    have hvk : v (Multiplicative.ofAdd (b k)) = res (Scheme.Hom.preimage_mono q.left h) (u k) := by
      simp [hv]
    have hT : (⊤ : Z.left.Opens) ≤ t.left ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have hc : splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) =
        res hT (pullU t.left ⊤ (charUnit S X (b k))) := by
      refine Units.ext ((splitTorusPointsEquiv_val S X Z t (b k)).trans ?_)
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    refine congrArg Additive.ofMul ?_
    change res h₁ (pullU _ _ (v (Multiplicative.ofAdd (b k)))) =
      splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd (b k)) *
        res h₂ (pullU _ _ (v (Multiplicative.ofAdd (b k))))
    rw [hvk, hc]
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res_pullU' _ z h₁ hz, gm_res_pullU' _ z h₂ hz, gm_res ((t ≫ i) * g).left z _ (h₁ hz),
      gm_res g.left z _ (h₂ hz),
      hu k Z t g z (h (h₂ hz)), gm_res_pullU' _ z hT hz]
  have := congrArg (fun φ => (Additive.toMul (φ χ)).val) hAC
  rw [← splitTorusPointsEquiv_val]
  exact this

end Weight

section Datum

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem HasWeight.baseChange {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G}
    {U : G.left.Opens} {u : Γ(G.left, U)ˣ} {χ : X} (hu : HasWeight i U u χ)
    (i' : splitTorus S' X ⟶ (Over.pullback f).obj G) (τ : (splitTorus S' X).left ⟶ (splitTorus S X).left)
    (hτ : τ ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f)
    (hi : i'.left ≫ pullback.fst G.hom f = τ ≫ i.left)
    (hc : τ.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val)
    {U' : ((Over.pullback f).obj G).left.Opens} (le : U' ≤ pullback.fst G.hom f ⁻¹ᵁ U)
    (hU' : ∀ (Z : Over S') (t : Z ⟶ splitTorus S' X) (g : Z ⟶ (Over.pullback f).obj G) (z : Z.left),
      g.left z ∈ U' → ((t ≫ i') * g).left z ∈ U') :
    HasWeight i' U' (res le (pullU (pullback.fst G.hom f) U u)) χ := by
  intro Z t g z hz
  have h := isGrpPullback_pullback G f
  have e := hu _ (pushPt hτ t) (pushPt h.1.w g) z (le hz)
  have e₁ := h.2 Z (t ≫ i') g (pushPt hτ t ≫ i) (pushPt h.1.w g) (by
    change (t.left ≫ τ) ≫ i.left = (t.left ≫ i'.left) ≫ _
    rw [Category.assoc, Category.assoc, hi]) rfl
  rw [e₁] at e
  have e₂ : charUnit S' X χ = pullU τ ⊤ (charUnit S X χ) := Units.ext hc.symm
  refine (gm_res_pullU _ _ z le (hU' Z t g z hz) u).trans (e.trans (congrArg₂ (· * ·) ?_
    (gm_res_pullU _ _ z le hz u).symm))
  rw [e₂]
  exact (gm_pull t.left τ z ⊤ trivial _).symm

theorem chart_le_preimage (E : SplitExt S) (j : (extBC f E).ChartIdx) :
    (extBC f E).chart j ≤ pullback.fst E.B.hom f ⁻¹ᵁ E.chart (fun k => j k PUnit.unit) := by
  intro y hy
  change pullback.fst E.B.hom f y ∈
    ((⨅ k, (E.O (E.basis k)).L.U (j k PUnit.unit) : E.B.left.Opens) : Set E.B.left)
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact fun k => mem_pull.1 ((extBC f E).chart_le j k hy)

theorem isGt_extBC (E : SplitExt S) (G : Over S) [GrpObj G] (d : E.GtDatum G) :
    (extBC f E).IsGt ((Over.pullback f).obj G) := by
  have := d.q_hom
  have := d.i_hom
  have : IsMonHom (Iso.refl ((Over.pullback f).obj G)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have : IsMonHom (Iso.refl ((Over.pullback f).obj E.B)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨eT, mT, hT⟩ := splitTorus_baseChange S S' f E.X
  obtain ⟨q, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := TorusExtBaseChange.exists_extension f eT
    (Iso.refl ((Over.pullback f).obj G)) (Iso.refl ((Over.pullback f).obj E.B)) d.i d.q d.q_flat d.q_surjective
    d.q_affine d.isKernel
  have hq : q.left ≫ pullback.fst E.B.hom f = pullback.fst G.hom f ≫ d.q.left := by simpa using h7
  have hi : i.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst _ f) ≫ d.i.left := by simpa using h8
  have le : ∀ j : (extBC f E).ChartIdx, q.left ⁻¹ᵁ (extBC f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) := fun j y hy => by
    change (pullback.fst G.hom f ≫ d.q.left) y ∈ E.chart (fun k => j k PUnit.unit)
    rw [← hq]
    exact chart_le_preimage f E j hy
  let u : ∀ (j : (extBC f E).ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X),
      Γ(((Over.pullback f).obj G).left, q.left ⁻¹ᵁ (extBC f E).chart j)ˣ := fun j k =>
    res (le j) (pullU (pullback.fst G.hom f) _ (d.u (fun k => j k PUnit.unit) k))
  have hw : ∀ j k, HasWeight i _ (u j k) (E.basis k) := fun j k =>
    HasWeight.baseChange f ((hasWeight_iff d.i _ _ _ (d.act_le _) _).2 (d.equiv _ k)) i _ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)) hi (hT _) (le j)
      fun Z t g z hz => translate_mem q i h6 t g _ z hz
  refine ⟨
    { q := q
      i := i
      q_hom := h1
      i_hom := h5
      q_flat := h2
      q_surjective := h3
      q_affine := h4
      isKernel := h6
      u := u
      coord := fun j V hV h => coord_of_hasWeight E.basis q i h2 h3 h4 h6 _ (u j) (hw j) V hV h
      trans := fun j j' k => unit_ext fun y hy => ?_
      act_le := fun j y hy => translate_mem q i h6 (fst _ _) (snd _ _) ((extBC f E).chart j) y hy
      equiv := fun j k => (hasWeight_iff i _ _ _ _ _).1 (hw j k)
      unit_norm := fun j k => unit_ext fun y hy => ?_ }⟩
  · have hm : pullback.fst G.hom f y ∈ d.q.left ⁻¹ᵁ
        (E.chart (fun k => j k PUnit.unit) ⊓ E.chart (fun k => j' k PUnit.unit)) := ⟨le j hy.1, le j' hy.2⟩
    have e := congrArg (gm (pullback.fst G.hom f) y _)
      (d.trans (fun k => j k PUnit.unit) (fun k => j' k PUnit.unit) k)
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_pull _ d.q.left y _ hm _).trans (gm_res (pullback.fst G.hom f ≫ d.q.left) y _ hm _))
      (gm_res _ y _ hm _))))
    refine ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j') hy.2 _)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j) hy.1 _)))
    refine ((gm_pull (𝟙 _) q.left y _ hy _).trans (gm_res (𝟙 _ ≫ q.left) y _ hy _)).trans ?_
    refine (gm_pull_g (E.O (E.basis k)).L (pullback.fst E.B.hom f) (𝟙 _ ≫ q.left) y (j k) (j' k)
      ((extBC f E).chart_le j k hy.1) ((extBC f E).chart_le j' k hy.2)).trans ?_
    rw [Category.id_comp, hq]
  · have hs := eSec_fst f G
    have h₁ : (eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f) y ∈
        d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit) := le j hy.1
    rw [hs] at h₁
    have h₂ := (rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k) hy.2
    let f' : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left := f
    have hm : f' y ∈ eSec G ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) ⊓
        ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k PUnit.unit) := ⟨h₁, h₂⟩
    have e := congrArg (gm f' y _) (d.unit_norm (fun k => j k PUnit.unit) k)
    have e' := ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res_pullU f' _ y _ hm _) (gm_res f' y _ hm _))).symm.trans (e.trans (map_one _))
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)).trans (e'.trans (map_one _).symm)
    · refine (gm_res_pullU' _ y _ hy _).trans ((gm_res_pullU _ _ y (le j) hy.1 _).trans ?_)
      rw [hs]
    · exact (gm_res (𝟙 _) y _ hy _).trans
        (gm_res_pullU' f' y ((rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k)) hy.2 _)

end Datum

end GtBaseChange

open GtBaseChange in

theorem gtBaseChange : GtBaseChangeSt := by
  rintro S S' f E G _ ⟨d⟩
  refine ⟨extBC f E, AddEquiv.refl _, Iso.refl _, inferInstanceAs (IsMonHom (𝟙 _)), fun χ => ?_,
    isGt_extBC f E G d⟩
  exact LBIso.chartPull (chartPullPull (E.O χ).L _ _ (Category.id_comp _).symm) (chartPullPull _ _ _ rfl)
    (lbIso_refl (E.O χ).isLB)

end GlobalTheory
