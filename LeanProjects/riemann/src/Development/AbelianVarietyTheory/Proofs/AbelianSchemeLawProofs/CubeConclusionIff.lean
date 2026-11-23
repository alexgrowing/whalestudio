import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.CubicalPullbackLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext exists_chart gm_cocycle gm_self)

namespace GlobalTheory.GtCubeCompare

section General

variable {X Y Z : Scheme.{0}}

theorem isGen_of_maps {A B : LB X} (hA : A.IsLB) {w : LB.Iso A B} (hw : w.IsGen) {a : LB.Gen A}
    {b : LB.Gen B} (h : LB.Gen.Maps w a b) : b.IsGen := by
  intro i j
  apply Pdiv.PullbackComparison.unit_ext
  intro x hx
  obtain ⟨q, hq⟩ := exists_chart hA x
  have e1 := congrArg (Pdiv.PullbackComparison.gU x (⟨hx.1, hq⟩ : x ∈ B.U i ⊓ A.U q)) (h (i, q))
  have e2 := congrArg (Pdiv.PullbackComparison.gU x (⟨hx.2, hq⟩ : x ∈ B.U j ⊓ A.U q)) (h (j, q))
  have e3 := Transport.gU_iso w hw i j q q x ⟨hq, hx.1⟩ ⟨hq, hx.2⟩
  simp only [id] at e1 e2
  erw [map_mul, Pdiv.PullbackComparison.gU_res, Pdiv.PullbackComparison.gU_res] at e1 e2
  erw [Transport.gU_self hA x hq] at e3
  erw [map_mul, Pdiv.PullbackComparison.gU_res, Pdiv.PullbackComparison.gU_res, e1, e2, e3]
  simp only [inv_one, _root_.mul_one]
  exact _root_.mul_assoc _ _ _

def idIso (L : LB X) : LB.Iso L L := ⟨fun p => L.g p.1 p.2⟩

theorem idIso_isGen {L : LB X} (hL : L.IsLB) : (idIso L).IsGen := by
  rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  apply Pdiv.PullbackComparison.unit_ext
  intro x hx
  have h11 : x ∈ L.U p₁ := hx.1.1
  have h12 : x ∈ L.U p₂ := hx.1.2
  have h21 : x ∈ L.U q₁ := hx.2.1
  have h22 : x ∈ L.U q₂ := hx.2.2
  rw [map_mul, Pdiv.PullbackComparison.gU_res, Pdiv.PullbackComparison.gU_res]
  erw [Transport.gU_div L L (p₁, p₂) (q₁, q₂) x hx.1 hx.2]
  have c1 := Transport.gU_cocycle hL x h11 h21 h22
  have c2 := Transport.gU_cocycle hL x h11 h12 h22
  show Pdiv.PullbackComparison.gU x (⟨h11, h12⟩ : x ∈ L.U p₁ ⊓ L.U p₂) (L.g p₁ p₂) =
    Pdiv.PullbackComparison.gU x (⟨h11, h21⟩ : x ∈ L.U p₁ ⊓ L.U q₁) (L.g p₁ q₁) *
      (Pdiv.PullbackComparison.gU x (⟨h12, h22⟩ : x ∈ L.U p₂ ⊓ L.U q₂) (L.g p₂ q₂))⁻¹ *
      Pdiv.PullbackComparison.gU x (⟨h21, h22⟩ : x ∈ L.U q₁ ⊓ L.U q₂) (L.g q₁ q₂)
  rw [eq_mul_inv_of_mul_eq c2, ← c1, mul_right_comm]

variable {A B : LB X}

def gw (w : LB.Iso A B) (f : Y ⟶ X) (y : Y) (p : B.ι) (q : A.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y (B.U p ⊓ A.U q) (w.s (p, q))

theorem gm_linCombIso (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : K → B.ι) (q : K → A.ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ LB.wchart B φ p ⊓ LB.wchart A φ q) :
    gm r z (LB.wchart B φ p ⊓ LB.wchart A φ q) ((LB.linCombIso w φ ε).s (p, q)) =
      ∏ a, gw w (r ≫ φ a) z (p a) (q a) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ B.U (p a) ⊓ A.U (q a) :=
    ⟨LB.wchart_le B φ p a hz.1, LB.wchart_le A φ q a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z (B.U (p a) ⊓ A.U (q a)) hm _)

def PM (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb A φ ε)) (b : LB.Gen (LB.LinComb B φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → B.ι) (q : K → A.ι),
    r z ∈ LB.wchart B φ p → r z ∈ LB.wchart A φ q →
    gm r z (LB.wchart B φ p) (b.s p) =
      (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart A φ q) (a.s q)

theorem maps_iff_pm (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb A φ ε)) (b : LB.Gen (LB.LinComb B φ ε)) :
    LB.Gen.Maps (LB.linCombIso w φ ε) a b ↔ PM w φ ε a b := by
  constructor
  · intro H Z r z p q hp hq
    have hm : r z ∈ LB.wchart B φ p ⊓ LB.wchart A φ q := ⟨hp, hq⟩
    have := congrArg (gm r z (LB.wchart B φ p ⊓ LB.wchart A φ q)) (H (p, q))
    rw [← gm_linCombIso w φ ε p q r z hm]
    exact (gm_res r z _ hm _).symm.trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res r z _ hm _))))
  · rintro H ⟨p, q⟩
    apply unit_ext
    intro x hx
    have := H _ (𝟙 Y) x p q hx.1 hx.2
    rw [← gm_linCombIso w φ ε p q (𝟙 Y) x hx] at this
    exact (gm_res _ x _ hx _).trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

variable {w : LB.Iso A B} {K K' : Type} [Fintype K] [Fintype K']

theorem PM.pullGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb A φ ε)}
    {b : LB.Gen (LB.LinComb B φ ε)} (H : PM w φ ε a b) (h : Z ⟶ Y) :
    PM w (fun k => h ≫ φ k) ε (LB.pullGen A φ ε a h) (LB.pullGen B φ ε b h) := by
  intro T r z p q hp hq
  have hp' : h (r z) ∈ LB.wchart B φ p := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hp k
  have hq' : h (r z) ∈ LB.wchart A φ q := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hq k
  have e := H T (r ≫ h) z p q hp' hq'
  simp only [Category.assoc] at e
  refine ((gm_res r z _ hp _).trans (gm_pull r h z _ hp' _)).trans (e.trans (congrArg _ ?_))
  exact ((gm_res r z _ hq _).trans (gm_pull r h z _ hq' _)).symm

theorem PM.mulGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb A φ ε)}
    {b : LB.Gen (LB.LinComb B φ ε)} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {a' : LB.Gen (LB.LinComb A φ' ε')} {b' : LB.Gen (LB.LinComb B φ' ε')} (H : PM w φ ε a b)
    (H' : PM w φ' ε' a' b') :
    PM w (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen A φ ε φ' ε' a a')
      (LB.mulGen B φ ε φ' ε' b b') := by
  intro T r z p q hp hq
  have e := H T r z (p ∘ Sum.inl) (q ∘ Sum.inl)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hp (Sum.inl k))
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hq (Sum.inl k))
  have e' := H' T r z (p ∘ Sum.inr) (q ∘ Sum.inr)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hp (Sum.inr k))
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hq (Sum.inr k))
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hp _).trans e)
    ((gm_res r z _ hp _).trans e'))).trans ?_
  rw [Fintype.prod_sum_type, _root_.mul_mul_mul_comm]
  exact congrArg _ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_res r z _ hq _) (gm_res r z _ hq _))).symm

theorem PM.oneGen (w : LB.Iso A B) :
    PM (Y := Y) w (K := PEmpty) PEmpty.elim PEmpty.elim (LB.oneGen A) (LB.oneGen B) := by
  intro T r z p q _ _
  refine (map_one _).trans ?_
  rw [Fintype.prod_empty, _root_.one_mul]
  exact (map_one _).symm

theorem corr_of_pm (hA : A.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb A φ ε)}
    {b : LB.Gen (LB.LinComb B φ ε)} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {a' : LB.Gen (LB.LinComb A φ' ε')} {b' : LB.Gen (LB.LinComb B φ' ε')} (H : PM w φ ε a b)
    (H' : PM w φ' ε' a' b') (hS : LB.SameSum φ ε φ' ε') (hc : LB.Gen.Corr A φ ε φ' ε' a a') :
    LB.Gen.Corr B φ ε φ' ε' b b' := by
  classical
  intro j j' cj cj' cjj
  apply unit_ext
  intro y hy
  obtain ⟨idx, hidx⟩ := Out.TLinPf.idx_exists A hA y
  have m : y ∈ LB.wchart A φ (fun k => idx (φ k)) := Set.mem_iInter.2 fun k => hidx _
  have m' : y ∈ LB.wchart A φ' (fun k => idx (φ' k)) := Set.mem_iInter.2 fun k => hidx _
  have e := H Y (𝟙 Y) y j _ hy.1 m
  have e' := H' Y (𝟙 Y) y j' _ hy.2 m'
  refine (gm_res _ y _ hy _).trans (e.trans (Eq.trans ?_ ((gm_res _ y _ hy _).trans e').symm))
  have hmm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart A φ (fun k => idx (φ k)) ⊓
    LB.wchart A φ' (fun k => idx (φ' k)) := ⟨m, m'⟩
  have hmid := congrArg (gm (𝟙 Y) y _) (hc (fun k => idx (φ k)) (fun k => idx (φ' k))
    (fun _ _ e => congrArg idx e) (fun _ _ e => congrArg idx e) (fun _ _ e => congrArg idx e))
  refine congrArg₂ (· * ·) ?_
    ((gm_res _ y _ hmm _).symm.trans (hmid.trans (gm_res _ y _ hmm _)))
  let F : (Y ⟶ X) → (Y.presheaf.stalk y)ˣ := fun ζ =>
    if hz : ∃ k, φ k = ζ then gw w ζ y (j hz.choose) (idx ζ)
    else if hz' : ∃ k', φ' k' = ζ then gw w ζ y (j' hz'.choose) (idx ζ) else 1
  have hF : ∀ k, gw w (𝟙 Y ≫ φ k) y (j k) (idx (φ k)) = F (φ k) := by
    intro k
    have hz : ∃ k', φ k' = φ k := ⟨k, rfl⟩
    show _ = (if hz : ∃ k', φ k' = φ k then _ else _)
    rw [dif_pos hz, cj _ _ hz.choose_spec, Category.id_comp]
  have hF' : ∀ k, gw w (𝟙 Y ≫ φ' k) y (j' k) (idx (φ' k)) = F (φ' k) := by
    intro k
    show _ = (if hz : ∃ k', φ k' = φ' k then _ else if hz' : ∃ k', φ' k' = φ' k then _ else _)
    by_cases hz : ∃ k', φ k' = φ' k
    · rw [dif_pos hz, cjj _ _ hz.choose_spec, Category.id_comp]
    · have hz' : ∃ k', φ' k' = φ' k := ⟨k, rfl⟩
      rw [dif_neg hz, dif_pos hz', cj' _ _ hz'.choose_spec, Category.id_comp]
  simp only [hF, hF']
  exact Out.Canon.prod_sameSum φ ε φ' ε' hS F

end General

section Group

open GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw

def transportCubical {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L M : RigLB G}
    (w : LB.Iso L.L M.L) (hw : w.IsGen) (c : CubicalStr G L) (t : LB.Gen (Theta G M.L))
    (h : LB.Gen.Maps (LB.linCombIso w (thφ G (x3 G)) thε) c.t t) : CubicalStr G M :=
  have H : PM w (thφ G (x3 G)) thε c.t t := (maps_iff_pm w _ _ _ _).1 h
  { t := t
    isGen := isGen_of_maps (LB.isLB_linComb L.isLB (thφ G (x3 G)) thε)
      (DVR.linCombIso_isGen w hw _ _) h
    face := fun i => corr_of_pm L.isLB (H.pullGen _) (PM.oneGen w)
      (Out.CubePf.face_sameSum G i) (c.face i)
    cubeSymmetric_swap_first := corr_of_pm L.isLB H (H.pullGen _) (Out.CubePf.swap_first_two_same_sum G) c.cubeSymmetric_swap_first
    cubeSymmetric_swap_last := corr_of_pm L.isLB H (H.pullGen _) (Out.CubePf.swap_last_two_same_sum G) c.cubeSymmetric_swap_last
    cocycle := corr_of_pm L.isLB ((H.pullGen _).mulGen (H.pullGen _))
      ((H.pullGen _).mulGen (H.pullGen _)) (Out.CubePf.cocycle_sameSum G) c.cocycle }

theorem idIso_maps {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    LB.Gen.Maps (LB.linCombIso (idIso L) φ ε) t t := fun p => ht p.1 p.2

variable {S S' : Scheme.{0}}

theorem cubical_clause_iff {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L)
    (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen) :
    (∃ c' : CubicalStr G' (m.rigLB L hL hr), m.IsPullCubical c' c) ↔
      ∃ c' : CubicalStr G' (m.rigLB L hL hr),
        c'.t = m.thetaPull L.L c.t ∧ m.IsPullCubical c' c := by
  refine ⟨fun ⟨c', w, hw, _, ht⟩ => ?_, fun ⟨c', _, h⟩ => ⟨c', h⟩⟩
  let c'' : CubicalStr G' (m.rigLB L hL hr) :=
    transportCubical (L := m.rigLB L hL hr) (M := m.rigLB L hL hr) w hw c' (m.thetaPull L.L c.t) ht
  exact ⟨c'', rfl, idIso _, idIso_isGen hL, idIso_maps _ _ _ _ hr,
    idIso_maps (L.L.pull m.F) (thφ G' (x3 G')) thε _ c''.isGen⟩

theorem cube_conclusion_iff {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L) :
    (∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen),
      (∃ c' : CubicalStr G' (m.rigLB L hL hr), m.IsPullCubical c' c) ∧
      (L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric)) ↔
    ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen)
      (c' : CubicalStr G' (m.rigLB L hL hr)),
      c'.t = m.thetaPull L.L c.t ∧ m.IsPullCubical c' c ∧
        (L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric) := by
  refine exists_congr fun hL => exists_congr fun hr => ?_
  rw [cubical_clause_iff]
  exact ⟨fun ⟨⟨c', h1, h2⟩, h3⟩ => ⟨c', h1, h2, h3⟩, fun ⟨c', h1, h2, h3⟩ => ⟨⟨c', h1, h2⟩, h3⟩⟩

end Group

end GlobalTheory.GtCubeCompare

end
