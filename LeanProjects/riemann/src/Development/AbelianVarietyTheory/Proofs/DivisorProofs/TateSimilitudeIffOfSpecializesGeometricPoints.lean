import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomPointsFactorHenselianOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointsRestrictBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsOfUnityMapBijectiveOfHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsRootLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeOfExistsRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTSpecTate

theorem transport_algO {p : ℕ} [Fact p.Prime] (D : Datum p)
    {R k k' QR Q Q' : Type} [CommRing R] [Field k] [Field k'] [Group QR] [Group Q] [Group Q']
    (hcomm : ∀ a b : QR, a * b = b * a)
    (actR : D.O → QR → QR) (act : D.O → Q → Q) (act' : D.O → Q' → Q')
    (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → k'ˣ → Prop)
    (ρ : QR →* Q) (ρ' : QR →* Q') (φ : Rˣ →* kˣ) (φ' : Rˣ →* k'ˣ)
    (hρi : ∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h)
    (hρs : ∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ g = x)
    (hρ'i : ∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h)
    (hρ's : ∀ n, 0 < n → n.Coprime p → ∀ x : Q', x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ' g = x)
    (hφi : ∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ u = φ v → u = v)
    (hφs : ∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ φ u = z)
    (hφ'i : ∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ' u = φ' v → u = v)
    (hactR : ∀ c g h, actR c (g * h) = actR c g * actR c h)
    (hρact : ∀ c g, ρ (actR c g) = act c (ρ g)) (hρ'act : ∀ c g, ρ' (actR c g) = act' c (ρ' g))
    (hact'1 : ∀ c, act' c 1 = 1)
    (hpair : ∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 →
      ∃ u : Rˣ, u ^ n = 1 ∧ e n (ρ g) (ρ h) (φ u) ∧ e' n (ρ' g) (ρ' h) (φ' u))
    (huniq : ∀ n, 0 < n → n.Coprime p → ∀ x y c c', e n x y c → e n x y c' → c = c')
    (I : TateIsoO D k Q act e) :
    ∃ I' : TateIsoO D k' Q' act' e', ∀ n, 0 < n → n.Coprime p → ∀ a (g : QR), g ^ n = 1 →
      ρ g = I.ev n a → ρ' g = I'.ev n a := by
  obtain ⟨L, hL⟩ := GlobalTheory.TateTransportAlg.exists_torsLift p ρ hρi
  obtain ⟨W, hW⟩ := GlobalTheory.TateTransportAlg.exists_torsLift p φ hφi
  have hLx : ∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → L x ^ n = 1 ∧ ρ (L x) = x := by
    intro n hn hnp x hx
    obtain ⟨g, hg, rfl⟩ := hρs n hn hnp x hx
    rw [hL n hn hnp g hg]; exact ⟨hg, rfl⟩
  have hWx : ∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → W z ^ n = 1 ∧ φ (W z) = z := by
    intro n hn hnp z hz
    obtain ⟨u, hu, rfl⟩ := hφs n hn hnp z hz
    rw [hW n hn hnp u hu]; exact ⟨hu, rfl⟩
  have hLmul : ∀ n, 0 < n → n.Coprime p → ∀ x y : Q, x ^ n = 1 → y ^ n = 1 → L (x * y) = L x * L y := by
    intro n hn hnp x y hx hy
    obtain ⟨hx1, hx2⟩ := hLx n hn hnp x hx
    obtain ⟨hy1, hy2⟩ := hLx n hn hnp y hy
    have := hL n hn hnp (L x * L y)
      (by rw [(show Commute (L x) (L y) from hcomm _ _).mul_pow, hx1, hy1, _root_.one_mul])
    rwa [map_mul, hx2, hy2] at this
  have hevt : ∀ n, 0 < n → n.Coprime p → ∀ a, I.ev n a ^ n = 1 :=
    fun n hn hnp a => (I.onto n hn hnp _).2 ⟨a, rfl⟩
  have hζt : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 :=
    fun n hn hnp => (I.ζ_prim n hn hnp).pow_eq_one
  have hactR1 : ∀ c, actR c 1 = 1 := fun c => by
    have := hactR c 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
  have hactRpow : ∀ c g (n : ℕ), actR c (g ^ n) = actR c g ^ n := by
    intro c g n
    induction n with
    | zero => simp [hactR1]
    | succ n ih => rw [pow_succ, hactR, ih, pow_succ]
  have hLact : ∀ n, 0 < n → n.Coprime p → ∀ c x, x ^ n = 1 → L (act c x) = actR c (L x) := by
    intro n hn hnp c x hx
    obtain ⟨h1, h2⟩ := hLx n hn hnp x hx
    have := hL n hn hnp (actR c (L x)) (by rw [← hactRpow, h1, hactR1])
    rwa [hρact, h2] at this
  refine ⟨{ ζ := fun n => φ' (W (I.ζ n)),
             ζ_prim := ?_,
             ζ_pow := ?_,
             ev := fun n a => if 0 < n ∧ n.Coprime p then ρ' (L (I.ev n a)) else 1,
             add := ?_,
             lin := ?_,
             ker := ?_,
             onto := ?_,
             tower := ?_,
             isom := ?_ }, ?_⟩
  · intro n hn hnp
    obtain ⟨hw1, hw2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    refine ⟨by rw [← map_pow, hw1, map_one], fun l hl => ?_⟩
    rw [← map_pow] at hl
    have : W (I.ζ n) ^ l = 1 := hφ'i n hn hnp _ _
      (by rw [← pow_mul, mul_comm, pow_mul, hw1, one_pow]) (one_pow n) (by rw [hl, map_one])
    exact (I.ζ_prim n hn hnp).dvd_of_pow_eq_one l (by rw [← hw2, ← map_pow, this, map_one])
  · intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
    obtain ⟨a1, a2⟩ := hWx (n * m) (Nat.mul_pos hn hm) hnm _ (hζt _ (Nat.mul_pos hn hm) hnm)
    obtain ⟨b1, b2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    show φ' (W (I.ζ (n * m))) ^ m = φ' (W (I.ζ n))
    rw [← map_pow, hφi n hn hnp (W (I.ζ (n * m)) ^ m) (W (I.ζ n))
      (by rw [← pow_mul, mul_comm m n, a1]) b1 (by rw [map_pow, a2, b2, I.ζ_pow n m hn hm hnm])]
  · intro n a b
    split_ifs with h
    · rw [I.add, hLmul n h.1 h.2 _ _ (hevt n h.1 h.2 a) (hevt n h.1 h.2 b), map_mul]
    · rw [_root_.mul_one]
  · intro n c a
    split_ifs with h
    · rw [I.lin, hLact n h.1 h.2 c _ (hevt n h.1 h.2 a), hρ'act]
    · rw [hact'1]
  · intro n hn hnp a
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    rw [← I.ker n hn hnp a]
    obtain ⟨h1, h2⟩ := hLx n hn hnp _ (hevt n hn hnp a)
    constructor
    · intro h
      have := hρ'i n hn hnp _ 1 h1 (one_pow n) (by rw [h, map_one])
      rw [← h2, this, map_one]
    · intro h
      rw [h, ← map_one ρ, hL n hn hnp 1 (one_pow n), map_one]
  · intro n hn hnp y
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    constructor
    · intro hy
      obtain ⟨g, hg1, rfl⟩ := hρ's n hn hnp y hy
      obtain ⟨a, ha⟩ := (I.onto n hn hnp (ρ g)).1 (by rw [← map_pow, hg1, map_one])
      exact ⟨a, by rw [ha, hL n hn hnp g hg1]⟩
    · rintro ⟨a, rfl⟩
      rw [← map_pow, (hLx n hn hnp _ (hevt n hn hnp a)).1, map_one]
  · intro n m hn hm hnm a
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
    have hnm0 : 0 < n * m := Nat.mul_pos hn hm
    have hg1 : 0 < n * m ∧ (n * m).Coprime p := ⟨hnm0, hnm⟩
    have hg2 : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg1, if_pos hg2]
    obtain ⟨h1, h2⟩ := hLx (n * m) hnm0 hnm _ (hevt _ hnm0 hnm a)
    have := hL n hn hnp (L (I.ev (n * m) a) ^ m) (by rw [← pow_mul, mul_comm m n, h1])
    rw [map_pow, h2, I.tower n m hn hm hnm] at this
    rw [← map_pow, ← this]
  · intro n hn hnp a b
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    obtain ⟨ga1, ga2⟩ := hLx n hn hnp _ (hevt n hn hnp a)
    obtain ⟨gb1, gb2⟩ := hLx n hn hnp _ (hevt n hn hnp b)
    obtain ⟨u, hu, he, he'⟩ := hpair n hn hnp _ _ ga1 gb1
    rw [ga2, gb2] at he
    obtain ⟨w1, w2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    have hk := huniq n hn hnp _ _ _ _ he (I.isom n hn hnp a b)
    have hu' : u = W (I.ζ n) ^ (2 * D.EF a b) := hφi n hn hnp _ _ hu
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm (2 * D.EF a b), zpow_mul, zpow_natCast, w1, one_zpow])
      (by rw [hk, map_zpow, w2])
    rw [hu', map_zpow] at he'
    exact he'
  · intro n hn hnp a g hg hρg
    have hgd : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hgd]
    rw [← hρg, hL n hn hnp g hg]

end GlobalTheory.HTSpecTate

noncomputable section

namespace GlobalTheory.HTSpecTate

variable {p : ℕ} [Fact p.Prime]

theorem tateCond_congr {D : Datum p} {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OActN D.O A)
    (L : LB A.left) (M : ℕ) {k : Type} [Field k] {x₀ x₁ : Sp k ⟶ S} (h : x₀ = x₁)
    (f₀ : D.La → (Over.mk x₀ ⟶ A)) (f₁ : D.La → (Over.mk x₁ ⟶ A))
    (hf : ∀ y, f₁ y = (Over.homMk (𝟙 _) (by simp [h]) : Over.mk x₁ ⟶ Over.mk x₀) ≫ f₀ y) :
    (∃ I : TateIsoO D k (Over.mk x₀ ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, f₀ y = I.ev M y) →
    (∃ I : TateIsoO D k (Over.mk x₁ ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, f₁ y = I.ev M y) := by
  subst h
  rintro ⟨I, hI⟩
  refine ⟨I, fun y => ?_⟩
  rw [hf, ← hI y]
  have e : (Over.homMk (𝟙 _) (by simp) : Over.mk x₀ ⟶ Over.mk x₀) = 𝟙 _ := by ext; simp
  rw [e, Category.id_comp]

theorem exists_rig_diag {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
    {s : S ⟶ Sp R} (o : Obj b N s) :
    ∃ r : LB.Gen ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull (eSec o.A)), r.IsGen := by
  have hP := o.isLB
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB hP _
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hL _)).1 ?_
  have e := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 o.rig₁
  rw [GlobalTheory.CechPic.cls_pull hP] at e
  have e' := congrArg (GlobalTheory.CechPic.pull (eSec o.A)) e
  rw [map_zero, ← GlobalTheory.CechPic.pull_comp] at e'
  rw [GlobalTheory.CechPic.cls_pull hL, GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp]
  have hη : η[o.A] ≫ lift (𝟙 o.A) (𝟙 o.A) = η[o.A] ≫ lift (1 : o.A ⟶ o.A) (𝟙 o.A) := by
    rw [comp_lift, comp_lift, MonObj.comp_one, Category.comp_id]
    congr 1
  have : eSec o.A ≫ (lift (𝟙 o.A) (𝟙 o.A)).left = eSec o.A ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left := by
    simp only [eSec, ← Over.comp_left, hη]
  rw [this]
  exact e'

end GlobalTheory.HTSpecTate

noncomputable section

namespace GlobalTheory.HTSpecTate

variable {p : ℕ} [Fact p.Prime]

theorem tateCond_transport (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hN'p : N'.Coprime p)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (Rh : Type) [CommRing Rh] [HenselianLocalRing Rh]
    [IsAlgClosed (IsLocalRing.ResidueField Rh)] (t : Sp Rh ⟶ S) (lvR : D.La → (Over.mk t ⟶ o.A))
    (hadd : ∀ x y, lvR (x + y) = lvR x * lvR y) (hker : ∀ x, lvR (N' • x) = 1)
    (hlin : ∀ (c : D.O) x, lvR (c • x) = lvR x ≫ o.act.act c)
    {k k' : Type} [Field k] [Field k'] (i : Sp k ⟶ Sp Rh) (i' : Sp k' ⟶ Sp Rh) :
    (∃ I : TateIsoO D k (Over.mk (i ≫ t) ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
        ∀ y, (Over.homMk i rfl : Over.mk (i ≫ t) ⟶ Over.mk t) ≫ lvR y = I.ev N' y) →
    (∃ I : TateIsoO D k' (Over.mk (i' ≫ t) ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
        ∀ y, (Over.homMk i' rfl : Over.mk (i' ≫ t) ⟶ Over.mk t) ≫ lvR y = I.ev N' y) := by
  intro hT
  have hA := o.ab
  have hN' : 0 < N' := levelPos_of_coprime hN'p
  set L : LB o.A.left := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left with hLdef
  have hL : L.IsLB := pull_isLB o.isLB _
  obtain ⟨r₀, hr₀⟩ := exists_rig_diag o
  let M : RigLB o.A := ⟨L, r₀, hL, hr₀⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple hA hL o.ample hL
  obtain ⟨θ', hθ', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised hL θ hθ
  let cub : CubicalStr o.A M := GlobalTheory.AbLaw.Cube.cubicalOfNormalised GlobalTheory.globalFns_holds hA M θ' hθ' hn
  have hS : ∀ n : ℕ, n.Coprime p → IsUnit (n : Γ(S, ⊤)) := by
    intro n hnp
    have := ((b.unit n hnp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map s.appTop.hom
    simpa using this
  have hRu : ∀ n : ℕ, n.Coprime p → IsUnit (n : Rh) := by
    intro n hnp
    have := ((hS n hnp).map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of Rh)).hom.hom
    simpa using this
  obtain ⟨φ, rfl⟩ : ∃ φ : Rh →+* k, i = spMap φ := ⟨(Spec.preimage i).hom, by simp [spMap]⟩
  obtain ⟨φ', rfl⟩ : ∃ φ' : Rh →+* k', i' = spMap φ' := ⟨(Spec.preimage i').hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := hT
  let j : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let j' : Over.mk (spMap φ' ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ') rfl
  let ρ : (Over.mk t ⟶ o.A) →* (Over.mk (spMap φ ≫ t) ⟶ o.A) :=
    { toFun := fun g => j ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  let ρ' : (Over.mk t ⟶ o.A) →* (Over.mk (spMap φ' ≫ t) ⟶ o.A) :=
    { toFun := fun g => j' ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  have hpull : ∀ {K : Type} [Field K] (ψ : Rh →+* K) (n : ℕ) (g h : Over.mk t ⟶ o.A) (u : Rhˣ),
      Out.WeilIs o.A L (n : ℤ) g h (unitOn u) →
      Out.WeilIs o.A L (n : ℤ) ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ g)
        ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ h)
        (unitOn (Units.map ψ.toMonoidHom u)) := by
    intro K _ ψ n g h u H
    have H' := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hA hL
      (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) H
    have e : Units.map (spMap ψ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map ψ.toMonoidHom u) :=
      Units.ext (congrArg (fun q => q.hom (u : Rh)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm
    exact e ▸ H'
  have hpow : ∀ a, lvR a ^ N' = 1 := by
    intro a
    have : ∀ m : ℕ, lvR (m • a) = lvR a ^ m := by
      intro m
      induction m with
      | zero =>
        have h0 := hadd 0 0
        rw [add_zero] at h0
        rw [zero_smul, pow_zero]
        exact left_eq_mul.1 h0
      | succ m ih => rw [succ_nsmul, hadd, ih, pow_succ]
    rw [← this]; exact hker a
  have h1 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ o.A, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S o.A hA n hn (hS n hnp) Rh t k φ).1
  have h2 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ ≫ t) ⟶ o.A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ o.A, g ^ n = 1 ∧ ρ g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S o.A hA n hn (hS n hnp) Rh t k φ).2
  have h3 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ o.A, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S o.A hA n hn (hS n hnp) Rh t k' φ').1
  have h4 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ' ≫ t) ⟶ o.A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ o.A, g ^ n = 1 ∧ ρ' g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S o.A hA n hn (hS n hnp) Rh t k' φ').2
  have h5 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    GlobalTheory.rootsOfUnity_map_bijective_of_henselian Rh k φ n hn (hRu n hnp)
  have h6 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    GlobalTheory.rootsOfUnity_map_bijective_of_henselian Rh k' φ' n hn (hRu n hnp)
  have h7 : ∀ (c : D.O) (g h : Over.mk t ⟶ o.A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have h8 : ∀ c, (1 : Over.mk (spMap φ' ≫ t) ⟶ o.A) ≫ o.act.act c = 1 := by
    intro c
    haveI := o.act.hom c
    exact MonObj.one_comp _
  have h9 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ o.A, g ^ n = 1 → h ^ n = 1 →
      ∃ u : Rhˣ, u ^ n = 1 ∧ Out.WeilIs o.A L (n : ℤ) (ρ g) (ρ h) (unitOn (Units.map φ.toMonoidHom u)) ∧
        Out.WeilIs o.A L (n : ℤ) (ρ' g) (ρ' h) (unitOn (Units.map φ'.toMonoidHom u)) := by
    intro n hn hnp g h hg hh
    obtain ⟨u, hu, H⟩ := GlobalTheory.WeilRootLocal.exists_weilIs_root_local S o.A hA M cub Rh t n g h hg hh
    exact ⟨u, hu, hpull φ n g h u H, hpull φ' n g h u H⟩
  have h10 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ (x y : Over.mk (spMap φ ≫ t) ⟶ o.A) (c c' : kˣ),
      Out.WeilIs o.A L (n : ℤ) x y (unitOn c) → Out.WeilIs o.A L (n : ℤ) x y (unitOn c') → c = c' :=
    fun n _ _ x y c c' h h' => GlobalTheory.weilIs_unique_fieldPoint S o.A L hL k (spMap φ ≫ t) n x y c c' h h'
  obtain ⟨I', hI'⟩ := transport_algO D (R := Rh) (k := k) (k' := k')
    (QR := Over.mk t ⟶ o.A) (Q := Over.mk (spMap φ ≫ t) ⟶ o.A) (Q' := Over.mk (spMap φ' ≫ t) ⟶ o.A)
    (fun a b => mul_comm a b) (fun c g => g ≫ o.act.act c) (fun c g => g ≫ o.act.act c)
    (fun c g => g ≫ o.act.act c)
    (fun n g g' c => Out.WeilIs o.A L n g g' (unitOn c)) (fun n g g' c => Out.WeilIs o.A L n g g' (unitOn c))
    ρ ρ' (Units.map φ.toMonoidHom) (Units.map φ'.toMonoidHom)
    h1 h2 h3 h4 (fun n hn hnp => (h5 n hn hnp).1) (fun n hn hnp => (h5 n hn hnp).2)
    (fun n hn hnp => (h6 n hn hnp).1)
    h7 (fun c g => (Category.assoc j g (o.act.act c)).symm) (fun c g => (Category.assoc j' g (o.act.act c)).symm)
    h8 h9 h10 I
  exact ⟨I', fun a => hI' N' hN' hN'p a (lvR a) (hpow a) (hI a)⟩

end GlobalTheory.HTSpecTate

noncomputable section

namespace GlobalTheory.HTSpecTate

theorem tateIsoO_iff_of_specializes : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S) [IsLocallyNoetherian T.left] (lv : D.La → (T ⟶ o.A)), (∀ x y, lv (x + y) = lv x * lv y) → (∀ x, lv (N' • x) = 1) → (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) → ∀ {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ T.left) (x' : Sp k' ⟶ T.left) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ((∃ I : TateIsoO D k (Over.mk (x ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y) ↔ (∃ I : TateIsoO D k' (Over.mk (x' ≫ T.hom) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, (Over.homMk x' rfl : Over.mk (x' ≫ T.hom) ⟶ T) ≫ lv y = I.ev N' y)) := by
  intro p _ D R _ b N N' hN'p S s o T _ lv hadd hker hlin k k' _ _ _ _ x x' u u' hsp
  obtain ⟨Rh, _, _, _, r, i, i', hi, hi'⟩ := GlobalTheory.geomPoints_factor_henselian_of_specializes x x' u u' hsp
  let lvR : D.La → (Over.mk (r ≫ T.hom) ⟶ o.A) := fun a => (Over.homMk r rfl : Over.mk (r ≫ T.hom) ⟶ T) ≫ lv a
  have hadd' : ∀ a c, lvR (a + c) = lvR a * lvR c := fun a c => by simp only [lvR, hadd, MonObj.comp_mul]
  have hker' : ∀ a, lvR (N' • a) = 1 := fun a => by simp only [lvR, hker, MonObj.comp_one]
  have hlin' : ∀ (c : D.O) a, lvR (c • a) = lvR a ≫ o.act.act c := fun c a => by
    simp only [lvR, hlin, Category.assoc]
  have e1 : x ≫ T.hom = i ≫ r ≫ T.hom := by rw [← hi, Category.assoc]
  have e2 : x' ≫ T.hom = i' ≫ r ≫ T.hom := by rw [← hi', Category.assoc]
  constructor
  · intro h
    have h1 := tateCond_congr o.A o.act (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) N' e1 _
      (fun a => (Over.homMk i rfl : Over.mk (i ≫ r ≫ T.hom) ⟶ Over.mk (r ≫ T.hom)) ≫ lvR a)
      (fun a => by simp only [lvR, ← Category.assoc]; congr 1; ext; simp [hi]) h
    have h2 := tateCond_transport D R b N N' hN'p S s o Rh (r ≫ T.hom) lvR hadd' hker' hlin' i i' h1
    exact tateCond_congr o.A o.act _ N' e2.symm _ _
      (fun a => by simp only [lvR, ← Category.assoc]; congr 1; ext; simp [hi']) h2
  · intro h
    have h1 := tateCond_congr o.A o.act (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) N' e2 _
      (fun a => (Over.homMk i' rfl : Over.mk (i' ≫ r ≫ T.hom) ⟶ Over.mk (r ≫ T.hom)) ≫ lvR a)
      (fun a => by simp only [lvR, ← Category.assoc]; congr 1; ext; simp [hi']) h
    have h2 := tateCond_transport D R b N N' hN'p S s o Rh (r ≫ T.hom) lvR hadd' hker' hlin' i' i h1
    exact tateCond_congr o.A o.act _ N' e1.symm _ _
      (fun a => by simp only [lvR, ← Category.assoc]; congr 1; ext; simp [hi]) h2

end GlobalTheory.HTSpecTate
