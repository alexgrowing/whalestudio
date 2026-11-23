import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
noncomputable section
namespace GlobalTheory.Ex.LabelsAllLevels

section Values
variable {O : Type} [CommRing O] {N N' : NumD O}

def lower {k m : ℕ} (p : N.QT (k * m)) : N.QT k :=
  ⟨(p.1.1, p.1.2 ^ m), (pow_mul' _ k m).symm.trans p.2⟩

private theorem twist_theta' {k : ℕ} (β : N.Form k) (u : Oˣ) : (N.twist β u).θ = N.θ := rfl

private theorem twist_c {k : ℕ} (β : N.Form k) (u : Oˣ) : (N.twist β u).c = N.c := rfl

theorem qEq_twist {j k m : ℕ} (β : N.Form j) {u r r' : Oˣ} (h₁ : r' ^ m = r) (h₂ : r ^ k = u)
    {q' : N.QT (k * m)} {q : N.QT k} {p' : (N.twist β u).QT (k * m)} {p : (N.twist β u).QT k}
    (t' : TwRel β u r' q' p') (t : TwRel β u r q p) (e : N.QEq (lower q') q) :
    (N.twist β u).QEq (lower p') p := by
  obtain ⟨z, hy, hg⟩ := e
  obtain ⟨ty', tb', ts'⟩ := t'
  obtain ⟨ty, tb, ts⟩ := t
  refine ⟨z, ?_, ?_⟩
  · have e1 : (lower p').1.1 = (lower q').1.1 := ty'
    rw [ty, e1]
    exact hy
  · show p.1.2 = p'.1.2 ^ m * (N.twist β u).io z
    have hg' : q.1.2 = q'.1.2 ^ m * N.io z := hg
    apply NumD.Gt.ext
    · rw [tb, hg', NumD.Gt.mul_b, NumD.Gt.mul_b, NumD.Gt.pow_b, NumD.Gt.pow_b, tb', NumD.io_b]
      rfl
    · refine funext fun (χ : N.X) => ?_
      have A1 := ts χ
      have A2 := NumD.Gt.mul_s (q'.1.2 ^ m) (N.io z) χ
      rw [NumD.io_s, NumD.io_b, ← hg'] at A2
      have A3 := NumD.Gt.pow_s q'.1.2 m χ
      have A4 : (p'.1.2 ^ m).s χ * cubN N.θ m 1 q'.1.2.b (N.c χ) = p'.1.2.s χ ^ m := by
        have A4' := NumD.Gt.pow_s p'.1.2 m χ
        rw [tb'] at A4'
        exact A4'
      have Bq : (p'.1.2 ^ m).b = (q'.1.2 ^ m).b := by
        rw [NumD.Gt.pow_b, NumD.Gt.pow_b, tb'] <;> rfl
      have A5 := ts' χ
      have A6 := N.twist_τ β u z χ
      have hy' : β.be q.1.1.toAdd χ = β.be q'.1.1.toAdd χ + k * β.be z χ := by
        rw [show q.1.1.toAdd = q'.1.1.toAdd + k • z from hy, map_add, map_nsmul, LinearMap.add_apply,
          LinearMap.smul_apply, nsmul_eq_mul]
      rw [hy'] at A1
      rw [NumD.Gt.mul_s (p'.1.2 ^ m) ((N.twist β u).io z) χ, NumD.io_s (N.twist β u) z χ,
        NumD.io_b (N.twist β u) z, Bq, twist_theta' β u, twist_c β u, A6]
      subst h₁ h₂
      apply Additive.ofMul.injective
      replace A1 := congrArg Additive.ofMul A1
      replace A2 := congrArg Additive.ofMul A2
      replace A3 := congrArg Additive.ofMul A3
      replace A4 := congrArg Additive.ofMul A4
      replace A5 := congrArg Additive.ofMul A5
      simp only [ofMul_mul, ofMul_div, ofMul_zpow, ofMul_pow] at A1 A2 A3 A4 A5 ⊢
      rw [A1, A2, eq_sub_of_add_eq A3, eq_sub_of_add_eq A4, A5]
      clear hy hg hg' hy' ty ty' tb tb' ts ts' A6 A1 A2 A3 A4 A5
      module

theorem rel_pow (J : NumD.Iso N N') {g : N.Gt} {g' : N'.Gt} (h : J.Rel g g') (n : ℕ) : J.Rel (g ^ n) (g' ^ n) :=
  (NumD.Hom.ofIso_rel J _ _).1 (((NumD.Hom.ofIso_rel J _ _).2 h).pow n)

theorem exists_image (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  let I := NumD.Hom.ofIso J
  have hp : p.1.2 ^ k = N.io p.1.1.toAdd := N.mem_QT.1 p.2
  have h1 : I.Rel (p.1.2 ^ k) (I.img p.1.2 ^ k) := (I.rel_img p.1.2).pow k
  have h2 : I.Rel (p.1.2 ^ k) (N'.io (I.e p.1.1.toAdd)) := by
    rw [hp]
    exact I.rel_io _
  have h3 : I.img p.1.2 ^ k = N'.io (J.e p.1.1.toAdd) :=
    ((I.rel_iff _ _).1 h1).trans ((I.rel_iff _ _).1 h2).symm
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), I.img p.1.2), N'.mem_QT.2 h3⟩, rfl,
    (NumD.Hom.ofIso_rel J _ _).1 (I.rel_img _)⟩

theorem qEq_image (J : NumD.Iso N N') {k m : ℕ} {p' : N.QT (k * m)} {p : N.QT k} {q' : N'.QT (k * m)} {q : N'.QT k}
    (a' : q'.1.1.toAdd = J.e p'.1.1.toAdd) (b' : J.Rel p'.1.2 q'.1.2) (a : q.1.1.toAdd = J.e p.1.1.toAdd)
    (b : J.Rel p.1.2 q.1.2) (e : N.QEq (lower p') p) : N'.QEq (lower q') q := by
  obtain ⟨z, hy, hg⟩ := e
  let I := NumD.Hom.ofIso J
  refine ⟨J.e z, ?_, ?_⟩
  · show q.1.1.toAdd = q'.1.1.toAdd + k • J.e z
    have hy' : p.1.1.toAdd = p'.1.1.toAdd + k • z := hy
    rw [a, a', hy', map_add, map_nsmul]
  · show q.1.2 = q'.1.2 ^ m * N'.io (J.e z)
    have hg' : p.1.2 = p'.1.2 ^ m * N.io z := hg
    have r1 : I.Rel p.1.2 q.1.2 := (NumD.Hom.ofIso_rel J _ _).2 b
    have r2 : I.Rel p.1.2 (q'.1.2 ^ m * N'.io (J.e z)) := by
      rw [hg']
      exact (((NumD.Hom.ofIso_rel J _ _).2 b').pow m).mul (I.rel_io z)
    exact ((I.rel_iff _ _).1 r1).trans ((I.rel_iff _ _).1 r2).symm

private theorem pow_left_of_isGrpPullback' {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (z : Over.mk (T.hom ≫ f) ⟶ G) (e : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero =>
    let o : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w])
    have ho : o * o = o := by
      apply Over.OverMorphism.ext
      rw [h.2 T 1 1 o o rfl rfl, _root_.mul_one]
      rfl
    have h1 : o = 1 := mul_left_cancel (a := o) (by rw [_root_.mul_one]; exact ho)
    rw [pow_zero, pow_zero, ← h1]
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih e
end Values

theorem pow_left {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (x : baseOver S' ⟶ G') (z : Over.mk f ⟶ G)
    (e : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  let w : Over.mk ((baseOver S').hom ≫ f) ⟶ Over.mk f := Over.homMk (𝟙 S') (by simp)
  have h1 : (w ≫ z).left = x.left ≫ φ := by
    rw [Over.comp_left, e]
    simp [w]
  have h2 := pow_left_of_isGrpPullback' h x (w ≫ z) h1 n
  rw [← comp_pow, Over.comp_left] at h2
  simpa [w] using h2

theorem labels_of_four_le : GlobalTheory.UT.LL → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → (∀ k, 4 ≤ k → Labels A u r M ν' J k) → ∀ k, 0 < k → Labels A u r M ν' J k := by
  intro hL hBr E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hR _ hT h4 k hk
  intro x p q' p' z hTw hqy hqg hQ hz
  have hK : 0 < k * 4 := by omega
  obtain ⟨p₁, hp₁, -⟩ := existsUnique_twRel A.be u (r (k * 4)) (hR.pow hK) (A.q (k * 4) x)
  obtain ⟨q₁, hq₁y, hq₁g⟩ := exists_image J p₁
  obtain ⟨-, -, -, -, hQk⟩ := hBr M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨p₁', hp₁'⟩ := (hQk (k * 4)).2.1 q₁
  have hw : ((o.I.ev (k * 4) x).left ≫ M.φ) ≫ M.P.A.A.hom = (Out.TFK (R := M.W) C).hom := by
    rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
    simp
  let z₁ : Out.TFK (R := M.W) C ⟶ M.P.A.A := Over.homMk ((o.I.ev (k * 4) x).left ≫ M.φ) hw
  have t₁ : M.P.ToA C (k * 4) p₁' z₁ := h4 (k * 4) (by omega) x p₁ q₁ p₁' z₁ hp₁ hq₁y hq₁g hp₁' rfl
  obtain ⟨p₂, hp₂⟩ := (hQk k).2.1 (lower q₁)
  have hy₂ : p₂.y = p₁'.y := hp₂.1.symm.trans hp₁'.1
  have hn₂ : GtPtF.IsNsmul 4 p₁'.g p₂.g := (GtValues.isNsmul_val ν' 4 hp₁'.2 hp₂.2).2 rfl
  haveI := M.admissible_base_of_complete_dvr.2
  have t₂ : M.P.ToA C k p₂ (z₁ ^ 4) :=
    (GlobalTheory.LevelCompat.qkToAkU_level hL M.W (IsLocalRing.maximalIdeal M.W) M.admissible_base_of_complete_dvr.1 M.P.D M.P.A M.t.G M.t.semi
      M.P.U C k 4 (k * 4) hk (by norm_num) rfl p₂ p₁' z₁).2 hy₂ hn₂ t₁
  obtain ⟨hgA, -, -, -, hQA⟩ := hBr O' a.D₀ a.even a.bimult C A.N A.ν
  obtain ⟨q₀, hq₀y, hq₀n, hq₀e⟩ := A.I.tower k 4 hk (by norm_num) x
  have hqA := A.hq (k * 4) x
  obtain ⟨c₀, hc₀, -⟩ := hgA q₀.g
  have hc : c₀ = (A.q (k * 4) x).1.2 ^ 4 := (GtValues.isNsmul_val A.ν 4 hqA.2 hc₀).1 hq₀n
  have hQP : A.ν.QPt q₀ (lower (A.q (k * 4) x)) := by
    refine ⟨hqA.1.trans hq₀y.symm, ?_⟩
    show A.ν.Pt q₀.g ((A.q (k * 4) x).1.2 ^ 4)
    rw [← hc]
    exact hc₀
  have hE1 : A.N.QEq (lower (A.q (k * 4) x)) (A.q k x) :=
    ((hQA k).2.2 q₀ (A.I.ev k x) _ _ hQP (A.hq k x)).1 hq₀e
  have hE0 := qEq_twist A.be (hR.2 k 4 hk (by norm_num)) (hR.pow hk) hp₁ hTw hE1
  have hE : Out.QkPt.Equiv M.P.D.toPre C p₂ p' :=
    ((hQk k).2.2 p₂ p' _ _ hp₂ hQ).2 (qEq_image J hq₁y hq₁g hqy hqg hE0)
  obtain ⟨F, hF1, -, hF3, -, -, -⟩ := hT C k hk
  have e3 : z = z₁ ^ 4 := by
    apply Over.OverMorphism.ext
    rw [hz, pow_left M.cart (o.I.ev (k * 4) x) z₁ rfl 4, o.I.tower k 4 hk (by norm_num) x]
  exact (hF1 p' z).2 (e3.trans (((hF1 p₂ _).1 t₂).trans ((hF3 p₂ p').2 hE)))

end GlobalTheory.Ex.LabelsAllLevels
end
