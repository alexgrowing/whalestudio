import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelClassZeroOfDividesAllThetaConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateLabelThetaConstantDividesAStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.IntLabel

section
variable {G X : Type} [AddCommGroup G] [AddCommGroup X] {N : ℕ} {Y : G → (Fin 8 → X) → Prop}

theorem yy_zero (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) : Y 0 0 := by
  obtain ⟨mu, hmu⟩ := h1 0
  have h2 := h4 0 0 mu mu hmu hmu
  rw [add_zero] at h2
  have hc := (h3 0 mu (mu + mu) hmu).1 h2
  refine (h3 0 mu 0 hmu).2 fun v => ?_
  obtain ⟨w, hw⟩ := hc v
  have e : mu v = N • w := add_left_cancel (a := mu v) (by simpa using hw)
  exact ⟨-w, by simp [e]⟩

theorem yy_neg (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a : G} {mu : Fin 8 → X} (ha : Y a mu) :
    Y (-a) (-mu) := by
  obtain ⟨mu', h'⟩ := h1 (-a)
  have h0 := h4 a (-a) mu mu' ha h'
  rw [add_neg_cancel] at h0
  have hc := (h3 0 0 (mu + mu') (yy_zero h1 h3 h4)).1 h0
  refine (h3 (-a) mu' (-mu) h').2 fun v => ?_
  obtain ⟨w, hw⟩ := hc v
  simp only [Pi.add_apply, Pi.zero_apply, zero_add] at hw
  refine ⟨-w, ?_⟩
  simp only [Pi.neg_apply, smul_neg]
  rw [← hw]
  abel

theorem yy_sub (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a b : G} {mu nu : Fin 8 → X} (ha : Y a mu)
    (hb : Y b nu) : Y (a - b) (mu - nu) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h4 _ _ _ _ ha (yy_neg h1 h3 h4 hb)

theorem yy_nsmul (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (k : ℕ) {a : G} {mu : Fin 8 → X} (ha : Y a mu) :
    Y (k • a) (k • mu) := by
  induction k with
  | zero => simpa using yy_zero h1 h3 h4
  | succ k ih => rw [succ_nsmul, succ_nsmul]; exact h4 _ _ _ _ ih ha

theorem mem_closure_iff (p J : ℕ) (hJ : 2 ≤ J) (hN : N = p ^ J) (hG : ∀ a : G, N • a = 0)
    (htor : ∀ b : G, p • b = 0 → ∃ c, b = p ^ (J - 1) • c) (htf : ∀ x : X, p ^ (J - 1) • x = 0 → x = 0)
    (h1 : ∀ a, ∃ mu, Y a mu) (h2 : ∀ mu, ∃ a, Y a mu)
    (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (S : Set G) (hS : ∀ a ∈ S, Y a 0)
    (hT : ∀ a, Y a 0 → ∃ b, p • b = 0 ∧ a + b ∈ S) (a : G) : a ∈ AddSubgroup.closure S ↔ Y a 0 := by
  constructor
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem x hx => exact hS x hx
    | zero => exact yy_zero h1 h3 h4
    | add x y _ _ hx hy => simpa using h4 x y 0 0 hx hy
    | neg x _ hx => simpa using yy_neg h1 h3 h4 hx
  · intro ha
    obtain ⟨b, hb, hab⟩ := hT a ha
    have hYb : Y b 0 := by simpa using yy_sub h1 h3 h4 (hS _ hab) ha
    obtain ⟨c, rfl⟩ := htor b hb
    obtain ⟨muc, hc⟩ := h1 c
    have hcong := (h3 _ _ _ (yy_nsmul h1 h3 h4 (p ^ (J - 1)) hc)).1 hYb
    have hw : ∀ v, ∃ w : X, muc v = p • w := by
      intro v
      obtain ⟨w, hw⟩ := hcong v
      simp only [Pi.zero_apply, Pi.smul_apply] at hw
      refine ⟨-w, ?_⟩
      have e : p ^ (J - 1) • (muc v + p • w) = 0 := by
        rw [smul_add, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN]
        exact hw.symm
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      exact htf _ e
    choose w hw using hw
    have hmu : muc = p • w := funext fun v => by simp [hw v]
    obtain ⟨c', hc'⟩ := h2 w
    have hk : Y (c - p • c') 0 := by
      have := yy_sub h1 h3 h4 hc (yy_nsmul h1 h3 h4 p hc')
      rwa [← hmu, sub_self] at this
    obtain ⟨bk, hbk, hkS⟩ := hT _ hk
    have hbk0 : p ^ (J - 1) • bk = 0 := by
      obtain ⟨e, he⟩ : ∃ e, J - 1 = e + 1 := ⟨J - 2, by omega⟩
      rw [he, pow_succ, mul_smul, hbk, smul_zero]
    have key : p ^ (J - 1) • c = p ^ (J - 1) • ((c - p • c') + bk) := by
      rw [smul_add, hbk0, add_zero, smul_sub, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN, hG, sub_zero]
    have hbcl : p ^ (J - 1) • c ∈ AddSubgroup.closure S := by
      rw [key]; exact nsmul_mem (AddSubgroup.subset_closure hkS) _
    have e : a = (a + p ^ (J - 1) • c) - p ^ (J - 1) • c := by abel
    rw [e]
    exact sub_mem (AddSubgroup.subset_closure hab) hbcl

theorem zmod_tors {p J M : ℕ} (hp : 0 < p) (hJ : 1 ≤ J) (hM : M = p ^ J) (x : ZMod M) (hx : p • x = 0) :
    ∃ y : ZMod M, x = p ^ (J - 1) • y := by
  subst hM
  haveI : NeZero (p ^ J) := ⟨pow_ne_zero _ hp.ne'⟩
  have h1 : p ^ J ∣ p * x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (p ^ J)) (p ^ J)]
    push_cast
    rw [ZMod.natCast_zmod_val]
    rwa [nsmul_eq_mul] at hx
  have h2 : p ^ (J - 1) ∣ x.val := by
    have e : p ^ J = p * p ^ (J - 1) := by rw [← pow_succ']; congr 1; omega
    have h1' : p * p ^ (J - 1) ∣ p * x.val := by rw [← e]; exact h1
    exact Nat.dvd_of_mul_dvd_mul_left hp h1'
  obtain ⟨q, hq⟩ := h2
  refine ⟨(q : ZMod (p ^ J)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [hq, nsmul_eq_mul]
  push_cast
  ring

end
end GlobalTheory.Poinc.Sep.IntLabel

namespace GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Sep.IntLabel in

theorem mem_HH_iff_yy_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ ↔ 𝔪.YY a 0 := by
  intro g n F W Z i X₁ z₁ act x₀ hx₀ V _ _ _ ev X _ m t δ 𝔪 a
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨j, hj, hr⟩ := X₁.ρ.r_eq
  have hp : 0 < X₁.ρ.n := X₁.ρ.n_prime.pos
  have hk := X₁.ρ.two_le
  have hN : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j + X₁.ρ.k * 2) := by rw [hr, X₁.ρ.N_eq, pow_add, pow_mul]
  have hJ : 2 ≤ j + X₁.ρ.k * 2 := by omega
  have hG : ∀ b : X₁.S.Gam, (X₁.S.r * X₁.S.N) • b = 0 := fun b => by
    funext v
    simp [nsmul_eq_mul]
  have htor : ∀ b : X₁.S.Gam, X₁.ρ.n • b = 0 → ∃ c : X₁.S.Gam, b = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • c := by
    intro b hb
    have hv : ∀ v, ∃ y : ZMod (X₁.S.r * X₁.S.N), b v = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • y := fun v =>
      zmod_tors hp (by omega) hN (b v) (by simpa using congrFun hb v)
    choose c hc using hv
    exact ⟨c, funext fun v => by simpa using hc v⟩
  have htf : ∀ x : X, X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • x = 0 → x = 0 := by
    intro x hx
    have hq : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) ≠ 0 := pow_ne_zero _ hp.ne'
    have hs : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • (Pi.single 0 x : Fin 8 → X) = 0 := by
      funext v
      by_cases hv : v = 0
      · subst hv; simp [hx]
      · simp [Pi.single_apply, hv]
    have he : ((X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) : ℕ) : ℤ) • 𝔪.e₈ (Pi.single 0 x) = 0 := by
      rw [natCast_zsmul, ← map_nsmul, hs, map_zero]
    have h0 : 𝔪.e₈ (Pi.single 0 x) = 0 := (smul_eq_zero.1 he).resolve_left (by exact_mod_cast hq)
    have h0' : (Pi.single 0 x : Fin 8 → X) = 0 := 𝔪.e₈.injective (h0.trans (map_zero _).symm)
    simpa using congrFun h0' 0
  rw [ThetaSys.HH]
  exact mem_closure_iff (X₁.ρ.n) (j + X₁.ρ.k * 2) hJ hN hG htor htf h1 h2 h3 h4 _
    (fun b hb => GlobalTheory.T.thetaLabel_class_zero_of_divides_all_thetaConstants g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 b hb)
    (fun b hb => GlobalTheory.T.exists_torsionTranslate_label_thetaConstant_divides_all g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hx₀ b hb) a

end GlobalTheory.Poinc.Sep
