import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleLevelMapsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStableOfNoBoundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvolutionRealPlacePairs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists

noncomputable section

namespace GlobalTheory.GalTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section ModN

theorem modN_zero (n : ℕ) : D.ModN n 0 := ⟨0, (smul_zero _).symm⟩

theorem modN_add {n : ℕ} {x y : D.La} (hx : D.ModN n x) (hy : D.ModN n y) : D.ModN n (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, (smul_add _ _ _).symm⟩

theorem modN_neg {n : ℕ} {x : D.La} (hx : D.ModN n x) : D.ModN n (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, (smul_neg _ _).symm⟩

theorem modN_sub {n : ℕ} {x y : D.La} (hx : D.ModN n x) (hy : D.ModN n y) : D.ModN n (x - y) := by
  rw [sub_eq_add_neg]; exact modN_add hx (modN_neg hy)

theorem modN_smul {n : ℕ} (c : 𝓞 E) {x : D.La} (hx : D.ModN n x) : D.ModN n (c • x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨c • a, smul_comm c n a⟩

theorem modN_nsmul (n : ℕ) (x : D.La) : D.ModN n (n • x) := ⟨x, rfl⟩

theorem modN_of_mul {n m : ℕ} {x : D.La} (h : D.ModN (n * m) x) : D.ModN n x := by
  obtain ⟨a, rfl⟩ := h; exact ⟨m • a, mul_smul n m a⟩

theorem modN_trans {n : ℕ} {a b c : D.La} (h₁ : D.ModN n (a - b)) (h₂ : D.ModN n (b - c)) : D.ModN n (a - c) := by
  have := modN_add h₁ h₂; rwa [sub_add_sub_cancel] at this

theorem modN_symm {n : ℕ} {a b : D.La} (h : D.ModN n (a - b)) : D.ModN n (b - a) := by
  have := modN_neg h; rwa [neg_sub] at this

theorem modN_of_sub {n : ℕ} {a b : D.La} (h : D.ModN n (a - b)) (hb : D.ModN n b) : D.ModN n a := by
  have := modN_add h hb; rwa [sub_add_cancel] at this

theorem dvd_EF_sub {n : ℕ} {a a' b b' : D.La} (ha : D.ModN n (a - a')) (hb : D.ModN n (b - b')) :
    (n : ℤ) ∣ D.EF a b - D.EF a' b' := by
  obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb
  rw [sub_eq_iff_eq_add] at hx hy
  subst hx hy
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
  exact ⟨D.EF x b' + D.EF a' y + n * D.EF x y, by ring⟩

end ModN

structure IsSemiIso (D : Datum H) (τ : 𝓞 E ≃+* 𝓞 E) (f : ℕ → D.La → D.La) : Prop where
  add : ∀ n, 0 < n → ∀ a b, D.ModN n (f n (a + b) - (f n a + f n b))
  semi : ∀ n, 0 < n → ∀ (c : 𝓞 E) a, D.ModN n (f n (c • a) - τ c • f n a)
  tower : ∀ n m, 0 < n → 0 < m → ∀ a, D.ModN n (f (n * m) a - f n a)
  onto : ∀ n, 0 < n → ∀ a, ∃ b, D.ModN n (f n b - a)
  inj : ∀ n, 0 < n → ∀ a, D.ModN n (f n a) → D.ModN n a
  isom : ∀ n : ℕ, 0 < n → ∀ a b, (n : ℤ) ∣ D.EF (f n a) (f n b) - D.EF a b

namespace IsSemiIso

variable {τ : 𝓞 E ≃+* 𝓞 E} {f : ℕ → D.La → D.La} (hf : IsSemiIso D τ f)
include hf

theorem sub {n : ℕ} (hn : 0 < n) (a b : D.La) : D.ModN n (f n (a - b) - (f n a - f n b)) := by
  have h := hf.add n hn (a - b) b
  rw [sub_add_cancel] at h
  have e : f n (a - b) - (f n a - f n b) = -(f n a - (f n (a - b) + f n b)) := by abel
  rw [e]; exact modN_neg h

theorem congr {n : ℕ} (hn : 0 < n) {a b : D.La} (h : D.ModN n (a - b)) : D.ModN n (f n a - f n b) := by
  obtain ⟨c, hc⟩ := h
  have h1 := hf.sub hn a b
  rw [hc] at h1
  have h2 := hf.semi n hn (n : 𝓞 E) c
  simp only [map_natCast, Nat.cast_smul_eq_nsmul] at h2
  have h3 : D.ModN n (f n (n • c)) := modN_of_sub h2 (modN_nsmul _ _)
  exact modN_of_sub (modN_symm h1) h3

theorem modN_map {n : ℕ} (hn : 0 < n) {a : D.La} (h : D.ModN n a) : D.ModN n (f n a) := by
  have h0 : D.ModN n (f n 0) := by
    have := hf.add n hn 0 0
    rw [add_zero] at this
    have e : f n 0 = -(f n 0 - (f n 0 + f n 0)) := by abel
    rw [e]; exact modN_neg this
  exact modN_of_sub (hf.congr hn (by rwa [sub_zero])) h0

theorem mem_smul_top {n : ℕ} (hn : 0 < n) {J : Ideal (𝓞 E)} (hJ : ∀ x ∈ J, τ x ∈ J) (hnJ : (n : 𝓞 E) ∈ J)
    {a : D.La} (ha : a ∈ J • (⊤ : Submodule (𝓞 E) D.La)) : f n a ∈ J • (⊤ : Submodule (𝓞 E) D.La) := by
  have hM : ∀ x : D.La, D.ModN n x → x ∈ J • (⊤ : Submodule (𝓞 E) D.La) := by
    rintro _ ⟨b, rfl⟩
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hnJ Submodule.mem_top
  refine Submodule.smul_induction_on ha (fun r hr x _ => ?_) (fun x y hx hy => ?_)
  · have h := hf.semi n hn r x
    have e : f n (r • x) = (f n (r • x) - τ r • f n x) + τ r • f n x := by abel
    rw [e]
    exact Submodule.add_mem _ (hM _ h) (Submodule.smul_mem_smul (hJ r hr) Submodule.mem_top)
  · have h := hf.add n hn x y
    have e : f n (x + y) = (f n (x + y) - (f n x + f n y)) + (f n x + f n y) := by abel
    rw [e]
    exact Submodule.add_mem _ (hM _ h) (Submodule.add_mem _ hx hy)

end IsSemiIso

theorem exists_inv {τ : 𝓞 E ≃+* 𝓞 E} {f : ℕ → D.La → D.La} (hf : IsSemiIso D τ f) :
    ∃ g : ℕ → D.La → D.La, IsSemiIso D τ.symm g ∧ (∀ n, 0 < n → ∀ a, D.ModN n (f n (g n a) - a)) ∧
      ∀ n, 0 < n → ∀ a, D.ModN n (g n (f n a) - a) := by
  classical
  let g : ℕ → D.La → D.La := fun n a => if h : 0 < n then Classical.choose (hf.onto n h a) else a
  have fg : ∀ n, 0 < n → ∀ a, D.ModN n (f n (g n a) - a) := fun n hn a => by
    simp only [g, dif_pos hn]; exact Classical.choose_spec (hf.onto n hn a)
  have inj2 : ∀ n, 0 < n → ∀ x y, D.ModN n (f n x - f n y) → D.ModN n (x - y) := fun n hn x y h =>
    hf.inj n hn _ (modN_of_sub (hf.sub hn x y) h)
  have gf : ∀ n, 0 < n → ∀ a, D.ModN n (g n (f n a) - a) := fun n hn a => inj2 n hn _ _ (fg n hn (f n a))
  refine ⟨g, ⟨fun n hn a b => ?_, fun n hn c a => ?_, fun n m hn hm a => ?_, fun n hn a => ⟨f n a, gf n hn a⟩,
    fun n hn a h => modN_of_sub (modN_symm (fg n hn a)) (hf.modN_map hn h), fun n hn a b => ?_⟩, fg, gf⟩
  · refine inj2 n hn _ _ (modN_trans (fg n hn (a + b)) (modN_symm ?_))
    have e : f n (g n a + g n b) - (a + b) = (f n (g n a + g n b) - (f n (g n a) + f n (g n b))) +
        ((f n (g n a) - a) + (f n (g n b) - b)) := by abel
    rw [e]
    exact modN_add (hf.add n hn _ _) (modN_add (fg n hn a) (fg n hn b))
  · refine inj2 n hn _ _ (modN_trans (fg n hn (c • a)) (modN_symm ?_))
    have e : f n (τ.symm c • g n a) - c • a = (f n (τ.symm c • g n a) - τ (τ.symm c) • f n (g n a)) +
        c • (f n (g n a) - a) := by rw [RingEquiv.apply_symm_apply, smul_sub]; abel
    rw [e]
    exact modN_add (hf.semi n hn _ _) (modN_smul c (fg n hn a))
  · refine inj2 n hn _ _ ?_
    have e : f n (g (n * m) a) - f n (g n a) = -(f (n * m) (g (n * m) a) - f n (g (n * m) a)) +
        (f (n * m) (g (n * m) a) - a) - (f n (g n a) - a) := by abel
    rw [e]
    exact modN_sub (modN_add (modN_neg (hf.tower n m hn hm _))
      (modN_of_mul (fg (n * m) (Nat.mul_pos hn hm) a))) (fg n hn a)
  · have h1 := hf.isom n hn (g n a) (g n b)
    have h2 := dvd_EF_sub (fg n hn a) (fg n hn b)
    have := dvd_sub h2 h1
    rwa [sub_sub_sub_cancel_left] at this

theorem rt_fix {τ : 𝓞 E ≃+* 𝓞 E} (hτ : τ H.w0 = H.w0) : τ H.rt = H.rt := by
  have h := congrArg τ H.two_weight_eq_one_add_root
  rw [map_mul, map_ofNat, hτ, H.two_weight_eq_one_add_root, map_add, map_one] at h
  exact (add_left_cancel h).symm

theorem symm_w0 {τ : 𝓞 E ≃+* 𝓞 E} (hτ : τ H.w0 = H.w0) : τ.symm H.w0 = H.w0 :=
  (τ.symm_apply_eq).2 hτ.symm

section Tate

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem act_one (I : TateIso D k Q act e) (c : 𝓞 E) : act c 1 = 1 := by
  have h0 : I.ev 1 0 = 1 := by
    have := I.add 1 0 0
    rw [add_zero] at this
    exact left_eq_mul.mp this
  have := I.lin 1 c 0
  rw [smul_zero, h0] at this
  exact this.symm

def tateTw (τ : 𝓞 E ≃+* 𝓞 E) (f : ℕ → D.La → D.La) (hf : IsSemiIso D τ f) (I : TateIso D k Q act e) :
    TateIso D k Q (fun c => act (τ c)) e where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := if n = 0 then 1 else I.ev n (f n a)
  add n a b := by
    split_ifs with hn
    · simp
    · rw [← I.add]
      exact GlobalTheory.LevelTwist.ev_congr I (Nat.pos_of_ne_zero hn) (hf.add _ (Nat.pos_of_ne_zero hn) a b)
  lin n c a := by
    split_ifs with hn
    · exact (act_one I (τ c)).symm
    · rw [← I.lin]
      exact GlobalTheory.LevelTwist.ev_congr I (Nat.pos_of_ne_zero hn) (hf.semi _ (Nat.pos_of_ne_zero hn) c a)
  ker n hn a := by
    rw [if_neg hn.ne', I.ker n hn]
    exact ⟨fun h => hf.inj n hn a h, fun h => hf.modN_map hn h⟩
  onto n hn x := by
    simp only [hn.ne', if_false]
    rw [I.onto n hn]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hf.onto n hn a
      exact ⟨b, GlobalTheory.LevelTwist.ev_congr I hn hb⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
  tower n m hn hm a := by
    rw [if_neg (Nat.mul_pos hn hm).ne', if_neg hn.ne', I.tower n m hn hm]
    exact GlobalTheory.LevelTwist.ev_congr I hn (hf.tower n m hn hm a)
  isom n hn a b := by
    rw [if_neg hn.ne', if_neg hn.ne', ← GlobalTheory.LevelTwist.zeta_zpow_congr I hn (hf.isom n hn a b)]
    exact I.isom n hn _ _

end Tate

section Lie

variable {S : Scheme.{0}} {k : Type} [Field k]

theorem isLieEigen_twist (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0) (t : SAB H S) (x : Sp k ⟶ S) (κ : 𝓞 E →+* k)
    (v : epsPt x ⟶ t.G) :
    IsLieEigen (GlobalTheory.FiniteStable.twist τ hτ t).act x κ v ↔ IsLieEigen t.act x (κ.comp τ.symm.toRingHom) v := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a => ?_⟩
    have := h2 (τ.symm a)
    simpa [GlobalTheory.FiniteStable.twist] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a => ?_⟩
    have := h2 (τ a)
    simpa [GlobalTheory.FiniteStable.twist] using this

theorem lieMult_twist (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0) (t : SAB H S) (x : Sp k ⟶ S) (κ : 𝓞 E →+* k)
    (n : ℕ) : LieMult (GlobalTheory.FiniteStable.twist τ hτ t).act x κ n ↔ LieMult t.act x (κ.comp τ.symm.toRingHom) n := by
  constructor
  · rintro ⟨v, hv, hw⟩
    exact ⟨v, fun i => (isLieEigen_twist τ hτ t x κ _).1 (hv i),
      fun w h => hw w ((isLieEigen_twist τ hτ t x κ _).2 h)⟩
  · rintro ⟨v, hv, hw⟩
    exact ⟨v, fun i => (isLieEigen_twist τ hτ t x κ _).2 (hv i),
      fun w h => hw w ((isLieEigen_twist τ hτ t x κ _).1 h)⟩

theorem detCond_twist (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0) (t : SAB H S) (x : Sp k ⟶ S) (ρ : k)
    (h : DetCond D t.act x ρ) : DetCond D (GlobalTheory.FiniteStable.twist τ hτ t).act x ρ := by
  intro κ
  have e : (κ.comp τ.symm.toRingHom) H.rt = κ H.rt := by
    simp [rt_fix (symm_w0 hτ)]
  obtain ⟨h1, h2⟩ := h (κ.comp τ.symm.toRingHom)
  exact ⟨fun hk => (lieMult_twist τ hτ t x κ _).2 (h1 (e.trans hk)),
    fun hk => (lieMult_twist τ hτ t x κ _).2 (h2 (by rw [e]; exact hk))⟩

end Lie

section Level

theorem M_pos (l : Level H) : 0 < l.M := by have := l.three_le; omega

theorem M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  rw [l.prod]; exact Ideal.mem_span_singleton_self _

theorem M_mem_Mb (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb :=
  Ideal.mul_le_left (M_mem l)

theorem M_mem_Mbbar (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) :=
  Ideal.mul_le_right (M_mem l)

theorem mb_stable (l : Level H) {τ : 𝓞 E ≃+* 𝓞 E} (hτ : τ H.w0 = H.w0) : ∀ x ∈ l.Mb, τ x ∈ l.Mb := by
  have fix : ∀ a ∈ Algebra.adjoin ℤ {H.w0}, τ a = a := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hτ]
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  intro x hx
  rw [l.fromK] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => rw [fix y hy.2]; exact Submodule.subset_span hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hy

theorem mbbar_stable (l : Level H) {τ : 𝓞 E ≃+* 𝓞 E} (hτ : τ H.w0 = H.w0) :
    ∀ x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), τ x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_of_equiv H.bar x).1 hx
  rw [GlobalTheory.FiniteStable.aut_bar]
  exact Ideal.mem_map_of_mem _ (mb_stable l hτ y hy)

end Level

section Obj

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def objTw (o : Obj D l b s) (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0) (f : ℕ → D.La → D.La) (hf : IsSemiIso D τ f) :
    Obj D l b s where
  t := GlobalTheory.FiniteStable.twist τ hτ o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta a := o.eta (f l.M a)
  eta_add a c := by
    rw [← o.eta_add]
    exact GlobalTheory.Moduli.LevelAction.eta_congr o (GlobalTheory.Moduli.LevelAction.mem_of_modN l (hf.add _ (M_pos l) a c))
  eta_ker a ha := o.eta_ker _ (hf.mem_smul_top (M_pos l) (mb_stable l hτ) (M_mem_Mb l) ha)
  etaA a := o.etaA (f l.A a)
  etaA_add a c := by
    rw [← o.etaA_add]
    exact GlobalTheory.Moduli.LevelAction.etaA_congr o (hf.add _ l.A_pos a c)
  etaA_ker a := by
    obtain ⟨c, hc⟩ := hf.modN_map l.A_pos (modN_nsmul l.A a)
    show o.etaA (f l.A (l.A • a)) = 1
    rw [hc, o.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, hζ, hA', hM⟩ := o.geom k x β hx
    refine ⟨detCond_twist τ hτ o.t x _ hd, tateTw τ f hf I, hζ, fun a => ?_, fun a ha => ?_⟩
    · show toUnit _ ≫ o.etaA (f l.A a) = if l.A = 0 then 1 else I.ev l.A (f l.A a)
      rw [if_neg l.A_pos.ne', hA']
    · show toUnit _ ≫ o.eta (f l.M a) = if l.M = 0 then 1 else I.ev l.M (f l.M a)
      rw [if_neg (M_pos l).ne']
      exact hM _ (hf.mem_smul_top (M_pos l) (mbbar_stable l hτ) (M_mem_Mbbar l) ha)

end Obj

section Maps

variable {S S' : Scheme.{0}}

def twSab (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0) {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    SABMap (GlobalTheory.FiniteStable.twist τ hτ t') (GlobalTheory.FiniteStable.twist τ hτ t) f :=
  ⟨m.cm, m.cart, m.base, fun a => m.act (τ a), m.lin⟩

def idTw (τ τ' : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0) (hτ' : τ' H.w0 = H.w0) (e : ∀ a, τ (τ' a) = a) (t : SAB H S) :
    SABMap t (GlobalTheory.FiniteStable.twist τ' hτ' (GlobalTheory.FiniteStable.twist τ hτ t)) (𝟙 S) :=
  ⟨(GlobalTheory.LevelTwist.sabMapId t).cm, (GlobalTheory.LevelTwist.sabMapId t).cart, rfl, fun a => by
    show (t.act.act a).left ≫ 𝟙 _ = 𝟙 _ ≫ (t.act.act (τ (τ' a))).left
    rw [e]; simp, (GlobalTheory.LevelTwist.sabMapId t).lin⟩

end Maps

section Moduli

variable {l : Level H} (Xo : Moduli D l) (c : Coeff l)

theorem comp_eq_id
    (oF : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))
    (m0 : ObjMap oF Xo.univ (pullback.fst _ _))
    {τ τ' : 𝓞 E ≃+* 𝓞 E} (hτ : τ H.w0 = H.w0) (hτ' : τ' H.w0 = H.w0) (e : ∀ a, τ (τ' a) = a)
    {f f' : ℕ → D.La → D.La} (hf : IsSemiIso D τ f) (hf' : IsSemiIso D τ' f')
    (hinv : ∀ n, 0 < n → ∀ a, D.ModN n (f n (f' n a) - a))
    {r₁ r₂ : Xo.XF c ⟶ Xo.XF c} (k₁ : ObjMap (objTw oF τ hτ f hf) oF r₁) (k₂ : ObjMap (objTw oF τ' hτ' f' hf') oF r₂)
    (h₁ : r₁ ≫ pullback.snd _ _ = pullback.snd _ _) (h₂ : r₂ ≫ pullback.snd _ _ = pullback.snd _ _) :
    r₁ ≫ r₂ = 𝟙 _ := by
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.ObjMaps.exists_sab_comp (twSab τ' hτ' k₁.toSABMap) (idTw τ τ' hτ hτ' e oF.t)
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp k₂.toSABMap n₁
  have eta : ∀ a, (oF.eta a).left ≫ n₂.cm.F = ((𝟙 _ ≫ r₁) ≫ r₂) ≫ (oF.eta a).left := by
    intro a
    have e1 : oF.eta a = oF.eta (f l.M (f' l.M a)) :=
      GlobalTheory.Moduli.LevelAction.eta_congr oF (GlobalTheory.Moduli.LevelAction.mem_of_modN l (modN_symm (hinv _ (M_pos l) a)))
    have k1e : (oF.eta (f l.M (f' l.M a))).left ≫ k₁.cm.F = r₁ ≫ (oF.eta (f' l.M a)).left := k₁.eta (f' l.M a)
    have k2e : (oF.eta (f' l.M a)).left ≫ k₂.cm.F = r₂ ≫ (oF.eta a).left := k₂.eta a
    change (oF.eta a).left ≫ n₂.φ = _
    rw [hn₂, hn₁]
    change (oF.eta a).left ≫ (𝟙 _ ≫ k₁.cm.F) ≫ k₂.cm.F = _
    calc (oF.eta a).left ≫ (𝟙 _ ≫ k₁.cm.F) ≫ k₂.cm.F
        = ((oF.eta (f l.M (f' l.M a))).left ≫ k₁.cm.F) ≫ k₂.cm.F := by
          rw [← e1]; erw [Category.id_comp, Category.assoc]
      _ = r₁ ≫ r₂ ≫ (oF.eta a).left := by rw [k1e]; erw [Category.assoc]; rw [k2e]
      _ = ((𝟙 _ ≫ r₁) ≫ r₂) ≫ (oF.eta a).left := by simp
  have etaA : ∀ a, (oF.etaA a).left ≫ n₂.cm.F = ((𝟙 _ ≫ r₁) ≫ r₂) ≫ (oF.etaA a).left := by
    intro a
    have e1 : oF.etaA a = oF.etaA (f l.A (f' l.A a)) :=
      GlobalTheory.Moduli.LevelAction.etaA_congr oF (modN_symm (hinv _ l.A_pos a))
    have k1e : (oF.etaA (f l.A (f' l.A a))).left ≫ k₁.cm.F = r₁ ≫ (oF.etaA (f' l.A a)).left := k₁.etaA (f' l.A a)
    have k2e : (oF.etaA (f' l.A a)).left ≫ k₂.cm.F = r₂ ≫ (oF.etaA a).left := k₂.etaA a
    change (oF.etaA a).left ≫ n₂.φ = _
    rw [hn₂, hn₁]
    change (oF.etaA a).left ≫ (𝟙 _ ≫ k₁.cm.F) ≫ k₂.cm.F = _
    calc (oF.etaA a).left ≫ (𝟙 _ ≫ k₁.cm.F) ≫ k₂.cm.F
        = ((oF.etaA (f l.A (f' l.A a))).left ≫ k₁.cm.F) ≫ k₂.cm.F := by
          rw [← e1]; erw [Category.id_comp, Category.assoc]
      _ = r₁ ≫ r₂ ≫ (oF.etaA a).left := by rw [k1e]; erw [Category.assoc]; rw [k2e]
      _ = ((𝟙 _ ≫ r₁) ≫ r₂) ≫ (oF.etaA a).left := by simp
  let k : ObjMap oF oF ((𝟙 _ ≫ r₁) ≫ r₂) := { toSABMap := n₂, eta := eta, etaA := etaA }
  obtain ⟨-, hcc⟩ := GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ oF oF
  obtain ⟨k', -⟩ := (hcc (pullback.fst _ _) ((𝟙 _ ≫ r₁) ≫ r₂) m0).1 k
  have hred := GlobalTheory.TransitionUnique.isReduced_XF Xo c
  have hg : ((𝟙 _ ≫ r₁) ≫ r₂) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [Category.id_comp, Category.assoc, h₂, h₁]
  have hs : (((𝟙 _ ≫ r₁) ≫ r₂) ≫ pullback.fst _ _) ≫ Xo.s = pullback.fst _ _ ≫ Xo.s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg]
  have u := (Xo.rep _ _ hred oF).unique ⟨hs, ⟨k'⟩⟩ ⟨rfl, ⟨m0⟩⟩
  apply pullback.hom_ext
  · calc (r₁ ≫ r₂) ≫ pullback.fst _ _ = ((𝟙 _ ≫ r₁) ≫ r₂) ≫ pullback.fst _ _ := by rw [Category.id_comp]
      _ = pullback.fst _ _ := u
      _ = 𝟙 _ ≫ pullback.fst _ _ := (Category.id_comp _).symm
  · calc (r₁ ≫ r₂) ≫ pullback.snd _ _ = pullback.snd _ _ := by rw [Category.assoc, h₂, h₁]
      _ = 𝟙 _ ≫ pullback.snd _ _ := (Category.id_comp _).symm

end Moduli

section Moduli

variable {l : Level H} (Xo : Moduli D l) (c : Coeff l)

theorem exists_twist
    (oF : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))
    (m0 : ObjMap oF Xo.univ (pullback.fst _ _)) (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0)
    {f : ℕ → D.La → D.La} (hf : IsSemiIso D σ.symm f) :
    ∃ r : Xo.XF c ≅ Xo.XF c, Nonempty (GlobalTheory.ShFam.TwMap σ oF.t oF.t r.hom) ∧
      r.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  obtain ⟨g, hg, hfg, hgf⟩ := exists_inv hf
  have hg' : IsSemiIso D σ g := by simpa using hg
  have hred := GlobalTheory.TransitionUnique.isReduced_XF Xo c
  have hσ' := symm_w0 hσ
  obtain ⟨f₁, ⟨hf₁, ⟨m₁⟩⟩, -⟩ := Xo.rep _ _ hred (objTw oF σ.symm hσ' f hf)
  obtain ⟨f₂, ⟨hf₂, ⟨m₂⟩⟩, -⟩ := Xo.rep _ _ hred (objTw oF σ hσ g hg')
  let r₁ : Xo.XF c ⟶ Xo.XF c := pullback.lift f₁ (pullback.snd _ _) (by rw [hf₁, pullback.condition])
  let r₂ : Xo.XF c ⟶ Xo.XF c := pullback.lift f₂ (pullback.snd _ _) (by rw [hf₂, pullback.condition])
  have e₁ : r₁ ≫ pullback.fst _ _ = f₁ := pullback.lift_fst _ _ _
  have e₂ : r₂ ≫ pullback.fst _ _ = f₂ := pullback.lift_fst _ _ _
  have s₁ : r₁ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have s₂ : r₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  obtain ⟨-, hc₁⟩ := GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ oF (objTw oF σ.symm hσ' f hf)
  obtain ⟨k₁, -⟩ := (hc₁ (pullback.fst _ _) r₁ m0).2 (by rw [e₁]; exact m₁)
  obtain ⟨-, hc₂⟩ := GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ oF (objTw oF σ hσ g hg')
  obtain ⟨k₂, -⟩ := (hc₂ (pullback.fst _ _) r₂ m0).2 (by rw [e₂]; exact m₂)
  refine ⟨⟨r₁, r₂, comp_eq_id Xo c oF m0 hσ' hσ (fun a => σ.symm_apply_apply a) hf hg' hfg k₁ k₂ s₁ s₂,
    comp_eq_id Xo c oF m0 hσ hσ' (fun a => σ.apply_symm_apply a) hg' hf hgf k₂ k₁ s₂ s₁⟩, ⟨?_⟩, s₁⟩
  exact ⟨k₁.cm, k₁.cart, k₁.base, fun a => by
    have := k₁.act (σ a)
    simpa [GlobalTheory.FiniteStable.twist, objTw] using this, k₁.lin⟩

end Moduli

end GlobalTheory.GalTwist

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open CategoryTheory

namespace GlobalTheory.GalTwist

theorem twist_aut : Hypotheses2 → ∀ (D : D7) (O : Setup D), O.Core → ∀ h ∈ D.R.Psi,
    ∃ (σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E) (r : (O.S.Xo O.κ.l).XF O.κ.c ≅ (O.S.Xo O.κ.l).XF O.κ.c),
      (∀ a : 𝓞 D.host.E, ((σ a : 𝓞 D.host.E) : D.host.E) = D.host.sigmaOf h (a : D.host.E)) ∧
      σ O.A.H.w0 = O.A.H.w0 ∧ Nonempty (GlobalTheory.ShFam.TwMap σ O.s.T.Z.oF.t O.s.T.Z.oF.t r.hom) ∧
      r.hom ≫ CategoryTheory.Limits.pullback.snd _ _ = CategoryTheory.Limits.pullback.snd _ _ := by
  intro _ D O _ h hh
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (D.host.sigmaOf h).toRingEquiv
  have hs : ∀ a : 𝓞 D.host.E, ((σ a : 𝓞 D.host.E) : D.host.E) = D.host.sigmaOf h (a : D.host.E) := fun a => rfl
  have hrt : σ O.A.H.rt = O.A.H.rt := by
    apply RingOfIntegers.ext
    rw [hs, O.A.rt_eq]
    exact GlobalTheory.InertiaPairs.sigmaOf_sqrt_pos D.host h hh
  have hw : σ O.A.H.w0 = O.A.H.w0 := by
    have h2 := congrArg σ O.A.H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add, map_one, hrt, ← O.A.H.two_weight_eq_one_add_root] at h2
    exact mul_left_cancel₀ two_ne_zero h2
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.T.exists_compatible_level_maps O.A.H O.S.Dw σ.symm (symm_w0 hw)
  have hf : IsSemiIso O.S.Dw σ.symm (fun n a => f n a) :=
    ⟨fun n _ a b => by rw [map_add, sub_self]; exact modN_zero n, hf1, hf2, hf3, hf4, hf5⟩
  obtain ⟨r, hr, hsnd⟩ := exists_twist (O.S.Xo O.κ.l) O.κ.c O.s.T.Z.oF O.s.T.Z.m0 σ hw hf
  exact ⟨σ, r, hs, hw, hr, hsnd⟩

end GlobalTheory.GalTwist
