import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.HT.TateTransportO

theorem exists_torsLift {G H : Type} [Group G] [Group H] (p : ℕ) (ρ : G →* H)
    (hi : ∀ n, 0 < n → n.Coprime p → ∀ g h : G, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) :
    ∃ L : H → G, ∀ n, 0 < n → n.Coprime p → ∀ g : G, g ^ n = 1 → L (ρ g) = g := by
  classical
  refine ⟨fun x => if h : ∃ g : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g ^ n = 1) ∧ ρ g = x then h.choose else 1, ?_⟩
  intro n hn hnp g hg
  have h : ∃ g' : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g' ^ n = 1) ∧ ρ g' = ρ g := ⟨g, ⟨n, hn, hnp, hg⟩, rfl⟩
  simp only [dif_pos h]
  obtain ⟨⟨m, hm, hmp, hgm⟩, he⟩ := h.choose_spec
  exact hi (m * n) (Nat.mul_pos hm hn) (Nat.Coprime.mul hmp hnp) _ _
    (by rw [pow_mul, hgm, one_pow]) (by rw [mul_comm, pow_mul, hg, one_pow]) he

theorem transport_alg :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p)
    {R k k' QR Q Q' : Type} [CommRing R] [Field k] [Field k'] [Group QR] [Group Q] [Group Q'],
    (∀ a b : QR, a * b = b * a) →
    ∀ (actR : D.O → QR → QR) (act : D.O → Q → Q) (act' : D.O → Q' → Q')
    (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → k'ˣ → Prop)
    (ρ : QR →* Q) (ρ' : QR →* Q') (φ : Rˣ →* kˣ) (φ' : Rˣ →* k'ˣ),
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) →
    (∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ g = x) →
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h) →
    (∀ n, 0 < n → n.Coprime p → ∀ x : Q', x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ' g = x) →
    (∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ u = φ v → u = v) →
    (∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ φ u = z) →
    (∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ' u = φ' v → u = v) →
    (∀ c g h, actR c (g * h) = actR c g * actR c h) →
    (∀ c g, ρ (actR c g) = act c (ρ g)) → (∀ c g, ρ' (actR c g) = act' c (ρ' g)) →
    (∀ c, act' c 1 = 1) →
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 →
      ∃ u : Rˣ, u ^ n = 1 ∧ e n (ρ g) (ρ h) (φ u) ∧ e' n (ρ' g) (ρ' h) (φ' u)) →
    (∀ n, 0 < n → n.Coprime p → ∀ x y c c', e n x y c → e n x y c' → c = c') →
    ∀ (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e),
    ∃ I' : GlobalTheory.UPel.HT.TateIsoO D k' Q' act' e', ∀ n, 0 < n → n.Coprime p → ∀ a (g : QR), g ^ n = 1 →
      ρ g = I.ev n a → ρ' g = I'.ev n a := by
  intro p _ D R k k' QR Q Q' _ _ _ _ _ _ hcomm actR act act' e e' ρ ρ' φ φ' hρi hρs hρ'i hρ's hφi hφs hφ'i
    hactR hρact hρ'act hact'1 hpair huniq I
  obtain ⟨L, hL⟩ := exists_torsLift p ρ hρi
  obtain ⟨W, hW⟩ := exists_torsLift p φ hφi
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

end GlobalTheory.UPel.HT.TateTransportO
