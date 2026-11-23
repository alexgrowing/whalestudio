import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubNSucc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormRepGeneratorsAndThetaSeriesTerm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQT

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition
open scoped BigOperators
noncomputable section
namespace GlobalTheory.SeriesCompare
section Alg
variable {O : Type} [CommRing O] {N : NumD O}

theorem wp_level {k m L : ℕ} (hL : L = k * m) (P Q : N.QT L) (p q : N.QT k) (h₁ : p.1.1 = P.1.1) (h₂ : p.1.2 = P.1.2 ^ m)
    (h₃ : Q.1.1.toAdd = m • q.1.1.toAdd) (h₄ : Q.1.2 = q.1.2) : N.wp P Q = N.wp p q := by
  have a := WpPairing.s_nsmul N P.1.2 m q.1.1.toAdd
  have b := P.1.2.pow_s m q.1.1.toAdd
  have c := CubeBalance.cubN_mul N.cub m k q.1.2.b P.1.2.b
  have d := CubeBalance.cubN_mul N.cub k m P.1.2.b q.1.2.b
  have e := CubeBalance.cubN_swap N.cub k m q.1.2.b P.1.2.b
  rw [N.QT_pow_b] at c e
  rw [mul_comm m k, ← hL] at c
  rw [← hL] at d
  rw [NumD.wp, NumD.wp, NumD.tk, NumD.tk, NumD.tk, NumD.tk, h₁, h₂, h₃, h₄, NumD.Gt.pow_b, c, d]
  have E := fun {p q : Oˣ} (e : p = q) => congrArg Additive.ofMul e
  have a := E a; have b := E b; have e := E e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a b e ⊢
  linear_combination (norm := abel) a - b - e

def cg (N : NumD O) : N.Gt →* N.Gt ⧸ N.ioHom.range := QuotientGroup.mk' _

theorem cg_eq_one {g : N.Gt} : cg N g = 1 ↔ ∃ y, g = N.io y :=
  (QuotientGroup.eq_one_iff g).trans ⟨fun ⟨y, h⟩ => ⟨y.toAdd, h.symm⟩, fun ⟨y, h⟩ => ⟨Multiplicative.ofAdd y, h.symm⟩⟩

theorem cg_pow {k : ℕ} (p : N.QT k) : cg N p.1.2 ^ k = 1 := by
  rw [← map_pow]; exact cg_eq_one.2 ⟨_, N.mem_QT.1 p.2⟩

theorem exists_rep {g : N.Gt} {d : ℕ} (h : cg N g ^ d = 1) : ∃ p : N.QT d, p.1.2 = g := by
  rw [← map_pow] at h
  obtain ⟨y, hy⟩ := cg_eq_one.1 h
  exact ⟨⟨(Multiplicative.ofAdd y, g), hy⟩, rfl⟩

theorem cg_of_qEq {k : ℕ} {p p' : N.QT k} (h : N.QEq p p') : cg N p.1.2 = cg N p'.1.2 := by
  obtain ⟨z, -, h⟩ := h
  rw [h, map_mul, cg_eq_one.2 ⟨z, rfl⟩, mul_one]

theorem qEq_iff_cg (hio : Function.Injective N.io) {k : ℕ} {p p' : N.QT k} : N.QEq p p' ↔ cg N p.1.2 = cg N p'.1.2 := by
  refine ⟨cg_of_qEq, fun h => ?_⟩
  obtain ⟨z, hz⟩ := cg_eq_one.1 (show cg N (p.1.2⁻¹ * p'.1.2) = 1 by rw [map_mul, map_inv, h, inv_mul_cancel])
  have e : p'.1.2 = p.1.2 * N.io z := by rw [← hz, mul_inv_cancel_left]
  refine ⟨z, hio ?_, e⟩
  rw [N.io_add, N.io_nsmul, ← N.mem_QT.1 p.2, ← N.mem_QT.1 p'.2, e, mul_pow]

theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (h : N.QEq p p') (h' : N.QEq q q') : N.wp p q = N.wp p' q' := by
  rw [WpPairing.wp_congr_left N h, N.wp_swap q p', WpPairing.wp_congr_left N h', ← N.wp_swap]

def up {k m L : ℕ} (hL : L = k * m) (p : N.QT k) : N.QT L :=
  ⟨(p.1.1 ^ m, p.1.2), by rw [NumD.mem_QT, hL, pow_mul, N.mem_QT.1 p.2, toAdd_pow, NumD.io_nsmul]⟩

theorem wp_level_cg (hio : Function.Injective N.io) {k m L : ℕ} (hL : L = k * m) (P Q : N.QT L) (p q : N.QT k)
    (h₂ : cg N p.1.2 = cg N P.1.2 ^ m) (h₄ : cg N Q.1.2 = cg N q.1.2) : N.wp P Q = N.wp p q := by
  let p₀ : N.QT k := ⟨(P.1.1, P.1.2 ^ m), by rw [NumD.mem_QT, ← pow_mul, mul_comm m k, ← hL]; exact N.mem_QT.1 P.2⟩
  rw [wp_congr ((N.qEq_equivalence _).refl P) ((qEq_iff_cg hio (p' := up hL q)).2 h₄),
    wp_congr ((qEq_iff_cg hio (p' := p₀)).2 (h₂.trans (map_pow _ _ _).symm)) ((N.qEq_equivalence _).refl q)]
  exact wp_level hL _ _ _ _ rfl rfl rfl rfl
end Alg

theorem io_injective {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (h : N.Int q) :
    Function.Injective N.io := by
  refine fun a b hab => Multiplicative.ofAdd.injective ((injective_iff_map_eq_one N.ioHom).2 (fun y hy => ?_) hab)
  by_contra h0
  have e := h.norm_τ y.toAdd y.toAdd
  have t : N.τ y.toAdd y.toAdd = 1 := congrArg (fun g : N.Gt => g.s y.toAdd) hy
  rw [t, Units.val_one, norm_one, eq_comm, Real.exp_eq_one_iff, QuadraticMap.polar_self, neg_eq_zero, two_smul] at e
  have q0 : q y.toAdd = 0 := by linarith
  have inj : Function.Injective fun m : ℤ => m • y.toAdd := smul_left_injective ℤ (fun h => h0 h)
  have t₁ := h.pos.comp inj.tendsto_cofinite
  have : (q : N.X → ℝ) ∘ (fun m : ℤ => m • y.toAdd) = fun _ => 0 := funext fun m => by
    simp [QuadraticMap.map_smul, q0]
  rw [this] at t₁
  exact (Filter.not_tendsto_const_atTop (0 : ℝ) Filter.cofinite) t₁

section Tower
variable {C : Type} [Field C] {N N' : NumD C} {n : ℕ} (w : TowerIso N N' n)

def Gr (x : N.Gt ⧸ N.ioHom.range) (x' : N'.Gt ⧸ N'.ioHom.range) : Prop :=
  ∃ j a, cg N a.1.2 = x ∧ cg N' (w.io j a).1.2 = x'

theorem gr_up {j j' : ℕ} (h : j ≤ j') (a : N.QT ((n ^ j) ^ 2)) :
    ∃ a' : N.QT ((n ^ j') ^ 2), cg N a'.1.2 = cg N a.1.2 ∧ cg N' (w.io j' a').1.2 = cg N' (w.io j a).1.2 := by
  induction j', h using Nat.le_induction with
  | base => exact ⟨a, rfl, rfl⟩
  | succ i _ ih =>
    obtain ⟨b, h₁, h₂⟩ := ih
    have e : (n ^ (i + 1)) ^ 2 = (n ^ i) ^ 2 * n ^ 2 := by ring
    exact ⟨up e b, h₁, (cg_of_qEq (w.incl i b (up e b) (up e (w.io i b)) rfl rfl rfl rfl)).trans h₂⟩

variable {w}
theorem Gr.common {x y x' y'} (h : Gr w x x') (h' : Gr w y y') : ∃ j a b, cg N a.1.2 = x ∧ cg N' (w.io j a).1.2 = x' ∧
    cg N b.1.2 = y ∧ cg N' (w.io j b).1.2 = y' := by
  obtain ⟨i, a, rfl, rfl⟩ := h
  obtain ⟨j, b, rfl, rfl⟩ := h'
  obtain ⟨a', h₁, h₂⟩ := gr_up w (le_max_left i j) a
  obtain ⟨b', h₃, h₄⟩ := gr_up w (le_max_right i j) b
  exact ⟨_, a', b', h₁, h₂, h₃, h₄⟩

theorem Gr.mul {x y x' y'} (h : Gr w x x') (h' : Gr w y y') : Gr w (x * y) (x' * y') := by
  obtain ⟨j, a, b, rfl, rfl, rfl, rfl⟩ := h.common h'
  exact ⟨j, a * b, map_mul _ _ _, (cg_of_qEq (w.mul j a b)).trans (map_mul _ _ _)⟩

theorem gr_one : Gr w 1 1 := by
  refine ⟨0, 1, map_one _, ?_⟩
  have := (cg_of_qEq (w.mul 0 1 1)).trans (map_mul _ _ _)
  rw [mul_one] at this
  exact left_eq_mul.1 this

theorem Gr.pow {x x'} (h : Gr w x x') (m : ℕ) : Gr w (x ^ m) (x' ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact gr_one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul h

variable (hio : Function.Injective N.io) (hio' : Function.Injective N'.io)
include hio hio'
theorem Gr.eq_iff {x y x' y'} (h : Gr w x x') (h' : Gr w y y') : x = y ↔ x' = y' := by
  obtain ⟨j, a, b, rfl, rfl, rfl, rfl⟩ := h.common h'
  rw [← qEq_iff_cg hio, ← qEq_iff_cg hio', w.eqv]

theorem Gr.pow_eq_one_iff {x x'} (h : Gr w x x') (m : ℕ) : x ^ m = 1 ↔ x' ^ m = 1 := (h.pow m).eq_iff hio hio' gr_one

theorem Gr.wp (hd : ∀ (j : ℕ) (g : N.Gt), ∃ g' : N.Gt, g' ^ n ^ j = g) {k : ℕ} {p q : N.QT k} {p' q' : N'.QT k}
    (h : Gr w (cg N p.1.2) (cg N' p'.1.2)) (h' : Gr w (cg N q.1.2) (cg N' q'.1.2)) : N'.wp p' q' = N.wp p q := by
  obtain ⟨j, a, b, a₁, a₂, b₁, b₂⟩ := h.common h'
  obtain ⟨k₀, hk⟩ := Nat.gcd_dvd_left k ((n ^ j) ^ 2)
  obtain ⟨l₀, hl⟩ := Nat.gcd_dvd_right k ((n ^ j) ^ 2)
  generalize hdd : Nat.gcd k ((n ^ j) ^ 2) = d at hk hl
  have t₁ : cg N p.1.2 ^ d = 1 := hdd ▸ pow_gcd_eq_one.2 ⟨cg_pow p, a₁ ▸ cg_pow a⟩
  have t₂ : cg N q.1.2 ^ d = 1 := hdd ▸ pow_gcd_eq_one.2 ⟨cg_pow q, b₁ ▸ cg_pow b⟩
  obtain ⟨p₁, hp₁⟩ := exists_rep t₁
  obtain ⟨q₁, hq₁⟩ := exists_rep t₂
  obtain ⟨p₁', hp₁'⟩ := exists_rep ((h.pow_eq_one_iff hio hio' d).1 t₁)
  obtain ⟨q₁', hq₁'⟩ := exists_rep ((h'.pow_eq_one_iff hio hio' d).1 t₂)
  rw [wp_level_cg hio hk p q (p₁ ^ k₀) q₁ (by rw [← hp₁, ← map_pow]; rfl) (by rw [hq₁]),
    wp_level_cg hio' hk p' q' (p₁' ^ k₀) q₁' (by rw [← hp₁', ← map_pow]; rfl) (by rw [hq₁']),
    WpPairing.wp_pow_left, WpPairing.wp_pow_left]
  congr 1
  obtain ⟨g, hg⟩ := hd (j * 2) p.1.2
  have hg' : cg N (g ^ d) ^ l₀ = cg N p.1.2 := by rw [← map_pow, ← pow_mul, ← hl, ← pow_mul, hg]
  obtain ⟨P, hP⟩ := exists_rep (g := g ^ d) (d := (n ^ j) ^ 2) (by rw [hl, mul_comm, pow_mul, hg', t₁])
  have G : Gr w (cg N P.1.2 ^ l₀) (cg N' (w.io j P).1.2 ^ l₀) := Gr.pow ⟨j, P, rfl, rfl⟩ l₀
  rw [← wp_level_cg hio hl P b p₁ q₁ (by rw [hp₁, hP, hg']) (by rw [hq₁, b₁]),
    ← wp_level_cg hio' hl (w.io j P) (w.io j b) p₁' q₁'
      (by rw [hp₁']; exact (h.eq_iff hio hio' G).1 (by rw [hP, hg'])) (by rw [hq₁', b₂]), w.wp]
end Tower

section MatchTower
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}

def SameMatch (mt : Match N N' n) (w : TowerIso N N' n) : Prop :=
  ∀ j p p', mt.r ((n ^ j) ^ 2) p p' ↔ N'.QEq (w.io j p) p'

theorem exists_match (hio : Function.Injective N.io) (hio' : Function.Injective N'.io) (hn : n ≠ 0)
    (hd : ∀ (j : ℕ) (g : N.Gt), ∃ g' : N.Gt, g' ^ n ^ j = g)
    (hc : ∀ j (p p' : N'.QT ((n ^ j) ^ 2)), N'.QEq p p' → N'.tx (n ^ j) p' = N'.tx (n ^ j) p)
    (w : TowerIso N N' n) {c₀ : C} (h0 : c₀ ≠ 0) (hw : w.Proportional c₀) :
    ∃ mt : Match N N' n, mt.c₀ = c₀ ∧ SameMatch mt w := by
  have key : ∀ j (p : N.QT ((n ^ j) ^ 2)) (p' : N'.QT ((n ^ j) ^ 2)),
      Gr w (cg N p.1.2) (cg N' p'.1.2) ↔ N'.QEq (w.io j p) p' := fun j p p' => by
    have G : Gr w (cg N p.1.2) (cg N' (w.io j p).1.2) := ⟨j, p, rfl, rfl⟩
    rw [qEq_iff_cg hio']
    exact ⟨fun h => (G.eq_iff hio hio' h).1 rfl, fun h => h ▸ G⟩
  refine ⟨{
    r := fun k p p' => k ≠ 0 ∧ Gr w (cg N p.1.2) (cg N' p'.1.2)
    tot := fun j p => ?_
    cotot := fun j p' => ?_
    mul := fun k p q p' q' h h' => ⟨h.1, by
      have := h.2.mul h'.2
      rwa [← map_mul, ← map_mul] at this⟩
    eqv := fun k p q p' q' h e => ?_
    inj := fun k p q p' h h' => (qEq_iff_cg hio).2 ((h.2.eq_iff hio hio' h'.2).2 rfl)
    incl := fun k k' p p' q q' hk _ b _ d => by rw [b, d, mul_ne_zero_iff, and_iff_left hk]
    wp := fun k p q p' q' h h' => Gr.wp hio hio' hd h.2 h'.2
    c₀ := c₀
    c₀_ne := h0
    tx := fun j p p' h => ?_ }, rfl,
    fun j p p' => (and_iff_right (pow_ne_zero _ (pow_ne_zero _ hn))).trans (key j p p')⟩
  · have G : Gr w (cg N p.1.2) _ := ⟨j, up (sq (n ^ j)) p, rfl, rfl⟩
    obtain ⟨p', hp'⟩ := exists_rep ((G.pow_eq_one_iff hio hio' _).1 (cg_pow p))
    exact ⟨p', pow_ne_zero _ hn, hp' ▸ G⟩
  · obtain ⟨a, ha⟩ := w.onto j (up (sq (n ^ j)) p')
    have G : Gr w (cg N a.1.2) (cg N' p'.1.2) := ⟨j, a, rfl, cg_of_qEq ha⟩
    obtain ⟨p, hp⟩ := exists_rep ((G.pow_eq_one_iff hio hio' _).2 (cg_pow p'))
    exact ⟨p, pow_ne_zero _ hn, hp ▸ G⟩
  · rw [qEq_iff_cg hio', ← cg_of_qEq e]
    exact ⟨fun h' => (h.2.eq_iff hio hio' h'.2).1 rfl, fun h' => ⟨h.1, h' ▸ h.2⟩⟩
  · obtain ⟨v, h₁, h₂⟩ := hw j p
    rw [hc j _ _ ((key j p p').1 h.2), NumD.tx, NumD.tx, h₁.tsum_eq, h₂.tsum_eq]

theorem r_incl (mt : Match N N' n) {k m L : ℕ} (hL : L = k * m) (hm : m ≠ 0) (p : N.QT k) (p' : N'.QT k) (q : N.QT L)
    (q' : N'.QT L) (a : q.1.1 = p.1.1 ^ m) (b : q.1.2 = p.1.2) (c : q'.1.1 = p'.1.1 ^ m) (d : q'.1.2 = p'.1.2) :
    mt.r k p p' ↔ mt.r L q q' := by
  subst hL
  exact mt.incl k m p p' q q' hm a b c d

theorem exists_tower (hn : n ≠ 0) (mt : Match N N' n) : ∃ w : TowerIso N N' n, SameMatch mt w := by
  have t : ∀ j (p : N.QT ((n ^ j) ^ 2)), ∃ p', mt.r _ p p' := fun j => by rw [← pow_mul]; exact mt.tot _
  have t' : ∀ j (p' : N'.QT ((n ^ j) ^ 2)), ∃ p, mt.r _ p p' := fun j => by rw [← pow_mul]; exact mt.cotot _
  choose f hf using t
  have key : ∀ j p p', mt.r ((n ^ j) ^ 2) p p' ↔ N'.QEq (f j p) p' := fun j p p' =>
    mt.eqv _ p p _ _ (hf j p) ((N.qEq_equivalence _).refl p)
  exact ⟨{
    io := f
    eqv := fun j p q => ⟨fun h => mt.inj _ _ _ _ ((key j _ _).2 h) (hf j q), fun h => (mt.eqv _ _ _ _ _ (hf j p) h).1 (hf j q)⟩
    onto := fun j p' => (t' j p').imp fun p h => (key j _ _).1 h
    mul := fun j p q => (key j _ _).1 (mt.mul _ _ _ _ _ (hf j p) (hf j q))
    incl := fun j p q q' a b c d => (key _ _ _).1 ((r_incl mt (m := n ^ 2) (by ring) (pow_ne_zero _ hn) p (f j p) q q'
      (Multiplicative.toAdd.injective a) b (Multiplicative.toAdd.injective c) d).1 (hf j p))
    wp := fun j p q => mt.wp _ _ _ _ _ (hf j p) (hf j q) }, key⟩

theorem SameMatch.proportional {mt : Match N N' n} {w : TowerIso N N' n} (h : SameMatch mt w)
    (hs : ∀ j p, Summable (N.txT (n ^ j) p)) (hs' : ∀ j p, Summable (N'.txT (n ^ j) p)) : w.Proportional mt.c₀ :=
  fun j p => ⟨_, (hs j p).hasSum, by
    have := mt.tx j p _ ((h j p _).2 ((N'.qEq_equivalence _).refl _))
    rw [NumD.tx, NumD.tx] at this
    exact this ▸ (hs' j _).hasSum⟩
end MatchTower

section Sum
variable {C : Type} [NormedField C] [IsUltrametricDist C] [CompleteSpace C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem summable_evT (h : N.Int q) {m j : ℕ} (hm : m ≠ 0) (hj : j ≠ 0) (p : N.QT (m ^ 2)) (r : N.QT j) :
    Summable (N.evT m p r.1.2) := by
  obtain ⟨s, hs⟩ := exists_rep (g := (r.1.2 * p.1.2) ^ m) (d := m * j) (by
    rw [map_pow, ← pow_mul, ← mul_assoc, ← sq, map_mul, mul_pow, pow_mul (cg N p.1.2), cg_pow, mul_comm (m ^ 2) j, pow_mul,
      cg_pow, one_pow, one_pow, mul_one])
  have := summable_vt_QT C N q h _ (mul_ne_zero hm hj) s
  rw [hs] at this
  exact this.mul_left _

theorem summable_txT (h : N.Int q) {m : ℕ} (hm : m ≠ 0) (p : N.QT (m ^ 2)) : Summable (N.txT m p) :=
  (summable_evT h hm one_ne_zero p 1).congr (TateInh.evT_one N m p)
end Sum

section Hom
variable {O : Type} [CommRing O] {N N' : NumD O} (I : NumD.Hom (RingHom.id O) N N')

def gMap : N.Gt →* N'.Gt :=
  have H := NumD.hom_transport O O _ N N' I
  MonoidHom.mk' (fun g => (H.1 g).choose) fun g h =>
    (H.1 _).unique (H.1 _).choose_spec.1 (H.2.1 _ _ _ _ (H.1 g).choose_spec.1 (H.1 h).choose_spec.1)

theorem rel_iff {g : N.Gt} {g' : N'.Gt} : I.Rel g g' ↔ g' = gMap I g :=
  have H := (NumD.hom_transport O O _ N N' I).1 g
  ⟨fun h => H.unique h H.choose_spec.1, fun h => h ▸ H.choose_spec.1⟩

theorem gMap_io (y : N.X) : gMap I (N.io y) = N'.io (I.e y) :=
  ((rel_iff I).1 ((NumD.hom_transport O O _ N N' I).2.2.1 y)).symm

def qMap (k : ℕ) : N.QT k →* N'.QT k :=
  MonoidHom.mk' (fun p => ⟨(Multiplicative.ofAdd (I.e p.1.1.toAdd), gMap I p.1.2), by
    rw [NumD.mem_QT, ← map_pow, N.mem_QT.1 p.2]; exact gMap_io I _⟩)
    fun p q => Subtype.ext (Prod.ext (map_add I.e _ _) (map_mul (gMap I) _ _))

theorem qMap_iff {k : ℕ} {p : N.QT k} {p' : N'.QT k} :
    (p'.1.1.toAdd = I.e p.1.1.toAdd ∧ I.Rel p.1.2 p'.1.2) ↔ p' = qMap I k p :=
  ⟨fun h => Subtype.ext (Prod.ext h.1 ((rel_iff I).1 h.2)), fun h => h ▸ ⟨rfl, (rel_iff I).2 rfl⟩⟩

theorem qMap_qTriv (k : ℕ) (z : N.X) : qMap I k (N.qTriv k z) = N'.qTriv k (I.e z) :=
  Subtype.ext (Prod.ext (map_nsmul I.e k z) (gMap_io I z))

theorem qEq_qMap {k : ℕ} (hi : Function.Injective (qMap I k)) {p q : N.QT k} :
    N'.QEq (qMap I k p) (qMap I k q) ↔ N.QEq p q := by
  rw [NumD.qEq_iff, NumD.qEq_iff, ← I.e.exists_congr_right]
  exact exists_congr fun z => by rw [← hi.eq_iff, map_mul, qMap_qTriv]; rfl

theorem wp_qMap {k : ℕ} (p q : N.QT k) : N'.wp (qMap I k p) (qMap I k q) = N.wp p q :=
  (NumD.hom_transport O O _ N N' I).2.2.2.1 k p q _ _ rfl ((rel_iff I).2 rfl) rfl ((rel_iff I).2 rfl)
end Hom

section Move
variable {C : Type} [NormedField C] {N N' M M' : NumD C} {n : ℕ} (I : NumD.Hom (RingHom.id C) N M)
  (I' : NumD.Hom (RingHom.id C) N' M')

theorem hasSum_qMap (hl : I.lam = 1) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (v : C) :
    HasSum (M.txT m (qMap I _ p)) v ↔ HasSum (N.txT m p) v := by
  rw [← I.e.toEquiv.hasSum_iff]
  refine iff_of_eq (congrArg (HasSum · v) (funext fun χ => ?_))
  have := ((NumD.hom_transport C C _ N M I).2.2.2.2 m hm p (qMap I _ p) rfl ((rel_iff I).2 rfl) χ).1
  rw [hl, Units.val_one, one_mul] at this
  exact this

theorem summable_evT_of_qMap {m j : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (r : N.QT j)
    (h : Summable (M.evT m (qMap I _ p) (qMap I _ r).1.2)) : Summable (N.evT m p r.1.2) := by
  refine ((I.e.toEquiv.summable_iff.2 h).mul_left (((I.lam * I.h r.1.2.b ^ (m ^ 2))⁻¹ : Cˣ) : C)).congr fun χ => ?_
  have := ((NumD.hom_transport C C _ N M I).2.2.2.2 m hm p (qMap I _ p) rfl ((rel_iff I).2 rfl) χ).2 r.1.2 _ ((rel_iff I).2 rfl)
  exact (congrArg _ this).trans (Units.inv_mul_cancel_left _ _)

theorem exists_move (hI : ∀ k, Function.Bijective (qMap I k)) (hI' : ∀ k, Function.Bijective (qMap I' k))
    (w : TowerIso N N' n) : ∃ w₀ : TowerIso M M' n, ∀ j p, w₀.io j (qMap I _ p) = qMap I' _ (w.io j p) := by
  let E := fun k => MulEquiv.ofBijective (qMap I k) (hI k)
  have hE : ∀ k p, qMap I k ((E k).symm p) = p := fun k p => (E k).apply_symm_apply p
  have g : ∀ {k l} (p : N.QT k) (q : N.QT l), (qMap I _ q).1.2 = (qMap I _ p).1.2 → q.1.2 = p.1.2 := fun p q h => by
    have := (hI 0).1 (a₁ := ⟨(1, q.1.2), by rw [NumD.mem_QT, pow_zero]; exact N.io_zero.symm⟩)
      (a₂ := ⟨(1, p.1.2), by rw [NumD.mem_QT, pow_zero]; exact N.io_zero.symm⟩) (Subtype.ext (Prod.ext rfl h))
    exact congrArg (fun x : N.QT 0 => x.1.2) this
  refine ⟨{
    io := fun j p => qMap I' _ (w.io j ((E _).symm p))
    eqv := fun j p q => by rw [qEq_qMap I' (hI' _).1, w.eqv, ← qEq_qMap I (hI _).1, hE, hE]
    onto := fun j p' => ?_
    mul := fun j p q => by rw [← map_mul, map_mul (E _).symm, qEq_qMap I' (hI' _).1]; exact w.mul _ _ _
    incl := fun j p q q' a b c d => ?_
    wp := fun j p q => by rw [wp_qMap, w.wp, ← wp_qMap I, hE, hE] }, fun j p =>
      congrArg (fun x => qMap I' _ (w.io j x)) ((E _).symm_apply_apply p)⟩
  · obtain ⟨p', rfl⟩ := (hI' _).2 p'
    obtain ⟨p, hp⟩ := w.onto j p'
    exact ⟨E _ p, by rw [MulEquiv.symm_apply_apply, qEq_qMap I' (hI' _).1]; exact hp⟩
  · have e : (n ^ (j + 1)) ^ 2 = (n ^ j) ^ 2 * n ^ 2 := by ring
    have h' : q' = qMap I' _ (up e (w.io j ((E _).symm p))) :=
      Subtype.ext (Prod.ext (Multiplicative.toAdd.injective (c.trans (map_nsmul I'.e _ _).symm)) d)
    rw [h', qEq_qMap I' (hI' _).1]
    refine w.incl j _ _ _ (I.e.injective ?_) (g _ _ (by rw [hE, hE, b])) rfl rfl
    rw [map_nsmul]
    exact (congrArg (fun x : M.QT _ => x.1.1.toAdd) (hE _ q)).trans (a.trans
      (congrArg (fun x : M.QT _ => n ^ 2 • x.1.1.toAdd) (hE _ p)).symm)
end Move
end GlobalTheory.SeriesCompare
end
