import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElementStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LineGen

open GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_span_iff {q : Cpt ξ} {a b : Ω} :
    a ∈ Submodule.span (regAt ξ q) {b} ↔ ∃ r ∈ regAt ξ q, r * b = a := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, r.2, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩

theorem unitAt_inv {q : Cpt ξ} {a : Ω} (h : unitAt ξ q a) : unitAt ξ q a⁻¹ :=
  ⟨inv_ne_zero h.1, h.2.2, by simpa using h.2.1⟩

theorem unitAt_mul {q : Cpt ξ} {a b : Ω} (ha : unitAt ξ q a) (hb : unitAt ξ q b) : unitAt ξ q (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by
    rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unitAt_pow {q : Cpt ξ} {a : Ω} (ha : unitAt ξ q a) (k : ℕ) : unitAt ξ q (a ^ k) :=
  ⟨pow_ne_zero _ ha.1, pow_mem ha.2.1 _, by rw [← inv_pow]; exact pow_mem ha.2.2 _⟩

theorem unitAt_left {q : Cpt ξ} {a b : Ω} (h : unitAt ξ q (a * b)) (ha : a ∈ regAt ξ q) (hb : b ∈ regAt ξ q) :
    unitAt ξ q a := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h.1
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have e : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [e]
  exact mul_mem hb h.2.2

theorem span_unit_mul {q : Cpt ξ} {a : Ω} (ha : unitAt ξ q a) (b : Ω) :
    Submodule.span (regAt ξ q) {a * b} = Submodule.span (regAt ξ q) {b} := by
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem]
    exact mem_span_iff.2 ⟨a, ha.2.1, rfl⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    refine mem_span_iff.2 ⟨a⁻¹, ha.2.2, ?_⟩
    have := ha.1
    field_simp

theorem piece_chart {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ U : X.Opens, IsPiece ξ U (chartSub x c) ∧ ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := by
  obtain ⟨U, hU, hm⟩ := hT.affine c hc
  have hq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun h => ((hm q.1).1 h).2, fun h => (hm q.1).2 ⟨q.2, h⟩⟩
  refine ⟨U, ⟨hU, fun q h => ((hm q).1 h).1, fun a => ?_⟩, hq⟩
  exact (hT.ring c hc a).trans (forall_congr' fun q => imp_congr (hq q).symm Iff.rfl)

theorem exists_basic (hg : IsCptGen ξ) {U : X.Opens} {R : Subring Ω} (hP : IsPiece ξ U R) (p : Cpt ξ)
    (hp : p.1 ∈ U) (V : X.Opens) (hV : p.1 ∈ V) :
    ∃ g ∈ R, g ≠ 0 ∧ unitAt ξ p g ∧ ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q g → q.1 ∈ V := by
  obtain ⟨f, hfV, hpf⟩ := hP.affine.exists_basicOpen_le (V := V) ⟨p.1, hV⟩ hp
  have hη : genPt ξ ∈ U := p.2.mem_open U.isOpen hp
  let g : Ω := (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη f)
  have hgerm : ∀ (q : Cpt ξ) (hq : q.1 ∈ U), genMap ξ q (X.presheaf.germ U q.1 hq f) = g := by
    intro q hq
    show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes q.2 (X.presheaf.germ U q.1 hq f)) = _
    congr 1
    exact X.presheaf.germ_stalkSpecializes_apply hq q.2 f
  have hgR : g ∈ R := (hP.ring g).2 fun q hq => ⟨_, hgerm q hq⟩
  obtain ⟨v, hv⟩ := ((Scheme.mem_basicOpen X f p.1 hp).1 hpf).exists_right_inv
  have h1 : g * genMap ξ p v = 1 := by
    rw [← hgerm p hp, ← map_mul, hv, map_one]
  have hg0 : g ≠ 0 := left_ne_zero_of_mul_eq_one h1
  refine ⟨g, hgR, hg0, ⟨hg0, ⟨_, hgerm p hp⟩, ⟨v, (inv_eq_of_mul_eq_one_right h1).symm⟩⟩, fun q hq hu => ?_⟩
  obtain ⟨-, -, ⟨t, ht⟩⟩ := hu
  refine hfV ((Scheme.mem_basicOpen X f q.1 hq).2 (isUnit_iff_exists_inv.2 ⟨t, hg.inj q ?_⟩))
  rw [map_mul, map_one, hgerm q hq, ht, mul_inv_cancel₀ hg0]

theorem exists_cover (hg : IsCptGen ξ) {U : X.Opens} {R : Subring Ω} (hP : IsPiece ξ U R) {Λ : Lat ξ Ω}
    (hΛ : Λ.IsVB 1 ⊤) :
    ∃ t : Finset (Ω × Ω), (∀ a ∈ t, a.1 ∈ R ∧ a.1 ≠ 0 ∧ a.2 ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q a.1 →
        Λ q = Submodule.span (regAt ξ q) {a.2}) ∧
      ∀ q : Cpt ξ, q.1 ∈ U → ∃ a ∈ t, unitAt ξ q a.1 := by
  classical
  have key : ∀ z : X, z ∈ U → ∃ (a : Ω × Ω) (W : X.Opens), z ∈ W ∧
      (a.1 ∈ R ∧ a.1 ≠ 0 ∧ a.2 ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q a.1 →
        Λ q = Submodule.span (regAt ξ q) {a.2}) ∧ ∀ q : Cpt ξ, q.1 ∈ W → unitAt ξ q a.1 := by
    intro z hz
    let p : Cpt ξ := ⟨z, hP.spec z hz⟩
    obtain ⟨V, hpV, b, -, hfr⟩ := hΛ p trivial
    obtain ⟨g, hgR, hg0, hpu, hgV⟩ := exists_basic hg hP p hz V hpV
    obtain ⟨U', -, hm⟩ := GlobalTheory.T.piece_localization_at_element X Ω ξ U R g hg hP hgR hg0
    refine ⟨(g, b 0), U', (hm p).2 ⟨hz, hpu⟩, ⟨hgR, hg0, (hfr p trivial hpV).1.ne_zero 0, fun q hq hu => ?_⟩,
      fun q hq => ((hm q).1 hq).2⟩
    have := (hfr q trivial (hgV q hq hu)).2
    rw [this, Set.range_unique]
    rfl
  choose! a W hzW ha hW using key
  obtain ⟨T, hTU, hcov⟩ := hP.affine.isCompact.elim_nhds_subcover (fun z => (W z : Set X))
    (fun z hz => (W z).isOpen.mem_nhds (hzW z hz))
  refine ⟨T.image a, fun y hy => ?_, fun q hq => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact ha z (hTU z hz)
  · obtain ⟨z, hz, hqz⟩ := Set.mem_iUnion₂.1 (hcov hq)
    exact ⟨a z, Finset.mem_image_of_mem a hz, hW z (hTU z hz) q hqz⟩

theorem div_mem_chart {κ : Type} (x : κ → Ω) (j c : κ) : x j / x c ∈ chartSub x c :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem exists_deg {κ : Type} (x : κ → Ω) {c c' : κ} (hc : x c ≠ 0) (hc' : x c' ≠ 0) {g : Ω}
    (hgR : g ∈ chartSub x c) : ∃ e : ℕ, ∀ e', e ≤ e' → (x c / x c') ^ e' * g ∈ chartSub x c' := by
  have hu : x c / x c' ∈ chartSub x c' := div_mem_chart x c c'
  have hgR' : g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := hgR
  induction hgR' using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨1, fun e' he => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
    have h1 : (x c / x c') * (x j / x c) = x j / x c' := by
      field_simp
    have e : (x c / x c') ^ (1 + k) * (x j / x c) = (x c / x c') ^ k * (x j / x c') := by
      rw [pow_add, pow_one, mul_comm (x c / x c') (_ ^ k), _root_.mul_assoc, h1]
    rw [e]
    exact mul_mem (pow_mem hu _) (div_mem_chart x j c')
  | algebraMap n =>
    refine ⟨0, fun e' _ => mul_mem (pow_mem hu _) ?_⟩
    simpa using intCast_mem (chartSub x c') n
  | add a b _ _ h1 h2 =>
    obtain ⟨e₁, h₁⟩ := h1 (Subalgebra.mem_toSubring.2 ‹_›)
    obtain ⟨e₂, h₂⟩ := h2 (Subalgebra.mem_toSubring.2 ‹_›)
    refine ⟨max e₁ e₂, fun e' he => ?_⟩
    rw [mul_add]
    exact add_mem (h₁ e' (le_trans (le_max_left _ _) he)) (h₂ e' (le_trans (le_max_right _ _) he))
  | mul a b _ _ h1 h2 =>
    obtain ⟨e₁, h₁⟩ := h1 (Subalgebra.mem_toSubring.2 ‹_›)
    obtain ⟨e₂, h₂⟩ := h2 (Subalgebra.mem_toSubring.2 ‹_›)
    refine ⟨e₁ + e₂, fun e' he => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
    have e : (x c / x c') ^ (e₁ + e₂ + k) * (a * b) =
        ((x c / x c') ^ e₁ * a) * ((x c / x c') ^ (e₂ + k) * b) := by ring
    rw [e]
    exact mul_mem (h₁ _ le_rfl) (h₂ _ (Nat.le_add_right _ _))

theorem pair {κ : Type} {x : κ → Ω} {Λ : Lat ξ Ω} (hT : CoordTie ℤ ξ x) {c c' : κ} (hc : x c ≠ 0)
    (hc' : x c' ≠ 0) {g g' b b' : Ω} {e : ℕ} (hgR : g ∈ chartSub x c) (hg0 : g ≠ 0)
    (hg'R : g' ∈ chartSub x c') (hg'0 : g' ≠ 0) (hb' : b' ≠ 0)
    (hΛ : ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q g → Λ q = Submodule.span (regAt ξ q) {b})
    (hΛ' : ∀ q : Cpt ξ, InChart ξ x c' q → unitAt ξ q g' → Λ q = Submodule.span (regAt ξ q) {b'})
    (he : (x c / x c') ^ e * g ∈ chartSub x c') :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ q : Cpt ξ, InChart ξ x c' q → unitAt ξ q g' →
      (x c / x c') ^ ((e + 1) * M) * g ^ M * b ∈ Λ q := by
  set u : Ω := x c / x c' with hu_def
  have hu : u ∈ chartSub x c' := div_mem_chart x c c'
  have hu0 : u ≠ 0 := div_ne_zero hc hc'
  set G : Ω := u ^ e * g with hG_def
  have hG0 : G ≠ 0 := mul_ne_zero (pow_ne_zero _ hu0) hg0
  set w : Ω := g' * (u * G) with hw_def
  have hw0 : w ≠ 0 := mul_ne_zero hg'0 (mul_ne_zero hu0 hG0)
  have hwR : w ∈ chartSub x c' := mul_mem hg'R (mul_mem hu he)
  obtain ⟨U₀, hU₀, hU₀m⟩ := piece_chart hT hc'
  obtain ⟨U₁, hU₁, hm⟩ := GlobalTheory.T.piece_localization_at_element X Ω ξ U₀ _ w hT.gen hU₀ hwR hw0
  have hreg : ∀ q : Cpt ξ, InChart ξ x c' q → ∀ a ∈ chartSub x c', a ∈ regAt ξ q :=
    fun q hq a ha => (hT.ring c' hc' a).1 ha q hq
  have hf : b / b' ∈ locSub (chartSub x c') w := by
    refine (hU₁.ring _).2 fun q hq => ?_
    obtain ⟨hq0, hqw⟩ := (hm q).1 hq
    have hqc' : InChart ξ x c' q := (hU₀m q).1 hq0
    have hr := hreg q hqc'
    have hg'u : unitAt ξ q g' := unitAt_left hqw (hr _ hg'R) (hr _ (mul_mem hu he))
    have huG : unitAt ξ q (u * G) := by
      rw [hw_def, mul_comm] at hqw
      exact unitAt_left hqw (hr _ (mul_mem hu he)) (hr _ hg'R)
    have huu : unitAt ξ q u := unitAt_left huG (hr _ hu) (hr _ he)
    have hGu : unitAt ξ q G := by
      rw [mul_comm] at huG
      exact unitAt_left huG (hr _ he) (hr _ hu)
    have hqc : InChart ξ x c q := by
      refine ⟨hc, fun l => ?_⟩
      have e1 : x l / x c = (x l / x c') * u⁻¹ := by
        rw [hu_def]
        field_simp
      rw [e1]
      exact mul_mem (hqc'.2 l) huu.2.2
    have hgu : unitAt ξ q g := by
      have e1 : g = (u⁻¹) ^ e * G := by
        rw [hG_def, ← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hu0, one_pow, _root_.one_mul]
      rw [e1]
      exact unitAt_mul (unitAt_pow (unitAt_inv huu) _) hGu
    have hmem : b ∈ Submodule.span (regAt ξ q) {b'} := by
      rw [← hΛ' q hqc' hg'u, hΛ q hqc hgu]
      exact Submodule.mem_span_singleton_self b
    obtain ⟨r, hr', rfl⟩ := mem_span_iff.1 hmem
    rwa [mul_div_cancel_right₀ _ hb']
  obtain ⟨k, hk⟩ := (mem_locSub_iff hwR hw0 _).1 hf
  refine ⟨k, fun M hM q hq hqu => ?_⟩
  have hwM : w ^ M * (b / b') ∈ chartSub x c' := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hM
    rw [pow_add, mul_comm (w ^ k), _root_.mul_assoc]
    exact mul_mem (pow_mem hwR _) hk
  rw [hΛ' q hq hqu]
  refine mem_span_iff.2 ⟨(g'⁻¹) ^ M * (w ^ M * (b / b')),
    mul_mem (pow_mem hqu.2.2 _) (hreg q hq _ hwM), ?_⟩
  have e1 : w ^ M = g' ^ M * (u ^ ((e + 1) * M) * g ^ M) := by
    rw [hw_def, hG_def]
    ring
  have e2 : (g'⁻¹) ^ M * g' ^ M = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hg'0, one_pow]
  have e3 : (g'⁻¹) ^ M * (g' ^ M * (u ^ ((e + 1) * M) * g ^ M) * (b / b')) * b' =
      ((g'⁻¹) ^ M * g' ^ M) * (u ^ ((e + 1) * M) * g ^ M) * (b / b' * b') := by ring
  rw [e1, e3, e2, div_mul_cancel₀ _ hb', _root_.one_mul]

end GlobalTheory.CompanionTheory.Ar.LineGen

namespace GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.LineGen

theorem line_twist_generated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (Λ : Lat ξ Ω), CoordTie ℤ ξ x → Λ.IsVB 1 ⊤ → ∃ (n m : ℕ) (s : Fin (m + 1) → Ω), (∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∀ i, s i / x c ^ n ∈ Λ p) ∧ ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ i, Λ.IsGenAt p (s i / x c ^ n) := by
  intro X Ω _ ξ κ _ x Λ hT hΛ
  classical
  let C := {c : κ // x c ≠ 0}
  choose U hU hUm using fun c : C => piece_chart hT c.2
  choose t ht hcov using fun c : C => exists_cover hT.gen (hU c) hΛ
  let I := Σ c : C, {a // a ∈ t c}
  let cc : I → κ := fun i => i.1.1
  let gg : I → Ω := fun i => i.2.1.1
  let bb : I → Ω := fun i => i.2.1.2
  have hcc : ∀ i, x (cc i) ≠ 0 := fun i => i.1.2
  have hgR : ∀ i, gg i ∈ chartSub x (cc i) := fun i => (ht i.1 _ i.2.2).1
  have hg0 : ∀ i, gg i ≠ 0 := fun i => (ht i.1 _ i.2.2).2.1
  have hb0 : ∀ i, bb i ≠ 0 := fun i => (ht i.1 _ i.2.2).2.2.1
  have hΛi : ∀ (i : I) (q : Cpt ξ), InChart ξ x (cc i) q → unitAt ξ q (gg i) →
      Λ q = Submodule.span (regAt ξ q) {bb i} :=
    fun i q hq hu => (ht i.1 _ i.2.2).2.2.2 q ((hUm i.1 q).2 hq) hu

  choose e₀ he₀ using fun ij : I × I => exists_deg x (hcc ij.1) (hcc ij.2) (hgR ij.1)
  obtain ⟨e, he⟩ := Finite.exists_le e₀

  choose M₀ hM₀ using fun ij : I × I => pair hT (hcc ij.1) (hcc ij.2) (hgR ij.1) (hg0 ij.1) (hgR ij.2)
    (hg0 ij.2) (hb0 ij.2) (hΛi ij.1) (hΛi ij.2) (he₀ ij e (he ij))
  obtain ⟨M, hM⟩ := Finite.exists_le M₀
  let n : ℕ := (e + 1) * M
  let T : I → Ω := fun i => x (cc i) ^ n * gg i ^ M * bb i
  have hpatch : ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ j : I, cc j = c ∧ unitAt ξ p (gg j) := by
    intro p c hp
    obtain ⟨a, ha, hu⟩ := hcov ⟨c, hp.1⟩ p ((hUm ⟨c, hp.1⟩ p).2 hp)
    exact ⟨⟨⟨c, hp.1⟩, ⟨a, ha⟩⟩, rfl, hu⟩
  have hsec : ∀ (i : I) (p : Cpt ξ) (c : κ), InChart ξ x c p → T i / x c ^ n ∈ Λ p := by
    intro i p c hp
    obtain ⟨j, rfl, hu⟩ := hpatch p c hp
    have h := hM₀ (i, j) M (hM (i, j)) p hp hu
    have e1 : T i / x (cc j) ^ n = (x (cc i) / x (cc j)) ^ n * gg i ^ M * bb i := by
      simp only [T, div_pow]
      ring
    rw [e1]
    exact h
  obtain ⟨k, ⟨eq⟩⟩ := Finite.exists_equiv_fin (Option I)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := by
    cases k with
    | zero => exact (eq none).elim0
    | succ m => exact ⟨m, rfl⟩
  refine ⟨n, m, fun l => (eq.symm l).elim 0 T, fun p c hp l => ?_, fun p c hp => ?_⟩
  · show Option.elim (eq.symm l) 0 T / x c ^ n ∈ Λ p
    cases eq.symm l with
    | none =>
      show (0 : Ω) / x c ^ n ∈ Λ p
      rw [zero_div]
      exact zero_mem _
    | some i => exact hsec i p c hp
  · obtain ⟨j, rfl, hu⟩ := hpatch p c hp
    refine ⟨eq (some j), ?_⟩
    have e1 : (eq.symm (eq (some j))).elim 0 T / x (cc j) ^ n = gg j ^ M * bb j := by
      have := pow_ne_zero n (hcc j)
      simp only [Equiv.symm_apply_apply, Option.elim, T]
      field_simp
    show Lat.IsGenAt Λ p ((eq.symm (eq (some j))).elim 0 T / x (cc j) ^ n)
    rw [e1]
    refine ⟨mul_ne_zero (pow_ne_zero _ (hg0 j)) (hb0 j), ?_⟩
    rw [span_unit_mul (unitAt_pow hu M)]
    exact hΛi j p hp hu

end GlobalTheory.CompanionTheory.Ar
