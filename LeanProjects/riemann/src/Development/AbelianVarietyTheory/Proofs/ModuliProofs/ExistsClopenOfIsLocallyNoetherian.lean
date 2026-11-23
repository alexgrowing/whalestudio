import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLocus

theorem exists_idempotent {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : u ^ n = 1) :
    ∃ e : R, IsIdempotentElem e ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), φ u = 1 ↔ φ e = 1 := by
  obtain ⟨m, hm⟩ := hn.exists_left_inv
  have h₀ : (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hu, sub_self]
  have h₁ : u * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    linear_combination m * h₀
  have h₂ : ∀ i : ℕ, u ^ i * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    intro i
    induction i with
    | zero => rw [pow_zero, _root_.one_mul]
    | succ i ih => rw [pow_succ, _root_.mul_assoc, h₁, ih]
  refine ⟨m * ∑ i ∈ Finset.range n, u ^ i, ?_, fun R' _ φ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · show _ * _ = _
    rw [_root_.mul_assoc, Finset.sum_mul, Finset.sum_congr rfl fun i _ => h₂ i, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← _root_.mul_assoc, hm, _root_.one_mul]
  · have := congrArg φ hm
    simp only [map_mul, map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      _root_.mul_one, map_natCast, map_one] at this ⊢
    exact this
  · have := congrArg φ h₁
    rwa [map_mul, h, _root_.mul_one] at this

theorem isClosed_basicOpen {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (X.basicOpen e : Set X) := by
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ X.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (X.mem_basicOpen e x trivial).2 h'
      · exact absurd ((X.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

theorem appTop_eq_one_iff {X Y : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) (h : Y ⟶ X) :
    h.appTop.hom e = 1 ↔ Set.range h ⊆ X.basicOpen e := by
  have p : h ⁻¹ᵁ X.basicOpen e = Y.basicOpen (h.appTop.hom e) := Scheme.preimage_basicOpen h e
  constructor
  · rintro H _ ⟨y, rfl⟩
    have : y ∈ h ⁻¹ᵁ X.basicOpen e := by
      rw [p, H, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    exact this
  · intro H
    have hu : IsUnit (h.appTop.hom e) := by
      refine RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace ⊤ _ fun y hy => ?_
      have : y ∈ Y.basicOpen (h.appTop.hom e) := by rw [← p]; exact H ⟨y, rfl⟩
      exact (Y.mem_basicOpen _ y hy).1 this
    exact hu.mul_left_cancel ((he.map h.appTop.hom).eq.trans (_root_.mul_one _).symm)

theorem exists_clopen_eq {X : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤))) {c c₀ : Γ(X, ⊤)ˣ}
    (hc : c ^ n = 1) (hc₀ : c₀ ^ n = 1) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ X),
      Units.map h.appTop.hom.toMonoidHom c = Units.map h.appTop.hom.toMonoidHom c₀ ↔ Set.range h ⊆ U := by
  have hu : (c * c₀⁻¹).val ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hc, hc₀, inv_one, _root_.mul_one, Units.val_one]
  obtain ⟨e, he, H⟩ := exists_idempotent hn hu
  refine ⟨X.basicOpen e, isClosed_basicOpen he, fun Y h => ?_⟩
  rw [← appTop_eq_one_iff he, ← H, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← Units.val_eq_one]
  rfl

theorem pow_eq_one (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A}
    (hx : x ^ k = 1) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ j : ℕ, WeilIs P.A P.L k (x ^ (j + 1)) y (c ^ (j + 1)) := by
    intro j
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c]; exact weilIs_mul_left hG S P k T _ _ _ _ _ ih hc
  have h := hpow k
  rw [pow_succ, hx, _root_.one_mul] at h
  have := CommutatorPairing.weilIs_unique hG P.isAb P.isLB h hc
  rwa [pow_succ, mul_eq_right] at this

theorem exists_clopen_of_weilIs (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) {T : Over S}
    {x y : T ⟶ P.A} {c c₀ : Γ(T.left, ⊤)ˣ} (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1) (hc : c ^ n = 1)
    (h₀ : WeilIs P.A P.L n x y c₀) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by
  obtain ⟨U, hU, H⟩ := exists_clopen_eq hn hc (pow_eq_one hG P n hx h₀)
  refine ⟨U, hU, fun T' h => ?_⟩
  have h₁ := CommPairing.weilIs_pull hG P.isAb P.isLB h h₀
  rw [← H]
  exact ⟨fun h₂ => CommutatorPairing.weilIs_unique hG P.isAb P.isLB h₂ h₁, fun e => e ▸ h₁⟩

theorem exists_clopen_of_lift : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A),
    x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) →
    ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), 0 < n →
      IsUnit (n : Γ(T.left, ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 →
      ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
        WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔
          Set.range h.left ⊆ U := by
  intro hG hl S P n T x y c _ hn hx hy hc
  obtain ⟨c₀, h₀, -⟩ := CommutatorPairing.existsUnique_weilIs hG hl S P n T x y hx hy
  exact exists_clopen_of_weilIs hG P n hn hx hc h₀

theorem exists_clopen_of_isLocallyNoetherian (hL : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ) (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hc : c ^ n = 1) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by
  obtain ⟨c₀, h₀, -⟩ := (hL.weil S P n T).1 x y hx hy
  exact exists_clopen_of_weilIs hL.globalFns P n hn hx hc h₀

end GlobalTheory.PairingLocus
