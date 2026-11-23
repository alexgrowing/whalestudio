import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem period_constantPart_eq_zero_injective {O : Type} [CommRing O] [StarRing O] (B : AnArc O) (la : B.La) (hy : la.y = 0)
    (h : B.P0 la = 0) : la = 0 := by
  have hl : la.l = 0 := by
    have := congrArg Prod.snd h
    rw [AnArc.degeneratingTori_basePeriodMap_snd, hy, map_zero, zero_add] at this
    exact Subtype.ext this
  refine AnArc.La.ext hy (AddMonoidHom.ext fun x => ?_) hl
  have : (B.P0 la).1 x = 0 := by rw [h]; rfl
  rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, hy, hl] at this
  simpa using this

theorem qkSt_of_ptSt : PtSt → QkSt := by
  intro hP O _ _ N B d k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP O N B d
  choose E hE hU using h1
  have hiff : ∀ v g, d.IsPt v g ↔ g = E v := fun v g => ⟨hU v g, fun h => h ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ la : B.La, E (B.P0 la) = N.io (d.eX la.y) := fun la => (hU _ _ (h5 la)).symm
  have hker : ∀ v v', E v = E v' → ∃ la : B.La, la.y = 0 ∧ v = v' + B.P0 la := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨la, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨la, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : B.V, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : B.V, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ (la : B.La) (p : N.QT k), d.Rep k la p ↔
      p.1.1.toAdd = d.eX la.y ∧ p.1.2 = E ((k : ℂ)⁻¹ • B.P0 la) := fun la p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun la => ?_, fun la la' p p' h h' => ?_, fun la la' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    have e : E (k • v) = E (B.P0 (AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0)) := by
      rw [hpow, hper, ← hv', AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      exact N.mem_QT.1 p.2
    obtain ⟨la, hy, hl⟩ := hker _ _ e
    refine ⟨AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0 + la, (hrep _ _).2 ⟨?_, ?_⟩⟩
    · rw [AnArc.La.add_y, hy, add_zero, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
    · rw [map_add, ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (d.eX la.y), E ((k : ℂ)⁻¹ • B.P0 la)), ?_⟩, (hrep _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    refine (hrep _ _).2 ⟨?_, ?_⟩
    · rw [AnArc.La.add_y, map_add, ← a, ← a']
      rfl
    · rw [map_add, smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      set z₀ : B.La := AnArc.La.mk (d.eX.symm z) 0 0 with hz₀
      have hz : d.eX z₀.y = z := by rw [hz₀, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      have e : E ((k : ℂ)⁻¹ • B.P0 la') = E ((k : ℂ)⁻¹ • B.P0 la + B.P0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨e₀, hy, hl⟩ := hker _ _ e
      refine ⟨z₀ + e₀, sub_eq_zero.1 (period_constantPart_eq_zero_injective B _ ?_ ?_)⟩
      · apply d.eX.injective
        rw [AnArc.La.sub_y, AnArc.La.add_y, AnArc.La.nsmul_y, AnArc.La.add_y, hy, add_zero, map_sub, map_add,
          map_nsmul, hz, ← a, ← a', c, sub_self, map_zero]
      · rw [map_sub, map_add, map_nsmul, map_add, ← hc2 (B.P0 la'), hl, add_assoc, smul_add, hc2, sub_self]
    · rintro ⟨e, rfl⟩
      refine ⟨d.eX e.y, ?_, ?_⟩
      · rw [a, a', AnArc.La.add_y, AnArc.La.nsmul_y, map_add, map_nsmul]
      · rw [b, b', map_add, map_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.Ex.Arch
