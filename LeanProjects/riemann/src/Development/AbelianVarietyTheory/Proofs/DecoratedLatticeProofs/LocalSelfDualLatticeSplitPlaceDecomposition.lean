import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitSelfDual

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def intMat : AddSubgroup (Matrix Y Y' k) where
  carrier := {x | ∀ r q, x r q ∈ 𝒪[k]}
  add_mem' hx hy r q := add_mem (hx r q) (hy r q)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx r q := neg_mem (hx r q)

theorem isHalf_neg {S T : HSp D} {e : AE D} {y : WO S T} (h : IsHalf e y) : IsHalf e (-y) := fun i j => by
  rw [Matrix.neg_apply, mul_neg, h i j]

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  rw [← GlobalTheory.LatVac.symplHom_apply, map_neg]; rfl

theorem psi_neg_eq_one {ψ : AddChar (AF D.host.F) ℂ} {a : AF D.host.F} (h : ψ a = 1) : ψ (-a) = 1 := by
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

theorem eq_zero_of_halves {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {y : WO S T} (h1 : IsHalf e y)
    (h2 : IsHalf (cA D e) y) : y = 0 := by
  ext i j
  rw [Matrix.zero_apply, ← h1 i j, ← h2 i j, ← mul_assoc, he.2.1, zero_mul]

def dualHalf (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) : AddSubgroup (WO S T) where
  carrier := {y | IsHalf (cA D p.e) y ∧
    ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) y) = 1}
  add_mem' {a b} ha hb := ⟨GlobalTheory.SplitScalar.isHalf_add ha.1 hb.1, fun t ht => by
    rw [GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul, ha.2 t ht, hb.2 t ht, one_mul]⟩
  zero_mem' := ⟨GlobalTheory.SplitScalar.isHalf_zero _, fun t _ => by
    rw [GlobalTheory.SplitScalar.symplO_zero_right, AddChar.map_zero_eq_one]⟩
  neg_mem' {a} ha := ⟨isHalf_neg ha.1, fun t ht => by
    rw [symplO_neg_right]; exact psi_neg_eq_one (ha.2 t ht)⟩

def lat (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) : AddSubgroup (WO S T) :=
  (intMat (k := k) (Y := Y) (Y' := Y')).map (Witness.upH p FS FT) ⊔ dualHalf p ψ S T FS FT

section
variable (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)

theorem mem_lat {u : WO S T} : u ∈ lat p ψ S T FS FT ↔
    ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ ∃ y ∈ dualHalf p ψ S T FS FT, p.up FS FT x + y = u := by
  unfold lat
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, y, hy, h⟩
    exact ⟨x, hx, y, hy, h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨_, ⟨x, hx, rfl⟩, y, hy, h⟩

theorem up_mem_lat {x : Matrix Y Y' k} (hx : ∀ r q, x r q ∈ 𝒪[k]) : p.up FS FT x ∈ lat p ψ S T FS FT :=
  (mem_lat p ψ FS FT).2 ⟨x, hx, 0, zero_mem _, add_zero _⟩

theorem dualHalf_le_lat : dualHalf p ψ S T FS FT ≤ lat p ψ S T FS FT := le_sup_right

theorem half_e_of_mem {u : WO S T} (hu : u ∈ lat p ψ S T FS FT) (he : IsHalf p.e u) :
    ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ u = p.up FS FT x := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
  have hye : IsHalf p.e y := (Witness.half_add (Witness.up_half p FS FT x)).1 (by rwa [add_comm] at he)
  rw [eq_zero_of_halves p.split hye hy.1, add_zero]
  exact ⟨x, hx, rfl⟩

theorem half_c_of_mem {u : WO S T} (hu : u ∈ lat p ψ S T FS FT) (hc : IsHalf (cA D p.e) u) :
    u ∈ dualHalf p ψ S T FS FT := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
  have hxc : IsHalf (cA D p.e) (p.up FS FT x) := (Witness.half_add hy.1).1 hc
  rw [eq_zero_of_halves p.split (Witness.up_half p FS FT x) hxc, zero_add]
  exact hy

end

theorem selfDual_lattice_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), ∃ Λ : AddSubgroup (WO S T), (∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1) ∧ (∀ y, IsHalf p.e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D p.e) l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ y, IsHalf (cA D p.e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf p.e l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ x : Matrix Y Y' k, p.up FS FT x ∈ Λ ↔ ∀ r q, x r q ∈ 𝒪[k]) ∧ (∀ u ∈ Λ, IsHalf p.e u → ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ u = p.up FS FT x) ∧ (∀ u ∈ Λ, IsHalf (cA D p.e) u → ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) u) = 1) := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT
  obtain ⟨⟨ψk, hψk⟩, hcont, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hψc, hψ1⟩ := hcont ψk hψk
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψk hψc hψ1
  obtain ⟨-, -, hiso, hpsi, hpair⟩ := GlobalTheory.LocSympl.halves_at_split D k p Y Y' S T FS FT ψ ψk hψk
  have hconj : IsSplitIdem D (cA D p.e) := GlobalTheory.SplitScalar.isSplitIdem_conj p.split
  refine ⟨lat p ψ S T FS FT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro u hu u' hu'
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
    obtain ⟨x', hx', y', hy', rfl⟩ := (mem_lat p ψ FS FT).1 hu'
    have h4 : symplO S T y y' = 0 := GlobalTheory.SplitScalar.half_orth hconj hy.1 hy'.1
    have h3 : ψ (symplO S T y (p.up FS FT x')) = 1 := by
      rw [GlobalTheory.SplitScalar.symplO_skew]; exact psi_neg_eq_one (hy.2 x' hx')
    rw [GlobalTheory.LatVac.symplO_add_left, GlobalTheory.LatVac.symplO_add_right, GlobalTheory.LatVac.symplO_add_right, hiso, h4,
      zero_add, add_zero, AddChar.map_add_eq_mul, hy'.2 x hx, h3, one_mul]
  ·
    intro y hy hyΛ
    have hyx : p.up FS FT (p.down FS FT y) = y := Witness.up_down p FS FT hy
    have hx : ¬ ∀ r q, p.down FS FT y r q ∈ 𝒪[k] := fun hx => hyΛ (hyx ▸ up_mem_lat p ψ FS FT hx)
    push_neg at hx
    obtain ⟨r, q, hrq⟩ := hx
    set a := p.down FS FT y r q with ha
    have hrq' : ¬ valuation k a ≤ 1 := fun h => hrq ((Valuation.mem_integer_iff _ _).2 h)
    have ha0 : a ≠ 0 := by rintro h; rw [h, map_zero] at hrq'; exact hrq' zero_le'
    have hc0 : 0 < valuation k (c : k) := by simp [zero_lt_iff]
    have hcv : ¬ valuation k (c * a) ≤ valuation k (c : k) := by
      rw [map_mul]; intro h
      have h' : valuation k (c : k) * valuation k a ≤ valuation k (c : k) * 1 := by rwa [mul_one]
      exact hrq' ((mul_le_mul_iff_of_pos_left hc0).1 h')
    obtain ⟨z, hz, hzne⟩ : ∃ z, valuation k z ≤ valuation k (c * a) ∧ ψk z ≠ 1 := by
      by_contra hcon; push_neg at hcon; exact hcv ((hc _).1 hcon)
    have hsum : ∀ t : Matrix Y Y' k, ∑ r', ∑ q', Matrix.single r q (z / a) r' q' * t r' q' = z / a * t r q := by
      intro t; simp [Matrix.single_apply, ite_and]
    obtain ⟨y', hy'c, hy'p⟩ := hpair (Matrix.single r q (z / a))
    have hy'Λ : y' ∈ dualHalf p ψ S T FS FT := by
      refine ⟨hy'c, fun t ht => ?_⟩
      rw [hpsi t y' hy'c, hy'p, hsum]
      have ha0' : 0 < valuation k a := by simp [zero_lt_iff, ha0]
      have hv : valuation k (z / a * t r q) ≤ valuation k (c : k) := by
        rw [map_mul, map_div₀]
        calc valuation k z / valuation k a * valuation k (t r q) ≤ valuation k z / valuation k a * 1 := by
              gcongr; exact (Valuation.mem_integer_iff _ _).1 (ht r q)
          _ ≤ valuation k (c : k) := by rw [mul_one, div_le_iff₀ ha0', ← map_mul]; exact hz
      rw [(hc c).2 le_rfl _ hv, Circle.coe_one]
    refine ⟨y', dualHalf_le_lat p ψ FS FT hy'Λ, hy'c, GlobalTheory.SplitScalar.psi_skew_ne ?_⟩
    rw [← hyx, hpsi _ y' hy'c, hy'p, hsum, ← ha, div_mul_cancel₀ z ha0]
    exact fun h => hzne (Circle.ext (by rw [h, Circle.coe_one]))
  ·
    intro y hy hyΛ
    have hyd : y ∉ dualHalf p ψ S T FS FT := fun h => hyΛ (dualHalf_le_lat p ψ FS FT h)
    have : ¬ ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) y) = 1 :=
      fun h => hyd ⟨hy, h⟩
    push_neg at this
    obtain ⟨t, ht, hne⟩ := this
    exact ⟨p.up FS FT t, up_mem_lat p ψ FS FT ht, Witness.up_half p FS FT t, hne⟩
  ·
    intro x
    refine ⟨fun hx => ?_, fun hx => up_mem_lat p ψ FS FT hx⟩
    obtain ⟨x', hx', hxx⟩ := half_e_of_mem p ψ FS FT hx (Witness.up_half p FS FT x)
    have := congrArg (p.down FS FT) hxx
    rw [Witness.down_up, Witness.down_up] at this
    exact this ▸ hx'
  · intro u hu he
    exact half_e_of_mem p ψ FS FT hu he
  · intro u hu hc' t ht
    exact (half_c_of_mem p ψ FS FT hu hc').2 t ht

end GlobalTheory.SplitSelfDual
