import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaBound

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem proj_mul_proj (T T' : AddSubgroup S.Gam) (h : T' ≤ T) (hT : T ≤ S.perp T)
    (hT' : S.IsoFree T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t : T', c' t = c (AddSubgroup.inclusion h t)) :
    S.proj T' c' * S.proj T c = S.proj T c := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have := Fintype.ofFinite T
  have := Fintype.ofFinite T'
  obtain ⟨d, ⟨e⟩⟩ := hT'.2
  have hζ : IsPrimitiveRoot S.ζN S.N := S.prim.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
  have hu : IsUnit (Nat.card T' : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have h1 : S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, χ (-c t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h2 : S.proj T' c' = Ring.inverse (Nat.card T' : o) • ∑ t : T', χ (-c' t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h3 : ∀ u : T', (χ (-c' u) • S.ρ u) * ∑ t : T, χ (-c t) • S.ρ t
      = ∑ t : T, χ (-c t) • S.ρ t := fun u => by
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addLeft (AddSubgroup.inclusion h u))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, ← AddChar.map_add_eq_mul, S.ρ_add _ _ (by
      rw [hT (h u.2) t t.2, smul_zero]), hc]
    simp only [Equiv.coe_addLeft, map_add, neg_add]
    rfl
  have h4 : ∀ u : T', (χ (-c' u) • S.ρ u) * S.proj T c = S.proj T c := fun u => by
    rw [h1, mul_smul_comm, h3]
  rw [h2, smul_mul_assoc, Finset.sum_mul]
  simp_rw [h4]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul o,
    smul_smul, Ring.inverse_mul_cancel _ hu, one_smul]

theorem norm_FF_le {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p)
    (hy : ∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : _) (hk : S.FF T c k ∈ S.R) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : T, ‖∑ j, y (algebraMap o S.R (S.proj T c j k.1)) * y ⟨S.ev t j, S.ev_mem _ j⟩‖ ≤ B) :
    ‖y ⟨S.FF T c k, hk⟩‖ ≤ B := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have := Fintype.ofFinite T
  have h1 : (⟨S.FF T c k, hk⟩ : S.R) = ∑ t : T, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj T c j k.1) * ⟨S.ev t j, S.ev_mem _ j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finset_sum,
      MulMemClass.coe_mul, SubalgebraClass.coe_algebraMap]
  rw [h1, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun t _ => ?_
  rw [map_mul, norm_mul, map_sum]
  simp_rw [map_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hy _)).trans (h t)

end GlobalTheory.ThetaBound

namespace GlobalTheory

open ThetaBound

theorem thetaSys_norm_FF_le_exp :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) := by
  intro o Ω _ _ _ hA S H p _ y τ hy T c k hk hT
  obtain ⟨-, -, hperp, href⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  have hpos : ∀ α : τ.X, 0 ≤ τ.δ * Real.exp (-(τ.q α / S.N)) := fun α =>
    mul_nonneg τ.δ_pos.le (Real.exp_pos _).le
  refine ⟨fun h1 h2 α hα hc => ?_, fun h1 => ?_⟩
  · refine norm_FF_le S y hy T c k hk (hpos α) fun t => ?_
    rw [← proj_mul_proj S T _ h1 hT.1 τ.isoFree c (τ.wt α) fun u => (hc u (h1 u.2) u.2).symm]
    simp_rw [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos α) fun l _ => ?_
    simp_rw [mul_right_comm _ (y (algebraMap o S.R (S.proj T c l k.1)))]
    rw [← Finset.sum_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hy _)).trans (τ.le α hα t (h2 t.2) l)
  · have hN := S.N_ge
    have hr := S.r_pos
    have : NeZero S.N := ⟨by omega⟩
    have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
    choose a ha hwa using (H p y τ).1
    obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨π, hπ⟩ := ThetaProj.exists_retraction T e
    have hfin : Finite (S.perp τ.yy.ker →+ ZMod S.N) := DFunLike.finite _
    set s := {c' : S.perp τ.yy.ker →+ ZMod S.N | c'.comp (AddSubgroup.inclusion h1) = c} with hs
    have hne : s.Nonempty := ⟨(c.comp π).comp (AddSubgroup.subtype _), by
      ext t
      exact congrArg c (hπ t)⟩
    obtain ⟨c₀, hc₀, hmax⟩ := Set.exists_max_image s
      (fun c' => τ.δ * Real.exp (-(τ.q (a c') / S.N))) (Set.toFinite _) hne
    refine ⟨a c₀, ha c₀, fun t h₁ h₂ => ?_, ?_⟩
    · rw [hwa, ← show _ = c from hc₀]
      rfl
    · refine norm_FF_le S y hy T c k hk (hpos _) fun t => ?_
      rw [href _ T h1 τ.isoFree hT c, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
      simp_rw [Matrix.sum_apply, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos _) fun c' hc' => ?_
      have ht : (t : S.Gam) ∈ τ.yy.ker := by
        rw [← hperp τ.yy.ker]
        exact τ.isoFree.1 (h1 t.2)
      have := τ.le (a c') (ha c') t ht k.1
      rw [hwa] at this
      exact this.trans (hmax c' ((Set.Finite.mem_toFinset _).mp hc'))

end GlobalTheory
