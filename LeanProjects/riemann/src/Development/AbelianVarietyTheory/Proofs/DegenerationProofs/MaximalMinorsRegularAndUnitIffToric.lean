import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsDualThetaTestLatticeBoundStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem RatModel.exists_ringHom_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {K : Type} [Field K] (y : Sp K ⟶ M.Z) {U : Set M.Z} (hy : Set.range y ⊆ U) :
    ∃ ψ : M.ringOn U →+* K, ∀ a, ψ a = M.val y a :=
  ⟨(RatModel.valHom y _ (RatModel.range_eq_singleton y (IsLocalRing.closedPoint K))).comp
    (Subalgebra.inclusion (RatModel.ringOn_le_O (hy ⟨_, rfl⟩))).toRingHom, fun _ => rfl⟩

theorem minors_regular_and_unit_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (R' : Subalgebra o Ω) (hR : S.R ≤ R') (n a : ℕ) (GG : Fin n → S.J → R'), S.Over₀ M U₀ → R' ≤ M.ringOn U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) → ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (∀ k, (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k / S.th x₀ ^ (a * Fintype.card S.J) ∈ M.O z) ∧ (S.TT M z = ⊥ ↔ ∃ k, (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k ≠ 0 ∧ S.th x₀ ^ (a * Fintype.card S.J) / (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k ∈ M.O z) := by
  intro o Ω _ _ _ _ S M U₀ R' hR n a GG hO hR' hLL hT hsup hTT hcl hGG
  obtain ⟨hLL, -⟩ := hLL
  obtain ⟨-, -, -, hcp⟩ := hTT
  set D : (S.J → Fin n) → Ω := fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)) with hD
  set m := a * Fintype.card S.J with hm

  have hDR : ∀ k, D k = ((Matrix.det (Matrix.of fun i j => GG (k i) j) : R') : Ω) := fun k =>
    ((R'.val.toRingHom.map_det (Matrix.of fun i j => GG (k i) j))).symm
  have hclosed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z,
      (∀ k, D k / S.th x₀ ^ m ∈ M.O z) ∧ (S.TT M z = ⊥ ↔ ∃ k, D k ≠ 0 ∧ S.th x₀ ^ m / D k ∈ M.O z) := by
    intro z hz x₀ hx₀
    have h0 : S.th x₀ ≠ 0 := hx₀.1
    have hth : S.th x₀ ∈ M.ringOn U₀ := hO.le (S.th_mem x₀)
    have hinv : (S.th x₀)⁻¹ ∈ M.ringOn U₀ := hO.th_unit x₀ h0
    have hDm : ∀ k, D k ∈ M.ringOn U₀ := fun k => hDR k ▸ hR' (Subtype.prop _)
    have hφ : ∀ k, D k / S.th x₀ ^ m ∈ M.ringOn U₀ := fun k => by
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_mem (hDm k) (pow_mem hinv m)
    have htest : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y →
        (∀ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ ≤ 1) ∧
        ((∃ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ = 1) ↔ S.TT M z = ⊥) := by
      intro p _ y hy
      obtain ⟨ψ, hψ⟩ := M.exists_ringHom_val (gPt p ≫ y) hy.2
      obtain ⟨y₀, hAt, hb, ⟨τ⟩⟩ := hT z p y hy
      let y' : R' →+* PadicAlgCl p := ψ.comp (Subalgebra.inclusion hR').toRingHom
      have e : y₀ = y'.comp (Subalgebra.inclusion hR).toRingHom :=
        RingHom.ext fun b => (hAt b).trans (hψ ⟨b, hO.le b.2⟩).symm
      subst e
      obtain ⟨hs, hH⟩ := hsup z p y _ τ hy hAt
      have hδ := (hs x₀).1 hx₀
      have hpos := τ.δ_pos
      obtain ⟨h1, h2⟩ := GlobalTheory.T.maximal_minors_dual_thetaTest_lattice_bound o Ω S p _ τ hb hcl n (τ.δ ^ a) (fun k j => y' (GG k j)) (pow_pos hpos a)
        (hGG p y' τ hb)
      rw [← pow_mul, ← hm] at h1 h2
      have hpm : 0 < τ.δ ^ m := pow_pos hpos m
      have hval : ∀ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ * τ.δ ^ m =
          ‖Matrix.det (Matrix.of fun i j => y' (GG (k i) j))‖ := by
        intro k
        have e1 : (⟨_, hφ k⟩ : M.ringOn U₀) * ⟨_, hth⟩ ^ m =
            Subalgebra.inclusion hR' (Matrix.det (Matrix.of fun i j => GG (k i) j)) :=
          Subtype.ext ((div_mul_cancel₀ _ (pow_ne_zero m h0)).trans (hDR k))
        have e2 := congrArg (fun t => ‖ψ t‖) e1
        simp only [map_mul, map_pow, norm_mul, norm_pow] at e2
        rw [hψ, hψ] at e2
        rw [← hδ]
        refine e2.trans ?_
        exact congrArg norm (y'.map_det (Matrix.of fun i j => GG (k i) j))
      refine ⟨fun k => ?_, ?_⟩
      · have := h1 k
        rw [← hval] at this
        exact le_of_mul_le_mul_right (by simpa using this) hpm
      · rw [ThetaSys.TT, hH, ← h2]
        refine exists_congr fun k => ?_
        rw [← hval]
        exact ⟨fun h => by rw [h, _root_.one_mul], fun h => mul_right_cancel₀ hpm.ne' (h.trans (_root_.one_mul _).symm)⟩
    obtain ⟨⟨p, _, y, hy⟩, hreg⟩ := hLL U₀ le_rfl hO.ne z hz
    have hmem : ∀ k, D k / S.th x₀ ^ m ∈ M.O z := fun k =>
      hreg _ (hφ k) fun p _ y hy => (htest p y hy).1 k
    refine ⟨hmem, ?_⟩
    rw [← (htest p y hy).2]
    refine exists_congr fun k => ?_
    rw [RatModel.norm_val_eq_one_iff hy.1 (hmem k), RatModel.isUnit_O_iff]
    simp only [inv_div, ne_eq, div_eq_zero_iff, pow_ne_zero m h0, or_false]
  intro z x₀ hx₀
  have hTTeq : ∀ x : M.Z, S.supI M x = S.supI M z → S.TT M x = S.TT M z := fun x h => by
    rw [ThetaSys.TT, ThetaSys.TT, ThetaSys.HH, ThetaSys.HH, h]
  obtain ⟨x, -, hx, hzx, hs⟩ := hcp z ⊤ trivial
  obtain ⟨h1, h2⟩ := hclosed x hx x₀ (hs ▸ hx₀)
  refine ⟨fun k => RatModel.O_le_of_specializes hzx (h1 k), fun h => ?_, fun ⟨k, hk, hk'⟩ => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := h2.1 ((hTTeq x hs).trans h)
    exact ⟨k, hk, RatModel.O_le_of_specializes hzx hk'⟩
  · obtain ⟨x', hW, hx', -, hs'⟩ := hcp z ⟨_, M.isOpen_setOf_mem_O (S.th x₀ ^ m / D k)⟩ hk'
    exact (hTTeq x' hs').symm.trans ((hclosed x' hx' x₀ (hs' ▸ hx₀)).2.2 ⟨k, hk, hW⟩)

end GlobalTheory.ZH
