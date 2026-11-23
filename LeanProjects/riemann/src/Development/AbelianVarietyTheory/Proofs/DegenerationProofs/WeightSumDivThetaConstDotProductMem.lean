import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FfDivFfMemOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.DualSection

theorem proj_mul_proj_eq_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω]
    (S : ThetaSys o Ω) {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N) (hc : c.comp (AddSubgroup.inclusion h) ≠ c') :
    S.proj T c * S.proj T' c' = 0 := by
  haveI : IsDomain o := hA.inj.isDomain
  haveI := FreeNear.finite_char S T
  haveI := Fintype.ofFinite (T →+ ZMod S.N)
  rw [(thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.2 T T' h hT hT' c',
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.mul_sum]
  refine Finset.sum_eq_zero fun c'' hc'' => ?_
  rw [(FreeNear.proj_orthogonal S T hT).1, if_neg]
  rintro rfl
  rw [Set.Finite.mem_toFinset] at hc''
  exact hc hc''

theorem mul_dotProduct_mem_of_mem_span {o Ω J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J]
    (O : Subalgebra o Ω) (a : Ω) (u : J → Ω) (V : Set (J → Ω)) (hV : ∀ v ∈ V, a * (u ⬝ᵥ v) ∈ O) :
    ∀ v ∈ Submodule.span O V, a * (u ⬝ᵥ v) ∈ O := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem _ h' => exact hV _ h'
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add, mul_add]; exact add_mem hx hy
  | smul s x _ hx =>
    rw [dotProduct_smul, Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 hx

theorem ff_div_th_mul_dotProduct_mem : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → ∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N) (k : _) (i : S.J) (z : M.Z), S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z, S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
  intro o Ω _ _ _ _ S M U₀ EE hAdm hLL hT hS hG hW hB hE _ hEE ξ c k i
  have hO := hAdm.1
  have key : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z,
      S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
    intro z hz hI x₀ hx₀
    have hH : S.HH M ξ ≤ S.HH M z := AddSubgroup.closure_mono hI
    have hTT : S.TT M z ≤ S.TT M ξ := FirstIneq.perp_anti_of_le S hH
    rw [hEE z hz]
    refine mul_dotProduct_mem_of_mem_span _ _ _ _ ?_
    rintro _ ⟨c₁, k₁, x₁, i₁, hd, -, rfl⟩
    have e : S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ
        fun j => S.th x₁ / S.FF _ c₁ k₁ * algebraMap o Ω (S.proj _ c₁ j i₁)) =
        S.FF _ c k / S.FF _ c₁ k₁ * (S.th x₁ / S.th x₀) *
          algebraMap o Ω ((S.proj _ c * S.proj _ c₁) i i₁) := by
      simp only [dotProduct, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    by_cases hc : c.comp (AddSubgroup.inclusion hTT) = c₁
    swap
    · rw [proj_mul_proj_eq_zero S hTT (hG.1 ξ).1 (hG.1 z).1 c c₁ hc]
      simp
    refine mul_mem (mul_mem ?_ (hx₀.2 x₁)) (Subalgebra.algebraMap_mem _ _)
    have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (FirstIneq.ff_mem_ring S _ c k)
    have hf' : S.FF _ c₁ k₁ ∈ M.ringOn U₀ := hO.le (FirstIneq.ff_mem_ring S _ c₁ k₁)
    have hi : (S.FF _ c₁ k₁)⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c₁ k₁ (hG.1 z).1 hd.1
    refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
    · rw [div_eq_mul_inv]
      exact mul_mem hf hi
    intro p _ y hy
    obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT z p y hy
    have hker : S.HH M z = τ.yy.ker := (hS z p y y₀ τ hy hAt).2
    have hperp : S.perp τ.yy.ker = S.TT M z := by rw [← hker]; rfl
    obtain ⟨α, hα, hwt⟩ := (hW p y₀ τ).1 (c₁.comp (AddSubgroup.inclusion hperp.le))
    have h1 := (hB p y₀ τ hint (S.TT M ξ) c k (FirstIneq.ff_mem_ring S _ c k) (hG.1 ξ).1).1
      (hperp.le.trans hTT) (((hG.1 ξ).1.1.trans (hG.1 ξ).2.le).trans (hH.trans hker.le)) α hα
      (fun t h₁ h₂ => by rw [hwt, ← hc]; rfl)
    have h2 := hE z p y y₀ τ hy hAt c₁ k₁ α hd hα (fun t h₁ h₂ => by rw [hwt]; rfl)
    rw [hAt, ← h2] at h1
    set yg := gPt p ≫ y with hyg
    have w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have hw : yg w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
    have hsp := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton yg w)
    have e1 : M.val yg (S.FF _ c₁ k₁) * M.val yg (S.FF _ c₁ k₁)⁻¹ = 1 := by
      rw [← RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf') (RatModel.ringOn_le_O hw hi),
        mul_inv_cancel₀ hd.1, RatModel.val_one]
    rw [div_eq_mul_inv, RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf) (RatModel.ringOn_le_O hw hi),
      norm_mul, ← norm_one (α := PadicAlgCl p), ← e1, norm_mul]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  intro z hI x₀ hx₀
  obtain ⟨U, b, hzU, -, hb⟩ := EE.loc z
  obtain ⟨x, hxU, hxc, hzx, hIx⟩ := hG.2.2.2 z U hzU
  rw [hb z hzU]
  refine mul_dotProduct_mem_of_mem_span _ _ _ _ fun v hv => RatModel.O_le_of_specializes hzx ?_
  refine key x hxc (hIx ▸ hI) x₀ (hIx ▸ hx₀) v ?_
  rw [hb x hxU]
  exact Submodule.subset_span hv

end GlobalTheory.ZH.DualSection
