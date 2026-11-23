import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

namespace ThetaSys

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω)

theorem supI_subset_of_specializes {ξ z : M.Z} (h : ξ ⤳ z) : S.supI M z ⊆ S.supI M ξ :=
  fun _ hx => ⟨hx.1, fun j => M.O_le_of_specializes h (hx.2 j)⟩

theorem exists_isClosed_supI_eq [JacobsonSpace M.Z] (ξ : M.Z) (W : M.Z.Opens) (hξ : ξ ∈ W) :
    ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hV : IsOpen ((W : Set M.Z) ∩ ⋂ a ∈ S.supI M ξ, {z | M.Div S.th a z}) :=
    W.isOpen.inter ((Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _)
  obtain ⟨x, ⟨⟨hxW, hxI⟩, hxc⟩, hx⟩ := nonempty_inter_closedPoints
    (Z := ((W : Set M.Z) ∩ ⋂ a ∈ S.supI M ξ, {z | M.Div S.th a z}) ∩ closure {ξ})
    ⟨ξ, ⟨hξ, Set.mem_iInter₂.mpr fun _ ha => ha⟩, subset_closure rfl⟩
    (hV.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hs : ξ ⤳ x := specializes_iff_mem_closure.mpr hxc
  exact ⟨x, hxW, hx, hs, (S.supI_subset_of_specializes M hs).antisymm
    fun a ha => Set.mem_iInter₂.mp hxI a ha⟩

theorem Over₀.supI_eq {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (h : S.Over₀ M U₀)
    {ξ : M.Z} (hξ : ξ ∈ U₀) : S.supI M ξ = {x | S.th x ≠ 0} := by
  ext x
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun j => ?_⟩⟩
  have h1 : S.th j / S.th x ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]
    exact mul_mem (h.le (S.th_mem j)) (h.th_unit x hx)
  exact (Algebra.mem_iInf.mp (Algebra.mem_iInf.mp h1 ξ) hξ :)

end ThetaSys

theorem isoFree_TT_and_supI_specializes :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) := by
  intro o Ω _ _ _ _ S M U₀ hO ⟨hL, hJ⟩ hT hS
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  refine ⟨fun ξ => ⟨?_, hpp _⟩, fun ξ z h => S.supI_subset_of_specializes M h, fun ξ hξ => ?_,
    fun ξ W hξ => S.exists_isClosed_supI_eq M ξ W hξ⟩
  · obtain ⟨x, -, hx, -, he⟩ := S.exists_isClosed_supI_eq M ξ ⊤ trivial
    obtain ⟨p, hp, y, hy⟩ := (hL U₀ le_rfl hO.ne x hx).1
    obtain ⟨y₀, hy₀, -, ⟨τ⟩⟩ := hT x p y hy
    have h1 : S.HH M ξ = τ.yy.ker := by
      rw [← (hS x p y y₀ τ hy hy₀).2, ThetaSys.HH, ThetaSys.HH, he]
    rw [ThetaSys.TT, h1]
    exact τ.isoFree
  · have h1 : S.perp ⊥ = ⊤ := by
      refine top_unique fun a _ h hh => ?_
      rw [AddSubgroup.mem_bot.mp hh]
      simp [eStd]
    rw [ThetaSys.TT, ThetaSys.HH, hO.supI_eq hξ, S.supp, ← h1, hpp]

end GlobalTheory.ZH
