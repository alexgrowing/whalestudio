import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocksStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMapStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace LevelTowerAlt

theorem exists_join {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'}
    {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
    [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)
    (hT' : CoordTie ℤ ξ' fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (g : X' ⟶ X) (i : Ω →+* Ω')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ g i) :
    ∃ (K₃ : Type) (_ : Fintype K₃) (J₃ : K₃ → Type) (_ : ∀ k, Fintype (J₃ k)) (y₃ : (Σ k, J₃ k) → Ω') (bk : K → K₃)
      (bx : ∀ k, J k ≃ J₃ (bk k)), Nonempty K₃ ∧ Function.Injective bk ∧ (∀ k x, y₃ ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧
      CoordTie ℤ ξ' fun c' : (k : K₃) → J₃ k => ∏ k, y₃ ⟨k, c' k⟩ := by
  let J₁ : K ⊕ Unit → Type := Sum.elim J fun _ => Unit
  letI : ∀ k, Fintype (J₁ k) := fun k => match k with
    | .inl k => (inferInstance : Fintype (J k))
    | .inr _ => (inferInstance : Fintype Unit)
  let s : (Σ k, J₁ k) → Ω' := fun q => match q with
    | ⟨.inl k, a⟩ => i (y ⟨k, a⟩)
    | ⟨.inr _, _⟩ => 1
  have h1 := GlobalTheory.T.coords_join_blocks X' Ω' ξ' K' J' y' (K ⊕ Unit) J₁ s hT' (by
    rintro (k | k) p
    · obtain ⟨hsp, hreg, -⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' g i hd p
      obtain ⟨c, hc⟩ := hT.cover ⟨g p.1, hsp⟩
      refine ⟨c k, (map_ne_zero i).2 (TiePrimes.ne_of_seg hc.1 k), fun a => ?_⟩
      have := hreg _ (TiePrimes.ratio_mem hc ⟨k, a⟩)
      rw [map_div₀] at this
      exact this
    · refine ⟨(), one_ne_zero, fun a => ?_⟩
      show (1 : Ω') / 1 ∈ _
      rw [div_one]; exact one_mem _)
  let J₃ : K' ⊕ (K ⊕ Unit) → Type := Sum.elim J' J₁
  let y₃ : (Σ k, J₃ k) → Ω' := fun q => match q with
    | ⟨.inl k, a⟩ => y' ⟨k, a⟩
    | ⟨.inr k, a⟩ => s ⟨k, a⟩
  refine ⟨K' ⊕ (K ⊕ Unit), inferInstance, J₃, fun k => match k with
    | .inl k => (inferInstance : Fintype (J' k))
    | .inr k => (inferInstance : Fintype (J₁ k)), y₃, fun k => .inr (.inl k), fun k => Equiv.refl _,
    ⟨.inr (.inr ())⟩, fun a b h => by simpa using h, fun _ _ => rfl, ?_⟩
  have e : (fun c' : (k : K' ⊕ (K ⊕ Unit)) → J₃ k => ∏ k, y₃ ⟨k, c' k⟩) =
      fun c' : (k : K' ⊕ (K ⊕ Unit)) → Sum.elim J' J₁ k =>
        (∏ k, y' ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ :=
    funext fun c' => Fintype.prod_sum_type _
  rw [e]; exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
  {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω}

@[reducible] def reTie (B : HodgeCpt Y S y) (h : CoordTie ℤ B.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) :
    HodgeCpt Y S y' := { B with tie := h }

theorem flag_zero [∀ k, Fintype (J k)] (B : HodgeCpt Y S y) (d : ℕ) (hc : B.IsCover d) (h0 : D.p + D.q = 0) :
    Nonempty B.Flag := by
  have hrk : ∀ s, labelRk D s = 0 := by
    rintro (τ | τ)
    · show D.p = 0; omega
    · show D.q = 0; omega
  haveI : ∀ s, IsEmpty (Fin (labelRk D s)) := fun s => by rw [hrk s]; infer_instance
  have hV : ∀ s, B.Vgen s = ⊥ := fun s => by
    obtain ⟨U, -, b, hb, -⟩ := B.vb s ⟨_, specializes_rfl⟩ trivial
    refine hb.symm.trans ?_
    rw [Set.range_eq_empty, Submodule.span_empty]
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Y.X Y.t.G B.Ω₀ B.ξ₀
  obtain ⟨j, hj⟩ := GlobalTheory.T.lie_model_pullback_map Y.X B.X B.Ω₀ Ω B.ξ₀ B.ξ B.f B.fn Y.t.G B.t.G B.m.φ Li₀ B.Li M₀ B.M B.fn_over B.m.cart
  obtain ⟨hext, -, -⟩ := GlobalTheory.T.lie_lattice_dominant_compat Y.X B.X B.Ω₀ Ω B.ξ₀ B.ξ B.f B.fn Y.t.G B.t.G B.m.φ Li₀ B.Li M₀ B.M j B.gen₀
    B.tie.gen B.fn_over B.m.cart Y.t.semi.smooth hj
  refine ⟨{ b := fun _ => isEmptyElim, sub := fun s p _ => ?_, Li₀ := Li₀, M₀ := M₀, j := j, j_pt := hj,
            V₀ := fun _ => ⊥, V₀_mem := fun s e => ?_, deg := d, generic := ?_ }⟩
  · obtain ⟨U, hU, b, -, hb⟩ := B.vb s p trivial
    exact ⟨U, hU, b, fun _ => by rw [Subsingleton.elim b isEmptyElim], hb⟩
  · rw [hV, Submodule.mem_bot, Submodule.mem_bot]
    refine ⟨fun h => by rw [h, map_zero], fun h => by_contra fun hne => ?_⟩
    have := hext.2 1 (fun _ => e) (linearIndependent_unique_iff.2 hne)
    exact this.ne_zero 0 h
  · letI := B.fn.toAlgebra
    refine ⟨fun _ => isEmptyElim, fun _ => 0, fun s => ⟨linearIndependent_empty_type, ?_⟩, hext.1,
      fun _ => linearIndependent_empty_type, fun _ => linearIndependent_empty_type, fun _ => isEmptyElim,
      fun _ => isEmptyElim, fun s i => congrArg (fun b => flagStep Ω b i) (Subsingleton.elim _ _), ?_, hc.1, ?_⟩
    · rw [Set.range_eq_empty, Submodule.span_empty]
    · haveI : IsEmpty (Σ σ : CMType H ⊕ CMType H,
          {lk : Fin (labelRk D σ) × Fin (labelRk D σ) // lk.2 < lk.1}) := ⟨fun q => isEmptyElim q.2.1.1⟩
      exact algebraicIndependent_empty_type
    · haveI : IsEmpty (Σ σ : CMType H ⊕ CMType H, Fin (labelRk D σ) × Fin (labelRk D σ)) :=
        ⟨fun q => isEmptyElim q.2.1⟩
      rw [Set.range_eq_empty, IntermediateField.adjoin_empty, IntermediateField.finrank_bot']
      exact hc.2

end LevelTowerAlt
