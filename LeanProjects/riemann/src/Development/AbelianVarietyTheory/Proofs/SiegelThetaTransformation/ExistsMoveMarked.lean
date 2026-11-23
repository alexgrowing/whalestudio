import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Move

theorem exists_pow_le {E : Type} [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)) {d : 𝓞 E} (hd : d ≠ 0) :
    ∃ N : ℕ, ∃ t, IsCoprime (Ideal.span {t}) 𝔪 ∧ ∀ b ∈ 𝔪 ^ N, t * b ∈ Ideal.span {d} := by
  haveI : Finite (𝓞 E ⧸ Ideal.span {d}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hd)
  haveI : IsArtinianRing (𝓞 E ⧸ Ideal.span {d}) := isArtinian_of_finite
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := 𝓞 E ⧸ Ideal.span {d}) (M := 𝓞 E ⧸ Ideal.span {d})
    ⟨fun n => OrderDual.toDual ((𝔪 ^ n).map (Ideal.Quotient.mk (Ideal.span {d}))),
      fun a b h => Ideal.map_mono (Ideal.pow_le_pow_right h)⟩
  have h1 : (𝔪 ^ N).map (Ideal.Quotient.mk (Ideal.span {d})) =
      (𝔪 ^ (N + 1)).map (Ideal.Quotient.mk (Ideal.span {d})) := hN (N + 1) (Nat.le_succ N)
  have h2 : 𝔪 ^ N ≤ Ideal.span {d} ⊔ 𝔪 • 𝔪 ^ N := by
    have := (Ideal.le_comap_map (f := Ideal.Quotient.mk (Ideal.span {d})) (I := 𝔪 ^ N))
    rw [h1, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_comm, pow_succ'] at this
    exact this
  exact ⟨N, Lev.nakayama (IsNoetherian.noetherian _) h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem exists_pow_smul {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) (v : Fin r → E) :
    ∃ N : ℕ, ∀ b ∈ 𝔪 ^ N, b • v ∈ Lev.loc 𝔪 (𝔪 • X.Λ) := by
  obtain ⟨k, hk, hx⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨N, t, ht, h⟩ := exists_pow_le 𝔪 (d := m * (k : 𝓞 E)) (mul_ne_zero hm0 (by exact_mod_cast hk))
  refine ⟨N, fun b hb => ⟨t, ht, ?_⟩⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h b hb)
  rw [← mul_smul, ← hc, mul_smul, mul_smul, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem_smul hm hx)

omit [IsCMField E] in

theorem isUnit_cols {𝔪 : Ideal (𝓞 E)} (h1 : 𝔪 ≠ ⊤) {L : Lt E r} (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) {u : Fin r → Fin r → E}
    (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ 𝔪 • L) : IsUnit (Matrix.of u)ᵀ := by
  obtain ⟨s, hs, hN⟩ := Lev.nakayama hfg h
  have hs0 : (s : E) ≠ 0 := by simpa using Lev.cop_ne_zero h1 hs
  have hli : LinearIndependent E u := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
    rw [← hsp, Submodule.span_le]
    intro v hv
    have := Submodule.span_le_restrictScalars (𝓞 E) E _ (hN v hv)
    exact (Submodule.smul_mem_iff _ hs0).1 this
  exact Matrix.linearIndependent_cols_iff_isUnit.1 hli

theorem exists_cong (D : SW.Level X) {L : Lt E r} {u : Fin r → Fin r → E} (hL : SelfD X L)
    (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L) :
    ∃ ga : GL (Fin r) E, IsUn X ga ∧
      ∀ i, Cong X D.𝔪 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i) (D.β i) := by
  obtain ⟨U, hU⟩ := isUnit_cols D.proper hL.1 (TensLat.span_of_selfD X hL) h
  obtain ⟨B, hB⟩ := isUnit_cols D.proper X.Λ_fg X.Λ_span D.β_span
  have hA (i) : ((B * U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u i = D.β i := by
    have e1 : u i = (U : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1 := by
      rw [hU]; funext k; simp
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, hB]
    funext k; simp
  choose N hN using fun p : Fin r × Fin r × Fin r =>
    exists_pow_smul (X := X) D.ne_bot (Pi.single p.2.1 (u p.1 p.2.2))
  obtain ⟨ga, hu, s, hs, hb⟩ := GlobalTheory.T.strong_approximation_unitary_congruence E r X D.𝔪 D.ne_bot D.cop (B * U⁻¹) (Finset.univ.sup N)
  choose b hb e using hb
  refine ⟨ga, hu, fun i => Lev.cong_iff.2 (Lev.loc_loc hs ?_)⟩
  have e2 : s • ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i - D.β i) =
      ∑ k, ∑ j, b k j • (Pi.single k (u i j) : Fin r → E) := by
    rw [← hA]
    funext k
    simp only [Lev.O_smul, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply,
      Matrix.mulVec, dotProduct, ← e]
    rw [← Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k (fun k' _ hk => by rw [if_neg (Ne.symm hk), mul_zero]) (by simp), if_pos rfl]
    change (s : E) * _ = _
    ring
  rw [e2]
  exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ =>
    hN (i, k, j) _ (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ _)) (hb k j))

theorem mem_lats (D : SW.Level X) {L : Lt E r} {u : Fin r → Fin r → E} (hΛ : SelfD X X.Λ) (hL : SelfD X L)
    (hu : ∀ i, u i ∈ L) (h : L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L)
    (hc : ∀ i, Cong X D.𝔪 (u i) (D.β i)) : L ∈ D.lats := by
  have h1 : L ≤ Lev.loc D.𝔪 X.Λ := by
    obtain ⟨s, hs, hN⟩ := Lev.nakayama hL.1 h
    intro v hv
    refine Lev.loc_loc hs (Submodule.span_le.2 ?_ (hN v hv))
    rintro _ ⟨i, rfl⟩
    have := add_mem (Lev.loc_mono Submodule.smul_le_right (Lev.cong_iff.1 (hc i)))
      (Lev.le_loc _ (D.β_mem i))
    rwa [sub_add_cancel] at this
  have h2 : X.Λ ≤ L ⊔ D.𝔪 • X.Λ := by
    refine D.β_span.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    refine Lev.mem_of_loc (D.β_mem i) le_sup_right ?_
    have := add_mem (Lev.loc_mono (le_sup_right (a := L)) (Lev.cong_iff.1 (Lev.cong_symm (hc i))))
      (Lev.le_loc _ (Submodule.mem_sup_left (hu i)))
    rwa [sub_add_cancel] at this
  obtain ⟨s, hs, h1⟩ := Lev.exists_mul_of_fg hL.1 h1
  obtain ⟨t, ht, h2⟩ := Lev.nakayama X.Λ_fg h2
  have h1' (v) (hv : v ∈ L) : Lev.bar t • v ∈ X.Λ := (hΛ.2 _).2 fun y hy => by
    rw [Lev.EF_smul, Lev.bar_bar]
    exact (hL.2 _).1 hv _ (h2 y hy)
  have h2' (v) (hv : v ∈ X.Λ) : Lev.bar s • v ∈ L := (hL.2 _).2 fun y hy => by
    rw [Lev.EF_smul, Lev.bar_bar]
    exact (hΛ.2 _).1 hv _ (h1 y hy)
  obtain ⟨a, b, hab⟩ := Lev.cop_glue D.cop hs (Lev.cop_bar ht)
  obtain ⟨a', b', hab'⟩ := Lev.cop_glue D.cop ht (Lev.cop_bar hs)
  refine ⟨hL, _, Lev.cop_mul hab hab', fun v hv => ?_, fun v hv => ?_⟩
  · rw [mul_comm, mul_smul]
    refine X.Λ.smul_mem _ ?_
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (X.Λ.smul_mem _ (h1 v hv)) (X.Λ.smul_mem _ (h1' v hv))
  · rw [mul_smul]
    refine L.smul_mem _ ?_
    rw [add_smul, mul_smul, mul_smul]
    exact add_mem (L.smul_mem _ (h2 v hv)) (L.smul_mem _ (h2' v hv))

end GlobalTheory.Dict.Move

theorem GlobalTheory.Dict.exists_move_marked : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (D : SW.Level X) (L : Lt E r) (u : Fin r → Fin r → E), SelfD X X.Λ → SelfD X L → (∀ i, u i ∈ L) → L ≤ Submodule.span (𝓞 E) (Set.range u) ⊔ D.𝔪 • L → ∃ ga : GL (Fin r) E, IsUn X ga ∧ mapL ga L ∈ D.lats ∧ ∀ i, Cong X D.𝔪 ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u i) (D.β i) := by
  intro E _ _ _ r X D L u hΛ hL hu h
  obtain ⟨ga, hun, hc⟩ := Move.exists_cong D hL h
  refine ⟨ga, hun, Move.mem_lats D (u := fun i => Lev.lin ga (u i)) hΛ (Lev.selfD_mapL hun hL)
    (fun i => ⟨_, hu i, rfl⟩) ?_ hc, hc⟩
  refine (Submodule.map_mono (f := Lev.lin ga) h).trans ?_
  rw [Submodule.map_sup, Submodule.map_span, ← Set.range_comp, Submodule.map_smul'']
  exact le_rfl
