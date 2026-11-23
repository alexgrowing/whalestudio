import Formalism.LocalRingCardinality.SpanPowerMembership.UrRing

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Ur IsLocalRing

structure UrPkg (l : ℕ) [Fact l.Prime] (O0 : Type) [CommRing O0] : Type 1 where
  O : Type
  [crO : CommRing O]
  [domO : IsDomain O]
  [dvrO : IsDiscreteValuationRing O]
  [algO : Algebra O0 O]
  O_inj : Function.Injective (algebraMap O0 O)
  O_l : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O
  [topO : TopologicalSpace O]
  [trO : IsTopologicalRing O]
  O_adic : IsAdic (IsLocalRing.maximalIdeal O)
  resO_ac : IsAlgClosed (IsLocalRing.ResidueField O)
  O_complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  Ok : ℕ → Type
  [crOk : ∀ k, CommRing (Ok k)]
  [domOk : ∀ k, IsDomain (Ok k)]
  [dvrOk : ∀ k, IsDiscreteValuationRing (Ok k)]
  [algOk : ∀ k, Algebra O (Ok k)]
  Ok_inj : ∀ k, Function.Injective (algebraMap O (Ok k))
  Ok_fin : ∀ k, Module.Finite O (Ok k)
  zk : ∀ k, (Ok k)ˣ
  zk_prim : ∀ k, IsPrimitiveRoot ((zk k : Ok k)) (l ^ k)
  Ok_gen : ∀ k (x : FractionRing (Ok k)), ∃ p : Polynomial O, ∃ d : O, d ≠ 0 ∧
    x * algebraMap (Ok k) (FractionRing (Ok k)) (algebraMap O (Ok k) d) =
      algebraMap (Ok k) (FractionRing (Ok k)) (Polynomial.aeval (zk k : Ok k) p)
  iC : FractionRing O →+* ℂ_[l]
  iC_int : ∀ x : FractionRing O, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range

theorem urPkg_nonempty (l : ℕ) [hl : Fact l.Prime] (O0 : Type) [CommRing O0] [IsDomain O0]
    [IsDiscreteValuationRing O0] (j : O0 →+* ℂ_[l]) (hj : Function.Injective j) (hle : ∀ x, ‖j x‖ ≤ 1)
    (hlt : ∀ x ∈ maximalIdeal O0, ‖j x‖ < 1) : Nonempty (UrPkg l O0) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O0
  have h0 : j ϖ ≠ 0 := (map_ne_zero_iff j hj).mpr hϖ.ne_zero
  have h1 : ‖j ϖ‖ < 1 := hlt ϖ hϖ.not_isUnit
  have hu : ∀ u : O0ˣ, ‖j u‖ = 1 := fun u => le_antisymm (hle _) (by
    have h : ‖j u‖ * ‖j (u⁻¹ : O0ˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
    nlinarith [hle (u⁻¹ : O0ˣ), norm_nonneg (j u), norm_nonneg (j (u⁻¹ : O0ˣ))])
  have hn : ∀ a : O0, a ≠ 0 → ∃ n : ℕ, ‖j a‖ = ‖j ϖ‖ ^ n := fun a ha => by
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    exact ⟨n, by rw [map_mul, norm_mul, hu, one_mul, map_pow, norm_pow]⟩
  let J : FractionRing O0 →+* ℂ_[l] := IsFractionRing.lift hj
  have hJ : ∀ a, J (algebraMap _ _ a) = j a := IsFractionRing.lift_algebraMap hj
  have hL : Disc J.fieldRange (j ϖ) := by
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O0) x
    rw [map_div₀, hJ, hJ] at hx ⊢
    obtain ⟨n, hn1⟩ := hn a (by rintro rfl; simp at hx)
    obtain ⟨m, hm⟩ := hn b (nonZeroDivisors.ne_zero hb)
    exact ⟨n - m, by rw [norm_div, hn1, hm, zpow_sub₀ (norm_ne_zero_iff.mpr h0), zpow_natCast, zpow_natCast]⟩
  obtain ⟨M, hLM, hM⟩ := exists_max _ _ hL
  have hmem : ∀ a, j a ∈ M := fun a => hLM ⟨_, hJ a⟩
  have hc := closed_of_max hM
  have := isDVR (hmem ϖ) h0 h1 hM.1
  let _ : Algebra O0 (ball M) := (j.codRestrict (ball M) fun a => (show j a ∈ ball M from And.intro (hmem a) (hle a))).toAlgebra
  have hζ : ∀ k : ℕ, ∃ ζ : ℂ_[l], IsPrimitiveRoot ζ (l ^ k) := fun k =>
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero k hl.out.ne_zero⟩
    HasEnoughRootsOfUnity.exists_primitiveRoot _ _
  choose ζ hζ using hζ
  have hpos : ∀ k, 0 < l ^ k := fun k => pow_pos hl.out.pos k
  have hint : ∀ k, IsIntegral M (ζ k) := fun k =>
    ⟨Polynomial.X ^ (l ^ k) - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ (hpos k).ne', by
      simp [(hζ k).pow_eq_one]⟩
  have hnorm : ∀ k, ‖ζ k‖ = 1 := fun k =>
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (hpos k).ne').mp (by rw [← norm_pow, (hζ k).pow_eq_one, norm_one])
  let z : ∀ k, ball (ext M (ζ k)) := fun k =>
    ⟨ζ k, IntermediateField.mem_adjoin_simple_self M (ζ k), (hnorm k).le⟩
  have hz : ∀ k, IsUnit (z k) := fun k => (Ur.isUnit_iff _ _).mpr (hnorm k)
  have hext := fun k => ext_spec (hπ := hmem ϖ) (h0 := h0) (h1 := h1) (hD := hM.1) (ζ := ζ k) hc (hint k)
  exact ⟨{ O := ball M
           O_inj := fun a b h => hj (congrArg (fun t : ball M => (t : ℂ_[l])) h)
           O_l := (mem_max M _).mpr (by
             rw [SubringClass.coe_natCast, ← map_natCast (algebraMap ℚ_[l] ℂ_[l])]
             exact (norm_algebraMap' ℂ_[l] (l : ℚ_[l])).trans_lt Padic.norm_p_lt_one)
           O_adic := isAdic (hmem ϖ) h0 h1 hM.1
           resO_ac := res_algClosed hM
           O_complete := isComplete (hmem ϖ) h0 h1 hM.1 hc
           Ok := fun k => ball (ext M (ζ k))
           dvrOk := fun k => (hext k).2
           Ok_inj := fun k => ext_inj M (ζ k)
           Ok_fin := fun k => (hext k).1
           zk := fun k => (hz k).unit
           zk_prim := fun k => IsPrimitiveRoot.of_map_of_injective (f := (ball (ext M (ζ k))).subtype)
             (hζ k) Subtype.val_injective
           Ok_gen := fun k => ext_gen (ζ := ζ k) (hint k) (z k) rfl
           iC := Ur.iC M
           iC_int := Ur.iC_int M }⟩

end Formalism.BasicNotions.Examples₂
