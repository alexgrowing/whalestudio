import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColMinorEqSupMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFiniteIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionRegularFunctionsGoodPrimesStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat.CramerFrame

theorem exists_rows_max_minor : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : Y.X.Opens) (p : ℕ), p.Prime → genericPoint Y.X ∈ W → ∀ {g : ℕ}, 0 < g → ∀ (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn), (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → ∀ (U₁ : V.X.Opens) (m : ℕ) (f : ∀ k : ℕ, (Fin k → Fin (g + g)) → V.X.functionField), 0 < m → (∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)) (z : V.G), V.j z ∈ U₁ → RegAt (V.j z) (f k τ) ∧ (UnitAt (V.j z) (f k τ) ↔ UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk τ))) → (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U₁ → ∀ (k : ℕ) (hk : k ≤ g), 0 < colMinor e.w (valMat V H (T (below y.1)) z) (Finset.univ.filter fun l : Fin g => (l : ℕ) < k) ∧ ∀ τ : Fin k → Fin (g + g), e.w (valAt (z ≫ V.j) (f k τ)) = (e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) / colMinor e.w (valMat V H (T (below y.1)) z) (Finset.univ.filter fun l : Fin g => (l : ℕ) < k)) ^ m) → ∀ x ∈ U₁, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (U' : V.X.Opens) (σ : ∀ k : ℕ, Fin k → Fin (g + g)), U' ≤ U₁ ∧ x ∈ U' ∧ (∀ (k : ℕ) (hk : k ≤ g), minorAt H k hk (σ k) ≠ 0) ∧ (∀ z : V.G, V.j z ∈ U' → ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk (σ k))) ∧ (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U' → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)), e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) ≤ e.w (minorAt (valMat V H (T (below y.1)) z) k hk (σ k))) := by
  intro F _ _ Y V W p hp hW g hg H d T hT U₁ m f hm hreg hval x hx hxp
  have : Nonempty (Fin (g + g)) := ⟨⟨0, by omega⟩⟩
  have key : ∀ k : ℕ, ∃ (s : Fin k → Fin (g + g)) (N : V.X.Opens), x ∈ N ∧ (k ≤ g → ∀ y ∈ N, UnitAt y (f k s)) := by
    intro k
    by_cases hk : k ≤ g
    · obtain ⟨s, hs⟩ := GlobalTheory.T.reduction_regular_functions_good_primes F Y V p hp W hW U₁ (f k) (fun s z hz => (hreg k hk s z hz).1)
        (fun v hv e y hy z yt h1 h2 h3 => by
          obtain ⟨hpos, hw⟩ := hval v hv e y hy z yt h1 h2 h3 k hk
          have hc := colMinor_filter_lt_eq_iSup_minorAt e.w (valMat V H (T (below y.1)) z) k hk
          refine ⟨fun s => ?_, ?_⟩
          · rw [hw]
            refine pow_le_one₀ (div_nonneg (e.w.nonneg _) hpos.le) ((div_le_one hpos).2 ?_)
            rw [hc]
            exact le_ciSup (f := fun τ : Fin k → Fin (g + g) =>
              e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ)) (Set.finite_range _).bddAbove s
          · obtain ⟨s, hs⟩ := exists_eq_ciSup_of_finite (f := fun τ : Fin k → Fin (g + g) =>
              e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ))
            refine ⟨s, ?_⟩
            rw [hw, hs, ← hc, div_self hpos.ne', one_pow]) x hx hxp
      obtain ⟨N, hN, hN'⟩ := hs.exists_nhds
      exact ⟨s, N, hN, fun _ => hN'⟩
    · exact ⟨fun _ => ⟨0, by omega⟩, ⊤, trivial, fun h => absurd h hk⟩
  choose σ N hxN hN using key
  let U' : V.X.Opens := U₁ ⊓ (Finset.range (g + 1)).inf N
  have hle : U' ≤ U₁ := inf_le_left
  have hleN : ∀ k, k ≤ g → U' ≤ N k := fun k hk =>
    inf_le_right.trans (Finset.inf_le (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  have hxU : x ∈ U' := by
    refine ⟨hx, ?_⟩
    have : ∀ s : Finset ℕ, x ∈ s.inf N := fun s => by
      induction s using Finset.induction_on with
      | empty => trivial
      | insert a s _ ih => rw [Finset.inf_insert]; exact ⟨hxN a, ih⟩
    exact this _
  have ha : ∀ z : V.G, V.j z ∈ U' → ∀ (k : ℕ) (hk : k ≤ g),
      UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk (σ k)) := fun z hz k hk =>
    (hreg k hk (σ k) z (hle hz)).2.1 (hN k hk _ (hleN k hk hz))
  refine ⟨U', σ, hle, hxU, fun k hk => ?_, ha, ?_⟩
  · have hgen : V.j (genericPoint V.G) ∈ U' :=
      ((HtGen.SplitCover.j_gen_specializes V).trans (genericPoint_specializes x)).mem_open U'.isOpen hxU
    have hne := (ha _ hgen k hk).ne_zero
    have hd : ∀ i, ((T (V.π (genericPoint V.G))).map V.φ) i i ≠ 0 := fun i => by
      rw [Matrix.map_apply, (hT _).2 i]
      exact (map_ne_zero V.φ).2 (Units.ne_zero _)
    have htri : ((T (V.π (genericPoint V.G))).map V.φ).BlockTriangular id := fun i j hij => by
      rw [Matrix.map_apply, (hT _).1 hij, map_zero]
    rw [minorAt_triChange H _ htri hd k hk]
    exact mul_ne_zero hne (prod_diag_ne_zero _ hd k hk)
  · intro v hv e y hy z yt h1 h2 h3 k hk τ
    have h3' : ⊤ ≤ yt ⁻¹ᵁ U₁ := fun q hq => hle (h3 hq)
    obtain ⟨hpos, hw⟩ := hval v hv e y hy z yt h1 h2 h3' k hk
    have hc := colMinor_filter_lt_eq_iSup_minorAt e.w (valMat V H (T (below y.1)) z) k hk
    have hcl : yt (IsLocalRing.closedPoint e.O) ∈ U' := h3 trivial
    have h1' := NormExt.w_valAt_eq_one e yt (hN k hk _ (hleN k hk hcl))
    rw [h2, hw, pow_eq_one_iff_of_nonneg (div_nonneg (e.w.nonneg _) hpos.le) hm.ne', div_eq_one_iff_eq hpos.ne'] at h1'
    rw [h1', hc]
    exact le_ciSup (f := fun τ : Fin k → Fin (g + g) =>
      e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ)) (Set.finite_range _).bddAbove τ

end GlobalTheory.ConstLat.CramerFrame

end
