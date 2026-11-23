import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.T0

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem qlen_of_idx (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (la : HeightOneSpectrum (𝓞 B.KO))
    (hLat : InLat X ka la S wL wF T) (hΘM : X.Theta S ka wL wF T ≤ X.Msup ka) (e r : ℝ)
    (h : ∀ U : Submodule (X.Kl la) ↥(WL X ka la),
      (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(WL X ka la) (MW X ka la ⊓ U.restrictScalars (X.Ol la))
        (ThW X S ka wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤ e * (finrank (X.Kl la) U : ℝ) + r)
    (V' : Submodule (X.Kl la) (X.Vl la)) (hV' : V' ≤ X.locK la (X.Msup ka)) :
    X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤ e * (finrank (X.Kl la) V' : ℝ) + r := by
  have hb := h (V'.comap (WL X ka la).subtype)
  have hrk : finrank (X.Kl la) ↥(V'.comap (WL X ka la).subtype) = finrank (X.Kl la) V' :=
    (Submodule.comapSubtypeEquivOfLe hV').finrank_eq
  have hq := qlen_eq_inW X ka la (X.loc la (X.Msup ka)) (X.loc la (X.Theta S ka wL wF T)) V' hV'
  have hle : ThW X S ka wL wF T la ≤ MW X ka la :=
    Submodule.comap_mono (Submodule.span_mono (Set.image_mono hΘM))
  have h0 := qlen_eq_zero_of_le
    (MW X ka la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (ThW X S ka wL wF T la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (inf_le_inf_right _ hle)
  have hfin := qlen_inf_ne_top (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) (ThW X S ka wL wF T la)
    hLat.1 hLat.2 ((V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
  rw [← hq]
  refine ⟨hfin, ?_⟩
  rw [hrk] at hb
  unfold Formalism.LatticeIndexTer.idx at hb
  rw [h0] at hb
  have hb' := hb
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero, Int.cast_natCast] at hb'
  exact hb'

theorem qlen_of_idx_of_hyp {large₂ : SizeData₂ D} (X : PJ D B P j) {H : KHyp} {C2 A2 CR Bx CT : ℝ} (S : Scal B)
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) (la : HeightOneSpectrum (𝓞 B.KO))
    (hLat : InLat X ka la S wL wF T) (e r : ℝ)
    (h : ∀ U : Submodule (X.Kl la) ↥(WL X ka la),
      (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(WL X ka la) (MW X ka la ⊓ U.restrictScalars (X.Ol la))
        (ThW X S ka wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤ e * (finrank (X.Kl la) U : ℝ) + r)
    (V' : Submodule (X.Kl la) (X.Vl la)) (hV' : V' ≤ X.locK la (X.Msup ka)) :
    X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤ e * (finrank (X.Kl la) V' : ℝ) + r :=
  qlen_of_idx X S ka wL wF T la hLat (theta_le_msup_of_hyp X S hH) e r h V' hV'

theorem isLattice_of_admissible (h : WeightAlgebra.adm1 B) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j) :
    Submodule.IsLattice B.KO (B.Mlat j ka) := h j h1 h2 ka

theorem span_eq_top_of_shortG {X : PJ D B P j} {w : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {β : ℝ}
    (h : ShortG X w N β) : Submodule.span B.KO (N : Set (B.Cusp j w)) = ⊤ := by
  obtain ⟨Sh, h1, h2, -⟩ := h
  exact top_le_iff.1 (h2 ▸ Submodule.span_mono h1)

theorem span_Thc_of_hyp {large₂ : SizeData₂ D} {X : PJ D B P j} {H : KHyp} {C2 A2 CR Bx CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) :
    Submodule.span B.KO (X.Thc S.sF wF : Set (B.Cusp j wF)) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.s0 (X.wF0 wL wF) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.sK ka : Set (B.Cusp j ka)) = ⊤ := by
  obtain ⟨-, -, ⟨-, -, -, -, -, po, -, -, PLam, -, -, hF, h0', hK⟩, -⟩ := hH
  exact ⟨span_eq_top_of_shortG hF, span_eq_top_of_shortG h0', span_eq_top_of_shortG hK⟩

end Formalism.MainNotions.Gaps.EtaleWeightGaps
