import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoPolPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKaehlerFormCongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsExphOfCover
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

section
local notation "T_base" => GlobalTheory.ShFam.lbIso_polPull
local notation "T_rel" => GlobalTheory.ShFam.RelAmpleFlag.eventually_ample
local notation "T_ab" => GlobalTheory.AmpleKaehler.exists_ample_model
local notation "T_fam" => GlobalTheory.ConjExph.exists_exph_conjComm

theorem GlobalTheory.existsPolDat : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)) (h0 : RefMets Φ), Nonempty (PolDat s Φ hm h0) := by
  intro D A N j S κ s Φ hm h0
  have : IsTotallyComplex D.what₂.LL := ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.1 fun hv => by
    let φ : D.host.E →+* D.what₂.LL := κ.e.symm.toRingHom.comp (D.host.φ₀.codRestrict κ.c.F (κ.c.conj _))
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (v.comap φ)) (hv.comap φ)⟩
  let μ : Fin N → ℤ := fun i => -(i : ℤ)
  have hμ : StrictAnti μ := fun a b h => neg_lt_neg (by exact_mod_cast h)
  choose n₀ hn₀ using fun k => T_rel D A N j S κ s Φ k μ hμ _ _ s.isRec.ample (T_base D A N j S κ s Φ k)
  let n : ℕ+ := ⟨(Finset.univ.sup n₀) + 1, Nat.succ_pos _⟩
  choose M h₁ h₂ h₃ h₄ h₅ using fun k => T_ab _ _ _ (hn₀ k n ((Finset.le_sup (Finset.mem_univ k)).trans (Nat.le_succ _)))
  choose E hE hE' using fun k => T_fam _ (Φ.C k).Y _ (fun σ => (h₄ k σ).2) (h₅ k)
  obtain ⟨a, K, δ, hc⟩ : ∃ a K δ, (∃ a' K' δ', CommonConst hm h0 (fun k σ => curvMet ((M k).m σ)) E a' K' δ') →
      CommonConst hm h0 (fun k σ => curvMet ((M k).m σ)) E a K δ := by
    by_cases h : ∃ a' K' δ', CommonConst hm h0 (fun k σ => curvMet ((M k).m σ)) E a' K' δ'
    · obtain ⟨a, K, δ, h⟩ := h
      exact ⟨a, K, δ, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h' => (h h').elim⟩
  let Q : ℕ := Finset.univ.sup (fun k => (((M k).divide n).n : ℕ)) + 1
  have hn : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 n.ne_zero
  refine ⟨⟨1, one_pos, ((n : ℕ) : ℚ)⁻¹, by positivity, μ, hμ, fun k => (M k).divide n, fun k => ?_, h₂, fun k => ?_,
    fun k σ => (h₄ k σ).1, _, fun k σ => (h₄ k σ).2, h₅, (Q : ℝ)⁻¹, by positivity, fun k σ c y hy ξ => ?_, E, hE, hE',
    a, K, δ, hc⟩⟩
  · have e : qDiv ((M k).divide n) = ((n : ℕ) : ℚ)⁻¹ • qDiv (M k) := by
      simp [qDiv, Adl.divide, TensorProduct.smul_tmul', mul_comm]
    rw [e, h₁, qL]
    simp only [← natCast_zsmul, TensorProduct.tmul_sub, TensorProduct.tmul_sum, smul_sub, Finset.smul_sum,
      ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', zsmul_eq_mul, smul_eq_mul, dirOf, ← Finset.sum_neg_distrib,
      ← TensorProduct.neg_tmul]
    rw [sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => (TensorProduct.sub_tmul _ _ _).symm.trans (congrArg (· ⊗ₜ _) ?_)
      unfold varpi
      split_ifs <;> push_cast <;> field_simp <;> ring
    · simp [hn]
  · obtain ⟨Z, L, q, h, h'⟩ := h₃ k
    exact ⟨Z, L, q, by have := h.divide n; simp only [Pi.zero_apply, zero_div] at this; exact this, h'⟩
  · have h0 : 0 ≤ curvMet ((M k).m σ) c y ξ := by
      by_cases hξ : ξ = 0
      · simpa [hξ] using ((continuous_and_smul (h₄ k σ).2 hy).2 0 0).ge
      · exact ((h₄ k σ).2.2 c y hy ξ hξ).le
    rw [inv_mul_eq_div]
    refine div_le_div_of_nonneg_left h0 (Nat.cast_pos.2 (PNat.pos _)) (Nat.cast_le.2 ?_)
    exact (Finset.le_sup (f := fun k => (((M k).divide n).n : ℕ)) (Finset.mem_univ k)).trans (Nat.le_succ _)

end
