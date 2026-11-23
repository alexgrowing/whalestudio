import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MapSumMinor
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

namespace PositivityTheory.Xgp.W

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem exists_penFrame {τ : Ψ} {a b ca cb : Fin N} {k₀ : K} (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀) (hca : (ca : ℕ) = lastCol N j a)
    (hcb : (cb : ℕ) = ca + 1) {z : (Σ k, ι k) → L} (hz : IsPt y z) (c : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    Nonempty (PenFrame y k₀ (vecB M τ a k₀ ca cb) (cFac M τ a) (eDeg M τ a k₀) z c) := by
  obtain ⟨cb', hcb'⟩ := Classical.axiomOfChoice (isPt_base M hz).1
  obtain ⟨F, hF, hG⟩ := M.frames _ (RingHom.ker_isPrime _) (CoordinateConeArithVar.relevant _ cb' hcb')
    (isPt_base M hz).le
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk z)) := hG
  choose uv huv using fun q I => exists_hasVal_of_regAt (hG'.2.1 q I).1
  have hυ : ∀ i, ∃ v, M.blk (τ, i) = none → HasVal M.x (basePart M.blk z) (F.υ (τ, i)) v := fun i => by
    by_cases h : M.blk (τ, i) = none
    · exact (exists_hasVal_of_regAt (hG'.2.2 _ h).2.1).imp fun _ hv _ => hv
    · exact ⟨0, fun h' => absurd h' h⟩
  choose υv hυ using hυ
  obtain ⟨PF, -⟩ := core M ⟨M.j_le, hb, hab, hca, hcb⟩ hk hz c hc hF hG' uv huv υv hυ
  exact ⟨PF⟩

end PositivityTheory.Xgp.W
