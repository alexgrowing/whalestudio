import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodinger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.CharSumHalf

open GlobalTheory.Core.Rk.ThetaOf GlobalTheory.DownLift.GenQuot

set_option synthInstance.maxHeartbeats 100000 in

theorem charSum_detects_multiple : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ) (R : Finset (WO S T)), 0 < k → (∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1) → (∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ) → (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ Λ) → (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ Λ → ∃! r, r ∈ R ∧ y - r ∈ Λ) → ∀ t ∈ Λ, IsHalf e t → ((∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = R.card) ∧ ((¬ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = 0) := by
  intro D ψ S T Λ e k R hk hpair hann hR hU t htΛ hte
  classical
  have half_sub : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x - y) :=
    fun hx hy i j => by simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]
  have half_add : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x + y) :=
    fun hx hy i j => by simp only [Matrix.add_apply, mul_add, hx i j, hy i j]
  have half_nsmul : ∀ {c : AE D} {x : WO S T} (n : ℕ), IsHalf c x → IsHalf c (n • x) :=
    fun n hx i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  have half_smul : ∀ {c : AE D} {x : WO S T} (a : AE D), IsHalf c x → IsHalf c (a • x) :=
    fun a hx i j => by simp only [Matrix.smul_apply, smul_eq_mul]; rw [mul_left_comm, hx i j]
  have pair_add : ∀ x y y' : WO S T,
      ψ (symplO S T x (y + y')) = ψ (symplO S T x y) * ψ (symplO S T x y') := by
    intro x y y'; rw [symplO_add_right, AddChar.map_add_eq_mul]
  constructor
  · rintro ⟨u, huΛ, hue, rfl⟩
    have h1 : ∀ r ∈ R, ψ (symplO S T (k • u) r) = 1 := fun r hr => by
      rw [symplO_nsmul_swap]
      exact hpair u huΛ hue _ (hR r hr).2 (half_nsmul k (hR r hr).1)
    rw [Finset.sum_congr rfl h1]; simp
  · intro hnot
    have hex : ∃ r₀ ∈ R, ψ (symplO S T t r₀) ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hnot
      set a : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹) with ha
      have hka : k • a = 1 := by
        rw [ha, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), map_one]
      have hkx : ∀ x : WO S T, k • (a • x) = x := fun x => by
        rw [← smul_assoc, hka, one_smul]
      refine ⟨a • t, ?_, half_smul a hte, (hkx t).symm⟩
      apply hann _ (half_smul a hte)
      intro y hyΛ hyc
      obtain ⟨r, ⟨hrR, hdiff⟩, -⟩ := hU (a • y) (half_smul a hyc) (by rw [hkx]; exact hyΛ)
      have hsw : symplO S T (a • t) y = symplO S T t (a • y) := by
        conv_lhs => rw [← hkx y]
        rw [← symplO_nsmul_swap, hkx]
      rw [hsw, show a • y = (a • y - r) + r by abel, pair_add, hall r hrR, mul_one]
      exact hpair t htΛ hte _ hdiff (half_sub (half_smul a hyc) (hR r hrR).1)
    obtain ⟨r₀, hr₀R, hr₀⟩ := hex
    obtain ⟨rep, rep_spec⟩ : ∃ rep : WO S T → WO S T,
        ∀ y, IsHalf (cA D e) y → k • y ∈ Λ → rep y ∈ R ∧ y - rep y ∈ Λ := by
      refine ⟨fun y => if h : IsHalf (cA D e) y ∧ k • y ∈ Λ then (hU y h.1 h.2).exists.choose else 0, ?_⟩
      intro y h1 h2
      dsimp only
      rw [dif_pos (And.intro h1 h2)]
      exact (hU y h1 h2).exists.choose_spec
    have rep_eq : ∀ y r, IsHalf (cA D e) y → k • y ∈ Λ → r ∈ R → y - r ∈ Λ → rep y = r :=
      fun y r h1 h2 hr hd => (hU y h1 h2).unique (rep_spec y h1 h2) ⟨hr, hd⟩
    have hadd : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r + s) ∧ k • (r + s) ∈ Λ := fun r hr s hs =>
      ⟨half_add (hR r hr).1 (hR s hs).1, by rw [nsmul_add]; exact Λ.add_mem (hR r hr).2 (hR s hs).2⟩
    have hsub : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r - s) ∧ k • (r - s) ∈ Λ := fun r hr s hs =>
      ⟨half_sub (hR r hr).1 (hR s hs).1, by rw [nsmul_sub]; exact Λ.sub_mem (hR r hr).2 (hR s hs).2⟩
    have key : ∑ r ∈ R, ψ (symplO S T t r₀) * ψ (symplO S T t r) = ∑ r ∈ R, ψ (symplO S T t r) := by
      apply Finset.sum_nbij' (fun r => rep (r + r₀)) (fun r => rep (r - r₀))
      · intro r hr; exact (rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2).1
      · intro r hr; exact (rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2).1
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hs := hsub _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r + r₀) - r₀ - r = -((r + r₀) - rep (r + r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2
        have hs := hadd _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r - r₀) + r₀ - r = -((r - r₀) - rep (r - r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hrep : rep (r + r₀) = (r + r₀) + -((r + r₀) - rep (r + r₀)) := by abel
        have hhalf : IsHalf (cA D e) (-((r + r₀) - rep (r + r₀))) := by
          have := half_sub (hadd r hr r₀ hr₀R).1 (hR _ h1).1
          intro i j; simp only [Matrix.neg_apply, mul_neg, this i j]
        show _ = ψ (symplO S T t (rep (r + r₀)))
        rw [hrep, pair_add, pair_add, hpair t htΛ hte _ (Λ.neg_mem h2) hhalf, mul_one, mul_comm]
    rw [← Finset.mul_sum] at key
    have h0 : (ψ (symplO S T t r₀) - 1) * ∑ r ∈ R, ψ (symplO S T t r) = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hr₀)

end GlobalTheory.CharSumHalf
