import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem pb_indep_cover : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k', ι' k') → Ω) (S' : AnSys D σ) (Re' : Realis S' (mCoordIdeal y)) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')), IsBlockMap κ v → imageZ v (mCoordIdeal y) = P → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsPullHerm κ v (Re.line a t) (Re'.line a t)) → Re'.deg = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * Re.deg → Re'.PB II = Re.PB II := by
  intro II hII K _ ι _ D σ _ S P Re K' _ ι' _ Ω _ _ y S' Re' κ v hbl hP hpull hdeg
  have hr0 : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 := by
    intro h
    have hd := Re'.deg_pos
    rw [hdeg, h, zero_mul] at hd
    exact lt_irrefl 0 hd
  have hr : ((IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hr0
  have harith : IsArithVar (imageZ v (mCoordIdeal y)) (D + 1) := by
    rw [hP]
    exact Re.arith
  have key : ∀ w : Fin (D + 1) → σ, Re'.limNum II w = Re.limNum II w := by
    intro w
    have ht0 : 0 < S.t₀ := (S.reg (w 0)).1
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ S.t₀ := by
      filter_upwards [Ioo_mem_nhdsGT ht0] with t ht using ht.2.le
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have heq : (fun t => Re'.num II t w) =ᶠ[𝓝[>] (0 : ℝ)] (fun t => Re.num II t w) := by
      filter_upwards [hpull, hle, hpos] with t hpt hle' hpos'
      have hPF := hII.2.2.1 K ι K' ι' κ v Ω y (D + 1) (fun j => Re.line (w j) t)
        (fun j => Re'.line (w j) t) hbl Re'.arith harith
        (fun j => Re.line_smooth (w j) t hpos' hle') (fun j => hpt (w j))
      rw [hP] at hPF
      show (II K' ι' (mCoordIdeal y) (D + 1) fun j => Re'.line (w j) t) / (Re'.deg : ℝ)
        = (II K ι P (D + 1) fun j => Re.line (w j) t) / (Re.deg : ℝ)
      rw [hPF, hdeg]
      push_cast
      exact mul_div_mul_left _ _ hr
    unfold Realis.limNum Filter.limUnder
    rw [Filter.map_congr heq]
  unfold Realis.PB
  rw [show Re'.limNum II = Re.limNum II from funext key]

end GlobalTheory.CompanionTheory.Ar.PB
