import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num.PullModel

noncomputable section

open ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem smooth_trivLine : IsSmoothHerm (trivLine ι) := contDiffOn_const

theorem pull_trivLine (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    IsPullHerm κ v (trivLine ι) (trivLine ι') := by
  refine ⟨?_, fun _ => rfl⟩
  funext k
  simp [trivLine, pullDeg]
  classical
  rw [Function.extend_def]
  split_ifs <;> rfl

theorem pull_oneLine (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    IsPullHerm κ v (ReciprocityTheory.ChartRestriction.G.Geo.oneLine : HermLine ι) (ReciprocityTheory.ChartRestriction.G.Geo.oneLine : HermLine ι') := by
  refine ⟨?_, fun _ => rfl⟩
  funext k
  simp [ReciprocityTheory.ChartRestriction.G.Geo.oneLine, HermLine.ofWeight, pullDeg]
  classical
  rw [Function.extend_def]
  split_ifs <;> rfl

theorem smooth_monoLines {J : Type} {ℓ : J → HermLine ι} (h : ∀ j, IsSmoothHerm (ℓ j)) (m : J →₀ ℕ) (d : ℕ)
    (k : Fin d) : IsSmoothHerm (monoLines ℓ m d k) := by
  unfold monoLines
  split_ifs
  · exact h _
  · exact smooth_trivLine

theorem pull_monoLines {J : Type} {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {ℓ : J → HermLine ι}
    {ℓ' : J → HermLine ι'} (h : ∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) (m : J →₀ ℕ) (d : ℕ) (k : Fin d) :
    IsPullHerm κ v (monoLines ℓ m d k) (monoLines ℓ' m d k) := by
  unfold monoLines
  split_ifs
  · exact h _
  · exact pull_trivLine κ v

theorem snoc_oneLine {I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {n : ℕ} (L : Fin n → HermLine ι)
    (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine) =
      -ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  have h1 : (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∉ P :=
    fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  rw [hI.2.2 P n L ReciprocityTheory.ChartRestriction.G.Geo.oneLine 1 (fun _ => 0) hP hL ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_oneLine
    (fun k => by simp [ReciprocityTheory.ChartRestriction.G.Geo.oneLine, HermLine.ofWeight])
    ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one h1]
  have hint : arInt P 1 ReciprocityTheory.ChartRestriction.G.Geo.oneLine L =
      ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    unfold arInt
    congr 1
    funext z
    exact ReciprocityTheory.ChartRestriction.G.Geo.logNorm_oneLine z
  unfold recR
  rw [ReciprocityTheory.ChartRestriction.G.Geo.divSupp_one, finsum_mem_empty, hint]
  ring

end Lines

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem smooth_line (M : RootModel Ψ N) (t : ℝ) (r : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t r) := by
  cases r with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

section Cover

variable {M M' : RootModel Ψ N} [CharZero M'.Ω] {II : IntersectionSystem}
  {κ : M.K → M'.K} {v : (Σ k, M.ι k) → (Σ k, M'.ι k)}

abbrev coverDeg (M M' : RootModel Ψ N) [CharZero M'.Ω] (v : (Σ k, M.ι k) → (Σ k, M'.ι k)) : ℕ :=
  IntermediateField.relfinrank (blockFnField (M'.y ∘ v)) (blockFnField M'.y)

theorem coverDeg_ne_zero (hδ : M'.δ = coverDeg M M' v * M.δ) : coverDeg M M' v ≠ 0 := by
  intro h
  have := M'.δ_pos
  rw [hδ, h, zero_mul] at this
  exact lt_irrefl _ this

theorem arMono_eq (hII : ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II) (hb : IsBlockMap κ v)
    (hP : imageZ v M'.P = M.P) (hl : ∀ t r, IsPullHerm κ v (M.line t r) (M'.line t r))
    (hk : M'.kA = M.kA) (hδ : M'.δ = coverDeg M M' v * M.δ) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M'.arMono II t m = M.arMono II t m := by
  have hP' : imageZ v (mCoordIdeal M'.y) = M.P := hP
  have he : (coverDeg M M' v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (coverDeg_ne_zero hδ)
  have hδ0 : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.δ_pos.ne'
  have hk0 : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.kA_pos.ne'
  have hpf := hII.2.2.1 M.K M.ι M'.K M'.ι κ v M'.Ω M'.y (dimFl Ψ N + 1)
    (monoLines (M.line t) m (dimFl Ψ N + 1)) (monoLines (M'.line t) m (dimFl Ψ N + 1)) hb M'.arith
    (by rw [hP']; exact M.arith) (smooth_monoLines (smooth_line M t) m _) (pull_monoLines (hl t) m _)
  rw [hP'] at hpf
  unfold RootModel.arMono
  split_ifs
  · change ReciprocityTheory.ChartRestriction.G.Geo.IntersectionSystem at II
    have hpf' : II M'.K M'.ι M'.P (dimFl Ψ N + 1) (monoLines (M'.line t) m (dimFl Ψ N + 1)) = _ := hpf
    rw [hpf', hk, hδ]
    push_cast
    field_simp
  · rfl

theorem geoMono_eq (hII : ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II) (hb : IsBlockMap κ v)
    (hP : imageZ v M'.P = M.P) (hl : ∀ t r, IsPullHerm κ v (M.line t r) (M'.line t r))
    (hk : M'.kA = M.kA) (hδ : M'.δ = coverDeg M M' v * M.δ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M'.geoMono m = M.geoMono m := by
  have hP' : imageZ v (mCoordIdeal M'.y) = M.P := hP
  have he : (coverDeg M M' v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (coverDeg_ne_zero hδ)
  have hδ0 : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.δ_pos.ne'
  have hk0 : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.kA_pos.ne'
  unfold RootModel.geoMono
  split_ifs
  · set L := monoLines (M.line 1) m (dimFl Ψ N) with hLdef
    set L' := monoLines (M'.line 1) m (dimFl Ψ N) with hL'def
    have hLs : ∀ j, IsSmoothHerm (L j) := smooth_monoLines (smooth_line M 1) m _
    have hL's : ∀ j, IsSmoothHerm (L' j) := smooth_monoLines (smooth_line M' 1) m _
    have hLp : ∀ j, IsPullHerm κ v (L j) (L' j) := pull_monoLines (hl 1) m _
    have hpf := hII.2.2.1 M.K M.ι M'.K M'.ι κ v M'.Ω M'.y (dimFl Ψ N + 1)
      (Fin.snoc (α := fun _ => HermLine M.ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine)
      (Fin.snoc (α := fun _ => HermLine M'.ι) L' ReciprocityTheory.ChartRestriction.G.Geo.oneLine) hb M'.arith
      (by rw [hP']; exact M.arith)
      (fun j => by
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_oneLine
        · simpa using hLs i)
      (fun j => by
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using pull_oneLine κ v
        · simpa using hLp i)
    rw [hP'] at hpf
    have e1 := snoc_oneLine (hII.1 M'.K M'.ι) L' M'.arith hL's
    have e2 : II M.K M.ι M.P (dimFl Ψ N + 1)
        (Fin.snoc (α := fun _ => HermLine M.ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine) =
        -ptsIntegral M.P (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
      snoc_oneLine (hII.1 M.K M.ι) L M.arith hLs
    have hpf' := hpf
    rw [e1, e2] at hpf'
    have hpts : ptsIntegral (mCoordIdeal M'.y) (fun j z => Real.log ((L' j).h z)) (fun _ => 1) =
        (coverDeg M M' v : ℝ) * ptsIntegral M.P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
      linarith
    change ptsIntegral (mCoordIdeal M'.y) (fun j z => Real.log ((L' j).h z)) (fun _ => 1) / _ = _
    rw [hpts, hk, hδ]
    push_cast
    field_simp
  · rfl

end Cover

end

theorem numbers_of_cover : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M M' : RootModel Ψ N) [CharZero M'.Ω] (II : IntersectionSystem), ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → ∀ (κ : M.K → M'.K) (v : (Σ k, M.ι k) → (Σ k, M'.ι k)), ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v → ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ v M'.P = M.P → (∀ t r, ReciprocityTheory.ChartRestriction.G.AI.I4.IsPullHerm κ v (M.line t r) (M'.line t r)) → M'.kA = M.kA → M'.δ = IntermediateField.relfinrank (ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (M'.y ∘ v)) (ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField M'.y) * M.δ → (∀ t, M'.arFun II t = M.arFun II t) ∧ M'.PP II = M.PP II ∧ (M.Converges II → M'.Converges II) ∧ M'.geoFun = M.geoFun := by
  intro Ψ _ _ N M M' _ II hII κ v hb hP hl hk hδ
  have hm : ∀ t, M'.arMono II t = M.arMono II t := fun t => funext fun m =>
    arMono_eq hII hb hP hl hk hδ t m
  have hg : M'.geoMono = M.geoMono := funext fun m => geoMono_eq hII hb hP hl hk hδ m
  refine ⟨fun t => ?_, ?_, fun hc m => ?_, ?_⟩
  · unfold RootModel.arFun
    rw [hm t]
  · unfold RootModel.PP
    congr 2
    funext m
    congr 1
    funext t
    exact congrFun (hm t) m
  · obtain ⟨L, hL⟩ := hc m
    exact ⟨L, by simpa only [hm] using hL⟩
  · unfold RootModel.geoFun
    rw [hg]

end GlobalTheory.CompanionTheory.Ar.Num.PullModel
