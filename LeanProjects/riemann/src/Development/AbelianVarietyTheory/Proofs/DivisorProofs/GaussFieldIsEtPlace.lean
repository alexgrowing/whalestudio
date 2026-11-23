import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsDivisionOfMOne

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def EtModel.ofRepFam {b : Base D R} {N : ℕ} (F : RepFam b N) (w0 : Ideal (𝓞 D.F)) : EtModel b N w0 0 where
  X := F.X
  s := F.s
  univ := F.univ
  lv := fun _ => 1
  isLev := isEtLev_zero _ _
  rep S s' o l hl := by
    obtain ⟨f, ⟨h1, ⟨m⟩⟩, hu⟩ := F.rep S s' o
    refine ⟨f, ⟨h1, m, fun y => ?_⟩, fun g hg => hu g ⟨hg.1, hg.2.elim fun m _ => ⟨m⟩⟩⟩
    have hy : l y = 1 := hl.2.2.1 y (by rw [wSub_zero]; trivial)
    have e1 : o.eta (N • (0 : D.La)) = 1 := o.eta_ker 0
    have e2 : F.univ.eta (N • (0 : D.La)) = 1 := F.univ.eta_ker 0
    have := m.eta (N • (0 : D.La))
    rw [e1, e2] at this
    rw [hy]; exact this

theorem isEtPlace_of_isUnit (b : Base D R) (hp : IsUnit (p : R)) (w0 : Ideal (𝓞 D.F)) (h : w0.IsMaximal)
    (hw : (p : 𝓞 D.F) ∈ w0) : IsEtPlace b w0 := by
  refine ⟨h, hw, fun i => ?_, fun k _ _ β φ _ => ?_⟩
  · refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, hw, by simp⟩) hp
  · exfalso
    have := hp.map β
    simp at this

def gaussFieldBase : Base gaussOneDatum gaussOneDatum.F where
  unit k hk := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
    exact (Nat.cast_ne_zero.2 hk0).isUnit
  ρ := algebraMap (𝓞 gaussOneDatum.F) gaussOneDatum.F gaussOneDatum.ω
  ρ_root := by
    have h : gaussOneDatum.ω ^ 2 - (gaussOneDatum.tr : 𝓞 gaussOneDatum.F) * gaussOneDatum.ω +
        (gaussOneDatum.nm : 𝓞 gaussOneDatum.F) = 0 := by
      rw [← gaussOneDatum.tr_eq, ← gaussOneDatum.nm_eq]; ring
    have h' := congrArg (algebraMap (𝓞 gaussOneDatum.F) gaussOneDatum.F) h
    simpa only [map_sub, map_add, map_mul, map_pow, map_intCast, map_zero] using h'
  t _ := algebraMap (𝓞 gaussOneDatum.F) gaussOneDatum.F
  t_ω _ := rfl
  comax i j h := (h (Fin.ext (by have hi := i.isLt; have hj := j.isLt; change _ < 1 at hi hj; omega))).elim
  apart i j h := (h (Fin.ext (by have hi := i.isLt; have hj := j.isLt; change _ < 1 at hi hj; omega))).elim

end GlobalTheory.UPel.HT.EtLev
