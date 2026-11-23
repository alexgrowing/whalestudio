import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
open ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.ChernMass

theorem chernInt_eq_of_isCInf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L),
    φ.IsCInf → ψ.IsCInf →
      φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  intro Y L φ ψ hφ hψ
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth Y.str Y.dim (RingHom.id ℂ)
  have hA := R.isAlgAtlas_finAtlas
  set v : CxPts Y.str (RingHom.id ℂ) → ℝ :=
    fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2 with hv
  have hdiff : ∀ i y, y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (ψ.φ i y - φ.φ i y) / 2 = v y := by
    intro i y hy
    have hp := mem_pick φ.isLB y
    simp only [hv]
    rw [ψ.trans i _ y hy hp, φ.trans i _ y hy hp]
    ring
  have hvC : ∀ y, CInfAt v y := by
    intro y
    have hp := mem_pick φ.isLB y
    refine (((hψ _ y hp).add (hφ _ y hp).neg).const_mul (1 / 2)).congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hp] with z hz
    rw [← hdiff _ z hz]
    ring
  have hvs : (R.finAtlas).Smooth v :=
    (hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hvC y)
  have sφ := (Weight.isCInf_iff_isSmooth R).1 hφ
  have sψ := (Weight.isCInf_iff_isSmooth R).1 hψ
  have hQ : IsPotential R.finAtlas (φ.locPot + LocPot.ofFun v) :=
    isPotentialAdd _ _ _ (Weight.isPotential_locPot sφ) (isPotential_ofFun _ _ hvs)
  have hS : SameForm R.finAtlas ψ.locPot (φ.locPot + LocPot.ofFun v) :=
    ψ.sameForm_of_re (R := R) hA hQ fun x => by
      refine ⟨pick φ.isLB x, mem_pick φ.isLB x, _, isOpen_ptsIn _, mem_pick φ.isLB x, fun _ => 0,
        fun _ => differentiableOn_const (0 : ℂ), fun z hz => ?_⟩
      have := hdiff _ z hz
      show ψ.φ _ z / 2 = (φ.φ _ z / 2 + v z) + _
      rw [← this]
      simp
      ring
  rw [(Weight.chernInt_eq_mInt R hφ measurable_const).2
      (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y φ hφ),
    (Weight.chernInt_eq_mInt R hψ measurable_const).2
      (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y ψ hψ),
    SameForm.mInt_eq (fun _ => hS) _]
  exact (massIndep R.finAtlas (fun _ => φ.locPot) (fun _ => v)
    (fun _ => Weight.isPotential_locPot sφ) (fun _ => hvs)).symm

end GlobalTheory.CompanionTheory.ChernMass
