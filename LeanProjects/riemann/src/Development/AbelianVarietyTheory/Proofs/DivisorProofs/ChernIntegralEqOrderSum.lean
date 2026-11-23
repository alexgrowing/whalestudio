import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSectionOrderFactorisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeromorphicSectionLocalOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOffOpenFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurve
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory

namespace ChernMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem sec_f_ne_zero [IsIntegral X] {L : LB X} {s : L.Sec} (hs : genericPoint X ∈ nonzeroLocus s)
    {i : L.ι} {x : X} (hx : x ∈ L.U i) : s.f i ≠ 0 := by
  intro h0
  have hgi : genericPoint X ∈ L.U i :=
    ((genericPoint_spec X).mem_open_set_iff (L.U i).isOpen).2 ⟨x, trivial, hx⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hs
  have hgj : genericPoint X ∈ L.U j := X.basicOpen_le _ hj
  have hu := (X.mem_basicOpen (s.f j) _ hgj).1 hj
  have hg : genericPoint X ∈ L.U j ⊓ L.U i := ⟨hgj, hgi⟩
  have e := s.compat j i
  rw [h0, map_zero, mul_zero] at e
  rw [← Cartier.germ_resG (inf_le_left : L.U j ⊓ L.U i ≤ L.U j) _ hg] at hu
  have e' : resG X (inf_le_left : L.U j ⊓ L.U i ≤ L.U j) (s.f j) = 0 := e
  rw [e', map_zero] at hu
  exact not_isUnit_zero hu

theorem exists_local_form [IsIntegral X] (hX : IsArithVar p 1) (R : AnRead p σ 1)
    [CompactSpace (CxPts p σ)] {L : LB X} (φ : Weight p σ L) (s : L.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (x : CxPts p σ) :
    ∃ ψ : OpenPartialHomeomorph (CxPts p σ) (Fin 1 → ℂ), IsCompatChart R.finAtlas ψ ∧ x ∈ ψ.source ∧
      ∃ u : (Fin 1 → ℂ) → ℂ, (∀ᶠ v in 𝓝 (ψ x), DifferentiableAt ℂ u v) ∧ u (ψ x) ≠ 0 ∧
        ∀ᶠ v in 𝓝 (ψ x), φ.locSec (secVal p σ s) x (ψ.symm v) =
          u v * (v 0 - ψ x 0) ^ secOrd φ.isLB s x.pt := by
  obtain ⟨a, ha⟩ := R.cover x
  set c := R.chart a
  have hW : x.pt ∈ L.U (pick φ.isLB x) := mem_ptsIn.1 (mem_pick φ.isLB x)
  obtain ⟨u, hu, hu0, he⟩ := GlobalTheory.T.local_section_order_factorisation k X p hX σ c _ (s.f (pick φ.isLB x))
    (sec_f_ne_zero hs hW) x ha hW
  have hc : Tendsto (FinChart.toV 1) (𝓝 (c.finChart x)) (𝓝 (c.e x)) :=
    (FinChart.toV 1).continuous.tendsto' _ _ (c.toV_finChart x)
  refine ⟨c.finChart, R.isCompatChart_finAtlas c, ha, u ∘ (EuclideanSpace.equiv (Fin 1) ℂ).symm,
    ?_, hu0, ?_⟩
  · filter_upwards [hc.eventually hu] with v hv
    exact DifferentiableAt.comp v hv (EuclideanSpace.equiv (Fin 1) ℂ).symm.differentiableAt
  · filter_upwards [hc.eventually he] with v hv
    rw [secOrd_eq φ.isLB s hW]
    exact hv

end ChernMass

open ChernMass in

theorem chernInt_curve_eq_finsum_secOrd : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X], IsArithVar p 1 → ∀ σ : k →+* ℂ, Nonempty (AnRead p σ 1) → ∀ (L : LB X)
    (φ : Weight p σ L), φ.IsCInf → ∀ s : L.Sec, genericPoint X ∈ nonzeroLocus s →
    φ.chernInt 1 Set.univ (fun _ => 1) = ∑ᶠ y : CxPts p σ, (secOrd φ.isLB s y.pt : ℝ) := by
  intro k _ X p _ hX σ ⟨R⟩ L φ hφ s hs
  have := hX.compactSpace σ
  have := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have hT : (ptsIn p σ (nonzeroLocus s))ᶜ.Finite :=
    GlobalTheory.SurfacePoints.finite_compl_ptsIn k X p hX _ hs σ
  set F := hT.toFinset with hF
  let P : Fin F.card → CxPts p σ := fun j => (F.equivFin.symm j).1
  have hP : Function.Injective P := fun a b h =>
    F.equivFin.symm.injective (Subtype.ext h)
  have hPr : ∀ y, y ∈ Set.range P ↔ y ∈ F := fun y =>
    ⟨fun ⟨j, e⟩ => e ▸ (F.equivFin.symm j).2,
      fun h => ⟨F.equivFin ⟨y, h⟩, by simp [P]⟩⟩
  let m : Fin F.card → ℕ := fun j => secOrd φ.isLB s (P j).pt
  have hsnc : IsSNC R.finAtlas φ.locPot (φ.locSec (secVal p σ s)) m (fun j => {P j}) := by
    refine GlobalTheory.T.meromorphic_section_local_order _ R.finAtlas φ.locPot _ _ m P hP fun x => ?_
    obtain ⟨ψ, hψ, hx, u, hu, hu0, he⟩ := exists_local_form hX R φ s hs x
    refine ⟨ψ, hψ, hx, secOrd φ.isLB s x.pt, u, hu, hu0, he, fun j e => by simp [m, e], fun h => ?_⟩
    refine secOrd_eq_zero φ.isLB (mem_ptsIn.1 ?_)
    by_contra h'
    exact h ((hPr x).2 (by simpa [hF] using h'))
  have hsm : φ.IsSmooth R := (Weight.isCInf_iff_isSmooth R).1 hφ
  have hpot : IsPotential R.finAtlas φ.locPot := Weight.isPotential_locPot hsm
  have hpl := plCurve R.finAtlas φ.locPot _ m P hP hpot
    (Weight.isSection_locSec φ (R.secVal_mem_holSec s)) hsnc (fun _ => 1)
    (fun _ => contDiffOn_const)
  have h0 : mInt R.finAtlas ![LocPot.ofFun fun _ => (1 : ℝ)]
      (logNormSec φ.locPot (φ.locSec (secVal p σ s))) = 0 :=
    mIntConstPot (e := 0) R.finAtlas 1 ![] _
  have hi : MIntegrable R.finAtlas (fun _ => φ.locPot) (fun _ => (1 : ℝ)) :=
    mIntegrableCont _ _ (fun _ => hpot) _ continuous_const
  have hc := Weight.chernInt_eq_mInt R hφ (g := fun _ => (1 : ℝ)) measurable_const
  have hfun : (![φ.locPot] : Fin 1 → LocPot (CxPts p σ)) = fun _ => φ.locPot := by
    funext i
    fin_cases i
    rfl
  rw [h0, hfun] at hpl
  rw [hc.2 (hc.1.2 hi)]
  have hsum : ∑ᶠ y : CxPts p σ, (secOrd φ.isLB s y.pt : ℝ) = ∑ k, (m k : ℝ) := by
    rw [finsum_eq_sum_of_support_subset (s := F)]
    · rw [← Finset.sum_coe_sort F]
      exact (Fintype.sum_equiv F.equivFin _ _ fun y => by simp [m, P]).trans rfl
    · intro y hy
      by_contra h'
      refine hy ?_
      have : y ∈ ptsIn p σ (nonzeroLocus s) := by
        by_contra h''
        exact h' (by simpa [hF] using h'')
      simp [secOrd_eq_zero φ.isLB (mem_ptsIn.1 this)]
  rw [hsum]
  simp only [mul_one] at hpl
  linarith

end GlobalTheory
