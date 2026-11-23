import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith

noncomputable section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.LineFlat

def two : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory (Fin 2)) where
  a := 0
  h _ := 2
  pos _ _ := two_pos
  smul _ _ _ := by simp

def root (r : Unit × Fin 2) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory (Fin 2)) :=
  if r.2 = 0 then ProjLine.fsLine1.inv else ProjLine.fsLine1.tensor two

theorem sm1 : IsSmoothHerm ProjLine.fsLine1 := by
  intro z hz
  have hz0 : (WithLp.toLp 2 z : EuclideanSpace ℂ (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Ix (Fin 2))) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz ()
    intro h0
    apply hi
    have h1 := congrArg (fun w : EuclideanSpace ℂ (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Ix (Fin 2)) => w ⟨(), i⟩) h0
    simpa using h1
  have hL := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Ix (Fin 2) => ℂ)).symm.contDiff
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
  exact ((contDiffAt_norm ℂ hz0).comp z hL.contDiffAt).contDiffWithinAt

theorem cj1 : IsConjInvariantH ProjLine.fsLine1 := by
  intro z
  show ‖WithLp.toLp 2 (fun p => (starRingEnd ℂ) (z p))‖ = ‖WithLp.toLp 2 z‖
  simp [EuclideanSpace.norm_eq]

theorem sm2 : IsSmoothHerm two := by
  show ContDiffOn ℝ _ (fun _ => (2 : ℝ)) _
  exact contDiffOn_const

def model : RootModel Unit 2 where
  K := Unit
  ι := GlobalTheory (Fin 2)
  Ω := ProjLine.FnField
  y := ProjLine.y
  arith := ProjLine.isArithVar_y'
  birational := ProjLine.birational_y
  xdeg r := (root r).a
  x _ r := root r
  x_deg _ _ := rfl
  x_smooth _ r := by
    unfold root; split_ifs
    · exact isSmoothHerm_inv sm1
    · exact isSmoothHerm_tensor sm1 sm2
  x_conj _ r := by
    unfold root; split_ifs
    · intro z; simp only [HermLine.inv]; rw [cj1 z]
    · intro z; simp only [HermLine.tensor, two]; rw [cj1 z]
  kA := 1
  kA_pos := one_pos
  A := ProjLine.fsLine1
  A_smooth := sm1
  A_conj := cj1
  δ := 1
  δ_pos := one_pos

theorem ptsInt_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegral P φ (fun _ => 0) = 0 := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegral, ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegralAt, ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity]

theorem one_not : (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing (GlobalTheory (Fin 2))) ∉ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal ProjLine.y := by
  intro h
  rw [ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, map_one] at h
  exact one_ne_zero h

theorem hom1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing (GlobalTheory (Fin 2))) 0 := by
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

def phi : ℚ →+* ProjLine.FnField := algebraMap ℚ _

def S : FlatHerm ProjLine.y phi two where
  M := 1
  M_pos := one_pos
  f := 1
  g := 1
  df := 0
  dg := 0
  hf := hom1
  hg := hom1
  deg := by intro k; simp [two]
  f_ne := one_not
  g_ne := one_not
  unit := fun W hW _ _ => ⟨1, 1, fun h => hW.ne_top ((Ideal.eq_top_iff_one _).2 h), fun h => hW.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  κ _ := 1/2
  κ_pos _ := by norm_num
  κ_conj _ := rfl
  norm σ z _ := by simp [evC, two]

theorem ovi : OverInt ProjLine.y phi := by
  refine ⟨fun k => ⟨(0 : Fin 2), ?_⟩, fun c _ a => ?_⟩
  · simp [ProjLine.y]
  · have ha : IsIntegral ℤ (a : ℚ) := a.2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 ha
    have e : phi (a : ℚ) = algebraMap ℤ ProjLine.FnField n := by
      rw [← hn]
      simp [phi]
    rw [e]
    exact Subalgebra.algebraMap_mem _ n

theorem dg : ∑ i : Fin 2, (root ((), i)).a = two.a := by
  funext k
  simp [root, two, Fin.sum_univ_two, HermLine.inv, HermLine.tensor, ProjLine.fsLine1, HermLine.ofCone]

def R : RootFlat model () where
  F := ℚ
  φ := phi
  overInt := ovi
  A := two
  A_smooth := sm2
  S := S
  deg := dg
  v _ _ := 0
  v_inv _ _ _ _ := rfl
  v_smooth _ := contDiffOn_const
  prod t _ z hz := by
    have := ProjLine.fsLine1.pos z hz.1
    simp only [model, root, two, Fin.prod_univ_two, HermLine.inv, HermLine.tensor]
    simp
    field_simp
  small m _ := by
    simp only [ptsInt_zero]
    exact tendsto_const_nhds

end GlobalTheory.CompanionTheory.Ar.Flat.LineFlat
