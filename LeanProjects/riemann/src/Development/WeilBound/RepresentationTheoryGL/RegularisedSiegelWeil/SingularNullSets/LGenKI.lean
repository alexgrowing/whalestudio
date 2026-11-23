import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKH

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {D : D7} {n : ℕ}

theorem factor {S : Finset (Pl D)} (hS2 : ∀ v ∉ S, (2 : 𝓞 D.host.F) ∉ v.asIdeal) {k : G D n} (hk : k ∈ KOff D n S) :
    ∃ g1 g2 g3 g4 : G D n, k = g1 * (g2 * (g3 * g4)) ∧ g1 ∈ KOff D n S ∧ IsN g1 ∧ g2 ∈ KOff D n S ∧ IsM g2 ∧
      g3 ∈ KOff D n S ∧ (∃ w u, IsW w ∧ IsN u ∧ u ∈ KOff D n S ∧ g3 = w * u * w⁻¹) ∧ g4 ∈ KOff D n S ∧ IsN g4 := by
  obtain ⟨hinf, hSv, hint⟩ := KOff_props hk
  obtain ⟨X, hXh, hXinf, hXS, hXint, hz, hu⟩ := exists_X hS2 hk
  obtain ⟨a, ha⟩ : ∃ a, a = bA (mat k) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = bB (mat k) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = bC (mat k) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = bD (mat k) := ⟨_, rfl⟩
  have hMb : mat k = blk4 a b c d := by rw [ha, hb, hc, hd, block_matrix_of_blocks]
  obtain ⟨ia, ib, ic, id⟩ := blocks_at (infPart D) hinf
  simp only [← ha, ← hb, ← hc, ← hd] at ia ib ic id hz hu
  obtain ⟨u, hudef⟩ : ∃ u, u = d + c * X := ⟨_, rfl⟩
  simp only [← hudef] at hz hu
  obtain ⟨ui, hui⟩ : ∃ ui, ui = u⁻¹ := ⟨_, rfl⟩
  have hu1 : u * ui = 1 := by rw [hui]; exact Matrix.mul_nonsing_inv _ hu
  have hu2 : ui * u = 1 := by rw [hui]; exact Matrix.nonsing_inv_mul _ hu
  obtain ⟨β, hβ⟩ : ∃ β, β = a * X + b := ⟨_, rfl⟩
  have hh : mat (k * nOf X hXh) = blk4 a β c u := by rw [mat_mul, mat_nOf, hMb, block_matrix_mul_upper_unipotent, hβ, hudef]
  have hunit := unit_fromBlocks (cA D) a β c u (by rw [← hh]; exact mat_unit _)
  obtain ⟨-, R2, -⟩ := unit_rel _ a β c u hunit
  obtain ⟨-, -, C3⟩ := unit_col _ a β c u hunit
  obtain ⟨hXnh, hZnh, hid⟩ := fact_alg (cA D) a β c u ui hu1 hu2 R2 C3
  have hZn' : cj (cA D) (-(ui * c)) = -(ui * c) := by rw [cj_neg, hZnh]
  have hXh' : cj (cA D) (-X) = -X := by rw [cj_neg, hXh]

  have hIa : ∀ v ∉ S, IntM v a ∧ IntM v b ∧ IntM v c ∧ IntM v d := fun v hv =>
    integral_block_matrix_iff.1 (by rw [← hMb]; exact hint v hv)
  have hIX : ∀ v ∉ S, IntM v X := fun v hv => hXint v hv
  have hIu : ∀ v ∉ S, IntM v ui := by
    intro v hv
    rw [hui]
    refine IntM.inv ?_ hu (hz v)
    rw [hudef]; exact (hIa v hv).2.2.2.add ((hIa v hv).2.2.1.mul (hIX v hv))
  have hIXn : ∀ v ∉ S, IntM v (β * ui) := fun v hv => by
    rw [hβ]; exact (((hIa v hv).1.mul (hIX v hv)).add (hIa v hv).2.1).mul (hIu v hv)
  have hIZn : ∀ v ∉ S, IntM v (-(ui * c)) := fun v hv => ((hIu v hv).mul (hIa v hv).2.2.1).neg

  have hXn0 : ∀ (T : Type) [CommRing T] (f : AE D →+* T), a.map f = 1 → b.map f = 0 → X.map f = 0 →
      (β * ui).map f = 0 := by
    intro T _ f h1 h2 h3
    rw [Matrix.map_mul, hβ, map_add', Matrix.map_mul, h2, h3]; simp
  have hZn0 : ∀ (T : Type) [CommRing T] (f : AE D →+* T), c.map f = 0 → (-(ui * c)).map f = 0 := by
    intro T _ f h1
    rw [map_neg', Matrix.map_mul, h1]; simp
  have hS' : ∀ v ∈ S, a.map (cv D v) = 1 ∧ b.map (cv D v) = 0 ∧ c.map (cv D v) = 0 ∧ d.map (cv D v) = 1 := by
    intro v hv
    have := blocks_at (cv D v) (hSv v hv)
    simp only [← ha, ← hb, ← hc, ← hd] at this
    exact this

  have m4 : nOf (-X) hXh' ∈ KOff D n S :=
    nOf_mem _ _ (by rw [map_neg', hXinf, neg_zero]) (fun v hv => by rw [map_neg', hXS v hv, neg_zero])
      (fun v hv => (hIX v hv).neg)
  have mX : nOf X hXh ∈ KOff D n S := nOf_mem _ _ hXinf hXS hIX
  have m1 : nOf (β * ui) hXnh ∈ KOff D n S :=
    nOf_mem _ _ (hXn0 _ _ ia ib hXinf) (fun v hv => hXn0 _ _ (hS' v hv).1 (hS' v hv).2.1 (hXS v hv)) hIXn
  have mu3 : nOf (-(ui * c)) hZn' ∈ KOff D n S :=
    nOf_mem _ _ (hZn0 _ _ ic) (fun v hv => hZn0 _ _ (hS' v hv).2.2.1) hIZn
  have m3 : wE D n * nOf (-(ui * c)) hZn' * (wE D n)⁻¹ ∈ KOff D n S :=
    conj_mem _ _ (hZn0 _ _ ic) (fun v hv => hZn0 _ _ (hS' v hv).2.2.1) hIZn
  have hmg3 : mat (wE D n * nOf (-(ui * c)) hZn' * (wE D n)⁻¹) = blk4 1 0 (ui * c) 1 := by
    rw [mat_conj, neg_neg]
  have hmg1i : mat (nOf (β * ui) hXnh)⁻¹ = blk4 1 (-(β * ui)) 0 1 := mat_inv_eq (by rw [mat_nOf, upper_unipotent_block_inverse])
  have hmg3i : mat (wE D n * nOf (-(ui * c)) hZn' * (wE D n)⁻¹)⁻¹ = blk4 1 0 (-(ui * c)) 1 :=
    mat_inv_eq (by rw [hmg3, lower_unipotent_block_inverse])
  have hX4 : nOf X hXh * nOf (-X) hXh' = 1 := by
    apply mat_inj
    rw [mat_mul, mat_nOf, mat_nOf, upper_unipotent_block_inverse, mat_one]
  set g1 := nOf (β * ui) hXnh with hg1
  set g3 := wE D n * nOf (-(ui * c)) hZn' * (wE D n)⁻¹ with hg3
  have hmg2 : mat (g1⁻¹ * k * nOf X hXh * g3⁻¹) = blk4 (a - β * ui * c) 0 0 u := by
    rw [mat_mul, mat_mul, mat_mul, hmg1i, hmg3i, Matrix.mul_assoc (blk4 1 (-(β * ui)) 0 1), ← mat_mul, hh, ← hid]
    calc blk4 1 (-(β * ui)) 0 1 * (blk4 1 (β * ui) 0 1 * blk4 (a - β * ui * c) 0 0 u * blk4 1 0 (ui * c) 1) *
          blk4 1 0 (-(ui * c)) 1
        = (blk4 1 (-(β * ui)) 0 1 * blk4 1 (β * ui) 0 1) * blk4 (a - β * ui * c) 0 0 u *
            (blk4 1 0 (ui * c) 1 * blk4 1 0 (-(ui * c)) 1) := by simp only [Matrix.mul_assoc]
      _ = blk4 (a - β * ui * c) 0 0 u := by
          rw [lower_unipotent_block_inverse, Matrix.mul_one]
          have := upper_unipotent_block_inverse (-(β * ui)); rw [neg_neg] at this; rw [this, Matrix.one_mul]
  refine ⟨g1, g1⁻¹ * k * nOf X hXh * g3⁻¹, g3, nOf (-X) hXh', ?_, m1, isN_nOf _ _, ?_, isM_of _ _ _ hmg2, m3,
    ⟨wE D n, _, isW_wE, isN_nOf _ _, mu3, rfl⟩, m4, isN_nOf _ _⟩
  · simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, hX4, mul_one]
  · exact mul_mem (mul_mem (mul_mem (inv_mem m1) hk) mX) (inv_mem m3)

end PositivityTheory.Rg.Rsw.L.LGenK
