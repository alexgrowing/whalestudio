import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLatticePairsIndexRpowLeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexStandardLatticeTransposeInvDvrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlIntegralInvMulOfLatticeMapEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeIndexSplitPlaceEqProductLocalStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.SplitHecke

noncomputable section

namespace GlobalTheory.SplitIndexSum
open GlobalTheory.AdelicLatMove (mt_mul mt_one)

abbrev stdLat (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

abbrev movLat (O K : Type) [CommRing O] [Field K] [Algebra O K] {r : ℕ} (h : GL (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)

theorem suppAt_mul {D : D7} {e : AE D} {V : HSp D} {g g' : GA D V} (hg : SuppAt e V g) (hg' : SuppAt e V g') :
    SuppAt e V (g * g') := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  have h' : (e + cA D e) • (mt V g' - 1) = mt V g' - 1 := Matrix.ext fun i j => hg' i j
  have h1 : mt V (g * g') - 1 = (mt V g - 1) * mt V g' + (mt V g' - 1) := by
    rw [mt_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  have h2 : (e + cA D e) • (mt V (g * g') - 1) = mt V (g * g') - 1 := by
    rw [h1, smul_add, ← Matrix.smul_mul, h, h']
  exact fun i j => congrFun (congrFun h2 i) j

theorem chart_of_finIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}
    (hv : IsFinIdem D v (e + cA D e)) (he : IsSplitIdem D e) : ∃ π : AE D →+* Fv D.host.F v, Chart e v π := by
  obtain ⟨v', π, hπ⟩ := GlobalTheory.T.exists_place_chart_of_splitIdempotent e he
  obtain ⟨ε, ⟨α, rfl, hα1, hα0⟩, hf⟩ := hv
  have hπe : π e = 1 := by
    have : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have hπc : π (cA D e) = 0 := (hπ.2.1 _).2 he.2.1
  have h1 : π (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 1 := by
    rw [← hf, map_add, hπe, hπc, add_zero]
  rw [hπ.2.2.1] at h1
  by_cases hvv : v' = v
  · subst hvv; exact ⟨π, hπ⟩
  · exfalso
    have h2 := hα0 v' hvv
    have h3 : sndA D.host.F (pairA D.host.F 0 α) = α := rfl
    rw [h3, h2] at h1
    exact zero_ne_one h1
theorem gInt_of_movLat_eq (O K : Type) [CommRing O] [Field K] [Algebra O K] {r : ℕ}
    (h h' : GL (Fin r) K) (hh : movLat O K h = movLat O K h') : GInt O (h⁻¹ * h') :=
  GlobalTheory.T.glIntegral_inv_mul_of_lattice_map_eq O K r h h' hh

theorem latIndex_eq_split : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v),
    IsSplitIdem D e → Chart e v π → ∀ (W : HSp D) (β : GL (Fin W.rank) (Fv D.host.F v)), Frame W e π β →
    ∀ g : GA D W, SuppAt e W g →
      latIndex W g = (movLat (Ov D v) (Fv D.host.F v) (rho W π β g)).toAddSubgroup.relIndex
          (stdLat (Ov D v) (Fv D.host.F v) W.rank).toAddSubgroup *
        (stdLat (Ov D v) (Fv D.host.F v) W.rank).toAddSubgroup.relIndex
          (movLat (Ov D v) (Fv D.host.F v) (rho W π β g)).toAddSubgroup := by
  intro D e v π he hπ W β hβ g hg
  haveI := Formalism.UG.P.glint_finite_residueField (F := D.host.F) v
  rw [GlobalTheory.T.lattice_index_split_place_eq_product_local e v π he hπ W β hβ g hg, map_inv, GlobalTheory.T.relIndex_standardLattice_transpose_inv_dvr]

theorem indexSum_split : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ (∏ i ∈ Finset.range W.rank, (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1 := by
  classical
  intro D W n hn v f hf ⟨e, he, hef⟩ C hC hdist
  subst hef
  obtain ⟨π, hπ⟩ := chart_of_finIdem hf he
  obtain ⟨β, hβ⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ W
  haveI := Formalism.UG.P.glint_finite_residueField (F := D.host.F) v
  set O := Ov D v
  set K := Fv D.host.F v
  set σ : ℝ := (n : ℝ) / 2 with hσ
  have hsupp : ∀ g ∈ C, SuppAt e W g := fun g hg => (hC g hg).1
  let Φ : GL (Fin W.rank) K → ℝ := fun h =>
    ((((movLat O K h).toAddSubgroup.relIndex (stdLat O K W.rank).toAddSubgroup : ℕ) : ℝ) *
      (((stdLat O K W.rank).toAddSubgroup.relIndex (movLat O K h).toAddSubgroup : ℕ) : ℝ)) ^ (-σ)
  have hK : ∀ g, SuppAt e W g → (g ∈ KsphC W ∅ ↔ GInt O (rho W π β g)) :=
    GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ W β hβ
  have hterm : ∀ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = Φ (rho W π β g) := by
    intro g hg
    rw [latIndex_eq_split e v π he hπ W β hβ g (hsupp g hg), Nat.cast_mul, neg_div]
  have hinj : ∀ g ∈ C, ∀ g' ∈ C, movLat O K (rho W π β g) = movLat O K (rho W π β g') → g = g' := by
    intro g hg g' hg' hm
    have h1 := gInt_of_movLat_eq O K _ _ hm
    rw [← map_inv, ← map_mul] at h1
    exact hdist g hg g' hg' ((hK _ (suppAt_mul (GlobalTheory.SplitHecke.Stab.suppAt_inv (hsupp g hg)) (hsupp g' hg'))).2 h1)
  have hone : ∀ g ∈ C, movLat O K (1 : GL (Fin W.rank) K) ≠ movLat O K (rho W π β g) := by
    intro g hg hm
    have h1 := gInt_of_movLat_eq O K _ _ hm
    rw [inv_one, one_mul] at h1
    exact (hC g hg).2 ((hK g (hsupp g hg)).2 h1)
  have hnot : (1 : GL (Fin W.rank) K) ∉ C.image (rho W π β) := by
    intro h1
    obtain ⟨g, hg, hg1⟩ := Finset.mem_image.1 h1
    exact hone g hg (by rw [hg1])
  have hsum : ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = ∑ h ∈ C.image (rho W π β), Φ h := by
    rw [Finset.sum_image (fun g hg g' hg' he' => hinj g hg g' hg' (congrArg (movLat O K) he'))]
    exact Finset.sum_congr rfl hterm
  have hΦ1 : Φ 1 = 1 := by
    have : movLat O K (1 : GL (Fin W.rank) K) = stdLat O K W.rank := by
      simp [movLat]
    simp only [Φ, this, AddSubgroup.relIndex_self, Nat.cast_one, mul_one, Real.one_rpow]
  have hσr : (W.rank : ℝ) - 1 < σ := by
    rw [hσ]; have : (2 * W.rank + 5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hbig := GlobalTheory.T.sum_lattice_pairs_index_rpow_le O K W.rank σ hσr (insert 1 (C.image (rho W π β))) (by
    intro h hh h' hh' hm
    rcases Finset.mem_insert.1 hh with rfl | hh <;> rcases Finset.mem_insert.1 hh' with rfl | hh'
    · rfl
    · obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hh'
      exact absurd hm (hone g' hg')
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hh
      exact absurd hm.symm (hone g hg)
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hh
      obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hh'
      rw [hinj g hg g' hg' hm])
  rw [Finset.sum_insert hnot] at hbig
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [Formalism.UG.P.tjcosets_card_residue]; rfl
  rw [hq] at hbig
  rw [hsum]
  change Φ 1 + ∑ h ∈ C.image (rho W π β), Φ h ≤ _ at hbig
  rw [hΦ1] at hbig
  rw [hσ] at hbig
  linarith

end GlobalTheory.SplitIndexSum

end
