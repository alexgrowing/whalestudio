import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StarDetMulDetMem
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem valuation_le_one_of_mem {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : FractionalIdeal.count D.host.E P D.host.AA = 0) {a : D.host.E} (ha : a ∈ D.host.AA) :
    P.valuation D.host.E a ≤ 1 := by
  by_cases h0 : a = 0
  · simp [h0]
  have h1 := FractionalIdeal.count_mono D.host.E P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr h0)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr ha)
  rw [hP, ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton D.host.E P h0] at h1
  have hv : P.valuation D.host.E a ≠ 0 := by simpa using h0
  have h2 : WithZero.log (P.valuation D.host.E a) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.log_one]; linarith
  exact (WithZero.log_le_log hv one_ne_zero).1 h2

theorem toEAf_mul_mem {Q : HeightOneSpectrum (𝓞 D.host.E)} {f : AE D} (hf : GlobalTheory.IdemSupport.Comparison₂ Q f)
    (hQ : FractionalIdeal.count D.host.E Q D.host.AA = 0) {a : D.host.E} (ha : a ∈ D.host.AA) :
    toEAf D (f * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨t, ht, H⟩ := GlobalTheory.DetSelfDual.exists_denom Q {a} (by simpa using valuation_le_one_of_mem hQ ha)
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 (H a (Finset.mem_singleton_self a))
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Q.asIdeal.zero_mem)
  have ht0' : (t : D.host.E) ≠ 0 := by simpa using ht0
  have h1 : finPart D (f * incA D ((t : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h; exact ht ((hf t ht0).2 h)
  have h2 := mul_mem (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1) (GlobalTheory.IdemIntegral.eToEAf_int D o)
  have e : a = (t : D.host.E)⁻¹ * (o : D.host.E) := by
    have : (o : D.host.E) = (t : D.host.E) * a := by
      rw [show ((o : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E o from rfl, ho, Algebra.smul_def]
    rw [this, inv_mul_cancel_left₀ ht0']
  rw [e, map_mul (incA D), ← mul_assoc, map_mul (toEAf D)]
  exact h2

theorem toEAf_cA_idem_mul_mem {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q)
    {a : D.host.E} (ha : a ∈ D.host.AA) :
    toEAf D (cA D (idem Pg) * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, h1, -, hsp⟩ := hP.split
  have hS : GlobalTheory.ExportSeries.SplitSet Pg := hsp.mono h1
  rw [GlobalTheory.ExportSeries.idem, map_sum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  have ht : GlobalTheory.IdemSupport.Comparison₂ PP (GlobalTheory.ExportSeries.idemAt PP) := (hS.isIdemAt hPP).2
  refine toEAf_mul_mem ht.conj ?_ ha
  exact hP.prime PP (Or.inl hPP) _ (Or.inr ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl))

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem isIntM_mul {m n k : ℕ} {A : Matrix (Fin m) (Fin n) (EAf D)} {B : Matrix (Fin n) (Fin k) (EAf D)}
    (hA : IsIntM A) (hB : IsIntM B) : IsIntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem isIntM_smul {m n : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {A : Matrix (Fin m) (Fin n) (EAf D)} (hA : IsIntM A) : IsIntM (c • A) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hA i j)

theorem frame_col_int {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : Fin n → D.host.E} (hv : v ∈ Λ) :
    IsIntM ((β⁻¹).val * Matrix.of fun i (_ : Fin 1) => eToEAf D (v i)) := fun i _ =>
  (hβ _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL Λ 1 (one_mem _) v hv) i

theorem pair_row_int {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ)
    {β : GL (Fin V.rank) (EAf D)} (hβ : Formalism.L2.DIV.IsFrame β Λ) {s : Fin V.rank → D.host.E} (hs : s ∈ Λ) :
    IsIntM ((Matrix.of fun (_ : Fin 1) l => eToEAf D (∑ k, star (s k) * V.gram k l)) * β.val) := fun _ j => by
  have hcol : (fun k => β.val k j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (hβ _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k j) i = ((β⁻¹).val * β.val) i j := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine GlobalTheory.PairIntegral.sum_mem_intAf Λ (fun l => ∑ k, star (s k) * V.gram k l) (fun y hy => ?_) _ hcol
  obtain ⟨b, hb⟩ := (hΛ.2 y).1 hy s hs
  refine ⟨b, ?_⟩
  rw [show algebraMap (𝓞 D.host.E) D.host.E b = (b : D.host.E) from rfl, hb]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem gram_inv_star (S : HSp D) (s : Fin S.rank → D.host.E) (e : Fin S.rank) :
    ∑ b, S.gram⁻¹ e b * star (∑ k, star (s k) * S.gram k b) = s e := by
  have : ∀ b, star (∑ k, star (s k) * S.gram k b) = (S.gram *ᵥ s) b := by
    intro b
    simp [star_sum, GlobalTheory.LatVac.gram_star, Matrix.mulVec, dotProduct, mul_comm]
  simp_rw [this]
  change (S.gram⁻¹ *ᵥ (S.gram *ᵥ s)) e = _
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.one_mulVec]

theorem map_gen (α : Af D.host.F) (c : AE D) (a : D.host.E) (S T : HSp D) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    ((c • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t) : WO S T).map (toEAf D)) =
      (toEAf D (c * incA D a) * ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D)) •
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)) *
          Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply,
    GlobalTheory.LatVac.finTens, GlobalTheory.LatVac.genMap, map_mul]
  change toEAf D c * ((a * t i * ∑ k, star (s k) * S.gram k j) ⊗ₜ[D.host.F] α) =
    toEAf D c * (a ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) *
      ((t i ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((∑ k, star (s k) * S.gram k j) ⊗ₜ[D.host.F] (1 : Af D.host.F)))
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem adj_shape {m n : ℕ} (c : EAf D) (C : Matrix (Fin m) (Fin 1) (EAf D)) (R : Matrix (Fin 1) (Fin n) (EAf D)) :
    ((c • (C * R)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      GlobalTheory.AdelicLatMove.cF D c • ((R.map (GlobalTheory.AdelicLatMove.cF D))ᵀ * (C.map (GlobalTheory.AdelicLatMove.cF D))ᵀ) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  rw [map_mul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [map_mul, mul_comm]

theorem cF_eToEAf (x : D.host.E) : GlobalTheory.AdelicLatMove.cF D (eToEAf D x) = eToEAf D (star x) := rfl

theorem frMapAdj_gen {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T} (hF : F.Good) {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q) {α : Af D.host.F}
    (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ F.ΛS)
    {t : Fin T.rank → D.host.E} (ht : t ∈ F.ΛT) :
    IsIntM (frMapAdj S T F.βS F.βT (cA D (idem Pg) • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, map_gen, adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem (toEAf_cA_idem_mul_mem hP ha) hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, cF_eToEAf, ← map_mul,
      ← map_sum]
    rw [gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, cF_eToEAf, ← map_mul,
      ← map_sum]
  have e : (F.βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * F.βT.val) =
      ((F.βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        F.βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact isIntM_mul (frame_col_int hF.frS hs) (pair_row_int hF.sdT hF.frT ht)

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem frMapAdj_neg {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x :=
  (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_neg x

theorem frMapAdj_zero {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 :=
  (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_zero

theorem frMapO_add {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_neg {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    frMapO S T βS βT (-x) = -frMapO S T βS βT x :=
  (AddMonoidHom.mk' _ (frMapO_add βS βT)).map_neg x

theorem frMapO_zero {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapO S T βS βT 0 = 0 :=
  (AddMonoidHom.mk' _ (frMapO_add βS βT)).map_zero

end GlobalTheory.ConjHalfInt
