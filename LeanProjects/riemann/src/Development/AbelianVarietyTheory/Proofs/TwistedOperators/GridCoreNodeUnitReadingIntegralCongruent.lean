import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemichara
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.UnitRead

theorem core_gen {R : Type} [CommRing R] (S : Subring R) (J : Ideal S) {n : ℕ} (f : R) (hf : f ∈ S)
    (γ : GL (Fin n) R) (B₁ B₂ : Matrix (Fin n) (Fin n) R)
    (hB₁ : ∀ i j, ∃ s ∈ J, (s : R) = B₁ i j) (hB₂ : ∀ i j, ∃ s ∈ J, (s : R) = B₂ i j)
    (heq : f • (1 - B₁) = γ.1 * (f • (1 - B₂))) (w₁ w₂ : R) (hw₁ : w₁ ∈ S) (hw₂ : w₂ ∈ S)
    (h1 : (1 - B₁).det * w₁ * f = f) (h2 : (1 - B₂).det * w₂ * f = f) :
    (∀ i j, (f • γ.1) i j ∈ S) ∧ (∀ i j, (f • (γ⁻¹).1) i j ∈ S) ∧
      ∀ i j, ∃ s ∈ J, (s : R) = (f • γ.1 - f • 1) i j := by
  choose s₁ hs₁ e₁ using hB₁
  choose s₂ hs₂ e₂ using hB₂
  have hint : ∀ (t : Fin n → Fin n → S), (1 - Matrix.of fun i j => (t i j : R)) = (1 - Matrix.of t).map S.subtype := by
    intro t
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.of_apply, Matrix.of_apply, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hB₁' : B₁ = Matrix.of fun i j => (s₁ i j : R) := by ext i j; exact (e₁ i j).symm
  have hB₂' : B₂ = Matrix.of fun i j => (s₂ i j : R) := by ext i j; exact (e₂ i j).symm
  have isInt_map : ∀ (X : Matrix (Fin n) (Fin n) S) i j, X.map S.subtype i j ∈ S := fun X i j => (X i j).2
  have isInt_adj : ∀ (X : Matrix (Fin n) (Fin n) S) i j, (X.map S.subtype).adjugate i j ∈ S := by
    intro X i j
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply]
    exact isInt_map _ i j
  have isInt_mul : ∀ (X Y : Matrix (Fin n) (Fin n) R), (∀ i j, X i j ∈ S) → (∀ i j, Y i j ∈ S) → ∀ i j, (X * Y) i j ∈ S := by
    intro X Y hX hY i j
    rw [Matrix.mul_apply]
    exact S.sum_mem fun k _ => S.mul_mem (hX i k) (hY k j)
  have isInt_smul : ∀ (c : R) (X : Matrix (Fin n) (Fin n) R), c ∈ S → (∀ i j, X i j ∈ S) → ∀ i j, (c • X) i j ∈ S := by
    intro c X hc hX i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact S.mul_mem hc (hX i j)
  have heq' : f • (1 - B₂) = (γ⁻¹).1 * (f • (1 - B₁)) := by
    rw [heq, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have adj : ∀ (C C' G : Matrix (Fin n) (Fin n) R) (w : R), C'.det * w * f = f → f • C = G * (f • C') →
      f • G = (w • (f • C)) * C'.adjugate := by
    intro C C' G w hw hC
    rw [hC]
    calc f • G = (C'.det * w * f) • G := by rw [hw]
      _ = _ := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_one, smul_smul]
        congr 1
        ring
  have hγ := adj _ _ _ w₂ h2 heq
  have hγ' := adj _ _ _ w₁ h1 heq'
  have hI₁ : ∀ i j, (1 - B₁) i j ∈ S := by rw [hB₁', hint]; exact isInt_map _
  have hI₂ : ∀ i j, (1 - B₂) i j ∈ S := by rw [hB₂', hint]; exact isInt_map _
  have hA₁ : ∀ i j, (1 - B₁).adjugate i j ∈ S := by rw [hB₁', hint]; exact isInt_adj _
  have hA₂ : ∀ i j, (1 - B₂).adjugate i j ∈ S := by rw [hB₂', hint]; exact isInt_adj _
  have hiγ : ∀ i j, (f • γ.1) i j ∈ S := by
    rw [hγ]
    exact isInt_mul _ _ (isInt_smul _ _ hw₂ (isInt_smul _ _ hf hI₁)) hA₂
  refine ⟨hiγ, ?_, ?_⟩
  · rw [hγ']
    exact isInt_mul _ _ (isInt_smul _ _ hw₁ (isInt_smul _ _ hf hI₂)) hA₁
  · have e1 : (f • γ.1) * (1 - B₂) = f • (1 - B₁) := by
      rw [heq, Matrix.smul_mul, Matrix.mul_smul]
    have e2 : f • γ.1 - f • 1 = (f • γ.1) * B₂ - f • B₁ := by
      have e3 : f • γ.1 - (f • γ.1) * B₂ = f • 1 - f • B₁ := by
        rw [← smul_sub, ← e1, Matrix.mul_sub, Matrix.mul_one]
      rw [← sub_eq_zero] at e3 ⊢
      rw [← e3]
      abel
    intro i j
    rw [e2, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨(∑ k, (⟨_, hiγ i k⟩ : S) * s₂ k j) - ⟨f, hf⟩ * s₁ i j,
      sub_mem (J.sum_mem fun k _ => J.mul_mem_left _ (hs₂ k j)) (J.mul_mem_left _ (hs₁ i j)), ?_⟩
    simp [e₁, e₂]

end GlobalTheory.UnitRead

namespace GlobalTheory.UnitRead

variable {D : D7}

theorem toEAf_idem_int {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h := GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e P he 1
    (fun Q _ h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h))
  simp at h
  exact GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h

theorem resS_idS {𝔪 : Ideal (𝓞 D.host.E)} {PP : Pl D.host.E} (h : 𝔪 ≤ PP.asIdeal)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ idS D.host.F 𝔪) : resS D.host.F PP s = 0 := by
  have hle : idS D.host.F 𝔪 ≤ RingHom.ker (resS D.host.F PP) := by
    unfold idS
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
    exact h ha
  exact hle hs

theorem one_sub_unit {𝔪 : Ideal (𝓞 D.host.E)} {Z : Finset (Pl D.host.E)} (hZ : ∀ PP ∈ Z, 𝔪 ≤ PP.asIdeal)
    {e : AE D} (he : IsIdemSum e Z) {n : ℕ} (B : Matrix (Fin n) (Fin n) (EAf D))
    (hB : ∀ i j, ∃ s ∈ idS D.host.F 𝔪, (s : EAf D) = B i j) :
    ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, (1 - B).det * w * toEAf D e = toEAf D e := by
  choose s hs hsB using hB
  have e0 : (1 - B) = (1 - Matrix.of s).map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype := by
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.of_apply, Matrix.one_apply,
      Matrix.one_apply, ← hsB]
    split_ifs <;> simp
  have hI : IsIntM (1 - B) := by rw [e0]; exact GlobalTheory.HalfUnit.isIntM_map _
  refine GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units Z e he _ (GlobalTheory.HalfUnit.det_mem hI) fun PP hPP => GlobalTheory.HalfUnit.isUnit_res_det PP hI ?_
  have hr : redM PP (1 - B) = 1 := by
    rw [e0, GlobalTheory.HalfUnit.redM_map]
    ext i j
    rw [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.of_apply, resS_idS (hZ PP hPP) (hs i j), sub_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hr, Matrix.det_one]
  exact isUnit_one

end GlobalTheory.UnitRead

namespace GlobalTheory.UnitRead

variable {D : D7}

theorem map_smul_one_sub {n : ℕ} (e : AE D) (a : Matrix (Fin n) (Fin n) (AE D)) :
    (e • (1 - a)).map (toEAf D) = toEAf D e • (1 - a.map (toEAf D)) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply,
    smul_eq_mul, smul_eq_mul, map_mul, map_sub, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem smul_mulVec_f {n : ℕ} (c : EAf D) (M : Matrix (Fin n) (Fin n) (EAf D)) (v : Fin n → EAf D) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

theorem conj_sub_one {R : Type} [CommRing R] {n : ℕ} (f : R) (b b' G : Matrix (Fin n) (Fin n) R) (h : b' * b = 1) :
    f • (b' * (G - 1) * b) = f • (b' * G * b) - f • (1 : Matrix (Fin n) (Fin n) R) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h, smul_sub]

theorem read_gen {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hlat : Submodule.IsLattice D.host.E Λ) {𝔪 : Ideal (𝓞 D.host.E)} {Z : Finset (Pl D.host.E)}
    (hZ : ∀ PP ∈ Z, 𝔪 ≤ PP.asIdeal) {e : AE D} (he : IsIdemSum e Z) (g : GA D V)
    (a₁ a₂ : Mx D V.rank V.rank) (ha₁ : a₁ ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat Λ Λ))
    (ha₂ : a₂ ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat Λ Λ))
    (heq : e • ((1 : WO V V) - a₁) = actO V V 1 g (e • (1 - a₂)))
    (x : Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E V.rank Λ hlat
  have hf := toEAf_idem_int he
  have hr : ∀ a : Mx D V.rank V.rank, a ∈ GlobalTheory.ChiGrid.hatMx (𝔪 • GlobalTheory.ChiGrid.homLat Λ Λ) →
      ∀ i j, ∃ s ∈ idS D.host.F 𝔪, (s : EAf D) = ((β⁻¹).1 * a.map (toEAf D) * β.1) i j :=
    fun a ha => ((GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ β β hβ hβ 𝔪 a).1 ha).2
  have hbb : (β⁻¹).1 * β.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbb' : β.1 * (β⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

  have hmap : toEAf D e • (1 - a₁.map (toEAf D)) =
      (Lev.finE V g).1 * (toEAf D e • (1 - a₂.map (toEAf D))) := by
    rw [actO, inv_one, GlobalTheory.ChainOnto.FrameAct.mt_one', Matrix.mul_one] at heq
    have h := congrArg (fun N : Mx D V.rank V.rank => N.map (toEAf D)) heq
    rw [map_smul_one_sub, Matrix.map_mul, map_smul_one_sub] at h
    exact h
  have hc : ∀ A : Matrix (Fin V.rank) (Fin V.rank) (EAf D),
      toEAf D e • (1 - (β⁻¹).1 * A * β.1) = (β⁻¹).1 * (toEAf D e • (1 - A)) * β.1 := by
    intro A
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [hbb]
  have hfr : toEAf D e • (1 - (β⁻¹).1 * a₁.map (toEAf D) * β.1) =
      (β⁻¹ * Lev.finE V g * β).1 * (toEAf D e • (1 - (β⁻¹).1 * a₂.map (toEAf D) * β.1)) := by
    rw [hc, hc, hmap, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.1 (β⁻¹).1, hbb', Matrix.one_mul]
  obtain ⟨w₁, hw₁, h1⟩ := one_sub_unit hZ he _ (hr a₁ ha₁)
  obtain ⟨w₂, hw₂, h2⟩ := one_sub_unit hZ he _ (hr a₂ ha₂)
  obtain ⟨hi1, hi2, hi3⟩ := core_gen (Formalism.L2.Herm.intAf D.host.F D.host.E) (idS D.host.F 𝔪) (toEAf D e) hf
    (β⁻¹ * Lev.finE V g * β) _ _ (hr a₁ ha₁) (hr a₂ ha₂) hfr w₁ w₂ hw₁ hw₂ h1 h2
  have key : ∀ (N : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) (y : Fin V.rank → EAf D),
      (β⁻¹).1 *ᵥ (toEAf D e • (N *ᵥ y)) = (toEAf D e • ((β⁻¹).1 * N * β.1)) *ᵥ ((β⁻¹).1 *ᵥ y) := by
    intro N y
    rw [Matrix.mulVec_smul, smul_mulVec_f, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β.1,
      hbb', Matrix.mul_one]
  have hy : ∀ k, ((β⁻¹).1 *ᵥ x) k ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (hβ x).1 hx
  have intv : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (EAf D)), (∀ i j, M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
      ∀ k, (M *ᵥ ((β⁻¹).1 *ᵥ x)) k ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro M hM k
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM k j) (hy j)
  refine ⟨(hβ _).2 fun k => ?_, (hβ _).2 fun k => ?_, ?_⟩
  · rw [key]
    exact intv _ (by simpa [Units.val_mul, Matrix.mul_assoc] using hi1) k
  · rw [key]
    have e4 := GlobalTheory.ChainOnto.FrameAct.conj_inv_val' β (Lev.finE V g)
    exact intv _ (by rw [← e4]; exact hi2) k
  · have e5 : toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) = toEAf D e • (((Lev.finE V g).1 - 1) *ᵥ x) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e5, GlobalTheory.FrameIdeal.mem_hatL_smul_iff β Λ hβ 𝔪]
    intro k
    rw [key]
    have e6 : toEAf D e • ((β⁻¹).1 * ((Lev.finE V g).1 - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D))) * β.1) =
        toEAf D e • (β⁻¹ * Lev.finE V g * β).1 - toEAf D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) := by
      rw [Units.val_mul, Units.val_mul]
      exact conj_sub_one _ _ _ _ hbb
    rw [e6]
    simp only [Matrix.mulVec, dotProduct]
    refine GlobalTheory.FrameIdeal.inId_sum _ fun j => ?_
    rw [mul_comm]
    exact GlobalTheory.FrameIdeal.inId_mul (hy j) (hi3 k j)

end GlobalTheory.UnitRead

theorem GlobalTheory.UnitRead.unit_read : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∀ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
    e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  intro D _ T L μ0 hL sc G W M hM i hi e he g a₁ ha₁ a₂ ha₂ heq x hx
  have hlat : Submodule.IsLattice D.host.E (G.Λ (.core i)) := (G.sp.P_is i hi.le).sd.1
  have hZ : ∀ PP ∈ G.pl.W0, G.modul ≤ PP.asIdeal := by
    intro PP hPP
    classical
    simp only [GlobalTheory.ChiGrid.Places.W0, Finset.mem_image] at hPP
    obtain ⟨v, hv, rfl⟩ := hPP
    have h1 : G.modul ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    exact h1.trans (Ideal.pow_le_self (G.pl.depth_pos sc v).ne')
  exact GlobalTheory.UnitRead.read_gen hlat hZ he g a₁ a₂ ha₁ ha₂ heq x hx
