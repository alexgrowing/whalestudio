import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcPrVEqOneOfAdAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitA
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdLift

section General

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sng (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E) : AfE F E := (afIso F E).symm (Formalism.UG.P.afsplitF P x)

theorem adAt_sng_self (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E) : adAt F P (sng F P x) = x := by
  rw [adAt_apply, sng]
  simp only [RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact Formalism.UG.P.afsplitF_self P x

theorem adAt_sng_ne {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) (x : P.adicCompletion E) : adAt F w (sng F P x) = 0 := by
  rw [adAt_apply, sng]
  simp only [RingEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact Formalism.UG.P.afsplitF_ne P w h x

def dev {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    Matrix (Fin n) (Fin n) (AfE F E) := (A - 1).map (sng F P)

theorem map_dev_self {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    (1 + dev F P A).map (adAt F P) = A := by
  ext i j
  simp only [dev, Matrix.map_apply, Matrix.add_apply, map_add, adAt_sng_self, Matrix.sub_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem map_dev_ne {n : ℕ} {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) (A : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    (1 + dev F P A).map (adAt F w) = 1 := by
  ext i j
  simp only [dev, Matrix.map_apply, Matrix.add_apply, map_add, adAt_sng_ne F h, Matrix.one_apply]
  split_ifs <;> simp

variable {F}

theorem mat_ext {n : ℕ} {M N : Matrix (Fin n) (Fin n) (AfE F E)} (h : ∀ w, M.map (adAt F w) = N.map (adAt F w)) : M = N := by
  ext i j
  exact PtExist.ad_ext fun w => congrFun (congrFun (h w) i) j

variable [StarRing E] (hc : CMData F E)

local notation "σ" => Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F)

theorem map_cT_dev {n : ℕ} {P w : HeightOneSpectrum (𝓞 E)} (h : conjPrime₂ w ≠ P) (A : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    (cT σ (1 + dev F P A)).map (adAt F w) = 1 := by
  have key : ∀ x, adAt F w (σ (sng F P x)) = 0 := fun x => by
    have e := valued_sigR hc w (sng F P x)
    rwa [adAt_sng_ne F h, map_zero, Valuation.zero_iff] at e
  refine Matrix.ext fun i j => ?_
  show adAt F w (σ ((1 + dev F P A) j i)) = _
  simp only [dev, Matrix.map_apply, Matrix.add_apply, map_add, key, Matrix.one_apply]
  by_cases e : i = j
  · subst e; simp
  · simp [e, Ne.symm e]

theorem cT_cT {n : ℕ} (M : Matrix (Fin n) (Fin n) (AfE F E)) : cT σ (cT σ M) = M := by
  ext i j
  exact PtExist.sig_sig hc (M i j)

theorem exists_unitary {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} (hP : conjPrime₂ P ≠ P) (A : GL (Fin n) (P.adicCompletion E)) :
    ∃ z ∈ UAd hc n, (∀ w, w ≠ P → w ≠ conjPrime₂ P → ∀ i j, adAt F w (z.1 i j) = if i = j then 1 else 0) ∧
      ∀ i j, adAt F P (z.1 i j) = A.1 i j := by
  set g := 1 + dev F P A.1 with hg
  set g' := 1 + dev F P (A⁻¹).1 with hg'
  have h1 : g' * g = 1 := mat_ext fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    by_cases e : w = P
    · subst e
      rw [map_dev_self, map_dev_self, Units.inv_mul]
    · rw [map_dev_ne F e, map_dev_ne F e, mul_one]
  have h2 : cT σ g * cT σ g' = 1 := by rw [← cT_mul, h1, cT_one]
  have h3 : cT σ g * g = g * cT σ g := mat_ext fun w => by
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases e : w = P
    · subst e
      rw [map_cT_dev hc hP, mul_one, one_mul]
    · rw [map_dev_ne F e, mul_one, one_mul]
  have h4 : cT σ (g * cT σ g') * (g * cT σ g') = 1 := by
    rw [cT_mul, cT_cT, mul_assoc, ← mul_assoc (cT σ g), h3, mul_assoc, h2, mul_one, h1]
  refine ⟨⟨g * cT σ g', cT σ (g * cT σ g'), mul_eq_one_comm.1 h4, h4⟩, (PtExist.mem_uad_iff _).2 h4,
    fun w hw hw' i j => ?_, fun i j => ?_⟩
  · have e : (g * cT σ g').map (adAt F w) = 1 := by
      rw [Matrix.map_mul, map_dev_ne F hw, map_cT_dev hc (fun e => hw' (by rw [← e, CharValCompare.conjP_conjP])), mul_one]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    exact this
  · have e : (g * cT σ g').map (adAt F P) = A.1 := by
      rw [Matrix.map_mul, map_dev_self, map_cT_dev hc hP, mul_one]
    exact congrFun (congrFun e i) j

end General

theorem exists_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ A : GL (Fin ((I.rec7 l Z).R.N i)) (P.1.adicCompletion B.fields.E), ∃ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) ∧ ∀ r s, adAt B.host.F P.1 (z.1 r s) = A.1 r s := by
  intro B X I hI hP l Z a i hi P v hv A
  have hJ := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have hne : conjPrime₂ P.1 ≠ P.1 := fun e =>
    GlobalTheory.Proof.NarrowJetMoments.conjP_notMem_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 hI.sel_ok hI.g_mem P.2
      (by rw [e]; exact P.2)
  have hs : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 x
  have hu : P.1.under (𝓞 B.host.F) = v := by
    rw [hs] at hv
    exact HeightOneSpectrum.ext (Eq.symm hv)
  obtain ⟨z, hz, h1, h2⟩ := exists_unitary (F := B.host.F) B.sp.cm hne A
  have key : ∀ v' : HeightOneSpectrum (𝓞 B.host.F), v' ≠ P.1.under (𝓞 B.host.F) → bc (prV (E := B.host.E) v') z = 1 := by
    intro v' hv'
    have e0 := AdPlace.bc_prV_eq_one_of_adAt _ _ _ v' z fun w hw => by
      have := (under_eq_iff B.host P.1 w).not.1 (hw ▸ hv')
      exact h1 w (fun e => this (Or.inl e)) fun e => this (Or.inr e)
    exact e0
  refine ⟨z, ?_, fun v' hv' => key v' fun e => hv' (e.trans hu), h2⟩
  rw [hJ]
  exact hz

end GlobalTheory.Mem.Col2.AdLift

end
