import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirstStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.LowerTower

open GlobalTheory.SmallerSource GlobalTheory.FockAlg

theorem lamA_mem (al be ga de : List ℚ) (a : Ix (al.length + be.length) (ga.length + de.length)) :
    lamA al be ga de a ∈ al ++ be ++ ga ++ de := by
  rw [List.append_assoc (al ++ be)]
  cases a with
  | inl i => exact List.mem_append_left _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) i)
  | inr j => exact List.mem_append_right _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) j)

theorem tensNo_first (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hpq : 1 ≤ p + q) (lam : Ix p q → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair r s) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair r s) (blattner lam) a ≤ 0))
    (hno : ∀ μ', ¬ JointShape p q r s (blattner lam) μ') :
    TensNo (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) := by
  intro MM f hf
  by_contra hne
  obtain ⟨hadm, hirr⟩ := discrete_series_gk_admissible_irreducible X h5 hpq lam
  obtain ⟨hone, -, hcone⟩ := hD p q lam hlam
  have hex : ∃ v, IsHW (X.ds p q lam).HK.act (blattner lam) v := by
    have hnb : hwSub (X.ds p q lam).HK.act (blattner lam) ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hone
      exact zero_ne_one hone
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
    exact ⟨v, hv0, hv⟩
  have hflow := GlobalTheory.T.degW_blattner_le_of_blattnerCone p q (X.ds p q lam).HK lam (cPair r s) θ hcone hsign
  obtain ⟨⟨μ, P, hPJ, hP1, hP2, -⟩, -⟩ :=
    GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub p q r s (X.ds p q lam).HK MM f hirr hadm hf hne (blattner lam) hex hflow
  have hbot := ((GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 (blattner lam) μ).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 (blattner lam) ⊓ hwSub (X.fock p q r s).act2 μ ⊓
      Submodule.span ℂ (X.fock p q r s).J :=
    ⟨⟨hP1.2, hP2.2⟩, Submodule.subset_span hPJ⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hP1.1 hmem

theorem tensNo_second (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam)) :
    TensNo (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam) := by
  intro MM f hf
  set c := TensorProduct.comm ℂ (X.ds r s lam).HK.V MM.V with hc
  have hcm : ∀ (A : Module.End ℂ (X.ds r s lam).HK.V) (B : Module.End ℂ MM.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hg : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK ((c : _ →ₗ[ℂ] _) ∘ₗ f) := by
    refine ⟨fun Z => LinearMap.ext fun P => ?_, fun Z => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct1 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
    · have := LinearMap.congr_fun (hf.1 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct2 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
  have h0 := intw_eq_zero X (GlobalTheory.JointHarm.fock_polynomials X) hD h5 hrs lam hlam θ hsign hno MM _ hg
  refine LinearMap.ext fun P => ?_
  have : c (f P) = 0 := LinearMap.congr_fun h0 P
  exact c.map_eq_zero_iff.1 this

theorem no_map_lower : ∀ (X : ProvA), DiscreteSeriesBlattner X → admQ5 X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → TensNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (fockAct2 _ _ _ _) (X.ds _ _ (lamA al be ga de))) ∧ ((∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → i ≤ al.length + be.length → i ≤ ga.length + de.length → TensNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (fockAct1 _ _ _ _) (X.ds _ _ (lamA' t al be ga de))) := by
  intro X hD h5 t al be ga de hA i hi
  have ht : 1 ≤ t := hA.1
  have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  obtain ⟨-, hpar, hpar', hsign, hsign'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  obtain ⟨hno, -, hno'⟩ := GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi
  refine ⟨fun hr hs => ?_, fun hbig hp hq => ?_⟩
  · refine tensNo_first X hD h5 (by omega) _ hpar 0 ?_ (hno hr hs)
    rw [cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith
  · refine tensNo_second X hD h5 (by omega) _ hpar' ((t : ℚ) / 2) ?_ (hno' (.inl ?_) hp hq).1
    · rw [cPair_sub hp hq]
      exact hsign'
    · rintro ⟨a, ha⟩
      have := hbig _ (lamA_mem al be ga de a)
      rw [ha, abs_of_nonneg (by positivity)] at this
      linarith

end GlobalTheory.LowerTower
