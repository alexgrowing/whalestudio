import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcPrVEqOneOfAdAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section

open Formalism.L2.DIV Formalism.L2.Col Formalism.UG

namespace GlobalTheory.Mem.Col2.AdT.SplitChi

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_conjP_eq_one (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ r s, adAt F P (u.1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) (r s : Fin n) :
    adAt F (conjPrime₂ P) (u.1 r s) = (1 : Matrix (Fin n) (Fin n) ((conjPrime₂ P).adicCompletion E)) r s := by
  subst hJ
  have hinv := GlobalTheory.Mem.Col2.AdT.Opn.inv_eq_cT hc.sig hu
  have h1 : (u : Matrix (Fin n) (Fin n) (AfE F E)) *
      (1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)) = 1 := by
    rw [← hinv, Units.mul_inv]
  have hC : (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)).map
      (adAt F (conjPrime₂ P)) = 0 := by
    refine Matrix.ext fun i j => ?_
    show adAt F (conjPrime₂ P) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i)) = 0
    have e2 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) j i := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    have hX : adAt F P (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i) = 0 := by
      rw [Matrix.sub_apply, map_sub, hP, e2, sub_self]
    have e := GlobalTheory.Mem.Col2.valued_sigR hc (conjPrime₂ P) (((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) j i)
    rw [GlobalTheory.CharValCompare.conjP_conjP, hX, Valuation.map_zero] at e
    exact (Valuation.zero_iff _).1 e
  have h2 := congrArg (adAt F (conjPrime₂ P)).mapMatrix h1
  rw [map_mul, map_add, map_one] at h2
  change _ * (1 + (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1)).map
      (adAt F (conjPrime₂ P))) = 1 at h2
  rw [hC, add_zero, mul_one] at h2
  exact congrFun (congrFun h2 r) s

theorem bc_prV_eq_one_of_split (hc : CMData F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {u : GL (Fin n) (AfE F E)}
    (hu : u ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hover : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P)
    (hP : ∀ r s, adAt F P (u.1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) :
    bc (prV (E := E) v) u = 1 := by
  refine GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt F E n v u fun w hw r s => ?_
  rcases hover w hw with rfl | rfl
  · rw [hP, Matrix.one_apply]
  · rw [adAt_conjP_eq_one hc hJ hu P hP r s, Matrix.one_apply]

end Gen

section Root

theorem exists_root_GL {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (m n : ℕ) (hn : 0 < n)
    (c : P.adicCompletion E) (hc : Valued.v c < 1) (A : GL (Fin m) (P.adicCompletion E))
    (hA : ∀ r s, Valued.v (A.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤
      Valued.v ((n : P.adicCompletion E) ^ 2 * c)) :
    ∃ M : GL (Fin m) (P.adicCompletion E), M ^ n = A ∧
      ∀ r s, Valued.v (M.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ Valued.v ((n : P.adicCompletion E) * c) := by
  obtain ⟨M, hM1, hM2⟩ := GlobalTheory.MatNthRoot.exists_nthRoot E P m n c A.1 hn hc
    (fun r s => by rw [Matrix.sub_apply]; exact hA r s)
  have hu : IsUnit M := (isUnit_pow_iff hn.ne').1 (hM2 ▸ A.isUnit)
  obtain ⟨M, rfl⟩ := hu
  exact ⟨M, Units.ext (by rw [Units.val_pow_eq_pow_val, hM2]), fun r s => by rw [← Matrix.sub_apply]; exact hM1 r s⟩

end Root

section Fin

theorem chi_eq_one_of_pow {G : Type} [Group G] {U : Subgroup G} (χ : U →* ℂˣ) (x z : U) (n : ℕ) (hz : χ z ^ n = 1)
    (hy : χ ((z ^ n)⁻¹ * x) = 1) : χ x = 1 := by
  rw [map_mul, map_inv, map_pow, hz, inv_one, one_mul] at hy
  exact hy

theorem map_inv_pow_mul_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {x z : G} (n : ℕ) (hz : f z = 1) (hx : f x = 1) :
    f ((z ^ n)⁻¹ * x) = 1 := by
  rw [map_mul, map_inv, map_pow, hz, hx, one_pow, inv_one, one_mul]

end Fin

set_option maxHeartbeats 2000000 in

theorem chi_eq_one_of_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (n : ℕ), 0 < n → (∀ κ : S.U, S.chi κ ^ n = 1) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x.1 = 1) → ∀ w : GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N w → bc (prV (E := (I.rec7 l Z).host.E) v) x.1 = bc (prV (E := (I.rec7 l Z).host.E) v) w → S.chi x = 1 := by
  intro B X I hI hPin l Z a T i hi bad S n hn hchi P v hv
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep I hI hPin l Z a T i hi bad S P v hv
  have hd := fun N z => GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z
  obtain ⟨hs, hq, -⟩ := hd 0 1
  have hu : P.1.under (𝓞 B.host.F) = v := by
    rw [hs] at hv
    exact HeightOneSpectrum.ext (Eq.symm hv)
  haveI : CharZero (P.1.adicCompletion B.fields.E) := algebraRat.charZero _
  set c : P.1.adicCompletion B.fields.E := ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) ^ (N₀ + 1) with hcdef
  have hc : Valued.v c = WithZero.exp (-((N₀ : ℤ) + 1)) := by
    rw [hcdef, map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc1 : Valued.v c < 1 := by
    rw [hc, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hn1 : Valued.v (n : P.1.adicCompletion B.fields.E) ≤ 1 := GlobalTheory.MatNthRoot.v_natCast_le_one n
  have hε : Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c) ≠ 0 := by
    rw [map_mul, hc]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  set e := WithZero.log (Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c)) with he
  refine ⟨(-e).toNat, fun x hxv w hw hxw => ?_⟩

  have hxP : ∀ r s, adAt B.host.F P.1 (x.1.1 r s) = adAt B.host.F P.1 (w.1 r s) := fun r s => by
    have h := congrArg (fun g : GL (Fin ((I.rec7 l Z).R.N i)) _ => g.1 r s) hxw
    refine GlobalTheory.Mem.Col2.AdT.LocSplice.adAt_eq_of_prV P.1 ?_
    rw [hu]
    exact h
  have hwP := ((hd _ w).2.2).1 hw
  have hwP := ((hd (-e).toNat w).2.2).1 hw
  have hA : ∀ r s, Valued.v (adAt B.host.F P.1 (x.1.1 r s) - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E)) r s) ≤
      Valued.v ((n : P.1.adicCompletion B.fields.E) ^ 2 * c) := fun r s => by
    rw [hxP]
    refine (hwP r s).trans ?_
    rw [← WithZero.exp_log hε, ← he]
    exact WithZero.exp_le_exp.2 (by omega)
  let x' : GlobalTheory.Mem.Col2.TC.GA B (B.R.N i) := x.1
  obtain ⟨Mu, hMun, hMu1⟩ := exists_root_GL P.1 (B.R.N i) n hn c hc1
    (Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) x') hA
  obtain ⟨z, hzU, hzv, hzP⟩ := GlobalTheory.Mem.Col2.AdLift.exists_lift I hI hPin l Z a i hi P v hv Mu
  have hz : z ∈ S.U := hN₀ z hzU hzv (((hd N₀ z).2.2).2 fun r s => by
    rw [hzP]
    refine (hMu1 r s).trans ?_
    rw [map_mul, hc]
    exact (mul_le_of_le_one_left' hn1).trans (WithZero.exp_le_exp.2 (by omega)))
  have hgU : (z ^ n)⁻¹ * x.1 ∈ S.U := by
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hz n)) x.2
  have hyU := ((S.U_eq _).1 hgU).1
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hPin l Z).2.2.2 i hi).1
  let z' : GlobalTheory.Mem.Col2.TC.GA B (B.R.N i) := z
  have hzmap : Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) z' = Mu := Units.ext (Matrix.ext hzP)
  have key : Matrix.GeneralLinearGroup.map (adAt B.host.F P.1) ((z' ^ n)⁻¹ * x') = 1 := by
    rw [map_mul, map_inv, map_pow, hzmap, hMun, inv_mul_cancel]
  have hyP : ∀ r s, adAt B.host.F P.1 (((z ^ n)⁻¹ * x.1).1 r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E)) r s :=
    fun r s => congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) key
  have hover : ∀ w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E), w.under (𝓞 (I.rec7 l Z).host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 :=
    fun w hw => (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 w).1 (hw.trans hu.symm)
  have hyv : ∀ v', bc (prV (E := (I.rec7 l Z).host.E) v') ((z ^ n)⁻¹ * x.1) = 1 := by
    intro v'
    by_cases hv' : v' = v
    · rw [hv']
      exact bc_prV_eq_one_of_split (I.rec7 l Z).sp.cm hgram hyU P.1 v hover hyP
    · exact map_inv_pow_mul_eq_one _ n (hzv v' hv') (hxv v' hv')
  exact chi_eq_one_of_pow S.chi x ⟨z, hz⟩ n (hchi _) (S.chi_triv _ fun v' _ => hyv v')

end GlobalTheory.Mem.Col2.AdT.SplitChi

end
