import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HalfOInt

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem idem_mem_at (D : D7) (e : AE D) (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have h3 := mul_mem h2 (GlobalTheory.IdemIntegral.eToEAf_int D c)
  rw [map_mul, GlobalTheory.IdemIntegral.toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  rw [hc', hcast]
  field_simp

theorem idem_mem_intAf (D : D7) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => idem_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

theorem smul_genE {D : D7} {S T : HSp D} (e : AE D) (c : EAf D) (τ : Fin T.rank → EAf D)
    (σ : Fin S.rank → EAf D) :
    e • genE (S := S) (T := T) c τ σ = genE (toEAf D e * c) τ σ := by
  ext i j
  simp only [genE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_liftE, mul_assoc]

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

set_option maxHeartbeats 4000000 in

theorem frMapO_int_of_half {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT (fun _ => True)) (hh : IsHalf e u) :
    IsIntM (frMapO S T βS βT u) := by
  have hx : e • u = u := Matrix.ext fun i j => hh i j
  rw [← hx]
  clear hx hh
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, a, ha, s, hs, t, ht, rfl⟩ := hw
    show IsIntM (frMapO S T βS βT (e • genL S T α a s t))
    rw [genL_eq_genE, smul_genE, genE, frMapO_mapLiftE, mul_vecMulVec_mul]
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    refine mul_mem ?_ (mul_mem ?_ ?_)
    · rw [← mul_assoc]
      exact mul_mem (idem_mem_intAf D e P he hP a ha)
        (Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩))
    · exact (fT _).1 (mem_hatL_of_mem ht) i
    · rw [Matrix.vecMul_vecMul]
      have e : (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) =
          S.gram.map (eToEAf D) *ᵥ (fun i => (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j) := by
        funext l; rw [Matrix.mul_apply]; rfl
      show (fun k => sR D (eToEAf D (s k))) ⬝ᵥ
        (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) ∈ _
      rw [e]
      exact hform_int hS hs (col_mem_hatL fS j)
  | zero =>
    rw [smul_zero, frMapO_zero]
    exact fun _ _ => zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add, frMapO_add]
    exact isIntM_add hx hy
  | neg x _ hx =>
    rw [smul_neg, frMapO_neg]
    exact fun i j => neg_mem (hx i j)

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem sum_decomp {R : Type} [CommRing R] {m n N : ℕ} (M : Matrix (Fin m) (Fin n) R) (g Y : Fin N → Fin n → R)
    (hb : ∑ k, vecMulVec (g k) (Y k) = 1) (c z : R) (hM : (c * z) • M = M) :
    ∑ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = M := by
  have h : ∀ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = (c * z) • (M * vecMulVec (g k) (Y k)) := by
    intro k
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.smul_sum, ← Matrix.mul_sum, hb, Matrix.mul_one, hM]

set_option maxHeartbeats 4000000 in

theorem mem_latO_of_int {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {t : WO S T} (ht : IsHalf e t) (hN : IsIntM (frMapO S T βS βT t)) :
    t ∈ latO S T ΛS ΛT (fun _ => True) := by
  have ha := GlobalTheory.HalfAdjLattice.natCast_mem_AA (D := D) (D.host.QS * D.host.q)
  generalize D.host.QS * D.host.q * Ideal.absNorm D.host.ccK = n at hP ha
  obtain ⟨N, g, s, hg, hs, hb⟩ := GlobalTheory.HalfAdjLattice.exists_dual_families S hS
  have hz := GlobalTheory.HalfAdjLattice.toEAf_int (GlobalTheory.HalfAdjLattice.idem_div_int he hP)
  have hze := GlobalTheory.HalfAdjLattice.natCast_mul_idem_div he hP
  generalize e * incA D (n : D.host.E)⁻¹ = z at hz hze
  set M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.map t (toEAf D) with hMdef
  have hN' : IsIntM ((βT⁻¹).val * M * βS.val) := hN
  have hb' : ∑ k, vecMulVec (fun i => eToEAf D (g k i))
      (vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) = 1 := by
    ext i j
    have h1 := congrArg (eToEAf D) (congrFun (hb (Pi.single j 1)) i)
    rw [Finset.sum_apply, map_sum] at h1
    rw [Matrix.sum_apply]
    have h2 : eToEAf D ((Pi.single j 1 : Fin S.rank → D.host.E) i) = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← h2, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_single_one]
    simp only [vecMulVec_apply, vecMul, dotProduct, map_apply, sR_eTo, Pi.smul_apply, smul_eq_mul, map_mul, map_sum,
      Matrix.col, transpose_apply]
    exact mul_comm _ _
  have hM : ((eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z) • M = M := by
    have h1 : (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z = toEAf D e := by
      rw [← hze, map_mul, toEAf_incA, ← Algebra.TensorProduct.one_def, mul_one]
    rw [h1]
    ext i j
    simp only [hMdef, Matrix.smul_apply, map_apply, smul_eq_mul]
    rw [← map_mul, ht i j]
  have key := sum_decomp M (fun k i => eToEAf D (g k i))
    (fun k => vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) hb' _ _ hM
  have hdec : t = ∑ k, genE (S := S) (T := T)
      (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)))
      (toEAf D z • (M *ᵥ fun i => eToEAf D (g k i))) (fun a => eToEAf D (s k a)) := by
    ext i j
    have h1 := congrFun (congrFun key i) j
    rw [Matrix.sum_apply] at h1
    rw [Matrix.sum_apply]
    unfold genE
    simp only [map_apply]
    rw [← liftE_sum, h1]
    have h0 : infPart D (t i j) = 0 := by rw [← ht i j, map_mul, infPart_of_idemSum he, zero_mul]
    exact (liftE_toEAf _ h0).symm
  rw [hdec]
  refine AddSubgroup.sum_mem _ fun k _ => genE_mem ?_ ha ?_ (mem_hatL_of_mem (hs k))
  · intro v; rw [map_one]; exact one_mem _
  · exact Submodule.smul_mem _ (⟨_, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
      (GlobalTheory.HalfAdjLattice.mulVec_mem_hatL fT fS hN' (mem_hatL_of_mem (hg k)))

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt

theorem mem_latO_iff_frMapO_int : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ w : WO S T, IsHalf e w → (w ∈ latO S T ΛS ΛT (fun _ => True) ↔ IsIntM (frMapO S T βS βT w)) := by
  intro D S T ΛS ΛT βS βT hS _ fS fT P e he hP w hw
  exact ⟨fun hu => frMapO_int_of_half hS fS fT he hP hu hw, fun hN => mem_latO_of_int hS fS fT he hP hw hN⟩

end GlobalTheory.HalfOInt
