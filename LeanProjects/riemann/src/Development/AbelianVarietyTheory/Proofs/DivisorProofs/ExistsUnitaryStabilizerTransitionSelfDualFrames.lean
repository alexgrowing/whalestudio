import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitSumStabLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameChange

open Formalism.L2.DIV
open scoped Matrix TensorProduct

set_option synthInstance.maxHeartbeats 160000

private theorem int_of_parts {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n]
    (G Gi : Matrix n n R) (hGG : G * Gi = 1) (ε ε' : R) (hε : ε ∈ O) (hε' : ε' ∈ O)
    (hs : (ε + ε') • (G - 1) = G - 1) (h1 : ∀ i j, ε * G i j ∈ O) (h2 : ∀ i j, ε' * G i j ∈ O)
    (h3 : ∀ i j, ε * Gi i j ∈ O) (h4 : ∀ i j, ε' * Gi i j ∈ O) :
    (∀ i j, G i j ∈ O) ∧ ∀ i j, Gi i j ∈ O := by
  have hone : ∀ i j, (1 : Matrix n n R) i j ∈ O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  have hs1 : (1 - ε - ε') ∈ O := O.sub_mem (O.sub_mem O.one_mem hε) hε'
  have hA : (1 - (ε + ε')) • G = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    have : (1 - (ε + ε')) • (G - 1) = 0 := by rw [sub_smul, one_smul, hs, sub_self]
    rw [smul_sub, sub_eq_zero] at this
    exact this
  have hB : (1 - (ε + ε')) • Gi = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    calc (1 - (ε + ε')) • Gi = ((1 - (ε + ε')) • (1 : Matrix n n R)) * Gi := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = ((1 - (ε + ε')) • G) * Gi := by rw [hA]
      _ = (1 - (ε + ε')) • (1 : Matrix n n R) := by rw [Matrix.smul_mul, hGG]
  constructor
  · intro i j
    have e1 := congrFun (congrFun hA i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : G i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * G i j + ε' * G i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h1 i j)) (h2 i j)
  · intro i j
    have e1 := congrFun (congrFun hB i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : Gi i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * Gi i j + ε' * Gi i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h3 i j)) (h4 i j)

private theorem smul_conj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b b' X : GL n R) (ε : R)
    (h : ε • X.1 = ε • (b' * b⁻¹ : GL n R).1) :
    ε • (b⁻¹ * X * b : GL n R).1 = ε • (b⁻¹ * b' : GL n R).1 ∧
      ε • ((b⁻¹ * X * b)⁻¹ : GL n R).1 = ε • (b'⁻¹ * b : GL n R).1 := by
  have key : ∀ u v : GL n R, ε • (u * X * v : GL n R).1 = ε • (u * (b' * b⁻¹) * v : GL n R).1 := by
    intro u v
    simp only [Units.val_mul] at h ⊢
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · rw [key, show b⁻¹ * (b' * b⁻¹) * b = b⁻¹ * b' by group]
  · have := key (b⁻¹ * X⁻¹) (b * b'⁻¹ * b)
    rw [show b⁻¹ * X⁻¹ * X * (b * b'⁻¹ * b) = b'⁻¹ * b by group,
      show b⁻¹ * X⁻¹ * (b' * b⁻¹) * (b * b'⁻¹ * b) = (b⁻¹ * X * b)⁻¹ by group] at this
    exact this.symm

private theorem smul_conj_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b X : GL n R) (s : R)
    (h : s • (X.1 - 1) = X.1 - 1) :
    s • ((b⁻¹ * X * b : GL n R).1 - 1) = (b⁻¹ * X * b : GL n R).1 - 1 := by
  have e : (b⁻¹ * X * b : GL n R).1 - 1 = (b⁻¹).1 * (X.1 - 1) * b.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h]

private theorem exists_int_GL {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n] (γ : GL n R)
    (h1 : ∀ i j, γ.1 i j ∈ O) (h2 : ∀ i j, (γ⁻¹).1 i j ∈ O) : ∃ y : GL n O, y.1.map O.subtype = γ.1 := by
  let A : Matrix n n O := Matrix.of fun i j => ⟨γ.1 i j, h1 i j⟩
  let B : Matrix n n O := Matrix.of fun i j => ⟨(γ⁻¹).1 i j, h2 i j⟩
  have hA : A.map O.subtype = γ.1 := rfl
  have hB : B.map O.subtype = (γ⁻¹).1 := rfl
  have hinj : Function.Injective (fun M : Matrix n n O => M.map O.subtype) :=
    Matrix.map_injective O.subtype_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, hA⟩
  · show (A * B).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · show (B * A).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem frame_inv_mul_int {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {b b' : GL (Fin n) (EAf D)} (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (i j : Fin n) :
    (b⁻¹ * b' : GL (Fin n) (EAf D)).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : b'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [hb']
    intro k
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h2 := (hb _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2

set_option maxHeartbeats 800000 in

private theorem mem_St_of_comp {D : D7} (e : AE D) (he : e * e = e) (V : HSp D)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (b b' : GL (Fin V.rank) (EAf D)) (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (k : GA D V) (hk : SuppAt e V k)
    (hc : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) :
    Formalism.IndefR.Lev.finE V k ∈ St b := by
  have hidem : ∀ a : AE D, a * a = a → toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha =>
    Formalism.IndefR.Fin.LevelGroupLemmas.toEAf_mem_intAf (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, ha]))
  have hε := hidem e he
  have hε' := hidem (cA D e) (by rw [← map_mul, he])
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin V.rank) (EAf D), X = Formalism.IndefR.Lev.finE V k := ⟨_, rfl⟩
  have hXv : X.1 = (mt V k).map (toEAf D) := by rw [hX]; rfl
  have hc' : toEAf D e • X.1 = toEAf D e • (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1 := by
    rw [hX]; exact Matrix.ext fun i j => hc i j
  obtain ⟨c1, c2⟩ := smul_conj b b' X (toEAf D e) hc'
  have hs : (toEAf D e + toEAf D (cA D e)) • (X.1 - 1) = X.1 - 1 := by
    refine Matrix.ext fun i j => ?_
    have h0 := congrArg (toEAf D) (hk i j)
    have h1 : toEAf D ((mt V k - 1) i j) = (X.1 - 1) i j := by
      rw [hXv, Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
    rw [map_mul, RingHom.map_add, h1] at h0
    exact h0
  have i1 : ∀ i j, (toEAf D e • (b⁻¹ * X * b : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c1]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb hb' i j)
  have i2 : ∀ i j, (toEAf D e • ((b⁻¹ * X * b)⁻¹ : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c2]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb' hb i j)
  obtain ⟨j1, j2⟩ := GlobalTheory.ConjIntegral.conj_smul_isIntM V Λ b hΛ hb X (hX ▸ GlobalTheory.LevSplit.finE_mem_UA V k)
    (b⁻¹ * X * b) rfl e i1 i2
  obtain ⟨g1, g2⟩ := int_of_parts (Formalism.L2.Herm.intAf D.host.F D.host.E) _ _ (Units.mul_inv (b⁻¹ * X * b)) _ _ hε hε'
    (smul_conj_sub_one b X _ hs) i1 j1 i2 j2
  obtain ⟨y, hy⟩ := exists_int_GL _ _ g1 g2
  refine ⟨y, ?_⟩
  have hy' : intGL D.host.F D.host.E V.rank y = b⁻¹ * X * b := Units.ext hy
  rw [← hX]
  show b * intGL D.host.F D.host.E V.rank y * b⁻¹ = X
  rw [hy']; group

set_option maxHeartbeats 800000 in

private theorem exists_unitary_frame_change : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y := by
  intro D e S hS V Λ hΛ b b' hb hb'
  have he : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hS
  have he' : e * cA D e = 0 := hS.2
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  let inv : EAf D →+* (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toRingEquiv.toRingHom
  have hinv : ∀ x, Lev.swapAE D (inv x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a c => rfl
    | add a c ha hc => rw [RingHom.map_add, RingHom.map_add, ha, hc]
  let P : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1
  let Q : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b * b'⁻¹ : GL (Fin V.rank) (EAf D)).1
  have hPQ : P * Q = 1 := by
    show (b' * b⁻¹ * (b * b'⁻¹) : GL (Fin V.rank) (EAf D)).1 = 1
    rw [show b' * b⁻¹ * (b * b'⁻¹) = 1 by group]
    rfl
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.SplitLift.exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D)
    GlobalTheory.DualPairCheck.cA_cA _ _ hJ hJK e he he' hinf (P.map inv) (Q.map inv)
    (by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)])
  let k : GA D V := ⟨g, hg⟩
  have hval : ∀ i j, (Lev.finE V k).1 i j = Lev.swapAE D (finPart D (g.1 i j)) := fun i j => rfl
  have hcomp : ∀ i j, toEAf D e * (Lev.finE V k).1 i j = toEAf D e * P i j := by
    intro i j
    have h3 : finPart D e * finPart D (g.1 i j) = finPart D e * inv (P i j) := congrFun (congrFun h2 i) j
    rw [hval, show toEAf D e = Lev.swapAE D (finPart D e) from rfl, ← map_mul, h3, map_mul, hinv]
  have hk : SuppAt e V k := h1
  have hSt := mem_St_of_comp e he V Λ hΛ b b' hb hb' k hk hcomp
  refine ⟨k, hk, GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.stabLat_of_mem_St V Λ b hb k hSt, hcomp, ?_⟩
  intro y hy
  have hyv : (y : AE D) = e * (mt V k).det + (1 - e) := hy
  have hyd : y = Formalism.IndefR.Fin.LevelGroupLemmas.detAt e V k :=
    Units.ext (hyv.trans (Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he V k).symm)
  have hint : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])
  refine ⟨?_, ?_, ?_⟩
  · rw [hyv, RingHom.map_add, map_mul, RingHom.map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_int he hint V hSt
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_inv_int he hint V hSt

end GlobalTheory.FrameChange

end

theorem _root_.GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y :=
  GlobalTheory.FrameChange.exists_unitary_frame_change
