import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEqSmulOfIsot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeHasSphericalHeckeEigensystem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem

noncomputable section

namespace GlobalTheory.EigRows

section Abstract

variable {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]

end Abstract

section Record

open Formalism.BasicNotions

def OccGood (D : D7) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ

theorem occGood_of_all (D : D7) (h : GoodFTAll D) : OccGood D := fun _ _ _ σ _ => h σ

end Record

section Real

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx
  Formalism.IndefR.RecTie GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

abbrev levW (R : RealDat D A3.A Ks) (F : Face D A3.A) (i : Fin D.R.m) : Set (GA D (Wc D i)) :=
  levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A3.A)))

abbrev chiW (R : RealDat D A3.A Ks) (F : Face D A3.A) (i : Fin D.R.m) : GA D (Wc D i) → ℂ :=
  levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A3.A)))

abbrev goodW (R : RealDat D A3.A Ks) (F : Face D A3.A) (i : Fin D.R.m) :
    Submodule ℂ (Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A))) :=
  Formalism.IndefR.Mult.goodPart R.θ (R.MW i (sg0 D A3.A)) (levW R F i) (chiW R F i) (R.eWf i (sg0 D A3.A))

def partR (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) (σ : D.what₂.FT) :
    Submodule ℂ (Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A))) :=
  principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levW R F i) (chiW R F i) (R.eWf i (sg0 D A3.A))
    (principalLevelFrame.rowRepR R.θ (Y.eFT σ))

def readW (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) :
    D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) :=
  (R.HW i (sg0 D A3.A)).e ∘ₗ Y.mj.eW i

theorem lift_readW (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) (y : D.what₂.Mj ((i : ℕ) + 1)) :
    PiTensorProduct.lift (readW Y i y) = (Y.IL.jMj i y).1 :=
  (Y.mjRead i y).symm

theorem mem_isot_iff (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) (σ : D.what₂.FT) (y : D.what₂.Mj ((i : ℕ) + 1)) :
    y ∈ D.what₂.isot ((i : ℕ) + 1) σ ↔ readW Y i y ∈ partR Y i σ := by
  rw [Y.tied.lift.isot, Y.prtWE, ← lift_readW]
  change PiTensorProduct.lift (readW Y i y) ∈ (partR Y i σ).map
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap ↔ _
  constructor
  · intro h
    obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 h
    have h' := (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective e
    rw [h'] at ha
    exact ha
  · intro h
    exact Submodule.mem_map_of_mem h

theorem exists_readW (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) {x : Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A))}
    (hx : x ∈ goodW R F i) : ∃ y, readW Y i y = x := by
  refine ⟨(Y.IL.jMj i).symm ⟨PiTensorProduct.lift x, Submodule.mem_map_of_mem hx⟩, ?_⟩
  apply (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective
  rw [lift_readW, LinearEquiv.apply_symm_apply]
  rfl

abbrev SbR (Y : Read (A3 := A3) R F X0) : Finset (HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) :=
  SsetF R (Y.tupT D.what₂.mu0)

def HkOnParts (Y : Read (A3 := A3) R F X0)
    (lam : Fin D.R.m → D.what₂.FT → HeightOneSpectrum (NumberField.RingOfIntegers D.host.E) → ℕ → ℂ) : Prop :=
  ∀ i σ, partR Y i σ ≤ Formalism.IndefR.Mult.part R.θ (R.MW i (sg0 D A3.A)) (levW R F i) (chiW R F i) (SbR Y) (lam i σ)

end Real

section RealMain

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx
  Formalism.IndefR.RecTie GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

end RealMain

section Spherical

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult
open GlobalTheory.Hk3 (SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

variable {D : D7} {V : HSp D} {n : ℕ}

def IsSphVec (Q : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n) (P : HeightOneSpectrum (𝓞 D.host.E))
    (x : Formalism.AUTREP.GAf D.host.E n → ℂ) : Prop :=
  x ∈ π.S ∧ ∀ κ, Q.ψ κ ∈ hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x

def ActsOnSph (Q : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (a : ℂ) : Prop :=
  ∀ B, SphOp V P d B → ∀ x, IsSphVec Q π P x → principalLevelFrame.Hecke₃ Q B x = a • x

open Classical in

def sphEig (Q : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) : ℂ :=
  if h : ∃ a, ActsOnSph Q π P d a then h.choose else 0

theorem actsOnSph_sphEig {hF : D.host.F = maximalRealSubfield D.host.E} {Q : principalLevelFrame.RowPsi V n} (hQ : StdPsi hF Q)
    (π : Formalism.L2.NG.FinTyp D.host.E n) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    ActsOnSph Q π P d (sphEig Q π P d) := by
  have h : ∃ a, ActsOnSph Q π P d a := by
    by_cases hB : ∃ B, SphOp V P d B
    · obtain ⟨B, hB⟩ := hB
      obtain ⟨a, ha⟩ := GlobalTheory.SphScalar.spherical_scalar hF Q hQ π P d B hB
      refine ⟨a, fun B' hB' x hx => ?_⟩
      rw [GlobalTheory.RowEig.heckeOperator_eq_of_spherical Q P d B' B hB' hB x hx.2]
      exact ha x hx.1 hx.2
    · exact ⟨0, fun B h => (hB ⟨B, h⟩).elim⟩
  unfold sphEig
  rw [dif_pos h]
  exact h.choose_spec

variable {Sp : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V Sp}
  {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}

theorem fixed_of_full {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {B : Finset (GA D V)}
    (hB : Hecke₂ V J χ Sb P d B) {U : MMap M} (hU : U ∈ Mult θ M J χ) :
    ∀ k ∈ hyp V P, postOn M (principalLevelFrame.rtA k) U = U := by
  intro k hk
  obtain ⟨e, f, ϖ, α, -, hP, -, -, -, hJ, hχ, -⟩ := hB
  rw [GlobalTheory.SphLabelOps.hyp_eq hP] at hk
  have h1 : k ∈ J := (hJ k hk.2).2 hk.1
  apply MultilinearMap.ext
  intro v
  funext g
  show U v (g * k) = U v g
  rw [principalLevelFrame.mult_lev hU v k h1 g, hχ k h1 hk.2, one_mul]

theorem isotL_le_partFull {hF : D.host.F = maximalRealSubfield D.host.E} {Q : principalLevelFrame.RowPsi V n} (hQ : StdPsi hF Q)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n) :
    principalLevelFrame.isotL θ Q M J χ e π ≤ partFull θ M J χ Sb (sphEig Q π) := by
  intro U hU
  have hM : U ∈ Mult θ M J χ := hU.1.1
  refine Submodule.mem_inf.2 ⟨hM, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  have hS := GlobalTheory.RowEig.sph_of_full hB
  exact GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF Q hQ θ M π P d B _ hS
    (fun x hx hf => actsOnSph_sphEig hQ π P d B hS x ⟨hx, hf⟩) U hU.2 (fixed_of_full hB hM)

theorem exists_sphVec {hF : D.host.F = maximalRealSubfield D.host.E} {Q : principalLevelFrame.RowPsi V n} (hQ : StdPsi hF Q)
    {e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} {π : Formalism.L2.NG.FinTyp D.host.E n} (h : principalLevelFrame.isotL θ Q M J χ e π ≠ ⊥)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {B : Finset (GA D V)} (hB : Hecke₂ V J χ Sb P d B) :
    ∃ x, IsSphVec Q π P x ∧ x ≠ 0 := by
  by_contra hn
  push_neg at hn
  obtain ⟨U, hU, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have key : ∀ a : ℂ, heckeOn M B U = a • U := fun a =>
    GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF Q hQ θ M π P d B a (GlobalTheory.RowEig.sph_of_full hB)
      (fun x hx hf => by rw [hn x ⟨hx, hf⟩, map_zero, smul_zero]) U hU.2 (fixed_of_full hB hU.1.1)
  exact h0 (by rw [← one_smul ℂ U, ← key 1, key 0, zero_smul])

theorem heckeOn_of_mem_partFull {c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ} {x : MMap M}
    (hx : x ∈ partFull θ M J χ Sb c) {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {B : Finset (GA D V)}
    (h : Hecke₂ V J χ Sb P d B) : heckeOn M B x = c P d • x := by
  have := (Submodule.mem_inf.1 hx).2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at this
  exact this P d B h

def diagLab (n k : ℕ) : List ℤ := List.replicate k 1 ++ List.replicate (n - k) 0

example : diagLab 3 1 = [1, 0, 0] := rfl

variable (V) in

def IsDiagOpAt (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (k : ℕ) (B : Finset (GA D V)) : Prop :=
  ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (α : GA D V),
    OffS D S P ∧ Formalism.L2.NTheta.IsIdemAt e P ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ k ≤ V.rank ∧
    (∀ g, SuppAt e V g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ J, SuppAt e V g → χ g = 1) ∧
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α ∧ (∀ γ ∈ B, SuppAt e V γ) ∧
    IsCosetRep V (locPart V J e) α B

theorem IsDiagOpAt.full {P : HeightOneSpectrum (𝓞 D.host.E)} {k : ℕ} {B : Finset (GA D V)}
    (h : IsDiagOpAt V J χ Sb P k B) : Hecke₂ V J χ Sb P (diagLab V.rank k) B := by
  obtain ⟨e, ϖ, α, hS, he, hϖ, hϖ2, hk, hJ, hχ, hα, hR, hC⟩ := h
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hD := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0
    (GlobalTheory.SplitHeckeLabel.divAt_inv V e P he ϖ hϖ hϖ2 k hk α hα)).1
  rw [inv_inv, show dualLab (splitLab V.rank k) = diagLab V.rank k by simp [dualLab, splitLab, diagLab]] at hD
  exact ⟨e, e + cA D e, ϖ, α, hS, Or.inl ⟨he, rfl⟩, hϖ, hϖ2,
    by simp [diagLab, List.pairwise_append, List.pairwise_replicate], hJ, hχ, hα.2.1, hD, hR, hC⟩

end Spherical

section RealHecke

open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx
  Formalism.IndefR.RecTie GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

def typeR (Y : Read (A3 := A3) R F X0) (σ : D.what₂.FT) : Formalism.L2.NG.FinTyp D.host.E D.R.r :=
  principalLevelFrame.rowRepR R.θ (Y.eFT σ)

def rowEig (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) (σ : D.what₂.FT) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) : ℂ :=
  sphEig (Y.PW i) (typeR Y σ) P d

theorem stdPsi_PW (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) : GlobalTheory.StdFrame.StdPsi Y.hF (Y.PW i) := Y.stdPsi.2 i

theorem partR_le_partFull (Y : Read (A3 := A3) R F X0) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (i : Fin D.R.m)
    (σ : D.what₂.FT) :
    partR Y i σ ≤ Mult.partFull R.θ (R.MW i (sg0 D A3.A)) (levW R F i) (chiW R F i) Sb (rowEig Y i σ) :=
  isotL_le_partFull (stdPsi_PW Y i) _ _

theorem readW_injective (Y : Read (A3 := A3) R F X0) (i : Fin D.R.m) : Function.Injective (readW Y i) := fun y y' h =>
  (Y.IL.jMj i).injective (Subtype.ext (by rw [← lift_readW, ← lift_readW, h]))

theorem partR_ne_bot (Y : Read (A3 := A3) R F X0) {i : Fin D.R.m} {σ : D.what₂.FT} (h : D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥) :
    partR Y i σ ≠ ⊥ := by
  obtain ⟨y, hy, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  intro e
  have := (mem_isot_iff Y i σ y).1 hy
  rw [e, Submodule.mem_bot] at this
  exact h0 (readW_injective Y i (this.trans (map_zero _).symm))

abbrev levTriv (R : RealDat D A3.A Ks) (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) :=
  levG (Wc D i) (R.βW i) (R.datWp i R.triv)

theorem rank_Wc (i : Fin D.R.m) : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2

theorem exists_local (hL : R.toLevCh.Is A3.A.μ0) (i : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : ∀ PP ∈ R.Pg, PP ≠ P ∧ ¬ Lev.IsConjPl PP P) {k : ℕ} (hk : k ≤ D.R.r) {α : GA D (Wc D i)}
    (hα : IsHeckeAt (Wc D i) P k α) :
    ∃ B, IsDiagOpAt (Wc D i) (levW R F i) (chiW R F i) ∅ P k B ∧ Bridge.IsDC (levTriv R i) α B := by
  obtain ⟨e, ϖ, he, h1, h2, hα⟩ := hα
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hp : Mult.IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have LS := fun Lv : LevelP R.Pg D.R.r ℂ => (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) _ (R.datWp i Lv) hβ).2 P e _ hp hN
    fun PP h => hP PP (h.elim id fun h => absurd h (Finset.notMem_empty _))
  obtain ⟨B, hB, hC⟩ := (GlobalTheory.SplitPlace.split_local (Wc D i) P e he).2.1 α hα.2.1
  have hset : ∀ Lv : LevelP R.Pg D.R.r ℂ, Mult.locPart (Wc D i) (levS _ (R.βW i) (R.datWp i Lv)) e =
      Mult.locPart (Wc D i) (KsphC (Wc D i) ∅) e := fun Lv => Set.ext fun g => and_congr_left fun hg => (LS Lv).1 g hg
  refine ⟨B, ⟨e, ϖ, α, GlobalTheory.LevOp.offS_empty, he, h1, h2, (rank_Wc i).symm ▸ hk, (LS _).1, (LS _).2.1, hα, hB,
    (hset _).symm ▸ hC⟩, ?_⟩
  obtain ⟨L, hLm⟩ := GlobalTheory.HeckeKeep.exists_loc (Wc D i) (e + cA D e)
  have hm : ∀ g, g ∈ levTriv R i ⊓ L ↔ g ∈ Mult.locPart (Wc D i) (KsphC (Wc D i) ∅) e := fun g => by
    rw [← hset R.triv]
    exact and_congr_right fun _ => hLm g
  refine GlobalTheory.HeckeParts.isDC_of_local ((hLm α).2 hα.2.1) (fun γ hγ => (hLm γ).2 (hB γ hγ)) (fun g hg => ?_)
    (fun γ hγ => ?_) fun y hy => ?_
  · obtain ⟨a, ha, b, hb, s₁, s₂, e'⟩ := (LS R.triv).2.2 g hg
    exact ⟨a, ha, b, hb, (hLm a).2 s₁, GlobalTheory.LevOp.comm_of_supp hp hα.2.1 s₂, e'⟩
  · simpa only [hm] using (hC.1 γ hγ).2
  · simpa only [hm] using hC.2 y (by simpa only [hm] using hy)

theorem inv_levTriv (i : Fin D.R.m) {U : Mult.MMap (R.MW i (sg0 D A3.A))}
    (hU : U ∈ Mult.Mult R.θ (R.MW i (sg0 D A3.A)) (levW R F i) (chiW R F i)) (v) :
    ∀ k ∈ levTriv R i, ∀ g, U v (g * k) = U v g := by
  intro k hk g
  obtain ⟨h1, h2⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) (R.levL F false (sg0 D A3.A)) k hk
  rw [principalLevelFrame.mult_lev hU v k h1 g]
  exact (congrArg (· * U v g) h2).trans (one_mul _)

theorem heckeOn_partR (Y : Read (A3 := A3) R F X0) (hL : R.toLevCh.Is A3.A.μ0) (i : Fin D.R.m)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : ∀ PP ∈ R.Pg, PP ≠ P ∧ ¬ Lev.IsConjPl PP P) {k : ℕ} (hk : k ≤ D.R.r)
    {α : GA D (Wc D i)} (hα : IsHeckeAt (Wc D i) P k α) {Rs : Finset (GA D (Wc D i))} (hR : Bridge.IsDC (levTriv R i) α Rs)
    (σ : D.what₂.FT) {z : Mult.MMap (R.MW i (sg0 D A3.A))} (hz : z ∈ partR Y i σ) :
    Mult.heckeOn (R.MW i (sg0 D A3.A)) Rs z = rowEig Y i σ P (diagLab D.R.r k) • z := by
  obtain ⟨B, hB, hD⟩ := exists_local (F := F) hL i hP hk hα
  have h := partR_le_partFull Y ∅ i σ hz
  have e := heckeOn_of_mem_partFull h hB.full
  rw [rank_Wc] at e
  rw [← e]
  exact MultilinearMap.ext fun v => funext fun g => GlobalTheory.HeckeParts.sum_eq_of_isDC hR hD (z v) (inv_levTriv i h.1 v) g

end RealHecke

end GlobalTheory.EigRows
