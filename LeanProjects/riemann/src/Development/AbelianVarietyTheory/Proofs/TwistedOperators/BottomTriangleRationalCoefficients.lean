import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitution
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMaximalCompactCharacterRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RealRatAct

def galFld (E : Type) [Field E] [NumberField E] : IntermediateField ℚ ℂ :=
  ⨆ σ : E →+* ℂ, (RingHom.toRatAlgHom σ).fieldRange

theorem galFld_fin (E : Type) [Field E] [NumberField E] : FiniteDimensional ℚ (galFld E) := by
  unfold galFld
  haveI : ∀ σ : E →+* ℂ, FiniteDimensional ℚ (RingHom.toRatAlgHom σ).fieldRange := fun σ =>
    (RingHom.toRatAlgHom σ).equivFieldRange.toLinearEquiv.finiteDimensional
  exact IntermediateField.finiteDimensional_iSup_of_finite

theorem mem_galFld {E : Type} [Field E] [NumberField E] (σ : E →+* ℂ) (x : E) : σ x ∈ galFld E :=
  (le_iSup (fun σ : E →+* ℂ => (RingHom.toRatAlgHom σ).fieldRange) σ) ⟨x, rfl⟩

theorem conj_mem_galFld {E : Type} [Field E] [NumberField E] {z : ℂ} (hz : z ∈ galFld E) :
    starRingEnd ℂ z ∈ galFld E := by
  have key : galFld E ≤ (galFld E).comap (starRingEnd ℂ : ℂ →+* ℂ).toRatAlgHom := by
    refine iSup_le fun σ => ?_
    rintro _ ⟨x, rfl⟩
    show starRingEnd ℂ (σ x) ∈ galFld E
    exact mem_galFld ((starRingEnd ℂ : ℂ →+* ℂ).comp σ) x
  exact key hz

theorem det_mem {K : IntermediateField ℚ ℂ} {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (h : ∀ i j, M i j ∈ K) : M.det ∈ K := by
  rw [Matrix.det_apply]
  refine K.sum_mem fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e]
  · rw [one_smul]; exact K.prod_mem fun i _ => h _ _
  · rw [Units.neg_smul, one_smul]; exact K.neg_mem (K.prod_mem fun i _ => h _ _)

variable {σ : Type}

def coefRing (K : IntermediateField ℚ ℂ) (σ : Type) : Subring (MvPolynomial σ ℂ) :=
  (MvPolynomial.map (K.val : K →+* ℂ)).range

theorem coeff_mem {K : IntermediateField ℚ ℂ} {P : MvPolynomial σ ℂ} (h : P ∈ coefRing K σ) (k : σ →₀ ℕ) :
    P.coeff k ∈ K := by
  obtain ⟨P', rfl⟩ := h
  rw [MvPolynomial.coeff_map]
  exact (P'.coeff k).2

theorem C_mem {K : IntermediateField ℚ ℂ} {c : ℂ} (h : c ∈ K) : MvPolynomial.C c ∈ coefRing K σ :=
  ⟨MvPolynomial.C ⟨c, h⟩, by rw [MvPolynomial.map_C]; rfl⟩

theorem X_mem (K : IntermediateField ℚ ℂ) (v : σ) : MvPolynomial.X v ∈ coefRing K σ :=
  ⟨MvPolynomial.X v, MvPolynomial.map_X _ _⟩

theorem monomial_mem (K : IntermediateField ℚ ℂ) (k : σ →₀ ℕ) : MvPolynomial.monomial k (1 : ℂ) ∈ coefRing K σ :=
  ⟨MvPolynomial.monomial k 1, by rw [MvPolynomial.map_monomial, map_one]⟩

theorem algHom_mem {K : IntermediateField ℚ ℂ} (φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hX : ∀ v, φ (MvPolynomial.X v) ∈ coefRing K σ) {P : MvPolynomial σ ℂ} (hP : P ∈ coefRing K σ) :
    φ P ∈ coefRing K σ := by
  obtain ⟨P', rfl⟩ := hP
  induction P' using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.map_C, MvPolynomial.algHom_C]; exact C_mem a.2
  | add p q hp hq => rw [map_add, map_add]; exact (coefRing K σ).add_mem hp hq
  | mul_X p v hp => rw [map_mul, map_mul, MvPolynomial.map_X]; exact (coefRing K σ).mul_mem hp (hX v)

end GlobalTheory.RealRatAct

namespace GlobalTheory.RealRatAct

open Formalism.L2.Theta

variable {D : D7}

theorem zpow_mem' {K : IntermediateField ℚ ℂ} {z : ℂ} (hz : z ∈ K) (n : ℤ) : z ^ n ∈ K := by
  exact K.pow_mem hz n

theorem compAt_of_GfC (θ : InfFam D) {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V g) = 1 := by
  have h1 : (infHom V g).1 = 1 := by
    rw [MonoidHom.mem_ker.1 hg]; rfl
  show infMat D.sp.cm.sig V.gram (θ τ) g = 1
  unfold infMat
  have e : ((HA.mat (AF D.host.F) D.sp.cm.sig V.gram g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) =
      (infHom V g).1 := rfl
  rw [e, h1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem compAt_mul (θ : InfFam D) {V : HSp D} (a b : GA D V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V (a * b)) = compAt θ τ (mt V a) * compAt θ τ (mt V b) :=
  GlobalTheory.PointAtPlaceHom.infMat_mul V (θ τ) a b

theorem compAt_one (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) : compAt θ τ (mt V 1) = 1 :=
  GlobalTheory.PointAtPlaceHom.infMat_one V (θ τ)

theorem compAt_inv (θ : InfFam D) {V : HSp D} (a : GA D V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V a⁻¹) = (compAt θ τ (mt V a))⁻¹ :=
  (Matrix.inv_eq_right_inv (GlobalTheory.OrientedHeis.compAt_mt_mul_inv τ a)).symm

end GlobalTheory.RealRatAct

namespace GlobalTheory.RealRatAct

open Formalism.L2.Theta

variable {D : D7}

theorem glue (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) :
    (∀ g : GA D V, (∀ ρ, compAt θ ρ (mt V g) = 1) → g ∈ GfC V) ∧
      ∀ γ ∈ GQ V, ∀ ρ i j, compAt θ ρ (mt V γ) i j ∈ galFld D.host.E := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  have hsurj : ∀ ρ, r ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩ = ρ := fun ρ => GlobalTheory.PointAtPlace.tauE_injective (hr _)
  obtain ⟨h1, h2, -, -⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact GlobalTheory.PointAtPlace.tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  refine ⟨fun g hg => h1 g fun σ => hg (r σ), fun γ hγ ρ i j => ?_⟩
  obtain ⟨γ₀, hγ₀, -⟩ := h2 γ hγ
  have e := hγ₀ ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩
  simp only [hsurj] at e
  show Formalism.L2.Pj.archM V (θ ρ) γ i j ∈ _
  rw [e, Matrix.map_apply]
  exact mem_galFld _ _

theorem compAt_mem (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {γ r : GA D V} (hγ : γ ∈ GQ V) (hr : γ * r ∈ GfC V)
    (ρ : D.what₂.Tau) (i j : Fin V.rank) : compAt θ ρ (mt V r) i j ∈ galFld D.host.E := by
  have e : r = γ⁻¹ * (γ * r) := by group
  rw [e, compAt_mul, compAt_of_GfC θ hr, Matrix.mul_one]
  exact (glue θ hθ V).2 _ ((GQ V).inv_mem hγ) ρ i j

end GlobalTheory.RealRatAct

namespace GlobalTheory.RealRatAct

open Formalism.L2.Theta

variable {D : D7}

theorem fockSub_mem {m n : ℕ} {K : IntermediateField ℚ ℂ} (hK : ∀ z ∈ K, starRingEnd ℂ z ∈ K) (τ : D.what₂.Tau)
    (pS pT : ℕ) {κS : Matrix (Fin n) (Fin n) ℂ} {κT : Matrix (Fin m) (Fin m) ℂ} (hS : ∀ i j, κS⁻¹ i j ∈ K)
    (hT : ∀ i j, κT i j ∈ K) {P : MvPolynomial (FVar D m n) ℂ} (hP : P ∈ coefRing K _) :
    fockSub τ pS pT κS κT P ∈ coefRing K _ := by
  have hs : ∀ g : Fin m → Fin n → ℂ, (∀ i j, g i j ∈ K) →
      ∑ i, ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X ((τ, i, j) : FVar D m n) ∈ coefRing K (FVar D m n) :=
    fun g hg => (coefRing K _).sum_mem fun i _ => (coefRing K _).sum_mem fun j _ =>
      (coefRing K _).mul_mem (C_mem (hg i j)) (X_mem K _)
  refine algHom_mem _ (fun y => ?_) hP
  unfold fockSub
  rw [MvPolynomial.aeval_X]
  by_cases h1 : y.1 = τ
  · rw [if_pos h1]
    exact hs _ fun i j => by
      split_ifs
      · exact K.mul_mem (hT _ _) (hS _ _)
      · exact hK _ (K.mul_mem (hT _ _) (hS _ _))
  · rw [if_neg h1]
    exact X_mem K _

theorem one_mem_entry {K : IntermediateField ℚ ℂ} {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) ℂ) i j ∈ K := by
  rw [Matrix.one_apply]
  split_ifs
  exacts [K.one_mem, K.zero_mem]

section Act

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem cart_neg {k : ℕ} : IsCartanInv (-1 : Matrix (Fin k) (Fin k) ℂ) (-1) :=
  ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

theorem cart_one {k : ℕ} : IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 :=
  ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

theorem onb_neg {k : ℕ} : IsONBasis (-1 : Matrix (Fin k) (Fin k) ℂ) (-1) 1 0 := by
  refine ⟨fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩ <;>
  · ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
      Matrix.neg_apply]
    split_ifs <;> simp

theorem onb_one {k : ℕ} : IsONBasis (1 : Matrix (Fin k) (Fin k) ℂ) 1 1 k := by
  refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩ <;>
  · ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem kmat_one {k : ℕ} : IsKMat 0 (1 : Matrix (Fin k) (Fin k) ℂ) :=
  ⟨one_mem _, fun i j h => absurd (by simp) h⟩

theorem kmat_of_UH {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ)) :
    IsKMat k M := by
  refine ⟨?_, fun i j h => absurd ⟨fun _ => j.2, fun _ => i.2⟩ h⟩
  have e : M.conjTranspose * 1 * M = 1 := hM
  rw [Matrix.mul_one] at e
  exact Matrix.mem_unitaryGroup_iff'.2 e

theorem isAtTau_one (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) : IsAtTau θ V τ 1 1 :=
  ⟨one_mem _, compAt_one θ V τ, fun ρ _ => compAt_one θ V ρ⟩

abbrev PT (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (f : WO S T → ℂ) :
    MvPolynomial (FVar D T.rank S.rank) ℂ →ₗ[ℂ] (WO S T → ℂ) :=
  pureTensorO ψ θ S T (fun _ => -1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f

variable (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (hgS : ∀ τ, gramAt D S τ = -1)
  (hgT : ∀ τ, gramAt D T τ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
  (hv : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (-1) 1) f) {K : IntermediateField ℚ ℂ}
  (hK : ∀ z ∈ K, starRingEnd ℂ z ∈ K)
include hW hθ hgS hgT hf hv

theorem step (τ : D.what₂.Tau) : ∀ M ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ), (∀ i j, M i j ∈ K) → ∀ h, IsAtTau θ T τ M h →
    ∃ c ∈ K, ∀ P, om (1, h) (PT ψ θ S T f P) = c • PT ψ θ S T f (fockSub τ 0 T.rank 1 M P) := by
  obtain ⟨mS, mT, hvc⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hW hθ τ
  intro M hM hMK h hh
  have hκ : IsKMat T.rank M := kmat_of_UH (by rw [← hgT τ]; exact hM)
  have hAS : IsAtTau θ S τ ((fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) τ * 1 *
      ((fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) τ)⁻¹) 1 := by
    simpa using isAtTau_one θ S τ
  have hAT : IsAtTau θ T τ ((fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ * M *
      ((fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ)⁻¹) h := by
    simpa using hh
  have cS : ∀ ρ, IsCartanInv (gramAt D S ρ) ((fun _ => (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) ρ) :=
    fun ρ => by rw [hgS]; exact cart_neg
  have cT : ∀ ρ, IsCartanInv (gramAt D T ρ) ((fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) ρ) :=
    fun ρ => by rw [hgT]; exact cart_one
  have oS : ∀ ρ, IsONBasis (gramAt D S ρ) ((fun _ => (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) ρ)
      ((fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) ρ) ((fun _ => 0) ρ) := fun ρ => by rw [hgS]; exact onb_neg
  have oT : ∀ ρ, IsONBasis (gramAt D T ρ) ((fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) ρ)
      ((fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) ρ) ((fun _ => T.rank) ρ) := fun ρ => by rw [hgT]; exact onb_one
  have hc := hvc _ _ _ _ _ _ (fun _ => Nat.zero_le _) (fun _ => le_rfl) cS cT oS oT f hf hv 1 M kmat_one hκ 1 h hAS hAT
  refine ⟨_, ?_, fun P => GlobalTheory.FockCompact.om_pureTensorO_compact D ψ θ S T χS χT om hW hθ _ _ _ _ _ _
    (fun _ => Nat.zero_le _) (fun _ => le_rfl) cS cT oS oT f hf τ 1 M kmat_one hκ 1 h hAS hAT _ hc P⟩
  have d1 : ∀ (p : ℕ) (N : Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ i j, N i j ∈ K) → detPos p N ∈ K ∧ detNeg p N ∈ K :=
    fun p N hN => ⟨det_mem fun i j => hN _ _, det_mem fun i j => hN _ _⟩
  have d2 : ∀ (p : ℕ), detPos p M ∈ K ∧ detNeg p M ∈ K :=
    fun p => ⟨det_mem fun i j => hMK _ _, det_mem fun i j => hMK _ _⟩
  obtain ⟨a1, a2⟩ := d1 0 1 one_mem_entry
  exact K.mul_mem (K.mul_mem (zpow_mem' a1 _) (zpow_mem' a2 _))
    (K.mul_mem (zpow_mem' (d2 _).1 _) (zpow_mem' (d2 _).2 _))

end Act

end GlobalTheory.RealRatAct

namespace GlobalTheory.RealRatAct

open Formalism.L2.Theta

variable {D : D7}

section Act

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (hgS : ∀ τ, gramAt D S τ = -1)
  (hgT : ∀ τ, gramAt D T τ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
  (hv : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (-1) 1) f) {K : IntermediateField ℚ ℂ}
  (hK : ∀ z ∈ K, starRingEnd ℂ z ∈ K)
include hW hθ hgS hgT hf hv hK

theorem act_fin (s : Finset D.what₂.Tau) : ∀ r ∈ GinfC T, (∀ ρ, ρ ∉ s → compAt θ ρ (mt T r) = 1) →
    (∀ ρ i j, compAt θ ρ (mt T r) i j ∈ K) → ∀ P ∈ coefRing K (FVar D T.rank S.rank),
    ∃ c ∈ K, ∃ Q ∈ coefRing K (FVar D T.rank S.rank), om (1, r) (PT ψ θ S T f P) = c • PT ψ θ S T f Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro r hr h1 _ P hP
    have e : r = 1 := GlobalTheory.PointAtPlace.eq_one_of_mem T r ((glue θ hθ T).1 r fun ρ => h1 ρ (Finset.notMem_empty ρ)) hr
    subst e
    refine ⟨1, K.one_mem, P, hP, ?_⟩
    rw [show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one, Module.End.one_apply, one_smul]
  | insert τ s hτ ih =>
    intro r hr h1 h2 P hP
    have hM : compAt θ τ (mt T r) ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ T r τ
    have hh := GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ hM
    have hdet : IsUnit (compAt θ τ (mt T r)).det := by
      have e : (compAt θ τ (mt T r)).conjTranspose * (gramAt D T τ) * compAt θ τ (mt T r) = gramAt D T τ := hM
      rw [hgT, Matrix.mul_one] at e
      exact Matrix.isUnit_det_of_left_inverse e
    set h := atTau θ T τ (compAt θ τ (mt T r)) with hdef
    have hA1 : compAt θ τ (mt T h) = compAt θ τ (mt T r) := hh.2.1
    have hA2 : ∀ ρ, ρ ≠ τ → compAt θ ρ (mt T h) = 1 := hh.2.2
    have cr : ∀ ρ, compAt θ ρ (mt T (h⁻¹ * r)) = if ρ = τ then 1 else compAt θ ρ (mt T r) := by
      intro ρ
      rw [compAt_mul, compAt_inv]
      split_ifs with e
      · rw [e, hA1]; exact Matrix.nonsing_inv_mul _ hdet
      · rw [hA2 ρ e, inv_one, Matrix.one_mul]
    obtain ⟨c', hc', Q', hQ', e'⟩ := ih (h⁻¹ * r) ((GinfC T).mul_mem ((GinfC T).inv_mem hh.1) hr)
      (fun ρ hρ => by
        rw [cr]
        split_ifs with e
        · rfl
        · exact h1 ρ (by simp [e, hρ]))
      (fun ρ i j => by
        rw [cr]
        split_ifs
        · exact one_mem_entry i j
        · exact h2 ρ i j) P hP
    obtain ⟨c, hc, hact⟩ := step hW hθ hgS hgT hf hv τ _ hM (h2 τ) h hh
    refine ⟨c' * c, K.mul_mem hc' hc, fockSub τ 0 T.rank 1 (compAt θ τ (mt T r)) Q',
      fockSub_mem hK τ 0 T.rank (fun i j => by rw [inv_one]; exact one_mem_entry i j) (h2 τ) hQ', ?_⟩
    have e : ((1 : GA D S), r) = (1, h) * (1, h⁻¹ * r) := by
      rw [Prod.mk_mul_mk, mul_one, mul_inv_cancel_left]
    rw [e, map_mul, Module.End.mul_apply, e', map_smul, hact, smul_smul]

end Act

end GlobalTheory.RealRatAct

namespace GlobalTheory.RealRatAct

open Formalism.L2.Theta

theorem real_translate : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ M₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ M₁ ∧ ∀ t, ∀ γ ∈ GQ WW, ∀ r ∈ GinfC WW, γ * r ∈ GfC WW → ∀ x k,
      ∃ c : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ, (∀ k', c k' ∈ M₁) ∧
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) = ∑ k' ∈ c.support, c k' * X.I W.ψ W.θ t (MvPolynomial.monomial k' 1) x := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX
  refine ⟨galFld D.host.E, galFld_fin _, fun t γ hγ r hr hγr x k => ?_⟩
  have h := hX.is
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have hWd := h.weil t
  have hgS : ∀ τ, gramAt D (GlobalTheory.Grid.neg A) τ = -1 := fun τ => by
    rw [gramAt, GlobalTheory.Grid.neg_gram, hX.std.1]
    ext a b
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hgT : ∀ τ, gramAt D WW τ = 1 := fun τ => by
    rw [gramAt, hX.stdW.1]; simp
  have hf := (GlobalTheory.ConstRatio.theta_f h t).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f t) := fun ρ => by
    have := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt h.isVac.1.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock ρ)
    simpa [(hX.std.2.2 ρ).1, (hX.stdW.2.2 ρ).1] using this
  obtain ⟨c, hc, Q, hQ, hact⟩ := act_fin hWd hθ hgS hgT hf hv (fun z hz => conj_mem_galFld hz) Finset.univ r hr
    (fun ρ hρ => absurd (Finset.mem_univ ρ) hρ) (compAt_mem W.θ hθ hγ hγr) _ (monomial_mem _ k)
  have hPT : ∀ P, pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P =
      PT W.ψ W.θ (GlobalTheory.Grid.neg A) WW (X.f t) P := fun P => by
    have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
      funext fun τ => by rw [(hX.std.2.2 τ).1]
    have e2 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have e3 : X.rA.B = fun _ => 1 := funext fun τ => (hX.std.2.2 τ).2
    have e4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
    rw [e1, e2, e3, e4]
  have e1r : (X.ω t) (1, r) = ((X.ω t).toSgn true) (1, r) := by
    show _ = (X.ω t) ((GlobalTheory.Grid.ofSgn true A).toMonoidHom 1, r)
    rw [map_one]
  have hQs : Q = ∑ k' ∈ Q.support, Q.coeff k' • MvPolynomial.monomial k' (1 : ℂ) := by
    have h1 := MvPolynomial.as_sum Q
    have h2 : ∑ v ∈ Q.support, MvPolynomial.monomial v (MvPolynomial.coeff v Q) =
        ∑ k' ∈ Q.support, Q.coeff k' • MvPolynomial.monomial k' (1 : ℂ) :=
      Finset.sum_congr rfl fun k' _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    exact h1.trans h2
  have hker : ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) g =
      ∑ k' ∈ Q.support, (c * Q.coeff k') * X.ker W.ψ W.θ t (MvPolynomial.monomial k' 1) x g := by
    intro g
    unfold Tri.ker thetaKO
    have e : (X.ω t) (g, x * r) = (X.ω t) (g, x) * (X.ω t) (1, r) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [hPT]
    rw [e, Module.End.mul_apply, e1r, hact]
    conv_lhs => rw [hQs]
    rw [map_sum, Finset.smul_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k' _ => ?_
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hint := (hX.integrable t).1
  classical
  let cc : (FVar D WW.rank A.rank →₀ ℕ) →₀ ℂ :=
    Finsupp.onFinset Q.support (fun k' => c * Q.coeff k') fun k' hk' => by
      by_contra hn
      exact hk' (by rw [MvPolynomial.notMem_support_iff.1 hn, mul_zero])
  have hcc : ∀ k', cc k' = c * Q.coeff k' := fun k' => Finsupp.onFinset_apply
  have hsub : cc.support ⊆ Q.support := Finsupp.support_onFinset_subset
  refine ⟨cc, fun k' => ?_, ?_⟩
  · rw [hcc]
    exact (galFld D.host.E).mul_mem hc (coeff_mem hQ k')
  · unfold Tri.I
    simp_rw [hker]
    rw [integral_finsetSum _ fun k' _ => (hint _ x).const_mul _]
    rw [← Finset.sum_subset hsub fun k' _ hk' => by
      rw [← hcc, Finsupp.notMem_support_iff.1 hk']; simp]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [integral_const_mul, hcc]

end GlobalTheory.RealRatAct
