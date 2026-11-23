import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerContractionOnePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDerivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.CompanionTheory.Pins

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {D : D7}

open Classical in

def PrIsoV {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) : Prop :=
  ∀ (ι : D.what₂.Tau → Type) [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (M.sm τ)) (w w' : c.W),
    inner ℂ w w' = ∑ f : (∀ τ, ι τ),
      starRingEnd ℂ (pr w (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) * pr w' (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))

def PrIsoF {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) : Prop :=
  (∀ τ, FiniteDimensional ℂ (M.sm τ)) ∧ PrIsoV M c pr

theorem PrIsoF.injective {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {c : CoefA V} {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}
    (h : PrIsoF M c pr) : Function.Injective pr := by
  haveI := h.1
  rw [injective_iff_map_eq_zero]
  intro w hw
  have e := h.2 _ (fun τ => stdOrthonormalBasis ℂ (M.sm τ)) w w
  rw [hw] at e
  simpa using e

theorem PrIsoF.ne_zero {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {c : CoefA V} [Nontrivial c.W]
    {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ} (h : PrIsoF M c pr) : pr ≠ 0 := by
  rintro rfl
  obtain ⟨w, hw⟩ := exists_ne (0 : c.W)
  exact hw (h.injective rfl)

def QHalfL {T : Type} (L : LevCh D T) : Prop :=
  ∀ t, ∀ PP ∈ L.Q t, ∀ PP' ∈ L.Q t, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def QGuardL {T : Type} (L : LevCh D T) : Prop :=
  QHalfL L ∧ ∀ t, ∀ PP ∈ L.Q t, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def QOffC {T : Type} (L : LevCh D T) : Prop :=
  ∀ t, ∀ PP ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

example {T : Type} (L : LevCh D T) (h : ∀ t, L.Q t = ∅) : QGuardL L :=
  ⟨fun t PP hP => absurd (h t ▸ hP) (Finset.notMem_empty _), fun t PP hP => absurd (h t ▸ hP) (Finset.notMem_empty _)⟩

def StdFrame (V : HSp D) : Prop :=
  (∀ a b, V.hT (V.frame a) (V.frame b) = if a = b then 1 else 0) ∧ V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)

structure SameDesign {T : Type} (L L' : LevCh D T) : Prop where
  C : L'.C = L.C
  xiH : L'.xiH = L.xiH
  mu0 : L'.mu0 = L.mu0
  eta : L'.eta = L.eta
  xi : L'.xi = L.xi
  Pg : L'.Pg = L.Pg
  chi : L'.chi = L.chi
  ΛY : L'.ΛY = L.ΛY
  βY : L'.βY = L.βY
  ΛW : L'.ΛW = L.ΛW
  βW : L'.βW = L.βW

theorem SameDesign.symm' {T : Type} {L L' : LevCh D T} (h : SameDesign L L') : SameDesign L' L :=
  ⟨h.C.symm, h.xiH.symm, h.mu0.symm, h.eta.symm, h.xi.symm, h.Pg.symm, h.chi.symm, h.ΛY.symm, h.βY.symm, h.ΛW.symm, h.βW.symm⟩

example {T : Type} (L : LevCh D T) (Q : T → Finset (Pl D.host.E)) (β : GL (Fin D.sp.X'.rank) (Lev.EAf D)) :
    SameDesign L { L with Q := Q, βX := β } := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def ConjLev {V : HSp D} (s : GA D V) (J : Set (GA D V)) (χ : GA D V → ℂ) (J' : Set (GA D V)) (χ' : GA D V → ℂ) : Prop :=
  ∀ k, (k ∈ J ↔ s⁻¹ * k * s ∈ J') ∧ (k ∈ J → χ' (s⁻¹ * k * s) = χ k)

section Fam

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)

def GrpPin (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (cG : G0 L.Pg D.R.r ≃* G0g D.nd) : Prop :=
  ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ L.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : L.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((eG.trans cG) g)) ∧
    (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧
    ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)

def LevelsAt (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (F : Face D A) : Prop :=
  ∃ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi L.Pg ψ0 ∧
    levPOf eG D.what₂.embLL (F.lvl false).P (F.lvl false).ψ = P0 L.Pg D.R.r ψ0 ∧
    ∃ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π ∧
      (∀ g, g ∈ (levPOf eG D.what₂.embLL (F.lvl true).P (F.lvl true).ψ).H ↔ reord π g ∈ (PsharpSym L.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧
      ∀ g hg hg', (levPOf eG D.what₂.embLL (F.lvl true).P (F.lvl true).ψ).chi ⟨g, hg⟩ =
        (PsharpSym L.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨reord π g, hg'⟩

structure LevPins (L : LevCh D T) (cf : Formalism.L2.Host.CharFrame D) (Pk : Finset (Pl D.host.E)) (eG0 : G ≃* G0g D.nd)
    (eG : G ≃* G0 L.Pg D.R.r) (cG : G0 L.Pg D.R.r ≃* G0g D.nd) : Prop where
  cfEq : L.C = cf
  qGuard : QGuardL L
  hF : D.host.F = maximalRealSubfield D.host.E
  grpRecPin : GrpPin A L eG cG
  fdiag : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)
  pgEq : L.Pg = Pk
  eGtie : eG0 = eG.trans cG
  betaStd : (∀ i, L.βV i = 1) ∧ L.βX = 1

variable {A}

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def scaleP (R : RealDat D A Ks) (u : Fin D.R.m → ℂ) : RealDat D A Ks :=
  { R with ioP := fun i => u i • R.ioP i, thF := fun i t => u i • R.thF i t, thG := fun i t => u i • R.thG i t }

def PhaseAt (R : RealDat D A Ks) (phs : Fin D.R.m → ℂ) : Prop :=
  ∀ i, ‖phs i‖ = 1 ∧ ((∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = c • R.thG i A.μ0 (R.jV i A.μ0 x)) →
    ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = cj (twAt D.what₂.embLL A.v0) (phs i) • R.thG i A.μ0 (R.jV i A.μ0 x))

structure RealPinsR (R : RealDat D A Ks) (phs : Fin D.R.m → ℂ) (cf : Formalism.L2.Host.CharFrame D) (Pk : Finset (Pl D.host.E))
    (eG0 : G ≃* G0g D.nd) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) : Prop where
  lev : LevPins A R.toLevCh cf Pk eG0 R.eG cG
  phsOne : ∀ i, phs i = 1
  prXunit : PrIsoV R.MX R.cX R.prX

structure RealPinsP (R : RealDat D A Ks) (phs : Fin D.R.m → ℂ) (cf : Formalism.L2.Host.CharFrame D) (Pk : Finset (Pl D.host.E))
    (eG0 : G ≃* G0g D.nd) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) : Prop extends RealPinsR R phs cf Pk eG0 cG where
  phase : PhaseAt R phs

theorem RealPinsP.rational {R : RealDat D A Ks} {phs : Fin D.R.m → ℂ} {cf : Formalism.L2.Host.CharFrame D} {Pk : Finset (Pl D.host.E)}
    {eG0 : G ≃* G0g D.nd} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : RealPinsP R phs cf Pk eG0 cG) (i : Fin D.R.m)
    (hc : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = c • R.thG i A.μ0 (R.jV i A.μ0 x)) :
    ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = R.thG i A.μ0 (R.jV i A.μ0 x) := by
  have aux : ∀ {Y H : Type} [AddCommGroup H] [Module ℂ H] (f : Y → H) (s : ℂ) (v : H), s = 1 → (∃ y, f y = s • v) → ∃ y, f y = v :=
    fun f s v hs h => by rwa [hs, one_smul] at h
  have e : cj (twAt D.what₂.embLL A.v0) (phs i) = 1 := (congrArg _ (h.phsOne i)).trans (map_one _)
  exact fun x => aux (fun y => (R.FW i).j (sg0 D A) y) _ _ e ((h.phase i).2 hc x)

end Fam

open Classical in

def LevPinsExist : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (F : Face D A)
    (L0 : LevCh D T) (Pk : Finset (Pl D.host.E)) (eG0 : G ≃* G0g D.nd),
    L0.Is A.μ0 → (∀ k v, L0.C.P.Div k (D.naut.plGw k v)) → (∀ i, StdFrame (Vc D i)) → StdFrame D.sp.X' →
    (∀ i, IsFDiag (Wc D i)) → QOffC L0 → GrpTie D A F.P0 F.ψ0 F.P1 F.ψ1 eG0 →
    (∀ PP, PP ∈ Pk ↔ ∃ k, PP ∈ Set.range (D.naut.plGw k)) →
    ∃ (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (cG : G0 L.Pg D.R.r ≃* G0g D.nd),
      L.Is A.μ0 ∧ SameDesign L0 L ∧ LevelsAt A L eG F ∧ LevPins A L L0.C Pk eG0 eG cG

open Classical in

def LevPinsExistQ : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (F : Face D A)
    (L0 : LevCh D T) (Pk : Finset (Pl D.host.E)) (eG0 : G ≃* G0g D.nd),
    L0.Is A.μ0 → (∀ k v, L0.C.P.Div k (D.naut.plGw k v)) → (∀ i, StdFrame (Vc D i)) → StdFrame D.sp.X' →
    (∀ i, IsFDiag (Wc D i)) → QOffC L0 → QHalfL L0 → GrpTie D A F.P0 F.ψ0 F.P1 F.ψ1 eG0 →
    (∀ PP, PP ∈ Pk ↔ ∃ k, PP ∈ Set.range (D.naut.plGw k)) →
    ∃ (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (cG : G0 L.Pg D.R.r ≃* G0g D.nd),
      L.Q = L0.Q ∧ L.Is A.μ0 ∧ SameDesign L0 L ∧ LevelsAt A L eG F ∧ LevPins A L L0.C Pk eG0 eG cG

end GlobalTheory.CompanionTheory.Pins

end

end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.CompanionTheory.Pins

namespace GlobalTheory.CompanionTheory.Pins

theorem isUnit_of_gram {n : ℕ} {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (h : gᴴ * G * g = G) : IsUnit g :=
  isUnit_of_mul_isUnit_right (h.symm ▸ hG : IsUnit (gᴴ * G * g))

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem gramAt_isUnit (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  rw [← M.fr_gram τ]
  exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul
    (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ)))).mul (M.fr_unit τ)

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  obtain ⟨u, rfl⟩ := isUnit_of_gram (gramAt_isUnit M τ) hg
  exact Submodule.subset_span
    (Formalism.IndefR.SchurOrthogonalityAlt.smoothVec_rep M τ ⟨u, hg⟩ (Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_of_mem hw))

end

end GlobalTheory.CompanionTheory.Pins

end

end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.CompanionTheory.Ipf.Aut.Adj

theorem multi_uniform {ι A : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (T : A → ContinuousMultilinearMap ℂ E ℂ)
    (h : ∀ x, ∃ c : ℝ, ∀ a, ‖T a x‖ ≤ c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖T a x‖ ≤ C * ∏ i, ‖x i‖ := by
  have key : ∀ s : Finset ι, ∀ x : ∀ i, E i, ∃ c : ℝ, ∀ a (y : ∀ i, E i), (∀ i, i ∉ s → y i = x i) →
      ‖T a y‖ ≤ c * ∏ i ∈ s, ‖y i‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x
      obtain ⟨c, hc⟩ := h x
      refine ⟨c, fun a y hy => ?_⟩
      have e : y = x := funext fun i => hy i (by simp)
      simpa [e] using hc a
    | insert j s hj ih =>
      intro x
      let I := {p : A × (∀ i, E i) // ∀ i, i ∉ insert j s → p.2 i = x i}
      let L : I → (E j →L[ℂ] ℂ) := fun p =>
        (((∏ i ∈ s, ‖p.1.2 i‖)⁻¹ : ℝ) : ℂ) • (T p.1.1).toContinuousLinearMap p.1.2 j
      have hL : ∀ p z, L p z = (((∏ i ∈ s, ‖p.1.2 i‖)⁻¹ : ℝ) : ℂ) * T p.1.1 (Function.update p.1.2 j z) := fun p z => by
        simp [L]
      have hb : ∀ z, ∃ C, ∀ p, ‖L p z‖ ≤ C := by
        intro z
        obtain ⟨c, hc⟩ := ih (Function.update x j z)
        refine ⟨|c|, fun p => ?_⟩
        have h1 := hc p.1.1 (Function.update p.1.2 j z) fun i hi => by
          by_cases e : i = j
          · subst e; simp
          · rw [Function.update_of_ne e, Function.update_of_ne e]
            exact p.2 i (by simp [e, hi])
        have h2 : ∏ i ∈ s, ‖Function.update p.1.2 j z i‖ = ∏ i ∈ s, ‖p.1.2 i‖ :=
          Finset.prod_congr rfl fun i hi => by
            rw [Function.update_of_ne (fun e : i = j => hj (e ▸ hi))]
        rw [h2] at h1
        set P := ∏ i ∈ s, ‖p.1.2 i‖ with hP
        have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
        rw [hL, ← hP, norm_mul, Complex.norm_real, norm_inv, Real.norm_of_nonneg hP0]
        rcases hP0.eq_or_lt with e | e
        · rw [← e]; simp
        · calc P⁻¹ * ‖T p.1.1 (Function.update p.1.2 j z)‖ ≤ P⁻¹ * (c * P) := by gcongr
            _ = c := by field_simp
            _ ≤ |c| := le_abs_self c
      obtain ⟨C, hC⟩ := banach_steinhaus hb
      refine ⟨|C|, fun a y hy => ?_⟩
      rw [Finset.prod_insert hj]
      set P := ∏ i ∈ s, ‖y i‖ with hP
      have hP0 : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
      rcases hP0.eq_or_lt with e | e
      · obtain ⟨i, hi, h0⟩ := Finset.prod_eq_zero_iff.1 (hP ▸ e.symm)
        rw [(T a).map_coord_zero i (norm_eq_zero.1 h0)]
        simp [← e]
      · let p : I := ⟨(a, y), hy⟩
        have h1 := (L p).le_opNorm (y j)
        have h2 : ‖L p (y j)‖ = P⁻¹ * ‖T a y‖ := by
          rw [hL]
          show ‖(((∏ i ∈ s, ‖y i‖)⁻¹ : ℝ) : ℂ) * T a (Function.update y j (y j))‖ = _
          rw [Function.update_eq_self, norm_mul, Complex.norm_real, norm_inv, ← hP, Real.norm_of_nonneg hP0]
        have h3 : ‖L p‖ * ‖y j‖ ≤ |C| * ‖y j‖ := by
          gcongr
          exact (hC p).trans (le_abs_self C)
        have h4 : P⁻¹ * ‖T a y‖ ≤ |C| * ‖y j‖ := h2 ▸ h1.trans h3
        calc ‖T a y‖ = P * (P⁻¹ * ‖T a y‖) := by field_simp
          _ ≤ P * (|C| * ‖y j‖) := by gcongr
          _ = |C| * (‖y j‖ * P) := by ring
  obtain ⟨c, hc⟩ := key Finset.univ 0
  refine ⟨|c|, abs_nonneg c, fun a x => ?_⟩
  refine (hc a x fun i hi => absurd (Finset.mem_univ i) hi).trans ?_
  gcongr
  exact le_abs_self c

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem exists_form (A : ⨂[ℂ] τ, M.H τ) : ∃ T : ContinuousMultilinearMap ℂ M.H ℂ,
    ∀ w, T w = starRingEnd ℂ (ellT M w A) := by
  induction A using PiTensorProduct.induction_on with
  | smul_tprod r z =>
    refine ⟨starRingEnd ℂ r • (ContinuousMultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compContinuousLinearMap
      fun τ => innerSL ℂ (z τ), fun w => ?_⟩
    rw [map_smul, GlobalTheory.Chain.RealIt.ellT_pure, smul_eq_mul, map_mul, map_prod]
    simp
  | add a b ha hb =>
    obtain ⟨T, hT⟩ := ha
    obtain ⟨T', hT'⟩ := hb
    exact ⟨T + T', fun w => by simp [hT, hT']⟩

theorem ellT_continuous (x : ⨂[ℂ] τ, M.H τ) : Continuous fun w : ∀ τ, M.H τ => ellT M w x := by
  obtain ⟨T, hT⟩ := exists_form M x
  have e : (fun w : ∀ τ, M.H τ => ellT M w x) = fun w => starRingEnd ℂ (T w) := by
    funext w
    rw [hT, Complex.conj_conj]
  rw [e]
  exact Complex.continuous_conj.comp T.cont

theorem forall_of_vec {C : Set (∀ τ, M.H τ)} (hC : IsClosed C) (h : ∀ u : M.Vec, (fun τ => (u τ : M.H τ)) ∈ C)
    (w : ∀ τ, M.H τ) : w ∈ C := by
  have hd : Dense (Set.pi Set.univ fun τ => (M.sm τ : Set (M.H τ))) :=
    dense_pi _ fun τ _ => Formalism.IndefR.SchurOrthogonalityAlt.sm_dense M τ
  refine (hC.closure_subset_iff.2 ?_) (hd w)
  intro y hy
  exact h fun τ => ⟨y τ, hy τ (Set.mem_univ τ)⟩

theorem tensor_ext {x y : ⨂[ℂ] τ, M.H τ} (h : ∀ u : M.Vec, ellT M (fun τ => u τ) x = ellT M (fun τ => u τ) y) :
    x = y := by
  refine sub_eq_zero.1 ((GlobalTheory.Chain.RealIt.tensorLaw D V S M).sep _ fun w => ?_)
  have hC : IsClosed {w | ellT M w x = ellT M w y} := isClosed_eq (ellT_continuous M _) (ellT_continuous M _)
  rw [map_sub, sub_eq_zero]
  exact forall_of_vec M hC h w

theorem sm_ext {x y : SmT M}
    (h : ∀ u : M.Vec, ellT M (fun τ => u τ) (inclT M x) = ellT M (fun τ => u τ) (inclT M y)) : x = y :=
  (GlobalTheory.Chain.RealIt.tensorLaw D V S M).inj (tensor_ext M h)

theorem incl_tprod (v : M.Vec) : inclT M (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => (v ρ : M.H ρ) := by
  rw [inclT, PiTensorProduct.map_tprod]
  rfl

variable {M} in
theorem rep_inner {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (a b : M.H τ) : ⟪M.rep τ g a, M.rep τ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (⟨(M.rep τ g : M.H τ →ₗ[ℂ] M.H τ), (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1.2.1 g hg⟩ : M.H τ →ₗᵢ[ℂ] M.H τ).inner_map_map a b

variable {M} in
theorem rep_cancel {τ : D.what₂.Tau} {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h : g * g' = 1) (a : M.H τ) : M.rep τ g (M.rep τ g' a) = a := by
  have hU := (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have e : M.rep τ (g * g') = (M.rep τ g).comp (M.rep τ g') := hU.1.2 g hg g' hg'
  rw [← ContinuousLinearMap.comp_apply, ← e, h, hU.1.1]
  rfl

include M in
theorem uh_inv (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ g * g⁻¹ = 1 := by
  have hu : IsUnit g := GlobalTheory.CompanionTheory.Pins.isUnit_of_gram (GlobalTheory.CompanionTheory.Pins.gramAt_isUnit M τ) hg
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  refine ⟨?_, Matrix.mul_nonsing_inv _ hd⟩
  show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
  calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gramAt D V τ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem smooth_facts (τ : D.what₂.Tau) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) {a : M.H τ}
    (ha : a ∈ M.sm τ) : dRep (M.rep τ) Y a ∈ M.sm τ ∧
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • Y)) a) (dRep (M.rep τ) Y a) 0 := by
  haveI := (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hsv := GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (GlobalTheory.SmoothAutCheck.gramAt_herm V τ)
    (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have h := (hsv.2 a (hsv.1 a ha)).2.1 Y hY
  exact ⟨Submodule.subset_span h.1, h.2⟩

def derS (τ : D.what₂.Tau) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) : M.sm τ →ₗ[ℂ] M.sm τ where
  toFun a := ⟨dRep (M.rep τ) Y a, (smooth_facts M τ hY a.2).1⟩
  map_add' a b := Subtype.ext <| by
    have h := (smooth_facts M τ hY a.2).2.add (smooth_facts M τ hY b.2).2
    refine (smooth_facts M τ hY (a + b).2).2.unique ?_
    have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • Y)) ((a + b : M.sm τ) : M.H τ)) =
        (fun t : ℝ => M.rep τ (NormedSpace.exp (t • Y)) (a : M.H τ)) +
          fun t : ℝ => M.rep τ (NormedSpace.exp (t • Y)) (b : M.H τ) := by
      funext t
      simp
    rw [e]
    exact h
  map_smul' c a := Subtype.ext <| by
    have h := (smooth_facts M τ hY a.2).2.const_smul c
    refine (smooth_facts M τ hY (c • a).2).2.unique ?_
    have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • Y)) ((c • a : M.sm τ) : M.H τ)) =
        c • fun t : ℝ => M.rep τ (NormedSpace.exp (t • Y)) (a : M.H τ) := by
      funext t
      simp
    rw [e]
    exact h

theorem derS_coe (τ : D.what₂.Tau) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) (a : M.sm τ) :
    (derS M τ hY a : M.H τ) = dRep (M.rep τ) Y a := rfl

def actS (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.sm τ →ₗ[ℂ] M.sm τ :=
  (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ).restrict fun w hw => GlobalTheory.CompanionTheory.Pins.rep_mem_sm M τ hg w hw

theorem actS_coe (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (a : M.sm τ) : (actS M τ hg a : M.H τ) = M.rep τ g a := rfl

section Slot

variable [DecidableEq D.what₂.Tau]

def intersection_update_fsHerm_neg_one (τ : D.what₂.Tau) (L : M.sm τ →ₗ[ℂ] M.sm τ) : SmT M →ₗ[ℂ] SmT M :=
  PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.sm ρ →ₗ[ℂ] M.sm ρ)) τ L)

theorem position_tprod (τ : D.what₂.Tau) (L : M.sm τ →ₗ[ℂ] M.sm τ) (v : M.Vec) :
    intersection_update_fsHerm_neg_one M τ L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (L (v τ))) := by
  rw [intersection_update_fsHerm_neg_one, PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases h : ρ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem coe_update (τ : D.what₂.Tau) (v : M.Vec) (y : M.sm τ) :
    (fun ρ => ((Function.update v τ y ρ : M.sm ρ) : M.H ρ)) =
      Function.update (fun ρ => (v ρ : M.H ρ)) τ (y : M.H τ) := by
  funext ρ
  by_cases h : ρ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem ell_act (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (w : ∀ ρ, M.H ρ) (A : ⨂[ℂ] ρ, M.H ρ) :
    ellT M (Function.update w τ (M.rep τ g (w τ))) (actT M τ g A) = ellT M w A := by
  induction A using PiTensorProduct.induction_on with
  | smul_tprod r z =>
    simp only [map_smul]
    rw [GlobalTheory.Chain.RealLine.Semi.actT_tprod, GlobalTheory.Chain.RealIt.ellT_pure, GlobalTheory.Chain.RealIt.ellT_pure]
    congr 1
    refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases h : ρ = τ
    · subst h; simp [rep_inner hg]
    · simp [Function.update_of_ne h]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem incl_act (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (x : SmT M) : inclT M (intersection_update_fsHerm_neg_one M τ (actS M τ hg) x) = actT M τ g (inclT M x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    rw [position_tprod, incl_tprod, incl_tprod, GlobalTheory.Chain.RealLine.Semi.actT_tprod, coe_update, actS_coe]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem der_mapFactor (τ : D.what₂.Tau) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) (x : SmT M) :
    DerT M τ Y x (intersection_update_fsHerm_neg_one M τ (derS M τ hY) x) := by
  intro w
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    refine HasDerivAt.const_smul c ?_
    rw [position_tprod, incl_tprod, incl_tprod, coe_update, derS_coe, GlobalTheory.Chain.RealLine.Semi.ellT_right]
    simp only [GlobalTheory.Chain.RealLine.Semi.actT_tprod, GlobalTheory.Chain.RealLine.Semi.ellT_right]
    refine HasDerivAt.mul_const ?_ _
    exact ((innerSL ℂ (w τ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (smooth_facts M τ hY (v τ).2).2
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

omit [DecidableEq D.what₂.Tau] in
theorem der_unique {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {x y y' : SmT M} (h : DerT M τ X x y)
    (h' : DerT M τ X x y') : y = y' := by
  refine (GlobalTheory.Chain.RealIt.tensorLaw D V S M).inj
    (sub_eq_zero.1 ((GlobalTheory.Chain.RealIt.tensorLaw D V S M).sep _ fun w => ?_))
  rw [map_sub, (h w).unique (h' w), sub_self]

theorem skew (τ : D.what₂.Tau) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) (u : ∀ ρ, M.H ρ)
    (hu : u τ ∈ M.sm τ) {x x' : SmT M} (h : DerT M τ Y x x') :
    ellT M u (inclT M x') = -ellT M (Function.update u τ (dRep (M.rep τ) Y (u τ))) (inclT M x) := by
  obtain ⟨c, hc, hg⟩ := GlobalTheory.Chain.RealLine.Semi.exists_ctr M τ u
  have hd := (smooth_facts M τ hY hu).2
  have e1 : ∀ z, ellT M (Function.update u τ (u τ)) z = ⟪u τ, c z⟫_ℂ := fun z => (hc _ z).symm
  have h1 := h (Function.update u τ (u τ))
  simp only [e1, hg] at h1
  have hgg : ∀ t : ℝ, NormedSpace.exp (t • Y) * NormedSpace.exp ((-t) • Y) = 1 := fun t => by
    rw [← Formalism.IndefR.SchurOrthogonalityAlt.gp_exp_split, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  have e : ∀ t : ℝ, ⟪u τ, M.rep τ (NormedSpace.exp (t • Y)) (c (inclT M x))⟫_ℂ =
      ⟪M.rep τ (NormedSpace.exp ((-t) • Y)) (u τ), c (inclT M x)⟫_ℂ := fun t => by
    have hm := Formalism.IndefR.SchurOrthogonalityAlt.gp_exp_mem τ hY t
    have hm' := Formalism.IndefR.SchurOrthogonalityAlt.gp_exp_mem τ hY (-t)
    rw [← rep_inner hm (M.rep τ _ (u τ)), rep_cancel hm hm' (hgg t)]
  simp only [e] at h1
  have h3 : HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp ((-t) • Y)) (u τ)) (-dRep (M.rep τ) Y (u τ)) 0 := by
    have hd0 : HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • Y)) (u τ)) (dRep (M.rep τ) Y (u τ)) (-(0 : ℝ)) := by
      simpa using hd
    have := hd0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  have h4 := HasDerivAt.inner ℂ h3 (hasDerivAt_const (0 : ℝ) (c (inclT M x)))
  have h5 := h1.unique h4
  have e2 : ellT M u (inclT M x') = ⟪u τ, c (inclT M x')⟫_ℂ := by rw [← e1, Function.update_eq_self]
  rw [e2, ← hc, h5]
  simp [inner_neg_left]

end Slot

end Model

section Main

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'} {Z P : Type}
  [AddCommGroup P] [Module ℂ P] {θ : InfFam D} {ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)}
  {ω' : GA D W × GA D V →* Module.End ℂ (Z → ℂ)} {pt : P → Z → ℂ} {It : P →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M'}
  {Tp : P → SmT M' →ₗ[ℂ] SmT M}

def AdjRel (It : P →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M') (Tp : P → SmT M' →ₗ[ℂ] SmT M) : Prop :=
  ∀ (p : P) (u : M.Vec) (w : M'.Vec), ellT M (fun τ => u τ) (inclT M (Tp p (PiTensorProduct.tprod ℂ w))) =
    starRingEnd ℂ (ellT M' (fun τ => w τ) (inclT M' (It p (PiTensorProduct.tprod ℂ u))))

theorem clause_ne (hI : GlobalTheory.Grid.IsIntw θ M' M ω' pt It) (hA : AdjRel It Tp) : ∃ φ, Tp φ ≠ 0 := by
  have h1 : ∃ p, It p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hI.ne (LinearMap.ext h)
  obtain ⟨p, hp⟩ := h1
  have h2 : ∃ u : M.Vec, It p (PiTensorProduct.tprod ℂ u) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hp (PiTensorProduct.ext (MultilinearMap.ext fun u => by simpa using h u))
  obtain ⟨u, hu⟩ := h2
  have h3 : ∃ w : M'.Vec, ellT M' (fun τ => w τ) (inclT M' (It p (PiTensorProduct.tprod ℂ u))) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (sm_ext M' fun w => by simpa using h w)
  obtain ⟨w, hw⟩ := h3
  refine ⟨p, fun h0 => hw ?_⟩
  have h4 := hA p u w
  rw [h0] at h4
  have h5 : starRingEnd ℂ (ellT M' (fun τ => w τ) (inclT M' (It p (PiTensorProduct.tprod ℂ u)))) = 0 := by
    rw [← h4]
    simp
  exact (map_eq_zero _).1 h5

theorem clause_bdd (hI : GlobalTheory.Grid.IsIntw θ M' M ω' pt It) (hA : AdjRel It Tp) (φ : P) (w : ∀ τ, M.H τ) :
    ∃ c : ℝ, ∀ v : M'.Vec, ‖ellT M w (inclT M (Tp φ (PiTensorProduct.tprod ℂ v)))‖ ≤ c * ∏ τ, ‖(v τ : M'.H τ)‖ := by
  classical
  choose T hT using fun u : M.Vec => exists_form M' (inclT M' (It φ (PiTensorProduct.tprod ℂ u)))
  have hN0 : ∀ u : M.Vec, 0 ≤ ∏ ρ, ‖(u ρ : M.H ρ)‖ := fun u => Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hb : ∀ x : ∀ τ, M'.H τ, ∃ c : ℝ, ∀ u : M.Vec,
      ‖((((∏ ρ, ‖(u ρ : M.H ρ)‖)⁻¹ : ℝ) : ℂ) • T u) x‖ ≤ c := by
    intro x
    obtain ⟨c, hc⟩ := hI.bdd φ x
    refine ⟨|c|, fun u => ?_⟩
    have h1 := hc u
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, norm_inv, hT, RCLike.norm_conj,
      Real.norm_of_nonneg (hN0 u)]
    rcases (hN0 u).eq_or_lt with e | e
    · rw [← e]; simp
    · calc _ ≤ (∏ ρ, ‖(u ρ : M.H ρ)‖)⁻¹ * (c * ∏ ρ, ‖(u ρ : M.H ρ)‖) := by gcongr
        _ = c := by field_simp
        _ ≤ |c| := le_abs_self c
  haveI : ∀ τ, CompleteSpace (M'.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D W S' M' τ).1
  obtain ⟨C, hC0, hC⟩ := multi_uniform _ hb
  have hb2 : ∀ (u : M.Vec) (v : M'.Vec), ‖ellT M (fun τ => u τ) (inclT M (Tp φ (PiTensorProduct.tprod ℂ v)))‖ ≤
      (C * ∏ τ, ‖(v τ : M'.H τ)‖) * ∏ τ, ‖(u τ : M.H τ)‖ := by
    intro u v
    rw [hA, RCLike.norm_conj]
    have hv0 : 0 ≤ ∏ τ, ‖(v τ : M'.H τ)‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    rcases (hN0 u).eq_or_lt with e | e
    · obtain ⟨i, -, h0⟩ := Finset.prod_eq_zero_iff.1 e.symm
      have hu : u i = 0 := Subtype.ext (norm_eq_zero.1 h0)
      rw [(PiTensorProduct.tprod ℂ).map_coord_zero i hu]
      simp only [map_zero, norm_zero]
      positivity
    · have h1 := hC u fun τ => (v τ : M'.H τ)
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, norm_inv, hT, RCLike.norm_conj,
        Real.norm_of_nonneg (hN0 u)] at h1
      set N := ∏ ρ, ‖(u ρ : M.H ρ)‖
      calc _ = N * (N⁻¹ * ‖ellT M' (fun τ => v τ) (inclT M' (It φ (PiTensorProduct.tprod ℂ u)))‖) := by field_simp
        _ ≤ N * (C * ∏ τ, ‖(v τ : M'.H τ)‖) := by gcongr
        _ = _ := by ring
  refine ⟨C * ∏ τ, ‖w τ‖, fun v => ?_⟩
  have hcl : IsClosed {x : ∀ τ, M.H τ | ‖ellT M x (inclT M (Tp φ (PiTensorProduct.tprod ℂ v)))‖ ≤
      (C * ∏ τ, ‖(v τ : M'.H τ)‖) * ∏ τ, ‖x τ‖} :=
    isClosed_le (ellT_continuous M _).norm
      (continuous_const.mul (continuous_finset_prod _ fun τ _ => (continuous_apply τ).norm))
  have h1 : ‖ellT M w (inclT M (Tp φ (PiTensorProduct.tprod ℂ v)))‖ ≤ (C * ∏ τ, ‖(v τ : M'.H τ)‖) * ∏ τ, ‖w τ‖ :=
    forall_of_vec M hcl (fun u => hb2 u v) w
  calc _ ≤ _ := h1
    _ = _ := by ring

variable [DecidableEq D.what₂.Tau]

theorem act_cancel (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h : g * g' = 1) (u : M.Vec) :
    Function.update (fun ρ => ((Function.update u τ (actS M τ hg' (u τ)) ρ : M.sm ρ) : M.H ρ)) τ
      (M.rep τ g ((Function.update u τ (actS M τ hg' (u τ)) τ : M.sm τ) : M.H τ)) = fun ρ => (u ρ : M.H ρ) := by
  funext ρ
  by_cases e : ρ = τ
  · subst e
    simp [actS_coe, rep_cancel hg hg' h]
  · simp [Function.update_of_ne e]

theorem clause_eqK (hω : ∀ g h, ω' (h, g) = ω (g, h)) (hI : GlobalTheory.Grid.IsIntw θ M' M ω' pt It) (hA : AdjRel It Tp)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (φ φ' : P)
    (hp : pt φ' = ω (atTau θ V τ g, 1) (pt φ)) (y : SmT M') :
    inclT M (Tp φ' y) = actT M τ g (inclT M (Tp φ y)) := by
  obtain ⟨hgi, hgg⟩ := uh_inv M τ hg
  have hp' : pt φ' = ω' (1, atTau θ V τ g) (pt φ) := by rw [hω]; exact hp
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul]
    congr 1
    refine tensor_ext M fun u => ?_
    have e := act_cancel τ hg hgi hgg u
    have hact : inclT M (PiTensorProduct.tprod ℂ u) =
        actT M τ g (inclT M (PiTensorProduct.tprod ℂ (Function.update u τ (actS M τ hgi (u τ))))) := by
      rw [incl_tprod, incl_tprod, GlobalTheory.Chain.RealLine.Semi.actT_tprod, e]
    have hI1 := hI.invK τ g hg φ φ' _ _ hp' hact
    have h2 := ell_act M τ hg (fun ρ => ((Function.update u τ (actS M τ hgi (u τ)) ρ : M.sm ρ) : M.H ρ))
      (inclT M (Tp φ (PiTensorProduct.tprod ℂ w)))
    rw [e] at h2
    rw [h2, hA, hA, hI1]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem clause_invK (hω : ∀ g h, ω' (h, g) = ω (g, h)) (hI : GlobalTheory.Grid.IsIntw θ M' M ω' pt It) (hA : AdjRel It Tp)
    (τ : D.what₂.Tau) (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) (φ φ' : P)
    (v v' : SmT M') (hp : pt φ' = ω (1, atTau θ W τ h) (pt φ)) (hv : inclT M' v' = actT M' τ h (inclT M' v)) :
    Tp φ' v' = Tp φ v := by
  have hp' : pt φ' = ω' (atTau θ W τ h, 1) (pt φ) := by rw [hω]; exact hp
  have e : v' = intersection_update_fsHerm_neg_one M' τ (actS M' τ hh) v :=
    (GlobalTheory.Chain.RealIt.tensorLaw D W S' M').inj (hv.trans (incl_act M' τ hh v).symm)
  subst e
  clear hv
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul]
    congr 1
    rw [position_tprod]
    refine sm_ext M fun u => ?_
    rw [hA, hA, hI.eqK τ h hh φ φ' hp' (PiTensorProduct.tprod ℂ u), coe_update, actS_coe]
    exact congrArg _ (ell_act M' τ hh _ _)
  | add a b ha hb => simp only [map_add, ha, hb]

theorem clause_eqg (hω : ∀ g h, ω' (h, g) = ω (g, h)) (hI : GlobalTheory.Grid.IsIntw θ M' M ω' pt It) (hA : AdjRel It Tp)
    (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hY : Y ∈ lieAt V τ) (φ φ' : P)
    (hd : ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ Y t, 1) (pt φ) z) (pt φ' z) 0) (y : SmT M') :
    DerT M τ Y (Tp φ y) (Tp φ' y) := by
  have hd' : ∀ z, HasDerivAt (fun t : ℝ => ω' (1, oneP θ V τ Y t) (pt φ) z) (pt φ' z) 0 := fun z => by
    simpa only [hω] using hd z
  suffices e : intersection_update_fsHerm_neg_one M τ (derS M τ hY) (Tp φ y) = Tp φ' y by
    rw [← e]
    exact der_mapFactor M τ hY _
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul]
    congr 1
    refine sm_ext M fun u => ?_
    rw [skew M τ hY _ (u τ).2 (der_mapFactor M τ hY _)]
    have hder := der_mapFactor M τ hY (PiTensorProduct.tprod ℂ u)
    rw [position_tprod] at hder
    have hinv := hI.invg τ Y hY φ φ' _ _ hd' hder
    have e := coe_update M τ u (derS M τ hY (u τ))
    rw [derS_coe] at e
    rw [← e, hA, hA, eq_neg_of_add_eq_zero_left hinv]
    simp only [map_neg]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem clause_invg (hω : ∀ g h, ω' (h, g) = ω (g, h)) (hI : GlobalTheory.Grid.IsIntw θ M' M ω' pt It) (hA : AdjRel It Tp)
    (τ : D.what₂.Tau) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hY : Y ∈ lieAt W τ) (φ φ' : P) (v v' : SmT M')
    (hd : ∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (pt φ) z) (pt φ' z) 0) (hv : DerT M' τ Y v v') :
    Tp φ' v + Tp φ v' = 0 := by
  have hd' : ∀ z, HasDerivAt (fun t : ℝ => ω' (oneP θ W τ Y t, 1) (pt φ) z) (pt φ' z) 0 := fun z => by
    simpa only [hω] using hd z
  have e : v' = intersection_update_fsHerm_neg_one M' τ (derS M' τ hY) v := der_unique M' hv (der_mapFactor M' τ hY v)
  subst e
  clear hv
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    have key : Tp φ' (PiTensorProduct.tprod ℂ w) + Tp φ (intersection_update_fsHerm_neg_one M' τ (derS M' τ hY) (PiTensorProduct.tprod ℂ w)) = 0 := by
      refine sm_ext M fun u => ?_
      have hs := skew M' τ hY (fun ρ => (w ρ : M'.H ρ)) (w τ).2 (hI.eqg τ Y hY φ φ' hd' (PiTensorProduct.tprod ℂ u))
      have e := coe_update M' τ w (derS M' τ hY (w τ))
      rw [derS_coe] at e
      rw [map_add, map_add, map_zero, map_zero, position_tprod, hA, hA, hs, e]
      simp
    simp only [map_smul]
    rw [← smul_add, key, smul_zero]
  | add a b ha hb =>
    simp only [map_add]
    rw [add_add_add_comm, ha, hb, add_zero]

end Main

theorem isIntwF_adjoint : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (Z P : Type) [AddCommGroup P] [Module ℂ P] (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (ω' : GA D W × GA D V →* Module.End ℂ (Z → ℂ)) (pt : P → Z → ℂ) (It : P →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M') (Tp : P → SmT M' →ₗ[ℂ] SmT M), (∀ g h, ω' (h, g) = ω (g, h)) → GlobalTheory.Grid.IsIntw θ M' M ω' pt It → (∀ (p : P) (v : M.Vec) (w : M'.Vec), ellT M' (fun τ => w τ) (inclT M' (It p (PiTensorProduct.tprod ℂ v))) = starRingEnd ℂ (ellT M (fun τ => v τ) (inclT M (Tp p (PiTensorProduct.tprod ℂ w))))) → IsIntwF θ M M' ω pt Tp := by
  classical
  intro D V W S S' M M' Z P _ _ θ ω ω' pt It Tp hω hI hadj
  have hA : AdjRel It Tp := fun p u w => by rw [hadj, Complex.conj_conj]
  exact ⟨clause_ne hI hA, clause_bdd hI hA, fun τ g hg φ φ' hp y => clause_eqK hω hI hA τ g hg φ φ' hp y,
    fun τ Y hY φ φ' hd y => clause_eqg hω hI hA τ Y hY φ φ' hd y,
    fun τ h hh φ φ' v v' hp hv => clause_invK hω hI hA τ h hh φ φ' v v' hp hv,
    fun τ Y hY φ φ' v v' hd hv => clause_invg hω hI hA τ Y hY φ φ' v v' hd hv⟩

end GlobalTheory.CompanionTheory.Ipf.Aut.Adj

end

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
theorem _root_.GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (Z P : Type) [AddCommGroup P] [Module ℂ P] (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (ω' : GA D W × GA D V →* Module.End ℂ (Z → ℂ)) (pt : P → Z → ℂ) (It : P →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M') (Tp : P → SmT M' →ₗ[ℂ] SmT M), (∀ g h, ω' (h, g) = ω (g, h)) → GlobalTheory.Grid.IsIntw θ M' M ω' pt It → (∀ (p : P) (v : M.Vec) (w : M'.Vec), ellT M' (fun τ => w τ) (inclT M' (It p (PiTensorProduct.tprod ℂ v))) = starRingEnd ℂ (ellT M (fun τ => v τ) (inclT M (Tp p (PiTensorProduct.tprod ℂ w))))) → IsIntwF θ M M' ω pt Tp := by
  first | exact @GlobalTheory.CompanionTheory.Ipf.Aut.Adj.isIntwF_adjoint | exact GlobalTheory.CompanionTheory.Ipf.Aut.Adj.isIntwF_adjoint | (intros; apply GlobalTheory.CompanionTheory.Ipf.Aut.Adj.isIntwF_adjoint <;> assumption)

end
