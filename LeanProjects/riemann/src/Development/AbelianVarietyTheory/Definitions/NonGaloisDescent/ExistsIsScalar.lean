import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmQAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjConj
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)

structure RealPin (ρ : Setup D.ntw) : Prop where
  psi : ∀ i j b, (ρ.B i j b).F.ψ = Rl.ψ
  inf : ∀ i j b, (ρ.B i j b).F.θ = Rl.θ
  cartT : ∀ i j b, (ρ.B i j b).F.sT = cart (Rl.MW j (sg0 D A3.A))
  onbS : ∀ i j b τ, ((ρ.B i j b).F.BS τ).val = Rl.BV j τ
  onbT : ∀ i j b, (ρ.B i j b).F.BT = onb (Rl.MW j (sg0 D A3.A))
  latS : ∀ i j b, (ρ.B i j b).F.ΛS = Rl.ΛV j
  latT : ∀ i j b, (ρ.B i j b).F.ΛT = Rl.ΛW j
  frS : ∀ i j b, (ρ.B i j b).F.βS = Rl.βV j
  frT : ∀ i j b, (ρ.B i j b).F.βT = Rl.βW j
  vac : ∀ i j b, (ρ.B i j b).F.f₀ = Rl.vacP j
  Pg : ∀ i j b, (ρ.B i j b).G.Pg = Rl.Pg
  grp : ∀ i j b (g : G0g D.nd) (P : Pl D.host.E) (h : P ∈ (ρ.B i j b).G.Pg) (h' : P ∈ Rl.Pg) (a c : Fin (Wc D j).rank),
    (ρ.eG i j b g ⟨P, h⟩).val a c = (cG.symm g ⟨P, h'⟩).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c)
  mu0 : ∀ i j b, (ρ.B i j b).mu0 = Rl.mu0 ((j : ℕ) + 1)
  eta : ∀ i j b, (ρ.B i j b).eta = Rl.eta
  delta : ∀ i j b, ChrEq (ρ.B i j b).de.chi (Rl.C.delAt (D.ntw.l i))
  deltaPl : ∀ i t, ∀ P ∈ Rl.Q t, P ∈ D.ntw.pD i → P ∈ ρ.ch i
  ap : ∀ i j b τ, (ρ.B i j b).w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ
  am : ∀ i j b τ, (ρ.B i j b).w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ

variable {Rl cG} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

def evW (j : Fin D.R.m) : S.WL ((j : ℕ) + 1) →+ (GA D (Wc D j) → ℂ) where
  toFun x := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x)) (v₀ j _)
  map_zero' := by rw [map_zero, map_zero, map_zero]; rfl
  map_add' x y := by rw [map_add, map_add, map_add]; rfl

theorem evW_smul (j : Fin D.R.m) (c : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (c • x) = D.what₂.embLL c • evW YS v₀ j x := by
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x))) (v₀ j _) = _
  rw [map_smul, map_smulₛₗ, map_smul, show sg0 D A3.A c = D.what₂.embLL c from
    congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]
  rfl

section Read

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

def evK : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1) →+ (GA D (Wc D j) → ℂ) :=
  TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.e i b a)).comp
        ((evW YS v₀ j).comp (S.A ((j : ℕ) + 1)).WK.subtype.toAddMonoidHom)
      map_zero' := by ext; simp [show ρ.e i b (0 : NX.KB S i b) = 0 from map_zero _]
      map_add' := fun x y => by ext; simp [show ρ.e i b (x + y : NX.KB S i b) = ρ.e i b x + ρ.e i b y from map_add _ _ _, add_mul] }
    fun c a f => by
      change ρ.e i b (sideEmb D.ntw i b (S.kKs c) * (show FractionRing (D.ntw.O i) from a)) • evW YS v₀ j (Subtype.val f) =
        ρ.e i b a • evW YS v₀ j (c • Subtype.val f)
      rw [← algebraMap_smul D.what₂.LL c, evW_smul, map_mul, hρ.e_LL0, smul_smul, mul_comm, ← S.kKs_spec]
      rfl

theorem evK_tmul (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (a ⊗ₜ f) = ρ.e i b a • evW YS v₀ j (Subtype.val f) := rfl

def realRd (ν : ℂ) : Rd ρ D.nexp i j b where
  toFun f := ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  map_add' f f' := by
    rw [map_add, ← smul_add]
    exact congrArg _ ((evK YS v₀ hρ i j b).map_add _ _)
  map_smul' c f := by
    rw [map_smul, smul_comm]
    congr 1
    generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 f = x
    have key : ∀ (c : NX.KB S i b) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)),
        evK YS v₀ hρ i j b (c • x) = ρ.e i b c • evK YS v₀ hρ i j b x := fun c x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        rw [TensorProduct.smul_tmul', evK_tmul, evK_tmul, smul_smul]
        exact congrArg (· • _) (map_mul (ρ.e i b) c a)
    exact key c x

theorem realRd_tmul (ν : ℂ) (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    realRd YS v₀ hρ i j b ν ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] f : NX.KB S i b ⊗[S.Ks] _)) =
      (ν⁻¹ * ρ.e i b a) • evW YS v₀ j (Subtype.val f) := by
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b _ j.2 ((YS.eF i _ b _ j.2).symm _)) = _
  rw [mul_smul]
  exact congrArg (fun x => ν⁻¹ • evK YS v₀ hρ i j b x) ((YS.eF i _ b (Nat.le_add_left _ _) j.2).apply_symm_apply _)

theorem realRd_apply (ν : ℂ) (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    realRd YS v₀ hρ i j b ν f = ν⁻¹ • realRd YS v₀ hρ i j b 1 f := by
  change _ = ν⁻¹ • (1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  rw [inv_one, one_smul]
  rfl

end Read

variable (Rl) in

def IsScale {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (c : ℂ) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
      ∀ F : VV D.what₂.LL (FWT.lamV D j),
        harmFn (Wc D j).rank B.w B.F.BS (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) =
          c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)

variable (Rl) in

def IsNorm {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) : Prop :=
  ν ≠ 0 ∧ ∃ c, IsScale Rl v₀ B c ∧ ∃ n : ℕ, n ≠ 0 ∧ ν ^ n = (cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c) ^ n

theorem heckeAt_realRd {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ} (hν : ν ≠ 0) (k P f g) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g ↔ HeckeAt (realRd YS v₀ hρ i j b 1) k P f g := by
  refine forall₃_congr fun α R z => imp_congr_right fun _ => ?_
  rw [realRd_apply YS v₀ hρ i j b ν, realRd_apply YS v₀ hρ i j b ν f, map_smul]
  exact (smul_right_injective _ (inv_ne_zero hν)).eq_iff

def RatRow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) : Prop :=
  ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ Rat hρ (realRd YS v₀ hρ i j b ν)

structure IsScalar {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) : Prop where
  ne : ν ≠ 0
  norm : (∃ ν', IsNorm Rl v₀ (ρ.B i j b) ν') → IsNorm Rl v₀ (ρ.B i j b) ν
  rat : RatRow YS v₀ hρ i j b → Rat hρ (realRd YS v₀ hρ i j b ν)

theorem exists_isScalar {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    ∃ ν, IsScalar YS v₀ hρ i j b ν := by
  by_cases h : RatRow YS v₀ hρ i j b
  · obtain ⟨ν, h1, h2⟩ := h
    exact ⟨ν, h1.1, fun _ => h1, fun _ => h2⟩
  · by_cases h' : ∃ ν', IsNorm Rl v₀ (ρ.B i j b) ν'
    · obtain ⟨ν, h1⟩ := h'
      exact ⟨ν, h1.1, fun _ => h1, fun h2 => absurd h2 h⟩
    · exact ⟨1, one_ne_zero, fun h1 => absurd h1 h', fun h2 => absurd h2 h⟩

structure ExportTie : Type 1 where

  ρ : Setup D.ntw
  good : ρ.Good
  pin : RealPin Rl cG ρ

  vec : ∀ j, FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)

  ν : D.ntw.Tw → Fin D.R.m → Bool → ℂ
  scalar : ∀ i j b, IsScalar YS v₀ good i j b (ν i j b)

  tie : Comparison₂ good (Y := D.nexp) fun i j b => realRd YS v₀ good i j b (ν i j b)

  hecke : ∀ i j b, HeckeTie (realRd YS v₀ good i j b (ν i j b))

  univ : GlobalTheory.UnivChar.IsUnivChar D.nexp

namespace ExportTie

variable {YS v₀} (Z : ExportTie YS v₀)

abbrev rd : Rds D.nexp Z.ρ := fun i j b => realRd YS v₀ Z.good i j b (Z.ν i j b)

def full : FullTie Z.good Z.rd := ⟨Z.tie, Z.hecke, Z.univ⟩

theorem heckeRead {i j b} (h : RatHecke (Z.rd i j b)) : HeckeRead (Z.rd i j b) := (Z.hecke i j b).heckeRead h

include Z in

theorem delU_ine (i : D.ntw.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) (hQ : Formalism.MainNotions.NAdm.AdmQ D.ntw i Q M) (P : Pl D.host.E)
    (hP : P ∈ Q) : (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩) ∧
    ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
      ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = 0 :=
  GlobalTheory.UnivCharIne.delU_ine D Z.univ i Q M hQ P hP

include Z in

theorem delUTie (hK : GlobalTheory.TwSys.K1 D.ntw) : GlobalTheory.TwSys.DelUTie D.nexp := GlobalTheory.UnivChar.delUTie_of_isUnivChar _ hK Z.univ

theorem rat {i j b} (h : RatRow YS v₀ Z.good i j b) : Rat Z.good (Z.rd i j b) := (Z.scalar i j b).rat h

include Z in

theorem thU_empty (i : D.ntw.Tw) (j : ℕ) (b : Bool) (M : ℕ) (d : D.nexp.Dat i j b) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    D.nexp.thU i j b ∅ M d = D.nexp.th i j b d ⊗ₜ[D.ntw.O i] 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (Z.tie i ⟨n, h2⟩ b).thU_empty M d

theorem exists_dat {i j b} (h : RatRow YS v₀ Z.good i j b) {s g P} (hd : Z.ρ.IsDatum i j b s g P) :
    ∃ d, (Z.tie i j b).cls d = g ∧ (Z.tie i j b).coef d = P ∧ Z.rd i j b (D.nexp.th i _ b d) = Z.ρ.theta i j b g P := by
  obtain ⟨d, -, rfl, rfl⟩ := (Z.tie i j b).dat_onto s g P hd ((Z.rat h).1 s g P hd)
  exact ⟨d, rfl, rfl, (Z.tie i j b).th_eq d⟩

end ExportTie

example (i : D.ntw.Tw) (b : Bool) : NX.readLL0 S i b = sideEmb D.ntw i b := rfl

example (i : D.ntw.Tw) : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt false (D.ntw.delta i) = (D.ntw.delta i)⁻¹ := rfl

example : normProd (∅ : Finset (Pl D.host.E)) = 1 := rfl

end GlobalTheory.SeriesTie

end
