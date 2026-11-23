import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw
import Formalism.LocalRingCardinality.DataForced
import Formalism.SharpRestriction.Divisibility.CartierLocalBounds
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalRingCardinality.DataParamsT

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.PDVN

variable (D : Formalism.BasicNotions.D7)

def IsConjPl (P P' : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  Formalism.BasicNotions.IsConjPl D.host P P'

def QOk (i : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.QOk D.ntw i Q

def SOk (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) (s : ℤ) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SOk D.ntw i lam s

theorem paramsT_s_eq {L : SizeData₂ D} {P : ParameterChoice' D L} (PT : ParamsT D L P) : PT.s = Formalism.MainNotions.BlochKatoReduction.Gen.sFun D.R := by
  cases PT
  simp only [Formalism.MainNotions.BlochKatoReduction.Gen.sFun]
  split_ifs <;> simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega

def kMap (i : D.ntw.Tw) (k : ℕ) : FractionRing (D.ntw.O i) →+* FractionRing (D.ntw.Ok i k) :=
  Formalism.MainNotions.BlochKatoReduction.Gen.kMap D.ntw i k

def thEval (i : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (lam : D.ntw.abelian₂ i) (k : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) : FractionRing (D.ntw.Ok i k) :=
  Formalism.MainNotions.BlochKatoReduction.Gen.thEval D.ntw i Q lam k ψ

def IntAfter (i : D.ntw.Tw) (n : ℕ) (x : FractionRing (D.ntw.O i)) : Prop :=
  ∃ y : D.ntw.O i, algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) y =
    ((D.ntw.l i : ℕ) : FractionRing (D.ntw.O i)) ^ n * x

def ThetaDenominatorWith (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk D i Q →
    ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → ∀ δ, ∃ y : D.ntw.O i, algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) y =
      ((D.ntw.l i : ℕ) : FractionRing (D.ntw.O i)) ^ (N0 i) * D.ntw.th i Q lam δ

def ThetaDenominatorExists : Prop := ∃ N0 : D.ntw.Tw → ℕ, ThetaDenominatorWith D N0

structure Loc where

  cE : ∀ i, D.ntw.abelian₂ i → ℕ

  kap : ∀ i, D.ntw.abelian₂ i → ℕ

  ffP : Finset ℕ

  a0 : ℕ → ℕ
  a0_mem_one_two : ∀ p ∈ ffP, a0 p = 1 ∨ a0 p = 2

  g_mem : ∀ k, D.host.g k ∈ ffP
  pde_mem : D.host.pde ∈ ffP ∧ D.host.pde' ∈ ffP

variable {D} in

def Loc.wt (X : Loc D) (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) : ℝ :=
  (X.kap i lam : ℝ) + (D.ntw.s2 i lam : ℝ) * (D.R.f : ℝ)

def ThetaDenominatorValues (X : Loc D) (C : ℝ) : Prop :=
  ∃ n : ∀ i, D.ntw.abelian₂ i → ℕ,
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ≠ 2 →
      (∀ P ∈ placesOver D.host.E (D.ntw.l i), P.asIdeal.ramificationIdx ℤ = 1) →
      D.ntw.l i ∉ X.ffP → n i lam = 0) ∧
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ∣ D.host.condN →
      (n i lam : ℝ) ≤ X.wt i lam * (2 + C * Formalism.MainNotions.ExistsIdealDenominator.vdd D (D.ntw.l i))) ∧
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ∈ X.ffP → (n i lam : ℝ) ≤ C * (X.a0 (D.ntw.l i) : ℝ) * X.wt i lam) ∧
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk D i Q →
      ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → ∀ δ, IntAfter D i (X.cE i lam + n i lam) (D.ntw.th i Q lam δ)

variable {D} in
theorem IntAfter.mono {i : D.ntw.Tw} {a b : ℕ} (h : a ≤ b) {x : FractionRing (D.ntw.O i)}
    (hx : IntAfter D i a x) : IntAfter D i b x := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨((D.ntw.l i : ℕ) : D.ntw.O i) ^ (b - a) * y, ?_⟩
  rw [map_mul, map_pow, hy, map_natCast, ← mul_assoc, ← pow_add, Nat.sub_add_cancel h]

theorem thetaDenominator_of_values (X : Loc D) (C : ℝ) (h : ThetaDenominatorValues D X C) : ThetaDenominatorExists D := by
  classical
  obtain ⟨n, -, -, -, h4⟩ := h
  refine ⟨fun i => Finset.univ.sup (fun lam : D.ntw.abelian₂ i => X.cE i lam + n i lam), ?_⟩
  intro i hi Q hQ lam s hs δ
  exact IntAfter.mono (Finset.le_sup (f := fun lam : D.ntw.abelian₂ i => X.cE i lam + n i lam) (Finset.mem_univ lam))
    (h4 i hi Q hQ lam s hs δ)

def familyThetaDenominatorValues {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i)) (C : ℝ) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaDenominatorValues (Fm.D x i) (XF x hx i) C

def ThetaEmptyNonzero : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → (∑ δ, D.ntw.th i ∅ lam δ) ≠ 0

def familyThetaEmptyNonzero {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ThetaEmptyNonzero (Fm.D x i)

def eq' {K : Type} [Field K] (Y qms : K) (q : ℕ) : K :=
  Formalism.MainNotions.BlochKatoReduction.Gen.eq' Y qms q

open Classical in

def CharacterTwistTheta : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk D i Q →
    ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → ∀ (P Pb : HeightOneSpectrum (𝓞 D.host.E)) (_hP : P ∈ Q) (_hPb : Pb ∈ Q),
      P ≠ Pb → IsConjPl D P Pb → ∀ (k : ℕ) (ψ : D.ntw.RCG i ((Q.erase P).erase Pb) →* (D.ntw.Ok i k)ˣ)
      (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsFrob (D.nd.plOm.1 P) (normV P) σ →
        thEval D i Q lam k (ψ.comp (D.ntw.res i Q ((Q.erase P).erase Pb)
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))) =
          eq' (kMap D i k (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.Xv i lam P)) *
                algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k))
                  ((ψ (D.ntw.art i ((Q.erase P).erase Pb) σ) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
              (((normV P : ℕ) : FractionRing (D.ntw.Ok i k)) ^ (-s)) (normV P) *
            thEval D i ((Q.erase P).erase Pb) lam k ψ

def OrdRule {σ B : Type} (lx : σ → B) (rk : B → ℕ) (o : List σ) : Prop :=
  o.Pairwise fun u u' => lx u ≠ lx u' → rk (lx u) < rk (lx u')

def oW (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (a : 𝓞 E) : (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) :=
  LinearMap.baseChange ℂ_[l] (DistribSMul.toAddMonoidHom Λ a).toIntLinearMap

structure PtTie {l : ℕ} [Fact l.Prime] (E : Type) [Field E] [NumberField E] {Λ σ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Y : Formalism.MainNotions.ExistsIdealDenominator.PtGeo l Λ σ) {Bx Ex : Type} (lx : σ → Bx) (le : σ → Ex)
    (slx : Bx → (𝓞 E →+* ℂ_[l])) where

  HA : Type
  [acgHA : AddCommGroup HA]
  [modHA : Module ℂ_[l] HA]
  LA : Type
  [acgLA : AddCommGroup LA]
  [modLA : Module ℂ_[l] LA]
  pr : HA →ₗ[ℂ_[l]] LA
  pr_surj : Function.Surjective pr

  oH : 𝓞 E →+* Module.End ℂ_[l] HA
  oL : 𝓞 E →+* Module.End ℂ_[l] LA
  pr_o : ∀ a h, pr (oH a h) = oL a (pr h)

  bx : Module.Basis Bx ℂ_[l] LA
  bx_eig : ∀ a x, oL a (bx x) = slx x a • bx x

  sle : Ex → (𝓞 E →+* ℂ_[l])
  be : Module.Basis Ex ℂ_[l] (ℂ_[l] ⊗[ℤ] Λ)
  be_eig : ∀ a e, oW l E Λ a (be e) = sle e a • be e

  th : 𝓞 E →+* 𝓞 E
  mu : HA →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] Y.H
  mu_bal : ∀ a h w, mu (oH a h) w = mu h (oW l E Λ (th a) w)

  fil : Y.Fil = Submodule.span ℂ_[l] {v | ∃ h w, pr h = 0 ∧ v = mu h w}

  letters : ∀ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id → ∃ b : Module.Basis σ ℂ_[l] (Y.H ⧸ Y.Fil),
    ∀ u, b u = Y.Fil.mkQ (mu (sA (bx (lx u))) (be (le u)))

  all_pairs : ∀ x e, slx x = (sle e).comp th → ∃ u, lx u = x ∧ le u = e

  EL_eq : Y.EL = {L | ∃ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id ∧ (∀ a, sA ∘ₗ oL a = oH a ∘ₗ sA) ∧
    ∀ u, L u = mu (sA (bx (lx u))) (be (le u))}

attribute [instance] PtTie.acgHA PtTie.modHA PtTie.acgLA PtTie.modLA

variable {D} in

structure ValRule (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) where

  Bx : D.ntw.Tw → ℕ → Type
  Ex : D.ntw.Tw → ℕ → Type
  lx : ∀ i j, D.nth.Let i j → Bx i j
  le : ∀ i j, D.nth.Let i j → Ex i j

  slx : ∀ i j, Bx i j → (𝓞 D.host.E →+* ℂ_[D.ntw.l i])

  rk : ∀ i j, Bx i j → ℕ
  rk_inj : ∀ i j, Function.Injective (rk i j)

  ord : ∀ i j, OrdRule (lx i j) (rk i j) (X.ord i j)

  pt : ∀ i j y, PtTie D.host.E (X.pt i j y) (lx i j) (le i j) (slx i j)

variable {D} in

def ValRuled (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop := Nonempty (ValRule X)

theorem ordRule_idx {σ : Type} [DecidableEq σ] (o : List σ) (h : o.Nodup) :
    OrdRule (fun u : σ => u) (fun u => o.idxOf u) o := by
  unfold OrdRule
  induction o with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.nodup_cons] at h
    rw [List.pairwise_cons]
    refine ⟨fun u' hu' _ => ?_, ?_⟩
    · have hua : ¬ (a = u') := fun e => h.1 (e ▸ hu')
      simp [List.idxOf_cons, hua]
    · refine (ih h.2).imp_of_mem fun {u u'} hu hu' hr hne => ?_
      have hua : ¬ (a = u) := fun e => h.1 (e ▸ hu)
      have hua' : ¬ (a = u') := fun e => h.1 (e ▸ hu')
      simpa [List.idxOf_cons, hua, hua'] using hr hne

variable {D} in

theorem valRuled_of_noPts (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) (h : ∀ i j, IsEmpty (D.nth.Pt i j))
    (e : ∀ i : D.ntw.Tw, 𝓞 D.host.E →+* ℂ_[D.ntw.l i]) : ValRuled X := by
  refine ⟨{
    Bx := fun _ _ => Unit
    Ex := fun _ _ => Unit
    lx := fun _ _ _ => ()
    le := fun _ _ _ => ()
    slx := fun i _ _ => e i
    rk := fun _ _ _ => 0
    rk_inj := fun _ _ _ _ _ => rfl
    ord := fun i j => ?_
    pt := fun i j y => (h i j).elim y }⟩
  unfold OrdRule
  exact List.pairwise_of_forall fun _ _ hne => (hne rfl).elim

variable {D} in

def LiftsIndependence (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j y, ∀ P ∈ D.nth.Harm i j, ∀ L ∈ (X.pt i j y).EL, ∀ L' ∈ (X.pt i j y).EL, ∀ g ∈ (X.pt i j y).Bas,
    (X.pt i j y).PN (X.ord i j) (X.pt i j y).nabD L (P.map (Formalism.MainNotions.ExistsIdealDenominator.iO i)) g =
      (X.pt i j y).PN (X.ord i j) ((X.pt i j y).nab 1) L' (P.map (Formalism.MainNotions.ExistsIdealDenominator.iO i)) g

variable {D} in

def LiftsIndependenceRuled (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop := ValRuled X → LiftsIndependence X

variable {D} in

def EigenLiftScaling (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j y, ∃ L ∈ (X.pt i j y).EL, ∃ U : D.nth.Let i j → (X.pt i j y).H, (∀ u, U u ∈ (X.pt i j y).HO) ∧
    ∀ u, L u - U u ∈ (X.pt i j y).Fil ∧
      ∀ d : ℂ_[D.ntw.l i], ‖d‖ ≤ (D.ntw.l i : ℝ) ^ (-(Formalism.MainNotions.ExistsIdealDenominator.vdd D (D.ntw.l i))) →
        d • (L u - U u) ∈ (X.pt i j y).HO

variable {D} in

def ValueFunctionFormula (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j b (d : D.nexp.Dat i j b) (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))),
    D.nth.datP i j b d ∈ D.nth.Harm i j →
    (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal)) →
    ∀ Ψ : ↥QP → D.nth.Lt i j → Formalism.MainNotions.ExistsIdealDenominator.KK i,
    (∀ (q : ↥QP) P', Formalism.MainNotions.ExistsIdealDenominator.ConjPl D q.1 P' → Formalism.MainNotions.ExistsIdealDenominator.PerI (q.1.asIdeal * P'.asIdeal) (Ψ q)) →
    (fun y => D.nth.thV i j (fun x => D.nth.datPhi i j b d x * ∏ q : ↥QP, Ψ q x) (D.nth.datP i j b d) y)
      ∈ X.FQ i j b QP

variable {D} in

def ValueFunctionRuled (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop := ValRuled X → ValueFunctionFormula X

def eG (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b

def eO (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.eO D.nexp i j b

def AO (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.AO D.nexp i j b

def Fm0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.Fm0 D.nexp i j b

def V0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.V0 D.nexp i j b

def HkIdx (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host) : Prop :=
  Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P

def hkO (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.hkO D.nexp i j b k P

def HeckeCommutesIdempotent : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ∀ k P, HkIdx D i k P →
    AO D i j b ∘ₗ hkO D i j b k P = hkO D i j b k P ∘ₗ AO D i j b

def T3 (i : D.ntw.Tw) (j : ℕ) (b : Bool) (B : Submodule (D.ntw.O i) (D.nexp.Fm i j b)) : Prop :=
  Formalism.MainNotions.IntegralHeckeForms.T3 D.nexp i j b B

def M0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.Mall D.nexp i j b

def Mj (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  M0 D i j b ⊓ (V0 D i j b).restrictScalars (D.ntw.O i)

def ConjugationNormInvariance : Prop :=
  (∀ (i : D.ntw.Tw) (b : Bool), ∃ c : MonoidAlgebra (D.ntw.O i) (G0g D.nd),
    MonoidAlgebra.map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).toAddMonoidHom c =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (D.ntw.O i)) • D.nexp.eAlg i b) ∧
  ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, (M0 D i j b).map (AO D i j b) ≤ Mj D i j b

def BsupStable : Prop := ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool) (g : G0g D.nd),
  (D.nexp.Bsup i j b).map ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i)) ≤ D.nexp.Bsup i j b

def IntegralityGoodReduction : Prop := BsupStable D → ConjugationNormInvariance D

def GoodHeckeEigensystems : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, T3 D i j b (Mj D i j b)

variable {D} in

def KeyTwoSidedBound (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j, ∃ C : ℝ, ∀ y, (D.ntw.l i : ℝ) ^ (-C) ≤ ‖(X.pt i j y).key‖ ∧ ‖(X.pt i j y).key‖ ≤ (D.ntw.l i : ℝ) ^ C

variable {D} in

def KeyUpperBound (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j, ∃ C : ℝ, ∀ y, ‖(X.pt i j y).key‖ ≤ (D.ntw.l i : ℝ) ^ C

variable {D} in
theorem keyUpper_of_twoSided (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) (h : KeyTwoSidedBound X) : KeyUpperBound X :=
  fun i j => let ⟨C, hC⟩ := h i j; ⟨C, fun y => (hC y).2⟩

variable {D} in

def ExistsUnitClasses (X : Formalism.MainNotions.ExistsIdealDenominator.Geo D) : Prop :=
  ∀ i j, ∃ (n : ℕ) (cp : D.nth.Pt i j → Fin n) (u : Fin n → (D.ntw.O i)ˣ) (tr : D.nth.Pt i j → ℂ_[D.ntw.l i]),
    (∀ y, (X.pt i j y).key = Formalism.MainNotions.ExistsIdealDenominator.iO i (u (cp y) : D.ntw.O i) * tr y) ∧
    (∀ s ∈ Formalism.MainNotions.ExistsIdealDenominator.GalF i (D.nth.MaximalUnramifiedExtension i), ∀ y, tr (X.actG i j s y) = s (tr y) ∧ cp (X.actG i j s y) = cp y) ∧
    (∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → ∀ (k : D.nth.Kq i j P) y, cp (D.nth.actK i j P k y) = cp y) ∧
    ∀ b (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i) →
      ∀ F ∈ X.FQ i j b QP, ∀ c, (fun y => if cp y = c then F y else 0) ∈ X.FQ i j b QP

def inL (w : D.what₂.places.Pl) (y : ℝ) : ℝ := y / (D.what₂.places.ramIdx w : ℝ)

theorem ramIdx_conj (w : D.what₂.places.Pl) :
    D.what₂.places.ramIdx (D.what₂.places.conj w) = D.what₂.places.ramIdx w := by
  have hnat : ∀ (w' : D.what₂.places.Pl) (n : ℕ), 0 ≤ D.what₂.places.val w' (n : D.what₂.LL) := by
    intro w' n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact le_trans (le_min ih (by rw [AddValuation.map_one])) (AddValuation.map_add _ _ _)
  have hint : ∀ (w' : D.what₂.places.Pl) (z : ℤ), 0 ≤ D.what₂.places.val w' (z : D.what₂.LL) := by
    intro w' z
    rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
    · simpa using hnat w' n
    · rw [Int.cast_neg, AddValuation.map_neg]
      simpa using hnat w' n
  have hstar : ∀ n : ℕ, D.what₂.places.val (D.what₂.places.conj w) (n : D.what₂.LL) =
      D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    rw [D.conj_val, star_natCast]
  have hres : D.what₂.places.resChar (D.what₂.places.conj w) = D.what₂.places.resChar w := by
    by_contra hne
    have hcop : Nat.Coprime (D.what₂.places.resChar (D.what₂.places.conj w)) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime _) (D.what₂.places.resChar_prime _)).2 hne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL) +
        (b : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hab
    have hq : 0 < D.what₂.places.val w ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL) := by
      rw [← hstar, D.what₂.places.val_resChar]
      exact_mod_cast D.what₂.places.ramIdx_pos _
    have hp : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
      rw [D.what₂.places.val_resChar]
      exact_mod_cast D.what₂.places.ramIdx_pos _
    have ha : 0 < D.what₂.places.val w ((a : D.what₂.LL) *
        ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]
      exact lt_of_lt_of_le hq (le_add_of_nonneg_left (hint w a))
    have hb : 0 < D.what₂.places.val w ((b : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]
      exact lt_of_lt_of_le hp (le_add_of_nonneg_left (hint w b))
    have hadd := AddValuation.map_add (D.what₂.places.val w) ((a : D.what₂.LL) *
        ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL))
      ((b : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL))
    rw [h1, AddValuation.map_one] at hadd
    exact absurd hadd (not_le.2 (lt_min ha hb))
  have hv := D.what₂.places.val_resChar (D.what₂.places.conj w)
  rw [hres, hstar, D.what₂.places.val_resChar] at hv
  exact_mod_cast hv.symm

def wJ (j : ℕ) : ℝ := ∑ ρ : D.what₂.Tau, DV.wSz D j ρ

def wMax : ℝ := (SizeData₂.lifts D).fold max 0 (wJ D)

def onL (L : SizeData₂ D) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) : ℝ :=
  ∑ j ∈ SizeData₂.lifts D,
    ((inL D w (D.what₂.Ij μ j w : ℝ) +
      inL D (D.what₂.places.conj w) (D.what₂.Ij μ j (D.what₂.places.conj w) : ℝ)) / (D.what₂.D0 : ℝ) - 2 * L.F j w)

def onRj (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ) (j : ℕ) (w : D.what₂.places.Pl) : ℝ :=
  fl j (D.what₂.places.resChar w) + (r j w + r j (D.what₂.places.conj w)) / (D.what₂.D0 : ℝ)

def onR (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ) (w : D.what₂.places.Pl) : ℝ :=
  (∑ j ∈ SizeData₂.lifts D, onRj D fl r j w) + 2 / ((D.what₂.places.resChar w : ℝ) ^ 2)

def onBound (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (D.R.m : ℝ) * (L.sc.L * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * wMax D +
    (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * Real.log L.sc.x)

def onBoundJ (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (L.sc.L * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * wMax D +
    (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * Real.log L.sc.x)

theorem onBound_eq (L : SizeData₂ D) (C : ℝ) : onBound D L C = (D.R.m : ℝ) * onBoundJ D L C := by
  simp only [onBound, onBoundJ]
  ring

def ONTw (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∃ (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ), (∀ j l, 0 ≤ fl j l) ∧ (∀ j w, 0 ≤ r j w) ∧
    (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → onL D L (D.what₂.muAt w) w ≤ onR D fl r w) ∧
    ∀ T : Finset D.what₂.places.Pl, ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (onR D fl r w) ≤ onBound D L C

variable {D} in

theorem ONTw.sum_le {L : SizeData₂ D} {C : ℝ} (h : ONTw D L C) (T : Finset D.what₂.places.Pl)
    (hT : ∀ w ∈ T, D.what₂.muAt w ≠ D.what₂.mu0) :
    ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (onL D L (D.what₂.muAt w) w) ≤ onBound D L C := by
  obtain ⟨fl, r, _, _, hle, hsum⟩ := h
  refine le_trans (Finset.sum_le_sum fun w hw => ?_) (hsum T)
  have h0 : 0 ≤ SizeData₂.lwP w := by
    unfold SizeData₂.lwP Formalism.BasicNotions.lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ h0
  unfold DV.ur
  exact mul_le_mul_of_nonneg_left (hle w (hT w hw)) (Nat.cast_nonneg _)

def ONTwJ (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∃ (fl : ℕ → ℕ → ℝ) (r : ℕ → D.what₂.places.Pl → ℝ), (∀ j l, 0 ≤ fl j l) ∧ (∀ j w, 0 ≤ r j w) ∧
    (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → onL D L (D.what₂.muAt w) w ≤ onR D fl r w) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ T : Finset D.what₂.places.Pl,
      ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (onRj D fl r j w) ≤ onBoundJ D L C) ∧
    ∀ T : Finset D.what₂.places.Pl,
      ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (2 / ((D.what₂.places.resChar w : ℝ) ^ 2)) ≤ C

variable {D} in

theorem ONTwJ.toONTw {L : SizeData₂ D} {C : ℝ} (h : ONTwJ D L C) (hC : C ≤ onBound D L C) : ONTw D L (2 * C) := by
  obtain ⟨fl, r, hfl, hr, hle, hJ, h2⟩ := h
  refine ⟨fl, r, hfl, hr, hle, fun T => ?_⟩
  have key : ∀ w, SizeData₂.lwP w * DV.ur D w (onR D fl r w) =
      (∑ j ∈ SizeData₂.lifts D, SizeData₂.lwP w * DV.ur D w (onRj D fl r j w)) +
        SizeData₂.lwP w * DV.ur D w (2 / ((D.what₂.places.resChar w : ℝ) ^ 2)) := by
    intro w
    simp only [onR, DV.ur, mul_add, Finset.mul_sum]
  simp only [key, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have hs : ∑ j ∈ SizeData₂.lifts D, ∑ w ∈ T, SizeData₂.lwP w * DV.ur D w (onRj D fl r j w) ≤
      ∑ _j ∈ SizeData₂.lifts D, onBoundJ D L C :=
    Finset.sum_le_sum fun j hj => hJ j hj T
  have hcard : ∑ _j ∈ SizeData₂.lifts D, onBoundJ D L C = onBound D L C := by
    rw [Finset.sum_const, nsmul_eq_mul, onBound_eq]
    simp [SizeData₂.lifts]
  have h2' := h2 T
  have hB : onBound D L (2 * C) = 2 * onBound D L C := by
    simp only [onBound]
    ring
  rw [hB]
  linarith

structure ThetaDenominatorData where

  dat : ∀ i j b, Set (D.nexp.Dat i j b)

def TraceLatticeInclusion (E : Formalism.MainNotions.IntegralHeckeForms.XD D) (T : ThetaDenominatorData D) : Prop := Formalism.MainNotions.IntegralHeckeForms.ThSub D.nexp E T.dat

abbrev Th0F {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Type := ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), ThetaDenominatorData (Fm.D x i)

def familyTraceInclusion {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (EF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.IntegralHeckeForms.XD (Fm.D x i)) (TF : Th0F Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TraceLatticeInclusion (Fm.D x i) (EF x hx i) (TF x hx i)

def DomON (L : SizeData₂ D) (nW : ℕ) (CP : ℝ) : Prop := ∀ j ∈ SizeData₂.lifts D, WeightAlgebra.DomAt D L j nW CP

def SizeConditionTwenty (L : SizeData₂ D) : Prop :=
  10 ^ 4 * zBase L * ((D.R.r + D.R.t : ℕ) : ℝ) ≤ L.sc.b

theorem sizeCondition_of_dominance (L : SizeData₂ D) {P : ParameterChoice' D L} (PT : ParamsT D L P) {CP : ℝ} (hD : DomON D L PT.nWn CP) : SizeConditionTwenty D L := by
  unfold SizeConditionTwenty
  have hZdef : zBase L = (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L := rfl
  have hCbN : (0 : ℝ) ≤ PT.CbN := by linarith [PT.CbN_ge]
  have hb0 : 0 ≤ L.sc.b := by
    refine le_trans ?_ PT.b_ge
    positivity
  have hnV : ((D.R.r + D.R.t : ℕ) : ℝ) = PT.nP + PT.TO * PT.nWn := by
    rw [PT.split]
    push_cast
    ring
  rcases le_or_gt (zBase L) 0 with hZ0 | hZ0
  · have h1 : 10 ^ 4 * zBase L * ((D.R.r + D.R.t : ℕ) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  · have hr : 1 ≤ D.R.r := by
      rcases Nat.eq_zero_or_pos D.R.r with h | h
      · rw [hZdef, h] at hZ0
        simp at hZ0
      · exact h
    have hf : 1 ≤ D.R.f := by
      rcases Nat.eq_zero_or_pos D.R.f with h | h
      · rw [hZdef, h] at hZ0
        simp at hZ0
      · exact h
    have hTOn : 2501 ≤ PT.TO := by
      have h1 : 2501 ≤ D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (PT.Dp + 1) := by nlinarith
      exact h1.trans PT.order_ge_rank_bound
    have hTO : (2501 : ℝ) ≤ PT.TO := by exact_mod_cast hTOn
    have hnWn : 2 ≤ PT.nWn := by
      have h1 : 2 ≤ D.R.f * D.R.r * (D.R.r + 1) :=
        calc 2 = 1 * 1 * (1 + 1) := rfl
          _ ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul (Nat.mul_le_mul hf hr) (Nat.add_le_add_right hr 1)
      exact h1.trans PT.nW_lo.1
    have hnW : (2 : ℝ) ≤ PT.nWn := by exact_mod_cast hnWn
    have hPP2 : (2 : ℝ) ≤ PT.PP := hnW.trans PT.nW_le
    have hnP : (PT.nP : ℝ) ≤ PT.nWn := by exact_mod_cast PT.nW_lo.2.2
    have hnV_le : ((D.R.r + D.R.t : ℕ) : ℝ) ≤ 2 * PT.TO * PT.PP := by
      rw [hnV]
      nlinarith [PT.nW_le]
    have hsq : L.sc.b = L.sc.b ^ (1 / 2 : ℝ) * L.sc.b ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hb0]
    have hZPP : 2 * 10 ^ 4 * zBase L ≤ PT.PP ^ 3 * (PT.TO : ℝ) ^ 2 := by
      have hT2 : (2501 : ℝ) ^ 2 ≤ (PT.TO : ℝ) ^ 2 := by nlinarith
      have hP3 : PT.PP ≤ PT.PP ^ 3 := by
        have h4 : (4 : ℝ) ≤ PT.PP ^ 2 := by nlinarith
        calc PT.PP = PT.PP * 1 := (mul_one _).symm
          _ ≤ PT.PP * PT.PP ^ 2 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          _ = PT.PP ^ 3 := by ring
      have hP3' : (2 : ℝ) ≤ PT.PP ^ 3 := hPP2.trans hP3
      rcases le_or_gt (zBase L) 1 with h1 | h1
      · have hm := mul_le_mul hP3' hT2 (by norm_num) (by linarith)
        linarith
      · have hrp : zBase L ≤ zBase L ^ PT.eP := by
          calc zBase L = zBase L ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ zBase L ^ PT.eP := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith [PT.eP_ge])
        have hpos : 0 ≤ zBase L ^ PT.eP := Real.rpow_nonneg hZ0.le _
        have hPPZ : zBase L ≤ PT.PP := by
          rw [PT.PP_eq]
          nlinarith [PT.one_le_CP]
        have hm := mul_le_mul (hPPZ.trans hP3) hT2 (by norm_num) (by linarith)
        linarith
    calc 10 ^ 4 * zBase L * ((D.R.r + D.R.t : ℕ) : ℝ) ≤ 10 ^ 4 * zBase L * (2 * PT.TO * PT.PP) := by
          gcongr
      _ = (2 * 10 ^ 4 * zBase L) * (PT.TO * PT.PP) := by ring
      _ ≤ L.sc.b ^ (1 / 2 : ℝ) * L.sc.b ^ (1 / 2 : ℝ) :=
          mul_le_mul (hZPP.trans PT.precision_cube_order_sq_le_sqrt) PT.TO_PP' (mul_nonneg (Nat.cast_nonneg _) (by linarith))
            (Real.rpow_nonneg hb0 _)
      _ = L.sc.b := hsq.symm

def OntoIndices (L : SizeData₂ D) (P : ParameterChoice' D L) (PT : ParamsT D L P) (CH : NChoice D) (I : Formalism.MainNotions.TwIn D) (T : ThetaDenominatorData D) (C : ℝ) :
    Prop :=
  DomON D L PT.nWn PT.CP → Formalism.MainNotions.TwConjAt D CH → TraceLatticeInclusion D I.E T → Formalism.MainNotions.TwGoodAt D CH I → ONTw D L C

def familyOntoIndices {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (TF : Th0F Fm) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x) (I : Formalism.MainNotions.TwIn (Fm.D x i)),
    OntoIndices (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) (Fm.ex x hx i).nch I (TF x hx i) C

def OntoIndicesByLift (L : SizeData₂ D) (P : ParameterChoice' D L) (PT : ParamsT D L P) (CH : NChoice D) (I : Formalism.MainNotions.TwIn D) (T : ThetaDenominatorData D) (C : ℝ) :
    Prop :=
  DomON D L PT.nWn PT.CP → Formalism.MainNotions.TwConjAt D CH → TraceLatticeInclusion D I.E T → Formalism.MainNotions.TwGoodAt D CH I → ONTwJ D L C

def familyOntoIndicesByLift {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (TF : Th0F Fm) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x) (I : Formalism.MainNotions.TwIn (Fm.D x i)),
    OntoIndicesByLift (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) (Fm.ex x hx i).nch I (TF x hx i) C

def OntoIndicesAndByLift (L : SizeData₂ D) (P : ParameterChoice' D L) (PT : ParamsT D L P) (CH : NChoice D) (I : Formalism.MainNotions.TwIn D) (T : ThetaDenominatorData D) (C : ℝ) :
    Prop :=
  OntoIndices D L P PT CH I T C ∧ OntoIndicesByLift D L P PT CH I T C

def FamilyOntoIndicesAndByLift {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (TF : Th0F Fm) (C : ℝ) : Prop :=
  familyOntoIndices Fm TF C ∧ familyOntoIndicesByLift Fm TF C

def OffG (w : D.what₂.places.Pl) : Prop := ∀ i0 : Fin 2, ¬ LiftErrorLocal.Over D i0 w

def GGAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  ∀ B1 B2 : Submodule (D.ntw.O (CH.twI w)) (D.nexp.Fm (CH.twI w) j b),
    B1.FG → B2 ≤ B1 → LiftErrorLocal.spK B2 = LiftErrorLocal.spK B1 → LiftErrorLocal.GStab B1 → LiftErrorLocal.GStab B2 →
    LiftErrorLocal.delq D * LiftErrorLocal.lenQ (D.ntw.l (CH.twI w)) (LiftErrorLocal.psiPart B1) (LiftErrorLocal.psiPart B2) ≤
      LiftErrorLocal.lenQ (D.ntw.l (CH.twI w)) B1 B2 + (LiftErrorLocal.rkK B1 : ℝ) * LiftErrorLocal.vU D (CH.twI w)

def SHAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  (LiftErrorLocal.rkK (D.nexp.Bsup (CH.twI w) j b) : ℝ) / LiftErrorLocal.delq D ≤
                 2 * (Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) : ℝ) ∧
    Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.V0 D.nexp (CH.twI w) j b) = D.what₂.D0 ∧
    (Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) : ℝ) ≤ 2 * D.what₂.D0 ∧
    (D.nexp.Bsup (CH.twI w) j b).map (IntegralHeckeForms.AO D.nexp (CH.twI w) j b) ≤ D.nexp.Bsup (CH.twI w) j b

def SHbAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  LiftErrorLocal.rkK (IntegralHeckeForms.Mall D.nexp (CH.twI w) j b) =
                 Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) ∧
    LiftErrorLocal.rkK (LiftErrorLocal.Mj D (CH.twI w) j b) = D.what₂.D0

def ShareAtTypePrimes (CH : NChoice D) : Prop := ∀ (i0 : Fin 2) w, LiftErrorLocal.Over D i0 w → TwistedAt D w → SHAt D CH w

section Run

variable {D} {CH : NChoice D} (X : LiftErrorLocal.Loc D CH)

def UAt (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (CH.twI w) j b (CH.k' w) (CH.Q w) (X.psiW w b) ≤ LiftErrorLocal.twistV0Submodule D CH w j b ∧
    (D.what₂.Ij (D.what₂.muTw w) j (LiftErrorLocal.plS CH w b) : ℝ) ≤
      (D.what₂.places.ramIdx (LiftErrorLocal.plS CH w b) : ℝ) * X.IsgTw w j b

def LKAt (w : D.what₂.places.Pl) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool),
  (D.nexp.Bsup (CH.twI w) j b).FG ∧ LiftErrorLocal.GStab (D.nexp.Bsup (CH.twI w) j b) ∧
    X.ThN w j h1 h2 b ≤ D.nexp.Bsup (CH.twI w) j b

def DepAt (L : SizeData₂ D) (T : ThetaDenominatorData D) (er : ℕ → ℕ → ℝ) (w : D.what₂.places.Pl) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool), ∃ c : D.ntw.O (CH.twI w), c ≠ 0 ∧
    (∀ x ∈ LiftErrorLocal.psiPart (LiftErrorLocal.GSpan (X.ThN w j h1 h2 b)),
      ∃ z ∈ IntegralHeckeForms.Th D.nexp (CH.twI w) j b (T.dat (CH.twI w) j b),
        ((Nat.card D.nexp.U : ℕ) : D.ntw.O (CH.twI w)) • x = c • z) ∧
    ((X.W j h1 h2).eLa X.TO (X.run j).nus (X.laK (LiftErrorLocal.plS CH w b)) : ℝ) /
        (eWL X.B.KO (X.laK (LiftErrorLocal.plS CH w b)) : ℝ) -
      LiftErrorLocal.vDv (D.ntw.O (CH.twI w)) (D.ntw.l (CH.twI w)) c ≤ L.F j w + er j (D.what₂.places.resChar w)

def WBAt : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
  ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
    s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def DomRun (L : SizeData₂ D) (CP : ℝ) : Prop := ∀ j (_h1 : 1 ≤ j) (_h2 : j ≤ D.R.m), WeightAlgebra.DomAt D L j (X.run j).nW CP

def AdmRun (L : SizeData₂ D) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  DomRun X L H.C1 → LiftErrorLocal.ArchimedeanSignatureMatching D L X H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D X CRd ∧ WBAt X ∧ LiftErrorLocal.adm11 D L X H C2 A2 CR CT CRd

end Run

structure ONObj (CH : NChoice D) (Xd : DivX D) where
  X : LiftErrorLocal.Loc D CH
  X' : LiftErrorLocal.Loc D CH

  I_eq : X'.I = X.I
  c6 : CartierLocalBounds.Loc D Xd X.P6
  c6' : CartierLocalBounds.Loc D Xd X'.P6
  T : ThetaDenominatorData D

def TwistedPlacesCover : Prop := Formalism.MainNotions.N.LocsCoverTw D

section AdmON

variable {D} (L : SizeData₂ D) {CH : NChoice D} {Xd : DivX D} (O : ONObj D CH Xd)

def admA (CA : ℝ) : Prop := LiftErrorLocal.ConjugationNormInvariance D L O.X CA

def unitBoundAtTwistedPlaces : Prop := ∀ w, TwistedAt D w → UAt O.X w

def OffTypePrimeConditions : Prop := ∀ w, OffG D w → TwistedAt D w → GGAt D CH w ∧ SHAt D CH w ∧ SHbAt D CH w ∧
  (D.what₂.places.resChar w ≠ D.host.pde → LKAt O.X w) ∧ (D.what₂.places.resChar w = D.host.pde → LKAt O.X' w)

def OrbitContentCond (C6 : ℝ) : Prop := CartierLocalBounds.Conclusion5 D Xd O.X.P6 O.c6 C6 ∧ CartierLocalBounds.Conclusion5 D Xd O.X'.P6 O.c6' C6

def DepthFromContent (C6 Cd : ℝ) : Prop := OrbitContentCond O C6 →
  ∃ er : ℕ → ℕ → ℝ, (∀ j l, 0 ≤ er j l) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ, ∑ l ∈ S, Real.log (l : ℝ) * er j l ≤ onBoundJ D L Cd) ∧
    (∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w ≠ D.host.pde → DepAt O.X L O.T er w) ∧
    ∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w = D.host.pde → DepAt O.X' L O.T er w

def TypePrimeSizeConds (Cs : ℝ) : Prop :=
  1 ≤ Real.log L.sc.x ∧
    ((O.X.TO : ℝ) + (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2) * (Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ)) ≤
      onBoundJ D L Cs

def AdmON (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 Cd Cs CA : ℝ) : Prop :=
  L.FDef ∧ AdmRun O.X L H C2 A2 CR CT CRd ∧ AdmRun O.X' L H C2 A2 CR CT CRd ∧ admA L O CA ∧ unitBoundAtTwistedPlaces O ∧
    OffTypePrimeConditions O ∧ OrbitContentCond O C6 ∧ DepthFromContent L O C6 Cd ∧ TypePrimeSizeConds L O Cs ∧ TwistedPlacesCover D ∧ ShareAtTypePrimes D CH

def OntoIndicesOfAdmissible (P : ParameterChoice' D L) (PT : ParamsT D L P) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 Cd Cs CA C : ℝ) : Prop :=
  AdmON L O H C2 A2 CR CT CRd C6 Cd Cs CA → OntoIndices D L P PT CH O.X.I O.T C ∧ OntoIndicesByLift D L P PT CH O.X.I O.T C

end AdmON

abbrev ONObjF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Type 1 :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ONObj (Fm.D x i) (Fm.ex x hx i).nch (Fm.X x i)

section FamON

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (OF : ONObjF Fm)

def AdmONF (H : WeightAlgebra.KHyp) (C2 A2 CR CRd C6 Cd Cs CA : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    AdmON (Fm.L x i) (OF x hx i) H C2 A2 CR (Fm.Ct + 1) CRd C6 Cd Cs CA

def familyOntoIndicesWith (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    OntoIndices (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) (Fm.ex x hx i).nch (OF x hx i).X.I (OF x hx i).T C ∧
      OntoIndicesByLift (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) (Fm.ex x hx i).nch (OF x hx i).X.I (OF x hx i).T C

variable {Fm OF} in

theorem familyOntoIndicesWith.concl {C : ℝ} (h : familyOntoIndicesWith Fm OF C)
    (hg : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      DomON (Fm.D x i) (Fm.L x i) (Fm.parT x hx i).nWn (Fm.parT x hx i).CP ∧ Formalism.MainNotions.TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧ TraceLatticeInclusion (Fm.D x i) (OF x hx i).X.I.E (OF x hx i).T ∧
        Formalism.MainNotions.TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch (OF x hx i).X.I) :
    ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ONTw (Fm.D x i) (Fm.L x i) C ∧ ONTwJ (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨x0, h0⟩ := h
  obtain ⟨x1, h1⟩ := hg
  refine ⟨max x0 x1, fun x hx hxm i => ?_⟩
  obtain ⟨a, b, c, d⟩ := h1 x hx (le_trans (le_max_right _ _) hxm) i
  obtain ⟨p, q⟩ := h0 x hx (le_trans (le_max_left _ _) hxm) i
  exact ⟨p a b c d, q a b c d⟩

end FamON

def FamilyOntoIndicesOfAdmissible (H : WeightAlgebra.KHyp) (C2 A2 CR CRd C6 Cd Cs CA C : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (OF : ONObjF Fm) (_CH : ℝ) :
    Prop :=
  AdmONF Fm OF H C2 A2 CR CRd C6 Cd Cs CA → familyOntoIndicesWith Fm OF C

def ClosedOntoIndices (𝒞 : Formalism.MainNotions.FamClass) (OB : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), ONObjF Fm) : Prop :=
  ∀ CA Cd Cs : ℝ, ∃ C : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm CH =>
    ∀ (H : WeightAlgebra.KHyp) (C2 A2 CR CRd C6 : ℝ), 2 ≤ CRd → FamilyOntoIndicesOfAdmissible H C2 A2 CR CRd C6 Cd Cs CA C Fm (OB Fm) CH)

end Formalism.MainNotions.PDVN

end
