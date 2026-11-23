import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.KernelPlaceMeanBound
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable (D) in

structure Sizes (b : ℝ) : Prop where
  e_pos : ∀ τ j, 0 < (D.hc τ).e j
  e_le : ∀ τ j, (((D.hc τ).e j : ℚ) : ℝ) ≤ 2 * b
  v_nonneg : ∀ τ i, 0 ≤ (D.hc τ).v i
  v_le : ∀ τ i, (((D.hc τ).v i : ℚ) : ℝ) ≤ b
  be_le : ∀ τ i j, |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ b
  g_ge : ∀ i, ((D.R.k : ℝ) * b) ^ 8 ≤ (D.host.g i : ℝ)

variable (D) in

def Lpr (b : ℝ) : ℝ := Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

abbrev pW (i : Fin D.R.m) (ρ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D ρ)).1

abbrev qW (i : Fin D.R.m) (ρ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D ρ)).2

def apAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ → ℕ := aPl D i (pW i ρ) (lab σ ρ)

def amAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ → ℕ := aMi D i (pW i ρ) (qW i ρ) (lab σ ρ)

def mainTerm (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ ρ : D.what₂.Tau, (Formalism.BasicNotions.DV.logHook (pW i ρ) (fun n => (apAt i σ ρ n : ℝ)) +
    Formalism.BasicNotions.DV.logHook (qW i ρ) (fun n => (amAt i σ ρ n : ℝ)))

def deltaAtEmb (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : PolF D (Wc D i).rank (Vc D i).rank :=
  delta (pW i) (qW i) (apAt i σ) (amAt i σ)

def SameOnK (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ a : D.host.E, a ∈ D.host.K → σ (D.embE a) = D.what₂.embLL (D.embE a)

def absPow (half : Bool) (P : Pl D.host.E) (k : D.host.E) : ℂ :=
  cond half ((Real.sqrt (NumberField.FinitePlace.mk P k) : ℝ) : ℂ) 1

def IsConjChr (s : ℂ →+* ℂ) (half : Bool) (c c' : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D c' ∧ ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P →
    ∀ (k : D.host.Eˣ) (x : (AE D)ˣ), (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E) →
      ((c' x : Circle) : ℂ) * absPow half P k = s (((c x : Circle) : ℂ) * absPow half P k)

def conjRes (s : ℂ →+* ℂ) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => (Units.map s.toMonoidHom).comp (χ PP)

theorem conjRes_id (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : conjRes (RingHom.id ℂ) χ = χ := by
  funext PP; ext u; rfl

open Classical in

def omegaP {a b : ℕ} {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : ℂ :=
  if h : (∀ PP ∈ Pg, LowZero r (y PP)) ∧
      ∃ g : P.H, ∀ PP : Pg, ((g.1 PP : GL (Fin r) (kP PP.1)) : Matrix (Fin r) (Fin r) (kP PP.1)) = topL r (y PP.1) then
    ((P.chi h.2.choose : ℂˣ) : ℂ) *
      ∏ PP : Pg, ((χ PP.1 (Matrix.GeneralLinearGroup.det (h.2.choose.1 PP)) : ℂˣ) : ℂ)
  else 0

theorem omegaP_triv {a b : ℕ} (Pg : Finset (Pl D.host.E)) {r : ℕ} (hr : a = r) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaP (LevelP.triv Pg r ℂ) χ y = omegaK Pg y := by
  subst hr
  unfold omegaP omegaK
  have key : ∀ g : (LevelP.triv Pg a ℂ).H, g.1 = 1 := fun g => Subgroup.mem_bot.1 g.2
  by_cases h : ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1
  · have h' : (∀ PP ∈ Pg, LowZero a (y PP)) ∧ ∃ g : (LevelP.triv Pg a ℂ).H, ∀ PP : Pg,
        ((g.1 PP : GL (Fin a) (kP PP.1)) : Matrix (Fin a) (Fin a) (kP PP.1)) = topL a (y PP.1) :=
      ⟨fun PP hP => (h PP hP).1, 1, fun PP => by rw [(h PP.1 PP.2).2]; rfl⟩
    rw [dif_pos h', if_pos h, key]
    simp [LevelP.triv]
    rfl
  · rw [if_neg h, dif_neg]
    rintro ⟨h1, g, hg⟩
    exact h fun PP hP => ⟨h1 PP hP, by rw [← hg ⟨PP, hP⟩, key]; rfl⟩

open Classical in

def IsLevelVec (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    {Pg : Finset (Pl D.host.E)} {r : ℕ} (P : LevelP Pg r ℂ) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ) : Prop :=
  IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (Pg ∪ Q) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaP P χ (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
        else 0) f

def defForms {V : HSp D} (c : CoefA V) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Submodule ℂ (GA D V → c.W) where
  carrier := {f | (∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h) ∧ (∀ u ∈ GinfC V, ∀ h, f (h * u) = c.ρ u⁻¹ (f h)) ∧
    ∀ κ ∈ levG V β L, ∀ h, f (h * κ) = levChi V β L κ • f h}
  add_mem' := by
    rintro f g ⟨f1, f2, f3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun γ hγ h => ?_, fun u hu h => ?_, fun κ hκ h => ?_⟩
    · simp only [Pi.add_apply, f1 γ hγ, g1 γ hγ]
    · simp only [Pi.add_apply, f2 u hu, g2 u hu, map_add]
    · simp only [Pi.add_apply, f3 κ hκ, g3 κ hκ, smul_add]
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro a f ⟨f1, f2, f3⟩
    refine ⟨fun γ hγ h => ?_, fun u hu h => ?_, fun κ hκ h => ?_⟩
    · simp only [Pi.smul_apply, f1 γ hγ]
    · simp only [Pi.smul_apply, f2 u hu, map_smul]
    · simp only [Pi.smul_apply, f3 κ hκ, smul_comm a]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def GoodPlaces (R : RealDat D A Ks) (t : T) : Prop :=
  ∀ PP : Pl D.host.E, PP ∈ R.Pg ∨ PP ∈ R.Q t →
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

open Classical in

def finS (R : RealDat D A Ks) (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => PP.under (𝓞 D.host.F)

def levV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (s : ℂ →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) :
    LevDat D.host.E ℂ (Vc D i).rank where
  r := D.R.r
  hr := r_le_V i
  t := D.R.t
  s := 1
  Pg := R.Pg
  Q := R.Q t
  P := P
  cg := fun _ PP => (conjRes s (R.chi ((i : ℕ) + 1)) PP)⁻¹
  xq := conjRes s (R.xiR t)

def typeVec (R : RealDat D A Ks) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) :
    Submodule ℂ (R.HW i σ).H :=
  (Mult R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))).comap (R.HW i σ).e

def typePart (R : RealDat D A Ks) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (t : T) (P : LevelP R.Pg D.R.r ℂ)
    (c : Pl D.host.E → List ℤ → ℂ) : Submodule ℂ (R.HW i σ).H :=
  (partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) (finS R t) c).comap (R.HW i σ).e

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure LiftInput (R : RealDat D A Ks) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) where

  mu : (AE D)ˣ →* Circle

  eta : (AE D)ˣ →* Circle

  om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)

  BV : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ

  BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ

  vac : WO (Vc D i) (Wc D i) → ℂ

  vec : WO (Vc D i) (Wc D i) → ℂ

  coef : CoefA (Vc D i)

  io : LowT (R.MW i σ) →ₗ[ℂ] coef.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank

  ν : Measure (GA D (Vc D i))

  fd : Set (GA D (Vc D i))

namespace LiftInput

variable {R : RealDat D A Ks} {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (X : LiftInput R i σ)

def pt : PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) X.BV X.BW X.vec

structure Is (t : T) (s : ℂ →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) : Prop where
  mu : IsConjChr s false (R.toLevCh.mu t ((i : ℕ) + 1)) X.mu
  eta : IsConjChr s true R.eta X.eta
  om : IsWeilDatumO R.ψ (Vc D i) (Wc D i) X.mu (X.mu * X.eta⁻¹) X.om
  BV : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 (X.BV τ) (Vc D i).rank
  BW : ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i σ) τ) (X.BW τ) (pW i τ)
  vec : IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) P
    (conjRes s (R.chi ((i : ℕ) + 1))) (R.Q t) (conjRes s (R.xiR t)) X.vac X.vec
  coef : X.coef.Is
  io : IsIoW R.θ (R.MW i σ) X.coef X.om X.pt (deltaAtEmb i σ) X.io
  meas : IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (levV R i t s P)) X.ν X.fd

abbrev src (t : T) (s : ℂ →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (GA D (Vc D i) → X.coef.W) :=
  defForms X.coef (R.βV i) (levV R i t s P)

variable {t : T} {s : ℂ →+* ℂ} {P : LevelP R.Pg D.R.r ℂ}

def IsLift (th : X.src t s P →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ∃ thP, Lift.IsThetaP X.ν X.fd (fun g h f => thetaKO X.om h g f) X.pt X.io (X.src t s P) thP ∧
    ∀ (f : X.src t s P) (v : ∀ ρ, lowT (R.MW i σ) ρ),
      (R.HW i σ).e (th f) (fun ρ => v ρ) = thP f (PiTensorProduct.tprod ℂ v)

def IsAdjVal (th : X.src t s P →ₗ[ℂ] (R.HW i σ).H) (U : (R.HW i σ).H) (f : X.src t s P) : Prop :=
  ∀ f' : X.src t s P,
    IntegrableOn (fun h => ⟪(f' : GA D (Vc D i) → X.coef.W) h, (f : GA D (Vc D i) → X.coef.W) h⟫_ℂ) X.fd X.ν ∧
      ((Nat.card P.H : ℂ))⁻¹ * ⟪th f', U⟫_ℂ =
        ∫ h in X.fd, ⟪(f' : GA D (Vc D i) → X.coef.W) h, (f : GA D (Vc D i) → X.coef.W) h⟫_ℂ ∂X.ν

def ActsBy (th : X.src t s P →ₗ[ℂ] (R.HW i σ).H) (N : Submodule ℂ (R.HW i σ).H) (l : ℝ) : Prop :=
  ∀ U ∈ N, ∃ f : X.src t s P, X.IsAdjVal th U f ∧ th f = (l : ℂ) • U

end LiftInput

def ScalarBoundAt (R : RealDat D A Ks) (b : ℝ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ →+* ℂ) (t : T) : Prop :=
  ∃ lam : (Pl D.host.E → List ℤ → ℂ) → ℝ,
    ∀ (P : LevelP R.Pg D.R.r ℂ) (X : LiftInput R i σ), X.Is t s P →
      (∃ th : X.src t s P →ₗ[ℂ] (R.HW i σ).H, X.IsLift th) ∧
      ∀ th : X.src t s P →ₗ[ℂ] (R.HW i σ).H, X.IsLift th →
        (∀ f, th f ∈ typeVec R i σ P) ∧
        ∀ c, typePart R i σ t P c ≠ ⊥ →
          X.ActsBy th (typePart R i σ t P c) (lam c) ∧ 0 < lam c ∧
            mainTerm i σ - 8 * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lpr D b) ≤ Real.log (lam c)

def AdelicLiftScalarBound (R : RealDat D A Ks) (F : Face D A) (b : ℝ) : Prop :=
  R.Char F → Sizes D b → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ →+* ℂ) (t : T),
    SameOnK σ → s.comp D.what₂.embLL = σ → GoodPlaces R t → ScalarBoundAt R b i σ s t

def LiftInputExists (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ →+* ℂ) (t : T),
    SameOnK σ → s.comp D.what₂.embLL = σ → GoodPlaces R t → ∀ P : LevelP R.Pg D.R.r ℂ, ∃ X : LiftInput R i σ, X.Is t s P

def ofReal (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : LiftInput R i (sg0 D A) where
  mu := R.toLevCh.mu t ((i : ℕ) + 1)
  eta := R.eta
  om := R.ωP i t
  BV := R.BV i
  BW := onb (R.MW i (sg0 D A))
  vac := R.vacP i
  vec := R.vP i t
  coef := R.cV i
  io := R.ioP i
  ν := R.νV i t
  fd := R.fdV i t

theorem isConjChr_id (half : Bool) {c : (AE D)ˣ →* Circle} (hc : IsHeckeChar D c) : IsConjChr (RingHom.id ℂ) half c c :=
  ⟨hc, fun _ _ _ _ _ _ => rfl⟩

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem lab_base (ρ : D.what₂.Tau) : lab D.what₂.embLL ρ = ρ := by
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (labE_base ρ)⟩
  unfold lab
  rw [dif_pos h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rw [labE_base] at hs
  rcases hs with hs | hs
  · have h1 : D.host.sigmaOf (D.eTau τ).1 = D.host.sigmaOf (D.eTau ρ).1 :=
      AlgEquiv.ext fun x => D.host.φ₀.injective (DFunLike.congr_fun hs x)
    apply D.eTau.injective
    apply Subtype.ext
    exact (by unfold Host.sigmaOf at h1; exact (EquivLike.injective _) h1)
  · exfalso
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem isONBasis_onb {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (p : ℕ)
    (h : ∀ a, M.ε τ a = decide ((a : ℕ) < p)) : IsONBasis (gramAt D V τ) (cart M τ) (onb M τ) p := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hJ : (Matrix.diagonal fun a => (((if M.ε τ a = true then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm (M.ε τ) := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    split_ifs <;> simp
  refine ⟨fun a => if M.ε τ a = true then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : (a : ℕ) < p
    · left; simp [h a, ha]
    · right; simp [h a, ha, Nat.le_of_not_lt ha]
  · rw [hJ, ← M.fr_gram τ, onb]
    have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹
        = (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  · rw [hJ, cart, onb, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem ofReal_is {R : RealDat D A Ks} {F : Face D A} (h : R.Char F) (i : Fin D.R.m) (t : T) :
    (ofReal R i t).Is t (RingHom.id ℂ) R.triv where
  mu := isConjChr_id _ (h.thP.ωP i t).hecS
  eta := isConjChr_id _ h.lev.eta.1
  om := h.thP.ωP i t
  BV := h.models.BV i
  BW := fun τ => isONBasis_onb _ τ _ (h.models.order i τ)
  vec := by
    have h1 := h.thP.vP i t
    unfold IsThPVecOf at h1
    unfold IsLevelVec
    simp only [conjRes_id, omegaP_triv R.Pg (D.sp.W_rank _ (Nat.le_add_left _ _) i.2)]
    exact h1
  coef := h.models.cV i
  io := by
    have e : deltaAtEmb i (sg0 D A) = RealDat.Delta i := by
      have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
        rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact lab_base ρ
      unfold deltaAtEmb RealDat.Delta
      congr 1 <;> funext ρ
      · unfold apAt; rw [hl]
      · unfold amAt; rw [hl]
    rw [e]
    exact h.thP.ioP i t
  meas := h.models.νV i t

end GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm

end
