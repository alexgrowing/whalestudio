import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LogFactorialIndices.StatementSize

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def OverK (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ x : D.host.E, x ∈ D.host.K → σ (D.embE x) = D.what₂.embLL (D.embE x)

def ConjVal (σ : D.what₂.LL →+* ℂ) (a b : ℂ) : Prop := ∃ y : D.what₂.LL, D.what₂.embLL y = a ∧ σ y = b

def IsEtaConj (σ : D.what₂.LL →+* ℂ) (η η' : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D η' ∧ UnramEverywhere D η' ∧
    ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ x : (AE D)ˣ,
      (x : AE D) = Formalism.L2.JoinChr.locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) →
        ConjVal σ (((η x : Circle) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ))
          (((η' x : Circle) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ))

def hookRows (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens (((List.range n).map a).insertionSort (· ≥ ·)) List.sortedGE_insertionSort)

variable (D) in

abbrev pW (i : Fin D.R.m) (ρ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D ρ)).1

variable (D) in

abbrev qW (i : Fin D.R.m) (ρ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D ρ)).2

def logHookSum (i : Fin D.R.m) (l : D.what₂.Tau → D.what₂.Tau) : ℝ :=
  ∑ ρ, Real.log ((hookRows (pW D i ρ) (aPl D i (pW D i ρ) (l ρ)) * hookRows (qW D i ρ) (aMi D i (pW D i ρ) (qW D i ρ) (l ρ)) : ℕ) : ℝ)

def deltaConj (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : PolF D (Wc D i).rank (Vc D i).rank :=
  delta (pW D i) (qW D i) (fun ρ => aPl D i (pW D i ρ) (lab σ ρ)) (fun ρ => aMi D i (pW D i ρ) (qW D i ρ) (lab σ ρ))

variable (D) in

def gramV (i : Fin D.R.m) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E :=
  if D.sp.Vneg ((i : ℕ) + 1) then -(Vc D i).gram else (Vc D i).gram

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Datum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev levW : Subgroup (GA D (Wc D i)) := Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

structure IsConjForms (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i))
    (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H) : Prop where
  coef : c.Is
  act : ∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE →
    ∀ v, c₁ (rhoVr (labLL D) (lamV D i) γE v) = c.ρ (γ : GA D (Vc D i)) (c₁ v)
  indep : LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL (lamV D i) a)
  span : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL (lamV D i) a)) = ⊤
  pair : ∀ a b, inner ℂ (c₁ (bVV D.what₂.LL (lamV D i) a)) (c₁ (bVV D.what₂.LL (lamV D i) b)) =
    σ (pairVr (labLL D) (lamV D i) (gramV D i) (bVV D.what₂.LL (lamV D i) a) (bVV D.what₂.LL (lamV D i) b))
  model : ∃ χ' : levJ R i A.μ0 →* ℂˣ,
    (∀ k, ConjVal σ (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ)) ∧
    H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levJ R i A.μ0) χ')
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levJ R i A.μ0) (R.B.L i A.μ0).pres.y)
  base : ∀ x h, ∃ v, (R.HV i A.μ0).e (R.jV i A.μ0 x) h = c₀ v ∧ H.e (j x) h = c₁ v

def IsConjLift (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ∃ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))),
    IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧
    IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f ∧
    (∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (B ρ) (pW D i ρ)) ∧
    (∀ P, IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f P)) ∧
    IsIoW R.θ (R.MW i σ) c ω (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f)
      (deltaConj i σ) io ∧
    Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f) io
      (LinearMap.range (c.ext ∘ₗ H.e)) thP ∧
    ∀ (x : H.H) (v : ∀ ρ, lowT (R.MW i σ) ρ),
      (R.HW i σ).e (th x) (fun ρ => v ρ) = R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ v))

def IsConjDatum (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i))
    (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H)
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ChiAt R i σ μ' ∧ IsEtaConj σ R.eta η' ∧ IsConjForms R i σ c₀ c c₁ H j ∧ IsConjLift R i σ μ' η' c H th

structure HypConj (μ' η' : (AE D)ˣ →* Circle) : Prop where
  vpos : (Vc D i).IsPosDef
  sig : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1)
  lab_bij : Function.Bijective (lab (D := D) σ)
  lab_at : ∀ ρ, labE σ (lab σ ρ) = tauE D ρ
  par : ∀ ρ, parAt (Wc D i) σ ρ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ)
  gap : ∀ ρ n, n < D.R.r →
    ((D.R.t : ℚ) + 3) / 2 ≤ |Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n + (D.hc (lab σ ρ)).e i|
  mu_res : ResEta D μ' 0
  mu_inf : ∀ ρ, HasInfExp D μ' ρ (-(D.hc (lab σ ρ)).e i)
  mu_cond : ∀ x, FinUnit x → (μ' x = 1 ↔ R.mu0 ((i : ℕ) + 1) x = 1)
  eta_res : ResEta D η' 1
  eta_unr : UnramEverywhere D η'
  eta_inf : ∀ ρ, HasInfExp D η' ρ (1 / 2)

def IsCompPhase (u : GA D (Wc D i) → ℂ) (U : (R.HW i σ).H ≃ₗᵢ[ℂ] (R.HW i σ).H) : Prop :=
  (∀ h, ‖u h‖ = 1) ∧ (∀ γ ∈ GQ (Wc D i), ∀ h, u (γ * h) = u h) ∧ (∀ g ∈ GinfC (Wc D i), ∀ h, u (h * g) = u h) ∧
    (∀ k ∈ levW R i, ∀ h, u (h * k) = u h) ∧ ∀ y v h, (R.HW i σ).e (U y) v h = u h * (R.HW i σ).e y v h

structure IsCentralShift (z : G) (ζ : GA D (Wc D i)) : Prop where
  z_cent : z ∈ Subgroup.center G
  cent : ζ ∈ Subgroup.center (GA D (Wc D i))
  fin : ζ ∈ GfC (Wc D i)
  supp : ∃ e : AE D, IsIdemSum e R.Pg ∧ SuppAt e (Wc D i) ζ
  lift : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) ζ
  transl : ∀ y v h, (R.HW i σ).e (R.gW i σ z y) v h = (R.HW i σ).e y v (h * ζ)
  unitary : ∀ y y', ⟪R.gW i σ z y, R.gW i σ z y'⟫_ℂ = ⟪y, y'⟫_ℂ
  comm_fin : ∀ g y, R.gW i σ z (R.gW i σ g y) = R.gW i σ g (R.gW i σ z y)
  comm_hecke : ∀ α ∈ GfC (Wc D i), ∀ S : Finset (GA D (Wc D i)), Bridge.IsDC (levW R i) α S → ∀ y y',
    (R.HW i σ).e y' = heckeOn (R.MW i σ) S ((R.HW i σ).e y) →
      (R.HW i σ).e (R.gW i σ z y') = heckeOn (R.MW i σ) S ((R.HW i σ).e (R.gW i σ z y))

def IsRatLift (ph : ℂ) (x : A.fam.amb.FL i A.μ0) (y : Fin (R.nW i) → D.what₂.LL) : Prop :=
  (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x)

def ConjAt (ph : ℂ) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) : Prop :=
  logHookSum i (lab σ) = logHookSum i id ∧
  (∃ μ' η' c c₁ H j th, IsConjDatum R i σ c₀ μ' η' c c₁ H j th) ∧
  ∃ (u : GA D (Wc D i) → ℂ) (U : (R.HW i σ).H ≃ₗᵢ[ℂ] (R.HW i σ).H) (z : G) (ζ : GA D (Wc D i)),
    IsCompPhase R i σ u U ∧ (σ = sg0 D A → ∀ h, u h = 1) ∧ IsCentralShift R i σ z ζ ∧
    ∀ μ' η' c c₁ H j th, IsConjDatum R i σ c₀ μ' η' c c₁ H j th →
      HypConj R i σ μ' η' ∧ ∃ κ : ℂ, ‖κ‖ = 1 ∧
        ∀ x y, IsRatLift R i ph x y → U ((R.FW i).j σ y) = κ • R.gW i σ z (th (j x))

end Datum

def GalLiftFor (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) : Prop :=
  R.Char F → ∀ fw : FWTie T R κw v₀, ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → PhaseTie T R κw v₀ O ph i →
    (∀ x, ∃! y, IsRatLift R i (ph i) x y) ∧
    (∀ gramR c0R c0L,
      Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
      ∀ σ, OverK σ → ConjAt R i σ (ph i) (c0L i)) ∧
    ∀ σ, ¬ OverK σ → OverK ((starRingEnd ℂ).comp σ) ∧
      (BarTie fw → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
        starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ)

def GalLift : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), GalLiftFor T R F κw v₀ O ph

theorem overK_base : OverK (D := D) D.what₂.embLL := by
  intro x _
  exact Eq.refl _

end GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature

end
