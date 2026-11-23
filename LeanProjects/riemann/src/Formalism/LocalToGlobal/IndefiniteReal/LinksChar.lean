import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Char

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}

open Classical in

def IsDualPair {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (c : CoefA V)
    (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) : Prop :=
  pr ≠ 0 ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (w : c.W) (v : M.Vec) (u : M.sm τ), (u : M.H τ) = M.rep τ g (v τ) →
    pr (c.ρ (atTau θ V τ g) w) (PiTensorProduct.tprod ℂ (Function.update v τ u)) = pr w (PiTensorProduct.tprod ℂ v)

open Classical in

def IsIoW {V W : HSp D} {S' : D.what₂.Tau → SPar} (θ : InfFam D) (M' : DSModel W S') (c : CoefA V)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ))
    (Δ : PolF D W.rank V.rank) (io : LowT M' →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank) : Prop :=
  (∀ u ∈ GinfC V, ∀ x w, ω (u, 1) (pt (io x w)) = pt (io x (c.ρ u w))) ∧
  (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ (v : ∀ ρ, lowT M' ρ) (u : lowT M' τ),
    ((u : M'.sm τ) : M'.H τ) = M'.σ τ k ((v τ : M'.sm τ) : M'.H τ) → ∀ w,
      ω (1, atTau θ W τ ((M'.fr τ)⁻¹ * k * M'.fr τ)) (pt (io (PiTensorProduct.tprod ℂ v) w)) =
        pt (io (PiTensorProduct.tprod ℂ (Function.update v τ u)) w)) ∧
  ∃ (v : ∀ ρ, lowT M' ρ) (w : c.W), (∀ ρ, ‖((v ρ : M'.sm ρ) : M'.H ρ)‖ = 1) ∧ ‖w‖ = 1 ∧ io (PiTensorProduct.tprod ℂ v) w = Δ

section It

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

def inclT : SmT M →ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.map fun τ => (M.sm τ).subtype

open Classical in

def actT (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : (⨂[ℂ] ρ, M.H ρ) →ₗ[ℂ] ⨂[ℂ] ρ, M.H ρ :=
  PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ))

def ellT (w : ∀ τ, M.H τ) : (⨂[ℂ] ρ, M.H ρ) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap fun ρ => innerₛₗ ℂ (w ρ))

def DerT (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x y : SmT M) : Prop :=
  ∀ w, HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (inclT M x))) (ellT M w (inclT M y)) 0

end It

structure IsItW {V W : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ))
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) : Prop where
  ne : It ≠ 0
  bdd : ∀ φ w, ∃ c : ℝ, ∀ v : M'.Vec,
    ‖ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v)))‖ ≤ c * ∏ τ, ‖(v τ : M'.H τ)‖
  eqK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ φ', pt φ' = ω (atTau θ V τ g, 1) (pt φ) →
    ∀ v, inclT M (It φ' v) = actT M τ g (inclT M (It φ v))
  eqg : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (pt φ) z) (pt φ' z) 0) →
    ∀ v, DerT M τ X (It φ v) (It φ' v)
  invK : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ φ' v v', pt φ' = ω (1, atTau θ W τ h) (pt φ) →
    inclT M' v' = actT M' τ h (inclT M' v) → It φ' v' = It φ v
  invg : ∀ τ, ∀ X ∈ lieAt W τ, ∀ φ φ' v v', (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ X t) (pt φ) z) (pt φ' z) 0) →
    DerT M' τ X v v' → It φ' v + It φ v' = 0

def IsSymOrd {r : ℕ} (ρ k : ℕ) (π : Equiv.Perm (Fin r)) : Prop :=
  ∀ a : Fin r, (π a : ℕ) = if (a : ℕ) < ρ then k + a else if (a : ℕ) < ρ + k then a - ρ else a

def reord {Pg : Finset (Pl D.host.E)} {r : ℕ} (π : Equiv.Perm (Fin r)) (g : G0 Pg r) : G0 Pg r :=
  fun PP => Units.map (Matrix.reindexAlgEquiv (kP PP.1) (kP PP.1) π.symm).toMonoidHom (g PP)

namespace RealDat

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def Delta (i : Fin D.R.m) : PolF D (Wc D i).rank (Vc D i).rank :=
  delta (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => ((Wc D i).sig (tauE D τ)).2)
    (fun τ => aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (fun τ => aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ)

def ptP (i : Fin D.R.m) (t : T) : PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t)

def ptY (t : T) (k : ℕ) : PolF D (Yc D (k + 1)).rank (Yc D k).rank → (WO (Yc D k) (Yc D (k + 1)) → ℂ) :=
  pureTensorO R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (onb (R.MY k)) (onb (R.MY (k + 1))) (R.vY t k)

def ptX (t : T) : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank → (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ) :=
  pureTensorO R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (onb (R.MY (D.R.m - 1))) (onb R.MX) (R.vX t)

def extV (i : Fin D.R.m) (t : T) : (R.HV i t).H →ₗ[ℂ] (GA D (Vc D i) → (R.cV i).W) := (R.cV i).ext ∘ₗ (R.HV i t).e

abbrev grp_red_R : Prop :=
  ∀ t (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q),
    R.eG ((R.B.R t).act_tie.red q) = rTup R.βX (R.datXt t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf D.sp.X') : GL _ _))

abbrev grp_red_L : Prop :=
  ∀ i t (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q),
    R.eG ((R.B.L i t).act_tie.red q) = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _))

abbrev grp_levels : Prop :=
  ∃ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi R.Pg ψ0 ∧ R.levR F false = P0 R.Pg D.R.r ψ0 ∧
    ∃ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π ∧
      (∀ g, g ∈ (R.levR F true).H ↔ reord π g ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧
      ∀ g hg hg', (R.levR F true).chi ⟨g, hg⟩ = (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨reord π g, hg'⟩

abbrev grp_record : Prop :=
  ∃ (eR : G ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧
      ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

abbrev grp_chiW : Prop :=
  ∀ (i : Fin D.R.m) g, D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) =
    ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)

structure IsGrp : Prop where
  red_R : R.grp_red_R
  red_L : R.grp_red_L
  levels : R.grp_levels F
  record : R.grp_record
  chiW : R.grp_chiW

abbrev fam_tie : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

abbrev fam_Sb : Prop :=
  R.Pg ⊆ R.Sb

abbrev fam_roots : Prop :=
  ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))

abbrev fam_pl_onto : Prop :=
  ∀ PP, Bridge.SplitOff PP (R.Sb : Set (Pl D.host.E)) → ∃ P, R.pl P = PP

abbrev fam_degR : Prop :=
  ∀ t P, A.heckeR t (P, 0) = 1 ∧ ∀ k, D.sp.X'.rank < k → A.heckeR t (P, k) = 0

abbrev fam_degL : Prop :=
  ∀ i t P, A.heckeL i t (P, 0) = 1 ∧ ∀ k, (Vc D i).rank < k → A.heckeL i t (P, k) = 0

abbrev fam_muVal : Prop :=
  ∀ (i : Fin D.R.m) t, ∀ P ∈ A.ok t,
    D.what₂.embLL (A.muVal i t P : D.what₂.LL) = (((R.C.mu0 i * R.xiH t).val (R.pl P) : ℂˣ) : ℂ)

abbrev fam_etaVal : Prop :=
  ∀ P ∈ A.ok A.μ0, D.what₂.embLL (A.etaVal P : D.what₂.LL) = Formalism.L2.Host.etaAlg D.host R.C.eta (R.pl P)

structure IsFam : Prop where
  tie : R.fam_tie
  Sb : R.fam_Sb
  roots : R.fam_roots
  pl_onto : R.fam_pl_onto
  degR : fam_degR (A := A)
  degL : fam_degL (A := A)
  muVal : R.fam_muVal
  etaVal : R.fam_etaVal

abbrev models_inf : Prop :=
  IsInfFam R.θ

abbrev models_vpos : Prop :=
  ∀ i, (Vc D i).IsPosDef

abbrev models_cX : Prop :=
  R.cX.Is

abbrev models_cV : Prop :=
  ∀ i, (R.cV i).Is

abbrev models_prX : Prop :=
  IsDualPair R.θ R.MX R.cX R.prX

abbrev models_HX : Prop :=
  ∀ t, (R.HX t).Is (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J (levEnv _ R.βX (R.datXt t)).χ)
    (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y)

abbrev models_HV : Prop :=
  ∀ i t, (R.HV i t).Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ)
    (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y)

abbrev models_HE : Prop :=
  R.HE.Is (R.EEat R.triv) (ipM (R.MY 0) R.ν0 R.fd0)

abbrev models_HW : Prop :=
  ∀ i σ, (R.HW i σ).Is (R.Wall i σ) (ipAt (R.MW i σ) (R.νW i) (R.fdW i))

abbrev models_gE : Prop :=
  ∀ g x, R.HE.e (R.gE g x) = postOn _ (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) (R.HE.e x)

abbrev models_gW : Prop :=
  ∀ i σ g x, (R.HW i σ).e (R.gW i σ g x) = postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x)

abbrev models_jX : Prop :=
  ∀ t x, (R.HX t).e (R.jX t x) = R.B.jR t x

abbrev models_jV : Prop :=
  ∀ i t x, (R.HV i t).e (R.jV i t x) = R.B.jL i t x

abbrev models_νY : Prop :=
  ∀ t j, j + 1 < D.R.m → IsMeasFD (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)

abbrev models_νY' : Prop :=
  ∀ t, IsMeasDef (Yc D (D.R.m - 1)) (lev D.sp.cm (Yc D (D.R.m - 1)).gram (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv))
    (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1))

abbrev models_ν0 : Prop :=
  IsMeasFD (Yc D 0) (lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) R.ν0 R.fd0

abbrev models_νX : Prop :=
  ∀ t, IsMeasDef D.sp.X' (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) (R.νX t) (R.fdX t)

abbrev models_νV : Prop :=
  ∀ i t, IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) (R.νV i t) (R.fdV i t)

abbrev models_νW : Prop :=
  ∀ i, IsMeasFD (Wc D i) (lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv)) (R.νW i) (R.fdW i)

abbrev models_BV : Prop :=
  ∀ i τ, IsONBasis (gramAt D (Vc D i) τ) 1 (R.BV i τ) (Vc D i).rank

abbrev models_order : Prop :=
  ∀ i τ a, (R.MW i (sg0 D A)).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)

structure IsModels : Prop where
  inf : R.models_inf
  vpos : models_vpos (D := D)
  cX : R.models_cX
  cV : R.models_cV
  prX : R.models_prX
  HX : R.models_HX
  HV : R.models_HV
  HE : R.models_HE
  HW : R.models_HW
  gE : R.models_gE
  gW : R.models_gW
  jX : R.models_jX
  jV : R.models_jV
  νY : R.models_νY
  νY' : R.models_νY'
  ν0 : R.models_ν0
  νX : R.models_νX
  νV : R.models_νV
  νW : R.models_νW
  BV : R.models_BV
  order : R.models_order

abbrev chain_ωY : Prop :=
  ∀ t k, k + 1 < D.R.m → IsWeilDatumO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k)

abbrev chain_ωX : Prop :=
  ∀ t, IsWeilDatumO R.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (R.ωX t)

abbrev chain_vY : Prop :=
  ∀ t k, k + 1 < D.R.m → IsStepVecOf R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1))
    (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) (R.vY t k)

abbrev chain_vX : Prop :=
  ∀ t, IsStepVecOf R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX
    (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) R.vacX (R.vX t)

abbrev chain_ptY : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ P, IsThetaFunO R.ψ (Yc D k) (Yc D (k + 1)) (R.ptY t k P)

abbrev chain_ptX : Prop :=
  ∀ t P, IsThetaFunO R.ψ (Yc D (D.R.m - 1)) D.sp.X' (R.ptX t P)

abbrev chain_ItY : Prop :=
  ∀ t k, k + 1 < D.R.m → IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t k) (R.ptY t k) (R.ItY k)

abbrev chain_ItX : Prop :=
  ∀ t, IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t) (R.ptX t) R.ItX

abbrev chain_ioY : Prop :=
  ∀ t, Lift.IsChainIo (R.CC t) (D.R.m - 1) (R.νY t) (R.fdY t) (fun k => thetaKO (R.ωY t k)) (R.ptY t) R.ItY (R.ioY t)

abbrev chain_ioX : Prop :=
  ∀ t, Lift.IsIo (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t) R.ItX _ _ (R.ioX t)

abbrev chain_Th : Prop :=
  ∀ t x, R.HE.e (R.Th t x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x))

structure IsChain : Prop where
  ωY : R.chain_ωY
  ωX : R.chain_ωX
  vY : R.chain_vY
  vX : R.chain_vX
  ptY : R.chain_ptY
  ptX : R.chain_ptX
  ItY : R.chain_ItY
  ItX : R.chain_ItX
  ioY : R.chain_ioY
  ioX : R.chain_ioX
  Th : R.chain_Th

abbrev thP_ωP : Prop :=
  ∀ i t, IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t)

abbrev thP_vP : Prop :=
  ∀ i t, IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg (R.Q t) (R.xiR t) (R.vacP i) (R.vP i t)

abbrev thP_pt_theta : Prop :=
  ∀ i t P, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ptP i t P)

abbrev thP_ioP : Prop :=
  ∀ i t, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (Delta i) (R.ioP i)

abbrev thP_thF_mem : Prop :=
  ∀ i t x, R.thF i t x ∈ R.Wall i (sg0 D A)

abbrev thP_thF : Prop :=
  ∀ i t, ∃ thP, Lift.IsThetaP (R.νV i t) (R.fdV i t) (fun g h f => thetaKO (R.ωP i t) h g f) (R.ptP i t) (R.ioP i)
      (LinearMap.range (R.extV i t)) thP ∧
    ∀ x (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
      R.thF i t x (fun ρ => v ρ) = thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

abbrev thP_thG : Prop :=
  ∀ i t x, (R.HW i (sg0 D A)).e (R.thG i t x) = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x)

structure IsThP : Prop where
  ωP : R.thP_ωP
  vP : R.thP_vP
  pt_theta : R.thP_pt_theta
  ioP : R.thP_ioP
  thF_mem : R.thP_thF_mem
  thF : R.thP_thF
  thG : R.thP_thG

def lamN (t : T) (j : ℕ) (p : A.fam.base.Ix) : ℝ := if h : j - 1 < D.R.m then R.lam ⟨j - 1, h⟩ t p A.v0 else 1

def NonzeroIndexPlace (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ w', (w' = w ∨ w' = conjPl w) ∧ ∃ i : Fin D.R.m,
    ((R.toCx F).data F.cr false).Iw i A.μ0 w' ≠ 0 ∨ ((R.toCx F).data F.cr false).Iw i A.μ0 (conjPl w') ≠ 0 ∨
    jw ((lv (F.fc (R.toCx F).zs) false).HT i A.μ0) w' ((lv (F.fc (R.toCx F).zs) false).Tl i A.μ0) ≠ 0 ∨
    (F.Zsc (R.toCx F).zs).F0 w' i ≠ 0 ∨ (F.Zsc (R.toCx F).zs).F0 (conjPl w') i ≠ 0

def PartAt (b : Bool) (i : Fin D.R.m) (p : A.fam.base.Ix) (v : InfinitePlace D.what₂.LL) : Prop :=
  ∃ x, (R.toCx F).tC F.cr b i A.μ0 (cpt A.v0.embedding x) ∈ (R.toCx F).Wp i p ∧
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx F).zs) b).XT i A.μ0) v x x ≠ 0

abbrev eigenvalue_at_base_of_scalar : Prop :=
  ∀ i t p (l : ℝ), R.Wp i p ≠ ⊥ → (∀ x ∈ R.Wp i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) →
    R.lam i t p A.v0 = l

abbrev scal_kap : Prop :=
  ∀ κ : ℝ, Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp R.lamN κ →
    (∃ t p, R.EEp p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p ≠ 0) → R.kap = κ

abbrev scal_lam_off : Prop :=
  ∀ b i p v (l : ℝ), v ≠ A.v0 → R.PartAt F b i p v → (b = false ∨ ¬ R.PartAt F false i p v) →
    (∀ x, (R.toCx F).tC F.cr b i A.μ0 (cpt A.v0.embedding x) ∈ (R.toCx F).Wp i p → ∀ y,
      inner ℂ ((R.toCx F).wC b i v (cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec x)))
          ((R.toCx F).wC b i v (cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec y))) =
        ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx F).zs) b).XT i A.μ0) v x y) →
    R.lam i A.μ0 p v = l

abbrev eigenvalue_at_base_default_of_eq_bot : Prop :=
  ∀ i t p, R.Wp i p = ⊥ → R.lam i t p A.v0 = Real.exp ((F.Zsc (R.toCx F).zs).l6m i)

abbrev scal_lam_abs : Prop :=
  ∀ i p v, v ≠ A.v0 → (∀ b, ¬ R.PartAt F b i p v) → R.lam i A.μ0 p v = Real.exp ((F.Zsc (R.toCx F).zs).l6m i)

abbrev scal_lam_tup : Prop :=
  ∀ i t p v, v ≠ A.v0 → R.lam i t p v = R.lam i A.μ0 p v

structure IsScal : Prop where
  lam0 : R.eigenvalue_at_base_of_scalar
  kap : R.scal_kap
  lam_off : R.scal_lam_off F
  zero_part_eigenvalue_abs : R.eigenvalue_at_base_default_of_eq_bot F
  lam_abs : R.scal_lam_abs F
  lam_tup : R.scal_lam_tup

abbrev tup_tw : Prop :=
  ∀ w, R.NonzeroIndexPlace F w → w ∈ R.twPl

abbrev tup_mu_off : Prop :=
  ∀ w, w ∉ R.twPl → R.mu w = A.μ0

abbrev tup_mu_used : Prop :=
  ∀ t, t = A.μ0 ∨ ∃ w, R.mu w = t

abbrev tup_mu_ne : Prop :=
  ∀ w ∈ R.twPl, R.mu w ≠ A.μ0

abbrev tup_mu_conj : Prop :=
  ∀ w, R.mu (conjPl w) = R.mu w

abbrev tup_mu_on : Prop :=
  ∀ w ∈ R.twPl, ∃ (ψw : Formalism.L2.Host.HChar D.host.E) (Qw : Finset (Pl D.host.E)),
    Formalism.L2.Host.IsPsi (H := D.host) (Formalism.EigenvalueLevelCeiling.plc w) Qw ψw ∧ R.xiH (R.mu w) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψw

structure IsTup : Prop where
  tw : R.tup_tw F
  mu_off : R.tup_mu_off
  mu_used : R.tup_mu_used
  mu_ne : R.tup_mu_ne
  mu_conj : R.tup_mu_conj
  mu_on : R.tup_mu_on

structure Char : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F
  tup : R.IsTup F

structure RealCol where

  ζ : (F.Dc (R.toCx F).zs).Mem → T → D.what₂.LL

  sEE : (R.toCx F).EE →ₗ⋆[ℂ] (F.Sp (R.toCx F).zs).HH

variable {R F}

def RealCol.toCol (Y : RealCol R F) : CxData.CxCol (fc := F.fc) (R.toCx F) := (R.toCx F).colDef (fun u t => (Y.ζ u t)⁻¹) Y.sEE

structure RealCol.Char (Y : RealCol R F) : Prop where
  zeta : ∀ u t, ∃ n : ℕ, 0 < n ∧ Y.ζ u t ^ n = 1
  zeta0 : ∀ u, Y.ζ u A.μ0 = 1
  sE : ∀ x ∈ (R.toCx F).EEl true, ‖Y.sEE x‖ ^ 2 = (nP F true)⁻¹ * ‖x‖ ^ 2 ∧ Y.sEE x ∈ (F.Sp (R.toCx F).zs).Rw

end RealDat

end Char

end Formalism.IndefR.Links

end
