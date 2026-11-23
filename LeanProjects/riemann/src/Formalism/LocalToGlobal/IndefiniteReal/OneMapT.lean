import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

noncomputable section

open NumberField
open scoped TensorProduct

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev inC {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} (c' : Coeff l) : c'.F →+* ℂ := c'.F.val.toRingHom

abbrev sOv (C : Core D) (c' : Coeff C.Q.l) (hle : C.Q.c.F ≤ c'.F) : C.Q.c.F →+* ℂ := (inC c').comp (incF C.Q.c c' hle)

theorem sOv_eq (C : Core D) (c' : Coeff C.Q.l) (hle : C.Q.c.F ≤ c'.F) : sOv C c' hle = C.σ₀ := by
  first
  | rfl
  | (ext x; rfl)
  | (ext x; simp [sOv, inC, incF])

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in

structure OMDat (C : Core D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) : Type 1 where
  c' : Coeff C.Q.l
  hle : C.Q.c.F ≤ c'.F
  jL : D.what₂.LL →+* c'.F
  hV : C.V ((i : ℕ) + 1) (sOv C c' hle) = Wc D i
  c0' : VsV D i c'.F →ₛₗ[inC c'] (R.cV i).W
  lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La
  dδ : Tp → DeltaDat (C.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank
  Cl' : Tp → Type
  [fCl : ∀ t, Fintype (Cl' t)]
  bad : Tp → ℕ
  Lh : ∀ t, Cl' t → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)
  La : ∀ t, Cl' t → GenLat D.host.E (Vc D i).rank
  Nc : ∀ t, Cl' t → ℕ
  gam : ∀ t, Cl' t → ℕ
  vol : Tp → c'.F
  ep : ∀ t, Cl' t → c'.F
  B : Tp → Ideal (𝓞 D.host.E) → c'.F
  epF : Tp → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E) → c'.F
  io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F
  hw : VsV D i c'.F
  φ : ∀ t, (Fin (Vc D i).rank → LevQc (C.Q.Dw ((i : ℕ) + 1)) (dδ t).l₂) → c'.F
  w : ∀ t, Cl' t → (Fin (Vc D i).rank → LevQ (C.Q.Dw ((i : ℕ) + 1)) (dδ t).l₂) → c'.F
  U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((inC c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) D.R.r
  dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r
  xi : Tp → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  thAd : ∀ t, (Cl' t → VsV D i c'.F) → AutQ (Wc D i) → ℂ
  Plc : ∀ t, (Cl' t → VsV D i c'.F) → Prop

attribute [instance] OMDat.fCl

namespace OMDat

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup)

abbrev s0 : C.Q.c.F →+* ℂ := sOv C O.c' O.hle

abbrev lev2 (g : G) := (O.lev g, (LinearMap.id : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La))

abbrev dict := castDict O.hV (C.dict ((i : ℕ) + 1) O.s0)

abbrev mu : GA D (Wc D i) → ℂ := castDict O.hV (C.mu ((i : ℕ) + 1) O.s0)

def phi (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adel (Wc D i) O.dict (muPin (Wc D i) O.dict O.mu cc) (rdU (C.U ((i : ℕ) + 1) O.s0) f)

variable (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def EquivAt (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k →
    ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n, actLev C.Q.c O.lev2 g f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n ∧ ∀ h,
      O.phi cc (actLev C.Q.c O.lev2 g f) h =
        (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)) * O.phi cc f (h * k)

def PhRat (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  ∀ x : A.fam.amb.FL i A.μ0, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
    ph * (R.HW i (sg0 D A)).e (R.thG i A.μ0 (jVx R i A.μ0 x)) v₀ h =
      ∑ k, D.what₂.embLL (a k) * ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cc (f k : C.R ((i : ℕ) + 1)) h)

structure Pins (v₀ : (R.MW i (sg0 D A)).Vec)
    (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop where
  lift : ThPinsR R i O.jL (inC O.c') v₀ O.c0' ι C.Q.l.M (Mfr C.Q.l) O.lev
  tuple : ∀ t, ThPinsT R i (inC O.c') (tup t) v₀ O.c0' ι (O.bad t) C.Q.l.Mb (O.dδ t).I (Mfr (O.dδ t).l₂ • ⊤) (O.Lh t) (O.gam t)
    (O.vol t) (O.B t) (O.xi t) (O.φ t) (O.thAd t) (O.Plc t)
  act : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2 ∧ ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2
  bad : ∀ t, 0 < O.bad t ∧ BadPin (O.bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1)
  reps : RepsCov (C.Q.Xo ((i : ℕ) + 1)) O.c' O.Cl' O.dδ O.bad O.Lh O.La O.Nc O.gam
  ep : ∀ t, (∀ k, O.ep t k = O.epF t (O.Lh t k)) ∧ EpIs (Dw := C.Q.Dw ((i : ℕ) + 1)) O.c' (O.bad t) (O.B t) (O.epF t)
  io : IoLFRec O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (wtA κ) O.io O.hw
  w : WPin (C.Q.Xo ((i : ℕ) + 1)) O.c' O.Cl' O.dδ O.φ O.w
  cov : CovPin (C.Q.Xo ((i : ℕ) + 1)) O.c' O.dδ
  cxi : CXiVal (Wc D i) (rank_Wc i) (inC O.c') O.dδ O.U₂ O.dict₂ ι x₀ O.xi
  model₂ : ∀ t k, ModelW (Wc D i) (rank_Wc i) ((O.U₂ t).X k)

def OneMapOf (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  O.EquivAt κ cc ∧
    OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (C.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA κ)
      (actLev C.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc cc ph ∧
    O.PhRat κ v₀ cc ph

theorem exists_choice (v₀ : (R.MW i (sg0 D A)).Vec) : ∃ (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ),
    (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ ((∃ cc' ph', O.OneMapOf κ v₀ cc' ph') → O.OneMapOf κ v₀ cc ph) := by
  by_cases hex : ∃ cc ph, O.OneMapOf κ v₀ cc ph
  · obtain ⟨cc, ph, hO⟩ := hex
    have hO' := hO
    obtain ⟨_, hT, _⟩ := hO'
    first | unfold OneMapTieC at hT | skip
    have hR := hT.2.2.2
    first | unfold OneMapRow at hR | skip
    exact ⟨cc, ph, hR.1, hR.2.1, fun _ => hO⟩
  · exact ⟨fun _ => 1, 1, fun _ => by simp, by simp, fun h => absurd h hex⟩

end OMDat

def QHalf {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ t, ∀ PP ∈ R.Q t, ∀ PP' ∈ R.Q t, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def QGuard {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  QHalf R ∧ ∀ t, ∀ PP ∈ R.Q t, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

def iotaW (i : Fin D.R.m) : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def OMPins (i : Fin D.R.m) : Prop :=
  (O i).c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧ (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) (O i).s0)

def OneMapRow0 (i : Fin D.R.m) : Prop := ∃ cc ph, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph

def PhaseTie (ph : Fin D.R.m → ℂ) (i : Fin D.R.m) : Prop :=
  OneMapRow0 T R κ v₀ O i → (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) (ph i)

def OneMapRowR (ph : Fin D.R.m → ℂ) (i : Fin D.R.m) : Prop :=
  OneMapRow0 T R κ v₀ O i ∧
    (QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
      O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧
        O'.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O'.s0) (ph i))

theorem phi_cE (i : Fin D.R.m) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) f h =
      ((O i).hV ▸ T.phiJ ((i : ℕ) + 1) (O i).s0 a f : GA D (Wc D i) → ℂ) h := by
  have key : ∀ (σ : T.Q.c.F →+* ℂ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (g : GA D W),
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) f) g = (hV ▸ T.phiJ ((i : ℕ) + 1) σ a f : GA D W → ℂ) g := by
    intro σ W hV g
    subst hV
    rfl
  exact key _ _ (O i).hV h

end Comparison₂

end Formalism.IndefR.FWT
