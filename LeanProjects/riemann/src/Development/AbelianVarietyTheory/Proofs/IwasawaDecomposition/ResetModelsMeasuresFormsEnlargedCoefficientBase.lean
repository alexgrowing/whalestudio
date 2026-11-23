import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLExistsBaseChangeCoordinates
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RSideA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw

def labEE {D : D7} (e : D.host.E →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  e.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

open Classical in

def labX {D : D7} (e : D.host.E →+* ℂ) (ρ : D.what₂.Tau) : D.what₂.Tau :=
  if h : ∃ τ, labEE e τ = tauE D ρ ∨ labEE e τ = (starRingEnd ℂ).comp (tauE D ρ) then h.choose else ρ

open Classical in

def parAtE {D : D7} (W : HSp D) (e : D.host.E →+* ℂ) (ρ : D.what₂.Tau) : SPar :=
  if labEE e (labX e ρ) = tauE D ρ then
    Formalism.L2.NTheta.holPar (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 (Formalism.L2.NTheta.kapW (D.hc (labX e ρ)) _ _)
  else Formalism.IndefR.Mult.dualPar
    (Formalism.L2.NTheta.holPar (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 (Formalism.L2.NTheta.kapW (D.hc (labX e ρ)) _ _))

theorem parAt_eq_parAtE {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) : parAt W σ = parAtE W (σ.comp D.embE) := rfl

theorem exists_heq_io {L : Type} (F : L → Type) [∀ a, AddCommGroup (F a)] [∀ a, Module ℂ (F a)] {P : Type} [AddCommGroup P]
    [Module ℂ P] {a b : L} (hab : a = b) {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W]
    [nW' : NormedAddCommGroup W'] [iW' : InnerProductSpace ℂ W'] (h1 : W' = W) (h2 : HEq nW' nW) (h3 : HEq iW' iW)
    (f : F b →ₗ[ℂ] W →ₗ[ℂ] P) : ∃ f' : F a →ₗ[ℂ] W' →ₗ[ℂ] P, HEq f' f := by
  subst hab h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  exact ⟨f, HEq.rfl⟩

theorem forms_crdOver {L L' Ks : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field Ks] [NumberField Ks] [Algebra Ks L]
    [Algebra Ks L'] {ι ι₂ : L →+* L'} (hι : ι₂ = ι) {n : ℕ} {W : (L →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] {G : Type} [Group G] {F : Formalism.IndefR.Arith.FormsL L Ks (Fin n → L) W G}
    {F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G}
    (h : (∀ (σ' : L' →+* ℂ) (x : Fin n → L), F'.j σ' (fun k => ι (x k)) = F.j (σ'.comp ι) x) ∧
      (∀ x' : Fin n → L', x' ∈ F'.WK ↔ ∃ x ∈ F.WK, x' = fun k => ι (x k)) ∧
      (∀ g, ((F'.chi g : L'ˣ) : L') = ι ((F.chi g : Lˣ) : L)) ∧
      (∀ g (x : Fin n → L), F'.ρ g (fun k => ι (x k)) = fun k => ι (F.ρ g x k)) ∧
      F'.Pt = F.Pt ∧
      ∀ lp (y' : F'.Pt lp) (y : F.Pt lp), HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), (φ'.1 = fun k => ι (φ.1 k)) →
        F'.nrm lp y' φ' = F.nrm lp y φ) :
    (∀ (σ' : L' →+* ℂ) x x', CrdOver ι₂ x x' → HEq (F'.j σ' x') (F.j (σ'.comp ι₂) x)) ∧
      ((∀ x x', CrdOver ι₂ x x' → (x' ∈ F'.WK ↔ x ∈ F.WK)) ∧ ∀ x' ∈ F'.WK, ∃ x : Fin n → L, CrdOver ι₂ x x') ∧
      (∀ g' g, HEq g' g → ((F'.chi g' : L'ˣ) : L') = ι₂ ((F.chi g : Lˣ) : L)) ∧
      (∀ g' g, HEq g' g → ∀ x x', CrdOver ι₂ x x' → CrdOver ι₂ (F.ρ g x) (F'.ρ g' x')) ∧
      HEq F'.Pt F.Pt ∧
      (∀ lp' lp, HEq lp' lp → ∀ y' y, HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), CrdOver ι₂ φ.1 φ'.1 →
        F'.nrm lp' y' φ' = F.nrm lp y φ) := by
  subst hι
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hc : ∀ (x : Fin n → L) (x' : Fin n → L'), CrdOver ι₂ x x' ↔ x' = fun k => ι₂ (x k) := fun x x' =>
    ⟨fun hx => funext fun k => hx.2 k k rfl, fun hx => ⟨rfl, fun k k' e => by rw [hx, Fin.ext e]⟩⟩
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, heq_of_eq h5, ?_⟩
  · intro σ' x x' hx
    rw [(hc _ _).1 hx, h1]
  · intro x x' hx
    rw [(hc _ _).1 hx, h2]
    constructor
    · rintro ⟨y, hy, hyx⟩
      obtain rfl : x = y := funext fun k => ι₂.injective (congrFun hyx k)
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  · intro x' hx'
    obtain ⟨x, -, e⟩ := (h2 x').1 hx'
    exact ⟨x, (hc _ _).2 e⟩
  · intro g' g e
    obtain rfl := eq_of_heq e
    exact h3 g'
  · intro g' g e x x' hx
    obtain rfl := eq_of_heq e
    rw [hc, (hc _ _).1 hx, h4]
  · intro lp' lp e y' y ey φ' φ hx
    obtain rfl := eq_of_heq e
    exact h6 lp' y' y ey φ' φ ((hc _ _).1 hx)

set_option maxHeartbeats 4000000 in

theorem resetW : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
    (∀ y : core'.Q.c.F, B'.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) = (y : ℂ)) →
    HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG → RSideA z Wt' R →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideW z Wt' R₁ := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp core' alg' halg eH el ec Xg tr R cG hK hA
  obtain ⟨hPre, -, -, hLL⟩ := hE
  have hι := enlEmb_spec hLL
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := core'
  dsimp only at eH el ec
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  set D := (w.st Z).toD7 with hD
  set D' := (ColW.st _ Z').toD7 with hD'
  set ι := enlEmb hLL with hιdef
  have hιc : D'.what₂.embLL.comp ι = D.what₂.embLL := RingHom.ext hι
  have hE' : D'.embE = ι.comp D.embE := by
    ext x
    apply D'.what₂.embLL.injective
    have h1 := RingHom.congr_fun D'.embE_φ₀ x
    have h2 := RingHom.congr_fun D.embE_φ₀ x
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    exact (h1.trans h2.symm).trans (hι _).symm
  have hpar : ∀ (i : Fin D.R.m) (σ' : D'.what₂.LL →+* ℂ), parAt (Wc D' i) σ' = parAt (Wc D i) (σ'.comp ι) := by
    intro i σ'
    rw [parAt_eq_parAtE, parAt_eq_parAtE, hE']
    rfl

  let MW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), Mult.DSModel (Wc D' i) (parAt (Wc D' i) σ') := fun i σ' =>
    { z.R.MW i (σ'.comp ι) with enum := fun τ => by rw [hpar i σ']; exact (z.R.MW i (σ'.comp ι)).enum τ }
  let HW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), HMod (Mult.MMap (MW' i σ')) := fun i σ' => z.R.HW i (σ'.comp ι)
  let gW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), Representation ℂ (Gc B w.px) (HW' i σ').H := fun i σ' => z.R.gW i (σ'.comp ι)
  have hs0' := sgAt_mk _ R.hv0
  have hs0 := sgAt_mk _ z.R.hv0
  have hs := (congrArg (fun s => RingHom.comp s ι) hs0').trans (hιc.trans hs0.symm)
  have hA0 := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcV, hjL⟩ := hA
  have hio := fun i : Fin D.R.m =>
    exists_heq_io (fun σ => LowT (z.R.MW i σ)) hs (eq_of_heq (hcV i i rfl).1) (hcV i i rfl).2.2.1 (hcV i i rfl).2.2.2 (z.R.ioP i)
  choose ioP' hioP using hio
  letI := z.alg
  have halgι : ∀ y : z.core.Q.c.F, ι (algebraMap z.core.Q.c.F D.what₂.LL y) = algebraMap z.core.Q.c.F D'.what₂.LL y := by
    intro y
    apply D'.what₂.embLL.injective
    exact (hι _).trans ((z.alg_eq y).trans (halg y).symm)
  have hfw := fun i : Fin D.R.m => GlobalTheory.formsL_exists_baseChange_coordinates (L := D.what₂.LL) (L' := D'.what₂.LL) ι halgι (z.R.nW i) (fun σ => (z.R.HW i σ).H) _ (z.R.FW i)
  choose FW' hFW using hfw
  let R₁ : RealDat3 D' _ z.core.Q.c.F :=
    { R with
      MW := MW'
      HW := HW'
      gW := gW'
      νW := (fun i => z.R.νW i)
      fdW := (fun i => z.R.fdW i)
      vacP := (fun i => z.R.vacP i)
      BV := (fun i => z.R.BV i)
      ioP := ioP'
      nW := z.R.nW
      FW := FW'
      thF := (fun _ _ => 0)
      thG := (fun _ _ => 0) }
  refine ⟨R₁, cG, ?_, ?_⟩
  · obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := hK
    have f6 := k6.fam
    refine ⟨k1, k2, k3, k4, k5,
      { k6 with fam := ⟨f6.tie, f6.Sb, f6.roots, f6.pl_onto, f6.degR, f6.degL, f6.muVal, f6.etaVal⟩, order := ?hord },
      ⟨k7.tie, k7.onto, k7.hR, k7.hL, k7.SF⟩, ⟨k8.mu_off, k8.mu_used, k8.mu_ne, k8.mu_conj, k8.mu_on⟩, k9,
      { k10 with frameKs := ⟨?hfk1, ?hfk2⟩ }, k11⟩
    case hord =>
      intro i τ a
      have e := z.pins.char.base.models.order i τ a
      exact (congrArg (fun s => (z.R.MW i s).ε τ a) hs).trans e
    case hfk1 =>
      intro i σ σ' h ρ
      have h' : (σ.comp ι).comp (algebraMap z.core.Q.c.F D.what₂.LL) = (σ'.comp ι).comp (algebraMap z.core.Q.c.F D.what₂.LL) := by
        ext y
        have := RingHom.congr_fun h y
        show σ (ι (algebraMap _ D.what₂.LL y)) = σ' (ι (algebraMap _ D.what₂.LL y))
        rw [halgι]
        exact this
      exact z.pins.keep.frameKs.1 i (σ.comp ι) (σ'.comp ι) h' ρ
    case hfk2 =>
      intro i σ h τ a
      have h'' : ∀ ρ, labE (σ.comp ι) (lab (σ.comp ι) ρ) = tauE D ρ := by
        intro ρ
        have e : labEE (D := D') (σ.comp D'.embE) (labX (D := D') (σ.comp D'.embE) ρ) = tauE D' ρ := h ρ
        rw [hE'] at e
        exact e
      exact z.pins.keep.frameKs.2 i (σ.comp ι) h'' τ a
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -, -⟩ := hA0
    have hinj : Function.Injective ι := ι.injective
    refine ⟨a1, a2, a3, a4, a5, HEq.rfl, a6, a7, a8, a9, a10, a11, ?blk, hjL⟩
    rintro i ⟨i', hi'⟩ e
    dsimp only at e
    subst e
    refine ⟨(hcV i i rfl).1, (hcV i i rfl).2.1, (hcV i i rfl).2.2.1, (hcV i i rfl).2.2.2, HEq.rfl, hioP i, HEq.rfl,
      congr_arg_heq (fun s => (z.R.MW i s).H) hιc, congr_arg_heq (fun s => (z.R.MW i s).nacg) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).ips) hιc, congr_arg_heq (fun s => (z.R.MW i s).σ) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).lam) hιc, congr_arg_heq (fun s => (z.R.MW i s).ε) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).fr) hιc, proof_irrel_heq _ _, congr_arg_heq (z.R.HW i) hιc, HEq.rfl, HEq.rfl, ?rest⟩
    intro ι₂ hι₂
    have hιι : ι₂ = ι := RingHom.ext fun x => D'.what₂.embLL.injective ((hι₂ x).trans (hι x).symm)
    have hσ : ∀ σ' : D'.what₂.LL →+* ℂ, σ'.comp ι = σ'.comp ι₂ := fun σ' => congrArg σ'.comp hιι.symm
    have hF := forms_crdOver (L := D.what₂.LL) (L' := D'.what₂.LL) (n := z.R.nW i) (W := fun σ => (z.R.HW i σ).H) (F := z.R.FW i)
      (F' := FW' i) hιι (hFW i)
    refine ⟨fun σ' => ⟨⟨congr_arg_heq (fun s => (z.R.MW i s).H) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).nacg) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).ips) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).σ) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).lam) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).ε) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).fr) (hσ σ'), proof_irrel_heq _ _⟩,
        congr_arg_heq (z.R.HW i) (hσ σ'), congr_arg_heq (z.R.gW i) (hσ σ'), hF.1 σ'⟩,
      hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2⟩

end GlobalTheory.Mem.R3.Rw
end
