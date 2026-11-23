import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.ProjectiveLattices.HeckeJ
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (X : FormsL LL Ks WL W G)

def ball (la : HeightOneSpectrum (𝓞 Ks)) (B : ℝ) : Set X.WK := {f | ∀ y : X.Pt la, X.nrm la y f ≤ B}

def onK (h : WL →ₗ[LL] WL) (hK : ∀ x ∈ X.WK, h x ∈ X.WK) : X.WK →ₗ[Ks] X.WK := (h.restrictScalars Ks).restrict hK

def LiesOver (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') : Prop :=
  ∀ a : Ks, algebraMap Ks K' a ∈ O ↔ la.valuation Ks a ≤ 1

def latK (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[Ks] X.WK) :=
  Submodule.span O ((fun f => (1 : K') ⊗ₜ[Ks] f) '' ball X la 1)

def partK (U : Submodule LL WL) (K' : Type) [Field K'] [Algebra Ks K'] : Submodule K' (K' ⊗[Ks] X.WK) :=
  ((U.restrictScalars Ks).comap X.WK.subtype).baseChange K'

def latL (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[LL] WL) :=
  Submodule.span O ((fun f : X.WK => (1 : K') ⊗ₜ[LL] (f : WL)) '' ball X la 1)

def KeepsTypes (h : WL →ₗ[LL] WL) : Prop :=
  (∀ g, h ∘ₗ X.ρ g = X.ρ g ∘ₗ h) ∧ (∀ eC : G → LL, h ∘ₗ X.eOp eC = X.eOp eC ∘ₗ h) ∧
    (∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ X.typeP J lam, h x ∈ X.typeP J lam) ∧
    ∀ eC : G → LL, ∀ x ∈ X.good eC, h x ∈ X.good eC

def KeepsLatK (h : WL →ₗ[LL] WL) (hK : ∀ x ∈ X.WK, h x ∈ X.WK) (la : HeightOneSpectrum (𝓞 Ks)) : Prop :=
  ∀ (K' : Type) [Field K'] [Algebra Ks K'] (O : ValuationSubring K'), LiesOver la O →
    ∀ x ∈ latK X la O, (onK X h hK).baseChange K' x ∈ latK X la O ∧
      ∀ (J : Subgroup G) (lam : J →* LLˣ),
        (x ∈ partK X (X.typeP J lam) K' → (onK X h hK).baseChange K' x ∈ partK X (X.typeP J lam) K') ∧
        ∀ eC : G → LL, x ∈ partK X (X.Wgood J lam eC) K' → (onK X h hK).baseChange K' x ∈ partK X (X.Wgood J lam eC) K'

def KeepsLatL (h : WL →ₗ[LL] WL) (la : HeightOneSpectrum (𝓞 Ks)) : Prop :=
  ∀ (K' : Type) [Field K'] [Algebra LL K'] [Algebra Ks K'] [IsScalarTower Ks LL K'] (O : ValuationSubring K'), LiesOver la O →
    ∀ x ∈ latL X la O, h.baseChange K' x ∈ latL X la O ∧
      ∀ (J : Subgroup G) (lam : J →* LLˣ),
        (x ∈ (X.typeP J lam).baseChange K' → h.baseChange K' x ∈ (X.typeP J lam).baseChange K') ∧
        ∀ eC : G → LL, x ∈ (X.Wgood J lam eC).baseChange K' → h.baseChange K' x ∈ (X.Wgood J lam eC).baseChange K'

structure KeepsSup (h : WL →ₗ[LL] WL) (hK : ∀ x ∈ X.WK, h x ∈ X.WK) (la : HeightOneSpectrum (𝓞 Ks)) : Prop where

  unitBall : ∀ f ∈ ball X la 1, onK X h hK f ∈ ball X la 1

  types : KeepsTypes X h

  latK : KeepsLatK X h hK la

  latL : KeepsLatL X h la

theorem baseChange_mem {k K' M : Type} [Field k] [Field K'] [Algebra k K'] [AddCommGroup M] [Module k M] (h : M →ₗ[k] M)
    (U : Submodule k M) (hU : ∀ x ∈ U, h x ∈ U) : ∀ x ∈ U.baseChange K', h.baseChange K' x ∈ U.baseChange K' := by
  intro x hx
  rw [Submodule.baseChange_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact Submodule.subset_span ⟨h m, hU m hm, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem span_mem {K' N : Type} [Field K'] [AddCommGroup N] [Module K' N] (O : ValuationSubring K') (h : N →ₗ[K'] N) (S : Set N)
    (hS : ∀ x ∈ S, h x ∈ S) : ∀ x ∈ Submodule.span O S, h x ∈ Submodule.span O S := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hS x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : h (a • x) = a • h x := h.map_smul (a : K') x
    rw [e]; exact Submodule.smul_mem _ a hx

omit [Fintype G] in
theorem partK_mem (h : WL →ₗ[LL] WL) (hK : ∀ x ∈ X.WK, h x ∈ X.WK) (U : Submodule LL WL) (hU : ∀ x ∈ U, h x ∈ U)
    (K' : Type) [Field K'] [Algebra Ks K'] : ∀ x ∈ partK X U K', (onK X h hK).baseChange K' x ∈ partK X U K' :=
  baseChange_mem (onK X h hK) ((U.restrictScalars Ks).comap X.WK.subtype) fun y hy => hU (y : WL) hy

variable {X} in

theorem keepsSup_iff {h : WL →ₗ[LL] WL} {hK : ∀ x ∈ X.WK, h x ∈ X.WK} {la : HeightOneSpectrum (𝓞 Ks)} :
    KeepsSup X h hK la ↔ (∀ f ∈ ball X la 1, onK X h hK f ∈ ball X la 1) ∧ ∀ g, h ∘ₗ X.ρ g = X.ρ g ∘ₗ h := by
  refine ⟨fun H => ⟨H.unitBall, H.types.1⟩, fun ⟨hb, hc⟩ => ?_⟩
  have hc' : ∀ g x, h (X.ρ g x) = X.ρ g (h x) := fun g x => LinearMap.congr_fun (hc g) x
  have he : ∀ (eC : G → LL) x, h (X.eOp eC x) = X.eOp eC (h x) := fun eC x => by
    simp only [FormsL.eOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hc']
  have ht : ∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ X.typeP J lam, h x ∈ X.typeP J lam := fun J lam x hx p => by
    rw [← hc', hx p, map_smul]
  have hg : ∀ eC : G → LL, ∀ x ∈ X.good eC, h x ∈ X.good eC := by
    rintro eC _ ⟨y, rfl⟩
    exact ⟨h y, (he eC y).symm⟩
  have hw : ∀ (J : Subgroup G) (lam : J →* LLˣ) (eC : G → LL), ∀ x ∈ X.Wgood J lam eC, h x ∈ X.Wgood J lam eC :=
    fun J lam eC x hx => ⟨ht J lam x hx.1, hg eC x hx.2⟩
  refine ⟨hb, ⟨hc, fun eC => LinearMap.ext (he eC), ht, hg⟩, fun K' _ _ O _ x hx => ⟨?_, fun J lam => ⟨?_, fun eC => ?_⟩⟩,
    fun K' _ _ _ _ O _ x hx => ⟨?_, fun J lam => ⟨?_, fun eC => ?_⟩⟩⟩
  · refine span_mem O _ _ ?_ x hx
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨_, hb f hf, by simp⟩
  · exact partK_mem X h hK _ (ht J lam) K' x
  · exact partK_mem X h hK _ (hw J lam eC) K' x
  · refine span_mem O _ _ ?_ x hx
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨_, hb f hf, (LinearMap.baseChange_tmul h 1 (f : WL)).symm⟩
  · exact baseChange_mem _ _ (ht J lam) x
  · exact baseChange_mem _ _ (hw J lam eC) x

theorem keepsSup_id (la : HeightOneSpectrum (𝓞 Ks)) : KeepsSup X LinearMap.id (fun _ hx => hx) la :=
  keepsSup_iff.2 ⟨fun _ hf => hf, fun _ => rfl⟩

theorem liesOver_self (la : HeightOneSpectrum (𝓞 Ks)) : LiesOver la (la.valuation Ks).valuationSubring := fun _ => Iff.rfl

end Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m)

structure ReadPinned : Prop where
  frame : ∃ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i,
    FramePin T R i (res T (sg0 D A)) hV ∧ JEvAt T R κ v₀ i (sg0 D A) hV
  inj : Function.Injective ((R.FW i).j (sg0 D A))
  act : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (actW R i (sg0 D A)) (R.FW i).chi (R.FW i).ρ

def hkConst (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : ℂ :=
  (muAt T R i P)⁻¹ ^ k * (Nat.card (kP P) : ℂ)⁻¹ ^ (k * D.R.nV / 2)

def IsHecke (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (h : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (hkConst T R i P k) h

def SupAt : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
    IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)), IsHecke T R i P k Rc h →
    ∀ (hK : ∀ x ∈ (R.FW i).WK, h x ∈ (R.FW i).WK) (la : HeightOneSpectrum (𝓞 T.Q.c.F)),
      (p : 𝓞 T.Q.c.F) ∉ la.asIdeal → KeepsSup (R.FW i) h hK la

def HkSup : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.Char F → FWTie T R κ v₀ → ∀ i : Fin D.R.m, ReadPinned T R κ v₀ i → SupAt T R i

variable {T R κ v₀ i}

theorem base_of_tie (fw : FWTie T R κ v₀) : res T (sg0 D A) = T.σ₀ ∧ GoodEmb T.Q.c (res T (sg0 D A)) ∧
    T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := by
  have hg := Formalism.IndefR.FWT.base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  refine ⟨?_, hg, fw.laws.spaceW _ (inR i) _ hg⟩
  rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
  exact res_embLL T fw.alg_eq fw.laws.pins.2.2.1

theorem ReadPinned.eval (fw : FWTie T R κ v₀) (H : ReadPinned T R κ v₀ i)
    (hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i) (f : Cu T κ i) :
    evAt R i (sg0 D A) (v₀ i (sg0 D A)) (fw.jK i (sg0 D A) f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) := by
  obtain ⟨_, -, jK, hjK⟩ := H.frame
  obtain ⟨j', hj'⟩ := exists_ext_of_isKsForm (R.FW i) (fw.ks i) (fw.e i) (sg0 D A) jK
  exact fw.ev i _ (base_of_tie (i := i) fw).2.1 hV ⟨j', fun f => (congrArg (evAt R i _ (v₀ i _)) (hj' f)).trans (hjK f)⟩ f

theorem readPinned_of_unif (hu : R.LUnif) (hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i)
    (hf : FramePin T R i (res T (sg0 D A)) hV) (hj : JEvAt T R κ v₀ i (sg0 D A) hV) : ReadPinned T R κ v₀ i := by
  refine ⟨⟨hV, hf, hj⟩, (injective_iff_map_eq_zero _).2 fun x hx => ?_, (hu i _).2.2⟩
  by_contra h0
  have h1 := (hu i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)
  exact h1.ne_zero 0 hx

end GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls
