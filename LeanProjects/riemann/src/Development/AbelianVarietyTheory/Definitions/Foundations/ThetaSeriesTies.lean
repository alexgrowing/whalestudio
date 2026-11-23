import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnTies

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.FormTies
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

def IsRightMul (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) {n : ℕ} (x x' : Fin n → Dw.La) : Prop :=
  ∀ (b : Fin n) (a : Dw.La), (l.M : ℤ) ∣ Dw.EF (x' b) (cSep l • a) - Dw.EF (x b) (cSep l • liftLa γ a)

def IsOrbitFamily (Xo : Moduli Dw l) (c : Coeff l) (bad : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (d : DeltaDat Xo c n)
    {I : Type} (ℓ : I → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)) (f : I → Rul Xo c) : Prop :=
  ∃ (Λ : GenLat E n) (N : ℕ) (x₀ : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (x : I → Fin n → Dw.La),
    Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt d.l₂.M ∧ Λ.LevOK N d.l₂.M ∧ AdmX (l := l) true x₀ ∧ P ∈ harmL c Λ a ∧
      ∀ u, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := l) true (x u) ∧ IsShortRule Xo c d Λ N (x u) P (f u)

end Geo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def traceSpan (B : WeightFamilies.Prov D) {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K] [Algebra B.KO K]
    {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) {P : Type} [Group P] (U : Subgroup P) (ψ : P → 𝓞 K)
    (s : Set (U → B.Cusp j w)) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) ((fun f : U → B.Cusp j w => ∑ᶠ u : U, ψ (u : P) • z.symm (1 ⊗ₜ[B.KO] f u)) '' s)

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev WeilRep (D : D7) (i : Fin D.R.m) : Type :=
  GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)

def adForm (x : Fin (R.nW i) → D.what₂.LL) : Mult.MMap (R.MW i (sg0 D A)) :=
  (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) x)

def InCoefLat (h : GA D (Vc D i)) (w : (R.cV i).W) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ P ∈ nabAtr (labLL D) (lamV D i) (Bridge.hLat (Vc D i) (fin (Vc D i) h)), w = c0L i P

open Classical in

def levelTrace (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) : (GA D (Wc D i) → ℂ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  gaL (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG fun g =>
    if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0

def singleSeries (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : GA D (Wc D i) → ℂ := fun g =>
  Datum.thetaKO ω h g
    (Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ
      (R.ioP i (PiTensorProduct.tprod ℂ v) w))

def seriesSet (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) :
    Set (Fin (R.nW i) → D.what₂.LL) :=
  {x | ∃ h ∈ GfC (Vc D i), ∃ w, InCoefLat R i h w ∧ ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
    adForm R i x (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h w v)}

def IsKernel (ξ : Formalism.L2.Host.HChar D.host.E) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i)
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∃ (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq χ ξ ∧ (∀ PP ∈ Q, IsRes ξ PP (ξR PP)) ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω ∧
    Datum.IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg Q ξR (R.vacP i) φ

open Classical in

def placesOver (t : T0) (p : ℕ) : Finset (Pl D.host.E) := (R.Q t).filter fun PP => (p : 𝓞 D.host.E) ∈ PP.asIdeal

def thetaBase (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) :
    Submodule (𝓞 D.what₂.LL) (Fin (R.nW i) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) {x | ∃ ω φ, IsKernel R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) (placesOver R (R.mu v) p) ω φ ∧
    x ∈ seriesSet R i U ψ ph ω φ}

def thetaTuple (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (t : T0) :
    Submodule (𝓞 D.what₂.LL) (Fin (R.nW i) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) (seriesSet R i U ψ ph (R.ωP i t) (R.vP i t))

variable (A) in

abbrev srcDim (t : T0) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) : ℕ := (A.MtCSD i t).lvlDim (A.leftGroupActionLift i t) U ψ

variable (A) in

def srcForm (t : T0) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) :
    (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (A.MtCSD i t).Forms :=
  ((A.MtCSD i t).basis.equivFun.symm : (Fin (A.MtCSD i t).dim → D.what₂.LL) →ₗ[D.what₂.LL] (A.MtCSD i t).Forms) ∘ₗ
    ((A.MtCSD i t).lvlE (A.leftGroupActionLift i t) U ψ).mulVecLin

def IsClassSum (t : T0) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ)
    (θ : (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  ∀ x, adForm R i (θ x) = ph • R.thF i t (jVx R i t (srcForm A i t U ψ x))

def ClassSumRational (t : T0) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) : Prop :=
  ∃ θ, IsClassSum R i t U ψ ph θ

end Adelic

def orthProj {K : Type} [Field K] [StarRing K] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) K) (Z : Submodule K (Fin n → K)) :
    (Fin n → K) →ₗ[K] (Fin n → K) :=
  (subE Z * orthPr Hm (subE Z)).mulVecLin

section Coord

variable {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def cutTo (fw : FWTie J R κ v₀) (i : Fin D.R.m) :
    cutR J.toCore.C ((i : ℕ) + 1) (κ i) →ₗ[J.Q.c.F] (Fin (R.nW i) → D.what₂.LL) :=
  (R.FW i).WK.subtype ∘ₗ (fw.e i).toLinearMap ∘ₗ Submodule.inclusion (cutR_le J.toCore.C ((i : ℕ) + 1) (κ i))

end Coord

theorem inR_succ (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

def thetaEig {T : Top D} (h : LawsP T) (j : ℕ) (w : WeightFamilies.Wt D j) {K : Type} [Field K] [NumberField K]
    [Algebra (recB h.toLawsCore).KO K] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp j w) {P : Type} [Group P] (U : Subgroup P)
    (ψ : P → 𝓞 K) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) : Submodule (𝓞 K) (Fin n → K) :=
  traceSpan (recB h.toLawsCore) z U ψ {f | IsOrbitFamily (T.Q.Xo j) T.Q.c (badN D) (wtA w) (T.dδ j w.n) (fun u : U => ℓ u)
    fun u => ((f u).1 : T.R j)}

section Comparison₂

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL]

instance algQ : Algebra T.Q.c.F D.what₂.LL := inst

variable {R : RealDat D A T.J.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def cuspTo (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (i : Fin D.R.m) :
    (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i) →ₗ[(recB h.toLawsCore).KO] (Fin (R.nW i) → D.what₂.LL) :=
  cutTo fw i

def toForms (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (i : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) :
    (Fin n → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL) :=
  (cuspTo h fw i).liftBaseChange D.what₂.LL ∘ₗ z.toLinearMap

structure OnTie (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (ι : Fin D.R.m) (wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)) (nT : ℕ)
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Bs.J)
    (z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι))
    (act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι))
    (inc : P →* G)
    (ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l))
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ)
    (y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)) : Prop
    extends FormTieK (recPJ h ((ι : ℕ) + 1) (inR_succ ι)) hinj EX p (κ ι) wL wF nT O v i z act where

  act_eq : IsLevAct T.toTop h ((ι : ℕ) + 1) (κ ι) (fun g => ℓ (inc g)) act

  U_eq : O.U = U.comap inc

  ψ_eq : ∀ (g : P) (hg : inc g ∈ U), ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) = (ψ ⟨inc g, hg⟩ : D.what₂.LLˣ)

  e_eq : toForms h fw ι z ∘ₗ O.e i = (R.FW ι).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ toForms h fw ι z

  V₀_eq : O.V₀ i = LinearMap.range (O.e i)

  Th0_eq : O.Th0 v i = thetaEig h ((ι : ℕ) + 1) (κ ι) z O.U O.ψ fun g => ℓ (inc g)

  ThJ_eq : O.ThJ v i = (thetaBase R ι U ψ ph v p).comap ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL))

  X₃_eq : O.X₃ v i = ((thetaTuple R ι U ψ ph (R.mu v)).comap ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL))).map
    ((O.e i).restrictScalars (𝓞 D.what₂.LL))

  Mt_eq : O.Mt v i = ((A.MtCSD ι (R.mu v)).lvlNab (A.leftGroupActionLift ι (R.mu v)) U ψ).comap (y.toLinearMap.restrictScalars (𝓞 D.what₂.LL))

  θ'_eq : ClassSumRational R ι (R.mu v) U ψ ph →
    IsClassSum R ι (R.mu v) U ψ ph (toForms h fw ι z ∘ₗ O.θ' v i ∘ₗ y.symm.toLinearMap)

  eX_eq : y.toLinearMap ∘ₗ O.eX v i =
    ((A.MtCSD ι (R.mu v)).lvlOp (A.leftGroupActionLift ι (R.mu v)) U ψ (idemOf A.X)).mulVecLin ∘ₗ y.toLinearMap

  pr_eq : y.toLinearMap ∘ₗ O.pr v i =
    orthProj ((A.MtCSD ι (R.mu v)).lvlH (A.leftGroupActionLift ι (R.mu v)) U ψ)
      (perpOf ((A.MtCSD ι (R.mu v)).lvlH (A.leftGroupActionLift ι (R.mu v)) U ψ) ((LinearMap.ker (O.θ' v i)).map y.toLinearMap)) ∘ₗ
      y.toLinearMap

def LevelPin (R : RealDat D A T.J.Q.c.F) (ι : Fin D.R.m)
    (ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)) : Prop :=
  LevIs R ι (iotaW T.J ι) T.Q.l.M (Mfr T.Q.l) fun g => liftLa (ℓ g)

def ActionPin (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (ι : Fin D.R.m)
    (ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)) : Prop :=
  ∃ act : G → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι),
    IsLevAct T.toTop h ((ι : ℕ) + 1) (κ ι) ℓ act ∧ ∀ g F, cuspTo h fw ι (act g F) = (R.FW ι).ρ g (cuspTo h fw ι F)

def RunPin (R : RealDat D A T.J.Q.c.F) (ι : Fin D.R.m) (n : ℕ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  p = (if Formalism.EigenvalueLevelCeiling.plc v = D.host.pde then D.host.pde' else D.host.pde) ∧ (T.dδ ((ι : ℕ) + 1) n).pd = p ∧
    (∀ PP ∈ placesOver R (R.mu v) p, T.half₂ ≤ PP.asIdeal) ∧
    ∃ χ : (AE D)ˣ →* Circle, ChrEq χ (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) ∧
      ∀ (g : GA D (Wc D ι)) (x : (AE D)ˣ), IsDetRoot (Wc D ι) g x →
        ((T.xi (Matrix.GeneralLinearGroup.det (finHom (Wc D ι) g)) : ℂˣ) : ℂ) = ((χ x : Circle) : ℂ)

end Comparison₂

section Api

theorem liftBaseChange_bijective {F K C V : Type} [Field F] [Field K] [Algebra F K] [AddCommGroup C] [Module F C]
    [AddCommGroup V] [Module F V] [Module K V] [IsScalarTower F K V] (f : C →ₗ[F] V) (hf : Function.Injective f)
    {n : ℕ} (b : Fin n → V) (hF : LinearIndependent F b) (hr : Submodule.span F (Set.range b) = LinearMap.range f)
    (hK : LinearIndependent K b) (hs : Submodule.span K (Set.range b) = ⊤) :
    Function.Bijective (f.liftBaseChange K) := by
  let c : Module.Basis (Fin n) F C :=
    (Module.Basis.span hF).map ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective f hf).symm)
  have hc : ∀ i, f (c i) = b i := fun i => by
    have := LinearEquiv.ofInjective_symm_apply f (h := hf) (LinearEquiv.ofEq _ _ hr (Module.Basis.span hF i))
    simpa [c, Module.Basis.span_apply] using this
  let bK : Module.Basis (Fin n) K V := Module.Basis.mk hK hs.ge
  have e : f.liftBaseChange K = ((c.baseChange K).equiv bK (Equiv.refl _)).toLinearMap := by
    refine (c.baseChange K).ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul,
      one_smul, hc]
    simp [bK]
  rw [e]
  exact LinearEquiv.bijective _

theorem cusp_liftBaseChange_bijective (B : WeightFamilies.Prov D) {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [Algebra B.KO K]
    {m : ℕ} (f : B.Cusp j w →ₗ[B.KO] (Fin m → K)) (hf : Function.Injective f)
    {n : ℕ} (b : Fin n → Fin m → K) (hF : LinearIndependent B.KO b)
    (hr : Submodule.span B.KO (Set.range b) = LinearMap.range f)
    (hK : LinearIndependent K b) (hs : Submodule.span K (Set.range b) = ⊤) :
    Function.Bijective (f.liftBaseChange K) :=
  liftBaseChange_bijective f hf b hF hr hK hs

theorem traceSpan_le {B : WeightFamilies.Prov D} {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K] [Algebra B.KO K]
    {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) {P : Type} [Group P] [Finite P] (U : Subgroup P) (ψ : P → 𝓞 K)
    {s : Set (U → B.Cusp j w)} {t : Set (B.Cusp j w)} (hst : ∀ f ∈ s, ∀ u, f u ∈ t) : traceSpan B z U ψ s ≤ spanK z t := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  haveI := Fintype.ofFinite U
  change ∑ᶠ u : U, ψ (u : P) • z.symm (1 ⊗ₜ[B.KO] f u) ∈ spanK z t
  rw [finsum_eq_sum_of_fintype]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (mem_spanK z (hst f hf u))

section Right

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem dvd_pair_of_mem (x : Dw.La) {q : Dw.La} (hq : q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ Dw.EF x (cSep l • q) := by
  have hc : cSep l ∈ Mfr l := by
    unfold cSep
    split_ifs with h
    · exact h.choose_spec.1
    · exact zero_mem _
  have h1 : cSep l • q ∈ (Ideal.span {(l.M : 𝓞 E)}) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [← l.prod, mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hc hq
  rw [Submodule.ideal_span_singleton_smul] at h1
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
  rw [← hy, Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  exact dvd_mul_right _ _

theorem IsRightMul.mul {γ δ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l} {n : ℕ} {x x' x'' : Fin n → Dw.La} (h : IsRightMul γ x x')
    (h' : IsRightMul δ x' x'') : IsRightMul (γ * δ) x x'' := by
  intro b a
  have e : (l.M : ℤ) ∣ Dw.EF (x b) (cSep l • liftLa γ (liftLa δ a)) - Dw.EF (x b) (cSep l • liftLa (γ * δ) a) := by
    rw [← map_sub, ← smul_sub]
    refine dvd_pair_of_mem _ ((Submodule.Quotient.eq _).1 ?_)
    exact ((liftLa_spec γ _).trans (congrArg γ (liftLa_spec δ a))).trans (liftLa_spec (γ * δ) a).symm
  have := dvd_add (dvd_add (h' b a) (h b (liftLa δ a))) e
  simpa using this

end Right

theorem IsOrbitFamily.mem_shortGen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {bad : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {d : DeltaDat Xo c n} {I : Type} {ℓ : I → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)} {f : I → Rul Xo c}
    (hf : IsOrbitFamily Xo c bad a d ℓ f) (nab : NabV Xo c) (u : I) (hu : f u ∈ sec Xo c a n) :
    f u ∈ shortGen Xo c nab bad n a n d := by
  obtain ⟨Λ, N, x₀, P, x, h1, h2, h3, h4, -, h6, h7⟩ := hf
  exact ⟨hu, Λ, N, x u, P, h1, h2, h3, h4, by simpa using (h7 u).2.1, h6, (h7 u).2.2⟩

theorem orthProj_mem {K : Type} [Field K] [StarRing K] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) K) (Z : Submodule K (Fin n → K))
    (x : Fin n → K) : orthProj Hm Z x ∈ Z := by
  have e : orthProj Hm Z x = (subE Z).mulVecLin ((orthPr Hm (subE Z)).mulVec x) := by
    simp [orthProj, Matrix.mulVec_mulVec]
  rw [e]
  exact (subspace_image_spec K n Z).2.le ⟨_, rfl⟩

theorem sub_orthProj_mem_perpOf {K : Type} [Field K] [StarRing K] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) K)
    (Z : Submodule K (Fin n → K)) (hd : IsUnit ((subE Z)ᴴ * Hm * subE Z).det) (x : Fin n → K) :
    x - orthProj Hm Z x ∈ perpOf Hm Z := by
  intro w hw
  obtain ⟨a, rfl⟩ := (subspace_image_spec K n Z).2.ge hw
  have h0 : ((subE Z)ᴴ * Hm).mulVec (x - orthProj Hm Z x) = 0 := by
    rw [Matrix.mulVec_sub, orthProj, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, orthPr, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, sub_self]
  have h1 : ∀ u y : Fin n → K, Formalism.DivisionValues.hform Hm u y = star u ⬝ᵥ Hm.mulVec y := fun u y => by
    simp [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_assoc, mul_comm,
      mul_left_comm]
  rw [h1, Matrix.mulVecLin_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h0, dotProduct_zero]

example {K : Type} [Field K] [StarRing K] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    orthProj Hm ⊥ x = 0 := orthProj_mem Hm ⊥ x

section

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem IsClassSum.unique {t : T0} {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
    {θ θ' : (Fin (srcDim A i t U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hinj : Function.Injective (adForm R i)) (h : IsClassSum R i t U ψ ph θ) (h' : IsClassSum R i t U ψ ph θ') : θ = θ' :=
  LinearMap.ext fun x => hinj ((h x).trans (h' x).symm)

end

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem cutTo_spec {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie J R κ v₀) (i : Fin D.R.m) :
    Function.Injective (cutTo fw i) ∧ LinearMap.range (cutTo fw i) = (R.FW i).WK := by
  refine ⟨Subtype.val_injective.comp ((fw.e i).injective.comp (Submodule.inclusion_injective _)), le_antisymm ?_ ?_⟩
  · rintro _ ⟨F, rfl⟩
    exact (fw.e i _).2
  · intro x hx
    obtain ⟨F, hF⟩ := (fw.e i).surjective ⟨x, hx⟩
    exact ⟨⟨F.1, (cutR_eq J.toCore.C (inR_succ i) (κ i)).symm ▸ F.2⟩, congrArg Subtype.val hF⟩

theorem toForms_tmul (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (i : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i))
    (a : D.what₂.LL) (F : (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) :
    toForms h fw i z (z.symm (a ⊗ₜ F)) = a • cuspTo h fw i F := by
  unfold toForms
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.liftBaseChange_tmul]

theorem toForms_bijective (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (i : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) :
    Function.Bijective (toForms h fw i z) := by
  obtain ⟨m, b, -, h1, h2, h3, h4⟩ := fw.ks i
  exact (cusp_liftBaseChange_bijective (recB h.toLawsCore) (cuspTo h fw i) (cutTo_spec fw i).1 b h1
    (h2.trans (cutTo_spec fw i).2.symm) h3 h4).comp z.bijective

section Use

variable {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
    {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
    {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {inc : P →* G}
    {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
    {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem OnTie.Th0_le_ThK (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hn : (κ ι).n = D.R.nV) :
    O.Th0 v i ≤ O.ThK v i := by
  rw [t.Th0_eq, t.ThK_eq]
  refine traceSpan_le z _ _ fun f hf u => Submodule.subset_span ?_
  have := IsOrbitFamily.mem_shortGen hf (T.nab _) u (cutR_le T.C _ _ (f u).2).1
  change (f u).1 ∈ shortGen _ _ _ _ D.R.nV _ _ _
  rw [← hn]
  exact this

theorem OnTie.e_eOp (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (x : Fin (O.nZ i) → D.what₂.LL) :
    toForms h fw ι z (O.e i x) = (R.FW ι).eOp (fun g => (idemOf A.X).coeff g) (toForms h fw ι z x) :=
  LinearMap.congr_fun t.e_eq x

theorem OnTie.adForm_θ' (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y)
    (hr : ClassSumRational R ι (R.mu v) U ψ ph) (x : Fin (O.nX v i) → D.what₂.LL) :
    adForm R ι (toForms h fw ι z (O.θ' v i x)) = ph • R.thF ι (R.mu v) (jVx R ι (R.mu v) (srcForm A ι (R.mu v) U ψ (y x))) := by
  have := t.θ'_eq hr (y x)
  simpa using this

theorem OnTie.rho_eq_of_actionPin (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (g : P) (x : Fin (O.nZ i) → D.what₂.LL) :
    toForms h fw ι z (O.ρ i g x) = (R.FW ι).ρ (inc g) (toForms h fw ι z x) := by
  obtain ⟨a, h1, h2⟩ := ha
  obtain ⟨u, rfl⟩ := z.symm.surjective x
  induction u using TensorProduct.induction_on with
  | zero => rw [z.symm.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
  | add u u' hu hu' => rw [z.symm.map_add, LinearMap.map_add, LinearMap.map_add, hu, hu', LinearMap.map_add, LinearMap.map_add]
  | tmul c F =>
    have e : act g F = a (inc g) F := Subtype.ext ((t.act_eq g F).trans (h1 (inc g) F).symm)
    rw [t.toFormTieK.rho_tmul, toForms_tmul, toForms_tmul, e, h2, map_smul]

end Use

open Classical in

def charInt {K : Type} [Field K] [NumberField K] {P : Type} [Group P] (inc : P →* G) (U : Subgroup G) (ψ : U →* Kˣ) (g : P) :
    𝓞 K :=
  if hg : inc g ∈ U then
    ⟨(ψ ⟨inc g, hg⟩ : Kˣ), IsIntegral.of_pow (n := Nat.card U) Nat.card_pos (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]; exact isIntegral_one)⟩
  else 1

theorem charInt_coe {K : Type} [Field K] [NumberField K] {P : Type} [Group P] (inc : P →* G) (U : Subgroup G) (ψ : U →* Kˣ)
    (g : P) (hg : inc g ∈ U) : ((charInt inc U ψ g : 𝓞 K) : K) = (ψ ⟨inc g, hg⟩ : Kˣ) :=
  congrArg (fun a : 𝓞 K => (a : K)) (dif_pos hg)

theorem exists_onTie (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (ι : Bs.J → Fin D.R.m) (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
    (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)
    (ℓ : ∀ i, G → (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
    (ρ : ∀ i, Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))))
    (hρ : ∀ i, IsLevAct T.toTop h ((ι i : ℕ) + 1) (κ (ι i)) (fun g => ℓ i (inc g)) fun g F => ρ i g F)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : Bs.J → ℂ) :
    ∃ (O' : OnObj S P oc) (z : ∀ i, (Fin (O'.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
        D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))
      (y : ∀ v i, (Fin (O'.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) (R.mu v) U ψ) → D.what₂.LL)),
      O'.pde = O.pde ∧ ∀ v i, OnTie h fw hinj EX (p v) (ι i) (wL i) (wF i) nT O' v i (z i) (fun g F => ρ i g F) inc (ℓ i) U ψ
        (ph i) (y v i) := by
  classical
  obtain ⟨O₁, z, -, hp, -, H⟩ := exists_formTieK (B := recB h.toLawsCore) (P6 := T.G.P) hinj EX O (fun i => (ι i : ℕ) + 1)
    (fun _ i => recPJ h ((ι i : ℕ) + 1) (inR_succ (ι i))) p (fun i => κ (ι i)) wL wF nT ρ
  let w : ∀ i, (Fin (O₁.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW (ι i)) → D.what₂.LL) := fun i =>
    LinearEquiv.ofBijective (toForms h fw (ι i) (z i)) (toForms_bijective h fw (ι i) (z i))
  let e : ∀ i, (Fin (O₁.nZ i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (O₁.nZ i) → D.what₂.LL) := fun i =>
    (w i).symm.toLinearMap ∘ₗ (R.FW (ι i)).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ toForms h fw (ι i) (z i)
  let θ : ∀ v i, (Fin (srcDim A (ι i) (R.mu v) U ψ) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (O₁.nZ i) → D.what₂.LL) := fun v i =>
    if hr : ClassSumRational R (ι i) (R.mu v) U ψ (ph i) then (w i).symm.toLinearMap ∘ₗ hr.choose else 0
  have hw : ∀ i x, toForms h fw (ι i) (z i) ((w i).symm x) = x := fun i x => (w i).apply_symm_apply x
  let O' : OnObj S P oc :=
    { O₁ with
      U := U.comap inc
      ψ := charInt inc U ψ
      e := e
      V₀ := fun i => LinearMap.range (e i)
      Th0 := fun _ i => thetaEig h ((ι i : ℕ) + 1) (κ (ι i)) (z i) (U.comap inc) (charInt inc U ψ) fun g => ℓ i (inc g)
      ThJ := fun v i => (thetaBase R (ι i) U ψ (ph i) v (p v)).comap
        ((toForms h fw (ι i) (z i)).restrictScalars (𝓞 D.what₂.LL))
      X₃ := fun v i => ((thetaTuple R (ι i) U ψ (ph i) (R.mu v)).comap
        ((toForms h fw (ι i) (z i)).restrictScalars (𝓞 D.what₂.LL))).map ((e i).restrictScalars (𝓞 D.what₂.LL))
      nX := fun v i => srcDim A (ι i) (R.mu v) U ψ
      θ' := θ
      eX := fun v i => ((A.MtCSD (ι i) (R.mu v)).lvlOp (A.leftGroupActionLift (ι i) (R.mu v)) U ψ (idemOf A.X)).mulVecLin
      pr := fun v i => orthProj ((A.MtCSD (ι i) (R.mu v)).lvlH (A.leftGroupActionLift (ι i) (R.mu v)) U ψ)
        (perpOf ((A.MtCSD (ι i) (R.mu v)).lvlH (A.leftGroupActionLift (ι i) (R.mu v)) U ψ) (LinearMap.ker (θ v i)))
      Mt := fun v i => (A.MtCSD (ι i) (R.mu v)).lvlNab (A.leftGroupActionLift (ι i) (R.mu v)) U ψ }
  refine ⟨O', z, fun _ _ => LinearEquiv.refl _ _, hp, fun v i =>
    { Ms_eq := (H v i).Ms_eq, rho_eq := (H v i).rho_eq, Th_eq := (H v i).Th_eq, σ_eq := (H v i).σ_eq,
      ThK_eq := (H v i).ThK_eq, act_eq := hρ i, U_eq := rfl, ψ_eq := fun g hg => ?_,
      e_eq := LinearMap.ext fun x => hw i _, V₀_eq := rfl, Th0_eq := rfl, ThJ_eq := rfl, X₃_eq := rfl, Mt_eq := rfl,
      θ'_eq := fun hr x => ?_, eX_eq := rfl, pr_eq := ?_ }⟩
  · exact charInt_coe inc U ψ g hg
  · change adForm R (ι i) (toForms h fw (ι i) (z i) (θ v i x)) = _
    simp only [θ, dif_pos hr]
    exact (congrArg (adForm R (ι i)) (hw i _)).trans (hr.choose_spec x)
  · change orthProj _ (perpOf _ (LinearMap.ker (θ v i))) = orthProj _ (perpOf _ ((LinearMap.ker (θ v i)).map LinearMap.id))
    rw [Submodule.map_id]

end Api
end GlobalTheory.OnTies
