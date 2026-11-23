import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Space

abbrev fin (V : HSp D) (h : GA D V) : Bridge.Gf V := (finHom V).rangeRestrict h

def SplitOffBad (V : HSp D) (bad : ℕ) (h : GA D V) : Prop :=
  h ∈ GfC V ∧ ∃ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P ∧ (∀ PP ∈ P, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ SuppAt e V h

def uMat (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X : Fin S.rank → Fin T.rank → D.host.E) : Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  fun b a => toEAf D e * HMul.hMul (HMul.hMul (βS⁻¹).val
    ((HMul.hMul (HMul.hMul S.gram⁻¹ (Matrix.of fun b a => D.sp.cm.sig (X b a))) T.gram).map (eToEAf D))) βT.val b a

end Space

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)

variable (D) in

abbrev lamV : D.what₂.Tau → DomWeight (Vc D i).rank := fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ

variable (D) in

abbrev VsV (K : Type) [Field K] : Type := ↥(VV K (lamV D i))

variable (D) in

def embV (τ : D.what₂.Tau) : D.host.E →+* K' := jL.comp (labLL D τ)

theorem embV_spec (h : σ'.comp jL = D.what₂.embLL) (τ : D.what₂.Tau) : σ'.comp (embV D jL τ) = tauE D τ := by
  ext x
  have h1 := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) x)
  have h2 := RingHom.congr_fun h (labLL D τ x)
  exact h2.trans h1

theorem embV_eq_embF {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (j : D.what₂.LL →+* c.F) (h : c.F.val.toRingHom.comp j = D.what₂.embLL) (τ : D.what₂.Tau) :
    embV D j τ = embF c (tauE D τ) := by
  ext x
  exact RingHom.congr_fun (embV_spec j c.F.val.toRingHom h τ) x

abbrev levJ (t : T0) : Subgroup (Bridge.Gf (Vc D i)) := (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J

variable (D) in

def VStd : Prop :=
  (Vc D i).gram = 1 ∧ Bridge.hLat (Vc D i) 1 = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)

def FrameIntegralCongruentOne : Prop := IsIntM (R.βV i).val ∧ ∀ t PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (R.βV i).val = 1

section Tuple

variable (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))

def RepsR (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i)))
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K') : Prop :=
  bad ≠ 0 ∧ (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    J' ≤ levJ R i t ∧ J'.relIndex (levJ R i t) ≠ 0 ∧ vol = ((J'.relIndex (levJ R i t) : ℕ) : K')⁻¹ ∧
    Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
    ∀ k, SplitOffBad (Vc D i) bad (h k) ∧ Lh k = Bridge.hLat (Vc D i) (fin _ (h k)) ∧
      gam k = Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k)))

def CoefficientBaseChange (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) : Prop :=
  ∀ v : VsV D i D.what₂.LL, ∃ v' : VsV D i K',
    (v' : Pol K' D.what₂.Tau (Vc D i).rank) = MvPolynomial.map jL (v : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank) ∧ c0' v' = c0 v

variable {σ'} (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

def Place (y : (R.HV i t).H) (x : Cl → VsV D i K') : Prop := ∀ k, (R.HV i t).e y (fin _ (h k)) = c0' (x k)

def jVx (x₀ : A.fam.amb.FL i t) : (R.HV i t).H := R.jV i t x₀

def PlaceEx : Prop := ∀ x₀ : A.fam.amb.FL i t, ∃ x, Place R i t h c0' (jVx R i t x₀) x

def ThAdIs (v₀ : (R.MW i (sg0 D A)).Vec) (thAd : (Cl → VsV D i K') → AutQ (Wc D i) → ℂ) : Prop :=
  ∀ y x, Place R i t h c0' y x → thAd x = onQ (Wc D i) (R.thF i t y v₀)

variable (σ')

def BIs (bad : ℕ) (B : Ideal (𝓞 D.host.E) → K') : Prop :=
  ∀ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ → cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ →
    σ' (B cc) = (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).onId (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℂˣ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)

def XiIs (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop :=
  ∀ (g : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) g x →
    ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) = ((R.xi t x : Circle) : ℂ)

variable {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))

open Classical in

def PhiIs (N : Submodule (𝓞 D.host.E) La) (φ : (Fin (Vc D i).rank → La ⧸ N) → K') : Prop :=
  ∃ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)) ∧
    σ' (φ fun b => Submodule.Quotient.mk (x b)) =
      omegaK R.Pg (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b))) *
        omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1)
          (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)))

def HalfIs (Mb I : Ideal (𝓞 D.host.E)) : Prop :=
  Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧ (∀ PP ∈ R.Q t, I ≤ PP.asIdeal) ∧
    ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

end Tuple

def LevIs {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ ∧
    ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat (Wc D i) 1,
      finVec (Wc D i) (ι (lev g a)) - (finHom (Wc D i) κ).1.mulVec (finVec (Wc D i) (ι a)) = M • w

def ActRho {Rl : Type} [AddCommGroup Rl] [Module Ks Rl] (C : Submodule Ks Rl) (e : C ≃ₗ[Ks] (R.FW i).WK)
    (act : G → Rl →ₗ[Ks] Rl) : Prop :=
  ∀ g (f : C), ∃ hf : act g f ∈ C,
    ((e ⟨act g f, hf⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = (R.FW i).ρ g ((e f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)

def ChiAt (σ : D.what₂.LL →+* ℂ) (χ : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D χ ∧ (∀ a, χ (idF D a) = 1) ∧ (∀ ρ, HasInfExp D χ ρ (-(D.hc (lab σ ρ)).e i)) ∧
    (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : Ks, ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y) ∧
      ((χ x : Circle) : ℂ) = σ (algebraMap Ks D.what₂.LL y)) ∧
    (σ.comp (algebraMap Ks D.what₂.LL) = D.what₂.embLL.comp (algebraMap Ks D.what₂.LL) → χ = R.mu0 ((i : ℕ) + 1))

structure ThPinsT (t : T0) (v₀ : (R.MW i (sg0 D A)).Vec) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (bad : ℕ) (Mb I : Ideal (𝓞 D.host.E)) (N : Submodule (𝓞 D.host.E) La) {Cl : Type} [Fintype Cl]
    (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K')
    (B : Ideal (𝓞 D.host.E) → K') (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (φ : (Fin (Vc D i).rank → La ⧸ N) → K') (thAd : (Cl → VsV D i K') → AutQ (Wc D i) → ℂ)
    (Plc : (Cl → VsV D i K') → Prop) : Prop where

  reps : ∃ (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i t h bad J' Lh gam vol ∧
    PlaceEx R i t h c0' ∧ ThAdIs R i t h c0' v₀ thAd ∧ ∀ x, Plc x ↔ ∃ x₀, Place R i t h c0' (jVx R i t x₀) x
  B : BIs R i σ' t bad B
  xi : XiIs R i t xi
  phi : PhiIs R i σ' t ι N φ
  half : HalfIs R t Mb I

structure ThPinsR (v₀ : (R.MW i (sg0 D A)).Vec) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La) : Prop where
  field : σ'.comp jL = D.what₂.embLL
  std : VStd D i
  v0 : IsChosenExtremalVector R i (sg0 D A) v₀
  c0 : ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0'
  lev : LevIs R i ι M Mh lev

theorem thF_of_pins {t : T0} {Cl : Type} [Fintype Cl] {h : Cl → GA D (Vc D i)} {c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    {v₀ : (R.MW i (sg0 D A)).Vec} {thAd : (Cl → VsV D i K') → AutQ (Wc D i) → ℂ} (hP : PlaceEx R i t h c0')
    (hT : ThAdIs R i t h c0' v₀ thAd) (x₀ : A.fam.amb.FL i t) :
    ∃ x, Place R i t h c0' (jVx R i t x₀) x ∧ thAd x = onQ (Wc D i) (R.thF i t (jVx R i t x₀) v₀) :=
  (hP x₀).imp fun x hx => ⟨hx, hT (jVx R i t x₀) x hx⟩

theorem chiW_val {μ0 : T0} (hL : R.toLevCh.Is μ0) (t : T0) (P : Pl D.host.E) (e : AE D) (he : Formalism.L2.JoinChr.IsPlIdem D e P)
    (x : (AE D)ˣ) (hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (Formalism.L2.Host.unif P : D.host.Eˣ)) :
    (((Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ) =
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val P : ℂˣ) : ℂ) := by
  have h1 := (hL.mu0 i).2 P e he _ x hx
  have h2 := (hL.xi t).2 P e he _ x hx
  have h3 := hL.eta.2 P e he _ x hx
  show (((R.mu0 ((i : ℕ) + 1) x * R.xi t x * (R.eta x)⁻¹ : Circle)) : ℂ) =
    ((((R.C.mu0 i).locK P (Formalism.L2.Host.unif P) * (R.xiH t).locK P (Formalism.L2.Host.unif P) *
      (R.C.eta.locK P (Formalism.L2.Host.unif P))⁻¹ : ℂˣ)) : ℂ)
  rw [Circle.coe_mul, Circle.coe_mul, Circle.coe_inv, h1, h2, h3, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]

theorem ext_fin {V : HSp D} (c : CoefA V) (hc : c.Is) (f : Bridge.Gf V → c.W) {h : GA D V} (hh : h ∈ GfC V) :
    c.ext f h = f (fin V h) := by
  show c.ρ h⁻¹ (f (fin V h)) = _
  rw [hc.1 _ (inv_mem hh)]
  rfl

theorem extV_fin (hc : (R.cV i).Is) (t : T0) (y : (R.HV i t).H) {h : GA D (Vc D i)} (hh : h ∈ GfC (Vc D i)) :
    R.extV i t y h = (R.HV i t).e y (fin _ h) :=
  ext_fin (R.cV i) hc ((R.HV i t).e y) hh

def MuR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : Core D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∃ χ, ChiAt R i σ χ ∧ MuVal (T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL))) χ
      (T.mu ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)))

def ChiR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ChiAt R i σ (T.chiW ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)))

end Formalism.IndefR.FWT
