import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Ord

section At

variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {n : ℕ} (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)

def ExpOf (π : CuspSub F n) (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) : Prop :=
  ∃ a, IsLocalArtin h a ∧ ∃ (hh : Fin n → (F →+* Qbar l) → ℤ) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ),
    (∀ τ, StrictMono fun j => hh j τ) ∧ (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) ∧
    ∀ σ, π.IsLocComp w σ → IsSubquotient σ.ρ (PS ω)

def OrdAt (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n) : Prop :=
  ∃ ψ, W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ ∧ ExpOf ι h π ψ

omit [NumberField F] [IsTotallyComplex F] [IsAlgClosure F Ω] in

def Unl (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) : Prop := ∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype

omit [IsAlgClosure F Ω] in

def TU (π : CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  Gam.TorAt π w ∧ ∀ s, Gam.SuppAt π w s → ImaginaryQuadraticEtaCharacter.Unl (Ideal.absNorm w.asIdeal) s

end At

def AutY {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l}
    (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)
    (P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.Part ι lam ξ → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.Part ι lam ξ // P lam d ξ Y}, Y.1.Y

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)

def ENDO : Prop :=
  ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ → Af.IsIrr ρ →
    ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
      ∀ v : Vl l L, ExpOf ι (s.hw v) π (x.psi v)

end U

def OrdJac : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → ∀ (c : ℕ) (φ : (glIwa k n).T →* ℂˣ),
    (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (c + 1) → φ (eT k n i y) = 1) → ∀ v ∈ (glIwa k n).eig π c φ, v ≠ 0 →
    ∀ a : ℕ → ℂ, (∀ j : Fin n, a (j + 1) ≠ 0 ∧ (glIwa k n).uOp π (al k n (j + 1)) v = a (j + 1) • v) →
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsInvOn φ ω ∧ IsSubquotient π (PS ω) ∧
      ∀ j : Fin n, psEig ω (j + 1) = a (j + 1)

def OrdScal : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.Part ι lam ξ) (K : H.Lev) (e : ℕ), c0 ≤ e → ∀ F ∈ Y.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K e, F ≠ 0 →
    ∀ (v : H.V) (b : Fin n → ℂ), (∀ j, b j ≠ 0 ∧ H.opC ι lam d (.inr (v, j)) F = b j • F) →
      ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient (Y.σl v).ρ (PS ω) ∧
        (∀ i (y : Uo ((H.Sl v).adicCompletion L)), (ω i y : ℂ) * ι (H.finPart θ x.toRingHom lam v i y) = 1) ∧
        ∀ j : Fin n, b j = (H.lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)

def PartPt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) P, AutY H ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → lam ∈ H.admitted →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] (y : H.TK θ a K →ₐ[c.O] Qbar l),
      y.toRingHom.comp (algebraMap A _) = x.toRingHom → ∃ (Y : H.Part ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d),
        P lam d ξ Y ∧ F ≠ 0 ∧ F ∈ Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 ∧ ∀ i, H.opC ι lam d i F = ι (y (H.gen θ a K i)) • F

def CoreOrd : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) P, AutY H ι P → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]
      [Alg.IsCO c.O (H.TK θ a K)] (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ),
      H.IsUniv θ a K (maximalIdeal _) D ψ → ∀ lam ∈ H.admitted, ∀ y : H.TK θ a K →ₐ[c.O] Qbar l,
      H.Arith θ (y.toRingHom.comp (algebraMap A _)) lam →
      ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.Part ι lam ξ), P lam d ξ Y ∧ D.map y.toRingHom = W.GDet.ofRep (W.mat Y.r) ∧
        ∀ v, ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, IsSubquotient (Y.σl v).ρ (PS ω) ∧
          ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh y.toRingHom (ψ v i))

def LinkU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
    ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → Af.IsIrr ρ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → ∀ B, GlobalTheory.LFun.HasSatGL w τ.ρ B →
        Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) →
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
      ∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)),
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → π.IsLocComp w τ

def AutUO : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ → AutY (hset Q τ₀) ι fun _ _ _ Y =>
      Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧
        Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)

def EndOrd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev), ∀ J : Ideal B.B, R.IsJ B K J → ENDO B ι J

def FlagPt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (x : B.Pt) (h : s.Wt n)
    (ρ : G L Ω →* GL (Fin n) (Qbar l)), x.Arith h → x.IsRep ρ → Af.IsIrr ρ →
    ∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)

def ExpTor : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (n : ℕ), 1 ≤ n → ∀ (ι : Qbar l ≃+* ℂ) (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A w),
    ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (π : CuspSub F n) (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ), ExpOf ι h π ψ → Gam.TorAt π w ∧
      (Unl ψ → TU π w) ∧ ∀ t : ℝ, ImaginaryQuadraticEtaCharacter.WinAt π t w → ∀ i j (m : ℕ), 1 ≤ m →
        ψ i ^ m ≠ (ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ^ m

def ConjTor : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, GlobalTheory.ContraPair.DualIsConj π →
    ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) →
      TU π w → TU π w'

def ConjUnl : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (ρ : G E Ω →* GL (Fin n) (Qbar l)) (π : CuspSub E n), Continuous ρ → GlobalTheory.ContraPair.DualIsConj π →
    Af.AttC ι ρ π → ∀ w w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∀ ψ : Fin n → Dec (F := E) A →* (Qbar l)ˣ, W.HasFlag (ρ.comp (Dec (F := E) A).subtype) ψ →
        (Win.Unl1 ρ w' → Unl ψ) ∧
        ((∀ i j (m : ℕ), 1 ≤ m → ψ i ^ m ≠ (ψ j * (cycBar E Ω l).comp (Dec (F := E) A).subtype) ^ m) → Win.PotUnl ρ w')

def ExtChar : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (v : HeightOneSpectrum (𝓞 K)) (w : GroundTheory.Global.SemiLocal.PlacesOver L v) (A : ValuationSubring Ω) (h : IsPlaceOver A w.1),
    ((l : ℕ) : 𝓞 K) ∈ v.asIdeal → ∀ a, IsLocalArtin h a → ∀ (κ : Dec (F := K) A →* (Qbar l)ˣ) (ψ : Dec (F := L) A →* (Qbar l)ˣ),
    Continuous κ → (∀ (g : Dec (F := L) A) (g' : Dec (F := K) A), (g' : G K Ω) = AlgEquiv.restrictScalarsHom K (g : G L Ω) → ψ g = κ g') →
    ∀ ω hh, OrdChar ι a ω hh ψ → ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ IsUnram (ω * χ.comp (Gam.nm w))

def BornL : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : UniversalOrdinaryDeterminantRing r)
    (J : Ideal B.B), ENDO B ι J → ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h →
    x.IsRep ρ → Af.IsIrr ρ → Continuous ρ → ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → Win.Unl1 ρ w →
      Win.PotUnl ρ w ∧ ∀ π : CuspSub L n, Af.AttC ι ρ π → TU π w

end UpperTheory.V.Z.Ord

end
