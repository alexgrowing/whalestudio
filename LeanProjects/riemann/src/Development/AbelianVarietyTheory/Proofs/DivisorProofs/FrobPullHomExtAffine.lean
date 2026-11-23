import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDatum

variable {O : Type} [CommRing O]

section Abelian

variable {T : Scheme.{0}} {A : Over T} [GrpObj A]

def IsSelfDual (c : O →+* O) (i : OAct O A) (P : LB (A ⊗ A).left) : Prop :=
  IsDual A A P ∧ LBIso (swap P) P ∧
    ∀ x, LBIso (ev P (fst A A ≫ i.act x) (snd A A)) (ev P (fst A A) (snd A A ≫ i.act (c x)))

def actPull (i : OAct O A) (x : O) {V : T.Opens} (hV : IsAffineOpen V) :
    primDR (onAff A hV) →ₗ[Γ(T, V)] primDR (onAff A hV) :=
  haveI := i.hom x
  primPull (dp0 Γ(T, V)) (𝟙 _) (A := onAff A hV) (B := onAff A hV) ((Over.pullback hV.fromSpec).map (i.act x))

variable {H : T.Modules} (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))

def IsDRAct (i : OAct O A) (ρ : O →+* End H) : Prop :=
  ∀ (x : O) (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
    e V hV ((VB.act ρ x).app V s) = actPull i x hV (e V hV s)

def IsHodgeIncl (a : omega A ⟶ H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(omega A, V)),
    e V hV (a.app V s) ∈ PrimitiveSubmodule (onAff A hV) ∧ HodgeSub.Corr A hV s (e V hV (a.app V s))

def IsPolPairing (P : LB (A ⊗ A).left) (β : H ⟶ dual H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V),
    ∃ (m : (onAff A hV ⊗ onAff A hV).left ⟶ (A ⊗ A).left)
      (φ : HdR (onAff A hV) →ₗ[Γ(T, V)] HdR (onAff A hV) →ₗ[Γ(T, V)] Γ(T, V)),
      m ≫ (fst A A).left = (fst (onAff A hV) (onAff A hV)).left ≫ pullback.fst A.hom hV.fromSpec ∧
      m ≫ (snd A A).left = (snd (onAff A hV) (onAff A hV)).left ≫ pullback.fst A.hom hV.fromSpec ∧
      IsCorrForm (dp0 Γ(T, V)) (𝟙 _) (onAff A hV) (onAff A hV) (P.pull m) φ ∧ φ.IsPerfPair ∧
      ∀ (s : Γ(H, V)) (x y : HdR (onAff A hV)), (∀ t, x (e V hV t) = dualApp (β.app V s) le_rfl t) →
        φ x y = y (e V hV s)

variable (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(T, ⊤)) = 0)

def IsLinFrob (Ψ : (frobPull p h0).obj H ⟶ H) : Prop :=
  ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
    e V hV (Ψ.app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s)) =
      ConjSeq.frobDR p Γ(T, V) (SS.FrobField.cast_zero h0 V) (onAff A hV) (e V hV s)

omit e in

def IsDRDatum (i : OAct O A) (P : LB (A ⊗ A).left) (ρ : O →+* End H) (a : omega A ⟶ H) (b : H ⟶ Lie A)
    (u : (frobPull p h0).obj (Lie A) ⟶ H) (v : H ⟶ (frobPull p h0).obj (omega A)) : Prop :=
  ∃ (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)) (β : H ⟶ dual H)
    (Ψ : (frobPull p h0).obj H ⟶ H),
    IsDRIso A H e ∧ IsDRAct e i ρ ∧ IsHodgeIncl e a ∧ IsPolPairing e P β ∧ IsLinFrob e p h0 Ψ ∧
    b = β ≫ dualMap a ∧ (frobPull p h0).map b ≫ u = Ψ ∧
    v ≫ (frobPull p h0).map (cartierDualToBidual (omega A)) ≫ DualPull.theta (frob T p h0) (Lie A) = β ≫ dualMap u

end Abelian

section Res

variable {S T : Scheme.{0}} {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {A : Over T} [GrpObj A] {f : T ⟶ S}
  {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)
  (hT : (p : Γ(T, ⊤)) = 0) {g : ℕ} (hg : IsVB (omega G) g)

def omegaRes : (Scheme.Modules.pullback f).obj (omega G) ≅ omega A := asIso (omegaBase h)

def lieRes : (Scheme.Modules.pullback f).obj (Lie G) ≅ Lie A := @asIso _ _ _ _ (lieBase h) (isIso_lieBase h hg)

def frobLieRes : (Scheme.Modules.pullback f).obj ((frobPull p hS).obj (Lie G)) ≅ (frobPull p hT).obj (Lie A) :=
  (frobPullPullbackIso p hS f hT).app (Lie G) ≪≫ (frobPull p hT).mapIso (lieRes h hg)

def frobOmegaRes : (Scheme.Modules.pullback f).obj ((frobPull p hS).obj (omega G)) ≅ (frobPull p hT).obj (omega A) :=
  (frobPullPullbackIso p hS f hT).app (omega G) ≪≫ (frobPull p hT).mapIso (omegaRes h)

end Res

section On

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C T : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G) {A : Over T} [GrpObj A] {f : T ⟶ C}
  {φ : A.left ⟶ G.left}

omit [Fact q.Prime] in
include k in

theorem cast_eq_zero (f : T ⟶ C) : (q : Γ(T, ⊤)) = 0 := SS.FrobField.cast_zero_of_hom f (natCast_eq_zero C q k)

def IsDRDatumOn (j : OAct O A) (h : IsGrpPullback A G f φ) (P : LB (A ⊗ A).left) {g : ℕ} (hg : IsVB (omega G) g)
    (d : TwoSeq.DieuDatumOn q k c i g f) : Prop :=
  IsDRDatum q (cast_eq_zero q k f) j P d.ρ ((omegaRes h).inv ≫ d.a) (d.b ≫ (lieRes h hg).hom)
    ((frobLieRes h q (natCast_eq_zero C q k) (cast_eq_zero q k f) hg).inv ≫ d.u)
    (d.v ≫ (frobOmegaRes h q (natCast_eq_zero C q k) (cast_eq_zero q k f)).hom)

end On

section Ext

variable {X : Scheme.{0}} {F G : X.Modules}

theorem hom_ext_affine {φ ψ : F ⟶ G}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ s : Γ(F, V), φ.app V s = ψ.app V s) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  refine QCoh.section_eq_of_cover _ (fun U : {U : X.Opens // IsAffineOpen U ∧ U ≤ W} ↦ U.1)
    (fun U ↦ U.2.2) ?_ _ _ fun U ↦ ?_
  · intro x hx
    obtain ⟨U, hU, hxU, hle⟩ := QCoh.exists_affine_mem_le x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hle⟩, hxU⟩
  · exact (QCoh.hom_app_res _ _ _).symm.trans ((h _ U.2.1 _).trans (QCoh.hom_app_res _ _ _))

theorem hom_dual_ext_affine {E : X.Modules} {φ ψ : E ⟶ dual F}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ (s : Γ(E, V)) (t : Γ(F, V)),
      dualApp (φ.app V s) le_rfl t = dualApp (ψ.app V s) le_rfl t) : φ = ψ := by
  refine hom_ext_affine fun V _ s ↦ dual_ext fun W hW t ↦ ?_
  refine AffinePairingGlue.fun_ext_affine fun U hU hUW ↦ ?_
  have k (χ : E ⟶ dual F) : resG X hUW (dualApp (χ.app V s) hW t) =
      dualApp (χ.app U (Twist.resM E (hUW.trans hW) s)) le_rfl (Twist.resM F hUW t) := by
    rw [Twist.app_resM, dualApp_res, dualApp_resM]
  rw [k, k, h U hU]

theorem frobPull_hom_ext_affine (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(X, ⊤)) = 0) {φ ψ : (frobPull p h0).obj F ⟶ G}
    (h : ∀ (V : X.Opens), IsAffineOpen V → ∀ s : Γ(F, V),
      φ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s) =
        ψ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s)) : φ = ψ := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (frob X p h0)
  apply (adj.homEquiv _ _).injective
  refine hom_ext_affine fun V hV s ↦ ?_
  have k (χ : (frobPull p h0).obj F ⟶ G) : (adj.homEquiv _ _ χ).app V s =
      χ.app V (QCoh.pullbackSections (frob X p h0) F (le_refl V) s) := by
    rw [Adjunction.homEquiv_unit]
    exact congrArg (χ.app V) (QCoh.res_self _ (le_refl V) _).symm
  rw [k, k, h V hV]

end Ext

end GlobalTheory.AbDatum
