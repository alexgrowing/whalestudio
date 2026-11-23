import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelVerticalLettersSetup

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct

namespace GlobalTheory.ChainPts

section Pre

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O} {Λ : Type} [CommRing Λ]

structure PreChain (o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) where
  g : Γ(B.X, ⊤)
  γ : ℕ → Γ(B.X, ⊤)
  π_root : IsRootOfP p π (p - 1)
  g_root : IsRootOfP p g p
  γ_root : ∀ n < o, IsRootOfP p (γ n) (p ^ (n + 1))
  hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0
  q : ℕ → EPres B Λ
  l : ℕ → EPres B Λ
  step : ∀ n < o, IsExtA (q (n + 1)).mod (q n).mod (l n).mod
  l_free : ∀ n < o, LocFreeMod (γ n) (l n).mod.V
  l_last : ∀ n < o, Nonempty ((frobA p hp)^[n + 1] (l n).mod ≅ cokernel (smulA Lie (p : Γ(B.X, ⊤))))
  q_kill : ∀ n < o, Kills g (q (n + 1)).mod.V
  q_frob : ∀ n < o, Nonempty ((q n).mod ≅ frobA p hp (q (n + 1)).mod)
  j : Lie ⟶ (q 0).mod
  j_kill : smulA Lie π ≫ j = 0
  ρ : Om ⟶ cokernel j
  ρ_epi : Epi ρ

variable {p}

theorem EqChain.exists_preChain {o : ℕ} (Q : EqChain p B Λ o) :
    ∃ P : PreChain p o Q.lw.E' Q.oo.E Q.π, P.q = Q.q ∧ P.l = Q.l := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := Q.c3
  haveI := hS.epi_g
  let j : Q.lw.E' ⟶ (Q.q 0).mod := (cokernel.π Q.wl ≫ e₁.inv) ≫ S.f ≫ e₂.hom
  have e : cokernel Q.oo.ψ ≅ cokernel j := e₃.symm ≪≫ (hS.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel S.f)) ≪≫
    (cokernelCompIsIso S.f e₂.hom).symm ≪≫ (cokernelEpiComp _ _).symm
  exact ⟨{ Q with
    j := j
    j_kill := by simp only [j, ← Q.lw_wl, Category.assoc, cokernel.condition_assoc, zero_comp, comp_zero]
    ρ := cokernel.π Q.oo.ψ ≫ e.hom
    ρ_epi := epi_comp _ _ }, rfl, rfl⟩

example (p : ℕ) [Fact p.Prime] (o : ℕ) (Λ : Type) [CommRing Λ] (χ : Λ →+* ℤ) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : CharZero O)
      (_ : CharP (ResidueField O) p) (Lie Om : AM (Model.base O) Λ) (π : Γ((Model.base O).X, ⊤))
      (P : PreChain p o Lie Om π), (∀ n, ¬ IsZero (P.q n).mod.V) ∧ ∀ n, ¬ IsZero (P.l n).mod.V := by
  obtain ⟨O, _, _, _, _, _, Q, -, -, h1, h2⟩ := Examples₂.exists_base_eqChain p o Λ χ
  obtain ⟨P, hq, hl⟩ := Q.exists_preChain
  exact ⟨O, _, _, _, inferInstance, inferInstance, _, _, _, P, by rw [hq]; exact h1, by rw [hl]; exact h2⟩

end Pre

def kerAt {X : Scheme.{0}} {R : Type} [CommRing R] (w : Sp R ⟶ X) {F Q : X.Modules} (u : F ⟶ Q) {V : X.Opens}
    (hV : ⊤ ≤ w ⁻¹ᵁ V) {r : ℕ} (e : Fin r → Γ(F, V)) : Set (Fin r → R) :=
  {c | ((Scheme.Modules.pullback w).map u).app ⊤
    (∑ l, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c l) • pullbackSections w F hV (e l)) = 0}

section Sys

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {B : Vert.Model O} {Λ : Type} [CommRing Λ]

def cstBp (U : AffOp B.X) (a : Γ(B.X, ⊤)) : U.Bp := algebraMap Γ(B.X, U.1) U.Bp (resG B.X le_top a)

abbrev SecBp (F : B.X.Modules) (U : AffOp B.X) : Type := U.Bp ⊗[Γ(B.X, U.1)] Γ(F, U.1)

abbrev ChainsBp (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) : Type :=
  ∀ U : AffOp B.X, RChain p U.Bp h o (cstBp U π) (fun n => cstBp U (γ n)) (SecBp Lie.V U) (SecBp Om.V U)

variable {p} {h o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)}

def IsSys (C : ChainsBp p h o Lie Om π γ) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) : Prop :=
  (∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1),
    (∀ n, (C U').L n = Submodule.span U'.Bp (GlobalTheory.PerfdLat.piMap (AffOp.res hle) (Fin h) '' ((C U).L n : Set (Fin h → U.Bp)))) ∧
    ∃ (l : SecBp Lie.V U →ₛₗ[AffOp.res hle] SecBp Lie.V U') (m : SecBp Om.V U →ₛₗ[AffOp.res hle] SecBp Om.V U'),
      (∀ s, l (1 ⊗ₜ s) = 1 ⊗ₜ resM Lie.V hle s) ∧ (∀ s, m (1 ⊗ₜ s) = 1 ⊗ₜ resM Om.V hle s) ∧
        (C U).Map (C U') (AffOp.res hle) 1 l m) ∧
  ∀ (U : AffOp B.X) (a : Λ), ∃ (l : SecBp Lie.V U →ₗ[U.Bp] SecBp Lie.V U) (m : SecBp Om.V U →ₗ[U.Bp] SecBp Om.V U),
    (∀ s, l (1 ⊗ₜ s) = 1 ⊗ₜ (Lie.ρ a : Lie.V ⟶ Lie.V).app _ s) ∧ (∀ s, m (1 ⊗ₜ s) = 1 ⊗ₜ (Om.ρ a : Om.V ⟶ Om.V).app _ s) ∧
      (C U).Map (C U) (RingHom.id _) (M a) l m

def KerMatch (C : ChainsBp p h o Lie Om π γ) {X' : Scheme.{0}} (f : X' ⟶ B.X) {Q₁ Q₂ : X'.Modules}
    (j' : (Scheme.Modules.pullback f).obj Lie.V ⟶ Q₁) (ρ' : (Scheme.Modules.pullback f).obj Om.V ⟶ Q₂) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Subring K), (∀ x : K, IsIntegral R x → x ∈ R) → (p : K) ≠ 0 →
    ∀ (w : Sp R ⟶ X') (U : AffOp B.X) (hU : ⊤ ≤ w ⁻¹ᵁ f ⁻¹ᵁ U.1), ∃ φ : U.Bp →+* R, spMap φ ≫ U.toX = w ≫ f ∧
      (∀ (r : ℕ) (e : Fin r → Γ(Lie.V, U.1)),
        kerAt w j' hU (fun l => pullbackSections f Lie.V le_rfl (e l)) = (C U).kerJ φ fun l => 1 ⊗ₜ e l) ∧
      ∀ (r : ℕ) (e : Fin r → Γ(Om.V, U.1)),
        kerAt w ρ' hU (fun l => pullbackSections f Om.V le_rfl (e l)) = (C U).kerR φ fun l => 1 ⊗ₜ e l

end Sys

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (Z : LocM.Mdl Y i₀)

def IsEqLat {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} (h : B.X ⟶ Z.X) {r : ℕ}
    (x : Fin r → Letter Dw) (d : Bool) (F : AM B (𝓞 E)) (s : ∀ a : Fin Z.m, Fin r → Γ(F.V, h ⁻¹ᵁ (Z.U a).1)) : Prop :=
  IsAdd F ∧ GlobalTheory.VB.IsVB F.V r ∧ IsLat Z h x d false F.V s ∧
    ∀ (a : Fin Z.m) (i : Fin r) (c : 𝓞 E), (F.ρ c : F.V ⟶ F.V).app _ (s a i) =
      (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c (x i).1 (if d then H.bar c else c))) • s a i

section Cond

variable {X : Scheme.{0}} (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) {F : X.Modules}
  {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} (hs : ∀ a, GlobalTheory.VB.IsFrame (s a))

def JCond (π : Γ(X, ⊤)) (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X) (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S)
    {V : X.Opens} {e : Fin r → Γ(F, V)} (he : GlobalTheory.VB.IsFrame e) (K : Set (Fin r → ↥(intO ↥y.C.S))) : Prop :=
  ∀ (cf : Fin r → ↥y.C.S) (v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left),
    IsCombAtG (Y Z.i).t (y.gen ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v →
      (v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) true ↔ ∃ c ∈ K, ∀ l, (c l : ↥y.C.S) =
        valF (spMap (intO ↥y.C.S).subtype ≫ w) ⊤ π *
          ∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (coef false he (hs a) l i))

def RCond (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X) (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S)
    {V : X.Opens} {e : Fin r → Γ(F, V)} (he : GlobalTheory.VB.IsFrame e) (K : Set (Fin r → ↥(intO ↥y.C.S))) : Prop :=
  ∀ (cf : Fin r → ↥y.C.S) (v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left),
    IsCombAtG (Y Z.i).t (y.gen ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v →
      (v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) true ↔ ∀ c ∈ K,
        ‖∑ l, (c l : ↥y.C.S) * ∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (coef true he (hs a) l i)‖ ≤ 1)

def PtJ (π : Γ(X, ⊤)) {Q : X.Modules} (j : F ⟶ Q) : Prop :=
  ∀ (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X), w ≫ h = y.z → ∀ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S),
    spMap φ ≫ Z.chart a = y.gen → ∃ (V : X.Opens) (e : Fin r → Γ(F, V)) (he : GlobalTheory.VB.IsFrame e) (hV : ⊤ ≤ w ⁻¹ᵁ V),
      JCond Z h x hs π y w a φ he (kerAt w j hV e)

def PtR {Q : X.Modules} (ρ : F ⟶ Q) : Prop :=
  ∀ (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X), w ≫ h = y.z → ∀ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S),
    spMap φ ≫ Z.chart a = y.gen → ∃ (V : X.Opens) (e : Fin r → Γ(F, V)) (he : GlobalTheory.VB.IsFrame e) (hV : ⊤ ≤ w ⁻¹ᵁ V),
      RCond Z h x hs y w a φ he (kerAt w ρ hV e)

end Cond

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} (h : B.X ⟶ Z.X) {r : ℕ}
  (x x' : Fin r → Letter Dw) {Lie Om : AM B (𝓞 E)}
  {sL : ∀ a : Fin Z.m, Fin r → Γ(Lie.V, h ⁻¹ᵁ (Z.U a).1)} (hL : ∀ a, GlobalTheory.VB.IsFrame (sL a))
  {sO : ∀ a : Fin Z.m, Fin r → Γ(Om.V, h ⁻¹ᵁ (Z.U a).1)} (hO : ∀ a, GlobalTheory.VB.IsFrame (sO a))

def SysPt {n o : ℕ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)} (C : ChainsBp p n o Lie Om π γ) : Prop :=
  ∀ (y : Z.Pt) (U : AffOp B.X) (ψ : U.Bp →+* ↥(intO ↥y.C.S)), (spMap ψ ≫ U.toX) ≫ h = y.z →
    ∀ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen →
      (∀ (e : Fin r → Γ(Lie.V, U.1)) (he : GlobalTheory.VB.IsFrame e),
        JCond Z h x hL π y (spMap ψ ≫ U.toX) a φ he ((C U).kerJ ψ fun l => 1 ⊗ₜ e l)) ∧
      ∀ (e : Fin r → Γ(Om.V, U.1)) (he : GlobalTheory.VB.IsFrame e),
        RCond Z h x' hO y (spMap ψ ≫ U.toX) a φ he ((C U).kerR ψ fun l => 1 ⊗ₜ e l)

variable {Z h x}

abbrev pullS {X X' : Scheme.{0}} (g : X' ⟶ X) {k : X ⟶ Z.X} {F : X.Modules}
    (s : ∀ a : Fin Z.m, Fin r → Γ(F, k ⁻¹ᵁ (Z.U a).1)) (a : Fin Z.m) (i : Fin r) :
    Γ((Scheme.Modules.pullback g).obj F, (g ≫ k) ⁻¹ᵁ (Z.U a).1) :=
  pullbackSections g F (Scheme.Hom.comp_preimage g k _).le (s a i)

theorem IsEqLat.pull {B' : Vert.Model O} (g : B'.X ⟶ B.X) {d : Bool} {F : AM B (𝓞 E)}
    {s : ∀ a : Fin Z.m, Fin r → Γ(F.V, h ⁻¹ᵁ (Z.U a).1)} (k : IsEqLat Z h x d F s) :
    IsEqLat Z (g ≫ h) x d ((pullA g).obj F) (pullS g s) := by
  obtain ⟨h0, vb, h1, h3⟩ := k
  refine ⟨PullHT.isAdd_pullA g h0, vb.pullback g, PullHT.isLat_pull g h vb h1, fun a i c => ?_⟩
  change ((Scheme.Modules.pullback g).map (F.ρ c : F.V ⟶ F.V)).app _ _ = _
  rw [pullS, pullback_map_app_pullbackSections, h3, pullbackSections_smul]
  congr 1
  rw [Scheme.Hom.comp_app]
  first
    | (erw [Scheme.Hom.appLE_eq_app]; rfl)
    | (simp only [Scheme.Hom.appLE]
       erw [show (homOfLE (le_refl (g ⁻¹ᵁ h ⁻¹ᵁ ↑(Z.U a)))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.comp_id]
       rfl)

end Lat

def SysCover {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
    {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  ∀ (c : (nmodel z.Z).Comp) (o : ℕ) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)),
    GlobalTheory.IsNormalScheme B.X → f.relDim = 0 → (∃ ζ : Γ(B.X, ⊤), IsPrimitiveRoot ζ (p ^ (o + 2))) →
      ∃ (Lie Om : AM B (𝓞 D.host.E)) (sL : _) (sO : _)
        (hL : IsEqLat z.Z (f.f ≫ (nmodel z.Z).compι c) (xAll S) false Lie sL)
        (hO : IsEqLat z.Z (f.f ≫ (nmodel z.Z).compι c) (fun k => xAll S k.rev) true Om sO)
        (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (n : ℕ) (M : 𝓞 D.host.E →+* Matrix (Fin n) (Fin n) ℤ)
        (C : ChainsBp p n o Lie Om π γ), IsRootOfP p π (p - 1) ∧ (∀ k ≤ o, IsRootOfP p (γ k) (p ^ (k + 1))) ∧ IsSys C M ∧
          SysPt z.Z (f.f ≫ (nmodel z.Z).compι c) (xAll S) (fun k => xAll S k.rev) hL.2.2.1.frame hO.2.2.1.frame C

def SysCoverSt : Prop := AtAll fun _ _ _ _ _ _ _ z => SysCover z

end GlobalTheory.ChainPts

end
