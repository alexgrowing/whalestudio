import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

abbrev Vecs (Dw : Datum H) {X : Scheme.{0}} (t : SAB H X) (R : Type) [CommRing R] : Type :=
  ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ t.G.left)

def IsFrame {l : Level H} {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (f : c.F →+* R)
    (x : Sp R ⟶ X) (u : Vecs Dw t R) : Prop :=
  (∀ τ i, IsTanAtG t x (u τ i) ∧
    ∀ a : 𝓞 E, u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i) ∧
  ∀ τ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ w) →
    ∃! a : Fin (Dw.mult τ) → R, IsCombAtG t x (u τ) a w

def SameFlag (ty : (E →+* ℂ) → Finset ℕ) {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (u u' : Vecs Dw t R) : Prop :=
  ∀ τ, ∀ k ∈ ty τ, ∀ i : Fin (Dw.mult τ), (i : ℕ) < k →
    ∃ cf : Fin (Dw.mult τ) → R, (∀ j : Fin (Dw.mult τ), k ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG t x (u τ) cf (u' τ i)

def ProperLE (Dw : Datum H) (ty' ty : (E →+* ℂ) → Finset ℕ) : Prop :=
  ∀ σ, ∀ k ∈ ty' σ, 0 < k → k < Dw.mult σ → k ∈ ty σ

theorem ProperLE.of_subset {ty' ty : (E →+* ℂ) → Finset ℕ} (h : ∀ σ, ty' σ ⊆ ty σ) : ProperLE Dw ty' ty :=
  fun σ _ hk _ _ => h σ hk

theorem SameFlag.of_properLE {l : Level H} {c : Coeff l} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R]
    {f : c.F →+* R} {x : Sp R ⟶ X} {u u' : Vecs Dw t R} {ty' ty : (E →+* ℂ) → Finset ℕ} (hu : IsFrame t f x u)
    (hu' : IsFrame t f x u') (hty : ProperLE Dw ty' ty) (h : SameFlag ty t x u u') : SameFlag ty' t x u u' := by
  intro σ k hk i hi
  by_cases hlt : k < Dw.mult σ
  · exact h σ k (hty σ k hk (by omega) hlt) i hi
  · obtain ⟨cf, hcf, -⟩ := hu.2 σ _ (hu'.1 σ i).1 (hu'.1 σ i).2
    exact ⟨cf, fun j hj => absurd j.2 (by omega), hcf⟩

def Vecs.bc {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (u : Vecs Dw t R) :
    Vecs Dw t S := fun τ i => spMap (dualMap φ) ≫ u τ i

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

structure Pre (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where

  i : Idx H p

  dvd : i₀.l.Dvd i.l

  le : i₀.c.F ≤ i.c.F

  n : ℕ

  I : (PSpace (i.c.V W) n).IdealSheafData

  π : I.subscheme ⟶ (Y i).X

  ty : (E →+* ℂ) → Finset ℕ

  m : ℕ

  U : Fin m → I.subscheme.affineOpens

  alg : ∀ a, i.c.F →+* Γ(I.subscheme, (U a).1)

  fr : ∀ a, Vecs Dw (Y i).t Γ(I.subscheme, (U a).1)

variable {Y : LocalSystem Xo p W} {i₀ : Idx H p}

namespace Pre

variable (Z : Pre Y i₀)

abbrev X : Scheme.{0} := Z.I.subscheme

def s : Z.X ⟶ Sp (Z.i.c.V W) := Z.I.subschemeι ≫ PSpace.str _ Z.n

def chart (a : Fin Z.m) : Sp Γ(Z.X, (Z.U a).1) ⟶ Z.X := (Z.U a).2.fromSpec

def opn : Set Z.X := Z.π ⁻¹' Set.range (Y Z.i).j

def FlagAt {k : Type} [Field k] (w : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) : Prop :=
  ∃ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k), spMap φ ≫ Z.chart a = w ∧
    IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (w ≫ Z.π) u ∧ SameFlag Z.ty (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ) u

end Pre

structure Mdl (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type extends Pre Y i₀ where

  π_s : π ≫ (Y i).s = toPre.s

  normal : IsNormalScheme toPre.X

  flat : Flat toPre.s

  dense : Dense toPre.opn

  cover : ⋃ a, ((U a).1 : Set toPre.X) = toPre.opn

  alg_s : ∀ a, toPre.chart a ≫ toPre.s = spMap ((alg a).comp (i.c.V W).subtype)

  smooth : ∀ a, Smooth (toPre.chart a ≫ π)

  frame : ∀ a, IsFrame (Y i).t (alg a) (toPre.chart a ≫ π) (fr a)

  glue : ∀ (k : Type) [Field k] (a a' : Fin m) (φ : Γ(toPre.X, (U a).1) →+* k) (φ' : Γ(toPre.X, (U a').1) →+* k),
    spMap φ ≫ toPre.chart a = spMap φ' ≫ toPre.chart a' →
      SameFlag ty (Y i).t (spMap φ ≫ toPre.chart a ≫ π) ((fr a).bc φ) ((fr a').bc φ')

  bij : ∀ (k : Type) [Field k] (f : i.c.F →+* k) (y : Sp k ⟶ (Xo i.l).XF i.c), y ≫ pullback.snd _ _ = spMap f →
    ∀ u, IsFrame (Y i).t f (y ≫ (Y i).j) u → ∃! w : Sp k ⟶ toPre.X, w ≫ π = y ≫ (Y i).j ∧ toPre.FlagAt w u

namespace Mdl

variable (Z : Mdl Y i₀)

def t : SAB H Z.X := (exists_sab Z.π (Y Z.i).t).choose

def tMap : SABMap Z.t (Y Z.i).t Z.π := (exists_sab Z.π (Y Z.i).t).choose_spec.some

structure Pt : Type where

  C : SCF p

  P : PointsOfFlagModel.PtC (Y Z.i) C

  z : Sp ↥(intO ↥C.S) ⟶ Z.X

  z_π : z ≫ Z.π = P.yt

def Pt.fld {Z : Mdl Y i₀} (y : Z.Pt) : Formalism.MainNotions.ModuliIntegralCharts.CF p := y.C.toCF

def Pt.gen {Z : Mdl Y i₀} (y : Z.Pt) : Sp ↥y.C.S ⟶ Z.X := spMap (intO ↥y.C.S).subtype ≫ y.z

def inQ (x : Z.X) : Prop := CharZero (Z.X.residueField x)

def abP (x : Z.X) : Prop := Z.π x ∈ abLocus (Y Z.i).t.G

def isGenP (x : Z.X) : Prop := ∀ x' : Z.X, x' ⤳ x → x' = x

def Gen : Type := {x : Z.X // ¬ Z.inQ x ∧ ∀ x' : Z.X, ¬ Z.inQ x' → x' ⤳ x → x' = x}

def free (a m : ℕ) : Z.X.Modules :=
  GlobalTheory.twist (GlobalTheory.QCoh.freeModule Z.X (Fin m)) ((GlobalTheory.ProjSpace.On (Z.i.c.V W) Z.n (-(a : ℤ))).pull Z.I.subschemeι)

structure Sh : Type where

  a : ℕ

  m : ℕ

  a' : ℕ

  m' : ℕ

  φ : Z.free a' m' ⟶ Z.free a m

def Sh.toMod {Z : Mdl Y i₀} (F : Z.Sh) : Z.X.Modules := cokernel F.φ

open Classical in

def ofMod (F : Z.X.Modules) : Z.Sh :=
  if h : ∃ S : Z.Sh, Nonempty (S.toMod ≅ F) then h.choose else ⟨0, 0, 0, 0, 0⟩

theorem ofMod_iso {F : Z.X.Modules} (h : ∃ S : Z.Sh, Nonempty (S.toMod ≅ F)) : Nonempty ((Z.ofMod F).toMod ≅ F) := by
  rw [ofMod, dif_pos h]
  exact h.choose_spec

def Idl : Type := {J : Z.X.IdealSheafData // ∀ x ∈ J.support, x ∉ Z.opn}

def powP (J : Z.Idl) : Prop := ∃ k : ℕ, ∀ U : Z.X.affineOpens, ((p : Γ(Z.X, U.1)) ^ k) ∈ J.1.ideal U

end Mdl

def IsTrans (i i₂ : Idx H p) (τ : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ) : Prop :=
  ∃ (b : i.c.V W →+* i₂.c.V W) (π' : (Y i₂).X ⟶ pullback (Y i).s (spMap b))
    (r : (Xo i₂.l).XF i₂.c ⟶ (Xo i.l).XF i.c), IsIncl b ∧
    π' ≫ pullback.fst _ _ = τ ∧ π' ≫ pullback.snd _ _ = (Y i₂).s ∧ IsFinite π' ∧ (Y i₂).j ≫ τ = r ≫ (Y i).j ∧
    (∀ a, ((Y i₂).oF.eta a ^ (i₂.l.M / i.l.M)).left ≫ (Y i₂).m.φ ≫ mu.φ = r ≫ ((Y i).oF.eta a).left ≫ (Y i).m.φ) ∧
    (∀ a, ((Y i₂).oF.etaA a ^ (i₂.l.A / i.l.A)).left ≫ (Y i₂).m.φ ≫ mu.φ = r ≫ ((Y i).oF.etaA a).left ≫ (Y i).m.φ)

def NatImg (Z₁ Z₂ : Mdl Y i₀) {k : Type} [Field k] (w₁ : Sp k ⟶ Z₁.X) (w₂ : Sp k ⟶ Z₂.X) : Prop :=
  ∃ (τ : (Y Z₁.i).X ⟶ (Y Z₂.i).X) (mu : SABMap (Y Z₁.i).t (Y Z₂.i).t τ) (u : Vecs Dw (Y Z₁.i).t k),
    IsTrans Z₂.i Z₁.i τ mu ∧ w₂ ≫ Z₂.π = w₁ ≫ Z₁.π ≫ τ ∧ Z₁.FlagAt w₁ u ∧ Z₂.FlagAt w₂ (fun σ i => u σ i ≫ mu.φ)

def NatCorr (Z₁ Z₂ : Mdl Y i₀) : Prop := Z₂.i.l.Dvd Z₁.i.l ∧ Z₂.i.c.F ≤ Z₁.i.c.F ∧ ProperLE Dw Z₂.ty Z₁.ty

def IsNatMap (Z₁ Z₂ : Mdl Y i₀) (f : Z₁.X ⟶ Z₂.X) : Prop :=
  NatCorr Z₁ Z₂ ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ Z₁.X), Set.range w ⊆ Z₁.opn → NatImg Z₁ Z₂ w (w ≫ f)

def Corr (Z₁ Z₂ : Mdl Y i₀) : Prop := Z₂.i.l.Dvd Z₁.i.l ∧ Z₂.i.c.F ≤ Z₁.i.c.F ∧ ∀ σ, Z₂.ty σ ⊆ Z₁.ty σ

def IsMap (Z₁ Z₂ : Mdl Y i₀) (f : Z₁.X ⟶ Z₂.X) : Prop :=
  Corr Z₁ Z₂ ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ Z₁.X), Set.range w ⊆ Z₁.opn → NatImg Z₁ Z₂ w (w ≫ f)

def IsNBlow (Z : Mdl Y i₀) (J : Z.Idl) (Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ ∃ (X' : Scheme.{0}) (b : X' ⟶ Z.X) (ν : Z'.X ⟶ X'),
    ReciprocityTheory.AnForm.R.FinalTheorems.Blowup b J.1 ∧ IsFinite ν ∧ IsMap Z' Z (ν ≫ b)

def IsNatDiag (Z₁ Z₂ Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z₁.i ∧ Z'.ty = Z₁.ty ∧ ∃ (f₁ : Z'.X ⟶ Z₁.X) (f₂ : Z'.X ⟶ Z₂.X), IsMap Z' Z₁ f₁ ∧ IsNatMap Z' Z₂ f₂ ∧
    IsFinite (prod.lift f₁ f₂)

def IsDiag (Z₁ Z₂ Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z₁.i ∧ Z'.ty = Z₁.ty ∧ ∃ (f₁ : Z'.X ⟶ Z₁.X) (f₂ : Z'.X ⟶ Z₂.X), IsMap Z' Z₁ f₁ ∧ IsMap Z' Z₂ f₂ ∧
    IsFinite (prod.lift f₁ f₂)

open Classical in

def blowUp (Z : Mdl Y i₀) (J : Z.Idl) : Mdl Y i₀ := if h : ∃ Z', IsNBlow Z J Z' then h.choose else Z

open Classical in

def natDiagCl (Z₁ Z₂ : Mdl Y i₀) : Mdl Y i₀ := if h : ∃ Z', IsNatDiag Z₁ Z₂ Z' then h.choose else Z₁

open Classical in

def diagCl (Z₁ Z₂ : Mdl Y i₀) : Mdl Y i₀ := if h : ∃ Z', IsDiag Z₁ Z₂ Z' then h.choose else Z₁

theorem blowUp_spec {Z : Mdl Y i₀} {J : Z.Idl} (h : ∃ Z', IsNBlow Z J Z') : IsNBlow Z J (blowUp Z J) := by
  rw [blowUp, dif_pos h]
  exact h.choose_spec

theorem natDiagCl_spec {Z₁ Z₂ : Mdl Y i₀} (h : ∃ Z', IsNatDiag Z₁ Z₂ Z') : IsNatDiag Z₁ Z₂ (natDiagCl Z₁ Z₂) := by
  rw [natDiagCl, dif_pos h]
  exact h.choose_spec

theorem diagCl_spec {Z₁ Z₂ : Mdl Y i₀} (h : ∃ Z', IsDiag Z₁ Z₂ Z') : IsDiag Z₁ Z₂ (diagCl Z₁ Z₂) := by
  rw [diagCl, dif_pos h]
  exact h.choose_spec

theorem NatCorr.refl (Z : Mdl Y i₀) : NatCorr Z Z := ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ _ hk _ _ => hk⟩

theorem NatCorr.trans {Z₁ Z₂ Z₃ : Mdl Y i₀} (h : NatCorr Z₁ Z₂) (h' : NatCorr Z₂ Z₃) : NatCorr Z₁ Z₃ :=
  ⟨⟨h'.1.1.trans h.1.1, h.1.2.1.trans h'.1.2.1, h'.1.2.2.trans h.1.2.2⟩, h'.2.1.trans h.2.1,
    fun σ k hk h₀ h₁ => h.2.2 σ k (h'.2.2 σ k hk h₀ h₁) h₀ h₁⟩

theorem Corr.natCorr {Z₁ Z₂ : Mdl Y i₀} (h : Corr Z₁ Z₂) : NatCorr Z₁ Z₂ := ⟨h.1, h.2.1, .of_subset h.2.2⟩

theorem IsMap.isNatMap {Z₁ Z₂ : Mdl Y i₀} {f : Z₁.X ⟶ Z₂.X} (h : IsMap Z₁ Z₂ f) : IsNatMap Z₁ Z₂ f := ⟨h.1.natCorr, h.2⟩

theorem IsNatMap.isMap {Z₁ Z₂ : Mdl Y i₀} {f : Z₁.X ⟶ Z₂.X} (h : IsNatMap Z₁ Z₂ f) (hty : ∀ σ, Z₂.ty σ ⊆ Z₁.ty σ) :
    IsMap Z₁ Z₂ f := ⟨⟨h.1.1, h.1.2.1, hty⟩, h.2⟩

theorem isNatDiag_iff_isDiag {Z₁ Z₂ Z' : Mdl Y i₀} (hty : ∀ σ, Z₂.ty σ ⊆ Z₁.ty σ) : IsNatDiag Z₁ Z₂ Z' ↔ IsDiag Z₁ Z₂ Z' :=
  ⟨fun ⟨a, b, f₁, f₂, c, d, e⟩ => ⟨a, b, f₁, f₂, c, d.isMap (b ▸ hty), e⟩,
    fun ⟨a, b, f₁, f₂, c, d, e⟩ => ⟨a, b, f₁, f₂, c, d.isNatMap, e⟩⟩

example : ProperLE Dw (fun σ => {0, Dw.mult σ}) (fun _ => ∅) := fun σ k hk h₀ h₁ => by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  omega

example (σ : E →+* ℂ) (h : Dw.mult σ = 2) : ¬ ProperLE Dw (fun _ => {1}) (fun _ => ∅) := fun h' =>
  Finset.notMem_empty 1 (h' σ 1 (Finset.mem_singleton_self 1) one_pos (by omega))

example (Z₁ Z₂ : Mdl Y i₀) (hi : Z₁.i = Z₂.i) (h₂ : ∀ σ, Z₂.ty σ ⊆ {0, Dw.mult σ}) : NatCorr Z₁ Z₂ :=
  ⟨hi ▸ (NatCorr.refl Z₁).1, hi ▸ le_rfl, fun σ k hk _ _ => by
    have := h₂ σ hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega⟩

def IsLvl (i₀ i : Idx H p) : Option ℕ → Prop
  | none => i = i₀
  | some n => i.l.M = i₀.l.M ∧ i.l.Mb = i₀.l.Mb ∧ i.l.A = i₀.l.A * p ^ n ∧
      i.c.F = i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta i.l.M'}

structure Bases (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where

  X : Option ℕ → Mdl Y i₀

  lvl : ∀ b, IsLvl i₀ (X b).i b

  iso : ∀ b, IsIso (X b).π

  ty : ∀ b σ, (X b).ty σ = ∅

theorem Bases.natCorr_base (B : Bases Y i₀) (Z : Mdl Y i₀) : NatCorr Z (B.X none) := by
  have h : (B.X none).i = i₀ := B.lvl none
  exact ⟨by rw [h]; exact Z.dvd, by rw [h]; exact Z.le, fun σ k hk => by simp [B.ty none σ] at hk⟩

end GlobalTheory.LocM
