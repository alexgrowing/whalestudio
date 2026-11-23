import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueTransUnit
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InjectiveOfFlatLocal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

namespace GlobalTheory.LocM

namespace Bdy

section Reg

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (maximalIdeal R) D A G) (hR : AdmBase R (maximalIdeal R)) [GeometricallyConnected G.hom]

theorem exists_coef_zero (x : FractionRing R) : ∃ s, coef U hR s 0 = x := by
  obtain ⟨Φ, hΦ, -⟩ := FamFree.exists_fam_single (F := FractionRing R) GlobalTheory.globalFns_holds D.tau_bimult le_rfl 0
    (x • secGenK D 0)
  obtain ⟨s, rfl⟩ := (expand_bijective U hR).2 Φ
  exact ⟨s, smul_left_injective _ (secGenK_ne D 0) ((coef_spec U hR s 0).symm.trans hΦ)⟩

end Reg

namespace BDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t₀ : SAB H X} {x : X} (B : BDat t₀ x)

abbrev Ylat : Type := B.U.D.toPre.X

def chX : Type := B.Ylat
instance : AddCommGroup B.chX := inferInstanceAs (AddCommGroup B.Ylat)
instance : Module (𝓞 E) B.chX := Module.compHom B.Ylat (H.bar : 𝓞 E →+* 𝓞 E)

def phi : B.Ylat ≃+ B.chX := AddEquiv.refl _

def tau : B.Ylat → B.Ylat → (FractionRing B.R)ˣ :=
  letI := H.starRing
  (exists_reading B.U.D B.U.oD).choose

theorem tau_spec : letI := H.starRing; IsReading B.U.D (𝓞 E) B.tau :=
  letI := H.starRing
  (exists_reading B.U.D B.U.oD).choose_spec

theorem adm : AdmBase B.R (maximalIdeal B.R) := ⟨B.noeth, B.dom, B.normal, B.complete⟩

instance : GeometricallyConnected B.t.G.hom := B.t.semi.geomConnected

def fc : SecGK B.U.U →ₗ[FractionRing B.R] (B.chX → FractionRing B.R) := coef B.U.U B.adm

def trU {w : 𝓞 E} (hw : w + H.bar w = 1) (a : B.Ylat) (χ : B.chX) : B.Rˣ :=
  letI := H.starRing
  (existsUnique_transUnit B.U.oD B.tau_spec hw a χ).choose

end BDat

end Bdy

open Bdy

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem bar_eq_of_conj (A : Amb D) {c c' : 𝓞 D.host.E} (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) :
    c' = A.H.bar c := by
  apply RingOfIntegers.ext
  rw [hc, A.H.bar_eq]
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem cmHostUnit_add_conj_eq_one (A : Amb D) : w0 D + A.H.bar (w0 D) = 1 := by
  rw [← bar_eq_of_conj A (one_sub_halfSqrt_eq_conj D), add_sub_cancel]

namespace At

variable (ct : At S κ p)

def BPt : Type :=
  {x : ct.Xm.X // IsClosed ({x} : Set ct.Xm.X) ∧ ¬ ct.Xm.abP x ∧ IsDomain (Cpl ct.Xm.X x) ∧ IsIntegrallyClosed (Cpl ct.Xm.X x)}

theorem nonempty_bdat (z : ct.BPt) : Nonempty (BDat ct.Xm.t z.1) :=
  haveI := z.2.2.2.1
  haveI := z.2.2.2.2
  Bdy.nonempty_bdat ct.hp.ne_zero ct.hW ct.Xm ((S.sys.clauses p ct.W ct.hp ct.hW).2 _).1
    ((S.sys.clauses p ct.W ct.hp ct.hW).2 _).2.1 z.1

def bdat (z : ct.BPt) : BDat ct.Xm.t z.1 := pick (ct.nonempty_bdat z)

end At

def bdyTrue (ct : At S κ p) : BdySt ct where
  BPt := ct.BPt
  Rl z := (ct.bdat z).R
  Yb z := (ct.bdat z).Ylat
  Xb z := (ct.bdat z).chX
  phib z := (ct.bdat z).phi
  phib_conj z c c' hc a := by
    obtain rfl := bar_eq_of_conj A hc
    rfl
  taub z := (ct.bdat z).tau
  taub_add_left z := letI := A.H.starRing; (ct.bdat z).tau_spec.add_left
  taub_add_right z a χ χ' := by
    letI := A.H.starRing
    have h := (ct.bdat z).tau_spec
    exact (h.symm _ _).trans ((h.add_left χ χ' a).trans (congrArg₂ (· * ·) (h.symm _ _) (h.symm _ _)))
  taub_symm z := letI := A.H.starRing; (ct.bdat z).tau_spec.symm
  taub_smul z := letI := A.H.starRing; (ct.bdat z).tau_spec.bal
  taub_pos z := letI := A.H.starRing; (ct.bdat z).tau_spec.pos
  Sg z := SecGK (ct.bdat z).U.U
  Sreg z := secReg (ct.bdat z).U.U
  fc z := (ct.bdat z).fc
  trU z := (ct.bdat z).trU (cmHostUnit_add_conj_eq_one A)

example (A : Amb D) : w0 D = A.H.w0 := by
  apply RingOfIntegers.ext
  have h := congrArg (algebraMap (𝓞 D.host.E) D.host.E) A.H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, map_ofNat] at h
  have h' : algebraMap (𝓞 D.host.E) D.host.E A.H.rt = D.host.sqrtMinusD := A.rt_eq
  change (1 + D.host.sqrtMinusD) / 2 = algebraMap (𝓞 D.host.E) D.host.E A.H.w0
  rw [← h', ← h]
  ring

example (ct : At S κ p) (z : (bdyTrue ct).BPt) (a : (bdyTrue ct).Yb z) (ha : a ≠ 0) :
    ∃ r ∈ maximalIdeal ((bdyTrue ct).Rl z), algebraMap _ (FractionRing ((bdyTrue ct).Rl z)) r =
      (bdyTrue ct).taub z a ((bdyTrue ct).phib z a) :=
  letI := A.H.starRing
  (ct.bdat z).tau_spec.pos_max ha

example (ct : At S κ p) (z : (bdyTrue ct).BPt) : ∃ s, (bdyTrue ct).fc z s 0 = 1 :=
  exists_coef_zero (ct.bdat z).U.U (ct.bdat z).adm 1

end GlobalTheory.LocM
