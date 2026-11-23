import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ValNeBot

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ref

open NumberField IsDedekindDomain IsLocalRing Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def cjE (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) : E := IsCMField.complexConj E x

abbrev SymB {E : Type} [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) :=
  Formalism.MainNotions.ModuliIntegralCharts.SymB cj Y

abbrev phiC {E : Type} [Field E] [NumberField E] (cj : E → E) {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    (b : SymB cj Y) : ℝ :=
  Formalism.MainNotions.ModuliIntegralCharts.phiC cj b

def IsPhiAt (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (t : ℝ) : Prop :=
  ∃ (e : ℕ) (_ : OverLa la T.V io e) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G)
    (ϖ : T.V) (Q : P.D.toPre.X → ℤ) (β : SymB (cjE E) P.D.toPre.X),
    P.TorsionIso ∧ Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧
    (∀ a b, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a b = QForm.bOf P.D.toPre Q a b) ∧
    (∀ a, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧
    (∀ a, 0 ≤ (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a) ∧
    phiC (cjE E) β = e * t

abbrev PtU (la : HeightOneSpectrum (𝓞 c.F)) : Type :=
  PtV Xo c (fun _ _ y => y.IsAlg) ℝ (IsPhiAt Xo c la) la

def pjSys : PtSys c.F (Rul Xo c) where
  Pt := PtU Xo c
  val y f := vAtV y f
  val_zero y := vAtV_zero y
  val_ne_bot y f := vAtV_ne_bot y f
  val_add y f g := vAtV_add y f g
  val_smul y a f ha := vAtV_smul y a f ha
  val_mul y f g := vAtV_mul y f g

def phU (la : HeightOneSpectrum (𝓞 c.F)) (y : (pjSys Xo c).Pt la) : ℝ := imgV (show PtU Xo c la from y)

variable {Xo c} in

def IsBC {T T' : CDVR} {io : c.F →+* T.Fr} (φ : T.Fr →+* T'.Fr) (y : IntFr Xo c T io)
    (z : IntFr Xo c T' (φ.comp io)) : Prop :=
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  FrMap ({ φ with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 z.1

def IsFinExt {T T' : CDVR} (φV : T.V →+* T'.V) (φ : T.Fr →+* T'.Fr) (r : ℕ) : Prop :=
  Function.Injective φV ∧ IsLocalHom φV ∧ φV.Finite ∧
    φ.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp φV ∧
    0 < r ∧ ∀ x, vV T'.V (φ x) = (r : ℤ) * vV T.V x

def UnifAll : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr Xo c T io, y.IsAlg →
      ∃ (T' : CDVR) (φV : T.V →+* T'.V) (φ : T.Fr →+* T'.Fr) (r : ℕ) (z : IntFr Xo c T' (φ.comp io)) (t : ℝ),
        IsFinExt φV φ r ∧ IsBC φ y z ∧ z.IsAlg ∧ IsPhiAt Xo c la T' (φ.comp io) z t

def levA (R : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (x : Dw.La) : ptO Xo x0 ⟶ Xo.univ.t.G :=
  toUnit _ ≫ Xo.univ.etaA ((l.A / R ^ 2) • x)

def IsThConst (nab : NabV Xo c) (R : ℕ) {n : ℕ} (x : Fin n → Dw.La) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R),
    ∃ F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((R : ℤ) ^ 2) (ptO Xo y.x)),
      (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP R (fun t' => t' = levA Xo R y.x (x b)) y.s
        (levA Xo R y.x (x b) ^ R) (F b)) ∧
      f p y = ∏ b, nab y ((R : ℤ) ^ 2) (F b) 0

variable [StarRing (𝓞 E)]

def JetUp (nab : NabV Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cc : ℝ) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (y : IntFr Xo c T io), y.IsAlg →
    ∀ t : ℝ, IsPhiAt Xo c la T io y t →
      ∃ f ∈ thGen Xo c nab a n, nval T.V e (evI y f) ≤ nuLoc y e k a n + ((cc * t : ℝ) : EReal)

def DepthGe (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℝ) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (y : IntFr Xo c T io), y.IsAlg →
    (m : EReal) ≤ nuLoc y e k a n

def GermLow (nab : NabV Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ m : ℝ, DepthGe Xo c la k a n m → ∀ f ∈ thGen Xo c nab a n,
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (y : IntFr Xo c T io), y.IsAlg →
      (m : EReal) ≤ nval T.V e (evI y f)

omit [StarRing (𝓞 E)] in

def PageHyp (Dw : Datum H) (l : Level H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : Fin 2 → ℕ) (cc : ℝ) : Prop :=
  (∀ i, (g i).Prime) ∧ g 0 ≠ g 1 ∧ l.M = g 0 * g 1 ∧
  (∀ i, Nat.card ((Ideal.span {(g i : ℤ)}).primesOver (𝓞 E)) = Module.finrank ℚ E) ∧
  (∃ π : Fin 2 → 𝓞 E, (∀ i, π i * H.bar (π i) = (g i : 𝓞 E)) ∧ l.Mb = Ideal.span {H.bar (π 0) * H.bar (π 1)}) ∧
  (∀ τ (i j : ℕ), i ≤ j → j < Dw.mult τ → a (τ, j) ≤ a (τ, i)) ∧
  Module.finrank ℚ E / 2 * (Dw.p * (Dw.p + 1) + Dw.q * (Dw.q + 1)) ≤ n ∧
  ∀ i, 2 * (DF Dw a : ℝ) * Real.sqrt ((Module.finrank ℚ E * min Dw.p Dw.q : ℕ) : ℝ) < g i ∧
    4 * DF Dw a + 4 ≤ g i ∧
    |(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E) / (2 * Module.finrank ℚ E) *
      (((Module.finrank ℚ E * min Dw.p Dw.q : ℕ) : ℝ) ^ 4 * n + 2 * ((Module.finrank ℚ E * min Dw.p Dw.q : ℕ) : ℝ) ^ 3) *
      (DF Dw a : ℝ) ^ 2 / g i ≤ cc

def JetsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ nab : NabV Xo c, IsNab Xo c nab → ThValTot Xo c nab →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : Fin 2 → ℕ) (cc : ℝ), PageHyp Dw l a n g cc →
    ∀ la : HeightOneSpectrum (𝓞 c.F), ((l.M : ℕ) : 𝓞 c.F) ∉ la.asIdeal → JetUp Xo c nab la l.M a n cc

def LevelSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ nab : NabV Xo c, IsNab Xo c nab → ThValTot Xo c nab →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : Fin 2 → ℕ) (cc : ℝ), PageHyp Dw l a n g cc →
    ∀ (i : Fin 2) (la : HeightOneSpectrum (𝓞 c.F)), ((g i : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
      ∃ m : ℤ, (∀ f ∈ thGen Xo c nab a n, ∀ y : PtU Xo c la, (((m : ℝ)) : EReal) ≤ vAtV y f) ∧
        ∀ y : PtU Xo c la, ∃ f ∈ thGen Xo c nab a n,
          vAtV y f ≤ ((m + ramOverZ la * (DF Dw a : ℝ) / ((g i : ℝ) - 1) + cc * phU Xo c la y : ℝ) : EReal)

section Basic

omit [StarRing (𝓞 E)]

theorem cjE_coe (H : Host E) (a : 𝓞 E) : cjE E (a : E) = (H.bar a : E) := (H.bar_eq a).symm

theorem isFinExt_id (T : CDVR) : IsFinExt (RingHom.id T.V) (RingHom.id T.Fr) 1 :=
  ⟨Function.injective_id, inferInstance, RingHom.Finite.id _, rfl, one_pos, fun x => by simp⟩

variable {c} in

theorem IsFinExt.overLa {T T' : CDVR} {φV : T.V →+* T'.V} {φ : T.Fr →+* T'.Fr} {r : ℕ} (h : IsFinExt φV φ r)
    {la : HeightOneSpectrum (𝓞 c.F)} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) :
    OverLa la T'.V (φ.comp io) (r * e) :=
  ho.bc φ h.2.2.2.2.1 h.2.2.2.2.2

theorem IsFinExt.nval_eq {T T' : CDVR} {φV : T.V →+* T'.V} {φ : T.Fr →+* T'.Fr} {r : ℕ} (h : IsFinExt φV φ r)
    (e : ℕ) (x : T.Fr) : nval T'.V (r * e) (φ x) = nval T.V e x :=
  nval_bc φ h.2.2.2.2.1 h.2.2.2.2.2 e x

variable {c} in

theorem overLa_unique {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e e' : ℕ}
    (h : OverLa la T.V io e) (h' : OverLa la T.V io e') : e = e' := by
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer c.F
  have h1 : vLa la π = 1 := by simp [vLa, hπ]
  have := (h.2 π).symm.trans (h'.2 π)
  rw [h1] at this
  omega

theorem pjSys_val_mk (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (hy : y.IsAlg) (t : ℝ) (ht : IsPhiAt Xo c la T io y t)
    (f : Rul Xo c) :
    (pjSys Xo c).val (show PtU Xo c la from PtV.mk la ho y hy t ht) f = nval T.V e (evI y f) := rfl

theorem phU_mk (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (hy : y.IsAlg) (t : ℝ) (ht : IsPhiAt Xo c la T io y t) :
    phU Xo c la (show PtU Xo c la from PtV.mk la ho y hy t ht) = t := rfl

theorem phiC_nonneg {E : Type} [Field E] [NumberField E] (cj : E → E) {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    (b : SymB cj Y) (hb : ∀ a, 0 ≤ (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) : 0 ≤ phiC cj b := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨l, -, h, rfl⟩
  by_cases h0 : b = 0
  · simp [h0]
  · exact (h b hb h0).le

variable {Xo c} in

theorem IsPhiAt.nonneg {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {t : ℝ}
    (h : IsPhiAt Xo c la T io y t) : 0 ≤ t := by
  obtain ⟨e, ho, I, P, ϖ, Q, β, -, -, -, -, -, hpos, ht⟩ := h
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have := phiC_nonneg _ β hpos
  rw [ht] at this
  exact nonneg_of_mul_nonneg_right this he

example (cj : E → E) (b : SymB cj PUnit.{1}) : phiC cj b = 0 := by
  have hb : b = 0 := by
    apply Subtype.ext; ext a b'
    rw [show a = 0 from rfl, map_zero]; simp
  refine le_antisymm (Real.sInf_nonpos ?_) (phiC_nonneg _ _ fun a => by simp [hb])
  rintro _ ⟨l, -, -, rfl⟩
  simp [hb]

example : (2 * (1 : ℝ) * Real.sqrt ((4 : ℕ) : ℝ) < (11 : ℕ) ∧ 4 * 1 + 4 ≤ 11) ∧ ¬ 4 * 1 + 4 ≤ 7 := by
  have : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [this]; norm_num

end Basic

end GlobalTheory.CompanionTheory.Ar.Ref
