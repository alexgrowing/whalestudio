import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfGuard
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt
open scoped TensorProduct

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Base

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m)

def nrmR (σ : D.what₂.LL →+* ℂ) (f : Fin (R.nW i) → D.what₂.LL) : ℝ :=
  ‖(R.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) f‖

def latAll : Submodule (𝓞 D.what₂.LL) (Fin (R.nW i) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) ((R.FW i).MK : Set (Fin (R.nW i) → D.what₂.LL))

def spType : Submodule D.what₂.LL (Fin (R.nW i) → D.what₂.LL) := (R.FW i).typeP (F.lvl false).P (F.lvl false).ψ⁻¹

def latType : Submodule (𝓞 D.what₂.LL) (Fin (R.nW i) → D.what₂.LL) := (R.FW i).Mall (F.lvl false).P (F.lvl false).ψ⁻¹

def eGood : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL) :=
  (R.FW i).eOp fun g => (idemOf A.X).coeff g

def latGood : Submodule (𝓞 D.what₂.LL) (Fin (R.nW i) → D.what₂.LL) :=
  latType R F i ⊓ (LinearMap.range (eGood R i)).restrictScalars (𝓞 D.what₂.LL)

def latBad : Submodule (𝓞 D.what₂.LL) (Fin (R.nW i) → D.what₂.LL) :=
  latType R F i ⊓ (LinearMap.ker (eGood R i)).restrictScalars (𝓞 D.what₂.LL)

theorem latGood_le : latGood R F i ≤ latType R F i := inf_le_left

end Base

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)

def laOf : Weight Dw := weightOf Dw (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)

def shiftG (s : ℤ) : WTZ E := wtZ a n + wtOf Dw (s • hodgeWt Dw) 0

def anchor (kc : ℕ) (τ : Psi H) : ℤ := if h : kc - 1 < Dw.p + Dw.q then laOf Dw a n τ ⟨kc - 1, h⟩ else 0

def uWt (kc : ℕ) : Weight Dw := laOf Dw a n - GlobalTheory.FlatLine.parWt Dw (anchor Dw a n kc)

def uMinus (kc : ℕ) (c0 : ℤ) : Weight Dw := uWt Dw a n kc - c0 • hodgeWt Dw

def sizeK : ℝ := ∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ)|

theorem uWt_anchor (kc : ℕ) (τ : Psi H) (k : Fin (Dw.p + Dw.q)) (hk : (k : ℕ) + 1 = kc) : uWt Dw a n kc τ k = 0 := by
  subst hk
  simp [uWt, anchor, GlobalTheory.FlatLine.parWt]

theorem uWt_add_anchor (kc : ℕ) : uWt Dw a n kc + GlobalTheory.FlatLine.parWt Dw (anchor Dw a n kc) = laOf Dw a n :=
  sub_add_cancel _ _

theorem sizeK_nonneg : 0 ≤ sizeK Dw a n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

end Weights

def cZeroN (D : D7) (j : ℕ) : ℕ :=
  8 * ((max (D.R.r + (D.R.f * (D.R.sigW j).1 * (D.R.sigW j).2 + 1).choose 2 + 2) (8 * D.R.f * D.R.r + 4) + 7) / 8)

def cZero (D : D7) (j : ℕ) : ℤ := (cZeroN D j : ℤ)

theorem cZeroN_isLeast (D : D7) (j : ℕ) :
    IsLeast {s : ℕ | 8 ∣ s ∧ D.R.r + (D.R.f * (D.R.sigW j).1 * (D.R.sigW j).2 + 1).choose 2 + 2 ≤ s ∧
      8 * D.R.f * D.R.r + 4 ≤ s} (cZeroN D j) := by
  unfold cZeroN
  refine ⟨⟨⟨_, rfl⟩, by omega, by omega⟩, fun s hs => ?_⟩
  obtain ⟨⟨y, rfl⟩, h1, h2⟩ := hs
  omega

theorem cZeroN_le (D : D7) (j : ℕ) : cZeroN D j ≤ 22 * D.R.f ^ 2 * D.R.r ^ 4 := by
  have hn : 0 < D.R.ord := D.R.ord_pos
  have hk := D.R.f_le_k
  have ht := D.R.rank_add_five_le
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; omega
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hpq : (D.R.sigW j).1 * (D.R.sigW j).2 ≤ D.R.r ^ 2 := by
    by_cases hj : j ≤ D.R.m
    · have h1 : (D.R.sigW j).1 ≤ D.R.r := by unfold Ranks.sigW Ranks.r; simp only; omega
      have h2 : (D.R.sigW j).2 ≤ D.R.r := by unfold Ranks.sigW Ranks.r; simp only; omega
      rw [sq]; exact Nat.mul_le_mul h1 h2
    · have h2 : (D.R.sigW j).2 = 0 := by unfold Ranks.sigW; simp only; omega
      simp [h2]
  unfold cZeroN
  rw [mul_assoc D.R.f]
  generalize (D.R.sigW j).1 * (D.R.sigW j).2 = s at hpq
  generalize D.R.f = f at *
  generalize D.R.r = r at *
  have hN : f * s ≤ f * r ^ 2 := Nat.mul_le_mul_left _ hpq
  have hc : (f * s + 1).choose 2 ≤ (f * s) ^ 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    generalize f * s = N
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp
    · exact Nat.div_le_of_le_mul (by nlinarith)
  have hc2 : (f * s) ^ 2 ≤ f ^ 2 * r ^ 4 := by
    calc (f * s) ^ 2 ≤ (f * r ^ 2) ^ 2 := Nat.pow_le_pow_left hN 2
      _ = f ^ 2 * r ^ 4 := by ring
  have h3 : f * r ≤ f ^ 2 * r ^ 4 :=
    Nat.mul_le_mul (Nat.le_self_pow (by norm_num) f) (Nat.le_self_pow (by norm_num) r)
  have h4 : r ≤ f * r := Nat.le_mul_of_pos_left r hf
  rw [mul_assoc 8 f r, mul_assoc 22]
  omega

theorem cZero_spec (D : D7) (j : ℕ) :
    8 ∣ cZero D j ∧ 0 ≤ cZero D j ∧ cZero D j ≤ 22 * (D.R.f : ℤ) ^ 2 * (D.R.r : ℤ) ^ 4 := by
  refine ⟨?_, Int.natCast_nonneg _, ?_⟩
  · exact Int.natCast_dvd_natCast.2 (cZeroN_isLeast D j).1.1
  · unfold cZero; exact_mod_cast cZeroN_le D j

def fieldSz (K : Type) [Field K] [NumberField K] : ℝ :=
  Real.log (Module.finrank ℚ K : ℝ) + Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ)

theorem log_finrank_le_fieldSz (K : Type) [Field K] [NumberField K] :
    Real.log (Module.finrank ℚ K : ℝ) ≤ fieldSz K := by
  have h : 0 ≤ Real.log |(discr K : ℝ)| := by
    rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  unfold fieldSz
  have : 0 ≤ Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by positivity
  linarith

theorem log_rd_le_fieldSz (K : Type) [Field K] [NumberField K] :
    Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) ≤ fieldSz K := by
  unfold fieldSz
  linarith [Real.log_natCast_nonneg (Module.finrank ℚ K)]

example : fieldSz ℚ = 0 := by simp [fieldSz, NumberField.discr_rat]

def expL (L : ℝ) : ℕ := ⌊3 * L / Real.log 3⌋₊

theorem le_expL {L : ℝ} {e : ℕ} (h : e * Real.log 3 ≤ 3 * L) : e ≤ expL L :=
  Nat.le_floor ((le_div_iff₀ (Real.log_pos (by norm_num))).2 h)

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Deep (T : Core D) (j : ℕ) : Type 1 where

  c' : Coeff T.Q.l
  hle : T.Q.c.F ≤ c'.F

  d : DeltaDat (T.Q.Xo j) c' 0

  U : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r

  dict : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r

  Kf : Subgroup (GA D (D.sp.W j))

namespace Deep

variable {T : Core D} {j : ℕ} (Y : Deep T j)

def Pin (σ : Y.d.c₂.F →+* ℂ) (ι : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop :=
  ∃ (hr : (D.sp.W j).rank = D.R.r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
    (F : FamilyUnif Y.d.Xo₂ (σ.comp (IntermediateField.inclusion Y.d.c₂.le).toRingHom) (fun i => relab Y.d.c₂ σ (e i).1))
    (ik : (Y.U σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((Y.U σ).X k).Λ)
    (th : ∀ k, ((Y.U σ).X k).Ψ → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat (Y.U σ) (D.sp.W j) hr (Y.dict σ) ι e F ik φ th x₀

structure Good (e : ℕ) (o : ℝ) : Prop where
  pd : Y.d.pd = 15 ^ e
  lev : Y.d.IsLev ∧ Y.d.l₂.A = 1
  unf : ∀ σ, GoodEmb Y.d.c₂ σ → IsUnf (Y.U σ)
  unTest : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ k x,
    FromTest (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) ((Y.U σ).un k x)
  chiTriv : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((Y.U σ).X k).Γ,
    ((Y.U σ).X k).χ (laU (Y.U σ) a n k) γ = 1
  dictU : ∀ σ, GoodEmb Y.d.c₂ σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) (Y.dict σ) Y.Kf th hr
  levelK : IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1 * Y.d.pd) Y.Kf
  xiAbs : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((Y.U σ).X k).ξ0‖ = xiR D
  geo : FnAlgClosed Y.d.Xo₂ Y.d.c₂
  normal : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ T.Q.c.F, s a = a) → ∀ a ∈ Y.c'.F, s a ∈ Y.c'.F
  size : fieldSz Y.d.c₂.F ≤ o

  unit : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ i, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ i‖ = 1

  modelW : ∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)

  adPin : ∃ ι, LatEmb (D.sp.W j) ι ∧ LatIsom (D.sp.W j) (T.Q.Dw j).EF ι ∧
    ∀ σ, GoodEmb Y.d.c₂ σ → ∃ x₀, (∀ k, IsOrthogonalFrame ((Y.U σ).X k) x₀) ∧ Y.Pin σ ι x₀

def resEmb (σ : Y.d.c₂.F →+* ℂ) : T.Q.c.F →+* ℂ :=
  σ.comp ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (IntermediateField.inclusion Y.hle).toRingHom)

theorem good_resEmb {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) : GoodEmb T.Q.c (Y.resEmb σ) := hσ

def Match {T : CoreJ D} (Y : Deep T.toCore j) : Prop :=
  ∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r,
    Y.Pin σ (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j (Y.resEmb σ))

abbrev GoodL (L o : ℝ) : Prop := Y.Good (expL L) o

variable {Y} in

theorem Good.deg {e : ℕ} {o : ℝ} (h : Y.Good e o) : Real.log (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ o :=
  (log_finrank_le_fieldSz _).trans h.size

variable {Y} in

theorem Good.rd {e : ℕ} {o : ℝ} (h : Y.Good e o) :
    Real.log |(discr Y.d.c₂.F : ℝ)| ≤ o * Module.finrank ℚ Y.d.c₂.F := by
  have hp : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
  exact (div_le_iff₀ hp).1 ((log_rd_le_fieldSz _).trans h.size)

variable {Y} in

theorem Good.mono {e : ℕ} {o o' : ℝ} (h : Y.Good e o) (ho : o ≤ o') : Y.Good e o' :=
  { h with size := h.size.trans ho }

def Pull (f : T.R j) (g : Rul Y.d.Xo₂ Y.d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra T.Q.c.F k] [Algebra Y.c'.F k] [Algebra Y.d.c₂.F k],
    AlgOver T.Q.c Y.c' Y.hle k → (∀ a : Y.c'.F, algebraMap Y.d.c₂.F k (Y.d.eF a) = algebraMap Y.c'.F k a) →
    ∀ (y₂ : FrPt Y.d.Xo₂ Y.d.c₂ k) (y' : FrPt (T.Q.Xo j) Y.c' k) (y : FrPt (T.Q.Xo j) T.Q.c k),
      FrOver Y.d y₂ y' → y.x = y'.x → y.u = y'.u → HEq y.s y'.s →
        evR Y.d.Xo₂ Y.d.c₂ g y₂ = evR (T.Q.Xo j) T.Q.c f y

abbrev V (G : WTZ D.host.E) : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂) := cuspW Y.d.Xo₂ Y.d.c₂ Y.U G

abbrev nrm (G : WTZ D.host.E) : (Y.d.c₂.F →+* ℂ) → Y.V G → ℝ := normW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G

abbrev GoodAt (G : WTZ D.host.E) : Prop := GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G

abbrev mu (G : WTZ D.host.E) : ℝ := slopeW_sq Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G

abbrev rk (G : WTZ D.host.E) : ℕ := rankW Y.U G

def latOver (G : WTZ D.host.E) (B : Set (T.R j)) : Submodule (𝓞 Y.d.c₂.F) (Y.V G) :=
  latW Y.U G ⊓ ((Submodule.span Y.d.c₂.F {g | ∃ f ∈ B, Y.Pull f g}).comap (Y.V G).subtype).restrictScalars (𝓞 Y.d.c₂.F)

abbrev ht (la : Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) : ℝ :=
  compHeight Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)

abbrev dg (la : Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) : ℝ := compDeg Y.U Z (wtOf (T.Q.Dw j) la 0)

abbrev degC (la : Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) : ℝ :=
  degOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)

abbrev rkC (la : Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) : ℝ := rankOn Y.U Z (wtOf (T.Q.Dw j) la 0)

end Deep

section Core

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (F : Face D A) (i : Fin D.R.m)

def typeK : Set (T.R ((i : ℕ) + 1)) :=
  {f | ∃ h : f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
    ((fw.e i ⟨f, h⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) ∈ spType R F i}

abbrev VK (_fw : FWTie T R κ v₀) (i : Fin D.R.m) : Submodule T.Q.c.F (T.R ((i : ℕ) + 1)) :=
  cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n)

abbrev nrmK : (T.Q.c.F →+* ℂ) → VK fw i → ℝ :=
  normW (T.U ((i : ℕ) + 1)) (xiR D) (T.V ((i : ℕ) + 1)) (T.dict ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n)

def latTypeK : Submodule (𝓞 T.Q.c.F) (VK fw i) :=
  latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) ⊓
    ((Submodule.span T.Q.c.F (typeK fw F i)).comap (VK fw i).subtype).restrictScalars (𝓞 T.Q.c.F)

end Core

def IsQuot {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (kc T : ℕ) (c0 : ℤ) (u u1 : Weight Dw) : Prop :=
  GlobalTheory.MeanTop.Wts.IsDiv (ι := Psi H) (N := Dw.p + Dw.q)
    { kc := kc, p := Dw.p, T := T, Dd := dimFlag Dw, c0 := c0, h0 := 0, S := 0, eta := 0, b := 0, w := 0, u := u, u1 := u1 }

namespace Inhab

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.JoinChr Formalism.L2.Host
open scoped Pointwise

section Half

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)

theorem bar_root : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h3 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h2] at h3
    have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have h5 : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
    have h6 := congrArg Complex.re h4
    simp [sq, h5] at h6
    have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  · exact h

theorem exists_half (s : ℤ) (hs : (15 : ℤ) ∣ s ^ 2 + H.d) (e : ℕ) :
    ∃ I : Ideal (𝓞 E), (∃ G : Set (𝓞 E), I = Ideal.span G ∧ G ⊆ Algebra.adjoin ℤ {H.w0}) ∧
      I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {((15 ^ e : ℕ) : 𝓞 E)} ∧ I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
  have hd : Nat.Coprime 15 H.d := by
    refine (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd H.d_prime).2 fun h => ?_))
    have h1 := Nat.le_of_dvd (by norm_num) h
    have h2 := H.d_mod
    have h3 : H.d = 7 := by omega
    rw [h3] at h; norm_num at h
  have hc : IsCoprime (15 : ℤ) (2 * s) := by
    refine IsCoprime.mul_right (by norm_num [Int.isCoprime_iff_gcd_eq_one]) ?_
    obtain ⟨t, ht⟩ := hs
    have hd' : IsCoprime (15 : ℤ) (H.d : ℤ) := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hd
    obtain ⟨a, b, hab⟩ := hd'
    exact ⟨a + b * t, -(b * s), by linear_combination hab - b * ht⟩
  obtain ⟨a, b, hab⟩ := hc
  have hab' : (a : 𝓞 E) * 15 + (b : 𝓞 E) * (2 * s) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
  obtain ⟨t, ht⟩ := hs
  have ht' : (s : 𝓞 E) ^ 2 + H.d = 15 * t := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) ht
  let J : Ideal (𝓞 E) := Ideal.span {15, (s : 𝓞 E) + H.rt}
  have hJ : J.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {15, (s : 𝓞 E) - H.rt} := by
    rw [Ideal.map_span, Set.image_pair]
    simp [bar_root, sub_eq_add_neg, map_ofNat]
  have m1 : (15 : 𝓞 E) ∈ J := Ideal.subset_span (by simp)
  have m2 : (s : 𝓞 E) + H.rt ∈ J := Ideal.subset_span (by simp)
  have m3 : (15 : 𝓞 E) ∈ J.map (H.bar : 𝓞 E →+* 𝓞 E) := hJ ▸ Ideal.subset_span (by simp)
  have m4 : (s : 𝓞 E) - H.rt ∈ J.map (H.bar : 𝓞 E →+* 𝓞 E) := hJ ▸ Ideal.subset_span (by simp)
  have hsup : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hab', show (2 * s : 𝓞 E) = (s + H.rt) + (s - H.rt) by ring]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left m1))
      (Ideal.mul_mem_left _ _ (add_mem (Ideal.mem_sup_left m2) (Ideal.mem_sup_right m4)))
  have hmul : J * J.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(15 : 𝓞 E)} := by
    apply le_antisymm
    · rw [hJ, Ideal.span_pair_mul_span_pair, Ideal.span_le]
      have hq : ((s : 𝓞 E) + H.rt) * (s - H.rt) = 15 * t := by linear_combination ht' - H.rt_sq
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
      · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
      · exact Ideal.mem_span_singleton.2 (dvd_mul_left _ _)
      · exact Ideal.mem_span_singleton.2 (hq ▸ dvd_mul_right _ _)
    · rw [Ideal.mul_eq_inf_of_coprime hsup, Ideal.span_singleton_le_iff_mem]
      exact ⟨m1, m3⟩
  refine ⟨J ^ e, ⟨({15, (s : 𝓞 E) + H.rt} : Set (𝓞 E)) ^ e, ?_, ?_⟩, ?_, ?_⟩
  · exact Submodule.span_pow _ e
  · have h0 : ({15, (s : 𝓞 E) + H.rt} : Set (𝓞 E)) ⊆ Algebra.adjoin ℤ {H.w0} := by
      have hw : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.subset_adjoin rfl
      rintro x (rfl | rfl)
      · exact ofNat_mem _ 15
      · rw [show (s : 𝓞 E) + H.rt = s + (H.w0 + H.w0 - 1) by linear_combination -H.two_weight_eq_one_add_root]
        exact add_mem (intCast_mem _ s) (sub_mem (add_mem hw hw) (one_mem _))
    induction e with
    | zero => intro x hx; rw [pow_zero, Set.mem_one] at hx; exact hx ▸ one_mem _
    | succ n ih =>
      rw [pow_succ]
      rintro x ⟨y, hy, z, hz, rfl⟩
      exact mul_mem (ih hy) (h0 hz)
  · rw [Ideal.map_pow, ← mul_pow, hmul, Ideal.span_singleton_pow]; push_cast; rfl
  · rw [Ideal.map_pow, ← Ideal.isCoprime_iff_sup_eq]
    exact (Ideal.isCoprime_iff_sup_eq.2 hsup).pow

end Half

theorem normalClosure_stable (K : IntermediateField ℚ ℂ) (s : ℂ ≃+* ℂ) (a : ℂ) (ha : a ∈ IntermediateField.normalClosure ℚ K ℂ) :
    s a ∈ IntermediateField.normalClosure ℚ K ℂ := by
  have : IntermediateField.normalClosure ℚ K ℂ ≤ (IntermediateField.normalClosure ℚ K ℂ).comap s.toRingHom.toRatAlgHom := by
    refine iSup_le fun f => ?_
    rintro x ⟨y, rfl⟩
    exact AlgHom.fieldRange_le_normalClosure (s.toRingHom.toRatAlgHom.comp f) ⟨y, rfl⟩
  exact this ha

theorem exists_root (h : 5 ≤ D.host.splitBound) : ∃ s : ℤ, (15 : ℤ) ∣ s ^ 2 + D.host.d := by
  have h3 := D.host.split_small 3 (by norm_num) (by norm_num) (by omega)
  have h5 := D.host.split_small 5 (by norm_num) (by norm_num) h
  rw [jacobiSym.mod_left] at h3 h5
  generalize (D.host.d : ℤ) = d at h3 h5 ⊢
  have a3 : -d % 3 = 1 := by
    have : -d % 3 = 0 ∨ -d % 3 = 1 ∨ -d % 3 = 2 := by omega
    push_cast at h3
    rcases this with h | h | h
    · rw [h] at h3; norm_num at h3
    · exact h
    · rw [h] at h3; norm_num at h3
  have a5 : -d % 5 = 1 ∨ -d % 5 = 4 := by
    have : -d % 5 = 0 ∨ -d % 5 = 1 ∨ -d % 5 = 2 ∨ -d % 5 = 3 ∨ -d % 5 = 4 := by omega
    push_cast at h5
    rcases this with h | h | h | h | h
    · rw [h] at h5; norm_num at h5
    · exact Or.inl h
    · rw [h] at h5; norm_num at h5
    · rw [h] at h5; norm_num at h5
    · exact Or.inr h
  rcases a5 with h | h
  · exact ⟨1, by omega⟩
  · exact ⟨2, by omega⟩

theorem norm_neg_cmConstant_eq_at_all_embeddings (τ : D.host.E →+* ℂ) : ‖τ (-D.host.xi0)‖ = xiR D := by
  have hs : ∀ τ : D.host.E →+* ℂ, ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    intro τ
    have h0 : (τ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (τ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg, Complex.norm_natCast]
  unfold xiR Formalism.BasicNotions.Host.xi0
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, hs]

theorem rank_pos (T : Core D) (hQ : T.Q.Pins) (j : ℕ) (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  obtain ⟨-, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hQ j hj
  have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
  rw [hr]; unfold Ranks.r; omega

set_option maxHeartbeats 1000000 in

theorem exists_good_pin (T : Core D) (hQ : T.Q.Pins) (j : ℕ) (hj : InR D j) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F)
    (d : DeltaDat (T.Q.Xo j) c' 0) (e : ℕ) (a1 : d.pd = 15 ^ e) (a2 : d.IsLev) (a3 : d.l₂.A = 1)
    (a4 : FnAlgClosed d.Xo₂ d.c₂) (a5 : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ T.Q.c.F, s a = a) → ∀ a ∈ c'.F, s a ∈ c'.F)
    (ι : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (hι : GlobalTheory.Member.IotaOK (T.Q.Dw j) (D.sp.W j) ι)
    (x : (d.c₂.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (hx : ∀ σ, GoodEmb d.c₂ σ → ∃ C : GlobalTheory.Member.Ctx d.Xo₂ d.c₂ σ (D.sp.W j) D.R.r, C.OK ∧ C.ι = ι ∧ C.x₀ = x σ) :
    ∃ U dict Kf, (⟨c', hle, d, U, dict, Kf⟩ : Deep T j).Good e (fieldSz d.c₂.F) ∧
      ∀ σ, GoodEmb d.c₂ σ → (⟨c', hle, d, U, dict, Kf⟩ : Deep T j).Pin σ ι (x σ) := by
  have hpos := rank_pos T hQ j hj
  have hM : d.l₂.M = D.host.g 0 * D.host.g 1 * d.pd := by rw [a2.2.1, hQ.2.1.1]
  obtain ⟨Kf, hKf⟩ := (GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D (D.sp.W j) d.l₂.M).1
  have hpk : ∀ σ, GoodEmb d.c₂ σ → ∃ (U : Unf d.Xo₂ d.c₂ σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r),
      ∃ hr mu, GlobalTheory.Member.PkgLaws (D.sp.W j) hr ι Kf 1 U dict mu (x σ) := fun σ hσ => by
    obtain ⟨C, hC, hCι, hCx⟩ := hx σ hσ
    obtain ⟨un, dict, mu, -, -, hP⟩ := GlobalTheory.Member.exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1
      ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
    exact ⟨C.unf un, dict, C.hr, mu, hCx ▸ hCι ▸ hP⟩
  have hall : ∀ σ, ∃ (U : Unf d.Xo₂ d.c₂ σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r), GoodEmb d.c₂ σ →
      ∃ hr mu, GlobalTheory.Member.PkgLaws (D.sp.W j) hr ι Kf 1 U dict mu (x σ) := fun σ => by
    by_cases hσ : GoodEmb d.c₂ σ
    · obtain ⟨U, dict, h⟩ := hpk σ hσ
      exact ⟨U, dict, fun _ => h⟩
    · obtain ⟨U, dict, -⟩ := hpk d.c₂.F.val.toRingHom rfl
      obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ _ _
        d.Xo₂ d.c₂ hpos σ
      exact ⟨{ Comp := Unit, X := fun _ => U.X (dict 1).1, un := fun _ _ => y }, fun _ => ⟨(), fun _ => 0⟩,
        fun h => absurd h hσ⟩
  choose U dict hP using hall
  have hpin : ∀ σ, GoodEmb d.c₂ σ → (⟨c', hle, d, U, dict, Kf⟩ : Deep T j).Pin σ ι (x σ) := fun σ hσ => by
    obtain ⟨hr, mu, h⟩ := hP σ hσ
    obtain ⟨g, e', F, ik, φ, th, b1, -, b3⟩ := h.dictLaws
    exact ⟨hr, g, e', F, ik, φ, th, b1, b3⟩
  refine ⟨U, dict, Kf, ⟨a1, ⟨a2, a3⟩, fun σ hσ => ?_, fun σ hσ => ?_, fun σ hσ _ _ _ k γ _ => ?_,
    fun σ hσ => ?_, hM ▸ hKf, fun σ hσ k τ => ?_, a4, a5, le_rfl, fun σ hσ => ?_, fun σ hσ => ?_,
    ι, hι.emb, ⟨1, fun x y => by simpa using hι.isom x y⟩, fun σ hσ => ?_⟩, hpin⟩
  all_goals obtain ⟨hr, mu, h⟩ := hP σ hσ
  · exact h.unf
  · exact h.unTest
  · exact h.chi1 k _ γ
  · obtain ⟨g, e', F, ik, φ, th, b1, b2, -⟩ := h.dictLaws
    exact ⟨th, hr, b1, b2⟩
  · exact (congrArg (fun z => ‖τ z‖) (h.modelW k).2).trans (norm_neg_cmConstant_eq_at_all_embeddings τ)
  · exact h.muUnit.2.2.2
  · exact ⟨hr, h.modelW⟩
  · exact ⟨x σ, h.familyUniformisationBasePointOrthogonal, hpin σ hσ⟩

theorem exists_good_of_cover (T : Core D) (hQ : T.Q.Pins) (j : ℕ) (hj : InR D j) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F)
    (d : DeltaDat (T.Q.Xo j) c' 0) (e : ℕ) (a1 : d.pd = 15 ^ e) (a2 : d.IsLev) (a3 : d.l₂.A = 1)
    (a4 : FnAlgClosed d.Xo₂ d.c₂) (a5 : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ T.Q.c.F, s a = a) → ∀ a ∈ c'.F, s a ∈ c'.F) :
    ∃ U dict Kf, (⟨c', hle, d, U, dict, Kf⟩ : Deep T j).Good e (fieldSz d.c₂.F) := by
  classical
  obtain ⟨⟨ι, hι⟩, -, -, -⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hQ j hj
  have h : ∀ σ, ∃ x, GoodEmb d.c₂ σ →
      ∃ C : GlobalTheory.Member.Ctx d.Xo₂ d.c₂ σ (D.sp.W j) D.R.r, C.OK ∧ C.ι = ι ∧ C.x₀ = x := fun σ => by
    by_cases hσ : GoodEmb d.c₂ σ
    · obtain ⟨C, hC, hCι⟩ := (GlobalTheory.Member.exists_ctx D _ _ _ d.Xo₂ d.c₂ σ (D.sp.W j) D.R.r (D.sp.W_rank j hj.1 hj.2) ι hι
        (rank_pos T hQ j hj) a3 hσ).1
      exact ⟨C.x₀, fun _ => ⟨C, hC, hCι, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hσ⟩
  choose x hx using h
  obtain ⟨U, dict, Kf, h, -⟩ := exists_good_pin T hQ j hj c' hle d e a1 a2 a3 a4 a5 ι hι x hx
  exact ⟨U, dict, Kf, h⟩

theorem exists_match_of_cover (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F)
    (d : DeltaDat (T.Q.Xo j) c' 0) (e : ℕ) (a1 : d.pd = 15 ^ e) (a2 : d.IsLev) (a3 : d.l₂.A = 1)
    (a4 : FnAlgClosed d.Xo₂ d.c₂) (a5 : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ T.Q.c.F, s a = a) → ∀ a ∈ c'.F, s a ∈ c'.F) :
    ∃ U dict Kf, (⟨c', hle, d, U, dict, Kf⟩ : Deep T.toCore j).Good e (fieldSz d.c₂.F) ∧
      Deep.Match (⟨c', hle, d, U, dict, Kf⟩ : Deep T.toCore j) := by
  have hW : (D.sp.W j).rank = D.R.r := D.sp.W_rank j hj.1 hj.2
  let res : (d.c₂.F →+* ℂ) → (T.Q.c.F →+* ℂ) := fun σ =>
    σ.comp ((d.eF : c'.F →+* d.c₂.F).comp (IntermediateField.inclusion hle).toRingHom)
  have hres : ∀ σ, GoodEmb d.c₂ σ → GoodEmb T.Q.c (res σ) := fun _ h => h
  have hι := (GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj _ T.good_σ₀ _ (hT.spaceW j hj _ T.good_σ₀) hW).1
  obtain ⟨U, dict, Kf, h, hp⟩ := exists_good_pin T.toCore hT.pins j hj c' hle d e a1 a2 a3 a4 a5 _ hι
    (fun σ => T.x₀ j (res σ)) fun σ hσ =>
      (GlobalTheory.Member.exists_ctx D _ _ _ d.Xo₂ d.c₂ σ (D.sp.W j) D.R.r hW _ hι (rank_pos T.toCore hT.pins j hj) a3 hσ).2.2 _
        (GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj _ (hres σ hσ) _ (hT.spaceW j hj _ (hres σ hσ)) hW).2
  exact ⟨U, dict, Kf, h, fun σ hσ => ⟨hW, hp σ hσ⟩⟩

set_option maxHeartbeats 1000000 in

theorem exists_cover (T : Core D) (hQ : T.Q.Pins) (j : ℕ) (hj : InR D j) (s : ℤ) (hs : (15 : ℤ) ∣ s ^ 2 + D.host.d)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) (e : ℕ) :
    ∃ (c' : Coeff T.Q.l) (_ : T.Q.c.F ≤ c'.F) (d : DeltaDat (T.Q.Xo j) c' 0), d.pd = 15 ^ e ∧ d.IsLev ∧ d.l₂.A = 1 ∧
      FnAlgClosed d.Xo₂ d.c₂ ∧ ∀ s : ℂ ≃+* ℂ, (∀ a ∈ T.Q.c.F, s a = a) → ∀ a ∈ c'.F, s a ∈ c'.F := by
  have hpos := rank_pos T hQ j hj
  obtain ⟨I, hK, hp, hI⟩ := exists_half T.Q.H s (by rw [hQ.1.1]; exact hs) e
  obtain ⟨l₂, l1, l2, l3, l4, l5, l6⟩ := GlobalTheory.CoverHalf.exists_coverLevel T.Q.l hQ.2.1.2 (15 ^ e) I (Odd.pow (by decide))
    (by rw [hQ.2.1.1]; exact h15.pow_left e) hK hp hI
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ (T.Q.Dw j) l₂ hpos
  obtain ⟨c₀, -⟩ := GlobalTheory.TupleCover.exists_coeff_ge l₂ ⊥
  obtain ⟨c₁, -, hc₁⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo₂ c₀ hpos).2
  haveI := c₁.fin
  haveI := T.Q.c.fin
  let K : IntermediateField ℚ ℂ := T.Q.c.F ⊔ c₁.F
  let N : IntermediateField ℚ ℂ := IntermediateField.normalClosure ℚ K ℂ
  have hKN : K ≤ N := IntermediateField.le_normalClosure K
  have hN : FiniteDimensional ℚ N := inferInstance
  have h1 : T.Q.c.F ≤ N := le_sup_left.trans hKN
  have h2 : c₁.F ≤ N := le_sup_right.trans hKN
  let c' : Coeff T.Q.l := ⟨N, hN, fun τ a => h1 (T.Q.c.conj τ a), h1 T.Q.c.zeta_mem, T.Q.c.le.trans h1⟩
  let c₂ : Coeff l₂ := ⟨N, hN, fun τ a => h2 (c₁.conj τ a), h2 c₁.zeta_mem, c₁.le.trans h2⟩
  have hd : ∃ d : DeltaDat (T.Q.Xo j) c' 0, d.pd = 15 ^ e ∧ d.IsLev ∧ d.l₂.A = 1 ∧ FnAlgClosed d.Xo₂ d.c₂ := by
    obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, mm, nab, cδ, φ₀⟩, a1, a2, a3, e₁, e₂, -, a4, a5⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo j) c' hpos 0 (15 ^ e) I l₂ Xo₂ c₂ rfl l1 l2 l3 l4 l5
    refine ⟨_, a1, a4, a3 ▸ l6, ?_⟩
    dsimp only at a3 e₁ e₂ ⊢
    subst a3
    obtain rfl := eq_of_heq e₁
    obtain rfl := eq_of_heq e₂
    exact hc₁ c₂ h2
  obtain ⟨d, a1, a2, a3, a4⟩ := hd
  exact ⟨c', h1, d, a1, a2, a3, a4, fun s _ a ha => normalClosure_stable K s a ha⟩

theorem exists_good (T : Core D) (hQ : T.Q.Pins) (j : ℕ) (hj : InR D j) (s : ℤ) (hs : (15 : ℤ) ∣ s ^ 2 + D.host.d)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) (e : ℕ) :
    ∃ (Y : Deep T j) (o : ℝ), Y.Good e o ∧ Y.d.l₂.M = D.host.g 0 * D.host.g 1 * 15 ^ e ∧ CompNe Y.d.Xo₂ Y.d.c₂ := by
  obtain ⟨c', h1, d, a1, a2, a3, a4, a5⟩ := exists_cover T hQ j hj s hs h15 e
  obtain ⟨U, dict, Kf, h⟩ := exists_good_of_cover T hQ j hj c' h1 d e a1 a2 a3 a4 a5
  exact ⟨_, _, h, by rw [← a1]; show d.l₂.M = _; rw [a2.2.1, hQ.2.1.1],
    (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ d.Xo₂ d.c₂ (rank_pos T hQ j hj)).1⟩

theorem exists_good_match (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (s : ℤ) (hs : (15 : ℤ) ∣ s ^ 2 + D.host.d)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) (e : ℕ) :
    ∃ (Y : Deep T.toCore j) (o : ℝ), Y.Good e o ∧ Y.Match := by
  obtain ⟨c', h1, d, a1, a2, a3, a4, a5⟩ := exists_cover T.toCore hT.pins j hj s hs h15 e
  obtain ⟨U, dict, Kf, h⟩ := exists_match_of_cover T hT j hj c' h1 d e a1 a2 a3 a4 a5
  exact ⟨_, _, h⟩

theorem pull_one {T : Core D} {j : ℕ} (Y : Deep T j) : Y.Pull 1 1 := by
  intro k _ _ _ _ _ _ _ y₂ y' y _ _ _ _
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  exact (evalAt_one _ _ y₂ (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ _ _ k y₂)).trans
    (evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ _ _ k y)).symm

theorem not_pull_one_zero {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o)
    (hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) : ¬ Y.Pull 1 0 := by
  intro hp
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨y'⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ _ _
    (T.Q.Xo j) Y.c' hpos Y.c'.F.val.toRingHom
  letI : Algebra Y.c'.F ℂ := Y.c'.F.val.toRingHom.toAlgebra
  letI : Algebra T.Q.c.F ℂ := T.Q.c.F.val.toRingHom.toAlgebra
  letI : Algebra Y.d.c₂.F ℂ := Y.d.c₂.F.val.toRingHom.toAlgebra
  change FrPt (T.Q.Xo j) Y.c' ℂ at y'
  have ho : AlgOver T.Q.c Y.c' Y.hle ℂ := fun _ => rfl
  obtain ⟨y₂, hy⟩ := h.lev.1.2.2.2.2.2.2.1 ℂ (fun _ => rfl) y'
  have := hp ℂ ho (fun _ => rfl) y₂ y' (y'.res Y.hle ho) hy rfl rfl HEq.rfl
  exact zero_ne_one ((evalAt_zero _ _ y₂).symm.trans (this.trans
    (evalAt_one _ _ _ (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ _ _ _ _))))

end Inhab

end GlobalTheory.CovTop

end
