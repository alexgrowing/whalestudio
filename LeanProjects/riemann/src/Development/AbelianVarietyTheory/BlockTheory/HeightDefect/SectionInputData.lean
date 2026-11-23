import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def valZ (h : GenFrEx Xo c) (G : WTZ E) (f : Rul Xo c) : ∀ Z : Comp Xo c, AC Z :=
  fun Z => AddMonoidAlgebra.single G (evC h Z f)

theorem valZ_wtZ (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    valZ h (wtZ a n) f = valC h a n f := rfl

theorem valZ_mem (h : GenFrEx Xo c) (G : WTZ E) (f : Rul Xo c) (Z : Comp Xo c) : valZ h G f Z ∈ AG Z G :=
  mem_AG.2 ⟨_, rfl⟩

def IsSecZ (G : WTZ E) (f : Rul Xo c) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
    ∀ (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R), FrBor t y y' →
      f p y' = ((∏ i, t i ^ exZ Dw G i : (p.R)ˣ) : p.R) * f p y

theorem isSecZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    IsSecZ (wtZ a n) f ↔ f ∈ sec Xo c a n := by
  have key : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      ((∏ i, t i ^ exZ Dw (wtZ a n) i : Sˣ) : S) = wchar (ex Dw a n) t := by
    intro S _ t
    rw [wchar, Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, wtZ, ex]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [← key]; exact h2 p t y y' hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [key]; exact h2 p t y y' hb⟩

theorem isSecZ_one : IsSecZ (0 : WTZ E) (1 : Rul Xo c) := by
  refine ⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩
  have : ∀ i, exZ Dw (0 : WTZ E) i = 0 := fun i => by cases i <;> rfl
  simp [this]

theorem IsSecZ.mul {G G' : WTZ E} {f g : Rul Xo c} (hf : IsSecZ G f) (hg : IsSecZ G' g) :
    IsSecZ (G + G') (f * g) := by
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · show f q z * g q z = φ (f p y * g p y)
    rw [hf.1 p q φ y z h, hg.1 p q φ y z h, map_mul]
  · show f p y' * g p y' = _ * (f p y * g p y)
    rw [hf.2 p t y y' h, hg.2 p t y y' h]
    simp only [exZ_add, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
    ring

theorem IsSecZ.pow {G : WTZ E} {f : Rul Xo c} (hf : IsSecZ G f) (k : ℕ) : IsSecZ (k • G) (f ^ k) := by
  induction k with
  | zero => simpa using isSecZ_one
  | succ k ih => rw [succ_nsmul, pow_succ]; exact ih.mul hf

variable (Xo c) in

structure Input : Type where

  D : ℕ
  N : ℕ
  T : ℕ
  i : ℕ
  g0 : ℕ

  cc : ℝ

  wL : WTZ E
  wF : WTZ E
  wde : WTZ E

  Mr : Set (Rul Xo c)

  w : Fin (N + 1) → Rul Xo c
  jc : Comp Xo c → Fin (N + 1)

  np : ℕ
  thp : Fin np → Rul Xo c

  n0 : ℕ
  th0 : Fin n0 → Rul Xo c

  nk : ℕ
  thk : Fin nk → Rul Xo c

  et : Rul Xo c
  ta1 : Rul Xo c
  ta2 : Rul Xo c

  nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ

  ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ

  wsize : WTZ E → ℝ
  DF : ℝ
  cNu : ℝ
  cQuot : ℝ
  cLow : ℝ
  cLow' : ℝ
  cDim : ℝ
  cGen : ℝ
  crystallineInclusion : ℝ
  cEta : ℝ
  cBase : ℝ
  cBase' : ℝ
  cRank : ℝ
  cField : ℝ
  f : ℝ
  r : ℝ

namespace Input

variable (I : Input Xo c)

def wG₁ : WTZ E := I.wL - I.wde

def wG₂ : WTZ E := (I.D + 4 : ℕ) • I.wL - I.wF

def wF₀ : WTZ E := I.wF + I.D • I.wL

def wka : WTZ E := I.wF + I.T • I.wL

def wet : WTZ E := (I.i * I.g0) • I.wde

structure Weighted : Prop where
  Mr : ∀ f ∈ I.Mr, IsSecZ I.wka f
  w : ∀ j, IsSecZ I.wL (I.w j)
  thp : ∀ k, IsSecZ I.wF (I.thp k)
  th0 : ∀ k, IsSecZ I.wF₀ (I.th0 k)
  thk : ∀ k, IsSecZ I.wka (I.thk k)
  et : IsSecZ I.wet I.et
  ta1 : IsSecZ ((2 : ℕ) • I.wG₁) I.ta1
  ta2 : IsSecZ I.wG₂ I.ta2

def BaseNe (h : GenFrEx Xo c) : Prop := ∀ Z : Comp Xo c, evC h Z (I.w (I.jc Z)) ≠ 0

def toData [Fintype (Comp Xo c)] (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) :
    ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z) where
  D := I.D
  N := I.N
  T := I.T
  i := I.i
  g0 := I.g0
  cc := I.cc
  wL := I.wL
  wF := I.wF
  wde := I.wde
  ord := fun Z v G x => ordC (δ Z v) v G x
  nrm := fun Z G x P => nrmC fn (yP Z) G x P
  M := @Submodule.span (𝓞 c.F) _ _ _ (_) (valZ h I.wka '' I.Mr)
  WW := @Submodule.span (𝓞 c.F) _ _ _ (_) (Set.range fun j => valZ h I.wL (I.w j))
  Thp := @Submodule.span (𝓞 c.F) _ _ _ (_) (Set.range fun k => valZ h I.wF (I.thp k))
  Th0 := @Submodule.span (𝓞 c.F) _ _ _ (_) (Set.range fun k => valZ h I.wF₀ (I.th0 k))
  Thk := @Submodule.span (𝓞 c.F) _ _ _ (_) (Set.range fun k => valZ h I.wka (I.thk k))
  w := fun j => valZ h I.wL (I.w j)
  jc := I.jc
  np := I.np
  thp := fun k => valZ h I.wF (I.thp k)
  n0 := I.n0
  th0 := fun k => valZ h I.wF₀ (I.th0 k)
  nk := I.nk
  thk := fun k => valZ h I.wka (I.thk k)
  et := valZ h I.wet I.et
  ta1 := valZ h ((2 : ℕ) • I.wG₁) I.ta1
  ta2 := valZ h I.wG₂ I.ta2
  nu := I.nu
  ip := I.ip
  wsize := I.wsize
  DF := I.DF
  PN := I.cNu
  PQ := I.cQuot
  tableDegreeThreeBase := I.cLow
  PP0' := I.cLow'
  Pd := I.cDim
  Gc := I.cGen
  PI4 := I.crystallineInclusion
  Pet := I.cEta
  tableLineDegreeFive := I.cBase
  tableLineDegreeTwo := I.cBase'
  Prw := I.cRank
  PO := I.cField
  f := I.f
  r := I.r

end Input

variable (Xo c)

def HasComp : Prop := Nonempty (Comp Xo c)

def FieldsFG : Prop := ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (Om Z)).FG

def FieldsTrdeg (D : ℕ) : Prop := ∀ Z : Comp Xo c, Algebra.trdeg c.F (Om Z) = D

def ConstClosed : Prop :=
  ∀ (Z : Comp Xo c) (a : Om Z), IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range

variable {Xo c}

def NeOnComps (h : GenFrEx Xo c) (f : Rul Xo c) : Prop := ∀ Z : Comp Xo c, evC h Z f ≠ 0

def CBaseAll (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ Z, CBase h Z (yP Z)

theorem neOnComps_iff (h : GenFrEx Xo c) (G : WTZ E) (f : Rul Xo c) :
    NeOnComps h f ↔ ∀ Z, valZ h G f Z ≠ 0 := by
  simp [NeOnComps, valZ]

theorem neOnComps_one (h : GenFrEx Xo c) (ht : GenFromTest Xo c h) : NeOnComps h (1 : Rul Xo c) := by
  intro Z
  have : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (ht Z)
  rw [this]; exact one_ne_zero

section
variable [Fintype (Comp Xo c)] (I : Input Xo c) (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem toData_ka : (I.toData h δ fn yP).ka = I.wka := rfl
theorem toData_F₀ : (I.toData h δ fn yP).F0 = I.wF₀ := rfl
theorem toData_G₂ : (I.toData h δ fn yP).G2 = I.wG₂ := rfl

theorem toData_et_mem (Z : Comp Xo c) :
    (I.toData h δ fn yP).et Z ∈ AG Z ((I.toData h δ fn yP).n1 • (I.toData h δ fn yP).wde) := valZ_mem h _ _ Z

theorem toData_torsionSection_mem (Z : Comp Xo c) :
    (I.toData h δ fn yP).ta1 Z ∈ AG Z ((2 : ℕ) • (I.toData h δ fn yP).G1) := valZ_mem h _ _ Z

theorem toData_M_mem (x : ∀ Z : Comp Xo c, AC Z) (hx : x ∈ (I.toData h δ fn yP).M) (Z : Comp Xo c) :
    x Z ∈ AG Z (I.toData h δ fn yP).ka := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨f, -, rfl⟩ := hx; exact valZ_mem h _ f Z
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    have : (a • x) Z = algebraMap c.F (Om Z) (a : c.F) • x Z := by
      rw [algebraMap_smul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

end

def ofSection (D T : ℕ) (L : WTZ E) (s : Rul Xo c) : Input Xo c where
  D := D
  N := 0
  T := T
  i := 1
  g0 := 1
  cc := 0
  wL := L
  wF := (D + 4 : ℕ) • L
  wde := L
  Mr := {s ^ (D + 4) * s ^ T}
  w := fun _ => s
  jc := fun _ => 0
  np := 1
  thp := fun _ => s ^ (D + 4)
  n0 := 1
  th0 := fun _ => s ^ (D + 4) * s ^ D
  nk := 1
  thk := fun _ => s ^ (D + 4) * s ^ T
  et := s
  ta1 := 1
  ta2 := 1
  nu := 0
  ip := 0
  wsize := fun G => (G.2 : ℝ) + 1
  DF := 0
  cNu := 1
  cQuot := 1
  cLow := 1
  cLow' := 1
  cDim := 1
  cGen := 1
  crystallineInclusion := 1
  cEta := 1
  cBase := 1
  cBase' := 1
  cRank := 1
  cField := 1
  f := 1
  r := 1

theorem ofSection_weighted (D T : ℕ) {L : WTZ E} {s : Rul Xo c} (hs : IsSecZ L s) :
    (ofSection D T L s).Weighted where
  Mr := by rintro f rfl; exact (hs.pow _).mul (hs.pow _)
  w := fun _ => hs
  thp := fun _ => hs.pow _
  th0 := fun _ => (hs.pow _).mul (hs.pow _)
  thk := fun _ => (hs.pow _).mul (hs.pow _)
  et := by simpa [Input.wet, ofSection] using hs
  ta1 := by simpa [Input.wG₁, ofSection] using (isSecZ_one (Xo := Xo) (c := c))
  ta2 := by
    have : (ofSection D T L s).wG₂ = 0 := sub_self _
    rw [this]; exact isSecZ_one

end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
