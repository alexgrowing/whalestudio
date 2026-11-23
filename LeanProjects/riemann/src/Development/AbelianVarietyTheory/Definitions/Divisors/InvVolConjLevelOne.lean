import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MiddleNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def finG (V : HSp D) : GfC V →* GL (Fin V.rank) (Lev.EAf D) := (Lev.finE V).comp (GfC V).subtype

def ratFin (V : HSp D) : Subgroup (GfC V) := ((GQ V).map (Lev.finE V)).comap (finG V)

abbrev FinCl (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Type :=
  DoubleCoset.Quotient (ratFin V : Set (GfC V)) (K.comap (finG V) : Set (GfC V))

def gamOrd (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : GfC V) : ℕ :=
  Nat.card {γ : ratFin V // finG V (x⁻¹ * γ * x) ∈ K}

def inBasis {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    GL (Fin n) (Lev.EAf D) →* GL (Fin n') (Kw w) :=
  ((reGL (finCongr h.symm)).toMonoidHom.comp (loc w)).comp (MulAut.conj β⁻¹).toMonoidHom

def prodLev {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (h : ∀ w, n' w = n)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) : Subgroup (GL (Fin n) (Lev.EAf D)) :=
  (⨅ w : P, (K w).comap (inBasis (h w) β w)) ⊓
    ⨅ (w' : Pl D.host.E) (_ : ∀ w ∈ P, w'.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)), (KO (Kw w') _).comap (inBasis rfl β w')

theorem exists_finEmb {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) :
    ∃ x : GfC B, EmbRel B A d.ι x.1 y.1 := by
  obtain ⟨g, hg, -⟩ := GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom y.1
  refine ⟨⟨g, Units.ext ?_⟩, hg⟩
  let π := (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hy : (matHom A y.1).1.map π = 1 := congrArg Units.val y.2
  set P := frameMat B A d.ι
  set C := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * B.gram
  have hG : C * P = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom
  set N : Matrix (Fin B.rank) (Fin B.rank) D.host.E := 1 - P * (A.gram⁻¹ * C) with hN
  have hC : C * N = 0 := by
    rw [hN, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hG, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul, sub_self]
  have h1 : (matHom B g).1 * N.map (incA D) = N.map (incA D) := by
    ext i j
    exact congr_fun (hg.2 (fun k => N k j) (by funext k; exact congr_fun (congr_fun hC k) j)) i
  refine GlobalTheory.AutFunCounterexample.split_gen (π.comp (incA D)) P (A.gram⁻¹ * C) ((matHom B g).1.map π) 1 ?_ ?_
  · have := congrArg (·.map π) h1
    simp only [Matrix.map_mul] at this
    exact this.trans (Matrix.one_mul _).symm
  · have := congrArg (·.map π) hg.1
    simp only [Matrix.map_mul, hy, Matrix.mul_one] at this
    exact this.trans (Matrix.one_mul _).symm

def finEmb {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) : GfC B := (exists_finEmb d y).choose

theorem finEmb_rel {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) :
    EmbRel B A d.ι (finEmb d y).1 y.1 := (exists_finEmb d y).choose_spec

def IsSumFrame {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D))
    (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w) : Prop :=
  (loc w β').val.submatrix id (frame d.rank) =
    fromCols ((frameMat B A d.ι).map (algebraMap D.host.E (Kw w)) * (loc w β).val)
      (d.a.map (algebraMap D.host.E (Kw w)) * diagonal u)

def frameSign (R : Type) [Ring R] (c : ℕ) (p : Fin c) : R := if c < 2 * p.1 + 1 then -1 else 1

example : frameSign ℤ 3 = ![1, 1, -1] ∧ frameSign ℤ 2 = ![1, -1] := by decide

section Wt

variable {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n)

open Classical in

def funOf : VV ℂ σ →ₗ[ℂ] VV ℂ fun τ => (σ τ).dual :=
  if h : ∃ φ : VV ℂ σ →ₗ[ℂ] VV ℂ fun τ => (σ τ).dual, ∀ F, IsFunForm σ F (φ F) then h.choose else 0

open Classical in

def covOf : (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] VV ℂ σ :=
  if h : ∃ φ : (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] VV ℂ σ, ∀ f, IsFunForm σ (φ f) f then h.choose else 0

def ReadOK : Prop := (∀ F, IsFunForm σ F (funOf σ F)) ∧ ∀ f, IsFunForm σ (covOf σ f) f

theorem readOK_of_equiv (φ : VV ℂ σ ≃ₗ[ℂ] VV ℂ fun τ => (σ τ).dual) (h : ∀ F, IsFunForm σ F (φ F)) : ReadOK σ := by
  have h1 : ∃ φ : VV ℂ σ →ₗ[ℂ] VV ℂ fun τ => (σ τ).dual, ∀ F, IsFunForm σ F (φ F) := ⟨φ, h⟩
  have h2 : ∃ φ : (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] VV ℂ σ, ∀ f, IsFunForm σ (φ f) f :=
    ⟨φ.symm, fun f => by simpa using h (φ.symm f)⟩
  rw [ReadOK, funOf, covOf, dif_pos h1, dif_pos h2]
  exact ⟨h1.choose_spec, h2.choose_spec⟩

def brPair {N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) : VV ℂ Λ →ₗ[ℂ] (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] ℂ :=
  (pairBK σ).compl₁₂ (Formalism.L2.Col.Br.brStd hN Λ σ) (covOf σ)

end Wt

noncomputable def chainTo {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) :
    ∀ n, V 0 →ₗ[ℂ] V n
  | 0 => LinearMap.id
  | n + 1 => k n ∘ₗ chainTo k n

example {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (v : V 0) :
    chainTo k 2 v = k 1 (k 0 v) := rfl

theorem one_le_sLen : 1 ≤ sLen D := (odd_sLen D).pos

def unitVol (w : Pl D.host.E) : Measure (Kw w) := GlobalTheory.SplitWeil.Model.exists_isUnitVol.choose

theorem isUnitVol_unitVol (w : Pl D.host.E) : IsUnitVol (unitVol w) := GlobalTheory.SplitWeil.Model.exists_isUnitVol.choose_spec

def bareGrid (w : Pl D.host.E) : Grid (Kw w) := ⟨D.R.m, D.R.r, D.R.t, sLen D, 1, 1, 1⟩

def genAt (w : Pl D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : (Kw w)ˣ :=
  unifAt w ^ FractionalIdeal.count D.host.E w 𝔞

def aaElt (w : Pl D.host.E) (j : ℕ) : GL (Fin ((bareGrid w).rank ((bareGrid w).m, j))) (Kw w) :=
  SplitFlip.diagGL fun a => if topRank (bareGrid w) j ≤ a then genAt w D.host.AA ^ (D.R.m - 1 - j - (a - topRank (bareGrid w) j)) *
    (genAt w D.host.AAbar ^ (a - topRank (bareGrid w) j + 1))⁻¹ else 1

def aaVac (w : Pl D.host.E) : (bareGrid w).Args → ℂ :=
  Set.indicator {z | ∀ b ∈ oppositePath (bareGrid w).m, ∀ i j, ((genAt w D.host.AA)⁻¹ : (Kw w)ˣ) * z b i j ∈ 𝒪[Kw w]} 1

variable {G : GridData L sc} (W : G.Weil)

def aaTerm (w : Pl D.host.E) : UnfTerm (bareGrid w) :=
  unfTerm (psiAt W w) (unitVol w) false (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)) (aaVac w)
    fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))

def aaScalar (w : Pl D.host.E) : ℂ :=
  (aaTerm W w).coef * (aaTerm W w).datum 0 0 * ((oppositePath D.R.m).map fun b =>
    apow (genAt w D.host.AAbar / genAt w D.host.AA) (((bareGrid w).rank b.src * (bareGrid w).rank b.tgt : ℕ) / 4)).prod

theorem invVol_conjLevel_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}
    (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m) : invVol (conjLevel hs (fun _ => KO k _) 1 hj) = 1 := by
  rw [← invVol_KO (k := k) (n := Fin (topRank Γ j)) (c := Γ.m - 1 - j), conjLevel]
  congr 1
  ext g
  rw [Pi.one_apply, map_one, Subgroup.map_equiv_eq_comap_symm', Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap,
    Subgroup.mem_comap, mem_KO_iff, mem_KO_iff, ← map_inv, ← map_inv]
  have h : topRank Γ j + (Γ.m - 1 - j) = Γ.rank (Γ.m, j) := by have := topRank_add hs j; omega
  exact and_congr ((frame h).symm.forall_congr fun _ => (frame h).symm.forall_congr fun _ => Iff.rfl)
    ((frame h).symm.forall_congr fun _ => (frame h).symm.forall_congr fun _ => Iff.rfl)

theorem unfTerm_coef_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (S : Γ.Args → ℂ) :
    (unfTerm ψ ν keep (Reps.through hs (fun _ => KO k _) fun _ => 1) S fun _ => DoubleCoset.mk _ _ 1).coef = 1 := by
  simp only [unfTerm, UnfModel.elt_one, invVol_conjLevel_one, Finset.prod_const_one]

theorem aaScalar_eq_one {w : Pl D.host.E} (h : FractionalIdeal.count D.host.E w D.host.AA = 0)
    (h' : FractionalIdeal.count D.host.E w D.host.AAbar = 0) (hψ : ∀ a ∈ 𝒪[Kw w], psiAt W w a = 1) : aaScalar W w = 1 := by
  have e1 : genAt w D.host.AA = 1 := by rw [genAt, h, zpow_zero]
  have e2 : genAt w D.host.AAbar = 1 := by rw [genAt, h', zpow_zero]
  have e3 : aaElt w = fun _ => 1 := funext fun j => Units.ext (by simp [aaElt, e1, e2, diagGL_val])
  have key : ∀ g : ∀ j, GL (Fin ((bareGrid w).rank ((bareGrid w).m, j))) (Kw w), (g = fun _ => 1) →
      let u := unfTerm (psiAt W w) (unitVol w) false (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) g) (aaVac w)
        fun i => DoubleCoset.mk _ _ (g (i + 1))
      u.datum 0 0 = 1 ∧ u.coef = 1 := by
    rintro _ rfl
    exact ⟨(UnfModel.vacuum_term (G := bareGrid w) one_le_sLen _ _ hψ (isUnitVol_unitVol w) (aaVac w)
      (fun z hz => Set.indicator_of_mem (by simpa [e1] using hz) _)
      (fun z hz => Set.indicator_of_notMem (by simpa [e1] using hz) _) _ _).1,
      unfTerm_coef_one (Γ := bareGrid w) one_le_sLen _ _ _ _⟩
  obtain ⟨e4, e5⟩ : (aaTerm W w).datum 0 0 = 1 ∧ (aaTerm W w).coef = 1 := key _ e3
  have e6 : ∀ z, apow (1 : (Kw w)ˣ) z = 1 := apow_of_valuation_eq_one (map_one _)
  simp only [aaScalar, e1, e2, e4, e5, div_one, e6, List.map_const', List.prod_replicate, one_pow, Rat.cast_one, mul_one]

variable (G) in

theorem topRank_eq (t : T) (w : Pl D.host.E) {j : ℕ} (h : j ≤ D.R.m) : topRank (locGrid G t w) j = (G.V (.top j)).rank :=
  (G.isV (X := .top j) h fun _ e => by cases e).rank.symm

structure GridChoice (U : Set T) where

  B : Frames G

  βp : ∀ j, GL (Fin (G.V (.top j)).rank) (Lev.EAf D)

  βp_is : ∀ j, j ≤ D.R.m → IsFrame (βp j) (G.Λ (.top j))

  row : ∀ t ∈ U, ∀ w ∈ locPl G t, ∀ j (hj : j < D.R.m), IsSumFrame (G.rowDec j hj) w (βp j) (B.β D.R.m j) fun p =>
    frameSign _ _ p * (unifAt w : Kw w) ^ if j = 0 then cosExp G w * (p.1 + 1) else 0

  last : ∀ t ∈ U, ∀ w ∈ locPl G t, IsSumFrame G.sp.topDec w (B.β D.R.m D.R.m) (βp D.R.m) 1

  N : Std G U

  Z : Normal W N

  PA : Finset (Pl D.host.E)

  PA_dvd : ∀ w ∈ PA, FractionalIdeal.count D.host.E w D.host.AA ≠ 0 ∨ FractionalIdeal.count D.host.E w D.host.AAbar ≠ 0

  PA_one : ∀ w, FractionalIdeal.count D.host.E w D.host.AA ≠ 0 →
    ∃! w', w' ∈ PA ∧ w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)

variable (G) in

abbrev PureDat (t : T) : Type := (∀ j : Fin D.R.m, FinDatum G t (.top t j)) × ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m)

variable (G) in

abbrev CosFam (t : T) : Type := ∀ w : locPl G t, Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w)

variable (G) in
open Classical in

def keepAt (w : Pl D.host.E) : Bool := decide (w ∉ G.pl.W0)

variable (G) in

def repsAt (t : T) (w : Pl D.host.E) : Reps (G := locGrid G t w) one_le_sLen (givenLevel G t w) :=
  Reps.through _ _ (stair _ (unifAt w) (cosExp G w))

namespace GridChoice

variable {W} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)

def sAA : ℂ := ∏ w ∈ S.PA, aaScalar W w

def term (β : CosFam G t) (w : locPl G t) : UnfTerm (locGrid G t w) :=
  unfTerm (psiAt W w.1) (unitVol w.1) (keepAt G w) (repsAt G t w) (Tflip W S.B t Φ w) (β w)

def supp : Set (CosFam G t) :=
  {β | ∀ w : locPl G t, β w ∈ unfSupport (psiAt W w.1) (unitVol w.1) (keepAt G w) (repsAt G t w) (Tflip W S.B t Φ w)}

def colAt (w : Pl D.host.E) (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) : ColArgs (locGrid G t w) := fun j =>
  if h : j < D.R.m then (((loc w (S.βp (j + 1)))⁻¹).val * Matrix.map (x ⟨j, h⟩) ((cpt w).comp (toEAf D)) *
    (loc w (S.βp j)).val).submatrix (Fin.cast (topRank_eq G t w h)) (Fin.cast (topRank_eq G t w h.le)) else 0

def rowAt (w : Pl D.host.E) (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    RowArgs (locGrid G t w) := fun i =>
  if h : i < D.R.m then (S.B.coord t w (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨h.le, le_rfl⟩ ⟨h, le_rfl⟩
    (Matrix.map (y ⟨i, h⟩) ((cpt w).comp (toEAf D))))ᵀ else 0

def IsExpansion (β : CosFam G t) (τ : PureDat G t →₀ ℂ) : Prop :=
  ∃ e : AE D, IsIdemSum e (locPl G t) ∧
    (∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1) ∧
    ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) →
      (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) =
        ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y)

def levTop (β : CosFam G t) : ∀ j, j < D.R.m → Subgroup (GL (Fin (G.V (.top j)).rank) (Lev.EAf D))
  | 0, _ => G.Kplus
  | j + 1, h => prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w h.le) fun w => (S.term t Φ β w).pr _ j.succ_pos h

def levRow (i : ℕ) (h : i ≤ D.R.m) : Subgroup (GL (Fin (G.V (.grid i D.R.m)).rank) (Lev.EAf D)) :=
  prodLev (S.B.β i D.R.m) (locPl G t) (fun w => rank_vertex G t w (X := (i, D.R.m)) ⟨h, le_rfl⟩)
    fun w => givenLevel G t w (i, D.R.m)

abbrev Classes (β : CosFam G t) : Type :=
  (∀ j : Fin D.R.m, FinCl _ (S.levTop t Φ β j j.2)) × ∀ i : Fin (D.R.m + 1), FinCl _ (S.levRow t i (Nat.le_of_lt_succ i.2))

variable {t Φ} {β : CosFam G t}

def ptRow (c : S.Classes t Φ β) (i : ℕ) : FinPt G (.grid i D.R.m) := if h : i < D.R.m + 1 then (c.2 ⟨i, h⟩).out else 1

def ptTop (c : S.Classes t Φ β) : ∀ j, FinPt G (.top j) :=
  Function.update (fun j => if h : j < D.R.m then (c.1 ⟨j, h⟩).out else 1) D.R.m (finEmb G.sp.topDec (S.ptRow c D.R.m))

def invGam (c : S.Classes t Φ β) : ℂ :=
  (∏ j : Fin D.R.m, (gamOrd _ (S.levTop t Φ β j j.2) (c.1 j).out : ℂ)⁻¹) *
    ∏ i : Fin (D.R.m + 1), (gamOrd _ (S.levRow t i (Nat.le_of_lt_succ i.2)) (c.2 i).out : ℂ)⁻¹

def colMap (d : PureDat G t) (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.kkMap 1 (d.1 ⟨j, h⟩) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMap (d : PureDat G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.kkMap 1 (d.2 ⟨i, h⟩) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairAt (τ : PureDat G t →₀ ℂ) (c : S.Classes t Φ β) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  τ.sum fun d a => a • (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (S.colMap d (S.ptTop c)) (S.rowMap d (S.ptRow c))

def classSum (Φ : G.Datum) (β : CosFam G t) (τ : PureDat G t →₀ ℂ) (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) : ℂ :=
  ∑ᶠ c : S.Classes t Φ β, S.invGam c * S.pairAt τ c (Ψ (S.ptTop c 0)) (F (S.ptRow c 0))

variable (t Φ)

def vCore (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) : ℂ :=
  ∑ᶠ β ∈ S.supp t Φ, (∏ w, ((S.term t Φ β w).coef : ℂ)) * S.classSum Φ β (Classical.epsilon (S.IsExpansion t Φ β)) Ψ F

structure SumOK : Prop where

  flat : ∀ w ∈ locPl G t, FlatIntegrable (G := locGrid G t w) one_le_sLen (psiAt W w) (unitVol w) (Tflip W S.B t Φ w)

  flatA : ∀ w ∈ S.PA, FlatIntegrable (G := bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (aaVac w)

  fin : (S.supp t Φ).Finite

  ex : ∀ β ∈ S.supp t Φ, ∃ τ, S.IsExpansion t Φ β τ

  vec : ∀ β τ, S.IsExpansion t Φ β τ → ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)

  indep : ∀ β τ τ', S.IsExpansion t Φ β τ → S.IsExpansion t Φ β τ' → ∀ c : S.Classes t Φ β, S.pairAt τ c = S.pairAt τ' c

  cls : ∀ β, Finite (S.Classes t Φ β)

  gam : ∀ β (c : S.Classes t Φ β), S.invGam c ≠ 0

  wts : ∀ i, i < D.R.m → WtOK G (.top t i) ∧ WtOK G (.chi i D.R.m)

  br : ∀ τ, Formalism.L2.Col.Br.Interlace G.sp.topDec.rank.symm (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) ∧
    Formalism.L2.Col.Br.SameShift (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ)

  read : ReadOK (listedWt G (.grid 0 D.R.m)) ∧ ReadOK (listedWt G (.grid D.R.m D.R.m))

theorem vCore_smul (a b : ℂ) (Ψ F) : S.vCore t Φ (a • Ψ) (b • F) = a * b * S.vCore t Φ Ψ F := by
  have h : ∀ (β : CosFam G t) τ, S.classSum Φ β τ (a • Ψ) (b • F) = a * b * S.classSum Φ β τ Ψ F := fun β τ => by
    simp only [classSum, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_finsum]
    exact finsum_congr fun c => by ring
  classical
  unfold vCore
  rw [mul_finsum]
  refine finsum_congr fun β => ?_
  by_cases hβ : β ∈ S.supp t Φ
  · rw [finsum_eq_if, finsum_eq_if, if_pos hβ, if_pos hβ, h]; ring
  · rw [finsum_eq_if, finsum_eq_if, if_neg hβ, if_neg hβ, mul_zero]

variable {S t Φ}

theorem SumOK.vCore_add (h : S.SumOK t Φ) (Ψ F F') : S.vCore t Φ Ψ (F + F') = S.vCore t Φ Ψ F + S.vCore t Φ Ψ F' := by
  rw [vCore, vCore, vCore, ← finsum_mem_add_distrib h.fin]
  refine finsum_mem_congr rfl fun β _ => ?_
  have := h.cls β
  rw [← mul_add, classSum, classSum, classSum, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  simp only [Pi.add_apply, map_add, mul_add]

theorem SumOK.vCore_eq (h : S.SumOK t Φ) (τ : CosFam G t → PureDat G t →₀ ℂ) (hτ : ∀ β ∈ S.supp t Φ, S.IsExpansion t Φ β (τ β))
    (Ψ F) : S.vCore t Φ Ψ F = ∑ β ∈ h.fin.toFinset, (∏ w, ((S.term t Φ β w).coef : ℂ)) * S.classSum Φ β (τ β) Ψ F := by
  rw [vCore, ← finsum_mem_eq_finite_toFinset_sum _ h.fin]
  refine finsum_mem_congr rfl fun β hβ => ?_
  simp only [classSum, h.indep β _ _ (Classical.epsilon_spec ⟨_, hτ β hβ⟩) (hτ β hβ)]

end GridChoice

variable (G) in

theorem wt_top_eq : wt G (.top 0) = LaP G := funext fun τ => by
  have h : (wt G (.top 0) τ).w = (LaP G τ).w := funext (wt_top_zero G (rank_Xp G) τ)
  generalize wt G (.top 0) τ = a at h
  generalize LaP G τ = b at h
  cases a; cases b; cases h; rfl

def psiC (Ψ : GLf G → WtSp G) (x : FinPt G (.top 0)) : VV ℂ (wt G (.top 0)) :=
  ⟨(GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (Ψ (finG (Xp G) x))).1, by rw [wt_top_eq]; exact Subtype.prop _⟩

variable (G) in

theorem rank_zero_m : D.sp.X'.rank = (G.V (.grid 0 D.R.m)).rank := (congrArg (·.sp.rank) (colY_m L)).symm

def toXf (y : FinPt G (.grid 0 D.R.m)) : Bridge.Gf D.sp.X' :=
  (finHom D.sp.X').rangeRestrict (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m L)) y.1)

end GlobalTheory.FunObj

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} (W : G.Weil)

structure SumChoice (U : Set T) extends GridChoice W U where

  co : R.cX.W →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m))

  co_is : ∃ gram c₀ c₁, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gram c₀ c₁ ∧
    ∀ v, (co (c₀ v)).1 = MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast (rank_zero_m G)) (Fin.cast (rank_zero_m G))))
      (MvPolynomial.map D.what₂.embLL v.1)

variable {U : Set T} (S : SumChoice W U)

variable {W} in

def SumChoice.formC (t : T) (u : (R.HX t).H) (y : FinPt G (.grid 0 D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) :=
  S.co ((R.HX t).e u (toXf y))

def vPair (t : T) (u : (R.HX t).H) (Ψ : GLf G → WtSp G) (Φ : G.Datum) : ℂ :=
  S.sAA * S.vCore t Φ (psiC Ψ) (S.formC t u)

def vSum (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (t : T) (F : A.fam.amb.FR t) (a : Fin n) : ℂ :=
  vPair W S t (R.jX t F) (psi rp e a) (datumOf e a)

variable (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (t : T)

theorem vPair_smul (c : ℂ) (u : (R.HX t).H) (Ψ Φ) : vPair W S t (c • u) Ψ Φ = c * vPair W S t u Ψ Φ := by
  have h : S.formC t (c • u) = c • S.formC t u := funext fun y => by simp [SumChoice.formC]
  have := S.vCore_smul t Φ 1 c (psiC Ψ) (S.formC t u)
  rw [one_smul] at this
  unfold vPair
  rw [h, this]; ring

theorem vPair_add {Φ : G.Datum} (h : S.SumOK t Φ) (u u' : (R.HX t).H) (Ψ) :
    vPair W S t (u + u') Ψ Φ = vPair W S t u Ψ Φ + vPair W S t u' Ψ Φ := by
  have e : S.formC t (u + u') = S.formC t u + S.formC t u' := funext fun y => by simp [SumChoice.formC]
  unfold vPair
  rw [e, h.vCore_add, mul_add]

theorem vSum_smul (c : D.what₂.LL) (F : A.fam.amb.FR t) (a : Fin n) :
    vSum W S rp e t (c • F) a = D.what₂.embLL c * vSum W S rp e t F a :=
  (congrArg (vPair W S t · _ _) ((R.jX t).map_smulₛₗ c F)).trans (vPair_smul W S t _ _ _ _)

theorem vSum_add {a : Fin n} (h : S.SumOK t (datumOf e a)) (F F' : A.fam.amb.FR t) :
    vSum W S rp e t (F + F') a = vSum W S rp e t F a + vSum W S rp e t F' a :=
  (congrArg (vPair W S t · _ _) ((R.jX t).map_add F F')).trans (vPair_add W S t h _ _ _)

end GlobalTheory.FunObj

end
