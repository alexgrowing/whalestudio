import Mathlib
import Formalism.HermitianCurvature.StatementC
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Corank
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section

namespace Formalism.L2.SG.DataInst

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt
open Classical ValuativeRel

variable {D : Formalism.BasicNotions.D7}

def signAux {K : Type} [Ring K] (r : ℕ) : ℕ → TB.Pt K → TB.Pt K
  | _, [] => []
  | b, (s, t) :: rest => (s, (-1) ^ (r + 1 - (b + s - 1)) * t) :: signAux r (b + s) rest

def signPt {K : Type} [Ring K] (r : ℕ) (x : TB.Pt K) : TB.Pt K := signAux r 1 x

theorem sign_list_fst {K : Type} [Ring K] (r : ℕ) : ∀ (b : ℕ) (x : TB.Pt K),
    (signAux r b x).map Prod.fst = x.map Prod.fst
  | _, [] => rfl
  | b, (s, t) :: rest => by simp [signAux, sign_list_fst r (b + s) rest]

theorem sign_list_mem_nonzero {K : Type} [Field K] (r : ℕ) : ∀ (b : ℕ) (x : TB.Pt K),
    (∀ c ∈ signAux r b x, 1 ≤ c.1 ∧ c.2 ≠ 0) ↔ (∀ c ∈ x, 1 ≤ c.1 ∧ c.2 ≠ 0)
  | _, [] => by simp [signAux]
  | b, (s, t) :: rest => by
    simp only [signAux, List.mem_cons, forall_eq_or_imp, sign_list_mem_nonzero r (b + s) rest]
    have : (-1 : K) ^ (r + 1 - (b + s - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    simp [this]

theorem isPtL_signPt {K : Type} [Field K] (r : ℕ) (x : TB.Pt K) (i : ℕ) :
    Formalism.L2.S.IsPtL (signPt r x) i ↔ Formalism.L2.S.IsPtL x i := by
  simp only [Formalism.L2.S.IsPtL, signPt, sign_list_fst, sign_list_mem_nonzero]

def ptOfList (i : ℕ) (x : TB.Pt D.host.E) : Option (Point D.host.E i) :=
  if h : Formalism.L2.S.IsPtL (signPt D.R.rS x) i then
    some ((Formalism.L2.S.ptEquiv D.host.E i).symm ⟨signPt D.R.rS x, h⟩) else none

def gNorm (D : Formalism.BasicNotions.D7) : ℝ := (((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (2 * D.R.f))⁻¹

def nrm (ν : ℕ) (t : D.host.E) : ℝ :=
  gNorm D * (D.host.rdE ^ (2 * D.R.f * ν))⁻¹ * ((|Algebra.norm ℚ t| : ℚ) : ℝ)

def blockWeightPhi (i : ℕ) : ℕ → TB.Pt D.host.E → ℝ
  | _, [] => 1
  | b, (s, t) :: rest =>
    nrm (Formalism.MainNotions.S.LocalSplitGroups.nu D.R.rS b (b + s - 1)) t ^ (s * (i - (b + s - 1)) + s * (s - 1) / 2) * blockWeightPhi i (b + s) rest

def phi (i : ℕ) (x : TB.Pt D.host.E) : ℝ := blockWeightPhi i 1 x

theorem nrm_pos {t : D.host.E} (ht : t ≠ 0) (ν : ℕ) : 0 < nrm ν t := by
  have hg : (0 : ℝ) < ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    simp only [Formalism.MainNotions.S.Lat.gS]
    exact_mod_cast Nat.mul_pos h0 h1
  have hr : 0 < D.host.rdE := by
    simp only [Formalism.BasicNotions.Host.rdE]
    exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
  have hn : (0 : ℝ) < ((|Algebra.norm ℚ t| : ℚ) : ℝ) :=
    Rat.cast_pos.mpr (abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr ht))
  simp only [nrm, gNorm]
  exact mul_pos (mul_pos (inv_pos.mpr (pow_pos hg _)) (inv_pos.mpr (pow_pos hr _))) hn

theorem block_weight_phi_pos (i : ℕ) : ∀ (b : ℕ) (x : TB.Pt D.host.E), (∀ c ∈ x, c.2 ≠ 0) → 0 < blockWeightPhi i b x
  | b, [] => by intro _; simp [blockWeightPhi]
  | b, (s, t) :: rest => by
    intro h
    simp only [blockWeightPhi]
    exact mul_pos (pow_pos (nrm_pos (h (s, t) (by simp)) _) _)
      (block_weight_phi_pos i (b + s) rest (fun c hc => h c (by simp [hc])))

theorem phi_pos {i : ℕ} {x : TB.Pt D.host.E} (hx : Formalism.L2.S.IsPtL x i) : 0 < phi i x := block_weight_phi_pos i 1 x (fun c hc => (hx.2 c hc).2)

def KrOf (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (T T' : ℕ) (i : ℕ) (x y : TB.Pt D.host.E) : ℂ :=
  if i = 0 then (if x = [] ∧ y = [] then 1 else 0)
  else if D.R.rS + 1 < i then 0
  else match ptOfList i x, ptOfList i y with
    | some a, some b => Kglob δ M T T' i a b / ((phi i x : ℂ) * (phi i y : ℂ))
    | _, _ => 0

theorem KrOf_zero (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (T T' : ℕ) : KrOf δ M T T' 0 [] [] = 1 := by
  simp [KrOf]

private theorem isPtL_of_ptOfList_ne_none {i : ℕ} {z : TB.Pt D.host.E} (hz : ptOfList i z ≠ none) :
    Formalism.L2.S.IsPtL z i := by
  unfold ptOfList at hz
  split_ifs at hz with hh
  · exact (isPtL_signPt _ _ _).mp hh
  · exact absurd rfl hz

theorem KrOf_of_not (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (T T' : ℕ) {i : ℕ} (hi : i ≠ 0) {x y : TB.Pt D.host.E}
    (h : ¬ (Formalism.L2.S.IsPtL x i ∧ Formalism.L2.S.IsPtL y i)) : KrOf δ M T T' i x y = 0 := by
  simp only [KrOf, if_neg hi]
  split_ifs
  · rfl
  · cases hx : ptOfList i x with
    | none => rfl
    | some a =>
      cases hy : ptOfList i y with
      | none => rfl
      | some b =>
        exact absurd ⟨isPtL_of_ptOfList_ne_none (by simp [hx]), isPtL_of_ptOfList_ne_none (by simp [hy])⟩ h

def ThOf : ℕ → ℕ → D.host.E → TB.Pt D.host.E → TB.Pt D.host.E → ℂ := fun _ _ _ _ _ => 0

def eOf : ℕ → ℝ := fun _ => 0

variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def dOf (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (u u' : D.what₂.Word) : TB.Data D.host.E S.W :=
  S.mkData (KrOf δ M (D.mem u).A.T (D.mem u').A.T) (KrOf_zero δ M _ _) ThOf eOf

def Compat (S : C.HidaSetting D.host.E Wp Wq) (u u' : D.what₂.Word) : Prop :=
  S.G.r = D.R.rS ∧ S.G.k = D.R.k ∧ S.G.g1 = D.host.g 0 ∧ S.G.g2 = D.host.g 1 ∧
  S.T = ((D.mem u).A.T : ℝ) ∧ S.T' = ((D.mem u').A.T : ℝ) ∧ S.f = D.R.f

theorem dOf_Kr (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (u u' : D.what₂.Word) :
    (dOf S δ M u u').Kr = KrOf δ M (D.mem u).A.T (D.mem u').A.T := rfl

theorem dOf_e (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (u u' : D.what₂.Word) (i : ℕ) :
    (dOf S δ M u u').e i = 0 := rfl

theorem dOf_r (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (u u' : D.what₂.Word) :
    (dOf S δ M u u').r = S.G.r := rfl

theorem inst_dOf (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (u u' : D.what₂.Word) :
    J.Inst (dOf S δ M u u') S.pl S.G S.CA S.de S.de' S.T S.T' S.l := by
  exact ⟨rfl, rfl, fun _ _ => rfl, S.hv, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem unram_host (D : Formalism.BasicNotions.D7) : S6.Unram D.host.E := MainNotions.LocalModelPeriodLattices.unramE D

def KrFinite (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ u u' : D.what₂.Word,
    (∀ (n : ℕ) (w w' : Point D.host.E n), n ≤ D.R.rS →
      (Function.mulSupport fun p => locK M δ (D.mem u).A.T (D.mem u').A.T p n w w').Finite) ∧
    (∀ w w' : Point D.host.E (D.R.rS + 1),
      (Function.mulSupport fun p => KtopP M δ (D.mem u).A.T (D.mem u').A.T p w w').Finite)

def LocalModelAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ u u' : D.what₂.Word, Compat S u u' → PB.LocalModel (dOf S δ M u u')

open Formalism.L2.SG.CntLocal Formalism.MainNotions.S.Lat

section Dens

variable {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def densSet (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp])
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Set ℝ :=
  {d | ∃ Z : MatZ D, (∃ Λ ∈ what₂, (EZ (Tn u') F0 Λ Z).Nonempty) ∧
    d = ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p}

def supDens (L : LocSp D M) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp])
    (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : ℝ :=
  sSup (densSet L δ ϖ u u' F0 what₂)

end Dens

def eta₃ (p : PlF D) : ℝ := if ∃ x : (D.s.atP p).Ep, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 then 1 else -1

def aPD (p : PlF D) (T : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc (if ((T : 𝓞 D.host.F) ∈ p.asIdeal) then D.R.k else D.R.k + 1) D.R.r,
    (1 - eta₃ p ^ i / ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ i)

def alpD (u u' : D.what₂.Word) (p : PlF D) : ℝ :=
  if Loc.resChar p = D.host.g 0 ∨ Loc.resChar p = D.host.g 1 then aPD p (D.mem u).A.T
  else aPD p (D.mem u).A.T * aPD p (D.mem u').A.T

def DensInputAt (D : Formalism.BasicNotions.D7) : Prop :=
  2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
      (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)), IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
      (∀ Z : CntLocal.MatZ D, (∃ Λ ∈ what₂, (CntLocal.EZ (CntLocal.Tn u') F0 Λ Z).Nonempty) →
        Multipliable (CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') Z)) ∧
      BddAbove (densSet L δ ϖ u u' F0 what₂) ∧ Multipliable (alpD u u') ∧ 0 < ∏' p, alpD u u' p ∧
      PB.DensInput D.R.k D.R.rS D.R.f (supDens L δ ϖ u u' F0 what₂ / ∏' p, alpD u u' p)

section Rows

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def Elig (t : TermDef.Term D u u' F0 what₂) : Prop := t.generic ∧ t.G ≠ 0

def RowLabel (κ : TermDef.Term D u u' F0 what₂ → ℕ) : Prop :=
  ∀ t t', Elig t → Elig t' → (κ t = κ t' ↔ Corank.TermScal D t t')

def rowVec (vR : TermDef.Term D u u' F0 what₂ → ℝ) (κ : TermDef.Term D u u' F0 what₂ → ℕ) (nc : ℝ) (ρ : ℕ)
    (x : TB.Pt D.host.E) : ℂ :=
  match ptOfList (D.R.rS + 1) x with
  | some w => (∑' t : {t : TermDef.Term D u u' F0 what₂ // Elig t ∧ κ t = ρ ∧ t.atPt w},
        ((Real.sqrt (PairVal.massTerm t.1) : ℝ) : ℂ) * PairVal.cAt vR t.1 w) /
      ((Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T w) * Formalism.L2.SG.DataInst.phi (D.R.rS + 1) x : ℝ) : ℂ)
  | none => 0

theorem isPt_of_isPtL {x : TB.Pt D.host.E} {i : ℕ} (h : Formalism.L2.S.IsPtL x i) : TB.IsPt x i := by
  obtain ⟨h1, h2⟩ := h
  unfold TB.IsPt TB.level
  exact ⟨h1, fun k hk => h2 _ (List.getElem_mem ..)⟩

theorem rowVec_support (vR : TermDef.Term D u u' F0 what₂ → ℝ) (κ : TermDef.Term D u u' F0 what₂ → ℕ) (nc : ℝ)
    (ρ : ℕ) (x : TB.Pt D.host.E) (h : rowVec vR κ nc ρ x ≠ 0) : TB.IsPt x (D.R.rS + 1) := by
  apply isPt_of_isPtL
  unfold rowVec at h
  cases hx : ptOfList (D.R.rS + 1) x with
  | none => rw [hx] at h; exact absurd rfl h
  | some w => exact isPtL_of_ptOfList_ne_none (by simp [hx])

end Rows

section RowsStmt

variable {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def RowsPSD (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (L : CntLocal.LocSp D M) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (vR : TermDef.Term D u u' F0 what₂ → ℝ)
    (κ : TermDef.Term D u u' F0 what₂ → ℕ) (nc α : ℝ) : Prop :=
  ∀ Y : Finset (TB.Pt D.host.E), (∀ p ∈ Y, TB.IsPt p ((dOf S δ M u u').r + 1)) → ∀ R : Finset ℕ,
    TB.PSDOn Y (fun p q => ((supDens L δ ϖ u u' F0 what₂ / α : ℝ) : ℂ) *
        (dOf S δ M u u').Kr ((dOf S δ M u u').r + 1) p q -
      ∑ ρ ∈ R, rowVec vR κ (nc * α) ρ p * (starRingEnd ℂ) (rowVec vR κ (nc * α) ρ q))

def RowsSum {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (vR : TermDef.Term D u u' F0 what₂ → ℝ)
    (κ : TermDef.Term D u u' F0 what₂ → ℕ) (nc : ℝ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Vt : TB.Pt D.host.E → H) : Prop :=
  ∀ ρ, Summable fun p : TB.Pt D.host.E => ‖rowVec vR κ nc ρ p‖ * ‖Vt p‖

theorem rowsInput_of {S : C.HidaSetting D.host.E Wp Wq} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hC : Compat S u u') {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]} {nc : ℝ}
    {vR : TermDef.Term D u u' F0 what₂ → ℝ} {κ : TermDef.Term D u u' F0 what₂ → ℕ} {α : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Vt : TB.Pt D.host.E → H}
    (hPSD : RowsPSD S δ M L u u' F0 what₂ ϖ vR κ nc α) (hSum : RowsSum vR κ (nc * α) Vt)
    {P : Type} [Fintype P] (B : S3.MassData P) (hsd : B.supdens = supDens L δ ϖ u u' F0 what₂ / α) (hKV : 0 ≤ B.KV)
    (h4 : ∀ Mb : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, rowVec vR κ (nc * α) ρ p • Vt p‖ ^ 2 ≤ Mb) →
      B.c0 * B.c0' * B.KV ≤ B.n0c * Mb) :
    PB.RowsInput (dOf S δ M u u') (supDens L δ ϖ u u' F0 what₂ / α) Vt (rowVec vR κ (nc * α)) B := by
  refine ⟨fun ρ p h => ?_, fun Y hY R => hPSD Y hY R, hSum, h4, hKV, hsd⟩
  have := rowVec_support vR κ (nc * α) ρ p h
  rw [dOf_r, hC.1]
  exact this

def RowLabelExists (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)), IsRowReps D F0 what₂ →
    ∃ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ

def RowsInputAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting D.host.E Wp Wq) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep), (∀ p, Agree δ M p) →
    ∀ (L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Compat S u u' →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
      (∃ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ) ∧
      ∀ κ : TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
        RowsPSD S δ M L u u' F0 what₂ ϖ (PairVal.vRdef D u u' F0 what₂ δ M) κ nc α

end RowsStmt

end Formalism.L2.SG.DataInst
