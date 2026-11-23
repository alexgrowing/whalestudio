import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts
import Formalism.LocalToGlobal.Columns.LevGSym

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

section Conv

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

def conv (c c' : WO S T →₀ ℂ) : WO S T →₀ ℂ :=
  ∑ x ∈ c.support, ∑ y ∈ c'.support, Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y))

def convList (l : List (WO S T →₀ ℂ)) : WO S T →₀ ℂ := l.foldr (conv ψ S T) (Finsupp.single 0 1)

theorem comb_conv (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (conv ψ S T c c') f = comb ψ S T c (comb ψ S T c' f) := by
  have h0 := fun u => zero_smul ℂ (heisO ψ S T u f)
  have h1 := fun u (a b : ℂ) => add_smul a b (heisO ψ S T u f)
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, conv, ← Finsupp.sum_finset_sum_index h0 h1]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finsupp.sum_finset_sum_index h0 h1]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_single_index (h0 _), GlobalTheory.WeilVacMove.heisO_heisO, smul_smul]

theorem comb_unit (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (zero_smul ℂ _), one_smul]
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem comb_convList {α : Type} (l : List α) (c : α → WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (convList ψ S T (l.map c)) f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil => exact comb_unit ψ S T f
  | cons i l ih => exact (comb_conv ψ S T _ _ f).trans (congrArg _ ih)

variable {ψ S T}

theorem mem_support_conv {c c' : WO S T →₀ ℂ} {w : WO S T} (hw : w ∈ (conv ψ S T c c').support) :
    ∃ x ∈ c.support, ∃ y ∈ c'.support, w = x + y := by
  classical
  obtain ⟨x, hx, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hw)
  obtain ⟨y, hy, h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum h2)
  exact ⟨x, hx, y, hy, Finset.mem_singleton.1 (Finsupp.support_single_subset h3)⟩

theorem support_convList {p : WO S T → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) {l : List (WO S T →₀ ℂ)}
    (hl : ∀ c ∈ l, ∀ x ∈ c.support, p x) : ∀ w ∈ (convList ψ S T l).support, p w := by
  induction l with
  | nil => exact fun w hw => Finset.mem_singleton.1 (Finsupp.support_single_subset hw) ▸ h0
  | cons c l ih =>
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_support_conv hw
    exact hadd x y (hl c List.mem_cons_self x hx) (ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) y hy)

example (x y : WO S T) :
    conv ψ S T (Finsupp.single x 1) (Finsupp.single y 1) = Finsupp.single (x + y) (ψ (symplOH S T x y)) := by
  rw [conv, Finsupp.support_single_ne_zero _ one_ne_zero, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finset.sum_singleton, Finsupp.single_eq_same, Finsupp.single_eq_same, one_mul, one_mul]

end Conv

section Gen

open Formalism.L2.DIV (Pl kP LevelP)
open GlobalTheory.SymBridge GlobalTheory.LocMod

variable {D : D7} {u : D.what₂.Word}

def symLevel (Pg : Finset (Pl D.host.E)) (ψ₀ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) : LevelP Pg D.R.r ℂ :=
  LevelP.ofLocal (fun PP => Formalism.L2.Col.HPsymF (kP PP.1) D.R.r D.R.k D.R.rS)
    fun PP => Formalism.L2.Col.chiSymF (ψ₀ PP.1) D.R.r D.R.k D.R.rS

theorem mem_symLevel {Pg : Finset (Pl D.host.E)} {ψ₀ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ} (g : Formalism.L2.DIV.G0 Pg D.R.r) :
    g ∈ (symLevel Pg ψ₀).H ↔ ∀ PP, g PP ∈ Formalism.L2.Col.HPsymF (kP PP.1) D.R.r D.R.k D.R.rS :=
  ⟨fun h PP => h PP (Set.mem_univ _), fun h PP _ => h PP⟩

theorem symLevel_chi {Pg : Finset (Pl D.host.E)} {ψ₀ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ} (g : (symLevel Pg ψ₀).H) :
    (symLevel Pg ψ₀).chi g =
      ∏ PP : Pg, Formalism.L2.Col.chiSymF (ψ₀ PP.1) D.R.r D.R.k D.R.rS ⟨g.1 PP, (mem_symLevel g.1).1 g.2 PP⟩ :=
  MonoidHom.finset_prod_apply _ _ _

section At

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Pl D.host.E} (G : GX a ζ₀ PP)

def GX.emb : D.host.E →+* G.k := G.q.pr.comp (incA D)

structure GX.Frames (fr : ∀ i, i ≤ D.R.m → Matrix (Fin (D.sp.X i).rank) (Fin (D.R.N i)) D.host.E) : Prop where
  under : G.q.v = PP.under (𝓞 D.host.F)
  frX : ∀ i (hi : i ≤ G.s + 1) (hm : i ≤ D.R.m), ∃ e : XIx (Fin D.R.k) (Fin D.R.t) i ≃ Fin (D.R.N i), IsOrd xPos e ∧
    ∀ r c, (G.FX i hi).β r c = G.emb (fr i hm r (e c))
  frM : ∀ hm : G.s + 1 + 1 ≤ D.R.m,
    ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2) ⊕ Unit ≃ Fin (D.R.N (G.s + 1 + 1)),
      IsOrd (Sum.elim zPos fun _ => D.R.N D.R.m - 1) e ∧
        ∀ r c, valuation G.k (G.FM.β r c - G.emb (fr (G.s + 1 + 1) hm r (e c))) < 1

def GX.InCoset (y : Fin (D.R.N (G.s + 1)) → D.host.E) : Prop :=
  ∀ e : XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ≃ Fin (D.R.N (G.s + 1)), IsOrd xPos e → ∀ c,
    G.emb (y (e c)) - G.S.y0 (Fin D.R.t) c ∈ 𝒪[G.k]

end At

structure StdSp (a : XPart D u) (ζ₀ : Fin a.Lz.rank → D.host.E) (π : D.host.E) : Prop where
  cart : ∀ j, j ≤ D.R.m → (a.x j).s = fun _ => 1
  onb : ∀ j, j ≤ D.R.m → (a.x j).B = fun _ => 1
  lat : ∀ j, j ≤ D.R.m → ∀ z, z ∈ (a.x j).L ↔ z ∈ GlobalTheory.AdForm.intVec D _
  lzRank : a.Lz.rank = 1
  lzGram : a.Lz.gram = 1
  lzSig : a.Lz.SigOK ∧ a.Lz.IsPosDef
  zeta : ζ₀ = fun _ => π
  iA : ∀ n h r c, (a.oT n h).iA r c = if r.val = c.val then 1 else 0
  iB : ∀ n h r c, (a.oT n h).iB r c = if r.val + 1 = (D.sp.X n).rank then 1 else 0
  topFr : a.top.β = 1
  topLat : ∀ z, z ∈ a.top.Λ ↔ z ∈ GlobalTheory.AdForm.intVec D _
  top : a.top.st.Is a.c D.R.m

namespace StdSp

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {π : D.host.E} (H : StdSp a ζ₀ π)
include H

theorem norm : star ζ₀ ⬝ᵥ a.Lz.gram *ᵥ ζ₀ = star π * π := by
  rw [H.lzGram, H.zeta, Matrix.one_mulVec]
  simp [dotProduct, H.lzRank]

theorem line (h : π ≠ 0) : IsLineVec a.Lz ζ₀ := ⟨H.lzRank, by rw [H.norm]; exact mul_ne_zero (star_ne_zero.2 h) h⟩

theorem vec (n) (h : n = D.R.m) (r) : vecB (a.oT n h) ζ₀ r = if r.val + 1 = (D.sp.X n).rank then π else 0 := by
  simp only [vecB, Matrix.mulVec, dotProduct, H.iB, H.zeta]
  split_ifs <;> simp [H.lzRank]

end StdSp

example {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {π : D.host.E} (h : (a.x 0).L = ⊥) : ¬ StdSp a ζ₀ π := fun H => by
  have h1 := (H.lat 0 (Nat.zero_le _) fun _ => 1).2 fun _ => isIntegral_one
  rw [h, Submodule.mem_bot] at h1
  exact one_ne_zero (congrFun h1 ⟨0, GlobalTheory.FinPl.rank_pos_of_le D (Nat.zero_le _)⟩)

def unitLine (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem unitLine_spec (D : D7) :
    (unitLine D).rank = 1 ∧ (unitLine D).gram = 1 ∧ (unitLine D).SigOK ∧ (unitLine D).IsPosDef := by
  refine ⟨rfl, ?_, Examples₂.posSpace_sigOK _ 1, fun _ => rfl⟩
  refine Matrix.ext fun i j => ?_
  refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0 i j).trans ?_
  obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
  rw [Matrix.one_apply_eq]
  exact if_pos rfl

def lastDec {V A : HSp D} (hV : V.gram = 1) (hA : A.gram = 1) (h : A.rank + 1 = V.rank) : OrthDec V A (unitLine D) where
  iA := Matrix.of fun r c => if r.val = c.val then 1 else 0
  iB := Matrix.of fun r _ => if r.val + 1 = V.rank then 1 else 0
  isoA := by
    refine Matrix.ext fun i j => ?_
    rw [hV, hA, Matrix.mul_one, Matrix.mul_apply, Finset.sum_eq_single ⟨i.val, by omega⟩]
    · simp [Matrix.one_apply, Fin.ext_iff]
    · intro r _ hr
      have : r.val ≠ i.val := fun e => hr (Fin.ext e)
      simp [this]
    · simp
  isoB := by
    refine Matrix.ext fun i j => ?_
    have hij : i = j := Subsingleton.elim (α := Fin 1) i j
    rw [hV, (unitLine_spec D).2.1, Matrix.mul_one, Matrix.mul_apply, Finset.sum_eq_single ⟨A.rank, by omega⟩]
    · rw [hij, Matrix.one_apply_eq]
      simp [h]
    · intro r _ hr
      have : r.val + 1 ≠ V.rank := fun e => hr (Fin.ext (by simp only; omega))
      simp [this]
    · simp
  orth := by
    refine Matrix.ext fun i j => ?_
    rw [hV, Matrix.mul_one, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases e : r.val = j.val
    · have : r.val + 1 ≠ V.rank := by omega
      simp [this]
    · simp [e]
  rank_add := h

section Ker

variable {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

@[reducible] def XPart.withKer (a : XPart D u) (c : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) : XPart D u :=
  { a with k := fun j => ⟨(a.k j).om, (a.k j).vac, c j⟩ }

@[reducible] def OffX.withKer (o : OffX a k ι) (c cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) : OffX (a.withKer c) k ι :=
  { o with cG := cG }

@[reducible] def GX.withKer {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Pl D.host.E} (G : GX a ζ₀ PP)
    (c : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) : GX (a.withKer c) ζ₀ PP :=
  { G with }

def prodG {ζ₀ : Fin a.Lz.rank → D.host.E} (G : ∀ PP : a.c.Pg, GX a ζ₀ PP.1) (j : ℕ) : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ :=
  if j < D.R.m then convList a.c.ψ _ _ (a.c.Pg.attach.toList.map fun PP => (G PP).cg j) else 0

end Ker

end Gen

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.SymBridge Formalism.L2.Forms Formalism.IndefR.Links

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

def psiC (P : HeightOneSpectrum (𝓞 B.fields.E)) : AddChar (𝓞 B.fields.E ⧸ P.asIdeal) ℂ :=
  (B.embLL : B.LL →* ℂ).compAddChar (Formalism.L2.Col.psi0P I.Ch P)

def chiC (i : ℕ) (P : HeightOneSpectrum (𝓞 B.fields.E)) : (𝓞 B.fields.E ⧸ P.asIdeal)ˣ →* ℂˣ :=
  (Units.map (B.embLL : B.LL →* ℂ)).comp (Formalism.L2.Col.chiP I.Ch P i)

theorem chiC_apply (i P x) : ((chiC I i P x : ℂˣ) : ℂ) = B.embLL ((Formalism.L2.Col.chiP I.Ch P i x : B.LLˣ) : B.LL) := rfl

structure IsComOf (c : GlobalTheory.ChainOnto.Com (I.rec7 l Z)) : Prop where
  std : IsStdChar (I.rec7 l Z) c.ψ (-1)
  inf : IsInfFam c.θ
  places : c.Pg = (B.primes X).vGs
  mu : ∀ j : Fin B.R.m, ChrEq (c.μ ((j : ℕ) + 1)) (I.C.mu0 j)
  eta : ChrEq c.η I.C.eta
  chi : ∀ i PP, c.chi (i + 1) PP = chiC I i PP
  lev : c.P = symLevel c.Pg (psiC I)

variable {I l Z}

theorem IsComOf.nonempty {c} (H : IsComOf I l Z c) : c.Pg.Nonempty := by
  classical
  obtain ⟨w, hw⟩ := Finset.card_pos.1 ((l.pr.vG_card 0).symm ▸ (base_fields_primes_ok B X).1.f_pos)
  refine ⟨w, ?_⟩
  rw [H.places]
  unfold Formalism.L2.Col.Primes.vGs
  exact (@Finset.mem_union _ (_) _ _ _).2 (Or.inl hw)

variable {v : B.Word} {Ch : ℕ → Type} (A : ColDat I l Z v Ch)

def BaseCoset : Prop :=
  ∀ j, j + 1 = B.R.m → ∀ P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs →
    ∃ c : Fin (B.R.N j), c.val = B.R.k ∧
      (Pi.single c ((Formalism.L2.Col.qOf P.1 : B.fields.E))⁻¹ : Fin (B.R.N j) → B.fields.E) ∈ cosetIn (A.p0 j) P

def BaseOne (i : ℕ) (hi : i ≤ B.R.m) : Prop :=
  ∀ P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs → ∀ r c,
    HeightOneSpectrum.valuation (I.rec7 l Z).host.E (show HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) from P.1)
      (baseFr A i hi P r c - if r.val = c.val then 1 else 0) < 1

def BaseEnds : Prop := BaseOne A 0 (Nat.zero_le _) ∧ BaseOne A B.R.m le_rfl

def baseY (j : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) : Fin (B.R.N j) → B.fields.E :=
  (Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 j).1.1 P).symm (Formalism.L2.Col.repY (A.p0 j).1.2)

variable {A} in

theorem BaseCoset.intAt (H : BaseCoset A) {j : ℕ} (hj : j + 1 = B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0))
    (hP : P.1 ∈ (B.primes X).vGs) (i : Fin (B.R.N j)) :
    Formalism.L2.Col.IntAt P.1 (baseY A j P i - if i.val = B.R.k then ((Formalism.L2.Col.qOf P.1 : B.fields.E))⁻¹ else 0) := by
  letI := GlobalTheory.Mem.Col2.starE B
  obtain ⟨c, hc, y, hy, h⟩ := H j hj P hP
  obtain ⟨y₀, -, e⟩ := (A.p0 j).mem_ybSet hj
  have h1 := (A.p0 j).repY_mem hj
  rw [e] at hy
  have h1' := e.subset h1
  have h2 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 (sub_mem h1' hy) P
  rw [if_pos hP, pow_zero, inv_one, one_smul] at h
  simp only [if_pos hP, zpow_zero, inv_one, one_smul, sub_sub_sub_cancel_right] at h2
  have h3 := GlobalTheory.ColNorms.liftFr_lifts B.fields.E _ _ _ (A.p0 j).1.1.deco ⟨P.1, hP⟩
  have e2 : Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 j).1.1 P = (A.p0 j).1.1.deco.1.liftFr ⟨P.1, hP⟩ := dif_pos hP
  have h4 := (h3.1 ((Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 j).1.1 P).symm (Formalism.L2.Col.repY (A.p0 j).1.2 - y))).1 (by
    rw [← e2, LinearEquiv.apply_symm_apply]
    exact h2)
  have h5 := (Formalism.L2.Col.mem_localization_standardLattice P.1 _).1 (sub_mem h4 h) i
  convert h5 using 1
  simp only [baseY, map_sub, Pi.sub_apply, Pi.single_apply, Fin.ext_iff, hc]
  ring

variable {a : XPart (I.rec7 l Z) v}

structure TiedX {ζ₀ : Fin a.Lz.rank → (I.rec7 l Z).host.E} {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} (G : GX a ζ₀ PP)
    (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) : Prop where
  eq : P.1 = PP
  type : letI := G.fld; letI := G.val; letI := G.top; letI := G.loc
    AtType (k := G.k) I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) B.embLL P G.emb G.S
  fr : G.Frames fun i hi => baseFr A i hi P

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl in

structure OffsetCompatibility (o : OffX a k ((B.primes X).vT v)) : Prop where
  idem : ∀ i, Formalism.L2.NTheta.IsIdemAt (o.p i).e i.1
  under : ∀ i, (o.p i).v = HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (show Formalism.L2.DIV.Pl (I.rec7 l Z).host.E from i.1)
  nodup : o.I.Nodup
  all : ∀ i, i ∈ o.I
  unif : ((o.q.1 : 𝒪[k]) : k) = (B.T v : ℕ)
  char : ∀ i, (o.p i).IsChar a.c.ψ (o.χ i)
  frame : ∀ j, j ≤ B.R.m → ∀ i, (o.β j i).b = 1
  lat : ∀ j, j ≤ B.R.m → ∀ i, (o.Q j i).lat = GlobalTheory.LatPair.stdLat k _

  fn : ∀ j (hj : j ≤ B.R.m) i (x : Fin (B.R.N j) → 𝓞 B.fields.E) (z : 𝓞 B.fields.E),
    Ideal.Quotient.mk i.1.asIdeal z =
      (letI := GlobalTheory.Mem.Col2.starE B; (A.p0 j).1.1.deco.1.f i fun r => (x r : B.fields.E)) →
    ∃ s : 𝒪[k], (s : k) = (o.p i).pr (incA (I.rec7 l Z) (z : B.fields.E)) ∧
      (o.Q j i).HasVal (fun r => (o.p i).pr (incA (I.rec7 l Z) (x (finCongr (rankN (I.rec7 l Z) j hj) r) : B.fields.E)))
        (residue 𝒪[k] s)
  supp : ∀ j, j < B.R.m → CombAt o.atT (o.cT j)
  rep : ∀ j, j < B.R.m → ∀ f, Vac a.c.ψ _ _ (a.x j).L (a.x (j + 1)).L o.atT f →
    OverAll a.c.ψ (o.β j) (o.β (j + 1)) (a.x j).L (a.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
      (comb a.c.ψ _ _ (o.cT j) f)
  frameTop : ∀ i, (o.γ i).b = 1
  sum : ∀ n h i, IsSumFrame (a.oT n h) o.ζ₀ (o.γ i) (o.γ₀ n h i)

variable (a) in

structure StdCol {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) : Prop where
  is : A.Is F a.c.ψ a.c.θ
  keeps : A.Keeps F
  coset : BaseCoset A
  ends : BaseEnds A
  chr : ∀ j, j < B.R.m → A.chr (j + 1) = a.c.μ (j + 1)
  rd : ∀ j (hj : j ≤ B.R.m), a.rd j = A.rd F a.c.θ j hj
  ram : ∀ j (hj : j ≤ B.R.m) φ, φ ∈ a.Ram j ↔ A.IsForm F j hj φ ∧ GlobalTheory.AdForm.RamAt (D := I.rec7 l Z) v j φ
  om : ∀ j, j < B.R.m → (a.k j).om = A.om j
  vac : ∀ j, j < B.R.m → (a.k j).vac = A.vac j
  vol : ∀ j, j ≤ B.R.m → (a.x j).vol.μ = A.μ j ∧ (a.x j).vol.𝓕 = A.fd j
  top : TopForm F a.top.M fun G y => (a.eT G).1 y
  onto : Function.Surjective a.eT

variable (w : World I l Z) (a : XPart (I.rec7 l Z) v) (o : OffX a k ((B.primes X).vT v)) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

structure XStdBy (A : ColDat I l Z v (w.C.herm.base.Ch v)) : Prop where
  com : IsComOf I l Z a.c
  sp : StdSp a o.ζ₀ ((X.piT v : 𝓞 B.host.E) : B.host.E)
  col : StdCol A a (w.C.forms v)
  atT : OffsetCompatibility A o
  atG : ∀ PP, ∃ P, TiedX A (G PP) P
  cG : ∀ j, j < B.R.m → o.cG j = convList a.c.ψ _ _ (a.c.Pg.attach.toList.map fun PP => (G PP).cg j)
  cG_zero : ∀ j, B.R.m ≤ j → o.cG j = 0
  ker : ∀ j, j < B.R.m → (a.k j).c = conv a.c.ψ _ _ (o.cG j) (o.cT j)

def XStd : Prop := ∃ A, XStdBy w a o G A

namespace XStdBy

variable {w a o G} {A : ColDat I l Z v (w.C.herm.base.Ch v)} (H : XStdBy w a o G A)
include H

theorem weil {j : ℕ} (hj : j < B.R.m) : IsWeilDatumO a.c.ψ _ _ (a.c.μ (j + 1)) (a.c.μ (j + 1)) (a.k j).om := by
  rw [H.col.om j hj, ← H.col.chr j hj]
  exact H.col.is.om j hj

theorem norm : star o.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ o.ζ₀ = ((B.T v : ℕ) : B.host.E) := by
  refine H.sp.norm.trans ?_
  have h := congrArg (algebraMap (𝓞 B.fields.E) B.fields.E) (l.pr.piT_norm v)
  rw [map_mul, map_natCast, mul_comm] at h
  exact h

end XStdBy

example : Nonempty ((B.primes X).vT v) :=
  let ⟨P, hP⟩ := Finset.card_pos.1 ((l.pr.vT_card v).symm ▸ (base_fields_primes_ok B X).1.f_pos)
  ⟨⟨P, hP⟩⟩

example (h : a.c.Pg = ∅) : ¬ XStd w a o G := fun ⟨_, H⟩ => H.com.nonempty.ne_empty h

example (H : OffsetCompatibility A o) : valuation k ((B.T v : ℕ) : k) < 1 := by
  rw [← H.unif]
  exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).1 o.q.2.not_isUnit

end World

end GlobalTheory.SeeSaw

end
