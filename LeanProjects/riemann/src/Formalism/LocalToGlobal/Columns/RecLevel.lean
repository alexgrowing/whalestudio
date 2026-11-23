import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.ColForms
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalRingCardinality.DataLevel

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

def levU : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := (JH hc n ST SG H).map (J0 hc n ST).subtype

theorem mem_levU {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} :
    x ∈ levU hc n ST SG H ↔ ∃ h : x ∈ J0 hc n ST, redG hc n ST SG ⟨x, h⟩ ∈ H := by
  unfold levU
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem unipotentLevel_le_mirabolicLevel : levU hc n ST SG H ≤ J0 hc n ST := Subgroup.map_subtype_le _

theorem levU_le_UAd : levU hc n ST SG H ≤ UAd hc n := fun x hx =>
  (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (unipotentLevel_le_mirabolicLevel hc n ST SG H hx)).1).1

theorem kOne_le_unipotentLevel : K1 hc n ST SG ≤ levU hc n ST SG H := by
  unfold K1 levU
  apply Subgroup.map_mono
  intro y hy
  rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hy]
  exact H.one_mem

def levRed : levU hc n ST SG H →* H :=
  ((redG hc n ST SG).comp (Subgroup.inclusion (unipotentLevel_le_mirabolicLevel hc n ST SG H))).codRestrict H
    (fun x => ((mem_levU hc n ST SG H).1 x.2).2)

variable {hc n ST SG H}

def levChr {M : Type} [CommGroup M] (lam : H →* M) : levU hc n ST SG H →* M := lam.comp (levRed hc n ST SG H)

def levTyp {M : Type} [CommGroup M] (lam : H →* M) : levU hc n ST SG H →* M := (levChr lam)⁻¹

variable (hc n ST SG H)

def levLoc (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F)) :=
  (levU hc n ST SG H).map (Formalism.UG.bc (Formalism.UG.prV (E := E) v))

end Lev

def IsOver {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (P : Pl E) : Prop :=
  v.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))

def plUnder (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (Pl E)) : Set (HeightOneSpectrum (𝓞 F)) := {v | ∃ P ∈ S, IsOver v P}

section Base

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) [NeZero n] (ST : Finset (Pl E))

def baseLb : Submodule (𝓞 E) (Fin n → E) := (Deco.base E n ST (∅ : Finset (Pl E))).L

def baseSh : Submodule (𝓞 E) (Fin n → E) := (Deco.base E n ST (∅ : Finset (Pl E))).Lsh

def baseKer : Submodule (𝓞 E) (Fin n → E) :=
  baseSh E n ST ⊓ ⨅ P ∈ ST, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (baseLb E n ST)

end Base

section Fun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E))

abbrev baseDual : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))

abbrev baseDualV (v : HeightOneSpectrum (𝓞 F)) : Submodule (Formalism.BasicNotions.intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseDual hc n ST)

abbrev fMod (v : HeightOneSpectrum (𝓞 F)) : Type :=
  baseDualV hc n ST v ⧸ (Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseKer E n ST)).comap
    (baseDualV hc n ST v).subtype

def fLoc (v : HeightOneSpectrum (𝓞 F)) : baseDualV hc n ST v →ₗ[Formalism.BasicNotions.intV E v] fMod hc n ST v :=
  Submodule.mkQ _

end Fun

section Cls

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

abbrev AdCl : Type := Formalism.L2.DIV.Cl hc (1 : Matrix (Fin n) (Fin n) E) (levU hc n ST SG H)

abbrev DecoCl : Type := MulAction.orbitRel.Quotient (UF E n × H) (DecoSet E n ST SG)

def decoCls (d : DecoSet E n ST SG) : DecoCl n ST SG H := Quotient.mk (MulAction.orbitRel (UF E n × H) (DecoSet E n ST SG)) d

def ptOf (d : DecoSet E n ST SG) : UAd hc n :=
  open Classical in
  if h : ∃ x : UAd hc n, decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d then h.choose else 1

def adClsOf (d : DecoSet E n ST SG) : AdCl hc n ST SG H := Quotient.mk'' (ptOf hc n ST SG d)

def decoOfD (c : DiaG E ST) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : DecoSet E n ST SG := (decoOf ST SG x).dia c

def ptOfD (c : DiaG E ST) (d : DecoSet E n ST SG) : UAd hc n := ptOf hc n ST SG (d.dia c⁻¹)

def stabRat (d : DecoSet E n ST SG) : MulAction.stabilizer (UF E n × H) d →* URat hc n :=
  (ratEquiv hc n).symm.toMonoidHom.comp ((MonoidHom.fst (UF E n) H).comp (Subgroup.subtype _))

end Cls

section Par

variable {E K : Type} [Field E] [NumberField E] [Field K] {r n : ℕ}

def parFam (h : r ≤ n) (t s : ℕ) {SG : Finset (Pl E)} (P : LevFam E K r SG)
    (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) : LevFam E K n SG := fun w =>
  ⟨HPar n (𝓞 E ⧸ w.1.asIdeal) h (List.replicate s t) (P w).H, lamPar h (List.replicate s t) (P w).lam (χ w)⟩

open Classical in

def parDat (h : r ≤ n) (t s : ℕ) {SG : Finset (Pl E)} (P : LevFam E K r SG)
    (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) : Formalism.L2.DIV.LevDat E K n where
  r := r
  hr := h
  t := t
  s := s
  Pg := SG
  Q := ∅
  P := Formalism.L2.DIV.LevelP.ofLocal (fun w => (P w).H) (fun w => (P w).lam)
  cg := fun c PP => if hP : PP ∈ SG then χ ⟨PP, hP⟩ (c - 1) else 1
  xq := fun _ => 1

end Par

section Cols

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem kj_le_N (R : Ranks) (j : ℕ) : R.k + j ≤ R.N j := by
  simp only [Ranks.N, Nat.mul_add, Nat.mul_one]
  omega

theorem N_eq_blocks (R : Ranks) (j : ℕ) : R.N j = (R.k + j) + j * R.t := by
  simp only [Ranks.N, Nat.mul_add, Nat.mul_one]
  omega

instance neZeroN (R : Ranks) (j : ℕ) : NeZero (R.N j) := ⟨(R.N_pos j).ne'⟩

def colP (Ch : Chars X Pr R.m) (j : ℕ) : LevFam X.E X.K (R.k + j) Pr.vGs := fun w =>
  ⟨HU (𝓞 X.E ⧸ w.1.asIdeal) (R.k + j), supChar (Ch.psi0 w) (R.k + j) (R.k + j) [] (SX R.k R.m j)⟩

def colDat (Ch : Chars X Pr R.m) (j : ℕ) : Formalism.L2.DIV.LevDat X.E X.K (R.N j) :=
  parDat (kj_le_N R j) R.t j (colP Ch j) fun w => extChi fun s => Ch.chi s w

def colLevS (Ch : Chars X Pr R.m) (j : ℕ) : LevFam X.E X.K (R.N j) Pr.vGs := fun w =>
  if j + 1 < R.m then colLev Ch j w
  else if j + 1 = R.m then
    ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j ⊓ fixCol (R.N j) (𝓞 X.E ⧸ w.1.asIdeal) R.k,
      (lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j).comp (Subgroup.inclusion inf_le_left)⟩
  else
    ⟨HXmsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m,
      lamXmsharp (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m⟩

@[reducible] def colGSDS (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (u : Pr.Word) (j : ℕ) : GSD X.K :=
  formGSD (colVal W u j (Pr.vT u) Pr.vGs) (colLevS Ch j)

variable (hc : Formalism.BasicNotions.CMData X.F X.E) (Ch : Chars X Pr R.m)

def colU (u : Pr.Word) (j : ℕ) : Subgroup (GL (Fin (R.N j)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) :=
  levU hc (R.N j) (Pr.vT u) Pr.vGs (colLev Ch j).grp

def colUS (u : Pr.Word) (j : ℕ) : Subgroup (GL (Fin (R.N j)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) :=
  levU hc (R.N j) (Pr.vT u) Pr.vGs (colLevS Ch j).grp

open Classical in

def diaT (u : Pr.Word) : DiaG X.E (Pr.vT u) := fun P =>
  if h : IsUnit (Ideal.Quotient.mk P.1.asIdeal (X.conjO (Pr.piT u))) then h.unit else 1

def colDia (R : Ranks) (u : Pr.Word) (j : ℕ) : DiaG X.E (Pr.vT u) := if j < R.m then 1 else diaT u

def colPt (u : Pr.Word) (j : ℕ) (d : ColDeco X Pr u (R.N j)) : UAd hc (R.N j) :=
  ptOfD hc (R.N j) (Pr.vT u) Pr.vGs (colDia R u j) d

def colTyp (u : Pr.Word) (j : ℕ) : colU hc Ch u j →* X.Kˣ := levTyp (colLev Ch j).chr

def colTypS (u : Pr.Word) (j : ℕ) : colUS hc Ch u j →* X.Kˣ := levTyp (colLevS Ch j).chr

end Cols

end Formalism.L2.Col
