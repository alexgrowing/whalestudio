import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Formalism.LocalToGlobal.Columns.TwQBOpen
import Formalism.LocalToGlobal.Columns.TwQExact
import Formalism.LocalToGlobal.Columns.TwQLat
import Formalism.LocalToGlobal.Columns.TwQLev

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Cut

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}

def frStab (P : HeightOneSpectrum (𝓞 E)) (C : Set (Sp E n)) : Subgroup ↥(GLint E n P) where
  carrier := {g | ∀ v, g.1 v ∈ C ↔ v ∈ C}
  one_mem' _ := Iff.rfl
  mul_mem' {a b} ha hb v := (ha (b.1 v)).trans (hb v)
  inv_mem' {a} ha v := by
    have h := ha ((a⁻¹).1 v)
    have e : a.1 ((a⁻¹).1 v) = v := LinearEquiv.apply_symm_apply a.1 v
    rw [e] at h
    exact h.symm

theorem mem_frStab {P : HeightOneSpectrum (𝓞 E)} {C : Set (Sp E n)} {g : ↥(GLint E n P)} :
    g ∈ frStab P C ↔ ∀ v, g.1 v ∈ C ↔ v ∈ C := Iff.rfl

def cutQ (Θ : LevQFam E K n Q) (C : ∀ P : Q, Set (Sp E n)) : LevQFam E K n Q := fun P =>
  ⟨(Θ P).H ⊓ frStab P.1 (C P), (Θ P).lam.comp (Subgroup.inclusion inf_le_left)⟩

theorem mem_cutQ_grp {Θ : LevQFam E K n Q} {C : ∀ P : Q, Set (Sp E n)} {t : GLQ E n Q} :
    t ∈ (cutQ Θ C).grp ↔ t ∈ Θ.grp ∧ ∀ P, t P ∈ frStab P.1 (C P) := by
  simp only [LevQFam.grp, Subgroup.mem_pi, Set.mem_univ, forall_const]
  exact forall_and

theorem cutQ_grp_le (Θ : LevQFam E K n Q) (C : ∀ P : Q, Set (Sp E n)) : (cutQ Θ C).grp ≤ Θ.grp := fun _ ht => (mem_cutQ_grp.1 ht).1

end Cut

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

open Classical in

def cqOf (q : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) : Set (Sp X.E (R.N j)) :=
  cosetIn q ⟨P.1, Finset.mem_union_right _ P.2⟩

end Pt

end GlobalTheory.Mem.Col2.ChEx

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Inv

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

def InvActs (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) : Prop :=
  ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ) (r : PtY ST SG Q y) (P : Q),
    cq (ya Λ Θ g r) P = (fun v => (g.2.2.1 P).1 v) '' cq r P

def PtDet (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) : Prop :=
  ∀ r r' : PtY ST SG Q y, r.1.1 = r'.1.1 → bar r = bar r' → cq r = cq r' → r = r'

end Inv

theorem mem_map_conj {G : Type} [Group G] (S : Subgroup G) (k x : G) :
    x ∈ S.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * x * k ∈ S := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨k⁻¹ * x * k, h, by simp [mul_assoc]⟩

section Main

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (a : I.ι) (i : ℕ) := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i

abbrev lvQ (a : I.ι) (i : ℕ) := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i

abbrev rpT (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : PtAt B.R I.sel (I.tup a) (I.cst a) u i :=
  rp (lvG I a i) (lvQ I a i) ((I.Tp a).pref u i) (I.pref u a i) c

open Classical in
theorem q_sub_SQ (a : I.ι) : I.Q a ⊆ I.SQ := by
  intro P hP
  unfold ColIn.SQ
  exact Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hP⟩

theorem q_disj (hI : I.Ok) (a : I.ι) : ∀ P ∈ QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K), P ∉ (B.primes X).vGs := by
  intro P hP hG
  exact Finset.disjoint_left.1 (LevTwist.levOk_twists B X I hI).2.1 hG (q_sub_SQ I a hP)

theorem q_conj (hI : I.Ok) (a : I.ι) : ∀ P : I.Q a, conjPrime₂ P.1 ≠ P.1 := by
  intro P hc
  obtain ⟨-, hs⟩ := (LevTwist.levOk_twists B X I hI).1
  have hm : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    simp [uSG, q_sub_SQ I a P.2]
  exact hs _ hm (by rw [hc]; exact hm)

theorem cos_of_neT {u : B.Word} {a : I.ι} {i : ℕ} (h : i + 1 ≠ B.R.m) (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u i) :
    cosetIn q = cosetIn q' := by
  have e : ∀ r : PtAt B.R I.sel (I.tup a) (I.cst a) u i, r.1.2 = ∅ := fun r => by
    have hr := r.2
    rw [ysAt_ys_of_ne (h := h)] at hr
    exact Set.mem_singleton_iff.1 hr
  funext P
  ext z
  simp [cosetIn, e q, e q']

end Main

end GlobalTheory.Mem.Col2.ChEx
