import Formalism.LocalToGlobal.Divisibility.NumbersLink
import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ColumnBoundOfPaths
import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AtG.EntryG

open Formalism.L2.Col (Fields Sp HomE homAt divLat IsSdLat)
open Formalism.L2.Ker (Amb DVar)
open Formalism.L2.AlgTh (KerStd SplitS JetAtSplit IsQInt GAt)
open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

section Terms

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ}

structure Term (X : Fields) (p : ℕ) [Fact p.Prime] (a b : ℕ) where

  coef : ℂ_[p]

  scal : X.K

  xi : X.K

  S : Finset (HeightOneSpectrum (𝓞 X.E))

  N : Submodule (𝓞 X.E) (Sp X.E a)

  N' : Submodule (𝓞 X.E) (Sp X.E b)

  c' : ℕ

  x : HomE X.E a b

  m : DVar X.Tau a b →₀ ℕ

def Term.val (A : Amb X) (ι : ℂ ≃+* ℂ_[p]) (T : Term X p a b) : ℂ_[p] :=
  T.coef * ι (A.σ₀ T.scal) * ι (A.σ₀ T.xi) * ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))

def Term.Ok (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (T : Term X p a b) : Prop :=
  ‖T.coef‖ ≤ 1 ∧ ‖ι (A.σ₀ T.scal)‖ ≤ 1 ∧ ‖ι (A.σ₀ T.xi)‖ ≤ ‖(p : ℂ_[p])‖ ^ e ∧
  KerStd A T.N T.N' a₀ b₀ c₀ ha hd lam hlam p ι ∧ IsSdLat T.N ∧ IsSdLat T.N' ∧ A.LaHyp a b T.S ∧ SplitS A T.S p ϖ pE ∧
  0 < T.c' ∧ ¬ p ∣ T.c' ∧ T.x ∈ divLat T.c' (homAt T.S T.N T.N') ∧ T.m.degree = D

def IsEntryG (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) (y : ℂ_[p]) : Prop :=
  ∃ (n : ℕ) (T : Fin n → Term X p a b), y = ∑ k, (T k).val A ι ∧ ∀ k, (T k).Ok A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e

theorem isEntryG_zero (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ι : ℂ ≃+* ℂ_[p])
    (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) (a b : ℕ) : IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e a b 0 :=
  ⟨0, Fin.elim0, by simp, fun k => k.elim0⟩

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ :=
  norm_pos_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

theorem term_bound (hJ : JetAtSplit) (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0)
    (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (hp2 : p ≠ 2) (hpd : ¬ p ∣ A.d) (hϖ : IsQInt A.d ϖ) (hϖϖ : ϖ * conj ϖ = (p : ℂ))
    {D : ℕ} {e : ℝ} {T : Term X p a b} (hT : T.Ok A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e) :
    ‖T.val A ι‖ * ‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) ≤ 1 := by
  obtain ⟨hc, hs, hx, hK, hN, hN', hLa, hS, hc0, hcp, hxd, hm⟩ := hT
  have hj := hJ X A a b T.S T.N T.N' a₀ b₀ c₀ ha hd lam hlam p ι hp2 hpd hK hN hN' hLa ϖ pE hϖ hϖϖ hS T.c' T.x hc0 hcp hxd T.m
  rw [hm] at hj
  have hp0 := norm_p_pos (p := p)
  have hval : ‖T.val A ι‖ ≤ ‖(p : ℂ_[p])‖ ^ e * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ := by
    unfold Term.val
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖T.coef‖ * ‖ι (A.σ₀ T.scal)‖ ≤ 1 :=
      (mul_le_mul hc hs (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1))
    calc ‖T.coef‖ * ‖ι (A.σ₀ T.scal)‖ * ‖ι (A.σ₀ T.xi)‖ * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖
        ≤ 1 * ‖(p : ℂ_[p])‖ ^ e * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ := by
          gcongr
      _ = ‖(p : ℂ_[p])‖ ^ e * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ := by ring
  have hsplit : ‖(p : ℂ_[p])‖ ^ e * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) =
      ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) := by
    rw [← Real.rpow_add hp0, add_sub_cancel, Real.rpow_natCast]
  have hR0 : 0 ≤ ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) := Real.rpow_nonneg hp0.le _
  calc ‖T.val A ι‖ * ‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e)
      ≤ (‖(p : ℂ_[p])‖ ^ e * ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖) * ‖ι (conj ϖ)‖ ^ D *
          ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) := by gcongr
    _ = ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ * ‖ι (conj ϖ)‖ ^ D *
          (‖(p : ℂ_[p])‖ ^ e * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e)) := by ring
    _ = ‖ι (A.σ₀ (A.jetK T.S T.N T.N' (p * T.c') T.x T.m))‖ * ‖ι (conj ϖ)‖ ^ D *
          ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) := by rw [hsplit]
    _ ≤ 1 := hj

theorem entry_bound (hJ : JetAtSplit) (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0)
    (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (hp2 : p ≠ 2) (hpd : ¬ p ∣ A.d) (hϖ : IsQInt A.d ϖ) (hϖϖ : ϖ * conj ϖ = (p : ℂ))
    {D : ℕ} {e : ℝ} {y : ℂ_[p]} (hy : IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE D e a b y) :
    ‖y‖ * ‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) ≤ 1 := by
  obtain ⟨n, T, rfl, hT⟩ := hy
  have hp0 := norm_p_pos (p := p)
  have hϖ0 : conj ϖ ≠ 0 := by
    intro h0
    have h1 : (p : ℂ) = 0 := by rw [← hϖϖ, h0, mul_zero]
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
  have hι0 : 0 < ‖ι (conj ϖ)‖ := norm_pos_iff.mpr (by simpa using hϖ0)
  have hc0 : 0 < ‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e) :=
    mul_pos (pow_pos hι0 _) (Real.rpow_pos_of_pos hp0 _)
  have hterm : ∀ k, ‖(T k).val A ι‖ ≤ (‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e))⁻¹ := by
    intro k
    have h := term_bound hJ A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE hp2 hpd hϖ hϖϖ (hT k)
    rw [mul_assoc] at h
    have h2 := (le_div_iff₀ hc0).mpr h
    rwa [one_div] at h2
  have hsum := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (inv_nonneg.mpr hc0.le) (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [mul_assoc]
  calc ‖∑ k, (T k).val A ι‖ * (‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e))
      ≤ (‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e))⁻¹ *
          (‖ι (conj ϖ)‖ ^ D * ‖(p : ℂ_[p])‖ ^ (((Fintype.card X.Tau * b * a : ℕ) : ℝ) - e)) :=
        mul_le_mul_of_nonneg_right hsum hc0.le
    _ = 1 := inv_mul_cancel₀ hc0.ne'

end Terms

section Place

variable {X : Fields}

def EntryG (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0) (ϖ : ℂ) (pE : 𝓞 X.E)
    {Bs : DefBase X.K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 X.K) (Fin (Dc.a u) → X.K))
    (w : HeightOneSpectrum (𝓞 X.K)) (g : ℕ) [Fact g.Prime] (Dg : Bs.J → ℕ) (ab : Bs.J → ℕ × ℕ) (e : Bs.J → ℝ) : Prop :=
  ∃ (ι : ℂ ≃+* ℂ_[g]) (Y : PathData X.K g Bs.J (Fin (Dc.a u) → X.K) (Fin (Df.nV t) → X.K)) (D : ℕ) (j1 : Bs.J),
    EmbAt w g ((ι : ℂ →+* ℂ_[g]).comp A.σ₀) ∧
    IsExpansion Y ((ι : ℂ →+* ℂ_[g]).comp A.σ₀) (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → X.K)) (Df.Mt t : Set (Fin (Df.nV t) → X.K)) ∧
    ColsInt Y w (Nu : Set (Fin (Dc.a u) → X.K)) ∧ RowsInt Y w (Df.Mt t : Set (Fin (Df.nV t) → X.K)) ∧
    LastInt Y ∧ UnitsInt Y ∧ StabDvd Y D j1 ∧ ¬ g ∣ D ∧
    ∀ π j, IsEntryG A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE (Dg j) (e j) (ab j).1 (ab j).2 (Y.e π j)

theorem gAt_of_entryG (hJ : JetAtSplit) (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0)
    (ϖ : ℂ) (pE : 𝓞 X.E) {Bs : DefBase X.K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem) (t : Bs.Tup)
    (Nu : Submodule (𝓞 X.K) (Fin (Dc.a u) → X.K)) (w : HeightOneSpectrum (𝓞 X.K)) (g : ℕ) [Fact g.Prime]
    (Dg : Bs.J → ℕ) (ab : Bs.J → ℕ × ℕ) (e : Bs.J → ℝ)
    (hg2 : g ≠ 2) (hgd : ¬ g ∣ A.d) (hϖ : IsQInt A.d ϖ) (hϖϖ : ϖ * conj ϖ = (g : ℂ)) (pb : X.K) (hpb : A.σ₀ pb = conj ϖ)
    (h : EntryG A a₀ b₀ c₀ ha hd lam hlam ϖ pE Dc u t Nu w g Dg ab e) :
    GAt Dc u t Nu w g pb Dg (fun j => ((Fintype.card X.Tau * (ab j).2 * (ab j).1 : ℕ) : ℝ) - e j) := by
  obtain ⟨ι, Y, D, j1, hι, hY, hc, hr, hl, hu, hD, hgD, he⟩ := h
  refine ⟨(ι : ℂ →+* ℂ_[g]).comp A.σ₀, Y, D, j1, hι, hY, hc, hr, hl, hu, hD, hgD, fun π j => ?_⟩
  have hb := entry_bound hJ A a₀ b₀ c₀ ha hd lam hlam ι ϖ pE hg2 hgd hϖ hϖϖ (he π j)
  have hpi : ((ι : ℂ →+* ℂ_[g]).comp A.σ₀) pb = ι (conj ϖ) := by
    rw [RingHom.comp_apply, hpb]
    rfl
  rw [hpi]
  exact hb

theorem perBd_of_entryG (hJ : JetAtSplit) (A : Amb X) (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam : ℂ) (hlam : lam ≠ 0)
    (ϖ : ℂ) (pE : 𝓞 X.E) {Bs : DefBase X.K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem) (t : Bs.Tup)
    (Nu : Submodule (𝓞 X.K) (Fin (Dc.a u) → X.K)) (w : HeightOneSpectrum (𝓞 X.K)) (g : ℕ) [Fact g.Prime]
    (Dg : Bs.J → ℕ) (ab : Bs.J → ℕ × ℕ) (e : Bs.J → ℝ)
    (hg2 : g ≠ 2) (hgd : ¬ g ∣ A.d) (hϖ : IsQInt A.d ϖ) (hϖϖ : ϖ * conj ϖ = (g : ℂ)) (pb : X.K) (hpb : A.σ₀ pb = conj ϖ)
    (hw : PlOver g w) (h : EntryG A a₀ b₀ c₀ ha hd lam hlam ϖ pE Dc u t Nu w g Dg ab e)
    {Jx : Type} (sx : Finset Jx) (Dx : Jx → ℕ) (cg : X.K) (E0 : ℝ) (hcg : ∃ k : ℕ, 0 < k ∧ cg ^ k = 1)
    (hD : ∑ j, (Dg j : ℝ) = ∑ l ∈ sx, (Dx l : ℝ))
    (hR : ∑ j, (((Fintype.card X.Tau * (ab j).2 * (ab j).1 : ℕ) : ℝ) - e j) ≤ E0) :
    PerBd Dc u Nu t w (colRhs sx g (fun l => pb ^ Dx l) cg E0 w) := by
  have hpb0 : pb ≠ 0 := by
    intro h0
    have h1 : conj ϖ = 0 := by rw [← hpb, h0, map_zero]
    have h2 : (g : ℂ) = 0 := by rw [← hϖϖ, h1, mul_zero]
    exact (Fact.out : g.Prime).ne_zero (by exact_mod_cast h2)
  have hG := gAt_of_entryG hJ A a₀ b₀ c₀ ha hd lam hlam ϖ pE Dc u t Nu w g Dg ab e hg2 hgd hϖ hϖϖ pb hpb h
  have hB := (Formalism.L2.AlgTh.column_bound_of_paths X.K Bs Df Dc u t Nu w g pb Dg
    (fun j => ((Fintype.card X.Tau * (ab j).2 * (ab j).1 : ℕ) : ℝ) - e j) hw hpb0 hG).2
  refine hB Jx sx (fun l => pb ^ Dx l) cg E0 ?_
  have hle := Formalism.L2.AlgTh.column_right_side_le X.K w g hw Bs.J pb cg Dg
    (fun j => ((Fintype.card X.Tau * (ab j).2 * (ab j).1 : ℕ) : ℝ) - e j) E0 hpb0 hcg hR
  refine le_trans (le_of_eq ?_) hle
  unfold colRhs
  simp only [Formalism.AtG.PlacesLyingOver.vw_pow' w pb hpb0]
  push_cast
  simp only [← Finset.sum_mul]
  rw [hD]

end Place

section Record

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Indef

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

def EntryGRec (hX : X.Ok) {Bs : DefBase X.K} (Df : DefSide Bs) {P : LevFam X.E X.K Rk.r Pr.vGs}
    (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m} (mu : Bs.Tup → Tup X.F X.E X.K Sg)
    (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K)))
    (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word)
    (b : ∀ t, Mem → (L t).β (m2 + 1)) (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < Am.d) (lam : ℂ) (hlam : lam ≠ 0) (ϖ : ℂ) (pE : 𝓞 X.E)
    (u : Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd u)) → X.K)) (w : HeightOneSpectrum (𝓞 X.K))
    (g : ℕ) [Fact g.Prime] (Dg : Bs.J → ℕ) (ab : Bs.J → ℕ × ℕ) (e : Bs.J → ℝ) : Prop :=
  EntryG Am a₀ b₀ c₀ ha hd lam hlam ϖ pE (colFace hX Df Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF ev) u t Nu w g
    Dg ab e

theorem val2AtG_concrete (hJ : JetAtSplit) (hX : X.Ok) {Bs : DefBase X.K} {Df0 Df1 : DefSide Bs} {P : LevFam X.E X.K Rk.r Pr.vGs}
    (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m} (mu : Bs.Tup → Tup X.F X.E X.K Sg)
    (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K)))
    (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word)
    (b : ∀ t, Mem → (L t).β (m2 + 1)) (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (ev : ∀ t, (Fin (Df1.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : SPer (colFace hX Df1 Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF ev)) (Nn : IndefNum Bs)
    (Pk : IndefCore Df0 Df1 (colFace hX Df1 Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF ev) Sp Nn)
    (u : Mem) (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd u)) → X.K))
    (N : Formalism.L2.DIV.NumDatum) (Lv : Formalism.L2.GlobalTheoryTheory.Arith.Lev N) (sd : X.K) (Dx : ℕ → ℕ) (cg : Fin 2 → X.K) (Cc : ℝ)
    (hcg : ∀ i, ∃ n : ℕ, 0 < n ∧ cg i ^ n = 1)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < Am.d) (lam : ℂ) (hlam : lam ≠ 0)
    (ϖ : Fin 2 → ℂ) (pE : Fin 2 → 𝓞 X.E) (hg : ∀ i, (N.g i).Prime) (hg2 : ∀ i, N.g i ≠ 2) (hgd : ∀ i, ¬ N.g i ∣ Am.d)
    (hϖ : ∀ i, IsQInt Am.d (ϖ i)) (hϖϖ : ∀ i, ϖ i * conj (ϖ i) = (N.g i : ℂ))
    (hpb : ∀ i, Am.σ₀ (Formalism.L2.GlobalTheoryTheory.Arith.eltBar sd (Lv.piG i)) = conj (ϖ i))
    (Dg : Bs.J → ℕ) (ab : Bs.J → ℕ × ℕ) (e : Fin 2 → Bs.J → ℝ)
    (hD : ∑ j, (Dg j : ℝ) = ∑ l ∈ N.lifts, (Dx l : ℝ))
    (hR : ∀ i, ∑ j, (((Fintype.card X.Tau * (ab j).2 * (ab j).1 : ℕ) : ℝ) - e i j) ≤
      Cc * (N.R.f : ℝ) * (N.R.m : ℝ) * (N.Nm : ℝ) * ((N.Nm : ℝ) + (N.R.t : ℝ)))
    (hE : ∀ (i : Fin 2) [Fact (N.g i).Prime] (w : HeightOneSpectrum (𝓞 X.K)), PlOver (N.g i) w →
      EntryGRec (W := W) (Ch := Ch) hX Df1 Xg mu cst L hL hP Mem wd b hY Am hK hF ev a₀ b₀ c₀ ha hd lam hlam (ϖ i) (pE i) u
        (Pk.cols.μ w) Nu w (N.g i) Dg ab (e i)) :
    ∀ i w, PlOver (N.g i) w →
      PerBd (colFace hX Df1 Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF ev) u Nu (Pk.cols.μ w) w
        (colRhs N.lifts (N.g i) (fun j => Formalism.L2.GlobalTheoryTheory.Arith.eltBar sd (Lv.piG i) ^ Dx j) (cg i)
          (Cc * (N.R.f : ℝ) * (N.R.m : ℝ) * (N.Nm : ℝ) * ((N.Nm : ℝ) + (N.R.t : ℝ))) w) := by
  intro i w hw
  have : Fact (N.g i).Prime := ⟨hg i⟩
  exact perBd_of_entryG hJ Am a₀ b₀ c₀ ha hd lam hlam (ϖ i) (pE i)
    (colFace hX Df1 Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF ev) u (Pk.cols.μ w) Nu w (N.g i) Dg ab (e i)
    (hg2 i) (hgd i) (hϖ i) (hϖϖ i) _ (hpb i) hw (hE i w hw) N.lifts Dx (cg i) _ (hcg i) hD (hR i)

theorem sumDeg_of_eJ (N : Formalism.L2.DIV.NumDatum) (Dx : ℕ → ℕ) {J : Type} [Fintype J] (eJ : J ≃ Fin N.R.m) :
    ∑ j, ((Dx ((eJ j).1 + 1) : ℕ) : ℝ) = ∑ l ∈ N.lifts, (Dx l : ℝ) :=
  Formalism.L2.DIV.NumDatum.sum_lifts N (fun l => (Dx l : ℝ)) eJ

end Record

end Formalism.L2.AtG.EntryG
