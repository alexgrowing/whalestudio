import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitaryExchangeUnimodularLatticesInerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertPathCardCommLatticePathsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

open Formalism.L2.Col Formalism.HermitianLatticesTheory

namespace GlobalTheory.InertSame

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem sameAt_trans {Q : HeightOneSpectrum (𝓞 E)} {A B C : Submodule (𝓞 E) (Sp E n)}
    (h1 : SameAt Q A B) (h2 : SameAt Q B C) : SameAt Q A C := by
  obtain ⟨a, ha, a', ha', h1, h1'⟩ := h1
  obtain ⟨b, hb, b', hb', h2, h2'⟩ := h2
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]; exact h1 _ (h2 x hx)
  · rw [mul_smul]; exact h2' _ (h1' x hx)

theorem sameAt_refl (Q : HeightOneSpectrum (𝓞 E)) (A : Submodule (𝓞 E) (Sp E n)) : SameAt Q A A :=
  ⟨1, fun h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), 1,
    fun h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem paths_equiv (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P) (hin : ∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal)
    (X Z : Submodule (𝓞 E) (Sp E n)) (hX : Submodule.IsLattice E X) (hZ : Submodule.IsLattice E Z)
    (hXu : IsUnimodular (hStd E n) X) (hZu : IsUnimodular (hStd E n) Z) (s t : List ℕ) :
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t X Y ∧ IsInertNbr P.asIdeal s Y Z}) := by
  by_cases hXZ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Z
  · obtain ⟨σ, hσX, hσZ, hgood, hsurj, hinj, hrel⟩ := GlobalTheory.T.exists_local_unitary_exchange_unimodular_lattices_inert P hP hin X Z hX hZ hXu hZu hXZ
    have gX : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X X := fun Q _ => sameAt_refl Q X
    have away : ∀ {u : List ℕ} {Y : Submodule (𝓞 E) (Sp E n)}, IsInertNbr P.asIdeal u X Y →
        ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y := fun h Q hQ => hi_sameAt_inert hQ h
    have fwd : ∀ Y : {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z},
        Submodule.IsLattice E (σ Y.1) ∧ IsUnimodular (hStd E n) (σ Y.1) ∧
          IsInertNbr P.asIdeal t X (σ Y.1) ∧ IsInertNbr P.asIdeal s (σ Y.1) Z := by
      rintro ⟨Y, hl, hu, h1, h2⟩
      obtain ⟨gl, gu, -⟩ := hgood Y hl hu (away h1)
      have r1 := (hrel s X Y hX hXu gX hl hu (away h1)).2 h1
      have r2 := (hrel t Y Z hl hu (away h1) hZ hZu hXZ).2 h2
      rw [hσX] at r1
      rw [hσZ] at r2
      exact ⟨gl, gu, r2.symm, r1.symm⟩
    refine ⟨Equiv.ofBijective (fun Y => ⟨σ Y.1, fwd Y⟩) ⟨?_, ?_⟩⟩
    · rintro ⟨Y, hl, hu, h1, h2⟩ ⟨Y', hl', hu', h1', h2'⟩ he
      have := congrArg Subtype.val he
      exact Subtype.ext (hinj Y Y' hl hu (away h1) hl' hu' (away h1') this)
    · rintro ⟨Y', hl', hu', h1', h2'⟩
      obtain ⟨Y, hl, hu, ha, rfl⟩ := hsurj Y' hl' hu' (away h1')
      refine ⟨⟨Y, hl, hu, ?_, ?_⟩, rfl⟩
      · refine (hrel s X Y hX hXu gX hl hu ha).1 ?_
        rw [hσX]
        exact h2'.symm
      · refine (hrel t Y Z hl hu ha hZ hZu hXZ).1 ?_
        rw [hσZ]
        exact h1'.symm
  · have e1 : IsEmpty {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s X Y ∧ IsInertNbr P.asIdeal t Y Z} :=
      ⟨fun Y => hXZ fun Q hQ => sameAt_trans (hi_sameAt_inert hQ Y.2.2.2.1) (hi_sameAt_inert hQ Y.2.2.2.2)⟩
    have e2 : IsEmpty {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t X Y ∧ IsInertNbr P.asIdeal s Y Z} :=
      ⟨fun Y => hXZ fun Q hQ => sameAt_trans (hi_sameAt_inert hQ Y.2.2.2.1) (hi_sameAt_inert hQ Y.2.2.2.2)⟩
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

section Ops
variable {K : Type} [Field K] [NumberField K] [StarRing K] {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

theorem heckeI_comm_same (c : DecoPts S E n ST SG) (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P)
    (hin : ∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) (hST : ∀ R : ST, R.1 ≠ P) (hSG : ∀ w : SG, w.1 ≠ P)
    (s t : List ℕ) : Commute (heckeI c P.asIdeal s).op (heckeI c P.asIdeal t).op := by
  classical
  refine hi_commute c _ _ _ _ (heckeI_op_apply' c _ s) (heckeI_op_apply' c _ t) fun d f => ?_
  exact GlobalTheory.T.inertPath_card_comm_latticePaths P hST hSG s t d f (paths_equiv P hP hin d.1.N f.1.N d.2.lat f.2.lat d.2.uni f.2.uni s t)

theorem heckeCommAll_all (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : HeckeCommAll c S0 :=
  heckeCommAll_of_same c S0 fun P s t => heckeI_comm_same c P.1 P.2.1 P.2.2.1
    (fun R => P.ne_of_mem (Or.inl (Or.inr R.2))) (fun w => P.ne_of_mem (Or.inr w.2)) s t
end Ops

end GlobalTheory.InertSame

namespace GlobalTheory.Mem.R3.Comm

theorem rows_lifts_comm : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → ∀ a : I.ι,
  Formalism.L2.Col.HeckeCommAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
    ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeCommAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ :=
  fun _ _ _ _ _ _ => ⟨GlobalTheory.InertSame.heckeCommAll_all _ _, fun _ => GlobalTheory.InertSame.heckeCommAll_all _ _⟩
end GlobalTheory.Mem.R3.Comm
