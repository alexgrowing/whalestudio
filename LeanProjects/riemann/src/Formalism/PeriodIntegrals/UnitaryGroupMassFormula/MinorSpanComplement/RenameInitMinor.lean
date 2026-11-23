import Mathlib
import Formalism.PeriodIntegrals.MinorSpanCompl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSpanComplement.ExistsCoeffNeZeroOfMemSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSpanComplement.ShapeColumnDegreeColumnSizes
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.MSC

def phi (N n : ℕ) : Fin N × Fin n → ℕ × Fin N := fun v => ((v.2 : ℕ), v.1)

theorem phi_inj (N n : ℕ) : Function.Injective (phi N n) := by
  rintro ⟨a, s⟩ ⟨a', s'⟩ h
  simp only [phi, Prod.mk.injEq] at h
  ext
  · exact congrArg Fin.val h.2
  · exact h.1

theorem rename_initMinor (R : Type) [CommRing R] (N n s : ℕ) (hs : s ≤ n) (I : Fin s ↪o Fin N) :
    rename (phi N n) (initMinor R (r := N) (n := n) (fun p => I p) hs) = PI.minorX R N s I := by
  unfold initMinor PI.minorX
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i k
  simp [phi, Matrix.transpose_apply, rename_X]

theorem map_bidet (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map (Int.castRingHom R) (bideterminant ℤ sz hsz I) = bideterminant R sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

def gen (R : Type) [CommRing R] (N : ℕ) (ν : YoungDiagram)
    (I : ∀ c : Fin (ν.rowLen 0), Fin (ν.colLen c) ↪o Fin N) :
    MvPolynomial (Fin N × Fin (ν.colLen 0)) R :=
  bideterminant R (sz0 ν) (hsz0 ν) fun c => I c

theorem nablaSpan_eq (R : Type) [CommRing R] (N : ℕ) (ν : YoungDiagram) :
    PI.nablaSpan R N ν = Submodule.map (rename (phi N (ν.colLen 0))).toLinearMap
      (Submodule.span R (Set.range (gen R N ν))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  unfold PI.nablaSpan
  congr 1
  congr 1
  funext I
  simp only [Function.comp_apply, AlgHom.toLinearMap_apply, gen, bideterminant, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  exact (rename_initMinor R N _ _ _ (I c)).symm

theorem span_map_le {σ : Type*} (R : Type) [CommRing R] {A B : Set (MvPolynomial σ ℤ)}
    (h : A ⊆ Submodule.span ℤ B) :
    Submodule.span R (MvPolynomial.map (Int.castRingHom R) '' A) ≤
      Submodule.span R (MvPolynomial.map (Int.castRingHom R) '' B) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have := h ha
  clear ha
  induction this using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul z x _ hx =>
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul R]
    exact Submodule.smul_mem _ _ hx

theorem minorSpanCompl : PI.MinorSpanCompl := by
  intro R _ N ν
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨⊤, ?_⟩
    have h0 : PI.nablaSpan R N ν = ⊥ :=
      eq_bot_iff.mpr fun x _ => (Submodule.mem_bot R).mpr (Subsingleton.elim x 0)
    rw [h0]
    exact isCompl_bot_top
  set n := ν.colLen 0
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis ℤ N n (nuR ν)

  have hZ : Submodule.span ℤ (Set.range (gen ℤ N ν)) = Submodule.span ℤ (Set.range b) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨I, rfl⟩
      rw [SetLike.mem_coe, hspan]
      have := bideterminantMem ℤ N n (ν.rowLen 0) (sz0 ν) (hsz0 ν) fun c => I c
      rwa [shapeColumnDegree_columnSizes] at this
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      obtain ⟨K, sz, hsz, I, hsh, hI, hbm⟩ := (hb m).2.2
      rw [SetLike.mem_coe, hbm]
      obtain ⟨J, hJ, heq⟩ := reorder ℤ ν N sz hsz I hI hsh
      rw [heq]
      exact Submodule.subset_span ⟨fun c => OrderEmbedding.ofStrictMono (J c) (hJ c), rfl⟩
  set c : ssIdx N n (nuR ν) → MvPolynomial (Fin N × Fin n) R :=
    fun m => MvPolynomial.map (Int.castRingHom R) (b m) with hcdef
  have hT : Submodule.span R (Set.range (gen R N ν)) = Submodule.span R (Set.range c) := by
    have e1 : Set.range (gen R N ν) = MvPolynomial.map (Int.castRingHom R) '' Set.range (gen ℤ N ν) := by
      rw [← Set.range_comp]
      congr 1
      funext I
      simp only [Function.comp_apply, gen]
      exact (map_bidet R _ _ _).symm
    have e2 : Set.range c = MvPolynomial.map (Int.castRingHom R) '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [e1, e2]
    apply le_antisymm
    · exact span_map_le R (by rw [← hZ]; exact Submodule.subset_span)
    · exact span_map_le R (by rw [hZ]; exact Submodule.subset_span)
  have hdl : ∀ m, (colLex N n).degree (c m) = m.1 ∧ (colLex N n).leadingCoeff (c m) = 1 := by
    intro m
    obtain ⟨K, sz, hsz, I, _, hI, hbm⟩ := (hb m).2.2
    have hR := column_lex_bideterminant R N n K sz hsz I hI
    have hZd := column_lex_bideterminant ℤ N n K sz hsz I hI
    have hdeg := (hb m).1
    rw [hbm] at hdeg
    simp only [hcdef, hbm, map_bidet]
    exact ⟨hR.1.trans (hZd.1.symm.trans hdeg), hR.2⟩
  have hinj : Function.Injective fun m => (colLex N n).degree (c m) := by
    intro m m' h
    apply Subtype.ext
    simpa [(hdl m).1, (hdl m').1] using h
  rw [nablaSpan_eq, hT]
  exact ⟨_, isCompl_map_rename (colLex N n) (phi_inj N n) c hinj fun m => (hdl m).2⟩

end PI.MSC
