import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationPropertiesStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp

def IsI {K : Type} [Field K] [NumberField K] (x : K) : Prop :=
  ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x

section I

variable {K : Type} [Field K] [NumberField K]

theorem IsI.add {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x + y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o + p, by simp⟩

theorem IsI.neg {x : K} (hx : IsI x) : IsI (-x) := by
  obtain ⟨o, rfl⟩ := hx
  exact ⟨-o, by simp⟩

theorem IsI.sub {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem IsI.mul {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x * y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o * p, by simp⟩

theorem isI_zero : IsI (0 : K) := ⟨0, by simp⟩

theorem isI_sum {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, IsI (f i)) :
    IsI (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isI_zero : IsI (0 : K))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Kc_le_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc c ≤ Kc (c + h) := by
  intro y hy i
  have h1 : IsI ((c *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := hy i
  have h2 : IsI ((h *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := by
    show IsI (∑ j, h i j * algebraMap (𝓞 K) K (y j))
    exact isI_sum (K := K) Finset.univ _ fun j _ => (hh i j).mul ⟨y j, rfl⟩
  have h3 := h1.add h2
  rw [Matrix.add_mulVec]
  exact h3

theorem Kc_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc (c + h) = Kc c := by
  refine le_antisymm ?_ (Kc_le_add c h hh)
  have := Kc_le_add (c + h) (-h) fun a b => by simpa using IsI.neg (hh a b)
  simpa using this

theorem delta_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    delta (c + h) = delta c := by
  unfold delta
  rw [Kc_add c h hh]

theorem vec_out {m : ℕ} (t : Fin m → K) (i : Fin m) :
    IsI ((Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) : Fin m → K) i - t i) := by
  have h : Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m))
      = (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) := Quotient.out_eq _
  have h2 := (Submodule.Quotient.eq _).1 h
  exact h2 i

end I

section H

variable {F E : Type} [Field F] [Field E] [Algebra F E] [NumberField E]

theorem herm_out (σ : E →ₐ[F] E) {n : ℕ} (t : hermE σ n) (a b : Fin n) :
    IsI ((Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b) := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) :
      hermE σ n ⧸ hermO σ n) = QuotientAddGroup.mk t := Quotient.out_eq _
  have h2 : IsI ((-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b) :=
    (QuotientAddGroup.eq.1 h) a b
  have h3 := h2.neg
  have e : -(-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b =
      (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b := by
    simp
    ring
  rwa [e] at h3

def topB (σ : E →ₐ[F] E) {m : ℕ} (C : hermE σ (m + 1)) : hermE σ m :=
  ⟨fun a b => C.1 a.castSucc b.castSucc, fun a b => C.2 a.castSucc b.castSucc⟩

def lastCol {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : Fin m → E :=
  fun a => C a.castSucc (Fin.last m)

theorem blk_cc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a b : Fin m) : blk σ c u d a.castSucc b.castSucc = c a b := by simp [blk]

theorem blk_cl (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a : Fin m) : blk σ c u d a.castSucc (Fin.last m) = u a := by simp [blk]

theorem blk_lc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (b : Fin m) : blk σ c u d (Fin.last m) b.castSucc = σ (u b) := by simp [blk]

theorem blk_ll (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    blk σ c u d (Fin.last m) (Fin.last m) = d := by simp [blk]

theorem blk_sub_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (C : hermE σ (m + 1)) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (hc : ∀ a b : Fin m, IsI (c a b - C.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (u a - C.1 a.castSucc (Fin.last m)))
    (hd : IsI (d - C.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) :
    IsI (blk σ c u d i j - C.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_ll]; exact hd
    | cast b =>
      rw [blk_lc, ← C.2 (Fin.last m) b.castSucc, ← map_sub]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [blk_cl]; exact hu a
    | cast b => rw [blk_cc]; exact hc a b

theorem herm_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (D : hermE σ (m + 1))
    (hc : ∀ a b : Fin m, IsI (D.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (D.1 a.castSucc (Fin.last m)))
    (hd : IsI (D.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) : IsI (D.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact hd
    | cast b =>
      rw [← D.2 (Fin.last m) b.castSucc]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => exact hu a
    | cast b => exact hc a b

end H

theorem isI_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {y : F} (hy : IsI y) : IsI (algebraMap F E y) := by
  obtain ⟨o, rfl⟩ := hy
  have h : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F o)) :=
    (RingOfIntegers.isIntegral_coe o).algebraMap
  exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ h⟩

theorem hermClass_blocks : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ m : ℕ, ∃ ι : (hermE σ (m + 1) ⧸ hermO σ (m + 1)) → (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F, Function.Injective ι ∧ ∀ x, delta (Quotient.out x).1 = delta (blk σ (Quotient.out (ι x).1).1 (Quotient.out (ι x).2.1) (algebraMap F E ((Quotient.out (ι x).2.2 : Fin 1 → F) 0))) := by
  intro F E _ _ _ _ _ σ hcm m
  obtain ⟨-, hfix, hsO, -⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hcm
  have hσ : ∀ x : E, IsI x → IsI (σ x) := by
    rintro x ⟨o, rfl⟩
    exact ⟨sO σ o, hsO o⟩
  have hcorner : ∀ C : hermE σ (m + 1), ∃ y : F,
      algebraMap F E y = C.1 (Fin.last m) (Fin.last m) := fun C => hfix _ (C.2 _ _)
  choose dd hdd using hcorner
  refine ⟨fun x => (QuotientAddGroup.mk (topB σ (Quotient.out x)),
    Submodule.Quotient.mk (lastCol (Quotient.out x).1),
    Submodule.Quotient.mk (fun _ => dd (Quotient.out x))), ?_, ?_⟩
  · intro x x' hxx
    obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := by simpa [Prod.ext_iff] using hxx
    have h1' := QuotientAddGroup.eq.1 h1
    have h2' := (Submodule.Quotient.eq _).1 h2
    have h3' := (Submodule.Quotient.eq _).1 h3
    rw [← Quotient.out_eq x, ← Quotient.out_eq x']
    refine QuotientAddGroup.eq.2 ?_
    refine fun i j => herm_isI σ hσ (-(Quotient.out x) + Quotient.out x') ?_ ?_ ?_ i j
    · intro a b
      exact h1' a b
    · intro a
      have : IsI (lastCol (Quotient.out x).1 a - lastCol (Quotient.out x').1 a) := h2' a
      have e := this.neg
      simpa [lastCol, add_comm, sub_eq_add_neg] using e
    · have : IsI (dd (Quotient.out x) - dd (Quotient.out x')) := h3' 0
      have e := (isI_algebraMap (E := E) this).neg
      simpa [hdd, add_comm, sub_eq_add_neg] using e
  · intro x
    dsimp only
    set C := Quotient.out x with hC
    set M := blk σ (Quotient.out (QuotientAddGroup.mk (topB σ C) : hermE σ m ⧸ hermO σ m)).1
      (Quotient.out (Submodule.Quotient.mk (lastCol C.1) : (Fin m → E) ⧸ intVec E m))
      (algebraMap F E ((Quotient.out (Submodule.Quotient.mk (fun _ => dd C) : FQ F) : Fin 1 → F) 0))
      with hM
    have hI : ∀ i j, IsI ((M - C.1) i j) := by
      intro i j
      refine blk_sub_isI σ hσ C _ _ _ ?_ ?_ ?_ i j
      · intro a b
        exact herm_out σ (topB σ C) a b
      · intro a
        exact vec_out (lastCol C.1) a
      · have h := isI_algebraMap (E := E) (vec_out (fun _ : Fin 1 => dd C) 0)
        rw [map_sub, hdd] at h
        exact h
    have := delta_add C.1 (M - C.1) hI
    rw [add_sub_cancel] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp
