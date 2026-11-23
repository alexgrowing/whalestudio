import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTail
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

section general

variable {R : Type} [CommRing R] {O : Subring R} {n : ℕ}

theorem smul_mem_of_mem' (Λ : Submodule O (Fin n → R)) {c : R} (hc : c ∈ O) {x : Fin n → R}
    (hx : x ∈ Λ) : c • x ∈ Λ := by
  have := Λ.smul_mem (⟨c, hc⟩ : O) hx
  simpa [Subring.smul_def] using this

theorem exists_nat_smul_mem (Λ : Submodule O (Fin n → R))
    (hd : ∀ y : R, ∃ m : ℕ, m ≠ 0 ∧ (m : R) * y ∈ O) {x : Fin n → R}
    (hx : x ∈ Submodule.span R (Λ : Set (Fin n → R))) : ∃ m : ℕ, m ≠ 0 ∧ (m : R) • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatSmulMem.exists_nat_smul_mem ..)

theorem exists_nat_between (Λ : Submodule O (Fin n → R)) (hfg : Λ.FG)
    (hsp : Submodule.span R (Λ : Set (Fin n → R)) = ⊤)
    (hd : ∀ y : R, ∃ m : ℕ, m ≠ 0 ∧ (m : R) * y ∈ O) :
    ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → R, (∀ i, v i ∈ O) → (m : R) • v ∈ Λ) ∧
      ∀ v ∈ Λ, ∀ i, (m : R) * v i ∈ O := by
  choose md hmd0 hmd using hd
  obtain ⟨S, hS⟩ := hfg

  set m1 : ℕ := ∏ s ∈ S, ∏ i, md (s i) with hm1
  have hm10 : m1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun i _ => hmd0 _
  have hup : ∀ v ∈ Λ, ∀ i, (m1 : R) * v i ∈ O := by
    intro v hv
    rw [← hS] at hv
    induction hv using Submodule.span_induction with
    | mem s hs =>
      intro i
      have hdvd : md (s i) ∣ m1 :=
        (Finset.dvd_prod_of_mem (fun j => md (s j)) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun t : Fin n → R => ∏ j, md (t j)) hs)
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, Nat.cast_mul, mul_comm (md (s i) : R), mul_assoc]
      exact O.mul_mem (natCast_mem O k) (hmd _)
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; simpa [mul_add] using O.add_mem (hx i) (hy i)
    | smul a x _ hx =>
      intro i
      have : (m1 : R) * (a • x) i = (a : R) * ((m1 : R) * x i) := by
        simp [Subring.smul_def]; ring
      rw [this]
      exact O.mul_mem a.2 (hx i)

  have hsingle : ∀ i : Fin n, ∃ m : ℕ, m ≠ 0 ∧ (m : R) • (Pi.single i 1 : Fin n → R) ∈ Λ := fun i =>
    exists_nat_smul_mem Λ (fun y => ⟨md y, hmd0 y, hmd y⟩) (by rw [hsp]; exact Submodule.mem_top)
  choose ms hms0 hms using hsingle
  set m2 : ℕ := ∏ i, ms i with hm2
  have hm20 : m2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hms0 i
  have hsing2 : ∀ i, (m2 : R) • (Pi.single i 1 : Fin n → R) ∈ Λ := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem ms (Finset.mem_univ i)
    rw [← hm2] at hk
    rw [hk, Nat.cast_mul, mul_comm, ← smul_smul]
    exact smul_mem_of_mem' Λ (natCast_mem O k) (hms i)
  have hlow : ∀ v : Fin n → R, (∀ i, v i ∈ O) → (m2 : R) • v ∈ Λ := by
    intro v hv
    have h : (m2 : R) • v = ∑ i, v i • ((m2 : R) • (Pi.single i 1 : Fin n → R)) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [h]
    exact Λ.sum_mem fun i _ => smul_mem_of_mem' Λ (hv i) (hsing2 i)
  refine ⟨m1 * m2, mul_ne_zero hm10 hm20, fun v hv => ?_, fun v hv i => ?_⟩
  · have : ((m1 * m2 : ℕ) : R) • v = (m1 : R) • ((m2 : R) • v) := by push_cast; rw [smul_smul]
    rw [this]
    exact smul_mem_of_mem' Λ (natCast_mem O m1) (hlow v hv)
  · have : ((m1 * m2 : ℕ) : R) * v i = (m2 : R) * ((m1 : R) * v i) := by push_cast; ring
    rw [this]
    exact O.mul_mem (natCast_mem O m2) (hup v hv i)

end general

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem lat_between (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (Λ : Submodule (A.L p).O (Fin n → (A.loc p).Ep)) (hΛ : IsLat (A.L p) Λ)
    (hd : ∀ y : (A.loc p).Ep, ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O) :
    ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ) ∧
      ∀ v ∈ Λ, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O :=
  exists_nat_between Λ hΛ.1 hΛ.2 hd

end GlobalTheory.HL.Glue
