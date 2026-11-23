import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcPrVEqOneOfAdAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Formalism.LocalToGlobal.Columns.HeckeEx
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.UnitaryLift

open GlobalTheory.Mem.Col2.PtExist

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

omit [StarRing E] in

theorem val_mulVec_le {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ i j, P.valuation E (A i j) ≤ 1) {v : Fin n → E} (hv : ∀ i, P.valuation E (v i) ≤ 1) (i : Fin n) :
    P.valuation E ((A *ᵥ v) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hA i j) (hv j)

def matE {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E)) : Matrix (Fin n) (Fin n) E := M.map (algebraMap (𝓞 E) E)

omit [StarRing E] in
theorem det_matE {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E)) : (matE M).det = algebraMap (𝓞 E) E M.det :=
  (RingHom.map_det _ _).symm

open Classical in

def frOf {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E)) : Sp E n ≃ₗ[E] Sp E n :=
  if h : IsUnit (matE M).det then (matE M).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ h) else LinearEquiv.refl E _

omit [StarRing E] in
theorem frOf_apply {n : ℕ} {M : Matrix (Fin n) (Fin n) (𝓞 E)} (h : IsUnit (matE M).det) (v : Sp E n) :
    frOf M v = matE M *ᵥ v := by
  classical
  rw [frOf, dif_pos h]
  rfl

omit [StarRing E] in
theorem mat_frOf {n : ℕ} {M : Matrix (Fin n) (Fin n) (𝓞 E)} (h : IsUnit (matE M).det) (i j : Fin n) :
    mat (frOf M) i j = algebraMap (𝓞 E) E (M i j) := by
  show frOf M (Pi.single j 1) i = _
  rw [frOf_apply h]
  simp [matE, Matrix.mulVec_single_one]

theorem isFr_frOf {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {M : Matrix (Fin n) (Fin n) (𝓞 E)} (hM : M.det ∉ P.asIdeal) :
    IsUnit (matE M).det ∧ CharValCompare.IsFr P (stdLat E n) (frOf M) := by
  have hv : P.valuation E (matE M).det = 1 := by
    rw [det_matE]
    exact (HeightOneSpectrum.valuation_of_algebraMap P _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hM)
  have h0 : (matE M).det ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
  have hu : IsUnit (matE M).det := isUnit_iff_ne_zero.2 h0
  have hent : ∀ i j, P.valuation E (matE M i j) ≤ 1 := fun i j => HeightOneSpectrum.valuation_le_one P (M i j)
  have hinv : ∀ i j, P.valuation E ((matE M)⁻¹ i j) ≤ 1 := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hv, inv_one, one_mul]
    have e : (matE M).adjugate = matE M.adjugate := (RingHom.map_adjugate _ _).symm
    rw [e]
    exact HeightOneSpectrum.valuation_le_one P _
  refine ⟨hu, fun v => ?_⟩
  show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) ↔ v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
  rw [mem_localization_standardLattice, mem_localization_standardLattice, frOf_apply hu]
  simp only [CharValCompare.intAt_iff]
  refine ⟨fun h i => ?_, fun h i => val_mulVec_le _ hent h i⟩
  have := val_mulVec_le _ hinv h i
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at this

theorem exists_lift (hc : CMData F E) (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E)))
    (hQ : ∀ P ∈ Q, conjPrime₂ P ∉ Q) (x : ∀ P : Q, GL (Fin n) (𝓞 E ⧸ P.1.asIdeal)) :
    ∃ t : GL (Fin n) (AfE F E), (∃ p : DecoF E n ∅ ∅ ∅, IsPtOf hc t p ∧ p.deco.1.N = stdLat E n) ∧
      (∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j,
        adAt F w ((t : Matrix (Fin n) (Fin n) (AfE F E)) i j) = if i = j then 1 else 0) ∧
      ∀ (P : Q) (r j : Fin n), HasRes P.1 (adAt F P.1 ((t : Matrix (Fin n) (Fin n) (AfE F E)) r j)) ((x P).1 r j) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, ⟨BasePoint.stdPt E 0, ⟨one_mem _, fun z => ?_, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim⟩, rfl⟩,
      fun _ _ _ i => i.elim0, fun _ r => r.elim0⟩
    rw [Subsingleton.elim z 0, Matrix.mulVec_zero]
    exact iff_of_true (zero_mem _) (zero_mem _)
  haveI : NeZero n := ⟨hn.ne'⟩
  let lift : ∀ P : HeightOneSpectrum (𝓞 E), 𝓞 E ⧸ P.asIdeal → 𝓞 E := fun P =>
    Function.surjInv (Ideal.Quotient.mk_surjective (I := P.asIdeal))
  have hlift : ∀ (P : HeightOneSpectrum (𝓞 E)) c, Ideal.Quotient.mk P.asIdeal (lift P c) = c := fun P c =>
    Function.surjInv_eq _ c
  let M : HeightOneSpectrum (𝓞 E) → Matrix (Fin n) (Fin n) (𝓞 E) := fun P =>
    if h : P ∈ Q then (x ⟨P, h⟩ : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)).map (lift P) else 1
  have hM : ∀ (P : Q) r j, M P.1 r j = lift P.1 ((x P).1 r j) := fun P r j => by
    simp only [M, dif_pos P.2]
    rfl
  have hdet : ∀ P ∈ Q, (M P).det ∉ P.asIdeal := by
    intro P hP hmem
    have h1 : (Ideal.Quotient.mk P.asIdeal) (M P).det = (x ⟨P, hP⟩ : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)).det := by
      rw [RingHom.map_det]
      congr 1
      ext r j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hM ⟨P, hP⟩ r j, hlift]
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem] at h1
    have hu : IsUnit (x ⟨P, hP⟩ : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)).det := Matrix.isUnits_det_units (x ⟨P, hP⟩)
    rw [← h1] at hu
    haveI : P.asIdeal.IsPrime := P.isPrime
    exact not_isUnit_zero hu
  have hfr : ∀ P ∈ Q, CharValCompare.IsFr P (Formalism.UG.CS.globLat (1 : GL (Fin n) (AfE F E)) (stdLat E n)) (frOf (M P)) := by
    intro P hP
    rw [globLat_one_std]
    exact (isFr_frOf (hdet P hP)).2
  obtain ⟨g, hg, c1, c2, c3⟩ := exists_modify (hc := hc) hQ (one_mem (UAd hc n)) (fun P => frOf (M P)) hfr
  rw [globLat_one_std] at c1
  refine ⟨g, ⟨BasePoint.stdPt E n, ⟨hg, c1, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim⟩, rfl⟩,
      fun w hw hw' i j => ?_, fun P r j => ?_⟩
  · have e1 : ∀ i j, adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        if i = j then 1 else 0 := by
      intro i j
      have h := c3 w hw hw' (Pi.single j 1) i
      have hv : (fun k => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j (1 : E) : Fin n → E) k)) =
          Pi.single j 1 := by
        ext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      have h' : adAt F w ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) =
          adAt F w ((((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) := by
        rw [← hv]; exact h
      rw [inv_one, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_single_one] at h'
      have h'' : adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
          adAt F w ((Pi.single j 1 : Fin n → AfE F E) i) := h'
      rw [h'', Pi.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hMi : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F w) = 1 := by
      ext a b
      rw [Matrix.map_apply, e1, Matrix.one_apply]
    have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)) * ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hMg : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
      have h := congrArg (fun M => M.map (adAt F w)) hgg
      simp only [Matrix.map_mul, hMi, mul_one] at h
      rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
    have h := congrFun (congrFun hMg i) j
    rw [Matrix.map_apply, Matrix.one_apply] at h
    exact h
  · rw [c2 P.1 P.2 r j, mat_frOf (isFr_frOf (hdet P.1 P.2)).1, ← hlift P.1 ((x P).1 r j), ← hM P r j]
    exact hasRes_coe _ _

end General

end GlobalTheory.Mem.Col2.TC.ChTw.Match.UnitaryLift

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.UnitaryLift

theorem false_of_primes_mem {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h1 : (p : A) ∈ I) (h2 : (q : A) ∈ I) : False := by
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)).map (Int.castRingHom A)
  have e1 : (Int.castRingHom A) (p : ℤ) = (p : A) := by simp
  have e2 : (Int.castRingHom A) (q : ℤ) = (q : A) := by simp
  rw [e1, e2] at hab
  apply hI
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

end GlobalTheory.Mem.Col2.TC.ChTw.Match.UnitaryLift

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

open UnitaryLift

theorem exists_unitary_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (n : ℕ)
    (x : ∀ w : (B.primes X).vGs, GL (Fin n) (𝓞 B.fields.E ⧸ w.1.asIdeal)), ∃ t : GA B n,
      (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
      (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
        bc (prV (E := B.host.E) v) t = 1) ∧
      ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((t : Matrix (Fin n) (Fin n) _) r j)) ((x w).1 r j) := by
  intro B X I _ l u n x
  classical
  have hPr := l.pr
  have hne : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have e := hPr.piG_norm i
    rw [h, mul_zero] at e
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast e.symm)
  have hvG : ∀ w : HeightOneSpectrum (𝓞 B.fields.E), w ∈ (B.primes X).vGs →
      ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := by
    intro w h
    rcases Finset.mem_union.1 h with h | h
    exacts [⟨0, (mem_divs (hne 0) w).1 h⟩, ⟨1, (mem_divs (hne 1) w).1 h⟩]
  have hgI : ∀ w : HeightOneSpectrum (𝓞 B.fields.E), w ∈ (B.primes X).vGs ∨ conjPrime₂ w ∈ (B.primes X).vGs →
      ∃ i, (((B.primes X).g i : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
    rintro w (h | h)
    · obtain ⟨i, hi⟩ := hvG w h
      exact ⟨i, by rw [← hPr.piG_norm i]; exact Ideal.mul_mem_left _ _ hi⟩
    · obtain ⟨i, hi⟩ := hvG _ h
      refine ⟨i, ?_⟩
      rw [← hPr.piG_norm i]
      apply Ideal.mul_mem_right
      have h2 := (mem_conjP w _).1 hi
      rwa [show cO B.fields.E (B.fields.conjO ((B.primes X).piG i)) = (B.primes X).piG i from cO_cO _] at h2
  have hgne : ∀ i i' : Fin 2, i ≠ i' → (B.primes X).g i ≠ (B.primes X).g i' := by
    intro i i' h
    fin_cases i <;> fin_cases i'
    · exact absurd rfl h
    · exact hPr.g_ne
    · exact fun e => hPr.g_ne e.symm
    · exact absurd rfl h
  have hQ : ∀ P ∈ (B.primes X).vGs, conjPrime₂ P ∉ (B.primes X).vGs := by
    intro P hP hP'
    obtain ⟨i, hi⟩ := hvG P hP
    obtain ⟨i', hi'⟩ := hvG _ hP'
    have hi'' := (mem_conjP P _).1 hi'
    rw [show cO B.fields.E (B.fields.conjO ((B.primes X).piG i')) = (B.primes X).piG i' from cO_cO _] at hi''
    by_cases e : i = i'
    · subst e
      obtain ⟨a, b, hab⟩ := hPr.piG_cop i
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hi'') (Ideal.mul_mem_left _ _ hi)
    · have h1 : (((B.primes X).g i : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i]; exact Ideal.mul_mem_left _ _ hi
      have h2 : (((B.primes X).g i' : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i']; exact Ideal.mul_mem_right _ _ hi''
      exact false_of_primes_mem P.isPrime.ne_top (hPr.g_prime i) (hPr.g_prime i') (hgne i i' e) h1 h2
  obtain ⟨t, hpt, hoff, hres⟩ := exists_lift (F := B.host.F) B.sp.cm n _ hQ x
  refine ⟨t, hpt, fun v hv => ?_, hres⟩
  refine GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt _ _ n v t fun w hw i j => ?_
  have hunder : ∀ m : ℕ, ((m : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal → ((m : ℕ) : 𝓞 B.host.F) ∈ v.asIdeal := by
    intro m hm
    rw [← hw]
    show ((m : ℕ) : 𝓞 B.host.F) ∈ w.asIdeal.under (𝓞 B.host.F)
    rwa [Ideal.under_def, Ideal.mem_comap, map_natCast]
  have hfree : w ∉ (B.primes X).vGs ∧ conjPrime₂ w ∉ (B.primes X).vGs := by
    by_contra hcon
    obtain ⟨k, hk⟩ := hgI w (by tauto)
    have hkv := hunder _ hk
    rcases hv with hv | hv
    · have hT : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ v.asIdeal := hv
      exact false_of_primes_mem v.isPrime.ne_top (hPr.T_prime u) (hPr.g_prime k) (hPr.T_ne_g u k) hT hkv
    · exact hv k hkv
  exact hoff w hfree.1 hfree.2 i j

end GlobalTheory.Mem.Col2.TC.ChTw.Match
