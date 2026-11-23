import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
import Development.WeilBound.CoreStatements.HodgeTatePoints.Invres
import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv

noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
variable {N Q : Type} [AddCommGroup N] [AddCommGroup Q] [Module F N] [Module F Q]

lemma stepOrder_eq (M : Submodule R (N → C)) (ψ : N →ₗ[F] Q) (hψ : Function.Surjective ψ)
    (t : N) :
    stepOrder M (LinearMap.ker ψ) t = (M.comap (LinearMap.funLeft R C ψ)).map
      (LinearMap.funLeft R C (LinearMap.toSpanSingleton F Q (ψ t))) := by
  rw [stepOrder, invFun_eq M ψ.toAddMonoidHom hψ _ (fun x => by simp), ← Submodule.map_comp]
  congr 1
  ext g a
  simp [LinearMap.funLeft]

lemma span_inj {t : Q} (ht : t ≠ 0) :
    Function.Injective (LinearMap.toSpanSingleton F Q t) := by
  intro a b h
  exact smul_left_injective F ht (by simpa using h)

lemma flagSub_succ {n : ℕ} (b : Module.Basis (Fin n) F N) (i : Fin n) :
    flagSub b ((i : ℕ) + 1) = Submodule.span F {b i} ⊔ flagSub b i := by
  have hs : {j : Fin n | (j : ℕ) < (i : ℕ) + 1} = insert i {j : Fin n | (j : ℕ) < (i : ℕ)} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagSub
  rw [hs, Set.image_insert_eq, Submodule.span_insert]

lemma notMem_flagSub {n : ℕ} (b : Module.Basis (Fin n) F N) (i : Fin n) :
    b i ∉ flagSub b i :=
  b.linearIndependent.notMem_span_image (by simp)

variable {v : Valuation C NNReal}

lemma colen_trivial [IsAlgClosed C] [CharZero C] (hv : v.Integers R) {T : Type} [AddCommGroup T]
    [Fintype T] [DecidableEq T] [Subsingleton T] (A : HopfOrder (C := C) R T) (c : NNReal)
    (hc : HasColen R v A.carrier c) : c = 1 := by
  obtain ⟨B, hB, rfl⟩ := hc
  rw [Matrix.det_eq_elem_of_subsingleton B 0]
  have hr : Set.range (fun (j x : T) => B x j) = {fun x => B x 0} := by
    ext g
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      rw [Subsingleton.elim j 0]
    · rintro rfl
      exact ⟨0, rfl⟩
  have h1 : (1 : T → C) ∈ Submodule.span R {fun x => B x 0} := by
    rw [← hr, ← hB]
    exact A.one_mem
  have hmem : (fun x => B x 0) ∈ A.carrier := by
    rw [hB, hr]
    exact Submodule.mem_span_singleton_self _
  rw [Submodule.mem_span_singleton] at h1
  obtain ⟨r, hr1⟩ := h1
  obtain ⟨s, hs⟩ := A.le_int hmem 0
  have e1 := congrFun hr1 0
  simp only [Pi.smul_apply, Pi.one_apply, Algebra.smul_def] at e1
  have e2 := congrArg v e1
  rw [map_mul, map_one] at e2
  have hr' := hv.map_le_one r
  have hs' : v (B 0 0) ≤ 1 := by
    have h3 : (algebraMap R C) s = B 0 0 := hs
    rw [← h3]
    exact hv.map_le_one s
  refine le_antisymm hs' ?_
  by_contra hlt
  push_neg at hlt
  have h0 : (0 : NNReal) ≤ v (B 0 0) := by positivity
  have := mul_lt_one_of_nonneg_of_lt_one_right hr' h0 hlt
  rw [e2] at this
  exact lt_irrefl _ this

lemma flag_ind [IsAlgClosed C] [CharZero C] (hv : v.Integers R) [Fintype F] [DecidableEq F]
    [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N) {n : ℕ}
    (b : Module.Basis (Fin n) F N) (cs : Fin n → NNReal)
    (hcs : ∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) :
    ∀ (d i : ℕ), i + d = n → ∀ (Q : Type) [AddCommGroup Q] [Module F Q] [Fintype Q]
      [DecidableEq Q] (ψ : N →ₗ[F] Q), Function.Surjective ψ → LinearMap.ker ψ = flagSub b i →
      ∀ c, HasColen R v (AA.carrier.comap (LinearMap.funLeft R C ψ)) c →
        c ^ Fintype.card F =
          (∏ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ)), cs j) ^ Fintype.card Q := by
  classical
  intro d
  induction d with
  | zero =>
    intro i hi Q _ _ _ _ ψ hψ hker c hc
    rw [Nat.add_zero] at hi
    have htop : LinearMap.ker ψ = ⊤ := by
      rw [hker, hi]
      unfold flagSub
      have hu : {j : Fin n | (j : ℕ) < n} = Set.univ := by
        ext j
        simp [j.isLt]
      rw [hu, Set.image_univ, b.span_eq]
    haveI : Subsingleton Q := by
      constructor
      intro x y
      obtain ⟨x', rfl⟩ := hψ x
      obtain ⟨y', rfl⟩ := hψ y
      have hx : x' ∈ LinearMap.ker ψ := by
        rw [htop]
        trivial
      have hy : y' ∈ LinearMap.ker ψ := by
        rw [htop]
        trivial
      rw [LinearMap.mem_ker] at hx hy
      rw [hx, hy]
    obtain ⟨AQ, hAQ⟩ := exists_quo hv AA ψ.toAddMonoidHom hψ
    have hc1 : c = 1 := colen_trivial hv AQ c (by rw [hAQ]; exact hc)
    have he : Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ)) = ∅ := by
      ext j
      have := j.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [hc1, he, Finset.prod_empty, one_pow, one_pow]
  | succ d ih =>
    intro i hi Q _ _ _ _ ψ hψ hker c hc
    have hin : i < n := by omega
    let ii : Fin n := ⟨i, hin⟩
    have hii : (ii : ℕ) = i := rfl
    have hbi : ψ (b ii) ≠ 0 := by
      intro h0
      apply notMem_flagSub b ii
      rw [hii, ← hker]
      exact h0
    let L : Submodule F Q := Submodule.span F {ψ (b ii)}
    haveI : Fintype (Q ⧸ L) := Fintype.ofFinite _
    let ψ' : N →ₗ[F] Q ⧸ L := L.mkQ.comp ψ
    have hψ' : Function.Surjective ψ' := L.mkQ_surjective.comp hψ
    have hker' : LinearMap.ker ψ' = flagSub b (i + 1) := by
      rw [LinearMap.ker_comp, L.ker_mkQ]
      have hL : L = Submodule.map ψ (Submodule.span F {b ii}) := by
        rw [Submodule.map_span, Set.image_singleton]
      rw [hL, Submodule.comap_map_eq, hker, ← hii, flagSub_succ b ii]
    obtain ⟨AQ, hAQ⟩ := exists_quo hv AA ψ.toAddMonoidHom hψ
    obtain ⟨AQ', hAQ'⟩ := exists_quo hv AA ψ'.toAddMonoidHom hψ'
    obtain ⟨cQ, hcQ⟩ := ReciprocityTheory.PGsh.Up.hasColen_of_lat v AQ'.lat
    rw [hAQ'] at hcQ
    have ih' := ih (i + 1) (by omega) (Q ⧸ L) ψ' hψ' hker' cQ hcQ
    have hst : stepOrder AA.carrier (flagSub b i) (b ii) = (AA.carrier.comap
        (LinearMap.funLeft R C ψ)).map
        (LinearMap.funLeft R C (LinearMap.toSpanSingleton F Q (ψ (b ii)))) := by
      rw [← hker]
      exact stepOrder_eq AA.carrier ψ hψ (b ii)
    have h3 : HasColen R v (stepOrder AA.carrier (flagSub b i) (b ii)) (cs ii) := hcs ii
    rw [hst] at h3
    have hrange : (LinearMap.toSpanSingleton F Q (ψ (b ii))).toAddMonoidHom.range =
        (L.mkQ.toAddMonoidHom).ker := by
      ext x
      simp [L, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    have hses := colen_ses hv AQ (LinearMap.toSpanSingleton F Q (ψ (b ii))).toAddMonoidHom
      (span_inj hbi) L.mkQ.toAddMonoidHom L.mkQ_surjective hrange c cQ (cs ii)
      (by rw [hAQ]; exact hc)
      (by
        have hcm : Submodule.comap (LinearMap.funLeft R C ⇑L.mkQ.toAddMonoidHom) AQ.carrier =
            Submodule.comap (LinearMap.funLeft R C ⇑ψ') AA.carrier := by
          rw [hAQ]
          ext h
          rfl
        rw [hcm]
        exact hcQ)
      (by rw [hAQ]; exact h3)
    have hcard : Fintype.card Q = Fintype.card (Q ⧸ L) * Fintype.card F := by
      have h1 := Submodule.card_eq_card_quotient_mul_card L
      have h2 : Nat.card L = Nat.card F :=
        Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton F Q _ hbi).toEquiv.symm
      rw [h2] at h1
      simp only [Nat.card_eq_fintype_card] at h1
      rw [h1, mul_comm]
    have hprod : ∏ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ)), cs j =
        cs ii * ∏ j ∈ Finset.univ.filter (fun j : Fin n => i + 1 ≤ (j : ℕ)), cs j := by
      have hs : Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ)) =
          insert ii (Finset.univ.filter (fun j : Fin n => i + 1 ≤ (j : ℕ))) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, hii]
        omega
      rw [hs, Finset.prod_insert]
      simp [hii]
    rw [hses, hprod, hcard, ih']
    ring

end Gen

theorem step : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → (∃ S : HopfOrder (C := C) R F, S.carrier = stepOrder AA.carrier K t ∧ FStable F S.carrier) ∧ stepOrder AA.carrier K t = stepOrderRes AA.carrier K t := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hf N _ _ _ _ AA hst K t ht
  classical
  haveI : Fintype (N ⧸ K) := Fintype.ofFinite _
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  have hne : K.mkQ t ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using ht
  have heq := stepOrder_eq AA.carrier K.mkQ hsurj t
  rw [K.ker_mkQ] at heq
  obtain ⟨AQ, hAQ⟩ := exists_quo hv AA K.mkQ.toAddMonoidHom hsurj
  obtain ⟨S, hS⟩ := exists_res hv AQ
    (LinearMap.toSpanSingleton F (N ⧸ K) (K.mkQ t)).toAddMonoidHom (span_inj hne)
  refine ⟨⟨S, ?_, ?_⟩, ?_⟩
  · rw [hS, hAQ, heq]
    rfl
  · rw [hS, hAQ]
    exact fstable_map _ (fstable_comap _ hst K.mkQ) _
  · unfold stepOrder stepOrderRes
    ext h
    constructor
    · intro hh
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hh
      exact ⟨g, hg.1, fun a k hk => hg.2 _ _ hk⟩
    · rintro ⟨g, hg, hgh⟩
      obtain ⟨g', hg', hg'e⟩ := invres p C v R hv hp N AA K.toAddSubgroup
        (Submodule.span F {t} ⊔ K).toAddSubgroup
        (by
          intro x hx
          exact Submodule.mem_sup_right hx) g hg
        (by
          intro x hx k hk
          obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
          rw [add_assoc, hgh a _ (K.add_mem hz hk), hgh a z hz])
      refine Submodule.mem_map.mpr ⟨g', hg', ?_⟩
      funext a
      show g' (a • t) = h a
      rw [hg'e (a • t) (Submodule.mem_sup_left (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩))]
      simpa using hgh a 0 K.zero_mem

theorem flag_colen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (cs : Fin n → NNReal) (cN : NNReal), (∀ i : Fin n, HasColen R v (stepOrder AA.carrier (flagSub b i) (b i)) (cs i)) → HasColen R v AA.carrier cN → cN ^ (p ^ f) = (∏ i, cs i) ^ Fintype.card N := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hf N _ _ _ _ AA hst n b cs cN hcs hN
  have h0 : LinearMap.ker (LinearMap.id : N →ₗ[F] N) = flagSub b 0 := by
    rw [LinearMap.ker_id]
    unfold flagSub
    simp
  have hid : HasColen R v
      (AA.carrier.comap (LinearMap.funLeft R C (LinearMap.id : N →ₗ[F] N))) cN := by
    have he : AA.carrier.comap (LinearMap.funLeft R C (LinearMap.id : N →ₗ[F] N)) = AA.carrier := by
      ext h
      rfl
    rw [he]
    exact hN
  have key := flag_ind hv AA b cs hcs n 0 (by omega) N LinearMap.id (fun x => ⟨x, rfl⟩) h0 cN hid
  have hu : Finset.univ.filter (fun j : Fin n => 0 ≤ (j : ℕ)) = Finset.univ := by
    ext j
    simp
  rw [hu] at key
  rw [← hf]
  exact key

end PositivityTheory.HtPt.Rc
