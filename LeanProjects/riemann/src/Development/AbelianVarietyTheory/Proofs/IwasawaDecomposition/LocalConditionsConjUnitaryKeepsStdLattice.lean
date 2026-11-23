import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedInvMulLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_val_le {P : HeightOneSpectrum (𝓞 E)} {a : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) : Valued.v a ≤ 1 := by
  obtain ⟨r, -, hr⟩ := h
  rw [← sub_add_cancel a (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r))]
  exact (Valuation.map_add _ _ _).trans (max_le hr.le (GlobalTheory.Mem.Dil.val_le_one P r))

theorem hasRes_add {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c d : 𝓞 E ⧸ P.asIdeal}
    (ha : HasRes P a c) (hb : HasRes P b d) : HasRes P (a + b) (c + d) := by
  obtain ⟨r, rfl, hr⟩ := ha
  obtain ⟨s, rfl, hs⟩ := hb
  refine ⟨r + s, map_add _ _ _, ?_⟩
  have e : a + b - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r + s)) =
      (a - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) +
        (b - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) := by
    rw [map_add, map_add]; ring
  rw [e]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt hr hs)

theorem hasRes_mul {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c d : 𝓞 E ⧸ P.asIdeal}
    (ha : HasRes P a c) (hb : HasRes P b d) : HasRes P (a * b) (c * d) := by
  have hb1 := hasRes_val_le hb
  obtain ⟨r, rfl, hr⟩ := ha
  obtain ⟨s, rfl, hs⟩ := hb
  refine ⟨r * s, map_mul _ _ _, ?_⟩

  have e : a * b - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r * s)) =
      (a - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) * b +
        algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) *
          (b - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_mul]
    exact (mul_le_of_le_one_right' hb1).trans_lt hr
  · rw [Valuation.map_mul]
    exact (mul_le_of_le_one_left' (GlobalTheory.Mem.Dil.val_le_one P r)).trans_lt hs

theorem hasRes_zero (P : HeightOneSpectrum (𝓞 E)) : HasRes P (0 : P.adicCompletion E) 0 := ⟨0, map_zero _, by simp⟩

theorem hasRes_one (P : HeightOneSpectrum (𝓞 E)) : HasRes P (1 : P.adicCompletion E) 1 := ⟨1, map_one _, by simp⟩

theorem hasRes_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) {f : ι → P.adicCompletion E}
    {g : ι → 𝓞 E ⧸ P.asIdeal} (h : ∀ i ∈ s, HasRes P (f i) (g i)) : HasRes P (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasRes_zero P
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact hasRes_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem hasRes_matMul {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {A B : Matrix (Fin n) (Fin n) (AfE F E)}
    {a b : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)} (hA : ∀ i j, HasRes P (adAt F P (A i j)) (a i j))
    (hB : ∀ i j, HasRes P (adAt F P (B i j)) (b i j)) (i j : Fin n) :
    HasRes P (adAt F P ((A * B) i j)) ((a * b) i j) := by
  rw [Matrix.mul_apply, Matrix.mul_apply, map_sum]
  exact hasRes_sum Finset.univ fun k _ => by
    rw [map_mul]
    exact hasRes_mul (hA i k) (hB k j)

private theorem hasRes_unique {P : HeightOneSpectrum (𝓞 E)}
    {a : P.adicCompletion E} {c d : 𝓞 E ⧸ P.asIdeal} (hc : HasRes P a c) (hd : HasRes P a d) : c = d := by
  obtain ⟨r, rfl, hr⟩ := hc
  obtain ⟨s, rfl, hs⟩ := hd
  rw [Ideal.Quotient.eq]
  have key : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r - s))) < 1 := by
    have e : algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r - s)) =
        (a - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) -
          (a - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hs hr)
  by_contra hne
  rw [GlobalTheory.Mem.Dil.val_eq_one hne] at key
  exact lt_irrefl _ key

private theorem hasRes_inv_entry_of_le_one [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) (X : GL (Fin n) (𝓞 E ⧸ P.asIdeal))
    (ht : ∀ i j, HasRes P (adAt F P ((t : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ((X : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j))
    (hti : ∀ i j, Valued.v (adAt F P (((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1)
    (i j : Fin n) :
    HasRes P (adAt F P (((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j))
      (((X⁻¹ : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j) := by
  choose c hc using fun a b => GlobalTheory.Mem.Dil.exists_res P _ (hti a b)
  let Y : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal) := Matrix.of fun a b => Ideal.Quotient.mk P.asIdeal (c a b)
  have hY : ∀ a b, HasRes P (adAt F P (((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) a b)) (Y a b) :=
    fun a b => ⟨c a b, rfl, hc a b⟩

  have hXY : (X : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) * Y = 1 := by
    ext a b
    have h1 := hasRes_matMul ht hY a b
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at h1
    have h2 : HasRes P (adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) a b))
        ((1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) a b) := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]; exact hasRes_one P
      · rw [map_zero]; exact hasRes_zero P
    exact hasRes_unique h1 h2
  rw [Units.inv_eq_of_mul_eq_one_right hXY]
  exact hY i j

end Res

end GlobalTheory.Mem.Col2.TC.ChTw.Match

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_conj [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E))
    (g : Matrix (Fin n) (Fin n) (AfE F E)) (X : GL (Fin n) (𝓞 E ⧸ P.asIdeal))
    (R : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal))
    (ht : ∀ i j, HasRes P (adAt F P ((t : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ((X : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j))
    (hti : ∀ i j, Valued.v (adAt F P (((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1)
    (hg : ∀ i j, HasRes P (adAt F P (g i j)) (R i j)) (i j : Fin n) :
    HasRes P (adAt F P ((((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) * g *
      (t : Matrix (Fin n) (Fin n) (AfE F E))) i j)) ((((X⁻¹ : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) * R *
        (X : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal))) i j) := by
  have hti' := hasRes_inv_entry_of_le_one P t X ht hti
  exact hasRes_matMul (fun a b => hasRes_matMul hti' hg a b) ht i j

theorem adAt_conj_of_one {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E))
    (g : Matrix (Fin n) (Fin n) (AfE F E))
    (h1 : ∀ i j, adAt F P ((t : Matrix (Fin n) (Fin n) (AfE F E)) i j) = if i = j then 1 else 0)
    (h2 : ∀ i j, adAt F P (((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) = if i = j then 1 else 0)
    (i j : Fin n) :
    adAt F P ((((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) * g *
      (t : Matrix (Fin n) (Fin n) (AfE F E))) i j) = adAt F P (g i j) := by
  have ht1 : (t : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = 1 := by
    ext a b; rw [Matrix.map_apply, h1, Matrix.one_apply]
  have ht2 : ((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = 1 := by
    ext a b; rw [Matrix.map_apply, h2, Matrix.one_apply]
  change ((((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) * g *
    (t : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F P)) i j = (g.map (adAt F P)) i j
  rw [Matrix.map_mul, Matrix.map_mul, ht1, ht2, one_mul, mul_one]

theorem carries_mul' [StarRing E] {N : ℕ} {g h : GL (Fin N) (AfE F E)} {L : Submodule (𝓞 E) (Fin N → E)}
    (hg : Formalism.L2.Herm.Carries g L L) (hh : Formalism.L2.Herm.Carries h L L) : Formalism.L2.Herm.Carries (g * h) L L := by
  unfold Formalism.L2.Herm.Carries at *
  intro x
  rw [hg x, hh, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem carries_inv' [StarRing E] {N : ℕ} {g : GL (Fin N) (AfE F E)} {L : Submodule (𝓞 E) (Fin N → E)}
    (hg : Formalism.L2.Herm.Carries g L L) : Formalism.L2.Herm.Carries g⁻¹ L L := by
  unfold Formalism.L2.Herm.Carries at *
  intro x
  rw [inv_inv]
  have key := hg ((g : Matrix (Fin N) (Fin N) (AfE F E)) *ᵥ x)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at key
  exact key.symm

theorem carries_one' [StarRing E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.Herm.Carries (1 : GL (Fin N) (AfE F E)) L L := by
  unfold Formalism.L2.Herm.Carries
  intro x
  simp

end Conj

end GlobalTheory.Mem.Col2.TC.ChTw.Match

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

set_option maxHeartbeats 1000000 in

theorem conj_unitary_preserves_stdLat_of_ptOf : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (n : ℕ) (t s : GA B n)
    (x : ∀ w : (B.primes X).vGs, GL (Fin n) (𝓞 B.fields.E ⧸ w.1.asIdeal)) (h : GLG B.fields.E n (B.primes X).vGs),
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E n) →
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∈ v.asIdeal → bc (prV (E := B.host.E) v) t = 1) →
    (∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((t : Matrix (Fin n) (Fin n) _) r j)) ((x w).1 r j)) →
    (LocalCondMoveDecoratedLattice u n (t⁻¹ * s * t) h ↔ LocalCondMoveDecoratedLattice u n s (fun w => x w * h w * (x w)⁻¹)) := by
  intro B X I _hI _l u n t s x h hp hT hx
  obtain ⟨p, ⟨htU, htC, -, -, -⟩, hp2⟩ := hp
  rw [hp2] at htC
  have htiC := carries_inv' htC

  have hint : ∀ (w : HeightOneSpectrum (𝓞 B.host.E)) (i j : Fin n),
      Valued.v (adAt B.host.F w (((t⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) i j)) ≤ 1 := by
    intro w i j
    have key := GlobalTheory.Mem.Col2.Splice.valued_inv_mul_le (w := w) htC (carries_one' _) le_rfl i j
    rwa [mul_one] at key

  have hvT : ∀ (P : (B.primes X).vT u) (i j : Fin n),
      adAt B.host.F P.1 ((t : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) i j) = (if i = j then 1 else 0) ∧
      adAt B.host.F P.1 (((t⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) i j) = (if i = j then 1 else 0) := by
    intro P i j
    have hP : X.piT u ∈ P.1.asIdeal := by
      have h0 : P.1 ∈ divs (X.piT u) := P.2
      unfold divs at h0
      split_ifs at h0 with hf
      · exact (Set.Finite.mem_toFinset hf).mp h0
      · simp at h0
    have hcI : IsIntegral ℤ (B.host.conj (X.piT u : B.host.E)) :=
      (RingOfIntegers.isIntegral_coe (X.piT u)).map
        (RingHom.toIntAlgHom (B.host.conj : B.host.E →+* B.host.E))
    have hTc : ((B.T u : ℕ) : 𝓞 B.host.E) =
        X.piT u * ⟨B.host.conj (X.piT u : B.host.E), hcI⟩ := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      exact (X.piT_norm u).symm
    have hbc : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) t = 1 := by
      apply hT
      show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) ((B.T u : ℕ) : 𝓞 B.host.F) ∈ P.1.asIdeal
      rw [map_natCast, hTc]
      exact Ideal.mul_mem_right _ _ hP
    have hbc' : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) t⁻¹ = 1 := by
      rw [map_inv, hbc, inv_one]
    exact ⟨GlobalTheory.Mem.Dil.adAt_of_bc_eq_one t P.1 hbc i j, GlobalTheory.Mem.Dil.adAt_of_bc_eq_one t⁻¹ P.1 hbc' i j⟩
  have inv1 : ((t⁻¹ * s * t)⁻¹ : GA B n) = t⁻¹ * s⁻¹ * t := by group
  have inv2 : (s⁻¹ : GA B n) = (t⁻¹)⁻¹ * (t⁻¹ * s * t)⁻¹ * t⁻¹ := by group
  have e3 : ∀ (P : (B.primes X).vT u) (r j : Fin n),
      adAt B.host.F P.1 ((((t⁻¹ * s * t)⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r j) =
        adAt B.host.F P.1 (((s⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r j) := by
    intro P r j
    rw [inv1, Units.val_mul, Units.val_mul]
    exact adAt_conj_of_one P.1 t _ (fun a b => (hvT P a b).1) (fun a b => (hvT P a b).2) r j
  unfold LocalCondMoveDecoratedLattice
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  ·
    constructor
    · intro hm
      have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ htU hm) (Subgroup.inv_mem _ htU)
      convert key using 1
      group
    · intro hm
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htU) hm) htU
  ·
    constructor
    · intro hm
      have key := carries_mul' (carries_mul' htC hm) htiC
      convert key using 2
      group
    · intro hm
      exact carries_mul' (carries_mul' htiC hm) htC
  · refine forall_congr' fun P => forall_congr' fun r => forall_congr' fun j => ?_
    rw [e3]
  · dsimp only
    constructor
    · intro H w r j
      have key := hasRes_conj w.1 t⁻¹ (((t⁻¹ * s * t)⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) (x w)⁻¹
        ((h w : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) (hasRes_inv_entry_of_le_one w.1 t (x w) (hx w) (hint w.1))
        (fun a b => by rw [inv_inv]; exact hasRes_val_le (hx w a b)) (H w) r j
      have eL : (((t⁻¹)⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) *
          (((t⁻¹ * s * t)⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) * ((t⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) =
          ((s⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) := by
        rw [← Units.val_mul, ← Units.val_mul, ← inv2]
      have eR : ((((x w)⁻¹)⁻¹ : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) * ((h w : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) *
          (((x w)⁻¹ : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) = ((x w * h w * (x w)⁻¹ : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) := by
        rw [inv_inv, Units.val_mul, Units.val_mul]
      rw [eL, eR] at key
      exact key
    · intro H w r j
      have key := hasRes_conj w.1 t ((s⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) (x w)
        ((x w * h w * (x w)⁻¹ : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) (hx w) (hint w.1) (H w) r j
      have eL : ((t⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) * ((s⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) *
          (t : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) = (((t⁻¹ * s * t)⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) := by
        rw [inv1, Units.val_mul, Units.val_mul]
      have eR : (((x w)⁻¹ : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) * ((x w * h w * (x w)⁻¹ : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) *
          ((x w : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) = ((h w : GL (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 B.host.E ⧸ w.1.asIdeal)) := by
        rw [← Units.val_mul, ← Units.val_mul]
        congr 1
        group
      rw [eL, eR] at key
      exact key

end GlobalTheory.Mem.Col2.TC.ChTw.Match
