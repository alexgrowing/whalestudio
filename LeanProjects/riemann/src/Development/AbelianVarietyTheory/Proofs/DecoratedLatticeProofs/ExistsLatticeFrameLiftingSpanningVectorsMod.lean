import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftFrameMod

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_one_sub_smul (c : R) (X : Matrix (Fin n) (Fin n) R) :
    ∃ a : R, (1 - c • X).det = 1 - c * a := by
  have h : Ideal.Quotient.mk (Ideal.span {c}) (1 - c • X).det = 1 := by
    rw [RingHom.map_det]
    have : (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix (1 - c • X) = 1 := by
      ext i j
      simp [Matrix.one_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c)]
    rw [this, Matrix.det_one]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {c})), Ideal.Quotient.eq] at h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨-a, by linear_combination -ha⟩

theorem isUnit_mix {e g : R} (he : e * e = e) (hu : ∀ a : R, IsUnit (1 - e * g * a))
    (M C X : Matrix (Fin n) (Fin n) R) (h : M * C = 1 - g • X) :
    IsUnit (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) := by
  have h1 : (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (e • C + (1 - e) • 1) = 1 - (e * g) • X := by
    rw [GlobalTheory.IdemSupport.mix_mul he, h, Matrix.one_mul, smul_sub, smul_smul, sub_add_eq_add_sub,
      GlobalTheory.IdemSupport.mix_self]
  obtain ⟨a, ha⟩ := det_one_sub_smul (e * g) X
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, ha] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ hu a : IsUnit _)

theorem exists_lift {A : Type} [CommRing A] (S : Subring A) (g : ℕ) {e t : S} (he : e * e = e) (ht : 1 - e = g * t)
    (hu : ∀ a : S, IsUnit (1 - e * g * a)) (Λ : Submodule S (Fin n → A)) (β₀ : GL (Fin n) A)
    (hβ : ∀ x, x ∈ Λ ↔ ∀ i, ((β₀⁻¹).val *ᵥ x) i ∈ S) (b : Fin n → Fin n → A) (hb : ∀ j, b j ∈ Λ)
    (hs : ∀ y ∈ Λ, y ∈ Submodule.span S (Set.range b) ⊔ Submodule.span S {y | ∃ x ∈ Λ, y = (g : A) • x}) :
    ∃ β : GL (Fin n) A, (∀ x, x ∈ Λ ↔ ∀ i, ((β⁻¹).val *ᵥ x) i ∈ S) ∧
      ∀ j, ∃ x ∈ Λ, (fun i => β.val i j) - b j = (g : A) • x := by
  have hback : ∀ v : Fin n → A, (β₀⁻¹).val *ᵥ (β₀.val *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hback' : ∀ v : Fin n → A, β₀.val *ᵥ ((β₀⁻¹).val *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hint : ∀ v : Fin n → S, β₀.val *ᵥ (fun i => (v i : A)) ∈ Λ := fun v => (hβ _).2 fun i => by
    rw [hback]; exact (v i).2
  let M : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨((β₀⁻¹).val *ᵥ b j) i, (hβ _).1 (hb j) i⟩
  have hg : ∀ z ∈ Submodule.span S {y | ∃ x ∈ Λ, y = (g : A) • x}, ∃ x ∈ Λ, z = (g : A) • x := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, (smul_add _ _ _).symm⟩
    | smul a x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact ⟨a • x, Λ.smul_mem a hx, smul_comm _ _ _⟩
  have hcol : ∀ k : Fin n, ∃ c r : Fin n → S, ∀ i, (M *ᵥ c) i = (1 : Matrix (Fin n) (Fin n) S) i k - g * r i := by
    intro k
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs _ (hint fun i => (1 : Matrix (Fin n) (Fin n) S) i k))
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hy
    obtain ⟨x, hx, rfl⟩ := hg z hz
    refine ⟨c, fun i => ⟨_, (hβ x).1 hx i⟩, fun i => Subtype.ext ?_⟩
    have h1 := congrArg (fun v => ((β₀⁻¹).val *ᵥ v) i) hyz
    simp only [hback, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_sum,
      Finset.sum_apply] at h1
    have h2 : (((M *ᵥ c) i : S) : A) = ∑ j, c j • ((β₀⁻¹).val *ᵥ b j) i := by
      change S.subtype (∑ j, M i j * c j) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h2, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast, ← h1, add_sub_cancel_right]
  choose c r hcr using hcol
  obtain ⟨U, hU⟩ := isUnit_mix he hu M (Matrix.of fun i k => c k i) (Matrix.of fun i k => r k i) (by
    ext i k
    exact congrArg Subtype.val (hcr k i))
  have hmv : ∀ (V : GL (Fin n) S) (v : Fin n → A), (∀ i, v i ∈ S) →
      ∀ i, ((GeneralLinearGroup.map S.subtype V).val *ᵥ v) i ∈ S := fun V v hv i => by
    change ∑ j, (V.val i j : A) * v j ∈ S
    exact sum_mem fun j _ => mul_mem (V.val i j).2 (hv j)
  refine ⟨β₀ * GeneralLinearGroup.map S.subtype U, fun x => ?_, fun j => ?_⟩
  · rw [hβ, _root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec, ← map_inv]
    refine ⟨hmv _ _, fun h => ?_⟩
    have := hmv U _ h
    rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec] at this
  · refine ⟨_, hint fun i => t * ((1 : Matrix (Fin n) (Fin n) S) i j - M i j), ?_⟩
    have h1 : (fun i => (β₀ * GeneralLinearGroup.map S.subtype U).val i j) =
        β₀.val *ᵥ fun i => (U.val i j : A) := rfl
    rw [h1, ← hback' (b j), ← mulVec_sub, ← mulVec_smul]
    congr 1
    funext i
    have h2 : U.val i j - M i j = g * (t * ((1 : Matrix (Fin n) (Fin n) S) i j - M i j)) := by
      rw [hU, ← mul_assoc, ← ht]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have h3 := congrArg Subtype.val h2
    rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast] at h3
    exact h3

end Alg

open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

theorem valued_natCast_lt_one_iff {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : Q.adicCompletion E) < 1 ↔ (N : 𝓞 E) ∈ Q.asIdeal := by
  rw [← Q.valuation_lt_one_iff_mem (K := E) (N : 𝓞 E), ← Formalism.UG.P.levelaf_valued_algebraMap]
  simp

theorem exists_inv_of_valued {D : D7} (z : Ef D) (h : ∀ Q : Pl D.host.E, Valued.v (cpt Q z) = 1) :
    ∃ y ∈ OA D, z * y = 1 := by
  have hi : ∀ Q : Pl D.host.E, (cpt Q z)⁻¹ ∈ Q.adicCompletionIntegers D.host.E := fun Q => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]
  obtain ⟨y, hy⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
    (⟨fun Q => (cpt Q z)⁻¹, Filter.Eventually.of_forall hi⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  have h1 : ∀ Q : Pl D.host.E, cpt Q y = (cpt Q z)⁻¹ := fun Q => by
    change toAd D y Q = _
    rw [hy]
    rfl
  refine ⟨y, (mem_OA_iff y).2 fun Q => h1 Q ▸ hi Q, cpt_ext fun Q => ?_⟩
  rw [RingHom.map_mul, RingHom.map_one, h1, mul_inv_cancel₀]
  intro h0
  have := h Q
  rw [h0, Valuation.map_zero] at this
  exact zero_ne_one this

theorem coe_one_sub {A : Type} [CommRing A] (S : Subring A) (g : ℕ) (e a : S) :
    ((1 - e * g * a : S) : A) = 1 - e * g * a := by
  push_cast
  rfl

theorem one_sub_eq {A : Type} [CommRing A] (S : Subring A) {g : ℕ} {c e : A} (hc : (g : A) * c = 1) (he : e ∈ S)
    (ht : c * (1 - e) ∈ S) : (1 - ⟨e, he⟩ : S) = g * ⟨_, ht⟩ := by
  refine Subtype.ext ?_
  push_cast
  rw [← mul_assoc, hc, one_mul]

section Val

variable {A K Γ : Type} [CommRing A] [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (φ : A →+* K)

theorem val_quot_le {g : ℕ} {c e : A} (hc : (g : A) * c = 1) (h : φ e = 1 ∨ φ e = 0 ∧ v (g : K) = 1) :
    v (φ (c * (1 - e))) ≤ 1 := by
  rcases h with h | ⟨h, h1⟩
  · simp [h]
  · have h2 := congrArg (fun x => v (φ x)) hc
    simp only [map_mul, map_natCast, map_one, h1, one_mul] at h2
    simp [h, h2]

theorem val_one_sub {g : ℕ} {a e : A} (ha : v (φ a) ≤ 1) (h : φ e = 1 ∧ v (g : K) < 1 ∨ φ e = 0) :
    v (φ (1 - e * g * a)) = 1 := by
  rcases h with ⟨h, h1⟩ | h
  · rw [map_sub, map_one, map_mul, map_mul, map_natCast, h, one_mul]
    refine Valuation.map_one_sub_of_lt _ ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' ha).trans_lt h1
  · simp [h]

end Val

theorem quot_mem {D : D7} {g : ℕ} {c e : Ef D} (hc : (g : Ef D) * c = 1)
    (he1 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∈ Q.asIdeal → cpt Q e = 1)
    (he0 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q e = 0) : c * (1 - e) ∈ OA D :=
  (mem_OA_iff _).2 fun Q => by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (val_quot_le Valued.v (cpt Q) hc ?_)
    by_cases hQ : (g : 𝓞 D.host.E) ∈ Q.asIdeal
    · exact Or.inl (he1 Q hQ)
    · exact Or.inr ⟨he0 Q hQ, le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
        (natCast_mem (Q.adicCompletionIntegers D.host.E) g))
        (not_lt.1 fun h => hQ ((valued_natCast_lt_one_iff Q g).1 h))⟩

theorem valued_one_sub {D : D7} {g : ℕ} {a e : Ef D} (ha : a ∈ OA D)
    (he1 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∈ Q.asIdeal → cpt Q e = 1)
    (he0 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q e = 0) (Q : Pl D.host.E) :
    Valued.v (cpt Q (1 - e * g * a)) = 1 := by
  refine val_one_sub Valued.v (cpt Q)
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_OA_iff _).1 ha Q)) ?_
  by_cases hQ : (g : 𝓞 D.host.E) ∈ Q.asIdeal
  · exact Or.inl ⟨he1 Q hQ, (valued_natCast_lt_one_iff Q g).2 hQ⟩
  · exact Or.inr (he0 Q hQ)

theorem exists_idem_over (D : D7) {g : ℕ} (hg : g ≠ 0) :
    ∃ e c : Ef D, e * e = e ∧ e ∈ OA D ∧ (g : Ef D) * c = 1 ∧ c * (1 - e) ∈ OA D ∧
      ∀ a ∈ OA D, ∃ y ∈ OA D, (1 - e * g * a) * y = 1 := by
  obtain ⟨e, he, heO, he1, he0⟩ := exists_idem {Q : Pl D.host.E | (g : 𝓞 D.host.E) ∈ Q.asIdeal}
  obtain ⟨c, hc⟩ : ∃ c : Ef D, (g : Ef D) * c = 1 := by
    refine ⟨algebraMap D.host.E (Ef D) (g : D.host.E)⁻¹, ?_⟩
    rw [← map_natCast (algebraMap D.host.E (Ef D)), ← RingHom.map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hg),
      RingHom.map_one]
  exact ⟨e, c, he, heO, hc, quot_mem hc he1 he0, fun a ha => exists_inv_of_valued _ (valued_one_sub ha he1 he0)⟩

theorem idem_subring {A : Type} [CommRing A] (S : Subring A) {g : ℕ}
    (h : ∃ e c : A, e * e = e ∧ e ∈ S ∧ (g : A) * c = 1 ∧ c * (1 - e) ∈ S ∧
      ∀ a ∈ S, ∃ y ∈ S, (1 - e * g * a) * y = 1) :
    ∃ e t : S, e * e = e ∧ 1 - e = g * t ∧ ∀ a : S, IsUnit (1 - e * g * a) := by
  obtain ⟨e, c, he, heS, hc, ht, hu⟩ := h
  refine ⟨⟨e, heS⟩, ⟨_, ht⟩, Subtype.ext he, one_sub_eq S hc heS ht, fun a => ?_⟩
  obtain ⟨y, hy, h⟩ := hu a a.2
  refine IsUnit.of_mul_eq_one ⟨y, hy⟩ (Subtype.ext ?_)
  rw [MulMemClass.coe_mul, coe_one_sub]
  exact h

theorem hatL_eq_Lf (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => ⟨⟨y, hy⟩, h⟩, fun ⟨y, h⟩ => ⟨y.1, y.2, h⟩⟩

theorem exists_isLiftFrame : ∀ (D : D7) (g : ℕ), g ≠ 0 → ∀ b : ℕ → VA (instOf D), (∀ j, b j ∈ (instOf D).Lf) →
    (∀ y ∈ (instOf D).Lf, InMod (instOf D) g (Set.range fun j : Fin (instOf D).n => b j.val) y) →
    ∃ β, IsLiftFrame (instOf D) g b β := by
  intro D g hg b hb hs
  obtain ⟨e, t, he, ht, hu⟩ := idem_subring (IntAf (instOf D).F (instOf D).E) (g := g) (exists_idem_over D hg)
  generalize instOf D = I at *
  obtain ⟨β₀, h₀⟩ := GlobalTheory.latticeFrame.exists_frame I.F I.E I.n I.L ⟨I.L_fg, I.L_span⟩
  obtain ⟨β, h1, h2⟩ := exists_lift (IntAf I.F I.E) g he ht hu I.Lf β₀ (fun x => hatL_eq_Lf I ▸ h₀ x)
    (fun j => b j.val) (fun j => hb j.val) hs
  exact ⟨β, fun x => (hatL_eq_Lf I).symm ▸ h1 x, fun j => Submodule.subset_span (h2 j)⟩

end GlobalTheory.LiftFrameMod

end
