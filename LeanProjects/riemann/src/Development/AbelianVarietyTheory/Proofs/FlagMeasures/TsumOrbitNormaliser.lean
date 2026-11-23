import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTermsStatement

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.InvH

theorem tsum_orbit_normaliser {G X M : Type} [Group G] [MulAction G X] [AddCommMonoid M]
    [TopologicalSpace M] (K : Subgroup G) (h : G) (h1 : ∀ s ∈ K, h * s * h⁻¹ ∈ K)
    (h2 : ∀ s ∈ K, h⁻¹ * s * h ∈ K) (φ ψ : X → M) (hφ : ∀ s ∈ K, ∀ x, φ (s • x) = φ x)
    (hψ : ∀ x, ψ (h • x) = φ x) :
    ∑' o : MulAction.orbitRel.Quotient K X, ψ o.out =
      ∑' o : MulAction.orbitRel.Quotient K X, φ o.out := by
  let e : MulAction.orbitRel.Quotient K X ≃ MulAction.orbitRel.Quotient K X :=
    Quotient.congr (MulAction.toPerm h) (by
      intro a b
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.toPerm_apply]
      constructor
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h1 s s.2⟩, ?_⟩
        rw [← hs]
        simp [Subgroup.smul_def, mul_smul]
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h2 s s.2⟩, ?_⟩
        simp only [Subgroup.smul_def, mul_smul] at hs ⊢
        rw [hs]; simp)
  rw [← e.tsum_eq]
  refine tsum_congr fun o => ?_
  have h3 : e o = Quotient.mk _ (h • o.out) := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have h4 : (MulAction.orbitRel K X) (e o).out (h • o.out) := by
    rw [h3]; exact Quotient.mk_out (s := MulAction.orbitRel K X) _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : (e o).out = h • ((h⁻¹ * s * h) • o.out) := by
    rw [← hs]; simp [Subgroup.smul_def, mul_smul]
  rw [h5, hψ, hφ _ (h2 s s.2)]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem conj_unipOn {n : ℕ} {A B : Submodule E (Fin n → E)} {h s : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (hs : s ∈ unipOn A B) :
    h * s * h⁻¹ ∈ unipOn A B := by
  have hA' : ∀ v, h.symm v ∈ A ↔ v ∈ A := fun v => by rw [← hA]; simp
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · change h (s (h.symm v)) ∈ A ↔ _
    rw [hA, hs.1, hA']
  · have := (hB _).2 (hs.2 _ ((hA' v).2 hv))
    rw [map_sub, LinearEquiv.apply_symm_apply] at this
    exact this

theorem mem_iff_of_fix {n : ℕ} {A : Submodule E (Fin n → E)} {h : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v ∈ A, h v = v) (v : Fin n → E) : h v ∈ A ↔ v ∈ A := by
  constructor
  · intro hv
    have := h.injective (hA _ hv)
    rwa [this] at hv
  · intro hv; rwa [hA v hv]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (hij : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha hij)

theorem conj_Nof (g : Fin (r + 1) → S.V) {h s : S.GLV} (hi : h ∈ isomG L S.Hm)
    (hg : ∀ v ∈ S.spanTo g (r + 1), h v = v) (hs : s ∈ S.Nof g) : h * s * h⁻¹ ∈ S.Nof g := by
  have hfix : ∀ j ≤ r + 1, ∀ v, h v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j := fun j hj =>
    mem_iff_of_fix fun v hv => hg v (spanTo_mono S g hj hv)
  obtain ⟨⟨s1, s2⟩, s3⟩ := hs
  refine ⟨⟨(isomG L S.Hm).mul_mem ((isomG L S.Hm).mul_mem hi s1) ((isomG L S.Hm).inv_mem hi), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun j => ?_
    exact conj_unipOn (hfix _ (by omega)) (hfix _ (by omega)) (Subgroup.mem_iInf.1 s2 j)
  · refine conj_unipOn (fun v => ?_) (hfix _ (by omega)) s3
    refine forall₂_congr fun y hy => ?_
    have := hi v y
    rw [hg y (spanTo_mono S g (by omega) hy)] at this
    rw [this]

theorem conj_St {h s : S.GLV} (hh : h ∈ S.H0) (hs : s ∈ S.St) : h * s * h⁻¹ ∈ S.St := by
  have hfix : ∀ v ∈ S.ME, h v = v := fun v hv => sub_eq_zero.1 ((Submodule.mem_bot E).1 (hh.2.2 v hv))
  exact ⟨conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_left hv)) hs.1,
    conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_right hv)) hs.2⟩

theorem amp_mass_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, ∀ (d : S.Datum) (Q Q' : Submodule L.O S.V → Prop), (∀ s ∈ S.St, ∀ Λ, S.IsTerm d Λ → Q Λ → Q (s • Λ)) → (∀ Λ, S.IsTerm d Λ → (Q Λ ↔ Q' (h • Λ))) → S.amp (h • d) Q' = S.amp d Q ∧ S.mass (h • d) Q' = S.mass d Q := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh d Q Q' hQ hQ'
  have c1 : ∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St := fun s hs => conj_St S hh hs
  have c2 : ∀ s ∈ S.St, h⁻¹ * s * h ∈ S.St := fun s hs => by
    simpa using conj_St S (inv_mem hh) hs
  have aS := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d
  have aH := GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms L r k S
  have hmu : ∀ Λ, S.IsTerm d Λ → ∀ s ∈ S.St, S.mu (s • Λ) = S.mu Λ := fun Λ hΛ =>
    ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ).1.1).2.2
  have iS : ∀ s ∈ S.St, ∀ Λ, (S.IsTerm d (s • Λ) ∧ Q (s • Λ)) ↔ (S.IsTerm d Λ ∧ Q Λ) := by
    intro s hs Λ
    constructor
    · rintro ⟨a, b⟩
      have a' := (aS _ a _ (inv_mem hs)).1
      have b' := hQ _ (inv_mem hs) _ a b
      rw [inv_smul_smul] at a' b'
      exact ⟨a', b'⟩
    · rintro ⟨a, b⟩
      exact ⟨(aS _ a _ hs).1, hQ _ hs _ a b⟩
  have iH : ∀ Λ, (S.IsTerm (h • d) (h • Λ) ∧ Q' (h • Λ)) ↔ (S.IsTerm d Λ ∧ Q Λ) := by
    intro Λ
    constructor
    · rintro ⟨a, b⟩
      have a' := (aH _ _ a _ (inv_mem hh)).1
      rw [inv_smul_smul, inv_smul_smul] at a'
      exact ⟨a', (hQ' _ a').2 b⟩
    · rintro ⟨a, b⟩
      exact ⟨(aH _ _ a _ hh).1, (hQ' _ a).1 b⟩
  constructor
  · refine tsum_orbit_normaliser S.St h c1 c2
      (fun Λ => if S.IsTerm d Λ ∧ Q Λ then (S.mu Λ : ℂ) * S.om d Λ else 0)
      (fun Λ => if S.IsTerm (h • d) Λ ∧ Q' Λ then (S.mu Λ : ℂ) * S.om (h • d) Λ else 0) ?_ ?_
    · intro s hs Λ
      exact if_ctx_congr (iS s hs Λ) (fun a => by rw [hmu _ a.1 s hs, (aS _ a.1 s hs).2.1])
        fun _ => rfl
    · intro Λ
      exact if_ctx_congr (iH Λ)
        (fun a => by rw [(aH _ _ a.1 h hh).2.1, (aH _ _ a.1 h hh).2.2.1]) fun _ => rfl
  · refine tsum_orbit_normaliser S.St h c1 c2
      (fun Λ => if S.IsTerm d Λ ∧ Q Λ then ENNReal.ofReal (S.mu Λ) else 0)
      (fun Λ => if S.IsTerm (h • d) Λ ∧ Q' Λ then ENNReal.ofReal (S.mu Λ) else 0) ?_ ?_
    · intro s hs Λ
      exact if_ctx_congr (iS s hs Λ) (fun a => by rw [hmu _ a.1 s hs]) fun _ => rfl
    · intro Λ
      exact if_ctx_congr (iH Λ) (fun a => by rw [(aH _ _ a.1 h hh).2.2.1]) fun _ => rfl

end GlobalTheory.InvH
