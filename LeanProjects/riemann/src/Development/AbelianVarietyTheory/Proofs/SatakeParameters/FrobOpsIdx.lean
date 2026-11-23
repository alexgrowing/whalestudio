import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalLocalOperators
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

noncomputable section

namespace GlobalTheory.FrobOpsIdx
open Polynomial

theorem frobOpsIdx : SphOps → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (Kw : Levels E a) (W0 : Set (HeightOneSpectrum (𝓞 E))), (∀ w ∈ W0, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ Kw w = GlobalTheory.LFun.KGL w a) → ∃ (J : Type) (T : LocOps l ι Kw J) (x fr : J → G E Ω) (n : J → ℕ), (∀ j, x j = (fr j)⁻¹ ^ n j) ∧ (∀ j, T.pl j ∈ W0 ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A (T.pl j) ∧ IsFrob A (normV (T.pl j)) (fr j)) ∧ (∀ w ∈ W0, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s : G E Ω, IsFrob A (normV w) s → ∃ j, T.pl j = w ∧ fr j = s ∧ n j = 1) ∧ (∀ j g, ∃ q : ℚ, T.f j g = q) ∧ (∀ (j : J) (σ : SmIrr (GL (Fin a) ((T.pl j).adicCompletion E))), GlobalTheory.PRep.fixed σ.ρ (Kw (T.pl j)) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL (T.pl j) σ.ρ B → ∀ ρ : G E Ω →* GL (Fin a) (Qbar l), ((ρ (fr j)⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV (T.pl j)) B).map fun b => Polynomial.X - Polynomial.C b).prod → ι.symm (T.z j σ) = trc ρ (x j)) ∧ ∀ w ∈ W0, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ r : G E Ω →* GL (Fin a) (Qbar l), (∀ j (h : T.pl j = w), trc r (x j) = ι.symm (T.z j (h ▸ σ))) → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s : G E Ω, IsFrob A (normV w) s → ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro hS E Ω _ _ _ _ _ _ l _ ι a Kw W0 hW
  classical
  have hl : l.Prime := Fact.out
  let J : Type := {p : HeightOneSpectrum (𝓞 E) × ValuationSubring Ω × G E Ω × ℕ //
    p.1 ∈ W0 ∧ IsPlaceOver p.2.1 p.1 ∧ IsFrob p.2.1 (normV p.1) p.2.2.1 ∧ 1 ≤ p.2.2.2}
  have hf : ∀ j : J, ∃ f : GL (Fin a) (j.1.1.adicCompletion E) →₀ ℂ,
      (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV j.1.1 : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 a),
          opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ ((j.1.2.2.2 : ℕ) : ℤ))).sum • v :=
    fun j => (hS E j.1.1 a).2 (j.1.2.2.2 : ℤ)
  let zz : ∀ j : J, SmIrr (GL (Fin a) (j.1.1.adicCompletion E)) → ℂ := fun j σ =>
    if h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B then
      ((UpperTheory.V.Af.algSat a (normV j.1.1) h.choose).map (· ^ j.1.2.2.2)).sum else 0
  have hz : ∀ (j : J) (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ),
      GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B → zz j σ = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ j.1.2.2.2)).sum := by
    intro j σ B hB
    have h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B := ⟨B, hB⟩
    simp only [zz, dif_pos h]
    rw [show h.choose = B from h.choose_spec.unique hB]
  let T : LocOps l ι Kw J :=
    { pl := fun j => j.1.1
      split := fun j => (hW _ j.2.1).1
      away := fun j => (hW _ j.2.1).2.1
      f := fun j => (hf j).choose
      int := fun j g => by
        obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
        rw [he]
        exact GlobalTheory.FrobOps.norm_le_one ι m _ e (GlobalTheory.FrobOps.not_dvd_normV hl _ (hW _ j.2.1).2.1)
      z := zz
      act := fun j σ v hv => by
        rw [(hW _ j.2.1).2.2] at hv
        by_cases h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B
        · obtain ⟨B, hB⟩ := h
          rw [hz j σ B hB, (hf j).choose_spec.2 σ B hB v hv]
          simp only [zpow_natCast]
        · have h0 : PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 a) = ⊥ := by
            by_contra hne
            exact h ((hS E j.1.1 a).1 σ hne)
          rw [h0, Submodule.mem_bot] at hv
          subst hv
          simp [opOf] }
  let fr : J → G E Ω := fun j => j.1.2.2.1
  let nn : J → ℕ := fun j => j.1.2.2.2
  let x : J → G E Ω := fun j => (fr j)⁻¹ ^ nn j
  refine ⟨J, T, x, fr, nn, fun j => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨j.2.1, j.1.2.1, j.2.2.1, j.2.2.2.1⟩
  · intro w hw A hA s hsF
    exact ⟨⟨(w, A, s, 1), hw, hA, hsF, le_rfl⟩, rfl, rfl, rfl⟩
  · intro j g
    obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
    refine ⟨(m : ℚ) / ((normV j.1.1 : ℕ) : ℚ) ^ e, ?_⟩
    show (hf j).choose g = _
    rw [he]
    push_cast
    rfl
  · intro j σ _ B hB ρ hFE
    show ι.symm (zz j σ) = trc ρ (x j)
    rw [hz j σ B hB]
    apply ι.injective
    rw [RingEquiv.apply_symm_apply, GlobalTheory.FrobOps.iota_trc]
    exact (GlobalTheory.FrobOps.trace_pow_of_charpoly _ _ (by rw [Matrix.charpoly_map]; exact hFE) _).symm
  · intro w hw σ _ B hBσ r hr A hA s hsF
    rw [← Matrix.charpoly_map]
    refine GlobalTheory.CharpolyNewton.charpoly_eq_prod_of_trace_pow ℂ a _ _ ?_ ?_
    · simp [UpperTheory.V.Af.algSat, hBσ.card]
    · intro n hn
      let j : J := ⟨(w, A, s, n), hw, hA, hsF, hn⟩
      have h2 : trc r (x j) = ι.symm (zz j σ) := hr j rfl
      rw [hz j σ B hBσ] at h2
      rw [← GlobalTheory.FrobOps.iota_trc]
      change ι (trc r (x j)) = _
      rw [h2, RingEquiv.apply_symm_apply]

end GlobalTheory.FrobOpsIdx
