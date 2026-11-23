import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContMapRepIotaOQ
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.TwistLG

open Formalism.MainNotions.SumRepresentations.At

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have h1 := W.smul_mem (((χ g)⁻¹ : kˣ) : k) (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at h1
    exact h1
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (h : IsSSRep ρ) : IsSSRep (twGL ρ χ) := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 h1, h2⟩

theorem cont_twGL [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_val]
  refine Continuous.smul (M := k) ?_ hρ
  have e : ∀ g, (((Matrix.GeneralLinearGroup.det.comp χ) g : kˣ) : k) =
      (χ g : Matrix (Fin 1) (Fin 1) k).det := fun g => rfl
  simp only [e]
  exact hχ.matrix_det

theorem charpoly_eq_of_dense [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    [Infinite k] (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem etaT_char_etaTinv (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} := by
  have u1 := A.etaT_unr w
  obtain ⟨u2, f2⟩ := A.etaTinv_def w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  obtain ⟨b, hb⟩ : ∃ b, A.frobEig (A.locG A.etaT w) = {b} :=
    Multiset.card_eq_one.mp (by rw [A.frobEig_card _ u1, A.locG_dim])
  have hb0 : b ≠ 0 := by
    intro h0
    apply A.frobEig_ne_zero _ u1
    rw [hb, h0]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at f2
  have hu := A.unr_char _ _ d2 u1 u2
  have hf := A.frobEig_char _ _ b⁻¹ u1 u2 d2 f2
  rw [hb, Multiset.map_singleton, mul_inv_cancel₀ hb0] at hf
  rw [A.unr_eq_lpUnr _ hu, hf]

theorem param_twist (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u s : ℝ) :
    A.lpChar (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpTw (A.locG A.etaTinv w) s) =
      A.lpTw (A.locG π w) (s + u) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  have c3 := (hLP w (A.lpTw (A.locG (A.tw π A.etaT) w) u) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) s d2 d2).2.2.1
  have c2 := (hLP w (A.locG (A.tw π A.etaT) w) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w) u
    d2 d2).2.1
  have c4 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w (A.locG π w) (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3, c2, A.lpTw_add, A.locG_tw, c4, etaT_char_etaTinv N A w, c5, add_comm]

theorem isSSRep_iotaOQ (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i))
    (h : IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ)) : IsSSRep (mapRep (iotaOQ N A i) ρ) := by
  let _ : Algebra (Kf N i) (Qbar (N.l i)) := (A.iotaQ i).toAlgebra
  have : CharZero (Kf N i) := RingHom.charZero (A.iotaQ i)
  have e : mapRep (iotaOQ N A i) ρ =
      mapRep (algebraMap (Kf N i) (Qbar (N.l i))) (mapRep (algebraMap (N.O i) (Kf N i)) ρ) := by
    ext g p q
    rfl
  rw [e]
  exact ssAscent (Kf N i) (Qbar (N.l i)) (G H.E N.Om) a _ h

theorem placesOver_finite (i : N.Loc) : (placesOver H.E (N.l i)).Finite := by
  have hne : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : (N.l i).Prime).ne_zero
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

end Glob

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem localGlobal_twist_at (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : exists_galois_rep_local_global_compatible N A)
    (hAN : JacquetShalikaStrongMultOne N A) (i : N.Loc) (a : ℕ) (ha : 1 ≤ a) (π : A.CG a) (s : ℝ)
    (hcsd : A.csd (A.tw π A.etaT)) (hralg : A.ralg (A.tw π A.etaT)) (hs : ∃ m : ℤ, s = (m : ℝ) + 1 / 2)
    (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) (hρ : GlobalTheory.LocalInv.Cont N i ρ)
    (hss : IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ))
    (hM : GlobalTheory.LocalInv.Matches N A i ρ π (s + (1 - (a : ℝ)) / 2)) (w : PlE H) :
    GlobalTheory.LocalInv.wd N A i ρ w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2) ∧
      (w ∈ placesOver H.E (N.l i) → GlobalTheory.LocalInv.DeRham N A i ρ w) := by

  obtain ⟨ρ1, c1, ss1, away1, above1⟩ := (hG i).1 a ha _ hcsd hralg

  have hint : ∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG A.etaTinv τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ) := by
    intro τ z hz
    obtain ⟨m, rfl⟩ := hs
    obtain ⟨h1, h2⟩ := hAut.2.1 τ
    rw [h2] at hz
    rcases h1 with h1 | h1
    · rw [h1] at hz
      simp at hz
      subst hz
      exact ⟨m, by push_cast; ring⟩
    · rw [h1] at hz
      simp at hz
      subst hz
      exact ⟨m + 1, by push_cast; ring⟩
  obtain ⟨χ1, cχ, awayχ, aboveχ⟩ := (hG i).2.2 A.etaTinv s hint
  obtain ⟨-, hconj, -, htw⟩ := hGal.2.2.2 i
  have ok1 : ∀ w, WDok N A i ρ1 w := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr (above1 w hw).1
    · exact Or.inl hw
  have okχ : ∀ w, WDok N A i χ1 w := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr (aboveχ w hw).1
    · exact Or.inl hw
  have wd1 : ∀ w, A.wdOf i ρ1 w = A.lpTw (A.locG (A.tw π A.etaT) w) ((1 - (a : ℝ)) / 2) := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact (above1 w hw).2.2
    · exact (away1 w hw).1
  have wdχ : ∀ w, A.wdOf i χ1 w = A.lpTw (A.locG A.etaTinv w) s := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact (aboveχ w hw).2.1
    · exact awayχ w hw

  let ρ0 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1)
  have c0 : ContQ N i ρ0 := cont_twGL ρ1 χ1 c1 cχ
  have wd0 : ∀ w, A.wdOf i ρ0 w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2) := fun w => by
    rw [(htw a ρ1 χ1 c1 cχ).2.1 w (ok1 w) (okχ w), wd1, wdχ, param_twist N A hLP]
  have dR0 : ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ0 w := fun w hw =>
    ((htw a ρ1 χ1 c1 cχ).1 w hw (aboveχ w hw).1).2 (above1 w hw).1
  have ok0 : ∀ w, WDok N A i ρ0 w := fun w => by
    by_cases hw : w ∈ placesOver H.E (N.l i)
    · exact Or.inr (dR0 w hw)
    · exact Or.inl hw

  let ρQ := mapRep (iotaOQ N A i) ρ
  have cQ : ContQ N i ρQ := GlobalTheory.LocalInv.cont_mapRep_iotaOQ N A i ρ hρ
  have ssQ : IsSSRep ρQ := isSSRep_iotaOQ N A i ρ hss
  have ss0 : IsSSRep ρ0 := isSSRep_twGL _ _ ss1

  have hcp : ∀ g, ((ρ0 g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly =
      ((ρQ g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly := by
    have hMf := Filter.eventually_cofinite.mp hM
    have hUf := Filter.eventually_cofinite.mp (A.locG_unr_ae π)
    refine charpoly_eq_of_dense ρ0 ρQ c0 cQ _
      (hAN.2.2.1 _ (((placesOver_finite N i).union hMf).union hUf)) ?_
    rintro g ⟨v, hv, hsp, B, hB, hg⟩
    simp only [Set.mem_union, not_or] at hv
    obtain ⟨⟨hvl, hvM⟩, hvU⟩ := hv
    have hvM' := not_not.mp hvM
    have hvU' := not_not.mp hvU
    apply Polynomial.map_injective (A.iotaQC i).toRingHom (A.iotaQC i).injective
    have hu0 : A.unr (A.wdOf i ρ0 v) := by
      rw [wd0]
      exact (A.unr_tw _ _).2 hvU'
    rw [A.wdOf_frob i ρ0 v hvl c0 hu0 B g hB hg, wd0]
    have e := hvM' hsp B g hB hg
    have e2 : ((ρQ g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.map
        (A.iotaQC i).toRingHom =
        ((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).charpoly.map (iotaO N A i) := by
      show ((((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)).map (iotaOQ N A i)).charpoly).map _ = _
      rw [Matrix.charpoly_map, Polynomial.map_map]
      rfl
    rw [e2, e]
    rfl

  obtain ⟨Pm, hPm⟩ := hAN.2.2.2 (Qbar (N.l i)) a ρ0 ρQ ss0 ssQ hcp
  obtain ⟨hdR, hwd, -⟩ := hconj a ρ0 ρQ c0 Pm hPm
  refine ⟨?_, fun hw => ?_⟩
  · show A.wdOf i ρQ w = _
    rw [hwd w (ok0 w), wd0]
  · show A.IsdRW i ρQ w
    exact (hdR w hw).2 (dR0 w hw)

end Main

theorem localGlobal_twist : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D →
    ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ (π : D.naut.CG a) (s : ℝ), D.naut.csd (D.naut.tw π D.naut.etaT) →
    D.naut.ralg (D.naut.tw π D.naut.etaT) → (∃ m : ℤ, s = (m : ℝ) + 1 / 2) →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin a) (D.nd.O i), GlobalTheory.LocalInv.Cont D.nd i ρ →
    IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) →
    GlobalTheory.LocalInv.Matches D.nd D.naut i ρ π (s + (1 - (a : ℝ)) / 2) →
    ∀ w, GlobalTheory.LocalInv.wd D.nd D.naut i ρ w = D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2) ∧
      (w ∈ placesOver D.host.E (D.nd.l i) → GlobalTheory.LocalInv.DeRham D.nd D.naut i ρ w) := by
  intro D ht h2 h5 i a ha π s hcsd hralg hs ρ hρ hss hM w
  exact localGlobal_twist_at D.nd D.naut ht.1 ht.2.1 ht.2.2 h2 h5 i a ha π s hcsd hralg hs ρ hρ hss hM w

end GlobalTheory.TwistLG
