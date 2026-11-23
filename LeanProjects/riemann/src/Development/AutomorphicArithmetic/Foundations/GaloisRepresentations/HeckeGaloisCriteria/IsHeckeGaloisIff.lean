import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.LengthLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfMemCcAt

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting Alg TensorProduct

variable {D : D7} {c : CutD D}

theorem mem_Zgood {i : (cut D c).nd.Loc} {x : (cut D c).nd.X i} : x ∈ (cut D c).nd.Zgood i ↔ x.1 ∈ D.nd.Zgood i.1 := by
  classical
  exact Finset.mem_subtype

theorem mem_ZgoodN {i : (cut D c).nd.Loc} {x : (cut D c).nd.X i} :
    x ∈ ZgoodN (cut D c).nd (cut D c).naut i ↔ x.1 ∈ ZgoodN D.nd D.naut i.1 :=
  ((cut D c).Zgood_tie i x).symm.trans (mem_Zgood.trans (D.Zgood_tie i.1 x.1))

theorem CutD.Good.hG (h : c.Good) (i : (cut D c).nd.Loc) : HG (cut D c).nd (cut D c).naut i := by
  obtain ⟨x, hx⟩ := (h.keep i.1).1 i.2
  exact ⟨⟨x, h.good _ x hx⟩, mem_ZgoodN.2 ((D.Zgood_tie i.1 x).1 hx)⟩

abbrev qc (c : CutD D) (i : (cut D c).nd.Loc) :
    FractionRing (D.nd.O i.1) ⊗[D.nd.O i.1] D.nd.Mt i.1 →ₗ[FractionRing (D.nd.O i.1)]
      FractionRing (D.nd.O i.1) ⊗[D.nd.O i.1] cutM (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) :=
  qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)

theorem eta_le (h : c.Good) (i : (cut D c).nd.Loc) : D.nd.etaLoc i.1 ≤ (cut D c).nd.etaLoc i +
    (∑ x ∈ D.nd.Zgood i.1, D.nd.mult i.1 x : ℕ) * (padicValNat (D.nd.l i.1) D.what₂.restRowsFiniteGroupCard : ℚ) := by
  classical
  obtain ⟨α, -, hα1, hα2⟩ := h.op i.1 i.2
  have hn : D.what₂.restRowsFiniteGroupCard ≠ 0 := (D.what₂.restRowsFiniteGroupCard_pos).ne'
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) ≠ 0 := by
    intro hz
    have h1 : ((D.what₂.restRowsFiniteGroupCard : D.what₂.LL) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h2 : D.nd.embK i.1 (D.what₂.restRowsFiniteGroupCard : D.what₂.LL) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (D.nd.O i.1) (FractionRing (D.nd.O i.1))), hz, map_zero]
    exact h1 ((map_eq_zero_iff _ (D.nd.embK i.1).injective).mp h2)
  have hα1' : ∀ x ∈ D.nd.Zgood i.1, ∀ u ∈ heckeEig (D.nd.T i.1) (D.nd.act i.1) x,
      (LinearMap.baseChange (FractionRing (D.nd.O i.1)) α) u = ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) • u := by
    intro x hx u hu
    rw [hα1 x hx u hu, Int.cast_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hY : ∀ x : ↥(c.Xs i.1), x ∈ (((cut D c).nd.Zgood i : Finset ((cut D c).nd.X i)) : Set ((cut D c).nd.X i)) ↔
      (x : D.nd.X i.1) ∈ D.nd.Zgood i.1 :=
    fun x => Iff.trans Finset.mem_coe mem_Zgood
  have key := Alg.length_le (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (D.nd.Zgood i.1) _ hY α _ hA hα1' hα2
  have hfinE : Module.length (D.nd.O i.1) (D.nd.O i.1 ⧸ Ideal.span {((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1)}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hA))
  have hpad := GlobalTheory.CutAtGood.lenUnit_natCast_le i.1 D.what₂.restRowsFiniteGroupCard hn
  refine (Alg.lenUnit_le_add (D.nd.l i.1) _ hfinE (fun hC => absurd hC ?_) key).trans ?_
  · exact Alg.length_ne_top ((cut D c).nd.T i) ((cut D c).nd.act i) ((cut D c).nd.T_sep i) ((cut D c).nd.Zgood i)
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpad (Nat.cast_nonneg _))

theorem eta_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.Zgood i = ∅) :
    N.etaLoc i = 0 := by
  have hsum : N.eigSum i ↑(N.Zgood i) = ⊥ := by
    rw [h]
    simp [NData.eigSum]
  have hup : N.MtUp i = ⊥ := by
    simp [NData.MtUp, hsum]
  have hsub : Subsingleton (N.MtUp i) := by
    rw [hup]
    infer_instance
  have hq : Subsingleton (↥(N.MtUp i) ⧸ Submodule.comap (N.MtUp i).subtype (N.MtLow i)) := by
    infer_instance
  unfold NData.etaLoc lenUnit
  rw [Module.length_eq_zero]
  simp

theorem etaJ_le (h : c.Good) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (D.what₂.etaJ j w : ℝ) ≤ ((cut D c).what₂.etaJ j w : ℝ) +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℝ) := by
  classical
  let F : D.nd.Loc → ℚ := fun i => if hk : c.keep i then (cut D c).nd.etaLoc (⟨i, hk⟩ : (cut D c).nd.Loc) else 0
  have hcut : (cut D c).what₂.etaJ j w = ∑ i ∈ D.nd.locs j w, F i := by
    rw [(cut D c).etaJ_tie j w h1 h2]
    show ∑ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = _
    have hF : ∀ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = F i.1 := by
      intro i _
      simp only [F, dif_pos i.2]
    rw [Finset.sum_congr rfl hF, Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_filter_of_ne ?_
    intro i _ hne
    by_contra hk
    exact hne (dif_neg hk)
  have hD := D.etaJ_tie j w h1 h2
  have hpt : ∀ i ∈ D.nd.locs j w, D.nd.etaLoc i ≤ F i +
      (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) * (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    intro i hi
    have hw : D.nd.w i = w := ((D.nd.locs_mem j w i).mp hi).2
    have hl : D.what₂.places.resChar w = D.nd.l i := by
      rw [← hw]
      exact D.nd.w_l i
    rw [hl]
    by_cases hk : c.keep i
    · have hb := eta_le h (⟨i, hk⟩ : (cut D c).nd.Loc)
      simp only [F, dif_pos hk]
      push_cast at hb
      exact hb
    · have hz : D.nd.Zgood i = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        exact fun hne => hk ((h.keep i).mpr hne)
      rw [eta_zero D.nd i hz]
      simp only [F, dif_neg hk, zero_add]
      positivity
  have hQ : D.what₂.etaJ j w ≤ (cut D c).what₂.etaJ j w +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    rw [hD, hcut, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  exact_mod_cast hQ

end UpperTheory.GalC
