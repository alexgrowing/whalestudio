import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseChangeInertUnramified
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DefiniteFormInstances

noncomputable section

namespace GlobalTheory.BaseChangeExistsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Matrix
open GlobalTheory.IndefiniteRowSideFullHecke

section Definite

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem emb_hD (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (x : S.V) :
    τ (S.hD x x) = star (fun a => τ (S.frame.repr x a)) ⬝ᵥ
      (S.gram.map τ *ᵥ fun a => τ (S.frame.repr x a)) := by
  rw [HSpace.hD, hT_expand]
  simp only [map_sum, map_mul, hτ, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply,
    mul_assoc]
  rfl

theorem denseRange_emb [IsTotallyComplex E] (τ : E →+* ℂ) : DenseRange τ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure τ.fieldRange) with h | h
  · exfalso
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : τ x ∈ τ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    simp
  · have : closure (Set.range τ) = Set.univ := congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h
    exact dense_iff_closure_eq.2 this

theorem closed_of_coords [IsTotallyComplex E] (S : HSpace E) (τ : E →+* ℂ) {C : Set (Fin S.rank → ℂ)}
    (hC : IsClosed C) (h : ∀ x : S.V, (fun a => τ (S.frame.repr x a)) ∈ C) (y : Fin S.rank → ℂ) : y ∈ C := by
  have hd : DenseRange (Pi.map fun (_ : Fin S.rank) => (τ : E → ℂ)) :=
    DenseRange.piMap fun _ => denseRange_emb τ
  refine hd.induction_on y hC fun v => ?_
  have := h (S.frame.equivFun.symm v)
  have e : (fun a => τ (S.frame.repr (S.frame.equivFun.symm v) a)) =
      Pi.map (fun (_ : Fin S.rank) => (τ : E → ℂ)) v := by
    funext a
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  rwa [e] at this

theorem coords_ne_zero (S : HSpace E) (τ : E →+* ℂ) {x : S.V} (hx : x ≠ 0) :
    (fun a => τ (S.frame.repr x a)) ≠ 0 := by
  intro h
  apply hx
  rw [← S.frame.repr.map_eq_zero_iff]
  ext a
  simpa using congrFun h a

theorem continuous_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun y : Fin n → ℂ => (star y ⬝ᵥ (M *ᵥ y)).re := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem sig_pos_iff [IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (S.rank, 0) ↔ ∀ x : S.V, x ≠ 0 → 0 < (τ (S.hD x x)).re := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_pos _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, 0 ≤ (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re := fun y =>
      closed_of_coords S τ (isClosed_le continuous_const (continuous_quad (S.gram.map τ))) (fun x => by
        show (0 : ℝ) ≤ _
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hq : (S.sig τ).2 = 0 := by
      by_contra hq
      have h1 := hall (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext (by simp only; omega) hq

theorem sig_neg_iff [IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (0, S.rank) ↔ ∀ x : S.V, x ≠ 0 → (τ (S.hD x x)).re < 0 := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_neg _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re ≤ 0 := fun y =>
      closed_of_coords S τ (isClosed_le (continuous_quad (S.gram.map τ)) continuous_const) (fun x => by
        show _ ≤ (0 : ℝ)
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hp : (S.sig τ).1 = 0 := by
      by_contra hp
      have h1 := hall (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext hp (by simp only; omega)

theorem isDefinite_iff (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (S : HSpace E) (hS : S.SigOK) :
    S.IsDefinite ↔ DefiniteFormInstances.IsDefiniteForm S := by
  have := hc.1
  exact forall_congr' fun τ =>
    or_congr (sig_pos_iff S hS τ (hc.2.1 τ)) (sig_neg_iff S hS τ (hc.2.1 τ))

end Definite

theorem unram_of_cm (D : D7) (hc : @CMData D.host.F D.host.E _ _ _ _ D.host.cmStar _) (w : PlE D.host) :
    Algebra.IsUnramifiedAt (𝓞 D.host.F) w.asIdeal := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  exact Algebra.unramified_iff_forall.1 hU ⟨w.asIdeal, w.isPrime⟩

theorem notOverTwo_iff (D : D7) (w : PlE D.host) :
    (2 : 𝓞 D.host.E) ∉ w.asIdeal ↔ w ∉ placesOver D.host.E 2 := by
  simp [placesOver]

theorem unimodularAt (D : D7) (j : ℕ) (w : PlE D.host) : letI := D.host.cmStar
    Formalism.HermitianLatticesTheory.IsUnimodularAt (DefiniteFormInstances.Vsp D j).hT w.asIdeal (DefiniteFormInstances.Vsp D j).L0 := by
  letI := D.host.cmStar
  have hstar : ∀ r : 𝓞 D.host.E, star (algebraMap (𝓞 D.host.E) D.host.E r) ∈
      Set.range (algebraMap (𝓞 D.host.E) D.host.E) := fun r =>
    ⟨RingOfIntegers.mapRingEquiv (D.host.conj : D.host.E ≃+* D.host.E) r,
      (bridge_star_holds D.R D.host _).symm⟩
  exact (Formalism.HermitianLatticesTheory.locDual _ _ _ _ (DefiniteFormInstances.Vsp D j).herm hstar _ (DefiniteFormInstances.Vsp D j).standardTuple_isLattice.fg).2.1
    (DefiniteFormInstances.Vsp D j).baseLattice_isUnimodular _ w.isMaximal

theorem standing_iff_hyp (D : D7) (j : ℕ) : BaseChangeInertUnramified.Standing D j ↔ DefiniteFormInstances.Hyp D j := by
  letI := D.host.cmStar
  constructor
  · intro h
    exact ⟨h.cm, h.degree, fun w hw => (notOverTwo_iff D w).1 (h.inertOdd w hw),
      (D.sp.V j).rank_eq.trans h.rank, (isDefinite_iff h.cm.cmUnram _ (D.sp.V_sig j)).1 h.definite,
      fun w _ => unimodularAt D j w⟩
  · rintro ⟨h1, h2, h3, h4, h5, -⟩
    exact ⟨h1, unram_of_cm D h1, h2, fun w hw => (notOverTwo_iff D w).2 (h3 w hw),
      (D.sp.V j).rank_eq.symm.trans h4, (isDefinite_iff h1.cmUnram _ (D.sp.V_sig j)).2 h5⟩

theorem isSplitPl_of_two_mem {R : Ranks} (H : Host R) (w : PlE H) (h2 : (2 : 𝓞 H.E) ∈ w.asIdeal) :
    IsSplitPl H w := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 8 * k := ⟨(H.d + 1) / 8, by have := H.hyp.2.2.2.1; omega⟩
  set c : H.E := (1 + H.sqrtMinusD) / 2 with hcdef
  have hc : c ^ 2 - c + ((2 * k : ℕ) : H.E) = 0 := by
    have e : ((H.d : ℕ) : H.E) + 1 = 8 * (k : H.E) := by exact_mod_cast hk
    have hs := H.sqrtMinusD_sq
    simp only [hcdef]
    push_cast
    linear_combination (1 / 4 : H.E) * hs - (1 / 4 : H.E) * e
  have hint : IsIntegral ℤ c :=
    ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k : ℕ) : ℤ), by monicity!, by
      simpa [Polynomial.eval₂_sub, Polynomial.eval₂_add] using hc⟩
  have hconj : H.conj c = 1 - c := by
    simp only [hcdef, map_div₀, map_add, map_one, H.conj_sqrtMinusD, map_ofNat]
    ring
  let ω : 𝓞 H.E := ⟨c, hint⟩
  have hω : (ω : H.E) = c := rfl
  have hprod : ω * (1 - ω) = 2 * (k : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    push_cast at hc ⊢
    simp only [map_mul, map_sub, map_one, map_ofNat, map_natCast]
    change c * (1 - c) = _
    linear_combination -hc
  have hone : ∀ a : 𝓞 H.E, a ∈ w.asIdeal → 1 - a ∉ w.asIdeal := fun a ha hb =>
    w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.add_mem ha hb))
  have hmem : ω * (1 - ω) ∈ w.asIdeal := hprod ▸ w.asIdeal.mul_mem_right _ h2
  rcases w.isPrime.mem_or_mem hmem with h | h
  · refine ⟨ω, h, fun y hy => ?_⟩
    have : y = 1 - ω := RingOfIntegers.ext (by rw [hy, hω, hconj]; rfl)
    rw [this]
    exact hone _ h
  · refine ⟨1 - ω, h, fun y hy => ?_⟩
    have : y = 1 - (1 - ω) := RingOfIntegers.ext (by
      rw [hy]
      change H.conj (1 - c) = 1 - (1 - c)
      rw [map_sub, map_one, hconj])
    rw [this]
    exact hone _ h

theorem standing_holds (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : BaseChangeInertUnramified.Standing D j := by
  letI := D.host.cmStar
  refine ⟨D.sp.cm, unram_of_cm D D.sp.cm, ?_, fun w hw h => hw (isSplitPl_of_two_mem _ w h),
    D.sp.V_rank j h1 h2, fun τ => ?_⟩
  · rw [D.host.finrank_hostF]
    have := D.R.ord_pos
    omega
  · rw [factVSig D.R D.host.F D.sp j h1 h2 τ, D.sp.V_rank j h1 h2]
    split_ifs <;> simp

section Concl

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem spherical_iff (B : NBC A) (j : ℕ) (π : B.AU j) :
    BaseChangeInertUnramified.SphericalAtInert B j π ↔ DefiniteFormInstances.SphericalInert B j π := Iff.rfl

theorem isBaseChange_iff (B : NBC A) (j : ℕ) (π : B.AU j) (P : List (Part A.CG)) :
    BaseChangeInertUnramified.IsBaseChange B j π P ↔ DefiniteFormInstances.IsBaseChange B j π P := by
  constructor
  · intro h
    exact ⟨fun p hp => ⟨(h.parts.discrete p hp).1, (h.parts.discrete p hp).2, h.parts.selfDual p hp⟩,
      h.parts.distinct, h.rank, h.split, fun w hw => ⟨h.inertUnr w hw, h.inertSat w hw⟩, h.infChar⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨fun p hp => ⟨(h1 p hp).1, (h1 p hp).2.1⟩, fun p hp => (h1 p hp).2.2, h2⟩, h3, h4,
      fun w hw => (h5 w hw).1, fun w hw => (h5 w hw).2, h6⟩

end Concl

theorem atRecordGuarded_iff (D : D7) : BaseChangeInertUnramified.AtRecordGuarded D ↔ DefiniteFormInstances.KappaDegreeStatement D :=
  forall_congr' fun j => forall_congr' fun _ => forall_congr' fun _ =>
    imp_congr (standing_iff_hyp D j) <| forall_congr' fun π =>
      imp_congr (spherical_iff D.nbc j π) (exists_congr fun P => isBaseChange_iff D.nbc j π P)

theorem atRecord_iff (D : D7) : BaseChangeInertUnramified.AtRecord D ↔ DefiniteFormInstances.KappaDegreeStatement D :=
  (BaseChangeInertUnramified.atRecord_iff_guarded D (standing_holds D)).trans (atRecordGuarded_iff D)

theorem forFamily_iff {eps : ℝ} (Fm : FamP eps) : BaseChangeInertUnramified.ForFamily Fm ↔ DefiniteFormInstances.KudlaFamilyStatement Fm :=
  forall_congr' fun x => forall_congr' fun _ => forall_congr' fun i => atRecord_iff (Fm.D x i)

theorem baseChangeClosed_iff (𝒞 : FamClass) : BaseChangeInertUnramified.BaseChangeClosed 𝒞 ↔ DefiniteFormInstances.ClosedAbsoluteShare 𝒞 :=
  ⟨fun h => Closed.imp h fun Fm _ _ => (forFamily_iff Fm).1,
    fun h => Closed.imp h fun Fm _ _ => (forFamily_iff Fm).2⟩

theorem stmtClosedTied_iff (𝒞 : FamClass) :
    DefiniteFormInstances.ClosedFamilySpectrumCondition 𝒞 ↔ BaseChangeInertUnramified.BaseChangeClosed fun Fm => 𝒞 Fm ∧ DefiniteFormInstances.SpectrumTie Fm :=
  (baseChangeClosed_iff _).symm

end GlobalTheory.BaseChangeExistsCompare

end
