import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralSourceTranslationRightMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqOfTwistConditionAStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterTwistUniversalCharAtChosenPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientRowsExteriorDetEqConstMulTopBlockDetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitCardResidueFieldOffExceptionalPlacesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpecSpan

open Classical in

theorem series_sum {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (ω : PairRep S T) {τs : Type} (s : Finset τs)
    (c : τs → ℂ) (f : τs → WO S T → ℂ) (hf : ∀ τ, IsThetaFunO B.F.ψ S T (f τ)) (h : GA D S) (P : PolF D T.rank S.rank) :
    series B.F ω (∑ τ ∈ s, c τ • f τ) h P = ∑ τ ∈ s, c τ • series B.F ω (f τ) h P := by
  have hθ : ∀ s : Finset τs, IsThetaFunO B.F.ψ S T (∑ τ ∈ s, c τ • f τ) := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact GlobalTheory.OrientedHeis.theta_zero
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hf a)) ih
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    funext g
    rw [series_apply]
    change ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT 0 P) 0 = 0
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_zero _ _ _ _ hB.frame.vac.1 hB.frame.vac.2.inf, map_zero]
    rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    funext g
    simp only [series_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (c a • f a + ∑ τ ∈ s, c τ • f τ) P) 0 = c a * ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (f a) P) 0 + ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (∑ τ ∈ s, c τ • f τ) P) 0
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin _ _ _ _ hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ _ (hf a) (hθ s), map_add, map_smul]
    rfl

theorem theta_vecAt {D : D7} {S T : HSp D} {B : Base S T} (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) : IsThetaFunO B.F.ψ S T (B.vecAt Q φ) :=
  GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf (Base.isThetaAt_vecAt hB hQ φ) hB.frame.vac.2.theta

open Classical in

theorem twist_series_mem_span {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ω : PairRep S T)
    (hω : B.IsWeil 1 ω) (t : Twist D Circle) (hQ : B.admitted t.Q) (O : Subring ℂ) (ι : ↥t.Q → Type) [∀ PP, Fintype (ι PP)]
    (a : ∀ PP, ι PP → ℂ) (ha : ∀ PP u, a PP u ∈ O) (g : ∀ PP, ι PP → GL (Fin S.rank) (kP PP.1))
    (loc : ∀ PP : ↥t.Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ)
    (hloc : ∀ PP y, loc PP y = ∑ u, a PP u * flat (t.resC PP.1) (y * (g PP u : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1))))
    (h : GA D S) (P : PolF D T.rank S.rank) :
    twistBy T t.chi (series B.F ω (B.vecAt t.Q loc) h P) ∈ Submodule.span O (B.genSet ω t h P) := by
  let φ : (∀ PP, ι PP) → ∀ PP : ↥t.Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ :=
    fun τ PP y => flat (t.resC PP.1) (y * (g PP (τ PP) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)))
  have hvec : B.vecAt t.Q loc = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.vecAt t.Q (φ τ) := by
    have e1 : B.locFn t.Q loc = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.locFn t.Q (φ τ) := by
      funext y
      simp only [Base.locFn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hloc]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.prod_mul_distrib]
      ring
    change B.F.vecL B.G _ (B.locFn t.Q loc) = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.F.vecL B.G _ (B.locFn t.Q (φ τ))
    rw [e1, map_sum]
    simp only [map_smul]
  rw [hvec, series_sum B hB ω _ _ _ (fun τ => theta_vecAt hB hQ (φ τ)), map_sum]
  refine Submodule.sum_mem _ fun τ _ => ?_
  obtain ⟨hQτ, hsupp, hmove⟩ := GlobalTheory.T.thetaSeries_integralSourceTranslation_right_mul D S T B hB hS ω hω t.Q hQ (fun PP => g PP (τ PP))
  have e2 : series B.F ω (B.vecAt t.Q (φ τ)) h P = series B.F ω (B.vecFlat t) (h * hQτ) P :=
    hmove (fun PP => flat (t.resC PP.1)) h P
  rw [map_smul, e2]
  have hmem : ∏ PP, a PP (τ PP) ∈ O := Subring.prod_mem _ fun PP _ => ha PP (τ PP)
  have e3 : (∏ PP, a PP (τ PP)) • twistBy T t.chi (series B.F ω (B.vecFlat t) (h * hQτ) P) =
      (⟨_, hmem⟩ : O) • twistBy T t.chi (series B.F ω (B.vecFlat t) (h * hQτ) P) := rfl
  rw [e3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hQτ, hsupp, rfl⟩)

end GlobalTheory.SpecSpan

namespace GlobalTheory.SpecSpan

open Classical in

theorem univ_spec {k : Type} [Field k] [Finite k] {r n : ℕ} {C : Type} [AddCommGroup C] [Fintype C]
    [Fintype (Planes k r n)] (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (ν : Multiplicative C →* ℂˣ)
    (g : Planes k r n → GL (Fin n) k) (c : Planes k r n → kˣ)
    (hg : ∀ U y, dU β U y = (c U : k) * (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det)
    (y : Matrix (Fin r) (Fin n) k) :
    ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * ((univCoef β κ a y : ℚ) : ℂ) =
      ∑ U : Planes k r n, ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * (ν (κ (c U)) : ℂ) *
        flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) := by
  have hterm : ∀ U : Planes k r n, ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * (((univTerm β κ y U).coeff a : ℚ) : ℂ) =
      (ν (κ (c U)) : ℂ) * flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) := by
    intro U
    unfold univTerm
    by_cases hC : Compl U.1 y
    · rw [dif_pos hC]
      have hd : dU β U y ≠ 0 := (dU_ne_zero_iff β U y).2 hC
      have hdet : (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det ≠ 0 := by
        intro h0; apply hd; rw [hg, h0, mul_zero]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [Finset.sum_eq_single (Multiplicative.toAdd (κ (Units.mk0 _ hd)))]
      · rw [if_pos rfl, Rat.cast_one, mul_one, flat_of_isUnit (ν.comp κ) (u := Units.mk0 _ hdet) rfl]
        have e : Units.mk0 _ hd = c U * Units.mk0 _ hdet := Units.ext (by simp [hg])
        rw [ofAdd_toAdd, e, map_mul, map_mul, Units.val_mul, MonoidHom.comp_apply]
      · intro a _ ha
        rw [if_neg (Ne.symm ha), Rat.cast_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hC]
      have hd : dU β U y = 0 := by
        by_contra h; exact hC ((dU_ne_zero_iff β U y).1 h)
      have hdet : ¬ IsUnit (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det := by
        rw [isUnit_iff_ne_zero]; intro h0
        rw [hg] at hd
        exact h0 ((mul_eq_zero.1 hd).resolve_left (c U).ne_zero)
      rw [flat_of_not_isUnit _ hdet, mul_zero]
      simp
  have hcoef : ∀ a : C, univCoef β κ a y =
      ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ * ∑ U : Planes k r n, (univTerm β κ y U).coeff a := by
    intro a
    rw [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    congr 1
    exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl
  simp only [hcoef, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, Rat.cast_sum]
  rw [Finset.sum_congr rfl fun U _ => (by rw [mul_assoc, ← hterm U] :
    ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * (ν (κ (c U)) : ℂ) * flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) =
      ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * (((univTerm β κ y U).coeff a : ℚ) : ℂ))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.SpecSpan

namespace GlobalTheory.SpecSpan

theorem specSer_mem_span : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → InRange X i Q →
    ∀ (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      ρ.IsDatum i j b s h P → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) →
      specSer ρ Y i j b k Q M χ h P ∈
        Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q (χ.comp (Y.delU i Q M)) h P) := by
  intro D N X ρ hρ Y hY i j b k Q M χ hT _ s h P _ _
  classical
  have hA : admissibleConjugatePairPlaces X i Q M = Q := GlobalTheory.T.admissibleConjugatePairPlaces_eq_of_twOK Y hY i k Q M χ hT
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D N X ρ hρ i j b k Q (χ.comp (Y.delU i Q M)) hT
  have hS : (Vc D j).SigOK := D.sp.V_sig _
  haveI : ∀ PP : Pl D.host.E, Fintype (Planes (kP PP) (Wc D j).rank (Vc D j).rank) := fun PP => Fintype.ofFinite _
  choose gC cC hgc using fun (PP : Pl D.host.E) (U : Planes (kP PP) (Wc D j).rank (Vc D j).rank) =>
    GlobalTheory.T.quotientRowsExteriorDet_eq_const_mul_topBlockDet (kP PP) (Wc D j).rank (Vc D j).rank (ρ.β j PP) U
  have key : ∀ (Q₀ : Finset (Pl D.host.E)), Q₀ = (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).Q →
      ∀ (loc : ∀ PP : ↥Q₀, Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1) → ℂ)
        (a : ∀ PP : ↥Q₀, Planes (kP PP.1) (Wc D j).rank (Vc D j).rank → ℂ),
        (∀ PP u, a PP u ∈ (ρ.eOk i b k).range) →
        (∀ PP y, loc PP y = ∑ u, a PP u * flat ((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1)
          (y * (gC PP.1 u : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP PP.1)))) →
        twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
          (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt Q₀ loc) h P) ∈
          Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q (χ.comp (Y.delU i Q M)) h P) := by
    intro Q₀ hQ₀
    subst hQ₀
    intro loc a ha hloc
    exact twist_series_mem_span (ρ.B i j b) (hρ.base i j b) hS (ρ.om i j b 1) (hρ.weil_base i j b) _ hadm _
      (fun PP => Planes (kP PP.1) (Wc D j).rank (Vc D j).rank) a ha (fun PP u => gC PP.1 u) loc hloc h P

  let ν : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), Multiplicative (ZMod (X.l i ^ M)) →* ℂˣ := fun PP =>
    (Units.map (ρ.eOk i b k).toMonoidHom).comp (χ.comp (AddMonoidHom.toMultiplicative
      ((spread Y i Q M (ρ.ch i)).comp (AddMonoidHom.single (fun _ : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => ZMod (X.l i ^ M)) PP))))
  have hν : ∀ PP a, (ν PP (Multiplicative.ofAdd a) : ℂ) =
      ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP a))) : (X.Ok i k)ˣ) : X.Ok i k) := by
    intro PP a; rfl
  have hres : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)),
      (ν PP).comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1) = (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 := by
    intro PP
    ext x
    rw [GlobalTheory.T.residueCharacter_twist_universalChar_at_chosen_place ρ hρ Y hY i b k Q M χ hT PP x, MonoidHom.comp_apply, ← hν, ofAdd_toAdd]
  have hnS : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), PP.1 ∉ X.S0 i := fun PP =>
    Finset.disjoint_left.1 hT.2.1 (admissibleConjugatePairPlaces_subset i Q M (mem_half.1 PP.2).1)
  let qi : Pl D.host.E → ℂ := fun PP => ((Nat.card (kP PP) : ℂ) ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)))⁻¹
  have hqi : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), qi PP.1 ∈ (ρ.eOk i b k).range := by
    intro PP
    obtain ⟨w, hw⟩ := GlobalTheory.T.isUnit_card_residueField_off_exceptional_places X i k PP.1 (hnS PP)
    refine ⟨((w⁻¹ ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)) : (X.Ok i k)ˣ) : X.Ok i k), ?_⟩
    have e : ρ.eOk i b k (w : X.Ok i k) = (Nat.card (kP PP.1) : ℂ) := by rw [hw, map_natCast]
    have e' : ρ.eOk i b k (w : X.Ok i k) ≠ 0 := by
      intro h0; exact w.ne_zero ((map_eq_zero_iff _ (ρ.eOk_injective i b k)).1 h0)
    have e2 : ρ.eOk i b k ((w⁻¹ : (X.Ok i k)ˣ) : X.Ok i k) = (Nat.card (kP PP.1) : ℂ)⁻¹ := by
      rw [← e]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    show _ = ((Nat.card (kP PP.1) : ℂ) ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)))⁻¹
    rw [Units.val_pow_eq_pow_val, map_pow, e2, inv_pow]
  refine key _ (by show half _ _ = half _ _; rw [hA]) (specLoc ρ Y i j b k Q M χ)
    (fun PP U => qi PP.1 * (ν PP ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 (cC PP.1 U)) : ℂ)) ?_ ?_
  · intro PP U
    refine Subring.mul_mem _ (hqi PP) ?_
    exact ⟨_, rfl⟩
  · intro PP y
    have := univ_spec (ρ.β j PP.1) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1) (ν PP) (gC PP.1) (cC PP.1)
      (hgc PP.1) y
    rw [hres PP] at this
    exact this
end GlobalTheory.SpecSpan

end
