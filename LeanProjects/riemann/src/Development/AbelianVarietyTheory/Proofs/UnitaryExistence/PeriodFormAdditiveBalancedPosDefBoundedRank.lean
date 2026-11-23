import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealPosOfDiscrete
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEqSmulOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphicStatement

noncomputable section

namespace GlobalTheory.PeriodLaws

section Valued

open Formalism.MainNotions.DIV.Cons

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_le_one_of_integral {x : C} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨q, hq, hqx⟩ := hx
  have hx0 : 0 < ‖x‖ := one_pos.trans h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at hqx
  have h1 : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ C (q.coeff i) * x ^ i‖ < ‖x‖ ^ q.natDegree := by
    rcases Finset.eq_empty_or_nonempty (Finset.range q.natDegree) with he | he
    · rw [he]; simpa using pow_pos hx0 _
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty he
        (fun i => algebraMap ℤ C (q.coeff i) * x ^ i)
      refine hle.trans_lt ?_
      rw [norm_mul, norm_pow]
      refine (mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_intCast_le_one C _)).trans_lt ?_
      exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  rw [eq_neg_of_add_eq_zero_left hqx, norm_neg, norm_pow] at h1
  exact lt_irrefl _ h1

theorem dvd_of_norm_le {a b : intO C} (ha : a ≠ 0) (h : ‖(b : C)‖ ≤ ‖(a : C)‖) : a ∣ b := by
  have ha' : (a : C) ≠ 0 := fun e => ha (Subtype.ext e)
  refine ⟨⟨(b : C) / a, ?_⟩, Subtype.ext ?_⟩
  · change ‖(b : C) / a‖ ≤ 1
    rw [norm_div]
    exact div_le_one_of_le₀ h (norm_nonneg _)
  · change (b : C) = a * (b / a)
    field_simp

theorem isFractionRing_intO : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · push_neg at h
    refine ⟨1, ⟨z⁻¹, ?_⟩, by rw [map_one, one_div]; exact (inv_inv z).symm⟩
    change ‖z⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ h.le

end Valued

section Geometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.LieEigen Matrix
open Formalism.MainNotions.DIV.Cons GlobalTheory.ToricRank
open scoped CategoryTheory.Obj

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out in

theorem finrank_le_of_lieMult_valued {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [IsDomain O] [StarRing O] [Module.Finite ℤ O]
    [Module O D.toPre.X] {oD : D.OAct O} {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct)
    {F : Type} [NormedField F] [IsUltrametricDist F] (f : R →+* intO F)
    (hf : ∀ a ∈ maximalIdeal R, ‖((f a : intO F) : F)‖ < 1) {τ : O →+* F}
    (hτ : Function.Injective τ) {N : ℕ} (hN : LieMult aG (spMap ((intO F).subtype.comp f)) τ N) :
    Module.finrank O D.toPre.X ≤ N := by
  classical
  have := U.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis G U.smooth
  obtain ⟨ρ, hρ⟩ := exists_action hv aG
  obtain ⟨v', ρ', hv', hρ', hM⟩ := exists_action_pullback hv hρ ((intO F).subtype.comp f)
  have hk := isLinearPullback_pullback aG (spMap ((intO F).subtype.comp f))
  rw [← finrank_of_lieMult hk.1 hv' hk.2 hρ' hN]
  let V := intO F
  have : IsFractionRing V F := isFractionRing_intO
  let : Algebra R V := f.toAlgebra
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ1 : ‖((f π : intO F) : F)‖ < 1 := hf π hπ.not_isUnit
  let τV : O →+* V := τ.codRestrict V fun a =>
    norm_le_one_of_integral (map_isIntegral_int τ (Algebra.IsIntegral.isIntegral a))
  let b := Module.finBasis ℤ D.toPre.X
  have : Module.Finite O D.toPre.X := .of_restrictScalars_finite ℤ _ _
  obtain ⟨φ⟩ := ConstBasis.nonempty_basis_eigenHom (X := D.toPre.X) (τ.comp (starRingEnd O))
    (hτ.comp star_injective)
  refine le_finrank_eigenSub (V := V) π (fun h => ?_) (fun c hc => ?_) τV
    (fun a => (LinearMap.toMatrix' (ρ a))ᵀ) ρ' hM star b (fun k => (φ k).1)
    (φ.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _))
    (fun k a x => ((φ k).2 _ x).trans (congrArg (τ · * _) (star_star a))) fun n => ?_
  · obtain ⟨w, hw⟩ := h.exists_right_inv
    have h₁ : ‖((f π : intO F) : F)‖ * ‖(w : F)‖ = 1 := by
      rw [← norm_mul]
      exact (congrArg (fun z : V => ‖(z : F)‖) hw).trans norm_one
    have h₂ : ‖(w : F)‖ ≤ 1 := w.2
    exact ((mul_le_of_le_one_right (norm_nonneg _) h₂).trans_lt hπ1).ne' h₁.symm
  · have hc' : 0 < ‖(c : F)‖ := norm_pos_iff.2 fun e => hc (Subtype.ext e)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc' hπ1
    exact ⟨n, dvd_of_norm_le hc ((norm_pow _ n).trans_le hn.le)⟩
  · obtain ⟨C, D', hCD, hC⟩ := exists_matrix_level U hl hv hρ b n
    refine ⟨C, D', hCD, fun a k j => Ideal.mem_span_singleton.1 ?_⟩
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact hC a k j

end Geometry

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_le_of_dvr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) [IsDiscreteValuationRing A.R] :
    ∃ ρ : ℕ, Module.finrank ℤ A.Ylat = 2 * (Module.finrank ℚ E / 2) * ρ ∧ ρ ≤ Dw.p ∧ ρ ≤ Dw.q := by
  let := H.starRing
  let F : Type := ↥C.S
  obtain ⟨b, hb⟩ := Spec.map_surjective (P.y ≫ pullback.fst _ _ ≫ Xo.s)
  have hdet := (Y.oF.geom F P.y b.hom hb.symm).1
  have key : ∀ (τ : 𝓞 E →+* F) (n : ℕ), Function.Injective τ → LieMult Y.oF.t.act P.y τ n →
      Module.finrank (𝓞 E) A.U.D.toPre.X ≤ n := fun τ n hτ hn => by
    refine finrank_le_of_lieMult_valued A.U.U.toUnifPre A.U.lin A.f A.f_loc hτ ?_
    rw [LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ Y.m.cart Y.m.act] at hn
    rw [LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ A.m.cart A.m.act]
    have e : spMap ((intO F).subtype.comp A.f) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
      refine Eq.trans ?_ P.ext
      rw [← A.fac, ← Category.assoc]
      exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO F).subtype))
    rw [e]
    exact hn
  let τ₀ : 𝓞 E →+* F := (IsAlgClosed.lift (R := ℚ) (S := E) (M := F)).toRingHom.comp (algebraMap _ E)
  have h₀ : Function.Injective τ₀ :=
    (IsAlgClosed.lift (R := ℚ) (S := E) (M := F)).injective.comp RingOfIntegers.coe_injective
  have h₁ : Function.Injective (τ₀.comp H.bar.toRingHom) := h₀.comp H.bar.injective
  have e₁ : τ₀.comp H.bar.toRingHom H.rt = -τ₀ H.rt := by
    rw [← map_neg, ← HostModel.bar_rt]; rfl
  have hsq : τ₀ H.rt ^ 2 = b.hom (baseKA l).ρ ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, (baseKA l).ρ_sq]; simp
  have hne : -τ₀ H.rt ≠ τ₀ H.rt := fun h => by
    have h2 : τ₀ H.rt ^ 2 = 0 := by rw [neg_eq_self.1 h]; simp
    rw [← map_pow, H.rt_sq] at h2
    exact H.d_prime.ne_zero (by simpa using h2)
  refine ⟨Module.finrank (𝓞 E) A.U.D.toPre.X, ?_, ?_⟩
  · have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    rw [ToricRank.finrank_int_eq E]
    congr 1
    omega
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨key _ _ h₀ ((hdet _).1 h), key _ _ h₁ ((hdet _).2 (by rw [e₁, ← h]; exact hne))⟩
    · have h' : -τ₀ H.rt = b.hom (baseKA l).ρ := by rw [h, neg_neg]
      exact ⟨key _ _ h₁ ((hdet _).1 (e₁.trans h')), key _ _ h₀ ((hdet _).2 (by rw [← h']; exact hne.symm))⟩

theorem period_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∀ A : DatAt Y P, (∀ a a' b, A.beta (a + a') b = A.beta a b + A.beta a' b) ∧ (∀ (x : 𝓞 E) a b, A.beta (x • a) b = A.beta a (H.bar x • b)) ∧ (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.Ylat), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * A.beta (b i) (b k)) ∧ ∃ ρ : ℕ, Module.finrank ℤ A.Ylat = 2 * (Module.finrank ℚ E / 2) * ρ ∧ ρ ≤ Dw.p ∧ ρ ≤ Dw.q := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P hp T g ιT hT hg hloc hfac A
  obtain ⟨A₀, ⟨_, -⟩, -⟩ := GlobalTheory.T.exists_degeneration_data_algebraic_point_model E H Dw l Xo c O β Y p C P hp T g ιT hT hg hloc hfac
  obtain ⟨hψ₀, e, he⟩ := GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C P hp T g ιT hT hg hloc hfac A₀ A
  obtain ⟨hψ, -⟩ := GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C P hp T g ιT hT hg hloc hfac A A
  let e' : A₀.Ylat ≃ₗ[ℤ] A.Ylat := e.toAddEquiv.toIntLinearEquiv
  refine ⟨(BetaAdd.main A.R A.U.D _ _ p A.normal (fun a => (A.f a).2) hψ).1,
    PeriodBalance.betaAt_balanced E H A.R A.t A.U _ _ p A.normal (fun a => (A.f a).2) hψ, ?_, ?_⟩
  · obtain ⟨ι, _, b, hb⟩ := PeriodFormPos.betaAt_pos A₀.R A₀.U.D _ ((intO ↥C.S).subtype.comp A₀.f) p hp.one_lt
      A₀.f_loc (fun a => (A₀.f a).2) hψ₀
    refine ⟨ι, inferInstance, b.map e', fun x hx => (hb x hx).trans_eq ?_⟩
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (x i * x k * ·) (he (b i) (b k)).symm
  · rw [← e'.finrank_eq]
    exact rank_le_of_dvr A₀

end GlobalTheory.PeriodLaws
