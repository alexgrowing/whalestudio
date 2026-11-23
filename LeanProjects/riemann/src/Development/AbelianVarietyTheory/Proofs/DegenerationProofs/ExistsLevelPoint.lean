import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem exists_lev_norm : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ e, ∀ x ∈ u.lev e, ‖(x : PadicAlgCl p)‖ ≤ r ^ (e + 1) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  refine ⟨‖(u.j π : PadicAlgCl p)‖, norm_nonneg _, ?_, fun e x hx => ?_⟩
  · by_contra h
    have h0 : algebraMap u.V (FractionRing u.V) π ≠ 0 := fun h₀ =>
      hπ.ne_zero (IsFractionRing.injective u.V (FractionRing u.V) (h₀.trans (map_zero _).symm))
    obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V _ π)⁻¹).1 (by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h))
    refine hπ.not_isUnit (IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_))
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]
  · rw [ThetaSys.Real.UTest.lev, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_pow]
    show ‖(a : PadicAlgCl p) * (u.j π : PadicAlgCl p) ^ (e + 1)‖ ≤ _
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) ((mem_OO_iff _).1 a.2)

theorem lev_ne_top (e : ℕ) : u.lev e ≠ ⊤ := fun h => by
  obtain ⟨r, h0, h1, h2⟩ := exists_lev_norm u
  have := h2 e 1 (h ▸ trivial)
  have h3 : r ^ (e + 1) < 1 := pow_lt_one₀ h0 h1 (Nat.succ_ne_zero e)
  simp only [OneMemClass.coe_one, norm_one] at this
  linarith

instance nontrivial_lev (e : ℕ) : Nontrivial (OO p ⧸ u.lev e) := Ideal.Quotient.nontrivial_iff.2 (lev_ne_top u e)

instance isLocalRing_lev (e : ℕ) : IsLocalRing (OO p ⧸ u.lev e) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance isLocalHom_lev (e : ℕ) : IsLocalHom (Ideal.Quotient.mk (u.lev e)) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

theorem norm_eq_one_of_isUnit {e : ℕ} {x : OO p} (h : IsUnit (Ideal.Quotient.mk (u.lev e) x)) :
    ‖(x : PadicAlgCl p)‖ = 1 := by
  obtain ⟨y, hy⟩ := (isUnit_of_map_unit _ x h).exists_right_inv
  have h1 : ‖(x : PadicAlgCl p)‖ * ‖(y : PadicAlgCl p)‖ = 1 := by
    rw [← norm_mul, show (x : PadicAlgCl p) * y = 1 from congrArg Subtype.val hy, norm_one]
  have hx := (mem_OO_iff _).1 x.2
  have hy := (mem_OO_iff _).1 y.2
  have := norm_nonneg (x : PadicAlgCl p)
  nlinarith

theorem mk_cpt (e : ℕ) : spMap (Ideal.Quotient.mk (u.lev e)) (cpt _) = cpt (OO p) :=
  IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (u.lev e))

theorem exists_level_point (c : Sp (OO p) ⟶ u.G.left) (hc : c ≫ u.G.hom = spMap u.j) (e : ℕ) :
    ∃ ce : Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left,
      ce ≫ (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c := by
  refine ⟨pullback.lift (spMap (Ideal.Quotient.mk (u.lev e)) ≫ c)
    (spMap (Ideal.quotientMap (u.lev e) u.j Ideal.le_comap_map)) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, hc]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem lev_succ_le (e : ℕ) : u.lev (e + 1) ≤ u.lev e :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))

section
variable (c : Sp (OO p) ⟶ u.G.left) (b₀ : Sp (OO p) ⟶ u.D.toPre.P.A.left)
  (ce : ∀ e, Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left)
  (hce : ∀ e, ce e ≫ fGl (IsLocalRing.maximalIdeal u.V) u.G e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c)
  (hbe : ∀ e, ce e ≫ pGl u.U.toUnifPre e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀)
  {jL : u.U.LG.L.ι} {jM : u.D.toPre.P.L.ι} (hL : ⊤ ≤ c ⁻¹ᵁ u.U.LG.L.U jL) (hM : ⊤ ≤ b₀ ⁻¹ᵁ u.D.toPre.P.L.U jM)
include hce hbe hL hM

theorem top_le_wchart (e : ℕ) {T : Type} [CommRing T] (r : Sp T ⟶ Sp (OO p ⧸ u.lev e)) :
    ⊤ ≤ (r ≫ ce e) ⁻¹ᵁ ((u.D.toPre.P.L.pull (u.U.gt e).pG.left).U (fun _ => jM) ⊓
      (u.U.LG.L.pull (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left).U (fun _ => jL)) := fun z _ =>
  ⟨mem_pull.2 ((congrArg (fun q => q (r z) ∈ u.D.toPre.P.L.U jM) (hbe e)).mpr (top_le_comp hM _ trivial)),
    mem_pull.2 ((congrArg (fun q => q (r z) ∈ u.U.LG.L.U jL) (hce e)).mpr (top_le_comp hL _ trivial))⟩

theorem top_le_wchart' (e : ℕ) :
    ⊤ ≤ (ce e) ⁻¹ᵁ ((u.D.toPre.P.L.pull (u.U.gt e).pG.left).U (fun _ => jM) ⊓
      (u.U.LG.L.pull (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left).U (fun _ => jL)) :=
  top_le_wchart u c b₀ ce hce hbe hL hM e (𝟙 _)

theorem factor_wVal (e : ℕ) :
    Ideal.Quotient.factor (lev_succ_le u e) (wVal u.U.toUnifPre (e + 1) (ce (e + 1)) jL jM) =
      wVal u.U.toUnifPre e (ce e) jL jM := by
  have := fstG_mono (I := IsLocalRing.maximalIdeal u.V) (G := u.G) (e + 1)
  have ht := top_le_wchart' u c b₀ ce hce hbe hL hM e
  have e₁ : spMap (Ideal.Quotient.factor (lev_succ_le u e)) ≫ ce (e + 1) =
      ce e ≫ thickMap u.V (IsLocalRing.maximalIdeal u.V) e u.G := by
    rw [← cancel_mono (fstG (IsLocalRing.maximalIdeal u.V) (e + 1) u.G).left, Category.assoc, Category.assoc]
    refine (congrArg (_ ≫ ·) (hce (e + 1))).trans (Eq.trans ?_ ((hce e).symm.trans
      (congrArg (_ ≫ ·) (thickMap_comp_fGl _ e u.G).symm)))
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  have e₂ : Ideal.Quotient.factor (lev_succ_le u e) (wVal u.U.toUnifPre (e + 1) (ce (e + 1)) jL jM) =
      wVal u.U.toUnifPre (e + 1) (spMap (Ideal.Quotient.factor (lev_succ_le u e)) ≫ ce (e + 1)) jL jM :=
    (valR_spMap _ _ _ (top_le_wchart' u c b₀ ce hce hbe hL hM (e + 1)) _).symm
  apply toStkA_injective
  rw [e₂]
  refine (toStkA_valR _ _ _ (top_le_wchart u c b₀ ce hce hbe hL hM (e + 1) _) _).trans
    (Eq.trans ?_ (toStkA_valR _ _ _ ht _).symm)
  have h := wv_comp_thickMap (U := u.U.toUnifPre) e (ce e) (cpt _) jM jL (mem_pull.1 (ht trivial).1) (mem_pull.1 (ht trivial).2)
  rw [← e₁] at h
  exact congrArg Units.val h

theorem exists_omega [ArithBase o Ω] (hc : c ≫ u.G.hom = spMap u.j) : ∃ (ω : PadicAlgCl p) (ωe : ℕ → OO p), ω ≠ 0 ∧
    Tendsto (fun e => (ωe e : PadicAlgCl p)) atTop (𝓝 ω) ∧
    ∀ e, Ideal.Quotient.mk (u.lev e) (ωe e) = wVal u.U.toUnifPre e (ce e) jL jM := by
  obtain ⟨-, -, -, K₀, hK₀, hK₀'⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  have := u.U.smooth
  obtain ⟨K, hK, hval⟩ := exists_finite_values u.j K₀ (fun x => by
    show _ ∈ (K₀ : Set (PadicAlgCl p))
    rw [hK₀']; exact ⟨_, rfl⟩) u.G.hom c hc
  have hcl : ∀ e, IsClosedImmersion (fGl (IsLocalRing.maximalIdeal u.V) u.G e) := fun e =>
    haveI : IsClosedImmersion (thick u.V (IsLocalRing.maximalIdeal u.V) e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    inferInstanceAs (IsClosedImmersion (pullback.fst u.G.hom (thick u.V (IsLocalRing.maximalIdeal u.V) e)))
  choose U' f' hU' hf' using fun e => exists_lift_valR (Ideal.Quotient.mk (u.lev e)) _ c (ce e) (hce e) _
    (top_le_wchart' u c b₀ ce hce hbe hL hM e) ((u.U.w e).s (fun _ => jM, fun _ => jL)).val
  have hw : ∀ e, Ideal.Quotient.mk (u.lev e) (valR c (U' e) (f' e)) = wVal u.U.toUnifPre e (ce e) jL jM := hf'
  obtain ⟨r, h0, h1, h2⟩ := exists_lev_norm u
  obtain ⟨ω, hω⟩ := exists_tendsto K h1 (fun e => (valR c (U' e) (f' e) : OO p)) (fun e => hval _ (hU' e) _)
    fun e => h2 e (valR c (U' (e + 1)) (f' (e + 1)) - valR c (U' e) (f' e)) (by
      rw [← Ideal.Quotient.eq, hw e, ← factor_wVal u c b₀ ce hce hbe hL hM e, ← hw (e + 1),
        Ideal.Quotient.factor_mk])
  refine ⟨ω, _, fun h => ?_, hω, hw⟩
  have h3 := hω.norm
  have h4 : ∀ e, ‖((valR c (U' e) (f' e) : OO p) : PadicAlgCl p)‖ = 1 := fun e =>
    norm_eq_one_of_isUnit u (e := e) (by
      rw [hw]; exact isUnit_valR _ _ (top_le_wchart' u c b₀ ce hce hbe hL hM e) _)
  simp only [h4, h, norm_zero] at h3
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h3)

end

theorem comp_Oφ_id {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) : x.left ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ x χ k :=
  (WeightPf.Oφ_comp x (𝟙 _) χ k).trans (by rw [Category.comp_id])

theorem level_Oφ (b₀ : Sp (OO p) ⟶ u.D.toPre.P.A.left) {e : ℕ}
    (ce : Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left)
    (hbe : ce ≫ pGl u.U.toUnifPre e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀) (χ : u.D.toPre.X) (i : Fin 4) :
    ce ≫ Oφl u.U.toUnifPre e χ i = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i := by
  rw [← Category.assoc, ← hbe, Category.assoc]
  exact congrArg (ce ≫ ·) (comp_Oφ_id u.D.toPre (u.U.gt e).pG χ i).symm

theorem hasSum_integral (c : Sp (OO p) ⟶ u.G.left) (b₀ : Sp (OO p) ⟶ u.D.toPre.P.A.left)
    (ce : ∀ e, Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left)
    (hce : ∀ e, ce e ≫ fGl (IsLocalRing.maximalIdeal u.V) u.G e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c)
    (hbe : ∀ e, ce e ≫ pGl u.U.toUnifPre e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀)
    {jL : u.U.LG.L.ι} (hL : ⊤ ≤ c ⁻¹ᵁ u.U.LG.L.U jL) (d : u.D.toPre.P.A.left → u.D.toPre.P.L.ι)
    (hd : ∀ y, y ∈ u.D.toPre.P.L.U (d y)) (x : u.D.toPre.X → OO p)
    (hx : ∀ e χ, Ideal.Quotient.mk (u.lev e) (x χ) = valR (ce e) _
      (((u.U.gt e).t χ).s (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _)))).val)
    (ω : PadicAlgCl p) (ωe : ℕ → OO p) (hω : Tendsto (fun e => (ωe e : PadicAlgCl p)) atTop (𝓝 ω))
    (hωe : ∀ e, Ideal.Quotient.mk (u.lev e) (ωe e) = wVal u.U.toUnifPre e (ce e) jL (d (b₀ (cpt _))))
    {k : ℕ} (σ : H0 u.U.LG.L k) (f : ∀ α, u.D.toPre.SecB k α) (hE : ∀ e, u.U.toUnifPre.ExpandsAt e k σ f) :
    HasSum (fun α => ((valR b₀ _ ((f α).f (fun i => d ((b₀ ≫ u.D.toPre.famφB α i) (cpt _)))) * x α : OO p) :
      PadicAlgCl p)) (ω ^ k * (secVal u.U.toUnifPre σ c jL : OO p)) := by
  obtain ⟨r, h0, h1, h2⟩ := exists_lev_norm u
  refine hasSum_of_levels h0 h1 _ (fun e => ((ωe e ^ k * secVal u.U.toUnifPre σ c jL : OO p) : PadicAlgCl p)) _
    ((hω.pow k).mul_const _) fun e => ?_
  obtain ⟨F, hF⟩ := expandsAt_val u.U.toUnifPre e k σ f (hE e)
  refine ⟨F, fun T hT => ?_⟩
  let J : (Sp (OO p ⧸ u.lev e) ⟶ u.D.toPre.P.A.left) → u.D.toPre.P.L.ι := fun ψ => d (ψ (cpt _))
  have hJ : Good u.D.toPre.P.L (cpt (OO p ⧸ u.lev e)) J := fun ψ => hd _
  have eJ : ∀ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, J (spMap (Ideal.Quotient.mk (u.lev e)) ≫ ψ) = d (ψ (cpt _)) :=
    fun ψ => congrArg (fun y => d (ψ y)) (mk_cpt u e)
  have hM : ⊤ ≤ b₀ ⁻¹ᵁ u.D.toPre.P.L.U (d (b₀ (cpt _))) := (top_le_iff_cpt _ _).2 (hd _)
  obtain ⟨H₀, H₁⟩ := hF _ (ce e) (cpt _) J hJ
  have H := H₁ jL ((congrArg (fun q => q (cpt _) ∈ u.U.LG.L.U jL) (hce e)).mpr (top_le_comp hL _ trivial))
  rw [hbe e] at H₀
  rw [hbe e, hce e, eJ, Finset.sum_subset hT (fun α _ hα => by rw [H₀ α hα, zero_mul])] at H
  rw [← AddSubmonoidClass.coe_finset_sum, ← AddSubgroupClass.coe_sub]
  refine h2 e _ (Ideal.Quotient.eq.1 (toStkA_injective ?_))
  rw [map_mul, map_pow, hωe, map_mul, map_pow, map_sum, map_sum]
  refine (congrArg₂ (· * ·) ?_ (toStkA_map_valR _ c _ _ (top_le_secChart hL) _)).trans
    (H.trans (Finset.sum_congr rfl fun α _ => ?_))
  · rw [Units.val_pow_eq_pow_val]
    exact congrArg (· ^ k) (toStkA_valR _ _ _ (top_le_wchart' u c b₀ ce hce hbe hL hM e) _)
  · rw [map_mul, map_mul, hx e α,
      sval_of (f α) _ _ J (fun i => d ((b₀ ≫ u.D.toPre.famφB α i) (cpt _))) (fun i => by rw [Category.assoc, eJ]),
      val_of (tG u.U.toUnifPre e α) _ _ J (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) α i) (cpt _)))
        (fun i => by rw [level_Oφ u b₀ _ (hbe e), eJ])]
    refine (congrArg₂ (· * ·) (toStkA_map_valR _ b₀ _ _ ((top_le_iff_cpt _ _).2
      (Set.mem_iInter.2 fun i => hd ((b₀ ≫ u.D.toPre.famφB α i) (cpt _)))) _) (toStkA_valR _ _ _ ((top_le_iff_cpt _ _).2
      (Set.mem_iInter.2 fun i => ?_)) _)).symm
    have := hJ (ce e ≫ Oφl u.U.toUnifPre e α i)
    rw [show J (ce e ≫ Oφl u.U.toUnifPre e α i) = _ by rw [level_Oφ u b₀ _ (hbe e), eJ]] at this
    exact this

end GlobalTheory.ZH.IntegralSum
end
