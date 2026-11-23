import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanExp

theorem approx {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
    {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G)
    {e j : ℕ} {σ : Out.H0 U.LG.L j} {f : ∀ α : D.toPre.X, D.toPre.SecB j α} (h : U.ExpandsAt e j σ f)
    {K : Type} (q : K ≃ D.toPre.X) : ∃ F : Finset K, ∀ (S : Type) [CommRing S] [IsLocalRing S] (J : Ideal S)
      [IsAdicComplete J S] (s : Sp S ⟶ Sp R) (g : Out.GtPt D.toPre (Over.mk s)) (x : Sp S ⟶ G.left),
      FormalValue.IsFormalPt U J g x → ∀ (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι), ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL →
      ⊤ ≤ FormalValue.basePt g ⁻¹ᵁ D.toPre.P.L.U jM → ∀ (ω τ φ p : S) (B : K → S), IsUnit ω → IsUnit τ →
      ω * τ = (FormalValue.tau U J x jL jM).val * φ →
      (∀ α jf jt, FormalValue.CohCharts g (q α) jM jf jt →
        ω ^ j * (FormalValue.famVal g (f (q α)) jf * FormalValue.coordVal g (q α) jt) = B α * φ ^ j) →
      FormalValue.secVal U σ x jL = p * τ ^ j → p - ∑ α ∈ F, B α ∈ J ^ (e + 1) := by
  obtain ⟨F, hF⟩ := FormalValue.map_secVal_eq U h
  refine ⟨F.map q.symm.toEmbedding, fun S _ _ J _ s g x hx jL jM hL hM ω τ φ p B hω hτ e₁ hB hp => ?_⟩
  haveI := isLocalRing_quotient_pow (ne_top_of_isHausdorff J) e
  choose jf jt hc using FormalValue.exists_cohCharts g jM hM
  have e₂ := Ideal.Quotient.eq.1 ((hF S J s g x hx _ (Ideal.Quotient.mk _) Ideal.mk_ker.ge).2
    ((F.map q.symm.toEmbedding).map q.toEmbedding) jL jM jf jt
    (fun α hα => Finset.mem_map.2 ⟨q.symm α, Finset.mem_map_of_mem _ hα, q.apply_symm_apply α⟩) hL hM
    (fun α _ => hc α))
  rw [Finset.sum_map, hp] at e₂
  have e₃ : ω ^ j * ∑ α ∈ F.map q.symm.toEmbedding, FormalValue.famVal g (f (q α)) (jf (q α)) *
      FormalValue.coordVal g (q α) (jt (q α)) = (∑ α ∈ F.map q.symm.toEmbedding, B α) * φ ^ j := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => hB α _ _ (hc _)
  rw [← Ideal.unit_mul_mem_iff_mem _ ((hω.mul hτ).pow j)]
  have e₄ := Ideal.mul_mem_left _ (ω ^ j) e₂
  have e₅ : (ω * τ) ^ j = (FormalValue.tau U J x jL jM).val ^ j * φ ^ j := by rw [e₁, mul_pow]
  refine (congrArg (· ∈ J ^ (e + 1)) ?_).mp e₄
  rw [mul_sub, mul_sub, mul_left_comm (ω ^ j) (_ ^ j)]
  refine congrArg₂ (· - ·) (by ring) ((congrArg (_ * ·) e₃).trans ?_)
  rw [e₅]
  ring

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isUnit_frame (v : Λ.A.V) (k : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U k) :
    IsUnit (Ξ.τ v k) := by
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v k jM j₀ h hj)).mpr ?_)
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)

theorem differentiable_term (j : ℕ) (α : Λ.A.X) (s : a.D₀.SecB j (Λ.ε α)) :
    Differentiable ℂ fun u : Λ.A.V => Λ.fn j α s u.2 * eTwoPi (u.1 α) := by
  have h₁ := FrameValue.differentiable_secVal (u := Λ.u) a.D₀.P.isLB s (𝟙 _) (q := id) differentiable_id
    (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop)
    (fun w => by rw [id, Category.comp_id]; exact ConstTerm.isLift_famφB Λ.u (Λ.ct α) w)
  simp only [id, Category.comp_id] at h₁
  have h₂ : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
  exact (h₁.comp differentiable_snd).fun_mul (h₂.const_mul _).cexp

end Points

theorem exists_eq_mul_pow {S : Type} [CommRing S] (s : S) {t : S} (ht : IsUnit t) (j : ℕ) : ∃ p, s = p * t ^ j := by
  obtain ⟨p, hp⟩ := (ht.pow j).dvd (a := s)
  exact ⟨p, hp.trans (_root_.mul_comm _ _)⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ W.t.G.left) (z : Λ.A.V) (jL : W.P.U.LG.L.ι) (jM : W.P.D.toPre.P.L.ι) (ω φ₁ τ : DualNumber ℂ⟦X⟧) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v → ⊤ ≤ v ⁻¹ᵁ W.P.U.LG.L.U jL → ⊤ ≤ FormalValue.basePt g₁ ⁻¹ᵁ W.P.D.toPre.P.L.U jM → IsUnit ω → IsUnit τ → ω * τ = (FormalValue.tau W.P.U.toUnifPre idealEps v jL jM).val * φ₁ → (∀ (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧) jf jt, IsConstMul W j (Λ.ε α) s₀ f r → FormalValue.CohCharts g₁ (W.e (Λ.ε α)) jM jf jt → ω ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e (Λ.ε α)) jt) = TrivSqZeroExt.inl r * constEps (jet (fun u : Λ.A.V => Λ.fn j α s₀ u.2 * eTwoPi (u.1 α)) z) * φ₁ ^ j) → HasConstExp W σ → ∃ (x : Λ.A.V → ℂ⟦X⟧) (y : DualNumber ℂ⟦X⟧), IsJet x z y ∧ (∀ u k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k → FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = x u * Ξ.τ u k ^ j) ∧ FormalValue.secVal W.P.U.toUnifPre σ v jL = y * τ ^ j := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ g₁ v z jL jM ω φ₁ τ j σ hv hL hM hω hτ e₁ hB ⟨f, hf, hs⟩
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  haveI : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [hJ]; infer_instance
  haveI := isAdicComplete_idealEps
  haveI := isLocalRing_dual ℂ⟦X⟧
  choose s₀ r hs using fun α : Λ.A.X => hs (Λ.ε α)
  choose F hF using fun e => approx W.P.U.toUnifPre (hf e) (Λ.ε.trans W.e).toEquiv
  have key : ∀ e u k p, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k →
      FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = p * Ξ.τ u k ^ j →
      p - ∑ α ∈ F e, r α * PowerSeries.C (Λ.fn j α (s₀ α) u.2 * eTwoPi (u.1 α)) ∈
        (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ^ (e + 1) := by
    intro e u k p hk hp
    obtain ⟨iM, i₀, hi, -⟩ := exists_charts Ξ u
    refine hF e _ _ _ (Ξ.g u) _ (Ξ.x_fm u) k iM hk (fun y hy => (hi hy).2) _ _ _ p _
      (FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g u).b.left _ hi (W.w.s (fun _ => i₀, iM)))
      (isUnit_frame Ξ u k hk) (Ξ.τ_eq u k iM i₀ hk hi) (fun α jf jt hc => ?_) hp
    refine (ConstTerm.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α (s₀ α) _ (r α) (hs α) u iM i₀ jf jt hc hi).trans ?_
    rw [map_mul, map_pow, _root_.mul_assoc]
  have hk : ∀ u, ∃ k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k := fun u => by
    obtain ⟨k, hk⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x u).left) (cpt ℂ⟦X⟧))
    exact ⟨k, (top_le_iff_cpt _ _).2 hk⟩
  choose k hk using hk
  choose x hx using fun u => exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left (k u))
    (isUnit_frame Ξ u (k u) (hk u)) j
  obtain ⟨y, hy⟩ := exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ v jL) hτ j
  refine ⟨x, y, isJet_of_approx fun e => ⟨_, _, IsJet.sum (F e) fun α _ =>
    (isJet_C (differentiable_term j α (s₀ α) 0) z).const_mul (r α), fun u => ?_, ?_⟩, fun u k' hk' => ?_, hy⟩
  · have := key e u _ _ (hk u) (hx u)
    rwa [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  · exact hF e _ _ _ g₁ v hv jL jM hL hM ω τ φ₁ y _ hω hτ e₁ (fun α jf jt hc => hB α (s₀ α) _ (r α) jf jt (hs α) hc) hy
  · obtain ⟨p, hp⟩ := exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k')
      (isUnit_frame Ξ u k' hk') j
    rw [hp]
    refine congrArg (· * _) (FormalValue.eq_of_forall_mk_eq
      ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) fun e => ?_)
    exact (Ideal.Quotient.eq.2 (key e u _ _ hk' hp)).trans (Ideal.Quotient.eq.2 (key e u _ _ (hk u) (hx u))).symm

end GlobalTheory.ConstTanExp
