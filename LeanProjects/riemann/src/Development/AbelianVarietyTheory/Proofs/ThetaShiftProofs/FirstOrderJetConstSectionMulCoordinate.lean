import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpHolomorphicOverUnif
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanJet

open FrameValue

theorem jet_comp_equiv {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    (e : V' ≃L[ℂ] V) (F : V → ℂ) (z : V') : jet (fun w => F (e w)) z = jet F (e z) := by
  have h := e.comp_right_fderiv (f := F) (x := 0)
  rw [map_zero] at h
  ext
  · simp
  · rw [snd_jet, snd_jet]
    exact congrArg (fun q : V' →L[ℂ] ℂ => q z) h

theorem valR_eq_jet {g : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {z : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e z v) (U : X.Opens) (hU : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR v U f = jet (fun w => valAt' (e w) U f) z := by
  ext
  · rw [fst_jet, ← hd.1]
    exact (FormalValue.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v U hU f).symm
  · rw [snd_jet, ← hd.2 U hU f, valR, dif_pos hU]

theorem frameProd_mul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {n : ℕ} (u : HolUnif A L n) (j : ℕ)
    (c z : Fin n → ℂ) (k : Fin 4 → L.ι) (hk : ∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ L.U (k i)) :
    frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] ![k 2, k 0, k 1, k 3] *
      frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
  have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
  have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
  have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
  have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
  simp only [frameProd, Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
    zpow_neg, zpow_one, zpow_natCast, add_comm z c]
  field_simp

theorem jet_sec_mul_coord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (jt₀ : Fin 4 → a.D₀.P.L.ι), IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (h.symm z)).b.left)) z₀ ν.b.left → (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (Λ.ex0 (h.symm 0)) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Λ.ex0 (h.symm z)) x j) 0 z₀)) → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀ → valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀) ((ν.s (Λ.ε α)).s jt₀).val = jet (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) (h.symm z₀) * jet (fun v : Λ.A.V => Λ.u.fr (jt₀ 2) v.2) (h.symm z₀) ^ j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ g h z₀ ν j α s₀ jt hd hs hj
  have hU : ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    intro y hy
    refine Set.mem_iInter.2 fun i => ?_
    have h₁ := Set.mem_iInter.1 (hj hy) (![2, 0, 1, 3] i)
    have h₂ : (![jt 2, jt 0, jt 1, jt 3] : Fin 4 → _) i = jt (![2, 0, 1, 3] i) := by fin_cases i <;> rfl
    rw [h₂]
    exact (congrArg (fun q => q y ∈ a.D₀.P.L.U (jt (![2, 0, 1, 3] i)))
      (ConstTerm.comp_famφB a.D₀ ν.b (Λ.ε α) i)).mpr h₁
  have h0 : ⊤ ≤ (Λ.u.ex (0 : Λ.A.V).2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    have h₁ := FormalValue.top_le_comp hU (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have h₂ := hd.1.trans (Λ.ex0_b (h.symm 0))
    rw [map_zero] at h₂
    exact h₂ ▸ h₁
  obtain ⟨ho, hh⟩ := Λ.u.hol _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  have hn : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] :=
    (ho.preimage continuous_snd).mem_nhds h0
  have lf := ConstTerm.isLift_famφB Λ.u (Λ.ct α)
  have hk : ∀ z, ⊤ ≤ (Λ.u.ex z).left ⁻¹ᵁ LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] →
      ∀ i, ⊤ ≤ (Λ.u.ex (![Λ.A.ct α + z, Λ.A.ct α, z, 0] i)).left ⁻¹ᵁ a.D₀.P.L.U (jt i) := fun z hz i => by
    have h₁ := ((lf z).le_iff _).1 hz
    fin_cases i
    exacts [add_comm z (Λ.A.ct α) ▸ h₁ 1, h₁ 2, h₁ 0, h₁ 3]
  have hg : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε α)) jt :=
    hn.mono fun v hv => ((gtHol_isLift a.D₀ Λ.u _ _ _ _ (Λ.ct α) (Λ.ex0_b v)).le_iff jt).2 (hk _ hv)
  obtain ⟨hc₁, hc₂⟩ := (analyticDictionaryExp_holomorphic_over_unif E H D l c O β b a Λ).2 (Λ.ε α) jt
  simp only [LinearEquiv.symm_apply_apply] at hc₂
  have dF : DifferentiableAt ℂ (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) 0 :=
    (hh.differentiableAt (ho.mem_nhds h0)).comp (0 : Λ.A.V) differentiableAt_snd
  have dG : DifferentiableAt ℂ (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) 0 := hc₁.differentiableAt hg
  have dfn : Differentiable ℂ (Λ.fn j α s₀) := by
    have := differentiable_secVal a.D₀.P.isLB s₀ (𝟙 _) (q := id) differentiable_id
      (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun w => by rw [id, Category.comp_id]; exact lf w)
    simp only [id, Category.comp_id] at this
    exact this
  have dP : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) 0 := by
    have : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
    exact ((dfn.comp differentiable_snd).fun_mul (this.const_mul _).cexp) 0
  have dQ : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.u.fr (jt 2) v.2) 0 :=
    ((Λ.u.fr_hol (jt 2)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds (hk _ h0 2))).comp (0 : Λ.A.V)
      differentiableAt_snd
  have e₁ := valR_eq_jet hd _ hU (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  simp only [Λ.ex0_b] at e₁
  replace e₁ := e₁.trans (jet_comp_equiv h.symm
    (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) z₀)
  have e₂ := (hs (Λ.ε α) jt hj).trans (jet_comp_equiv h.symm (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) z₀)
  refine (congrArg₂ (· * ·) e₁ e₂).trans ?_
  rw [← jet_mul dF dG, ← jet_pow dQ, ← jet_mul dP (dQ.fun_pow j)]
  refine jet_congr ?_ _
  filter_upwards [hn, hg] with v hv hv'
  refine (congrArg₂ (· * ·) (valAt'_sec a.D₀.P.isLB s₀ (lf v.2) hv) (hc₂ v hv')).trans ?_
  rw [← frameProd_mul Λ.u j (Λ.A.ct α) v.2 jt (hk _ hv), _root_.mul_mul_mul_comm]
  rfl

end GlobalTheory.ConstTanJet
