import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section Move2

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem vge_move₂ {k₁ k₂ : ℕ} {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k₁))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k₂))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {TB : D.toPre.P.A.left ⟶ D.toPre.P.A.left}
    (hh : h ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ TB)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k₂) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k₁) s h φ₃ ε₃ u)
    {ψ : K₄ → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heB : eB.IsGen)
    (hform : FormEq (Sum.elim (fun i => TB ≫ D.toPre.famφB α i) ψ) (Sum.elim (DegPre.famε k₁) δ)
      (D.toPre.famφB χ) (DegPre.famε k₂))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eB (DegPre.prB D.toPre F).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k₁ α s r) : VGe D F v k₂ χ s' (r + q) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  have e1 : ∀ i, ∃ t : D.toPre.SecB k₂ χ, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval t ρ z J = sval (σ i) (ρ ≫ TB) z J * (val eB ρ z J).val := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hform (pullMulSec (σ i) TB eB heB)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ heB ρ z hJ)⟩
  choose σ' hσ' using e1
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k₂)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k₂) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  have e2 : ∀ i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k₂)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ' i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (σ' i) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose σ'F hσ'F using e2
  refine ⟨n, fun i => c * a i, σ', σ'F, fun i => ?_, fun i => ?_, fun j => ?_⟩
  · exact secScal_of_sval hL fun y J hJ => (hσ'F i _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_mul, WithTop.coe_add, add_comm ((r : ℚ) : WithTop ℚ)]
    exact add_le_add hq (hva i)
  · show s'.f j = ∑ i, resTop _ (gF D.toPre F (c * a i)) * (σ'F i).f j
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have m := hIy.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    have hy' : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j := hy
    have T0 := sec_trans s' (𝟙 _) y hy' m
    set τ := (Geo.Tor.trF (DegPre.famφ D.toPre F χ) (DegPre.famε k₂) (𝟙 _) y j
      (fun k => I (𝟙 _ ≫ DegPre.famφ D.toPre F χ k))).val with hτ
    have Ti : ∀ i, gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * (gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I) := fun i => by
      have S1 : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
          (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i))) =
          gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) := gs_res _ y le_top hy' _
      rw [gs_mul _ y _ hy', S1, sec_trans (σ'F i) (𝟙 _) y hy' m, hτ]
      exact mul_left_comm _ _ _
    have RHS : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (∑ i, resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      rw [gs_sum _ y _ hy', Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Ti i
    have CORE : sval s' (𝟙 _) y I = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      have H1 := (secRel_iff hL _ _ s' _ _ s h _ _ u).1 hrel _ (𝟙 _) y I hIy
      have H2 := sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) (𝟙 _ ≫ h) y hIy
      rw [H1, H2, hc y I hIy, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have A1 : gs (𝟙 _ ≫ h) y ⊤ (gF D.toPre F (a i)) = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) := by
        rw [Category.id_comp]; exact gs_gF_comp hfst y (a i)
      have A2 : sval (σF i) (𝟙 _ ≫ h) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I := by
        rw [← secScal_sval (hscal i) (𝟙 _ ≫ h) y hIy, Category.assoc, hh, Category.id_comp]
      have A3 : sval (σ'F i) (𝟙 _) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I *
          (val eB (DegPre.prB D.toPre F).left y I).val := by
        rw [hσ'F i _ (𝟙 _) y I hIy, Category.id_comp, hσ' i _ _ y I hIy]
      rw [A1, A2, A3, map_mul, gs_mul _ y ⊤ (by trivial)]
      ring
    exact T0.trans ((congrArg (fun x => τ * x) CORE).trans RHS.symm)

end Move2

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

def PullReflStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ (χ : D.toPre.X) (q : ℚ),
          VGe D F v (k * N) (star a • χ) (s'.s (star a • χ)) q → VGe D F v k χ (s.s χ) q

def PullGenStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (χ : D.toPre.X)
        (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))), u.IsGen →
        LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
          (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1)))
            (jFK (R := V) F)) →
        ∃ (m : ℕ) (ψ : Fin m → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (δ : Fin m → ℤ)
          (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)), eB.IsGen ∧
          FormEq (Sum.elim (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i) ψ)
            (Sum.elim (DegPre.famε k) δ) (D.toPre.famφB (star a • χ)) (DegPre.famε (k * N)) ∧
          ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧
            ∀ (y : (DegPre.BF D.toPre F).left)
              (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
              Good D.toPre.P.L y J →
              (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) *
                (val eB (DegPre.prB D.toPre F).left y J).val

def QAlStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (_oa : D.toPre.OAct O) (a : O) (N : ℕ),
      a * star a = (N : O) → star a * a = (N : O) → ∀ χ : D.toPre.X, Q (star a • χ) = N * Q χ

def PullbackValuationInvariance : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v (k * N) s' r

private theorem fwd_lemma (hG : PullGenStatement) (hQ : QAlStatement) :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r → NuGe D Q F v (k * N) s' r := by
  intro V _ _ _ ϖ hϖ D Q hQD F _ _ v hv O _ _ _ oa w0 hw0 a N hN ha1 ha2 k hk s s' hpull r hs
  unfold NuGe at hs ⊢
  intro β
  obtain ⟨hrelAll, hzero⟩ := hpull
  by_cases hβ : ∃ χ, β = star a • χ
  · obtain ⟨χ, rfl⟩ := hβ
    obtain ⟨u, hu, hcorr, hrel⟩ := hrelAll χ
    obtain ⟨m, ψ, δ, eB, heB, hform, c, hc0, hc⟩ :=
      hG V ϖ hϖ D F v hv O oa w0 hw0 a N hN ha1 ha2 k hk χ u hu hcorr
    have hfst : (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left =
        (fst (TF (R := V) F) D.toPre.P.A).left :=
      congrArg (fun φ => φ.left) (lift_fst (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
    have hh : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left =
        (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
      congrArg (fun φ => φ.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))
    have hq0 : ((0 : ℚ) : WithTop ℚ) ≤ v c := by simpa using hc0
    have key := SectionScalarValuation.vge_move₂ hfst hh u hrel eB heB hform c hc (q := 0) hq0 (hs χ)
    have hQa := hQ V ϖ hϖ D Q hQD O oa a N ha1 ha2 χ
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    convert key using 1
    rw [hQa]
    push_cast
    field_simp
    try ring
  · push_neg at hβ
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => ?_⟩
    rw [hzero β hβ j]
    simp

theorem pullback_valuation_invariance_of (hR : PullReflStatement) (hG : PullGenStatement) (hQ : QAlStatement) : PullbackValuationInvariance := by
  intro V _ _ _ ϖ hϖ D Q hQD F _ _ v hv O _ _ _ oa w0 hw0 a N hN ha1 ha2 k hk s s' hpull r
  refine ⟨fwd_lemma hG hQ V ϖ hϖ D Q hQD F v hv O oa w0 hw0 a N hN ha1 ha2 k hk s s' hpull r, fun hs' => ?_⟩
  unfold NuGe at hs' ⊢
  intro χ
  have hQa := hQ V ϖ hϖ D Q hQD O oa a N ha1 ha2 χ
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 := hs' (star a • χ)
  have heq : r + (Q (star a • χ) : ℚ) / ((k * N : ℕ) : ℚ) = r + (Q χ : ℚ) / (k : ℚ) := by
    rw [hQa]
    push_cast
    field_simp
    try ring
  rw [heq] at h1
  exact hR V ϖ hϖ D F v hv O oa a N hN ha1 ha2 k hk s s' hpull χ _ h1

def PullbackValuationForwardBound : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r → NuGe D Q F v (k * N) s' r

theorem pullback_valuation_forward_of (hG : PullGenStatement) (hQ : QAlStatement) : PullbackValuationForwardBound :=
  fwd_lemma hG hQ

end ReciprocityTheory.ChartRestriction.G.DVR
