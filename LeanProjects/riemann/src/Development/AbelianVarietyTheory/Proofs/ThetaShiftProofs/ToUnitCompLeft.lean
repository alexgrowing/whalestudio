import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstTerm

section Values

variable {A : Type} [CommRing A] {B B₀ : Scheme.{0}}

theorem valR_zpow (x : Sp A ⟶ B) (U : B.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (t : Γ(B, U)ˣ) (u : Aˣ)
    (hu : (u : A) = valR x U t.val) (n : ℤ) : valR x U (t ^ n).val = ((u ^ n : Aˣ) : A) := by
  have e : u = Units.map (HolHom.evalHom x U h).toMonoidHom t := Units.ext (hu.trans (HolHom.valR_eq x U h _))
  rw [e, ← map_zpow, HolHom.valR_eq x U h]
  rfl

theorem le_div {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} (x : Sp A ⟶ B) {k : M₀.ι} {m : M.ι}
    (h₀ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ M₀.U k) (h : ⊤ ≤ x ⁻¹ᵁ M.U m) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => k, m) :=
  fun _ hz => ⟨Set.mem_iInter.2 fun _ => h₀ hz, h hz⟩

theorem valR_pullGen {A₀ : Type} [CommRing A₀] (ρ : A₀ →+* A) {M₀ : LB B₀} {K : Type} [Fintype K]
    {ψ : K → (Sp A₀ ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M₀ ψ ε)) (k : K → M₀.ι)
    (h : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ LB.wchart M₀ ψ k) :
    valR (𝟙 (Sp A)) _ ((LB.pullGen M₀ ψ ε t (spMap ρ)).s k).val = ρ (valR (𝟙 (Sp A₀)) _ (t.s k).val) := by
  have h' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M₀ (fun i => spMap ρ ≫ ψ i) k :=
    fun z _ => Set.mem_iInter.2 fun i => Set.mem_iInter.1 (h (show spMap ρ z ∈ (⊤ : (Sp A₀).Opens) from trivial)) i
  refine (HolHom.valR_res (𝟙 (Sp A)) _ _ h').trans ((HolHom.valR_comp (𝟙 (Sp A)) (spMap ρ) _ _).symm.trans ?_)
  refine Eq.trans ?_ (HolHom.valR_spMap ρ (𝟙 (Sp A₀)) _ h _)
  rw [Category.id_comp, Category.comp_id]
  rfl

theorem prod_factors {G : Type} [CommGroup G] (u : Fin 4 → G) (j : ℕ) :
    (∏ i, u i ^ Out.DegPre.famε j i) * ∏ i, ![u 1, u 2, u 0, u 3] i ^ Out.DegPre.gtε i = u 0 ^ j := by
  simp only [Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub, zpow_neg, zpow_one,
    zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end Values

section Points

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {T : Over (Sp R)} (b : T ⟶ D.P.A) (α : D.X)

theorem comp_famφB (i : Fin 4) : b.left ≫ D.famφB α i = D.gtφT T b α (![2, 0, 1, 3] i) := by
  have h : ∀ p : 𝟙_ (Over (Sp R)) ⟶ D.P.A, b ≫ toUnit D.P.A ≫ p = toUnit T ≫ p := fun p => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases i
  · exact Category.comp_id _
  · change (b ≫ (𝟙 D.P.A * toUnit _ ≫ D.c α)).left = ((toUnit _ ≫ D.c α) * b).left
    rw [MonObj.comp_mul, h, Category.comp_id, mul_comm]
  · exact congrArg (·.left) (h _)
  · exact congrArg (·.left) (h _)

end Points

section Core

open FrameValue

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {D₀ : Out.DegPre ℂ} {n : ℕ}
  (u : HolUnif D₀.P.A D₀.P.L n) {α₀ : D₀.X} {c : Fin n → ℂ}

theorem toUnit_comp_left {B : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ p).left) = p.left := by
  have e : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact Spec.map_id _
  change (Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ) ≫ p.left = _
  rw [e]
  exact Category.id_comp _

theorem gtφ_eq (hc : u.ex c = D₀.c α₀) {b₀ : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A} {z : Fin n → ℂ}
    (hb : (show Sp ℂ ⟶ _ from b₀.left) = (u.ex z).left) (k : Fin 4) :
    (show Sp ℂ ⟶ _ from Out.DegPre.gtφ D₀ ℂ b₀ α₀ k) = (u.ex (![c + z, c, z, 0] k)).left := by
  have hb' : b₀ = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hb.trans (toUnit_comp_left _).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]
  fin_cases k
  · refine Eq.trans ?_ (toUnit_comp_left _)
    change (toUnit _ ≫ D₀.c α₀ * b₀).left = (toUnit _ ≫ u.ex (c + z)).left
    rw [hb', u.ex_add, MonObj.comp_mul, hc]
  · exact (toUnit_comp_left _).trans (congrArg (·.left) hc.symm)
  · exact hb
  · exact (toUnit_comp_left _).trans (congrArg (·.left) h0.symm)

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem isLift_famφB (hc : u.ex c = D₀.c α₀) (z : Fin n → ℂ) :
    IsLift u (D₀.famφB α₀) (u.ex z).left ![z, z + c, c, 0] := fun k => by
  have h : ∀ p : 𝟙_ (Over (Sp ℂ)) ⟶ D₀.P.A, u.ex z ≫ toUnit D₀.P.A ≫ p = p := fun p => by
    rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  fin_cases k
  · exact Category.comp_id _
  · change (u.ex z ≫ (𝟙 D₀.P.A * toUnit _ ≫ D₀.c α₀)).left = (u.ex (z + c)).left
    rw [MonObj.comp_mul, h, Category.comp_id, u.ex_add, hc]
  · change (u.ex z ≫ toUnit _ ≫ D₀.c α₀).left = (u.ex c).left
    rw [h, hc]
  · change (u.ex z ≫ toUnit _ ≫ η[D₀.P.A]).left = (u.ex 0).left
    rw [h, (u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    [IsLocalRing S] (κ : R →+* S) (ρ : ℂ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ))) (g₀ : Out.GtPtF D₀ ℂ)
    {α : D.toPre.X} {z : Fin n → ℂ} (hc : u.ex c = D₀.c α₀) (hb : (show Sp ℂ ⟶ _ from g₀.b.left) = (u.ex z).left)
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (j₀ : D₀.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (hj : FormalValue.CohCharts g α jM jf jt)
    (hM : ⊤ ≤ (show Sp S ⟶ _ from g.b.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀, jM)) :
    valR (A := S) g.b.left _ (w.s (fun _ => j₀, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (secVal u D₀.P.isLB s₀ (u.ex z).left ![z, z + c, c, 0] *
        genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] * u.fr j₀ z ^ j) := by
  have hφ : ∀ k, FormalValue.coordφ g α k ≫ φ = spMap ρ ≫ (u.ex (![c + z, c, z, 0] k)).left := fun k =>
    (hg.1 k).trans (congrArg (spMap ρ ≫ ·) (gtφ_eq u hc hb k))
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have h₀ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.U j₀ := by
    intro y _
    obtain rfl : y = spMap ρ (cpt S) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact (congrArg (fun q => q (cpt S) ∈ D₀.P.L.U j₀) (hφ 2)).mp (mem_pull.1 (hM trivial).1)
  obtain ⟨k, hk, ek⟩ : ∃ k : Fin 4 → D₀.P.L.ι,
      (∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ D₀.P.L.U (k i)) ∧ k 2 = j₀ := by
    refine ⟨![chartAt D₀.P.isLB (u.ex (c + z)).left, chartAt D₀.P.isLB (u.ex c).left, j₀,
      chartAt D₀.P.isLB (u.ex 0).left], fun i => ?_, rfl⟩
    fin_cases i
    exacts [le_chartAt D₀.P.isLB _, le_chartAt D₀.P.isLB _, h₀, le_chartAt D₀.P.isLB _]
  subst ek ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have lf := isLift_famφB u hc z
  have lg : IsLift u (Out.DegPre.gtφ D₀ ℂ g₀.b α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] :=
    fun i => (Category.id_comp _).trans (gtφ_eq u hc hb i)
  have cf : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) := by
    refine (lf.le_iff _).2 fun i => ?_
    fin_cases i
    exacts [hk 2, add_comm c z ▸ hk 0, hk 1, hk 3]
  have cg := (lg.le_iff k).2 hk
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      ((HolHom.valR_spMap ρ (u.ex z).left _ cf _).trans (congrArg ρ (valAt'_sec D₀.P.isLB s₀ lf cf)))
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    ((valR_pullGen ρ (g₀.s α₀) k cg).trans (congrArg ρ (valAt'_gen D₀.P.isLB (g₀.isGen α₀) lg cg))))
  have e₄ : frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] (fun i => k (![2, 0, 1, 3] i)) *
      frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
    have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
    have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
    have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
    have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
    simp only [frameProd, Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
      zpow_neg, zpow_one, zpow_natCast, add_comm z c]
    field_simp
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₄]
  simp only [map_mul] at e₁ ⊢
  rw [← e₅] at e₁
  unfold FormalValue.famVal
  linear_combination (ρ (genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0]) *
    ρ (frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k)) * e₁

end Core

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧), (∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z) (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ → (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) → ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) = valR (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧ (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) * valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e (Λ.ε α))) jf) (f.f jf) = κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) j₀) (s₀.f j₀)) → ∀ v jM j₀ jf jt, FormalValue.CohCharts (Ξ.g v) (W.e (Λ.ε α)) jM jf jt → ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) → valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j * (FormalValue.famVal (Ξ.g v) f jf * FormalValue.coordVal (Ξ.g v) (W.e (Λ.ε α)) jt) = r * PowerSeries.C (Λ.fn j α s₀ v.2 * eTwoPi (v.1 α) * Λ.u.fr j₀ v.2 ^ j) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j α s₀ f r hf v jM j₀ jf jt hj hM
  have h := core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v) (Λ.ct α) (Λ.ex0_b v)
    (Ξ.g_rel v (Λ.ε α)) s₀ f r (fun p => hf _ p _) jM j₀ jf jt hj hM
  rw [Λ.arcDict_expZero_section v α] at h
  exact h

end GlobalTheory.ConstTerm
