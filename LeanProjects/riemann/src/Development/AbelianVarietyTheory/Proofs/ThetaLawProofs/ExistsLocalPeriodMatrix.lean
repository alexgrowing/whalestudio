import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.PeriodLift

open GlobalTheory.LocLift GlobalTheory.ThetaValueCont Filter Topology

theorem exists_bilin_omegaStd (g : ℕ) :
    ∃ EF : LinearMap.BilinForm ℤ (Fin g ⊕ Fin g → ℤ), ∀ a b, EF a b = omegaStd a b :=
  ⟨LinearMap.mk₂ ℤ (fun x y => omegaStd x y)
    (fun x x' y => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring), fun _ _ => rfl⟩

theorem eq_zero_of_per_eq_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef)
    {a : Fin g ⊕ Fin g → ℤ} (h : per τ a = 0) : a = 0 := by
  have h1 : (τ.map Complex.im).mulVec (fun i => (a (.inl i) : ℝ)) = 0 := by
    funext i
    have := congrArg Complex.im (congrFun h i)
    simpa [per, Matrix.mulVec, dotProduct] using this
  have h2 : (fun i => (a (.inl i) : ℝ)) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.2 hp.isUnit (h1.trans (Matrix.mulVec_zero _).symm)
  have h3 : ∀ i, a (.inl i) = 0 := fun i => by simpa using congrFun h2 i
  funext i
  rcases i with i | i
  · exact h3 i
  · simpa [per, h3, Matrix.mulVec, dotProduct] using congrFun h i

theorem perLev_of_periods (hT : ThetaUnifAV) (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {g : ℕ} (hg : P.g = g) (k : ℕ)
    (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (hon : Function.Surjective e) (hol : IsHolTo Set.univ fun z => (e z).left)
    (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (hker : ∀ z, e z = 1 ↔ z ∈ p.range) (hi : Function.Injective p)
    (hs : Submodule.span ℝ (Set.range p) = ⊤) (hd : DiscreteTopology p.range)
    (hweil : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (e ((n : ℂ)⁻¹ • p a)) (e ((n : ℂ)⁻¹ • p b)) (unitOn c)) :
    IsUnit (Matrix.of fun i j => p (Pi.single (.inr j) 1) i).det ∧
      PerLev P ((Matrix.of fun i j => p (Pi.single (.inr j) 1) i)⁻¹ * Matrix.of fun i j => p (Pi.single (.inl j) 1) i) k
        fun a => e ((k : ℂ)⁻¹ • p a) := by
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, -, hW⟩ := hT P rig hrig
  obtain ⟨EF, hEF'⟩ := exists_bilin_omegaStd P.g
  obtain ⟨F, hF⟩ := ThetaPoint.exists_linearEquiv_lift hmul P u e hadd hon hol
    ((Set.countable_range p).mono fun z hz => (hker z).1 hz)
  have hFΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ p.range := fun z => by rw [← u.ker, hF, hker]
  have hEF : ∀ a a₂, (hermForm Hm (F (p a)) (F (p a₂))).im = EF a a₂ := fun a a₂ => by
    refine (hE ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩).symm.trans (congrArg _ ?_)
    rw [hEF']
    refine int_eq_of_exp fun k hk => ?_
    have k₁ := hW k ⟨_, (hFΛ _).2 ⟨a, rfl⟩⟩ ⟨_, (hFΛ _).2 ⟨a₂, rfl⟩⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have k₂ := hweil k a a₂ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    simp only [← map_smul, hF] at k₁
    exact congrArg Units.val (weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k _ _ _ _ k₁ k₂)
  obtain ⟨Hm', h1, h2, h3⟩ : HasForm EF p := HasForm.of_comp F.toLinearMap F.injective ⟨Hm, hAH.1, hAH.2.1, hEF⟩
  obtain ⟨h, τ, hh, hinv, hτ, hsy, hp, -, hper⟩ := SiegelPeriod.exists_siegel_form _ EF _ (LinearEquiv.refl ℤ _) p Hm'
    hEF' ⟨hi, hd, hs, h1, h2, h3⟩
  simp only [LinearEquiv.refl_apply] at hinv hτ hper
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hh
  rw [← hinv, Matrix.nonsing_inv_nonsing_inv _ hdet, ← hτ]
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  let ψ : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofBijective h.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hh, Matrix.mulVec_surjective_iff_isUnit.2 hh⟩
  have hψ : ∀ a, ψ.symm (per τ a) = p a := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact (hper a).symm
  obtain ⟨u', hex, hΛ, -⟩ := exists_holUnif_reparam P.A P.L P.g u (ψ.symm.trans F) (fun _ => 1)
    (differentiable_const _) (fun _ => one_ne_zero) rfl
  have hex' : ∀ (c : ℂ) a, u'.ex (c • per τ a) = e (c • p a) := fun c a => by
    rw [hex, LinearEquiv.trans_apply, hF, map_smul, hψ]
  refine ⟨rfl, hsy, hp, u', fun z => ?_, fun n a b c hn hc => ?_, fun a => (hex' _ a).symm⟩
  · rw [hΛ, LinearEquiv.trans_apply, hFΛ]
    refine exists_congr fun a => ?_
    rw [← hψ, ψ.symm.injective.eq_iff, eq_comm]
  · rw [hex', hex']
    exact hweil n a b c hn hc

theorem exists_local_period_matrix : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Q : Out.PolAV X) (g k m : ℕ) (l : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over X) ⟶ Q.A)) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (φ₀ : P₀.A.left ⟶ Q.A.left) (τ₀ : Matrix (Fin g) (Fin g) ℂ) (lev₀ : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P₀.A)), LocallyOfFiniteType s → 0 < k → (∀ a, l a ^ k = 1) → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → PolPB P₀ Q (y b₀) φ₀ → PerLev P₀ τ₀ k lev₀ → (∀ a, (lev₀ a).left ≫ φ₀ = y b₀ ≫ (l a).left) → ∃ (B' : Set (Fin m → ℂ)) (τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ τ b₀ = τ₀ ∧ (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B') ∧ ∀ b ∈ B', ∃ (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ Q.A.left) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PolPB P Q (y b) φ ∧ PerLev P (τ b) k lev ∧ ∀ a, (lev a).left ≫ φ = y b ≫ (l a).left := by
  intro hL hT K _ σ X s Q g k m l B y b₀ P₀ φ₀ τ₀ lev₀ hft hk hl0 hB hb₀ hyσ hy ⟨hφ₀, hg₀, hL₀⟩
    ⟨hg, _, hp₀, u, hΛ, w₀, hlev₀⟩ hlev
  subst hg
  haveI : CharZero K := σ.charZero
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI := Q.isAb.proper
  obtain ⟨Φ₀, hΦ₀, hΦW₀⟩ := exists_push_iff Q P₀ hφ₀ hL₀
  have he₀ : IsExp (y b₀) fun z => Φ₀ (u.ex z) := by
    obtain ⟨rig, hrig⟩ := P₀.rigid
    obtain ⟨u₀, -, -, -, -, -, h₁, h₂, -⟩ := hT P₀ rig hrig
    obtain ⟨F, hF⟩ := ThetaPoint.exists_linearEquiv_lift hL.mulN P₀ u₀ u.ex u.ex_add u.ex_onto
      (fun U f => by simpa using u.hol U f) ((Set.countable_range (per τ₀)).mono fun z hz => by
        obtain ⟨a, ha⟩ := (hΛ z).1 ((u.ker z).1 hz)
        exact ⟨a, ha.symm⟩)
    have := (PointUnif.isExp_push hφ₀ u₀ h₁ h₂ Φ₀ hΦ₀).comp_equiv F
    simp only [hF] at this
    exact this
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, he0, hr, hol, he, hl⟩ := RelExp.exists_relative_exp K σ X s Q.A P₀.g m B y b₀
    (fun z => Φ₀ (u.ex z)) hft Q.isAb (hg₀ ▸ Q.smoothDim) hB hb₀ hyσ hy he₀
  change HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, IsExp (y b) (e b) ∧ _ at he
  have hy₁ := isHolTo_mono hy hB₁ hB₁B
  let p₀ : (Fin P₀.g ⊕ Fin P₀.g → ℤ) →+ (Fin P₀.g → ℂ) := AddMonoidHom.mk' (per τ₀) (per_add τ₀)
  have hrange : Set.range p₀ = u.Λ := Set.ext fun z => by
    rw [SetLike.mem_coe, hΛ]
    exact exists_congr fun a => eq_comm
  obtain ⟨P, hP₀, hP⟩ := exists_periods latContinuation hB₁ hb₁ hy₁ hr hol he hl p₀
    ((injective_iff_map_eq_zero p₀).2 fun a ha => eq_zero_of_per_eq_zero hp₀ ha) (hrange ▸ u.full) (fun z => by
      rw [he0]
      exact (map_eq_one_iff Φ₀ Φ₀.injective).trans ((u.ker z).trans (Set.ext_iff.1 hrange z).symm))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb => ((hball b hb).1.1 x).differentiableWithinAt
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'),
      hk1 b hb]
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : Fin P₀.g ⊕ Fin P₀.g → ℤ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a a₂ : ℂ) / k) →
      Out.WeilIs Q.A Q.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (torsion_eq_and_weilIs_of_isHolTo hL X Q m k C y
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk
      (isUnit_natCast_of_over s hk) hCo hCc hC₀ (htor k a) (htor k a₂)
      fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2
        (by rw [hP₀, he0]; exact (hΦW₀ _ _ _ _).1 (w₀ k a a₂ c hk hc)) b hb
  have hleft : ∀ a b, (toUnit (Over.mk (y b)) ≫ l a).left = y b ≫ (l a).left := fun a b => by
    rw [Over.comp_left, Over.toUnit_left]; rfl
  have hsec : ∀ a, ∀ b ∈ C, toUnit _ ≫ l a = e b ((k : ℂ)⁻¹ • P b a) :=
    fun a => (torsion_eq_and_weilIs_of_isHolTo hL X Q m k C y (fun b => toUnit _ ≫ l a)
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) 1 b₀ hk (isUnit_natCast_of_over s hk) hCo hCc hC₀
      (isHolTo_congr (isHolTo_comp_hom (isHolTo_mono hy₁ hCo hC₁) (l a).left) fun b _ => hleft a b) (htor k a)
      fun b hb => ⟨by rw [← MonObj.comp_pow, hl0, MonObj.comp_one], hpow k hk a b hb⟩).1 (by
        rw [hP₀, he0]
        refine Over.OverMorphism.ext ?_
        rw [hleft, ← hlev, hlev₀]
        exact (hΦ₀ _).symm)
  have fib : ∀ b ∈ C, IsUnit (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i).det ∧
      ∃ (A : Out.PolAV (Sp ℂ)) (φ : A.A.left ⟶ Q.A.left)
        (lev : (Fin P₀.g ⊕ Fin P₀.g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ A.A)), PolPB A Q (y b) φ ∧
        PerLev A ((Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ *
          Matrix.of fun i j => P b (Pi.single (.inl j) 1) i) k lev ∧
        ∀ a, (lev a).left ≫ φ = y b ≫ (l a).left := fun b hb => by
    obtain ⟨A, φ, hφ, hgA, hm, t, ht⟩ := hL.polBaseChange _ _ (y b) Q
    have hgp : IsGrpPullback A.A Q.A (y b) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
      rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
      rfl⟩
    have hLA : LBIso A.L (Q.L.pull φ) := LBIso.symm ⟨t, ht⟩
    obtain ⟨Φ, hΦ, hΦW⟩ := exists_push_iff Q A hgp hLA
    have h₁ : ∀ z, (Φ.symm (e b z)).left ≫ φ = (e b z).left := fun z => by rw [← hΦ, Φ.apply_symm_apply]
    have hex := (he b (hC₁ hb)).1
    obtain ⟨q1, q2⟩ := perLev_of_periods hT hL.mulN A (hgA.trans hg₀.symm) k (fun z => Φ.symm (e b z))
      (fun z w => by rw [hex.1, map_mul]) (Φ.symm.surjective.comp hex.2.1)
      (ThetaPoint.isHolTo_fibre hφ _ (fun z => Over.w (Φ.symm (e b z))) (by simpa only [h₁] using hex.2.2.1)) (P b)
      (fun z => (map_eq_one_iff _ Φ.symm.injective).trans ((hball b hb).1.2.1 z)) (hball b hb).1.2.2.1
      (hball b hb).1.2.2.2.1 (hball b hb).1.2.2.2.2 fun n a a₂ c hn hc => by
        rw [hΦW, Φ.apply_symm_apply, Φ.apply_symm_apply]
        exact hwe b hb n a a₂ c hn hc
    exact ⟨q1, A, φ, _, ⟨hgp, hgA, hLA⟩, q2, fun a => by rw [h₁, ← hsec a b hb, hleft]⟩
  refine ⟨C, fun b => (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ *
    Matrix.of fun i j => P b (Pi.single (.inl j) 1) i, hCo, hC₀, hC₁.trans hB₁B, ?_, fun i j => ?_,
    fun b hb => (fib b hb).2⟩
  · have e1 : (Matrix.of fun i j => P b₀ (Pi.single (.inr j) 1) i) = 1 := by
      ext i j
      simp [hP₀, p₀, per, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]
    beta_reduce
    rw [e1, inv_one, Matrix.one_mul]
    ext i j
    simp [hP₀, p₀, per, Matrix.mulVec, dotProduct, Pi.single_apply]
  · have dh : ∀ i j, DifferentiableOn ℂ (fun b => (Matrix.of fun i j => P b (Pi.single (.inr j) 1) i)⁻¹ i j) C :=
      ThetaFamily.differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hPd _) i)
        fun b hb => Matrix.nonsing_inv_mul _ (fib b hb).1
    simp only [Matrix.mul_apply]
    exact DifferentiableOn.fun_sum fun l _ => (dh i l).fun_mul (differentiableOn_pi.1 (hPd _) l)

end GlobalTheory.PeriodLift
