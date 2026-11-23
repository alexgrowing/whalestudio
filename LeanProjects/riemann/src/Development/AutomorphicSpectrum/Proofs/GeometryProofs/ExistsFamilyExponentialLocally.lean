import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHolomorphicExponentialChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminantStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealSheafComapIdealAffineOpenOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc

section Hol

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem isHolTo_precomp {X : Scheme.{0}} {B : Set E} {y : E → (Sp ℂ ⟶ X)} (hy : IsHolTo B y)
    {W : Set E'} (hW : IsOpen W) {φ : E' → E} (hφ : DifferentiableOn ℂ φ W) (hm : Set.MapsTo φ W B) :
    IsHolTo W (fun w => y (φ w)) := by
  intro U f
  have hset : {w ∈ W | ⊤ ≤ y (φ w) ⁻¹ᵁ U} = W ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hm h1, h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  have hopen : IsOpen {w ∈ W | ⊤ ≤ y (φ w) ⁻¹ᵁ U} := by
    rw [hset]
    exact hφ.continuousOn.isOpen_inter_preimage hW (hy U f).1
  refine ⟨hopen, ?_⟩
  refine DifferentiableOn.comp (g := fun b => valAt' (y b) U f) (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U})
    (hy U f).2 (hφ.mono fun w hw => hw.1) ?_
  intro w hw
  exact ⟨hm hw.1, hw.2⟩

theorem isHolTo_congr {X : Scheme.{0}} {B : Set E} {y y' : E → (Sp ℂ ⟶ X)} (hy : IsHolTo B y)
    (h : ∀ b ∈ B, y' b = y b) : IsHolTo B y' := by
  intro U f
  have hset : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [← h b h1]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [h b h1]⟩
  rw [hset]
  refine ⟨(hy U f).1, (hy U f).2.congr fun b hb => ?_⟩
  simp only [h b hb.1]

theorem isHolTo_mono {X : Scheme.{0}} {B B' : Set E} {y : E → (Sp ℂ ⟶ X)} (hy : IsHolTo B y)
    (hB' : IsOpen B') (h : B' ⊆ B) : IsHolTo B' y :=
  isHolTo_precomp hy hB' differentiableOn_id h

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isHolTo_mul {W : Set E} (hW : IsOpen W) (ψ : E → (R →+* ℂ))
    (x y : ∀ w, Over.mk (spMap (ψ w)) ⟶ G) (hx : IsHolTo W fun w => (x w).left)
    (hy : IsHolTo W fun w => (y w).left) : IsHolTo W fun w => (x w * y w).left := by
  have hpb : IsPullback (fst G G).left (snd G G).left G.hom G.hom :=
    IsPullback.of_hasPullback G.hom G.hom
  have hl : IsHolTo W fun w => (lift (x w) (y w)).left := by
    refine HolPullback.isHolTo_of_components E W _ _ _ _ (fst G G).left (snd G G).left G.hom G.hom
      (fun w => (lift (x w) (y w)).left) hpb hW ?_ ?_
    · refine isHolTo_congr hx fun w _ => ?_
      rw [← Over.comp_left, lift_fst]
    · refine isHolTo_congr hy fun w _ => ?_
      rw [← Over.comp_left, lift_snd]
  refine isHolTo_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hl (μ[G]).left) fun w _ => ?_
  rw [Hom.mul_def, Over.comp_left]

theorem isHolTo_pow {W : Set E} (hW : IsOpen W) (ψ : E → (R →+* ℂ))
    (x : ∀ w, Over.mk (spMap (ψ w)) ⟶ G) (hx : IsHolTo W fun w => (x w).left) (k : ℕ) (hk : 0 < k) :
    IsHolTo W fun w => (x w ^ k).left := by
  induction k, hk using Nat.le_induction with
  | base => simpa using hx
  | succ k hk ih =>
    simp only [pow_succ]
    exact isHolTo_mul hW ψ _ _ ih hx

end Hol

section Inverse

open scoped ContDiff

variable {n g : ℕ}

theorem exists_family_inverse (b₀ : Fin n → ℂ) (L : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ))
    (hL : AnalyticAt ℂ L (b₀, 0))
    (h0 : ∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧
      HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) :
    ∃ Λ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ Λ (b₀, 0) ∧
      (∀ᶠ p in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), L (p.1, Λ p) = p.2) ∧
      (∀ᶠ p in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), Λ (p.1, L p) = p.2) := by
  set a : (Fin n → ℂ) × (Fin g → ℂ) := (b₀, 0) with ha
  obtain ⟨hL0, hLd⟩ := h0.self_of_nhds
  set Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin n → ℂ) × (Fin g → ℂ) := fun p => (p.1, L p) with hΦ
  have hΦa : Φ a = a := by simp only [hΦ, ha, hL0]
  have hΦan : AnalyticAt ℂ Φ a := analyticAt_fst.prod hL
  set L' := fderiv ℂ L a with hL'
  have hLfd : HasFDerivAt L L' a := hL.differentiableAt.hasFDerivAt
  have hinr : ∀ v : Fin g → ℂ, L' (0, v) = v := by
    intro v
    have h1 : HasFDerivAt (fun s : Fin g → ℂ => ((b₀, s) : (Fin n → ℂ) × (Fin g → ℂ)))
        (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (Fin g → ℂ)) 0 :=
      hasFDerivAt_prodMk_right b₀ 0
    have h2 := HasFDerivAt.comp (0 : Fin g → ℂ) (g := L) (f := fun s => ((b₀, s) : (Fin n → ℂ) × (Fin g → ℂ))) hLfd h1
    have h3 := h2.unique hLd
    have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T v) h3
    simpa using this
  have hsplit : ∀ u v, L' (u, v) = L' (u, 0) + v := by
    intro u v
    have : ((u, v) : (Fin n → ℂ) × (Fin g → ℂ)) = (u, 0) + (0, v) := by simp
    rw [this, map_add, hinr]
  let D : ((Fin n → ℂ) × (Fin g → ℂ)) →L[ℂ] ((Fin n → ℂ) × (Fin g → ℂ)) :=
    (ContinuousLinearMap.fst ℂ _ _).prod L'
  let Di : ((Fin n → ℂ) × (Fin g → ℂ)) →L[ℂ] ((Fin n → ℂ) × (Fin g → ℂ)) :=
    (ContinuousLinearMap.fst ℂ _ _).prod
      (ContinuousLinearMap.snd ℂ _ _ - L' ∘L (ContinuousLinearMap.inl ℂ _ _) ∘L (ContinuousLinearMap.fst ℂ _ _))
  let e : ((Fin n → ℂ) × (Fin g → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin g → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse D Di
      (by
        rintro ⟨u, v⟩
        simp [D, Di, hsplit u v])
      (by
        rintro ⟨u, v⟩
        change ((u, L' (u, v - L' (u, 0))) : (Fin n → ℂ) × (Fin g → ℂ)) = (u, v)
        rw [hsplit u]
        simp)
  have hΦd : HasFDerivAt Φ (e : _ →L[ℂ] _) a := by
    have := (hasFDerivAt_fst (𝕜 := ℂ) (p := a)).prodMk hLfd
    exact this
  have hc : ContDiffAt ℂ ω Φ a := hΦan.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hc.hasStrictFDerivAt' hΦd hn
  set F := hc.localInverse hΦd hn with hF
  have hFan : AnalyticAt ℂ F (Φ a) := by
    have := hc.to_localInverse hΦd hn
    exact this.analyticAt
  have hr : ∀ᶠ y in 𝓝 (Φ a), Φ (F y) = y := hs.eventually_right_inverse
  have hl : ∀ᶠ x in 𝓝 a, F (Φ x) = x := hs.eventually_left_inverse
  rw [hΦa] at hr hFan
  refine ⟨fun p => (F p).2, analyticAt_snd.comp hFan, ?_, ?_⟩
  · filter_upwards [hr] with y hy
    have h1 : (F y).1 = y.1 := by
      have := congrArg Prod.fst hy
      exact this
    have h2 : L (F y) = y.2 := by
      have := congrArg Prod.snd hy
      exact this
    have h3 : ((y.1, (F y).2) : (Fin n → ℂ) × (Fin g → ℂ)) = F y := by rw [← h1]
    rw [h3, h2]
  · filter_upwards [hl] with x hx
    have := congrArg Prod.snd hx
    exact this

theorem family_inverse_slices (b₀ : Fin n → ℂ) (L Λ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ))
    (hΛ : AnalyticAt ℂ Λ (b₀, 0))
    (h0 : ∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧
      HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0)
    (h1 : ∀ᶠ p in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), L (p.1, Λ p) = p.2)
    (h2 : ∀ᶠ p in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), Λ (p.1, L p) = p.2) :
    ∀ᶠ b in 𝓝 b₀, Λ (b, 0) = 0 ∧
      HasFDerivAt (fun z => Λ (b, z)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 := by
  have ht : Tendsto (fun b : Fin n → ℂ => ((b, 0) : (Fin n → ℂ) × (Fin g → ℂ))) (𝓝 b₀) (𝓝 (b₀, 0)) :=
    (Continuous.prodMk continuous_id continuous_const).tendsto b₀
  have hΛev : ∀ᶠ p in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)), AnalyticAt ℂ Λ p := hΛ.eventually_analyticAt
  filter_upwards [h0, ht.eventually h2, ht.eventually hΛev, ht.eventually h1.eventually_nhds] with b hb hb2 hbA hb1
  have hz : Λ (b, 0) = 0 := by
    have : Λ (b, L (b, 0)) = 0 := hb2
    rwa [hb.1] at this
  refine ⟨hz, ?_⟩
  have hcont : ContinuousAt (fun z => Λ (b, z)) 0 :=
    ContinuousAt.comp (f := fun z : Fin g → ℂ => ((b, z) : (Fin n → ℂ) × (Fin g → ℂ))) hbA.continuousAt
      (Continuous.prodMk continuous_const continuous_id).continuousAt
  have hd : HasFDerivAt (fun s => L (b, s))
      ((ContinuousLinearEquiv.refl ℂ (Fin g → ℂ) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
      ((fun z => Λ (b, z)) 0) := by
    simp only [hz]
    exact hb.2
  have hev : ∀ᶠ y in 𝓝 (0 : Fin g → ℂ), L (b, Λ (b, y)) = y := by
    have hc2 : Tendsto (fun z : Fin g → ℂ => ((b, z) : (Fin n → ℂ) × (Fin g → ℂ))) (𝓝 0) (𝓝 (b, 0)) :=
      (Continuous.prodMk continuous_const continuous_id).tendsto 0
    exact hc2.eventually hb1
  exact HasFDerivAt.of_local_left_inverse hcont hd hev

end Inverse

section Law

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}

def coord (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) {φ : R →+* ℂ} (x : Over.mk (spMap φ) ⟶ G) : Fin g → ℂ :=
  fun a => valAt' x.left V (t a)

variable [IsCommMonObj G] {ψ : (Fin n → ℂ) → (R →+* ℂ)} {b₀ : Fin n → ℂ} {V : G.left.Opens}
  {t : Fin g → Γ(G.left, V)} {N : ℕ} {f : Fin N → Γ(G.left, V)} {ε δ : ℝ}
  {Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)}

def chartMul (V : G.left.Opens) (t : Fin g → Γ(G.left, V))
    (Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G))
    (w : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) : Fin g → ℂ :=
  coord V t (Ψ w.1 w.2.1 * Ψ w.1 w.2.2)

theorem chartMul_law (hε : 0 < ε) (hδ : 0 < δ)
    (hΨ : IsHolTo (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ bz.1 bz.2).left))
    (hone : ∀ b ∈ ball b₀ ε, Ψ b 0 = 1)
    (hV : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V)
    (ht : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, coord V t (Ψ b z) = z)
    (hret : ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V →
      (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) →
      coord V t x ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (coord V t x)) :
    AnalyticAt ℂ (chartMul V t Ψ) (b₀, 0, 0) ∧ chartMul V t Ψ (b₀, 0, 0) = 0 ∧
      (∀ᶠ w in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)),
        Ψ w.1 w.2.1 * Ψ w.1 w.2.2 = Ψ w.1 (chartMul V t Ψ w)) ∧
      (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0),
        chartMul V t Ψ (p.1, p.2, 0) = p.2 ∧ chartMul V t Ψ (p.1, 0, p.2) = p.2) ∧
      (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0),
        chartMul V t Ψ (p.1, p.2.1, p.2.2) = chartMul V t Ψ (p.1, p.2.2, p.2.1)) ∧
      (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0, 0),
        chartMul V t Ψ (p.1, chartMul V t Ψ (p.1, p.2.1, p.2.2.1), p.2.2.2) =
          chartMul V t Ψ (p.1, p.2.1, chartMul V t Ψ (p.1, p.2.2.1, p.2.2.2))) := by
  have hb₀ : b₀ ∈ ball b₀ ε := mem_ball_self hε
  have h0ε : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε := mem_ball_self hε
  set W : Set ((Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) :=
    ball b₀ ε ×ˢ (ball (0 : Fin g → ℂ) ε ×ˢ ball (0 : Fin g → ℂ) ε) with hWdef
  have hWo : IsOpen W := isOpen_ball.prod (isOpen_ball.prod isOpen_ball)
  have hx : IsHolTo W (fun w => (Ψ w.1 w.2.1).left) :=
    isHolTo_precomp hΨ hWo (φ := fun w => (w.1, w.2.1)) (by fun_prop) fun w hw => ⟨hw.1, hw.2.1⟩
  have hy : IsHolTo W (fun w => (Ψ w.1 w.2.2).left) :=
    isHolTo_precomp hΨ hWo (φ := fun w => (w.1, w.2.2)) (by fun_prop) fun w hw => ⟨hw.1, hw.2.2⟩
  have hQ : IsHolTo W (fun w => (Ψ w.1 w.2.1 * Ψ w.1 w.2.2).left) :=
    isHolTo_mul hWo (fun w => ψ w.1) (fun w => Ψ w.1 w.2.1) (fun w => Ψ w.1 w.2.2) hx hy
  have hq0 : Ψ b₀ 0 * Ψ b₀ 0 = Ψ b₀ 0 := by rw [hone b₀ hb₀, _root_.one_mul]
  set w₀ : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) := (b₀, 0, 0) with hw₀
  have hw₀W : w₀ ∈ W := ⟨hb₀, h0ε, h0ε⟩
  set O := {w ∈ W | ⊤ ≤ (Ψ w.1 w.2.1 * Ψ w.1 w.2.2).left ⁻¹ᵁ V} with hOdef
  have hOo : IsOpen O := (hQ V 0).1
  have hw₀O : w₀ ∈ O := by
    refine ⟨hw₀W, ?_⟩
    change ⊤ ≤ (Ψ b₀ 0 * Ψ b₀ 0).left ⁻¹ᵁ V
    rw [hq0]
    exact hV b₀ hb₀ 0 h0ε
  have hON : O ∈ 𝓝 w₀ := hOo.mem_nhds hw₀O
  have hmd : DifferentiableOn ℂ (chartMul V t Ψ) O :=
    differentiableOn_pi.2 fun a => (hQ V (t a)).2
  have hm0 : chartMul V t Ψ w₀ = 0 := by
    change coord V t (Ψ b₀ 0 * Ψ b₀ 0) = 0
    rw [hq0]
    exact ht b₀ hb₀ 0 h0ε
  have hK : ∀ᶠ w in 𝓝 w₀, Ψ w.1 w.2.1 * Ψ w.1 w.2.2 = Ψ w.1 (chartMul V t Ψ w) := by
    have hb : ∀ᶠ w in 𝓝 w₀, w.1 ∈ ball b₀ δ :=
      (continuous_fst.tendsto w₀).eventually (ball_mem_nhds b₀ hδ)
    have hj : ∀ᶠ w in 𝓝 w₀, ∀ j, ‖valAt' (Ψ w.1 w.2.1 * Ψ w.1 w.2.2).left V (f j) -
        valAt' (Ψ b₀ 0).left V (f j)‖ < δ := by
      refine eventually_all.2 fun j => ?_
      have hc : ContinuousAt (fun w : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
          valAt' (Ψ w.1 w.2.1 * Ψ w.1 w.2.2).left V (f j)) w₀ :=
        ((hQ V (f j)).2.differentiableAt hON).continuousAt
      have hval : valAt' (Ψ w₀.1 w₀.2.1 * Ψ w₀.1 w₀.2.2).left V (f j) = valAt' (Ψ b₀ 0).left V (f j) := by
        change valAt' (Ψ b₀ 0 * Ψ b₀ 0).left V (f j) = _
        rw [hq0]
      have := hc.tendsto
      rw [hval] at this
      have h2 := (Metric.tendsto_nhds.1 this) δ hδ
      filter_upwards [h2] with w hw
      simpa [dist_eq_norm] using hw
    filter_upwards [hON, hb, hj] with w hw1 hw2 hw3
    exact (hret w.1 hw2 _ hw1.2 hw3).2
  have hWN : W ∈ 𝓝 w₀ := hWo.mem_nhds hw₀W
  refine ⟨GlobalTheory.SCV.analyticAt_of_differentiableOn hmd hON, hm0, hK, ?_, ?_, ?_⟩
  · have hn : ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε ∈ 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) :=
      (isOpen_ball.prod isOpen_ball).mem_nhds ⟨hb₀, h0ε⟩
    filter_upwards [hn] with p hp
    constructor
    · change coord V t (Ψ p.1 p.2 * Ψ p.1 0) = p.2
      rw [hone p.1 hp.1, _root_.mul_one]
      exact ht _ hp.1 _ hp.2
    · change coord V t (Ψ p.1 0 * Ψ p.1 p.2) = p.2
      rw [hone p.1 hp.1, _root_.one_mul]
      exact ht _ hp.1 _ hp.2
  · refine Eventually.of_forall fun p => ?_
    change coord V t (Ψ p.1 p.2.1 * Ψ p.1 p.2.2) = coord V t (Ψ p.1 p.2.2 * Ψ p.1 p.2.1)
    rw [mul_comm]
  · have t1 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        ((p.1, p.2.1, p.2.2.1) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ))) (𝓝 (b₀, 0, 0, 0)) (𝓝 w₀) :=
      (by fun_prop : Continuous (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        ((p.1, p.2.1, p.2.2.1) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)))).tendsto (b₀, 0, 0, 0)
    have t2 : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        ((p.1, p.2.2.1, p.2.2.2) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ))) (𝓝 (b₀, 0, 0, 0)) (𝓝 w₀) :=
      (by fun_prop : Continuous (fun p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) =>
        ((p.1, p.2.2.1, p.2.2.2) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)))).tendsto (b₀, 0, 0, 0)
    filter_upwards [t1.eventually hK, t2.eventually hK] with p h1 h2
    have h1' : Ψ p.1 p.2.1 * Ψ p.1 p.2.2.1 = Ψ p.1 (chartMul V t Ψ (p.1, p.2.1, p.2.2.1)) := h1
    have h2' : Ψ p.1 p.2.2.1 * Ψ p.1 p.2.2.2 = Ψ p.1 (chartMul V t Ψ (p.1, p.2.2.1, p.2.2.2)) := h2
    change coord V t (Ψ p.1 (chartMul V t Ψ (p.1, p.2.1, p.2.2.1)) * Ψ p.1 p.2.2.2) =
      coord V t (Ψ p.1 p.2.1 * Ψ p.1 (chartMul V t Ψ (p.1, p.2.2.1, p.2.2.2)))
    rw [← h1', ← h2', _root_.mul_assoc]

end Law

section Family

theorem pow_of_add {g : ℕ} {A : Type} [CommGroup A] (e : (Fin g → ℂ) → A) (he : ∀ z w, e (z + w) = e z * e w)
    (y : Fin g → ℂ) (k : ℕ) : e ((k : ℂ) • y) = e y ^ k := by
  induction k with
  | zero =>
    have h0 := he 0 0
    rw [add_zero] at h0
    simpa using h0
  | succ k ih => rw [Nat.cast_succ, add_smul, _root_.one_smul, he, ih, pow_succ]

theorem isDerivAt0_of_reparam {g : ℕ} {X : Scheme.{0}} {e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {l : (Fin g → ℂ) → (Fin g → ℂ)}
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e w v)
    (hl : HasFDerivAt l (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) (hl0 : l 0 = 0)
    (hev : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), e' z = e (l z))
    (hhol : ∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ e 0 ⁻¹ᵁ U →
      DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0) : IsDerivAt0 e' w v := by
  refine ⟨by rw [hev.self_of_nhds, hl0]; exact hd.1, fun U h f => ?_⟩
  have hU : ⊤ ≤ e 0 ⁻¹ᵁ U := by
    rw [← hd.1, Scheme.Hom.comp_preimage]
    exact fun p _ => h (Set.mem_univ _)
  rw [hd.2 U h f]
  have hcongr : (fun z => valAt' (e' z) U f) =ᶠ[𝓝 0] (fun z => valAt' (e z) U f) ∘ l := by
    filter_upwards [hev] with z hz
    simp only [Function.comp, hz]
  rw [hcongr.fderiv_eq]
  have hh : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (l 0) := by
    rw [hl0]
    exact (hhol U f hU).hasFDerivAt
  rw [(hh.comp 0 hl).fderiv]
  simp

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {g n : ℕ}
  {ψ : (Fin n → ℂ) → (R →+* ℂ)} {b₀ : Fin n → ℂ}

theorem family_isHolTo {ρ : ℝ} (hρ : 0 < ρ) (ex : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G))
    (hadd : ∀ b ∈ ball b₀ ρ, ∀ z w, ex b (z + w) = ex b z * ex b w)
    (hbase : IsHolTo (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ)
      (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (ex bz.1 bz.2).left)) :
    IsHolTo (ball b₀ ρ ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (ex bz.1 bz.2).left) := by
  have hM : ∀ M : ℕ, 0 < M → IsHolTo (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) (M * ρ))
      (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (ex bz.1 bz.2).left) := by
    intro M hM
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    have hWo : IsOpen (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) (M * ρ)) := isOpen_ball.prod isOpen_ball
    have h1 : IsHolTo (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) (M * ρ))
        (fun p : (Fin n → ℂ) × (Fin g → ℂ) => (ex p.1 ((M : ℂ)⁻¹ • p.2)).left) := by
      refine isHolTo_precomp hbase hWo (φ := fun p => (p.1, (M : ℂ)⁻¹ • p.2)) (by fun_prop) fun p hp => ⟨hp.1, ?_⟩
      have h2 : ‖p.2‖ < M * ρ := mem_ball_zero_iff.1 hp.2
      refine mem_ball_zero_iff.2 ?_
      rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_lt_iff₀ hMr]
      exact h2
    have h2 := isHolTo_pow hWo (fun p => ψ p.1) (fun p => ex p.1 ((M : ℂ)⁻¹ • p.2)) h1 M hM
    refine isHolTo_congr h2 fun p hp => ?_
    rw [← pow_of_add (ex p.1) (hadd p.1 hp.1), smul_inv_smul₀ hMc]
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_local fun U f p hp hU => ?_
  obtain ⟨M, hM0, hMz⟩ := localHom_exists_nat hρ ‖p.2‖
  have hh := hM M hM0 U f
  exact ⟨_, hh.1.mem_nhds ⟨⟨hp.1, mem_ball_zero_iff.2 hMz⟩, hU⟩, fun q hq => ⟨⟨hq.1.1, trivial⟩, hq.2⟩, hh.2⟩

variable {V : G.left.Opens} {t : Fin g → Γ(G.left, V)} {N : ℕ} {f : Fin N → Γ(G.left, V)} {ε δ ρ : ℝ}
  {Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)}

theorem famExp_of_inverse (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (hρ : 0 < ρ) (hρε : ρ ≤ ε) (hρδ : ρ ≤ δ)
    (hΨ : IsHolTo (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ bz.1 bz.2).left))
    (hder : ∀ b ∈ ball b₀ ε, ∀ a : Fin g, IsDerivAt0 (fun z => (Ψ b z).left) (Pi.single a 1)
      (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left))
    (hV : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V)
    (ht : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, coord V t (Ψ b z) = z)
    (hret : ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V →
      (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) →
      coord V t x ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (coord V t x))
    (L Λ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ))
    (hA : ∀ b ∈ ball b₀ ρ, ∀ z ∈ ball (0 : Fin g → ℂ) ρ, Λ (b, z) ∈ ball (0 : Fin g → ℂ) ε ∧ L (b, Λ (b, z)) = z ∧
      Λ (b, L (b, z)) = z ∧ AnalyticAt ℂ Λ (b, z) ∧ AnalyticAt ℂ L (b, z))
    (hB : ∀ b ∈ ball b₀ ρ, L (b, 0) = 0 ∧ Λ (b, 0) = 0 ∧
      HasFDerivAt (fun z => Λ (b, z)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
      ∀ j, ‖valAt' (Ψ b 0).left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ)
    (hC : ∀ b ∈ ball b₀ ρ, ∀ z ∈ ball (0 : Fin g → ℂ) ρ, ∀ w ∈ ball (0 : Fin g → ℂ) ρ, z + w ∈ ball (0 : Fin g → ℂ) ρ →
      Ψ b (Λ (b, z + w)) = Ψ b (Λ (b, z)) * Ψ b (Λ (b, w))) :
    Nonempty (FamExp G M (ball b₀ ρ) ψ) := by
  classical
  have hε : 0 < ε := hρ.trans_le hρε
  have h0ε : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε := mem_ball_self hε
  have h0ρ : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ρ := mem_ball_self hρ
  have hext := fun (b : Fin n → ℂ) (hb : b ∈ ball b₀ ρ) =>
    existsUnique_extension_of_ball g (Over.mk (spMap (ψ b)) ⟶ G) ρ hρ (fun z => Ψ b (Λ (b, z)))
      (fun z hz w hw hzw => hC b hb z hz w hw hzw)
  let ex : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G) :=
    fun b => if hb : b ∈ ball b₀ ρ then (hext b hb).choose else fun _ => 1
  have hexa : ∀ b ∈ ball b₀ ρ, (∀ z w, ex b (z + w) = ex b z * ex b w) ∧
      ∀ z ∈ ball (0 : Fin g → ℂ) ρ, ex b z = Ψ b (Λ (b, z)) := by
    intro b hb
    simp only [ex, dif_pos hb]
    exact (hext b hb).choose_spec.1
  have hBo : IsOpen (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := isOpen_ball.prod isOpen_ball
  have hΛd : DifferentiableOn ℂ Λ (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ) := fun p hp =>
    (hA p.1 hp.1 p.2 hp.2).2.2.2.1.differentiableAt.differentiableWithinAt
  have hbase : IsHolTo (ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ)
      (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (ex bz.1 bz.2).left) := by
    refine isHolTo_congr (isHolTo_precomp hΨ hBo (φ := fun p => (p.1, Λ p))
      (differentiableOn_fst.prodMk hΛd) fun p hp => ⟨ball_subset_ball hρε hp.1, ?_⟩) fun p hp => ?_
    · exact (hA p.1 hp.1 p.2 hp.2).1
    · rw [(hexa p.1 hp.1).2 p.2 hp.2]
  refine ⟨{ ex := ex, add := fun b hb z w => (hexa b hb).1 z w,
            hol := family_isHolTo hρ ex (fun b hb => (hexa b hb).1) hbase, diff := ?_, log := ?_ }⟩
  · intro b hb a
    have hb' := ball_subset_ball hρε hb
    refine isDerivAt0_of_reparam (hder b hb' a) (hB b hb).2.2.1 (hB b hb).2.1 ?_ ?_
    · filter_upwards [ball_mem_nhds (0 : Fin g → ℂ) hρ] with z hz
      rw [(hexa b hb).2 z hz]
    · intro U f' hU
      have hs : IsHolTo (ball (0 : Fin g → ℂ) ε) (fun z => (Ψ b z).left) :=
        isHolTo_precomp hΨ isOpen_ball (φ := fun z => (b, z)) (by fun_prop) fun z hz => ⟨hb', hz⟩
      exact (hs U f').2.differentiableAt ((hs U f').1.mem_nhds ⟨h0ε, hU⟩)
  · intro b₁ hb₁
    have hb₁' := ball_subset_ball hρε hb₁
    have hex0 : ex b₁ 0 = Ψ b₁ 0 := by rw [(hexa _ hb₁).2 0 h0ρ, (hB _ hb₁).2.1]
    let πL : ((Fin n → ℂ) × (Fin (g + N) → ℂ)) →L[ℂ] ((Fin n → ℂ) × (Fin g → ℂ)) :=
      (ContinuousLinearMap.fst ℂ _ _).prod
        ((ContinuousLinearMap.pi fun a : Fin g => ContinuousLinearMap.proj (Fin.castAdd N a)) ∘L
          (ContinuousLinearMap.snd ℂ _ _))
    set y₁ : Fin (g + N) → ℂ := fun j => valAt' (ex b₁ 0).left V (Fin.append t f j) with hy₁
    have hy1 : (fun a => y₁ (Fin.castAdd N a)) = 0 := by
      funext a
      simp only [hy₁, Fin.append_left, hex0]
      exact congrFun (ht _ hb₁' 0 h0ε) a
    have hy2 : ∀ j, y₁ (Fin.natAdd g j) = valAt' (Ψ b₁ 0).left V (f j) := by
      intro j
      simp only [hy₁, Fin.append_right, hex0]
    have hπ : πL (b₁, y₁) = (b₁, 0) := by
      change ((b₁, fun a => y₁ (Fin.castAdd N a)) : (Fin n → ℂ) × (Fin g → ℂ)) = (b₁, 0)
      rw [hy1]
    have hLan : AnalyticAt ℂ L (b₁, 0) := (hA b₁ hb₁ 0 h0ρ).2.2.2.2
    have hn : ball b₀ ρ ×ˢ ball (0 : Fin g → ℂ) ρ ∈ 𝓝 ((b₁, 0) : (Fin n → ℂ) × (Fin g → ℂ)) :=
      hBo.mem_nhds ⟨hb₁, h0ρ⟩
    refine ⟨V, g + N, Fin.append t f, fun p => L (p.1, fun a => p.2 (Fin.castAdd N a)), ?_, ?_, ?_, ?_⟩
    · rw [hex0]
      exact hV b₁ hb₁' 0 h0ε
    · have h1 : AnalyticAt ℂ L (πL (b₁, y₁)) := by rw [hπ]; exact hLan
      exact AnalyticAt.comp h1 (πL.analyticAt _)
    · filter_upwards [hn] with bz hbz
      have hs := hA bz.1 hbz.1 bz.2 hbz.2
      have e1 := (hexa _ hbz.1).2 _ hbz.2
      have e2 : (fun a => valAt' (ex bz.1 bz.2).left V (Fin.append t f (Fin.castAdd N a))) = Λ (bz.1, bz.2) := by
        simp only [Fin.append_left, e1]
        exact ht _ (ball_subset_ball hρε hbz.1) _ hs.1
      change L (bz.1, fun a => valAt' (ex bz.1 bz.2).left V (Fin.append t f (Fin.castAdd N a))) = bz.2
      rw [e2]
      exact hs.2.1
    · have hev1 : ∀ᶠ q in 𝓝 ((b₁, 0) : (Fin n → ℂ) × (Fin g → ℂ)),
          q.1 ∈ ball b₀ ρ ∧ q.2 ∈ ball (0 : Fin g → ℂ) ρ ∧ L q ∈ ball (0 : Fin g → ℂ) ρ := by
        have hc := hLan.continuousAt.tendsto
        rw [(hB b₁ hb₁).1] at hc
        filter_upwards [hn, hc.eventually (ball_mem_nhds (0 : Fin g → ℂ) hρ)] with q h1 h2
        exact ⟨h1.1, h1.2, h2⟩
      have hπt : Tendsto πL (𝓝 (b₁, y₁)) (𝓝 (b₁, 0)) := by
        have := πL.continuous.tendsto (b₁, y₁)
        rwa [hπ] at this
      have hev2 : ∀ᶠ p : (Fin n → ℂ) × (Fin (g + N) → ℂ) in 𝓝 (b₁, y₁), ∀ j,
          ‖p.2 (Fin.natAdd g j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ := by
        refine eventually_all.2 fun j => ?_
        have hcont : Continuous (fun p : (Fin n → ℂ) × (Fin (g + N) → ℂ) =>
            ‖p.2 (Fin.natAdd g j) - valAt' (Ψ b₀ 0).left V (f j)‖) := by fun_prop
        have hlt : ‖y₁ (Fin.natAdd g j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ := by
          rw [hy2]
          exact (hB b₁ hb₁).2.2.2 j
        exact (hcont.tendsto (b₁, y₁)).eventually (Iio_mem_nhds hlt)
      filter_upwards [hπt.eventually hev1, hev2] with p h1 h2 x hxV hxf
      obtain ⟨hpb, hps, hpL⟩ := h1
      have hpb' : p.1 ∈ ball b₀ ρ := hpb
      have hps' : (fun a => p.2 (Fin.castAdd N a)) ∈ ball (0 : Fin g → ℂ) ρ := hps
      have hpL' : L (p.1, fun a => p.2 (Fin.castAdd N a)) ∈ ball (0 : Fin g → ℂ) ρ := hpL
      have hT : coord V t x = fun a => p.2 (Fin.castAdd N a) := by
        funext a
        have := hxf (Fin.castAdd N a)
        rw [Fin.append_left] at this
        exact this
      have hf : ∀ j, valAt' x.left V (f j) = p.2 (Fin.natAdd g j) := by
        intro j
        have := hxf (Fin.natAdd g j)
        rw [Fin.append_right] at this
        exact this
      have hx := (hret p.1 (ball_subset_ball hρδ hpb') x hxV (fun j => by rw [hf]; exact h2 j)).2
      rw [hT] at hx
      refine hx.trans ?_
      change Ψ p.1 (fun a => p.2 (Fin.castAdd N a)) = ex p.1 (L (p.1, fun a => p.2 (Fin.castAdd N a)))
      rw [(hexa p.1 hpb').2 _ hpL', (hA p.1 hpb' _ hps').2.2.1]

end Family

end GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ExpLoc in

theorem exists_famExp_near : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ ε : ℝ, 0 < ε ∧ ball b₀ ε ⊆ B ∧ Nonempty (FamExp G M (ball b₀ ε) ψ) := by
  intro R _ G _ _ g n M B ψ hsm hψ b₀ hb₀
  obtain ⟨V, t, N, f, ε, Ψ, hε, hsub, hΨ, hfib, δ, hδ, hret⟩ := GlobalTheory.T.local_holomorphic_exponential_chart R G g n M B ψ hsm hψ b₀ hb₀
  have hone : ∀ b ∈ ball b₀ ε, Ψ b 0 = 1 := fun b hb => (hfib b hb).1
  have hder := fun b hb => (hfib b hb).2.1
  have hV : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V :=
    fun b hb z hz => ((hfib b hb).2.2 z hz).1
  have ht : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, coord V t (Ψ b z) = z :=
    fun b hb z hz => funext ((hfib b hb).2.2 z hz).2
  have hret' : ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V →
      (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) →
      coord V t x ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (coord V t x) := hret
  obtain ⟨hman, hm0, hK, hunit, hcomm, hassoc⟩ := chartMul_law (f := f) hε hδ hΨ hone hV ht hret'
  obtain ⟨L, hLan, hL0, hLadd⟩ := GlobalTheory.T.holomorphic_group_law_germ n g b₀ (chartMul V t Ψ) hman hunit hcomm hassoc
  obtain ⟨Λ, hΛan, hLΛ, hΛL⟩ := exists_family_inverse b₀ L hLan hL0
  have hsl := family_inverse_slices b₀ L Λ hΛan hL0 hLΛ hΛL
  have hΛ0 : Λ (b₀, 0) = 0 := hsl.self_of_nhds.1
  have hmc : Tendsto (fun w : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => ((w.1, chartMul V t Ψ w) : (Fin n → ℂ) × (Fin g → ℂ)))
      (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) := by
    have h1 : ContinuousAt (fun w : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) => ((w.1, chartMul V t Ψ w) : (Fin n → ℂ) × (Fin g → ℂ))) (b₀, 0, 0) :=
      continuousAt_fst.prodMk hman.continuousAt
    have h2 := h1.tendsto
    simp only [hm0] at h2
    exact h2
  have hF : ∀ᶠ w in 𝓝 ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)),
      Ψ w.1 w.2.1 * Ψ w.1 w.2.2 = Ψ w.1 (chartMul V t Ψ w) ∧
      L (w.1, chartMul V t Ψ w) = L (w.1, w.2.1) + L (w.1, w.2.2) ∧
      Λ (w.1, L (w.1, chartMul V t Ψ w)) = chartMul V t Ψ w := by
    filter_upwards [hK, hLadd, hmc.eventually hΛL] with w h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨r₁, hr₁, hF'⟩ := Metric.eventually_nhds_iff_ball.1 hF
  have hclose : ∀ᶠ b in 𝓝 b₀, ∀ j, ‖valAt' (Ψ b 0).left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ := by
    have hs : IsHolTo (ball b₀ ε) (fun b => (Ψ b 0).left) :=
      isHolTo_precomp hΨ isOpen_ball (φ := fun b => (b, 0)) (by fun_prop) fun b hb => ⟨hb, mem_ball_self hε⟩
    refine eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun b => valAt' (Ψ b 0).left V (f j)) b₀ :=
      ((hs V (f j)).2.differentiableAt
        ((hs V (f j)).1.mem_nhds ⟨mem_ball_self hε, hV b₀ (mem_ball_self hε) 0 (mem_ball_self hε)⟩)).continuousAt
    have h2 := (Metric.tendsto_nhds.1 hc.tendsto) δ hδ
    filter_upwards [h2] with b hb
    simpa [dist_eq_norm] using hb
  have hfst : Tendsto (fun p : (Fin n → ℂ) × (Fin g → ℂ) => p.1) (𝓝 (b₀, 0)) (𝓝 b₀) := continuous_fst.tendsto (b₀, 0)
  have hΛt : Tendsto Λ (𝓝 (b₀, 0)) (𝓝 0) := by
    have := hΛan.continuousAt.tendsto
    rwa [hΛ0] at this
  have hE : ∀ᶠ p in 𝓝 ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)),
      Λ p ∈ ball (0 : Fin g → ℂ) ε ∧ Λ p ∈ ball (0 : Fin g → ℂ) r₁ ∧ L (p.1, Λ p) = p.2 ∧ Λ (p.1, L p) = p.2 ∧
      AnalyticAt ℂ Λ p ∧ AnalyticAt ℂ L p ∧ p.1 ∈ ball b₀ r₁ ∧
      (L (p.1, 0) = 0 ∧ Λ (p.1, 0) = 0 ∧ HasFDerivAt (fun z => Λ (p.1, z)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
        ∀ j, ‖valAt' (Ψ p.1 0).left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) := by
    filter_upwards [hΛt.eventually (ball_mem_nhds _ hε), hΛt.eventually (ball_mem_nhds _ hr₁), hLΛ, hΛL,
      hΛan.eventually_analyticAt, hLan.eventually_analyticAt, hfst.eventually (ball_mem_nhds _ hr₁),
      hfst.eventually hL0, hfst.eventually hsl, hfst.eventually hclose] with p h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8.1, h9.1, h9.2, h10⟩
  obtain ⟨ρ₀, hρ₀, hE'⟩ := Metric.eventually_nhds_iff_ball.1 hE
  have hmem : ∀ (ρ : ℝ), ρ ≤ ρ₀ → ∀ b ∈ ball b₀ ρ, ∀ z ∈ ball (0 : Fin g → ℂ) ρ,
      ((b, z) : (Fin n → ℂ) × (Fin g → ℂ)) ∈ ball ((b₀, 0) : (Fin n → ℂ) × (Fin g → ℂ)) ρ₀ := by
    intro ρ hρ b hb z hz
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball hρ hb, ball_subset_ball hρ hz⟩
  set ρ : ℝ := min ρ₀ (min ε δ) with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ (lt_min hε hδ)
  have hρ₀' : ρ ≤ ρ₀ := min_le_left _ _
  have hρε : ρ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, (ball_subset_ball hρε).trans hsub, ?_⟩
  refine famExp_of_inverse (f := f) M hρ hρε hρδ hΨ hder hV ht hret' L Λ ?_ ?_ ?_
  · intro b hb z hz
    obtain ⟨h1, -, h3, h4, h5, h6, -⟩ := hE' _ (hmem ρ hρ₀' b hb z hz)
    exact ⟨h1, h3, h4, h5, h6⟩
  · intro b hb
    exact (hE' _ (hmem ρ hρ₀' b hb 0 (mem_ball_self hρ))).2.2.2.2.2.2.2
  · intro b hb z hz w hw hzw
    obtain ⟨-, hs, hs1, -, -, -, hbr, -⟩ := hE' _ (hmem ρ hρ₀' b hb z hz)
    obtain ⟨-, hs', hs1', -, -, -, -, -⟩ := hE' _ (hmem ρ hρ₀' b hb w hw)
    have hin : ((b, Λ (b, z), Λ (b, w)) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) ∈
        ball ((b₀, 0, 0) : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ)) r₁ := by
      rw [← ball_prod_same, ← ball_prod_same]
      exact ⟨hbr, hs, hs'⟩
    obtain ⟨h1, h2, h3⟩ := hF' _ hin
    have h1' : Ψ b (Λ (b, z)) * Ψ b (Λ (b, w)) = Ψ b (chartMul V t Ψ (b, Λ (b, z), Λ (b, w))) := h1
    have h2' : L (b, chartMul V t Ψ (b, Λ (b, z), Λ (b, w))) = z + w := by
      have e1 : L (b, Λ (b, z)) = z := hs1
      have e2 : L (b, Λ (b, w)) = w := hs1'
      have := h2
      simp only [e1, e2] at this
      exact this
    have h3' : Λ (b, L (b, chartMul V t Ψ (b, Λ (b, z), Λ (b, w)))) = chartMul V t Ψ (b, Λ (b, z), Λ (b, w)) := h3
    rw [h2'] at h3'
    rw [h3', h1']

end GlobalTheory.CompanionTheory.Ar.Flat
