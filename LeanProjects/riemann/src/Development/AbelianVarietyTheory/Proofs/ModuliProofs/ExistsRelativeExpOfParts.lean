import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AnalyticAtCoordinateZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsChartWithParameters
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticParamInverse
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreconnectedSpacePtsOfIsIntegral

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.RelExp

theorem exists_lift {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)}
    {U : G.left.Opens} {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {Q : Set ((Fin m → ℂ) × (Fin g → ℂ))}
    {L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)} (hO : IsOpen O) (hQ : IsOpen Q)
    (hadd : ∀ b z w, e b (z + w) = e b z * e b w)
    (hinv : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → (b, crd0 t a) ∈ Q →
      e b (L (b, crd0 t a)) = a)
    {k : ℕ} {β : (Fin k → ℂ) → (Fin m → ℂ)} {x : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : Fin k → ℂ} {z₀ : Fin g → ℂ}
    (hβ : AnalyticAt ℂ β w₀) (hx : HolAt (fun w => pt (x w)) w₀) (h0 : e (β w₀) z₀ = x w₀)
    (he : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (β w₀, z₀))
    (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U) (hO₀ : (β w₀, crd U f (pt (1 : Over.mk (y (β w₀)) ⟶ G))) ∈ O)
    (hQ₀ : (β w₀, 0) ∈ Q) (hL0 : L (β w₀, 0) = 0) (hL : AnalyticAt ℂ L (β w₀, 0)) :
    ∃ ζ : (Fin k → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in 𝓝 w₀, e (β w) (ζ w) = x w := by
  have h1 := HolAt.comp (φ := fun w => (β w, z₀)) (v₀ := w₀) he (hβ.prod analyticAt_const)
  have h2 := HolAt.inv (y := fun w => y (β w)) (a := fun w => e (β w) z₀) h1
  have ha : HolAt (fun w => pt (x w * (e (β w) z₀)⁻¹)) w₀ :=
    HolAt.mul (y := fun w => y (β w)) (a := x) (b := fun w => (e (β w) z₀)⁻¹) hx h2
  have ha0 : x w₀ * (e (β w₀) z₀)⁻¹ = 1 := by rw [h0, mul_inv_cancel]
  have hc : AnalyticAt ℂ (fun w => (β w, crd0 t (x w * (e (β w) z₀)⁻¹))) w₀ :=
    hβ.prod (HolAt.analyticAt_coordinate_zero (a := fun w => x w * (e (β w) z₀)⁻¹) ha ha0 hU)
  have hc0 : (β w₀, crd0 t (x w₀ * (e (β w₀) z₀)⁻¹)) = (β w₀, 0) := by
    rw [ha0]; exact Prod.ext rfl (sub_self _)
  refine ⟨fun w => L (β w, crd0 t (x w * (e (β w) z₀)⁻¹)) + z₀, ?_, ?_, ?_⟩
  · simp only [hc0, hL0, zero_add]
  · exact (AnalyticAt.comp (g := L) (hc0 ▸ hL) hc).add analyticAt_const
  · filter_upwards [HolAt.eventually_near (a := fun w => x w * (e (β w) z₀)⁻¹) ha hβ.continuousAt ha0 hO hU hO₀,
      hc.continuousAt.eventually (hQ.mem_nhds (by simpa only [hc0] using hQ₀))] with w h3 h4
    rw [hadd, hinv _ _ h3.1 h3.2 h4, inv_mul_cancel_right]

theorem exists_relative_exp_of_parts
    (hchart : ∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v')
    (htan : ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)))
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    (hsub : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤) :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w := by
  intro k _ σ₀ X s₀ G _ g m B y b₀ e₀ _ hab hsm hB hb₀ _ hy ⟨he₀add, _, he₀hol, _, he₀tan⟩
  have := hab.comm
  have hy₀ : HolAt y b₀ := ⟨B, hB, hb₀, hy⟩
  obtain ⟨U, t, n, f, N, O, σ, hN, hO, hU, hO₀, hσ, hσN, hσinv, hunr⟩ :=
    hchart m g G.left X G.hom B y b₀ (pt (1 : Over.mk (y b₀) ⟶ G)) hsm hB hb₀ hy (Over.w _)
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_centred_chart hy₀ hN hU hO₀ hσ hσN hσinv
  obtain ⟨B', e, r, Q, L, hB', hb', hB'B, hr, hQ, hadd, hfib, hinv⟩ :=
    exists_global_exp hexp (hB.mem_nhds hb₀) hy₀ hO hU hO₀ hs1 hs2 hs3
  have hzero : ∀ {x : Sp ℂ ⟶ X} {u : (Fin g → ℂ) → (Over.mk x ⟶ G)}, (∀ z w, u (z + w) = u z * u w) → u 0 = 1 :=
    fun {x u} h => by
      have := h 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
  have he₀0 : e₀ 0 = 1 := hzero he₀add
  have he₀U : ⊤ ≤ pt (e₀ 0) ⁻¹ᵁ U := by rw [he₀0]; exact hU
  have hinj := ((htan X G (y b₀) g e₀ he₀hol).2 U t he₀U hunr).1 he₀tan
  set T₀ : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fderiv ℂ (fun z => crd U t (pt (e₀ z))) 0 with hT₀
  have hsurj : Function.Surjective T₀ :=
    (LinearMap.injective_iff_surjective (f := (T₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)))).1 hinj
  let T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := ContinuousLinearEquiv.ofBijective T₀ (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hT : ∀ z, T z = T₀ z := fun _ => rfl
  have hhol : ∀ b ∈ B', ∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 (T₀ q.2))) (b, z) :=
    fun b hb z => by
      have := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, T₀ q.2)) (v₀ := (b, z))
        ((hfib b hb).1 (T₀ z)) (analyticAt_fst.prod ((T₀.analyticAt _).comp analyticAt_snd))
      exact this
  refine ⟨B', fun b z => e b (T₀ z), r / (‖T₀‖ + 1), hB', hb', hB'B, ?_, by positivity,
    isHolTo_of_holAt (hB'.prod isOpen_univ) fun q hq => hhol q.1 hq.1 q.2, fun b hb => ?_, ?_⟩
  ·
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib b₀ hb'
    obtain ⟨ζ, hζ0, hζ, hζe⟩ := exists_lift hO hQ hadd hinv (β := fun _ : Fin g → ℂ => b₀) (x := e₀) (w₀ := 0)
      (z₀ := 0) analyticAt_const ⟨Set.univ, isOpen_univ, trivial, he₀hol⟩ ((hzero (hadd b₀)).trans he₀0.symm)
      (h1 0) h2 h3 h4 h6 h7
    have hd : HasFDerivAt ζ T₀ 0 := by
      have k1 := HasFDerivAt.comp (f := ζ) (0 : Fin g → ℂ) (hζ0.symm ▸ h5) hζ.differentiableAt.hasFDerivAt
      have k2 : HasFDerivAt (fun z => crd U t (pt (e₀ z))) _ 0 := k1.congr_of_eventuallyEq
        (hζe.mono fun z hz => by simp only [Function.comp, hz])
      rw [hT₀, k2.fderiv, ContinuousLinearMap.id_comp]
      exact hζ.differentiableAt.hasFDerivAt
    have tζ : Tendsto ζ (𝓝 0) (𝓝 0) := by simpa only [ContinuousAt, hζ0] using hζ.continuousAt
    have t1 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
    have t2 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
    have t3 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => p.1 + p.2) (𝓝 0) (𝓝 0) := by simpa using t1.add t2
    have t4 : Tendsto (fun p : (Fin g → ℂ) × (Fin g → ℂ) => ζ (p.1 + p.2) - (ζ p.1 + ζ p.2)) (𝓝 0) (𝓝 0) := by
      simpa using (tζ.comp t3).sub ((tζ.comp t1).add (tζ.comp t2))
    have hζT := eventuallyEq_of_additive_of_hasFDerivAt hd (by
      filter_upwards [t1.eventually hζe, t2.eventually hζe, t3.eventually hζe,
        t4.eventually (Metric.ball_mem_nhds 0 hr)] with p k1 k2 k3 k4
      refine sub_eq_zero.1 (h8 _ (mem_ball_zero_iff.1 k4) ?_)
      have k5 := hadd b₀ (ζ (p.1 + p.2) - (ζ p.1 + ζ p.2)) (ζ p.1 + ζ p.2)
      rw [sub_add_cancel, hadd b₀ (ζ p.1), k1, k2, k3, he₀add] at k5
      exact mul_eq_right.1 k5.symm)
    have key := addMonoidHom_eq_of_eventuallyEq
      (e := AddMonoidHom.mk' (fun z => Additive.ofMul (e b₀ (T₀ z))) fun z w => by rw [map_add, hadd]; rfl)
      (e' := AddMonoidHom.mk' (fun z => Additive.ofMul (e₀ z)) fun z w => by rw [he₀add]; rfl) (by
        filter_upwards [hζT, hζe] with z k1 k2
        exact congrArg Additive.ofMul (by rw [← k1]; exact k2))
    exact funext fun z => congrArg Additive.toMul (DFunLike.congr_fun key z)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib b hb
    have hH : IsHolTo Set.univ (fun z => pt (e b (T₀ z))) := isHolTo_of_holAt isOpen_univ fun z _ => by
      have := HolAt.comp (φ := fun z : Fin g → ℂ => (b, z)) (v₀ := z) (hhol b hb z)
        (analyticAt_const.prod analyticAt_id)
      exact this
    have hadd' : ∀ z w, e b (T₀ (z + w)) = e b (T₀ z) * e b (T₀ w) := fun z w => by rw [map_add, hadd]
    obtain ⟨k1, k2⟩ := htan X G (y b) g (fun z => e b (T₀ z)) hH
    refine ⟨⟨hadd', ?_, hH, k1, (k2 U t ?_ hunr).2 ?_⟩, fun z hz h => ?_⟩
    · refine Function.Surjective.comp (g := e b) ?_ hsurj
      let ε : (Fin g → ℂ) →+ Additive (Over.mk (y b) ⟶ G) :=
        AddMonoidHom.mk' (fun z => Additive.ofMul (e b z)) fun z w => by rw [hadd]; rfl
      have hc : Continuous fun u : Fin n ⊕ Fin g → ℂ => (b, fun j => u (Sum.inl j)) := by fun_prop
      have hc' : Continuous fun u : Fin n ⊕ Fin g → ℂ =>
        (b, (fun j => u (Sum.inr j)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) := by fun_prop
      have := hsub X G (y b) (AddSubgroup.toSubgroup' ε.range) U (Fin n ⊕ Fin g) (Sum.elim f t) _ hab.smooth
        hab.geomConnected ((hO.preimage hc).inter (hQ.preimage hc')) h2
        ⟨h3, by simpa only [Set.mem_preimage, Sum.elim_inr, sub_self] using h4⟩
        fun a ha hb => ⟨_, congrArg Additive.ofMul (hinv b a ha hb.1 hb.2)⟩
      intro a
      obtain ⟨z, hz⟩ : a ∈ AddSubgroup.toSubgroup' ε.range := this ▸ Subgroup.mem_top a
      exact ⟨z, congrArg Additive.toMul hz⟩
    · rw [hzero (u := fun z => e b (T₀ z)) hadd']; exact h2
    · have := HasFDerivAt.comp (f := T₀) (0 : Fin g → ℂ) (by rw [map_zero]; exact h5) T₀.hasFDerivAt
      have k3 : fderiv ℂ (fun z => crd U t (pt (e b (T₀ z)))) 0 = _ := this.fderiv
      rw [ContinuousLinearMap.id_comp] at k3
      exact k3.symm ▸ hinj
    · refine hinj ((h8 _ ((T₀.le_opNorm z).trans_lt ?_) h).trans (map_zero T₀).symm)
      rw [lt_div_iff₀ (by positivity)] at hz
      nlinarith [norm_nonneg z]
  · intro j W β x w₀ z₀ hW hw₀ hβ hβW hx h0
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfib _ (hβW hw₀)
    obtain ⟨ζ, hζ0, hζ, hζe⟩ := exists_lift hO hQ hadd hinv (x := x)
      (SCV.analyticAt_of_differentiableOn hβ (hW.mem_nhds hw₀)) ⟨W, hW, hw₀, hx⟩ h0 (h1 _) h2 h3 h4 h6 h7
    refine ⟨fun w => T.symm (ζ w), by simp only [hζ0, ← hT, T.symm_apply_apply], (T.symm.analyticAt _).comp hζ, ?_⟩
    filter_upwards [hζe] with w hw
    rw [← hT, T.apply_symm_apply, hw]

theorem exists_relative_exp :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (G : Over X) [GrpObj G] (g m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ G)), LocallyOfFiniteType s → IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) → ∃ (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (r : ℝ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ e b₀ = e₀ ∧ 0 < r ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ (∀ b ∈ B', ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) ∧ ∀ (n : ℕ) (W : Set (Fin n → ℂ)) (β : (Fin n → ℂ) → (Fin m → ℂ)) (x : ∀ w, Over.mk (y (β w)) ⟶ G) (w₀ : Fin n → ℂ) (z₀ : Fin g → ℂ), IsOpen W → w₀ ∈ W → DifferentiableOn ℂ β W → Set.MapsTo β W B' → IsHolTo W (fun w => (x w).left) → e (β w₀) z₀ = x w₀ → ∃ ζ : (Fin n → ℂ) → (Fin g → ℂ), ζ w₀ = z₀ ∧ AnalyticAt ℂ ζ w₀ ∧ ∀ᶠ w in nhds w₀, e (β w) (ζ w) = x w :=
  exists_relative_exp_of_parts (RelChart.exists_chart_with_parameters EtaleFamily.exists_holomorphic_sections)
    vertical_derivative_in_coordinates exists_param_exp_log_pi OpenSubgroupPts.subgroup_eq_top_of_nhds_one

end GlobalTheory.RelExp
