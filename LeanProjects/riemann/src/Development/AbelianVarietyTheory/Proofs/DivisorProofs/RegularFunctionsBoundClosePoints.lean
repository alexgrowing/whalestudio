import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerOfInducedBundleGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePlacesLgNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMetricGeneratedSectionsBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedSectionsMetricLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedSectionsFiniteMetricBoundStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HtLocBound

theorem valAt_mul {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f g : Z.functionField}
    (hf : RegAt (below y) f) (hg : RegAt (below y) g) : valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, Base.valAt_stalk, Base.valAt_stalk, Base.valAt_stalk, map_mul]

theorem unitAt_of_mul {X : Scheme.{0}} [IsIntegral X] {x : X} {f g : X.functionField} (hf : RegAt x f)
    (hg : RegAt x g) (h : UnitAt x (f * g)) : UnitAt x g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  obtain ⟨c, hc, e⟩ := h
  rw [← map_mul] at e
  obtain rfl := IsFractionRing.injective (X.presheaf.stalk x) X.functionField e
  exact ⟨b, isUnit_of_mul_isUnit_right hc, rfl⟩

theorem regAt_div {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {x : X} {f g : X.functionField}
    (hf : D.RegularAt x f) (hg : D.GeneratesAt x g) : RegAt x (f / g) := by
  obtain ⟨e, he, hu⟩ := hg
  have h1 := he.regularAt_iff.1 hf
  have hg0 : g ≠ 0 := left_ne_zero_of_mul hu.ne_zero
  have he0 : (e : X.functionField) ≠ 0 := e.ne_zero
  have h2 : f / g = f * e * (g * e)⁻¹ := by field_simp
  rw [h2]
  exact h1.mul hu.inv.regAt

theorem generatesAt_of_div {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {x : X} {s t : X.functionField}
    (hs : D.RegularAt x s) (ht : D.GeneratesAt x t) (h : RegAt x (t / s)) (hs0 : s ≠ 0) :
    D.GeneratesAt x s := by
  obtain ⟨e, he, hu⟩ := ht
  refine ⟨e, he, unitAt_of_mul h (he.regularAt_iff.1 hs) ?_⟩
  have h2 : t / s * (s * e) = t * e := by field_simp
  rw [h2]
  exact hu

theorem htLoc : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y), Y.ample A.D →
  (∃ (M : Model Y) (L : GlobalTheory.HermLB M.p) (q : ℕ+), A.Induced M L q 0) → (∀ σ, C.mSmooth Y σ A.D (A.m σ)) →
  ∃ (N : ℕ) (f : Fin N → Y.Fn), (∃ U : Y.X.Opens, (U : Set Y.X).Nonempty ∧ ∀ x ∈ U, ∀ i, RegAt x (f i)) ∧
    ∀ (a : ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support b).Finite →
      ∃ K : ℝ, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → (∀ i, RegAt x (f i)) →
        (∀ (σ : F →+* ℂ) (z : Pts Y σ), under z = x → ∀ i, ‖ratVal (f i) z‖ ≤ a) →
        (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), below y.1 = x → ∀ i,
          e.w (valAt y.1 (f i)) ≤ Real.exp (b v)) →
        A.ht x ≤ K := by
  intro F _ _ C Y A hA ⟨M, L, q, hI⟩ hsm
  obtain ⟨m, hm, hg⟩ := InducedGen.exists_isGenerated_pow F C Y A M L q 0 hI hA
  have hI' := InducedPow.induced_pow F C Y A M L q ⟨m, hm⟩ 0 hI
  generalize hk : q * ⟨m, hm⟩ = k at hI'
  obtain ⟨-, r, hr, -, -⟩ := id hI'
  obtain ⟨N, σ, hσ⟩ := hg
  have hgen : ∀ x : Y.X, ∃ i, ((k : ℕ) • A.D).GeneratesAt x (hr.rat (σ i)) := fun x => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hσ.ge (Set.mem_univ x))
    exact ⟨i, (hr.generatesAt_rat_iff _).2 hi⟩
  obtain ⟨i₀, hi₀⟩ := hgen (genericPoint Y.X)
  let s : Fin (N + 1) → Y.Fn := Fin.cons (hr.rat (σ i₀)) fun i => hr.rat (σ i)
  have hsH : ∀ i, s i ∈ Y.H0 ((k : ℕ) • A.D) := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i <;> exact Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 (CartierDiv.mem_sections.1 (hr.rat_mem _))
  have hsgen : ∀ x : Y.X, ∃ i, ((k : ℕ) • A.D).GeneratesAt x (s i) := fun x =>
    have ⟨i, hi⟩ := hgen x; ⟨i.succ, hi⟩
  have hne : s 0 ≠ 0 := hi₀.ne_zero
  refine ⟨N + 1, fun i => s i / s 0, ⟨Out.nonzeroLocus (σ i₀), ⟨genericPoint Y.X, (hr.generatesAt_rat_iff _).1 hi₀⟩,
    fun x hx i => regAt_div (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hsH i) x) ((hr.generatesAt_rat_iff _).2 hx)⟩, ?_⟩
  intro a b hb
  choose c hc hcz using fun τ : F →+* ℂ => GlobalTheory.T.generated_sections_metric_lower_bound F C Y A.D τ (A.m τ) (hsm τ) k (N + 1) s hsH hsgen
  obtain ⟨d, hd, hdy⟩ := GlobalTheory.T.generated_sections_finite_metric_bound F C Y A M _ k hI' (N + 1) s hsH hsgen
  refine ⟨(∑ τ : F →+* ℂ, (Real.log ((a ^ 2 + 1) / c τ) / 2 + (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk τ)) +
    ∑ᶠ v, (d v + b v)) / ((k : ℕ) * (A.n : ℕ) * (Module.finrank ℚ F : ℝ)), fun x hx hreg harch hfin => ?_⟩
  have hgx : ((k : ℕ) • A.D).GeneratesAt x (s 0) := by
    obtain ⟨j, hj⟩ := hsgen x
    exact generatesAt_of_div (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hsH 0) x) hj (hreg j) hne
  refine GlobalTheory.T.adelic_metric_generated_sections_bound F C Y A k x hx (fun y _ => finite_places_lg_ne_zero F C Y A M _ k 0 hI' y) (s 0) hgx
    (fun τ => Real.log ((a ^ 2 + 1) / c τ) / 2) (fun v => d v + b v)
    ((hd.union hb).subset (Function.support_add _ _)) ?_ ?_
  · intro τ z hz
    obtain ⟨j, hj⟩ := hcz τ z
    have e1 : s j = s j / s 0 * s 0 := (div_mul_cancel₀ _ hne).symm
    have hreg' : RegAt (under z) (s j / s 0) := hz ▸ hreg j
    have hpn := C.pn_mul Y τ _ (C.mPow Y τ A.D (k : ℕ) (A.m τ)) (s j / s 0) (s 0) z hreg'
      (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hsH 0) _)
    rw [← e1] at hpn
    rw [hpn] at hj
    have ha := harch τ z hz j
    have hp0 := C.pn_nonneg Y τ _ (C.mPow Y τ A.D (k : ℕ) (A.m τ)) (C.cx Y τ (s 0)) z
    have hn := norm_nonneg (ratVal (s j / s 0) z)
    have hc0 := hc τ
    have hex : Real.exp (-(2 * (Real.log ((a ^ 2 + 1) / c τ) / 2))) = c τ / (a ^ 2 + 1) := by
      rw [show -(2 * (Real.log ((a ^ 2 + 1) / c τ) / 2)) = -Real.log ((a ^ 2 + 1) / c τ) by ring,
        Real.exp_neg, Real.exp_log (by positivity), inv_div]
    rw [hex, div_le_iff₀ (by positivity)]
    have h2 : ‖ratVal (s j / s 0) z‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hn ha 2
    nlinarith [mul_le_mul_of_nonneg_right h2 hp0]
  · intro v e y hy
    obtain ⟨j, hj⟩ := hdy v e y
    rw [hy] at hj
    have hg0 : RegAt x (s 0 * (eqn A.D x : Y.Fn) ^ (k : ℕ)) := by
      have h1 := ((Base.isEqn_eqn A.D x).nsmul (k : ℕ)).regularAt_iff.1 (Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 (hsH 0) x)
      rwa [Units.val_pow_eq_pow_val] at h1
    have e1 : s j * (eqn A.D x : Y.Fn) ^ (k : ℕ) = s j / s 0 * (s 0 * (eqn A.D x : Y.Fn) ^ (k : ℕ)) := by
      field_simp
    rw [e1, valAt_mul y.1 (hy ▸ hreg j) (hy ▸ hg0), map_mul] at hj
    have hw := hfin v e y hy j
    have hW := e.w.nonneg (valAt y.1 (s 0 * (eqn A.D x : Y.Fn) ^ (k : ℕ)))
    have hE := Real.exp_pos ((k : ℕ) * A.lg v e y)
    have hb0 := Real.exp_pos (b v)
    have h2 : Real.exp (-d v) ≤ Real.exp (b v) * (e.w (valAt y.1 (s 0 * (eqn A.D x : Y.Fn) ^ (k : ℕ))) *
        Real.exp ((k : ℕ) * A.lg v e y)) := by
      refine hj.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hw (by positivity)
    rw [neg_add, Real.exp_add, Real.exp_neg (b v), mul_inv_le_iff₀ hb0]
    linarith

end GlobalTheory.HtLocBound
