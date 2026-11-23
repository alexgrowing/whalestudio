import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupGenTies
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GCauchyHolds
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SemicharUnitFrame
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.RelabellingGoodEmbeddingIsTypeFn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleValuePeriods
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivLevelSqEqAlpha
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HmEqDiagonal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusOfRows
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTorusAtOfIsTorusOf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdFockEqTranslate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsPiActLOfIsTorusOf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRepsLevelTranslates
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DatumNsmulEqZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaLower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_dmin {r : ℕ} (X : FD.Data E r) {x : FD.Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖FD.dmin X.Gm x τ i‖ = 1 := by
  unfold FD.dmin FD.lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp, FD.sgn]
  split_ifs <;> simp

theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem exists_mult_le {H : Host E} (Dw : Datum H) (m : ℕ) (h : Dw.p ≤ m ∨ Dw.q ≤ m) : ∃ τ, Dw.mult τ ≤ m := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    intro τ
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    rw [this]; simp
  have h0 : H.rt0 ≠ 0 := by
    intro h0
    have := H.sqrt_neg_disc_sq
    rw [h0] at this
    have hd := H.d_prime.pos
    have : (H.d : ℂ) = 0 := by simpa using this
    exact hd.ne' (by exact_mod_cast this)
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have h1 : H.rt0 ^ 2 = -(H.d : ℂ) := H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp [pow_two] at hre him
    have : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [this]
  have hne : -H.rt0 ≠ H.rt0 := fun h => h0 (by linear_combination -h / 2)
  have key : ∃ τ₁ τ₂ : E →+* ℂ, τ₁ (H.rt : E) = H.rt0 ∧ τ₂ (H.rt : E) = -H.rt0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hsq τ) with h | h
    · exact ⟨τ, (starRingEnd ℂ).comp τ, h, by simp [h, hconj]⟩
    · exact ⟨(starRingEnd ℂ).comp τ, τ, by simp [h, hconj], h⟩
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := key
  rcases h with h | h
  · exact ⟨τ₁, by rwa [Datum.mult, if_pos h₁]⟩
  · exact ⟨τ₂, by rwa [Datum.mult, if_neg (by rw [h₂]; exact hne)]⟩

theorem normSq_emb_bar {H : Host E} (α : 𝓞 E) (M : ℕ) (hα : α * H.bar α = (M : 𝓞 E)) (τ : E →+* ℂ) :
    ‖τ ((H.bar α : 𝓞 E) : E)‖ ^ 2 = M := by
  have h1 : τ ((H.bar α : 𝓞 E) : E) = starRingEnd ℂ (τ (α : E)) := by
    rw [H.bar_eq]; exact IsCMField.complexEmbedding_complexConj E τ _
  have h2 : τ (α : E) * τ ((H.bar α : 𝓞 E) : E) = M := by
    rw [← map_mul]
    have := congrArg (fun z : 𝓞 E => (z : E)) hα
    simp only [map_mul, map_natCast] at this
    erw [this]; simp
  rw [h1] at h2 ⊢
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  rw [RCLike.norm_conj]
  exact_mod_cast h2

theorem exists_kappa {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (σ : c.F →+* ℂ)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0)
    (hh : P.IsHomogeneous P.totalDegree) (s : (E →+* ℂ) → ℂ) (M : ℝ) (hs : ∀ τ, ‖s τ‖ ^ 2 = M) :
    ∃ κ : ℂ, ‖κ‖ ^ 2 = M ^ P.totalDegree ∧
      ∀ m ∈ (MvPolynomial.map σ P).support, (m.prod fun ℓ e => s ℓ.1 ^ e) = κ := by
  have key : ∀ m ∈ P.support, (m.prod fun ℓ e => s ℓ.1 ^ e) = ∏ τ, ∏ i : Fin (Dw.mult τ), s τ ^ a (τ, i) := by
    intro m hm
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum]
    exact congrArg _ (hP.1.2.2 m hm τ i)
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  refine ⟨_, ?_, fun m' hm' => key m' (MvPolynomial.support_map_subset _ _ hm')⟩
  rw [← key m hm]
  have hd : ∑ ℓ ∈ m.support, m ℓ = P.totalDegree := by
    have := hh (MvPolynomial.mem_support_iff.1 hm)
    rw [← this]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [← hd, Finsupp.prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm, pow_mul, hs]

theorem sum_le_finsum {A B : Type} [Finite B] (K : Finset A) (φ : B → A) (u : A → ℝ) (v : B → ℝ)
    (hK : ∀ a ∈ K, ∃ b, a = φ b) (huv : ∀ b, v b = u (φ b)) (hv : ∀ b, 0 ≤ v b) :
    ∑ a ∈ K, u a ≤ ∑ᶠ b, v b := by
  classical
  haveI := Fintype.ofFinite B
  rw [finsum_eq_sum_of_fintype]
  choose ψ hψ using fun a : K => hK a.1 a.2
  have hinj : Function.Injective ψ := fun a a' h => Subtype.ext (by rw [hψ a, hψ a', h])
  calc ∑ a ∈ K, u a = ∑ a : K, v (ψ a) := by
        rw [← Finset.sum_coe_sort K]
        exact Finset.sum_congr rfl fun a _ => by rw [huv, ← hψ]
    _ = ∑ b ∈ Finset.univ.image ψ, v b := (Finset.sum_image fun a _ a' _ h => hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hv b

theorem differentiable_translate (X : I2.PT E) (q n : ℕ) (π : I2.Vsp X.dim →ₗ[ℂ] I2.Vsp X.dim)
    (s : (Fin 1 → I2.Vsp X.dim) → ℂ) (hs : Differentiable ℂ s) (b : Fin n → I2.Vsp X.dim) :
    Differentiable ℂ (X.U q b (I2.s0 X π s)) := by
  have hπ : Differentiable ℂ π := (LinearMap.toContinuousLinearMap π).differentiable
  have h0 : Differentiable ℂ (I2.s0 (n := n) X π s) := by
    unfold I2.s0
    have hk : ∀ k : Fin n, Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => s fun _ => π (v k) := fun k =>
      hs.comp (differentiable_pi.2 fun _ => hπ.comp (differentiable_apply k))
    exact fun v => (HasFDerivAt.finset_prod fun k _ => (hk k v).hasFDerivAt).differentiableAt
  have h1 : Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => I2.HC v b := by
    unfold I2.HC I2.Hf
    fun_prop
  unfold I2.PT.U
  exact (((h1.const_mul _).sub_const _).cexp).mul (h0.comp (differentiable_id.sub_const b))

theorem theta_law {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)
    (Wu : UnitAt W) (hu : ∀ τ' i', ‖FD.dmin (U.X k).Gm x.1 τ' i'‖ = 1) :
    Differentiable ℂ Wu.θ ∧ ∀ a z, Wu.θ (z + W.Pm a) =
      (((Int.negOnePow ((W.F.Di (W.ik k)).EF a (H.w0 • a)) : ℤˣ) : ℤ) : ℂ) *
        Complex.exp (Real.pi * hermForm Wu.Hm z (W.Pm a) + Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) *
          Wu.θ z := by
  have hF : AHFrame W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr :=
    ⟨Wu.herm, Wu.pos, Wu.c1, Wu.c2, Wu.c3, Wu.c4, fun j hj => by
      rw [← W.pt]; exact Wu.c5 j hj, Wu.c6⟩
  have gen : ∀ (y : Sp ℂ ⟶ Xo.X) (_ : y = W.F.u (W.ik k) W.Pm) (s : LB.Sec (PPx y)),
      IsFnOf W.F (W.ik k) W.Pm Wu.fr y s Wu.θ → Differentiable ℂ Wu.θ ∧ ∀ a z, Wu.θ (z + W.Pm a) =
        Wu.χl (W.Pm a) * Complex.exp (Real.pi * hermForm Wu.Hm z (W.Pm a) +
          Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) * Wu.θ z := by
    rintro y rfl s hs
    exact isFnOf_entire_factor E H Dw l Xo _ _ _ W.F (W.ik k) W.Pm Wu.Hm Wu.χl Wu.fr W.per hF s Wu.θ hs
  obtain ⟨h1, h2⟩ := gen (U.un k x).x W.pt (U.un k x).s Wu.c7
  refine ⟨h1, fun a z => ?_⟩
  rw [h2, GlobalTheory.semichar_unit_frame Xo c σ r U hU k x W Wu hu a, Int.cast_negOnePow]

open Classical in

theorem value_torus {H : Host E} {Dw : Datum H} (T : I2.PT E) {g n : ℕ} (e : Fin g ≃ Lt1 Dw)
    (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hH : ∀ z w, I2.Hf (ψ z) (ψ w) = hermForm Hm z w) (hθ : Differentiable ℂ θ)
    (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ T.dim (rl τ)) (t : ℂ)
    (hrow : ∀ j, ∃ h : ((e j).2 : ℕ) < T.dim (rl (e j).1), ψ (Pi.single j 1) =
      t • EuclideanSpace.single (⟨rl (e j).1, ⟨(e j).2, h⟩⟩ : I2.Idx T.dim) (1 : ℂ))
    (α : 𝓞 E) (M : ℕ) (hα : α * H.bar α = (M : 𝓞 E)) (Q : MvPolynomial (LtN Dw n) ℂ) (κ : ℂ)
    (hκ : ∀ m ∈ Q.support, (m.prod fun ℓ k => rl ℓ.1 ((H.bar α : 𝓞 E) : E) ^ k) = κ)
    (a : Fin n → Fin g → ℂ) :
    I2.polyDeriv Q (letDir e) (fun z => ∏ b, fock Hm ((M : ℤ) ^ 2) (a b) (fun w => θ ((M : ℂ) • w)) (z b)) 0 =
      κ * I2.polyDeriv Q (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n T.dim))
        (T.U M (fun b => I2.act (H.bar α) (-ψ (a b))) (I2.s0 T (vspActL α) fun v => θ (ψ.symm (v 0)))) 0 := by
  have hdir : (fun (ℓ : LtN Dw n) b => ψ (letDir e ℓ b)) = fun ℓ => t •
      I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n T.dim) := by
    have h1 : ∀ y : Lt1 Dw, ψ (Pi.single (e.symm y) 1) = t •
        EuclideanSpace.single (⟨rl y.1, Fin.castLE (hd y.1) y.2⟩ : I2.Idx T.dim) (1 : ℂ) := by
      intro y
      obtain ⟨j, rfl⟩ := e.surjective y
      obtain ⟨h, hh⟩ := hrow j
      rw [e.symm_apply_apply]
      exact hh
    funext ℓ b
    by_cases hb : b = ℓ.2.2
    · subst hb
      simp only [letDir, I2.dir, Pi.smul_apply, Pi.single_eq_same]
      exact h1 ⟨ℓ.1, ℓ.2.1⟩
    · simp [letDir, I2.dir, hb]
  have hs : Differentiable ℂ fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0)) :=
    hθ.comp ((LinearMap.toContinuousLinearMap ψ.symm.toLinearMap).differentiable.comp (differentiable_apply 0))
  rw [polyDeriv_prod_fock_eq_translate E T g ψ Hm θ hH hθ, hdir]
  refine GlobalTheory.AlphaChain.polyDeriv_levelSq_eq_alpha E T α (H.bar α) M n (H.bar_eq α) hα _ hs _ _ _ _
      (fun ℓ => rl ℓ.1 ((H.bar α : 𝓞 E) : E)) κ ?_ hκ
  intro ℓ b
  ext i
  by_cases hb : b = ℓ.2.2
  · subst hb
    by_cases hi : i = ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩
    · subst hi
      simp [I2.act, I2.dir]
    · simp [I2.act, I2.dir, hi]
  · simp [I2.act, I2.dir, hb]

theorem norm_sq_value (v κ D : ℂ) (M d : ℕ) (t : ℝ) (hM : (0 : ℝ) < M) (ht : 0 ≤ t) (hκ : ‖κ‖ ^ 2 = (M : ℝ) ^ d)
    (hv : v = ((M : ℂ)⁻¹) ^ d * (κ * (((Real.sqrt t : ℝ) : ℂ) ^ d * D))) : ‖v‖ ^ 2 = (t / M) ^ d * ‖D‖ ^ 2 := by
  rw [hv, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, hκ, norm_pow, norm_pow, norm_inv,
    Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← pow_mul, ← pow_mul,
    mul_comm d 2, pow_mul, pow_mul, Real.sq_sqrt ht, ← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow]
  congr 2
  field_simp

theorem thetaRule_sum_lower : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → GoodEmb c σ → IsUnf U → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) → (U.X k).IsOrtho x.1 → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (T : I2.PT E) (Pr : I2.Par T P₁.totalDegree), T.r = r ∧ Pr.q = l.M ∧ Pr.m = m ∧ Pr.ph = I2.phiFD (U.X k) (I2.th (E := E) l.M R0) x.1 ∧ ∀ f : (Fin n → LevQ Dw l) → Rul Xo c, (∀ q, IsThRule Xo c nab (fun b => levRep (q b)) P₁ (f q)) → (2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ᶠ q, ‖toC (evR Xo c (f q) (U.un k x))‖ ^ 2 := by
  intro hCI E _ _ _ H Dw l Xo c _ σ r U k x xR nab hnab hσ hU hft hx hxR α hα hMb a n P₁ hP hB R0 m hrun hm
  classical
  obtain ⟨W⟩ := nonempty_unfAt hU k x
  have hu := norm_dmin (U.X k) hx
  obtain ⟨Wu⟩ := nonempty_unitAt W hu
  have hM0 : (0 : ℝ) < l.M := by have := l.three_le; exact_mod_cast (by omega : 0 < l.M)
  have hxR0 : 0 < xR := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hxR τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 (U.X k).ξ0_ne)
  have hHm : Wu.Hm = Matrix.diagonal fun _ => ((2 * xR : ℝ) : ℂ) := by
    rw [GlobalTheory.HermDiag.hm_eq_diagonal E H Dw l Xo c σ r U k x W Wu hσ hU hx]
    simp only [hxR]
  obtain ⟨hbij, hmul, hty⟩ := relab_isTypeFn E H Dw l Xo c σ hσ
  change Function.Bijective (relab c σ) at hbij
  change ∀ τ, Dw.mult (relab c σ τ) = Dw.mult τ at hmul
  have hty' : IsTypeFn H (W.F.Di (W.ik k)).p (W.F.Di (W.ik k)).q (fun j => relab c σ (W.e j).1) := by
    rw [(W.F.sig _).1, (W.F.sig _).2]; exact hty W.g W.e
  have hDm : ∀ τ, (W.F.Di (W.ik k)).mult τ = Dw.mult τ := fun τ => by
    simp only [Datum.mult, (W.F.sig _).1, (W.F.sig _).2]
  obtain ⟨T, ψ, hT, hrow⟩ := GlobalTheory.ScalarTorus.exists_torusOf_rows E H (W.F.Di (W.ik k)) W.g
    (fun j => relab c σ (W.e j).1) W.Pm (2 * xR) (fun j => (W.e j).2.1) (by positivity) hty' W.per
    (fun a b => by rw [← hHm]; exact Wu.c1 a b)
    (fun j => by rw [hDm, hmul]; exact (W.e j).2.2)
    (fun j j' h h' => by
      apply W.e.injective
      have h1 := hbij.1 h
      generalize W.e j = y at h1 h'
      generalize W.e j' = y' at h1 h'
      obtain ⟨τ, i⟩ := y
      obtain ⟨τ', i'⟩ := y'
      dsimp only at h1 h'
      subst h1
      rw [Fin.ext h'])
  rw [← hHm] at hT
  obtain ⟨-, hTr, hTph⟩ := GlobalTheory.OrthoPeriodTorus.isTorusAt_of_isTorusOf E H Dw l Xo c σ r U k x W Wu T ψ hσ hU hx hT
  have hdim : ∀ τ, T.dim τ = Dw.mult τ := fun τ => (hT.2.1 τ).trans (hDm τ)
  have hd : ∀ τ, Dw.mult τ ≤ T.dim (relab c σ τ) := fun τ => by rw [hdim, hmul]
  obtain ⟨hP0, hhom, nb, bs, hdisj, hDF, hren⟩ := GlobalTheory.BlockRen.blockProd_rename E H Dw n c.F σ P₁ hB T.dim
    (relab c σ) hd hbij.1
  obtain ⟨hθ, hlaw⟩ := theta_law hU W Wu hu
  obtain ⟨hsec, hl2, -⟩ := ThetaTorus.theta_section_l2_torus E H _ _ _ W.Pm Wu.Hm T ψ Wu.θ Wu.Fd hT hθ hlaw Wu.c8
  rw [Wu.c9] at hl2
  set s : (Fin 1 → I2.Vsp T.dim) → ℂ := fun v => Wu.θ (ψ.symm (v 0)) with hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hl2
    simp [I2.PT.l2, I2.PT.ptN2] at hl2
  have hπ := IsPiAct.isPi_actL_of_isTorusOf E H _ _ _ W.Pm Wu.Hm T ψ W.per hT α l.M hα
  choose x2 hx2a hx2b using fun q : LevQ Dw l => Pf.rep_level Dw l (levRep q)
  obtain ⟨hmi, hms⟩ := marking_iso_mod E H Dw l Xo c _ _ _ W.F (W.ik k)
  let mk : Dw.La →+ I2.Vsp T.dim :=
    (ψ.toLinearMap.toAddMonoidHom.comp W.Pm).comp (W.F.t (W.ik k)).toAddMonoidHom
  have hmk : ∀ a, mk a = ψ (W.Pm (W.F.t (W.ik k) a)) := fun _ => rfl
  have hnat : ∀ b, ψ (W.Pm (l.M • b)) = (l.M : ℂ) • ψ (W.Pm b) := fun b => by
    rw [map_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨K, hK, hKq⟩ := GlobalTheory.isReps_level_translates E H Dw l T mk α hα hMb
    (fun a => (hT.2.2.2.1 _).2 ⟨_, rfl⟩)
    (fun β a => by
      rw [hmk, hmk, map_smul, ← hT.2.2.2.2.1]
      exact congrArg ψ (funext fun j => W.per.1 β _ j))
    (fun a ⟨v, hv, h⟩ => by
      obtain ⟨b, rfl⟩ := (hT.2.2.2.1 v).1 hv
      rw [hmk, ← hnat] at h
      exact hmi a ⟨b, W.per.2.1 (ψ.injective h)⟩)
    (fun v hv => by
      obtain ⟨b, rfl⟩ := (hT.2.2.2.1 v).1 hv
      obtain ⟨a, e, rfl⟩ := hms b
      exact ⟨a, ψ (W.Pm e), (hT.2.2.2.1 _).2 ⟨_, rfl⟩, by rw [map_add, map_add, hnat, hmk]⟩)
    x2 hx2a hx2b n
  obtain ⟨κ, hκ, hκm⟩ := exists_kappa c σ hP hP0 hhom (fun τ => relab c σ τ ((H.bar α : 𝓞 E) : E)) l.M
    (fun τ => normSq_emb_bar α l.M hα _)
  obtain ⟨τ0, hτ0⟩ := exists_mult_le Dw m hm
  obtain ⟨Pr, hq, hR, hm'⟩ := hrun T hTr ⟨τ0, by rwa [hdim]⟩
  refine ⟨T, Pr, hTr, hq, hm', by rw [I2.Par.ph, hq, hR, hTph], fun f hf => ?_⟩
  have hI : Pr.Jbound n ≤ ∑ b ∈ K, ‖I2.polyDeriv (I2.P1 bs) I2.dir (T.U l.M b (I2.s0 T (vspActL α) s)) 0‖ ^ 2 := by
    have gen : ∀ (d : ℕ) (_ : I2.DF bs = d) (Pr : I2.Par T d), Pr.q = l.M →
        Pr.Jbound n ≤ ∑ b ∈ K, ‖I2.polyDeriv (I2.P1 bs) I2.dir (T.U l.M b (I2.s0 T (vspActL α) s)) 0‖ ^ 2 := by
      rintro d rfl Pr hq
      have := GlobalTheory.ThetaTorus.I_holds E T n nb bs hdisj Pr (vspActL α) (hq ▸ hπ) s hsec hs0 K (hq ▸ hK)
      rwa [hl2, one_pow, _root_.mul_one, hq] at this
    exact gen _ hDF Pr hq
  haveI := finite_levQ Dw l
  refine le_trans (mul_le_mul_of_nonneg_left hI (pow_nonneg (div_nonneg (by positivity) hM0.le) _)) ?_
  rw [Finset.mul_sum]
  refine sum_le_finsum K (fun q i => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 (q i)))))
    (fun b => (2 * xR / l.M) ^ P₁.totalDegree *
      ‖I2.polyDeriv (I2.P1 bs) I2.dir (T.U l.M b (I2.s0 T (vspActL α) s)) 0‖ ^ 2)
    (fun q => ‖toC (evR Xo c (f q) (U.un k x))‖ ^ 2) hKq
    (fun q => ?_) fun _ => sq_nonneg _
  have hv := (GlobalTheory.AnVal.thetaRule_value_periods hCI E H Dw l Xo c σ r U k x W Wu nab hnab hft n (fun b => levRep (q b))
    (fun b => x2 (q b)) (fun b => hx2a _) (fun b => hx2b _) a P₁ hP (f q) (hf q)).2
  have hw := value_torus T W.e ψ Wu.Hm Wu.θ hT.2.2.1 hθ (relab c σ) hd _ hrow α l.M hα _ κ hκm
    (fun b => ((l.M : ℂ) ^ 2)⁻¹ • W.Pm (W.F.t (W.ik k) (x2 (q b))))
  rw [hren _ _ (differentiable_translate T _ _ _ _ hsec.1 _)] at hw
  simp only [map_smul] at hw
  exact norm_sq_value _ κ _ l.M _ (2 * xR) hM0 (by positivity) hκ (hv.trans (congrArg _ hw))

end GlobalTheory.ThetaLower
