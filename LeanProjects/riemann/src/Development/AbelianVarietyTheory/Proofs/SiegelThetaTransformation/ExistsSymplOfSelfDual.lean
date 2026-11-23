import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodCoordinateThetaOfSignedHeisenbergVacuumStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetHermitianFormAtFramePeriodCoordsOfUnitFrameStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VacNorm

theorem exists_sympl_of_selfDual {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] {g : ℕ}
    (B : LinearMap.BilinForm ℚ V) (hB : ∀ u, B u u = 0) (hnd : B.Nondegenerate)
    (hV : Module.finrank ℚ V = 2 * g) (N : Submodule ℤ V) (hfg : N.FG)
    (hfull : ∀ v, ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ N)
    (hN : ∀ x, x ∈ N ↔ ∀ y ∈ N, ∃ k : ℤ, B x y = k) :
    ∃ b : Fin g ⊕ Fin g → V, (∀ u, u ∈ N ↔ ∃ m : Fin g ⊕ Fin g → ℤ, u = ∑ j, m j • b j) ∧
      ∀ i j, B (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ) := by
  haveI : Module.Finite ℤ N := Module.Finite.iff_fg.2 hfg
  haveI : IsAddTorsionFree V := IsAddTorsionFree.of_module_rat V
  haveI : Module.Free ℤ N := inferInstance
  choose f hf using fun (x y : N) => (hN x).1 x.2 y y.2
  let ω : LinearMap.BilinForm ℤ N := LinearMap.mk₂ ℤ (fun x y => -f x y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℚ); push_cast; simp only [← hf]; simp; ring)
    (fun k x y => by
      apply Int.cast_injective (α := ℚ); simp only [smul_eq_mul]; push_cast; simp only [← hf]; simp)
    (fun x y y' => by
      apply Int.cast_injective (α := ℚ); push_cast; simp only [← hf]; simp; ring)
    (fun k x y => by
      apply Int.cast_injective (α := ℚ); simp only [smul_eq_mul]; push_cast; simp only [← hf]; simp)
  have hω : ∀ x y : N, B x y = -(ω x y : ℤ) := fun x y => by simp [ω, hf]
  have halt : ω.IsAlt := fun x => by
    have := hω x x
    rw [hB] at this
    exact_mod_cast (neg_eq_zero.1 this.symm)
  let e := Module.finBasis ℤ N
  have hli : LinearIndependent ℚ (fun i => (e i : V)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1 (e.linearIndependent.map' N.subtype N.ker_subtype)
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range fun i => (e i : V)) := by
    intro v _
    obtain ⟨k, hk, hv⟩ := hfull v
    have h1 : k • v ∈ Submodule.span ℚ (Set.range fun i => (e i : V)) := by
      have := congrArg (Subtype.val) (e.sum_repr ⟨_, hv⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at this
      rw [← this]
      exact Submodule.sum_mem _ fun i _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
    have := Submodule.smul_mem _ (k : ℚ)⁻¹ h1
    rwa [← Int.cast_smul_eq_zsmul ℚ, inv_smul_smul₀ (Int.cast_ne_zero.2 hk)] at this
  let eQ := Module.Basis.mk hli hsp
  have hrk : Module.finrank ℤ N = 2 * g := by
    rw [← hV, Module.finrank_eq_card_basis eQ, Fintype.card_fin]
  have hbij : Function.Bijective ω := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      apply Subtype.ext
      refine hnd.1 _ fun y => ?_
      obtain ⟨k, hk, hy⟩ := hfull y
      have := hω x ⟨_, hy⟩
      rw [hx] at this
      simpa [hk] using this
    · intro φ
      let ψ : V →ₗ[ℚ] ℚ := eQ.constr ℚ fun i => -(φ (e i) : ℚ)
      have hψ : ∀ y : N, ψ y = -(φ y : ℚ) := by
        intro y
        conv_lhs => rw [← e.sum_repr y]
        conv_rhs => rw [← e.sum_repr y]
        have : ∀ i, ψ (e i) = -(φ (e i) : ℚ) := fun i => by
          have := eQ.constr_basis ℚ (fun i => -(φ (e i) : ℚ)) i
          rwa [Module.Basis.mk_apply] at this
        simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, map_sum, map_zsmul, this]
        simp
      let z := (B.toDual hnd).symm ψ
      have hz : ∀ y, B z y = ψ y := fun y => LinearMap.BilinForm.apply_toDual_symm_apply ψ y
      have hzN : z ∈ N := (hN z).2 fun y hy => ⟨-φ ⟨y, hy⟩, by rw [hz, hψ ⟨y, hy⟩]; simp⟩
      refine ⟨⟨z, hzN⟩, LinearMap.ext fun y => ?_⟩
      have := hω ⟨z, hzN⟩ y
      rw [hz, hψ] at this
      exact_mod_cast (neg_inj.1 this).symm
  obtain ⟨c, hc⟩ := exists_isSymplecticBasis_of_finrank halt hbij hrk
  refine ⟨fun j => c j, fun u => ⟨fun hu => ⟨c.repr ⟨u, hu⟩, ?_⟩, ?_⟩, fun i j => ?_⟩
  · have := congrArg (Subtype.val) (c.sum_repr ⟨_, hu⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at this
    exact this.symm
  · rintro ⟨m, rfl⟩
    exact Submodule.sum_mem _ fun j _ => N.smul_mem _ (c j).2
  · rw [hω, hc.apply_eq_sum halt, omegaStd]
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem exists_sympl_of_selfD (hs : IsSympl X bas) {L : Lt E r} (hL : SelfD X L) :
    ∃ b : Fin g ⊕ Fin g → (Fin r → E), (∀ u, u ∈ L ↔ ∃ m : Fin g ⊕ Fin g → ℤ, u = ∑ j, m j • b j) ∧
      ∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ) := by
  have hz : ∀ u, (∀ v, EF X u v = 0) → u = 0 := by
    intro u h
    have h' (t) := (EF_vecQ hs (crd X bas u) t).symm.trans ((congrArg (EF X · _) (vecQ_crd X bas u)).trans (h _))
    rw [← vecQ_crd X bas u, ← vecQ_zero X bas]
    congr 1
    funext j
    rcases j with j | j
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)
  let f : (Fin g ⊕ Fin g → ℚ) →ₗ[ℚ] (Fin r → E) :=
    { toFun := vecQ X bas, map_add' := vecQ_add X bas, map_smul' := vecQ_smul X bas }
  have hV : Module.finrank ℚ (Fin r → E) = 2 * g := by
    rw [← (LinearEquiv.ofBijective f ⟨vecQ_injective hs, vecQ_surjective X bas⟩).finrank_eq]
    simp [two_mul]
  refine exists_sympl_of_selfDual (EFBil X) (fun u => ?_) ⟨hz, fun u h => hz u fun v => ?_⟩ hV
    (L.restrictScalars ℤ) hL.1.restrictScalars
    (fun v => GlobalTheory.LatFin.exists_int_smul_mem L (TensLat.span_of_selfD X hL) v) hL.2
  · have := TensLat.EF_swap X u u
    change EF X u u = 0
    linarith
  · rw [TensLat.EF_swap, neg_eq_zero]; exact h v

theorem re_dot (Y : Matrix (Fin g) (Fin g) ℝ) (u v : Fin g → ℂ) :
    (u ⬝ᵥ (Y.map fun t : ℝ => (t : ℂ)) *ᵥ v).re =
      (fun i => (u i).re) ⬝ᵥ Y *ᵥ (fun i => (v i).re) - (fun i => (u i).im) ⬝ᵥ Y *ᵥ (fun i => (v i).im) := by
  simp only [dotProduct, mulVec, map_apply, Finset.mul_sum, re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp

theorem re_dot_star (Y : Matrix (Fin g) (Fin g) ℝ) (u v : Fin g → ℂ) :
    (u ⬝ᵥ (Y.map fun t : ℝ => (t : ℂ)) *ᵥ star v).re =
      (fun i => (u i).re) ⬝ᵥ Y *ᵥ (fun i => (v i).re) + (fun i => (u i).im) ⬝ᵥ Y *ᵥ (fun i => (v i).im) := by
  simp only [dotProduct, mulVec, map_apply, Finset.mul_sum, re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp

theorem re_dot_star_comm {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.IsSymm) (u v : Fin g → ℂ) :
    (u ⬝ᵥ (Y.map fun t : ℝ => (t : ℂ)) *ᵥ star v).re = (v ⬝ᵥ (Y.map fun t : ℝ => (t : ℂ)) *ᵥ star u).re := by
  have h (a b : Fin g → ℝ) : a ⬝ᵥ Y *ᵥ b = b ⬝ᵥ Y *ᵥ a := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hY.eq, dotProduct_comm]
  rw [re_dot_star, re_dot_star, h, h (fun i => (u i).im)]

theorem norm_sq_of_mean {τ h : Matrix (Fin g) (Fin g) ℂ} {c₁ c₂ : Fin g → ℂ} {A : AddSubgroup (Fin g → ℂ)}
    (hτ : τ ∈ SW.Siegel (Fin g)) (hh : IsUnit h.det) (h₁ : ∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2)
    (h₂ : ∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2)
    (hA : ∀ lam, lam ∈ A ↔ ∃ m n : Fin g → ℤ, h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))
    {H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ}
    (hH : ∀ z w, H z w = (h *ᵥ z) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ star (h *ᵥ w))
    {θ : (Fin g → ℂ) → ℂ} {a : ℂ}
    (ha : ∀ z, θ z = a * (cexp (Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ
      (h *ᵥ z))) * thetaChar τ c₁ c₂ (h *ᵥ z)))
    (hper : ∀ p ∈ A, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z,
      ε * (cexp (-(((1 : ℕ) : ℂ) * Real.pi * H (z + (1 / 2 : ℂ) • p) p)) * θ (z + p)) = θ z)
    {Fd : Set (Fin g → ℂ)} (hFd : MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume)
    (hm : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (H z z).re)) / (MeasureTheory.volume Fd).toReal = 1) :
    ‖a‖ ^ 2 = Real.sqrt (2 ^ g * (τ.map Complex.im).det) := by
  obtain ⟨Fd', hFd', hm'⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar
    g τ h c₁ c₂ A hτ.1 hτ.2 hh h₁ h₂ hA
  haveI : Countable A := by
    have : (A : Set (Fin g → ℂ)) ⊆ Set.range fun p : (Fin g → ℤ) × (Fin g → ℤ) =>
        h⁻¹ *ᵥ ((fun i => (p.1 i : ℂ)) + τ *ᵥ (fun i => (p.2 i : ℂ))) := by
      intro lam hl
      obtain ⟨m, n, e⟩ := (hA lam).1 hl
      exact ⟨(m, n), by simp only [← e, mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have hY : ((τ.map Complex.im)⁻¹).IsSymm := by
    have := hτ.2.inv.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hinv : ∀ (p : A) z, ‖θ (p +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (H (p +ᵥ z) (p +ᵥ z)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (H z z).re) := by
    intro p z
    obtain ⟨ε, hε, hp⟩ := hper p p.2
    change ‖θ (p + z)‖ ^ 2 * Real.exp (-Real.pi * (H (p + z) (p + z)).re) = _
    rw [← hp z, add_comm (p : Fin g → ℂ) z, norm_mul, norm_mul, hε, _root_.one_mul, mul_pow, Complex.norm_exp,
      ← Real.exp_nat_mul, mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
    congr 2
    have e1 : (H (z + p) (z + p)).re = (H z z).re + 2 * (H z p).re + (H p p).re := by
      have := re_dot_star_comm hY (h *ᵥ z) (h *ᵥ p)
      simp only [hH, mulVec_add, star_add, add_dotProduct, dotProduct_add, add_re]
      linarith
    have e2 : H (z + (1 / 2 : ℂ) • (p : Fin g → ℂ)) p = H z p + (1 / 2 : ℝ) * H p p := by
      simp only [hH, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
      push_cast; ring
    rw [e1, e2]
    simp only [Nat.cast_one, _root_.one_mul, neg_re, re_ofReal_mul, add_re]
    push_cast; ring
  rw [hFd.setIntegral_eq hFd' hinv, hFd.measure_eq hFd'] at hm
  have hint : ∀ z, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (H z z).re) = ‖a‖ ^ 2 *
      (‖thetaChar τ c₁ c₂ (h *ᵥ z)‖ ^ 2 * Real.exp (-2 * Real.pi * ((fun i => ((h *ᵥ z) i).im) ⬝ᵥ
        (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((h *ᵥ z) i).im)))) := by
    intro z
    rw [ha, norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, _root_.mul_assoc,
      mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
    congr 3
    have : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hH, this, re_ofReal_mul, re_dot, re_dot_star]
    push_cast; ring
  simp only [hint] at hm
  rw [MeasureTheory.integral_const_mul, mul_div_assoc, hm'] at hm
  have hpos : 0 < Real.sqrt (2 ^ g * (τ.map Complex.im).det) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) hτ.2.det_pos)
  rwa [mul_inv_eq_one₀ hpos.ne'] at hm

theorem exists_factor {α : Type} {n : ℕ} {θ θ₀ : α → ℂ} {K : ℂ} (hn : n ≠ 0) {z₀ : α} (h0 : θ z₀ ≠ 0)
    (h : ∀ z : Fin n → α, ∏ b, θ (z b) = K * ∏ b, θ₀ (z b)) :
    ∃ a : ℂ, (∀ z, θ z = a * θ₀ z) ∧ a ^ n = K := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h1 := h fun _ => z₀
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : θ₀ z₀ ^ (m + 1) ≠ 0 := fun e => pow_ne_zero _ h0 (by rw [h1, e, mul_zero])
  have ha : ∀ z, θ z = K * θ₀ z₀ ^ m / θ z₀ ^ m * θ₀ z := by
    intro z
    have := h (Fin.cons z fun _ => z₀)
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this
    field_simp
    linear_combination this
  refine ⟨_, ha, mul_right_cancel₀ h2 ?_⟩
  rw [← mul_pow, ← ha, h1]

theorem norm_factor_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ X.dom, IsUnitFr X x → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx w x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ‖κ‖ = ρ := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL v hv
  obtain ⟨b, hb, hb'⟩ := exists_sympl_of_selfD hs hL
  obtain ⟨c₁, c₂, C, hC, h₁, h₂, hx'⟩ := GlobalTheory.T.periodCoordinateTheta_of_signedHeisenbergVacuum E r X g bas idx n hs hn w hw hw' L hL v hv b hb hb'
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero_iff τ.1 τ.1.injective).2 X.ξ0_ne
    unfold Data.c
    positivity
  have hD : 0 < ∏ τ : X.Ψ, X.c τ ^ r := Finset.prod_pos fun τ _ => pow_pos (hc τ) _
  have hC' : 0 < ‖C‖ := norm_pos_iff.2 hC
  refine ⟨Real.sqrt (2 ^ g / ∏ τ : X.Ψ, X.c τ ^ r) ^ (n / 2) / ‖C‖, by positivity, ?_⟩
  intro x hx hu θ κ hθ ⟨A, Fd, hA, hFd, hm⟩ hκ
  obtain ⟨hh, hτ, hH, -, hth⟩ := hx' x hx _ _ rfl rfl
  clear hx'
  set P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i with hP
  set Q : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i with hQ
  have hPu : IsUnit P.det := by
    by_contra hne
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp at hne
    · haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
      rw [nonsing_inv_apply_not_isUnit _ hne, det_zero] at hh
      exact not_isUnit_zero hh
  generalize hh' : P⁻¹ = h at *
  generalize hτ' : h * Q = τ at *
  have hhP : h * P = 1 := by rw [← hh', nonsing_inv_mul _ hPu]
  have hK : ∀ z : Fin n → Fin g → ℂ, ∏ k, θ (z k) = (κ * C * h.det ^ (n / 2)) *
      ∏ k, (fun z => cexp (Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ
        (h *ᵥ z))) * thetaChar τ c₁ c₂ (h *ᵥ z)) (z k) := fun z => by
    rw [hκ, hth]; ring
  rw [eq_div_iff hC'.ne']
  rcases eq_or_ne n 0 with rfl | hn0
  · have := congrArg norm (hK fun i => i.elim0)
    simpa using this.symm
  have hθ0 : ∃ z₀, θ z₀ ≠ 0 := by
    by_contra! h0
    simp [h0] at hm
  obtain ⟨z₀, hz₀⟩ := hθ0
  obtain ⟨a, ha, haK⟩ := exists_factor (θ₀ := fun z => cexp (Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ
    ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ (h *ᵥ z))) * thetaChar τ c₁ c₂ (h *ᵥ z)) hn0 hz₀ hK
  have hpv : ∀ m : Fin g ⊕ Fin g → ℤ, h *ᵥ pv X idx x (∑ j, m j • b j) =
      (fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (m (Sum.inr i) : ℂ)) := by
    intro m
    have : pv X idx x (∑ j, m j • b j) =
        P *ᵥ (fun i => (m (Sum.inl i) : ℂ)) + Q *ᵥ (fun i => (m (Sum.inr i) : ℂ)) := by
      funext i
      rw [pv, per_sum]
      simp only [per_zsmul, Fintype.sum_sum_type, hP, hQ, pv]
      simp [mulVec, dotProduct, mul_comm]
    rw [this, mulVec_add, mulVec_mulVec, mulVec_mulVec, hhP, hτ', one_mulVec]
  have hA' : ∀ lam, lam ∈ A ↔ ∃ m n : Fin g → ℤ,
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    rw [hA]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m, rfl⟩ := (hb u).1 hu
      exact ⟨_, _, hpv m⟩
    · rintro ⟨m, m', e⟩
      refine ⟨_, (hb _).2 ⟨Sum.elim m m', rfl⟩, ?_⟩
      have e' : h *ᵥ lam = h *ᵥ pv X idx x (∑ j, Sum.elim m m' j • b j) := e.trans (hpv (Sum.elim m m')).symm
      have := congrArg (h⁻¹ *ᵥ ·) e'
      simpa only [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec] using this
  have hsq := norm_sq_of_mean hτ hh h₁ h₂ hA' hH ha (fun p hp => by
    obtain ⟨u, hu, rfl⟩ := (hA p).1 hp
    refine ⟨eps1 X w u, ?_, fun z => congrFun (hθ.2 u hu) z⟩
    rw [eps1, Complex.norm_exp]
    simp) hFd hm
  have hY := hτ.2.det_pos
  have hdet := GlobalTheory.T.det_hermitianFormAtFramePeriodCoords_of_unitFrame E r X g bas idx n hs hn x hx hu
    (hᵀ * ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) * h.map (starRingEnd ℂ)) (fun z w' => by
      have : star (h *ᵥ w') = h.map (starRingEnd ℂ) *ᵥ star w' := by
        funext i; simp [mulVec, dotProduct]
      rw [hH, hermForm, this, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec z, vecMul_transpose])
  have e1 : (h.map (starRingEnd ℂ)).det = conj h.det := ((starRingEnd ℂ).map_det h).symm
  have e2 : ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)).det = (((τ.map Complex.im).det⁻¹ : ℝ) : ℂ) := by
    rw [← Ring.inverse_eq_inv, ← det_nonsing_inv]
    exact (Complex.ofRealHom.map_det _).symm
  rw [det_mul, det_mul, det_transpose, e1, e2, mul_right_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hdet
  have hdet' : ‖h.det‖ ^ 2 * (τ.map Complex.im).det⁻¹ = ∏ τ : X.Ψ, X.c τ ^ r := by exact_mod_cast hdet
  have hh0 : 0 < ‖h.det‖ := norm_pos_iff.2 hh.ne_zero
  have e3 : ‖a‖ ^ 2 = Real.sqrt (2 ^ g / ∏ τ : X.Ψ, X.c τ ^ r) * ‖h.det‖ := by
    rw [hsq, ← Real.sqrt_sq hh0.le, ← Real.sqrt_mul (by positivity), ← hdet']
    congr 1
    field_simp
  have e4 := congrArg norm haK
  obtain ⟨k, rfl⟩ := hn.two_dvd
  rw [Nat.mul_div_cancel_left _ two_pos] at e4 ⊢
  rw [norm_pow, pow_mul, e3, mul_pow, norm_mul, norm_mul, norm_pow] at e4
  exact (mul_right_cancel₀ (pow_ne_zero _ hh0.ne') e4).symm

end GlobalTheory.Dict.VacNorm
