import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.HermLinApply
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorantStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLineBasis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.LatticeCovolumeL2

theorem hermForm_sum_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (c : Fin g → ℂ)
    (p : Fin g → Fin g → ℂ) :
    hermForm Hm z (∑ j, c j • p j) = ∑ j, hermForm Hm z (p j) * (starRingEnd ℂ) (c j) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, RCLike.star_def, mul_comm]

theorem riem_inv {g : ℕ} (Hm τ : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g → Fin g → ℂ)
    (hq : ∀ l, q l = ∑ j, τ j l • p j) (h1 : ∀ k l, (hermForm Hm (p k) (p l)).im = 0)
    (h2 : ∀ k l, (hermForm Hm (p k) (q l)).im = -(if k = l then 1 else 0)) :
    (Matrix.of fun k l => (hermForm Hm (p k) (p l)).re) * τ.map Complex.im = 1 := by
  ext k l
  have := h2 k l
  rw [hq, hermForm_sum_smul, Complex.im_sum] at this
  simp only [Complex.mul_im, h1, Complex.conj_im, zero_mul, add_zero, mul_neg, Finset.sum_neg_distrib,
    neg_inj] at this
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

theorem polar {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    2 * (hermForm Hm z w).re =
      (hermForm Hm (z + w) (z + w)).re - (hermForm Hm z z).re - (hermForm Hm w w).re := by
  have hs : hermForm Hm w z = (starRingEnd ℂ) (hermForm Hm z w) := by
    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hH.apply j i, RCLike.star_def]
    ring
  have : hermForm Hm (z + w) (z + w) = hermForm Hm z z + hermForm Hm z w + hermForm Hm w z + hermForm Hm w w := by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    ring
  rw [this, hs]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem cols {g : ℕ} (h τ : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g → Fin g → ℂ)
    (hp : ∀ k, h.mulVec (p k) = Pi.single k 1) (hq : ∀ k, h.mulVec (q k) = τ.mulVec (Pi.single k 1)) (l : Fin g) :
    q l = ∑ j, τ j l • p j := by
  have hs : Function.Surjective (Matrix.toLin' h) := fun v =>
    ⟨∑ j, v j • p j, by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hp]
      ext i
      simp [Pi.single_apply]⟩
  apply LinearMap.injective_iff_surjective.2 hs
  simp only [Matrix.toLin'_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hp, hq]
  ext i
  simp [Pi.single_apply]

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} [Algebra (FractionRing ℂ) ℂ]
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {a : ArcIn Dw l β ℂ (σ.comp β)}
  {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} {Ha : HolArc Y σ a χ W Fu}
  {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th)

theorem card_le (h1 : Module.finrank (𝓞 E) a.D₀.X = 1) :
    Fintype.card {k // k ∈ Θ.S} ≤ Module.finrank ℚ E := by
  refine le_trans ?_ (finrank_int_le h1)
  refine LinearIndependent.fintype_card_le_finrank
    (b := fun k : {k // k ∈ Θ.S} => Ha.y (Θ.bas (Pi.single (.inr k.1) 1))) ?_
  rw [Fintype.linearIndependent_iff]
  intro u hu k
  have : Ha.y (Θ.bas (∑ k : {k // k ∈ Θ.S}, u k • Pi.single (.inr k.1) 1)) = 0 := by
    simpa only [map_sum, map_zsmul] using hu
  have := (Θ.ker _).1 this k.1 k.2
  simpa [Pi.single_apply, Subtype.coe_inj] using this

theorem mem_span (v : (Fu.Di Ha.i).La) (hv : ∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF v v' = 0) :
    v ∈ Submodule.span ℤ (Set.range fun k : {k // k ∈ Θ.S} => Θ.bas (Pi.single (.inl k.1) 1)) := by
  obtain ⟨u, rfl⟩ := Θ.bas.surjective v
  obtain ⟨h1, h2⟩ := (Θ.orth u).1 hv
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun k => u (.inl k.1), ?_⟩
  simp only [← map_zsmul, ← map_sum]
  congr 1
  ext (i | i)
  · by_cases hi : i ∈ Θ.S
    · rw [Finset.sum_apply, Finset.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro b _ hb
        have : i ≠ b.1 := fun e => hb (Subtype.ext e.symm)
        simp [this]
      · simp
    · rw [h2 i hi, Finset.sum_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      have : i ≠ b.1 := fun e => hi (e ▸ b.2)
      simp [this]
  · simp [h1]

end

theorem key (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (k : U.Comp) (ξ' : Fin r → E)
    (hG : GoodEmb c σ) (hU : IsUnf U) (hξ : ξ' ≠ 0) (h1 : Module.finrank (𝓞 E) a.D₀.X = 1)
    (w : ℂ) (x : (U.X k).dom) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ))
    (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La)
    (hL : ∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w v))
    (hγ : ∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v')
    (t : (Uw.F.Di Ha.i).La) (ht : ∀ v', Ha.y v' = 0 → (Uw.F.Di Ha.i).EF t v' = 0)
    (htξ : (Uw.φ k (γ t) : Fin r → E) = ξ') :
    Fintype.card {k // k ∈ Θ.S} = Module.finrank ℚ E ∧ ∃ b : {k // k ∈ Θ.S} → E,
      (∀ e : E, e • ξ' ∈ (U.X k).Λ ↔ e ∈ Submodule.span ℤ (Set.range b)) ∧
      (((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det =
        |((Algebra.discr ℚ b : ℚ) : ℝ)| * (∏ τ, (((U.X k).tt ξ' x.1 τ)⁻¹ / 2)) ^ 2 * ((Θ.τ w).map Complex.im).det := by
  let ψ : (Uw.F.Di Ha.i).La →ₗ[𝓞 E] (Fin r → E) :=
    (U.X k).Λ.subtype ∘ₗ (γ.trans (Uw.φ k)).toLinearMap
  have hψ : ∀ v, ψ v = (Uw.φ k (γ v) : Fin r → E) := fun _ => rfl
  have hinj : Function.Injective ψ := Subtype.val_injective.comp (γ.trans (Uw.φ k)).injective
  have hrange : LinearMap.range ψ = (U.X k).Λ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hψt : ψ t = ξ' := htξ
  obtain ⟨hcard, b, hb, hspan⟩ := exists_line_basis ψ hinj
    (fun v => ∀ v', Ha.y v' = 0 → (Uw.F.Di Ha.i).EF v v' = 0)
    (fun k : {k // k ∈ Θ.S} => Θ.bas (Pi.single (.inl k.1) 1))
    (fun c v hv v' hv' => by
      rw [Datum.adj]; exact hv _ (by rw [map_smul, hv', smul_zero]))
    (fun m v hm hv v' hv' => by
      have := hv v' hv'
      rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hm)
    (mem_span Θ) (card_le Θ h1) t ht (hψt ▸ hξ)
  rw [hψt] at hb hspan
  rw [hrange] at hspan
  refine ⟨hcard, b, hspan, ?_⟩
  obtain ⟨Hm, hR⟩ := (Uw.period k x).2.2.2.2
  have hmaj := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k x Hm hG hU hR).1
  let p : Fin Uw.g → Fin Uw.g → ℂ := fun j => Uw.Pm k x (γ (Θ.bas (Pi.single (.inl j) 1)))
  let q : Fin Uw.g → Fin Uw.g → ℂ := fun j => Uw.Pm k x (γ (Θ.bas (Pi.single (.inr j) 1)))
  have hq : ∀ j, q j = ∑ i, Θ.τ w i j • p i := fun j => by
    simp only [p, q, hL, ← map_smul, ← map_sum]
    congr 1
    exact cols Θ.h (Θ.τ w) _ _ (fun i => (Θ.per w i).1) (fun i => (Θ.per w i).2) j
  have hM := riem_inv Hm (Θ.τ w) p q hq
    (fun i j => by simp [p, hR.2.2, hγ, Θ.sympl, omegaStd])
    (fun i j => by
      simp only [p, q, hR.2.2, hγ, Θ.sympl, omegaStd]
      by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm])
  have hJ := det_compl _ _ hM (· ∈ Θ.S)
  have hQ : ∀ v (e : E), ψ v = e • ξ' → (hermForm Hm (Uw.Pm k x (γ v)) (Uw.Pm k x (γ v))).re =
      ∑ τ : (U.X k).Ψ, Complex.normSq (τ.1 e) * ((U.X k).tt ξ' x.1 τ)⁻¹ := by
    intro v e hv
    rw [hmaj, ← hψ, hv]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : Data.emb τ.1 (e • ξ') = τ.1 e • Data.emb τ.1 ξ' := by
      ext i; simp [Data.emb]
    rw [this, UnipMove.DeltaValuation.maj_smul, Data.tt, one_div, inv_inv]
    ring
  have hD := det_gram hcard (U.X k).Ψ (U.X k).cmType b (fun τ => ((U.X k).tt ξ' x.1 τ)⁻¹)
    (Matrix.toSquareBlockProp (Matrix.of fun i j => (hermForm Hm (p i) (p j)).re) (· ∈ Θ.S)) (fun i j => by
      have e0 := polar hR.1 (p i.1) (p j.1)
      have e1 := hQ _ _ (hb i)
      have e2 := hQ _ _ (hb j)
      have e3 := hQ (Θ.bas (Pi.single (.inl i.1) 1) + Θ.bas (Pi.single (.inl j.1) 1)) (b i + b j)
        (by rw [map_add, hb i, hb j, add_smul])
      rw [map_add, map_add] at e3
      simp only [p] at e0
      rw [e1, e2, e3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib] at e0
      change (hermForm Hm (p i.1) (p j.1)).re = _
      refine mul_left_cancel₀ (two_ne_zero) (e0.trans ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_add, Complex.normSq_add]
      ring)
  rw [← hD]
  convert hJ using 2 <;> first | rfl | congr!

theorem final {g s : ℕ} (hs : s ≤ g) {dY dO D : ℝ} (hY : 0 < dY) (hD : 0 < D) {ι : Type} [Fintype ι] (u : ι → ℝ)
    (hu : ∀ i, 0 < u i) (h : dO = D * (∏ i, (u i / 2)) ^ 2 * dY) :
    (Real.sqrt (2 ^ g * dY))⁻¹ = (Real.sqrt (2 ^ (g - s) * dO))⁻¹ *
      (Real.sqrt D * ((Real.sqrt (2 ^ s))⁻¹ * ∏ _i : ι, (2 : ℝ)⁻¹)) * ∏ i, u i := by
  have hp : 0 < ∏ i, (u i / 2) := Finset.prod_pos fun i _ => half_pos (hu i)
  have e : (∏ _i : ι, (2 : ℝ)⁻¹) * ∏ i, u i = ∏ i, (u i / 2) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => by ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_sub_cancel_left, h, pow_add, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, e]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul hD.le, Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]
  have := Real.sqrt_pos.2 hY
  have := Real.sqrt_pos.2 hD
  have : 0 < Real.sqrt (2 ^ s) := by positivity
  have : 0 < Real.sqrt (2 ^ m) := by positivity
  field_simp

theorem discr_bound {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = Module.finrank ℚ E) (b : ι → E)
    (h : ∀ c : 𝓞 E, (c : E) ∈ Submodule.span ℤ (Set.range b)) :
    Algebra.discr ℚ b ≠ 0 ∧ |Algebra.discr ℚ b| ≤ |((NumberField.discr E : ℤ) : ℚ)| := by
  classical
  let f : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ ι := Fintype.equivOfCardEq (by
    rw [hι, Module.finrank_eq_card_basis (integralBasis E)])
  have e : Algebra.discr ℚ (integralBasis E ∘ f.symm) = ((NumberField.discr E : ℤ) : ℚ) := by
    rw [Algebra.discr_reindex, coe_discr]
  rw [← e]
  refine discr_le b _ (fun i => ?_) (by rw [e]; exact_mod_cast discr_ne_zero E)
  rw [Function.comp_apply, integralBasis_apply]
  exact h _

theorem det_im_eq_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (k : U.Comp) (ξ' : Fin r → E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → Module.finrank (𝓞 E) a.D₀.X = 1 → ∃ C : ℝ, 0 < C ∧ C ≤ Real.sqrt |((NumberField.discr E : ℤ) : ℝ)| ∧ ∀ (w : ℂ) (x : (U.X k).dom) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), Ha.T < w.im → (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w v)) → (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') → (∃ t, (∀ v', Ha.y v' = 0 → (Uw.F.Di Ha.i).EF t v' = 0) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') → (Real.sqrt (2 ^ Uw.g * ((Θ.τ w).map Complex.im).det))⁻¹ = (Real.sqrt (2 ^ (Uw.g - Θ.S.card) * ((((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ * C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹ := by
  intro E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha th Θ k ξ' hG hU hξ h1
  by_cases hex : Fintype.card {k // k ∈ Θ.S} = Module.finrank ℚ E ∧ ∃ b : {k // k ∈ Θ.S} → E,
      ∀ e : E, e • ξ' ∈ (U.X k).Λ ↔ e ∈ Submodule.span ℤ (Set.range b)
  · obtain ⟨hcard, b₀, hb₀⟩ := hex
    have hO : ∀ c : 𝓞 E, (c : E) • ξ' ∈ (U.X k).Λ := fun c => (U.X k).Λ.smul_mem c hξ.1
    obtain ⟨n0, le0⟩ := discr_bound hcard b₀ (fun c => (hb₀ _).1 (hO c))
    have hD : (0 : ℝ) < |((Algebra.discr ℚ b₀ : ℚ) : ℝ)| := abs_pos.2 (by exact_mod_cast n0)
    refine ⟨Real.sqrt |((Algebra.discr ℚ b₀ : ℚ) : ℝ)| *
      ((Real.sqrt (2 ^ Θ.S.card))⁻¹ * ∏ _i : (U.X k).Ψ, (2 : ℝ)⁻¹), by positivity, ?_, ?_⟩
    · refine le_trans (mul_le_of_le_one_right (Real.sqrt_nonneg _) ?_) (Real.sqrt_le_sqrt (by exact_mod_cast le0))
      refine mul_le_one₀ (inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (one_le_pow₀ one_le_two))) (by positivity) ?_
      exact Finset.prod_le_one (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    · rintro w x L γ hw hL hγ ⟨t, ht, htξ⟩
      obtain ⟨-, b, hb, hdet⟩ := key E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hG hU hξ.2.2 h1 w x L γ hL hγ
        t ht htξ
      obtain ⟨n1, l1⟩ := discr_le b b₀ (fun i => (hb _).1 ((hb₀ _).2 (Submodule.subset_span ⟨i, rfl⟩))) n0
      obtain ⟨-, l2⟩ := discr_le b₀ b (fun i => (hb₀ _).1 ((hb _).2 (Submodule.subset_span ⟨i, rfl⟩))) n1
      have e : |((Algebra.discr ℚ b : ℚ) : ℝ)| = |((Algebra.discr ℚ b₀ : ℚ) : ℝ)| := by
        exact_mod_cast le_antisymm l1 l2
      rw [e] at hdet
      refine final (by simpa using Finset.card_le_univ Θ.S) (Θ.pos w hw).2.det_pos hD _ (fun τ => ?_) hdet
      rw [Data.tt, one_div, inv_inv]
      refine mul_pos ?_ ((U.X k).maj_pos x.2 τ ?_)
      · exact mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero τ.1).2 (U.X k).ξ0_ne))
      · intro h0
        exact hξ.2.2 (funext fun i => (map_eq_zero τ.1).1 (congrFun h0 i))
  · refine ⟨_, Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero E)), le_rfl, ?_⟩
    rintro w x L γ hw hL hγ ⟨t, ht, htξ⟩
    obtain ⟨hc, b, hb, -⟩ := key E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hG hU hξ.2.2 h1 w x L γ hL hγ
      t ht htξ
    exact absurd ⟨hc, b, hb⟩ hex

end GlobalTheory.LatticeCovolumeL2
