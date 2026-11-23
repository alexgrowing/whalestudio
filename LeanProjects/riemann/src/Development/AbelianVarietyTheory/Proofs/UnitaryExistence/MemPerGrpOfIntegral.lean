import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalThetaStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusOfSelfD
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralHarmonicNeZeroAndIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleExistsAndEval
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaFunctionIsogenyRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

section Analytic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.ThetaNeZero

section Forms

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem hf_transpose (a v : Fin g → ℂ) : star v ⬝ᵥ Hmᵀ *ᵥ a = hermForm Hm a v := by
  rw [hermForm, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

theorem hf_add_left (a b v : Fin g → ℂ) : hermForm Hm (a + b) v = hermForm Hm a v + hermForm Hm b v := by
  simp only [hermForm, add_dotProduct]

theorem hf_add_right (a u v : Fin g → ℂ) : hermForm Hm a (u + v) = hermForm Hm a u + hermForm Hm a v := by
  simp only [hermForm, star_add, mulVec_add, dotProduct_add]

theorem hf_smul_left (t : ℂ) (a v : Fin g → ℂ) : hermForm Hm (t • a) v = t * hermForm Hm a v := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

theorem eq_zero_of_im (hpos : ∀ z, z ≠ 0 → 0 < (hermForm Hm z z).re) {S : Set (Fin g → ℂ)}
    (hS : Submodule.span ℝ S = ⊤) {d : Fin g → ℂ} (h : ∀ a ∈ S, (hermForm Hm a d).im = 0) : d = 0 := by
  have key : ∀ z, (hermForm Hm z d).im = 0 := by
    intro z
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem u hu => exact h u hu
    | zero => simp [hermForm]
    | add a b _ _ ha hb => rw [hf_add_left, add_im, ha, hb, add_zero]
    | smul t a _ ha => rw [← Complex.coe_smul, hf_smul_left, im_ofReal_mul, ha, mul_zero]
  by_contra hd
  have h1 := key (I • d)
  rw [hf_smul_left, I_mul_im] at h1
  exact (hpos d hd).ne' h1

theorem discrete_of_integral (hpos : ∀ z, z ≠ 0 → 0 < (hermForm Hm z z).re) (Λ : AddSubgroup (Fin g → ℂ))
    (hS : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hint : ∀ a ∈ Λ, ∀ v ∈ Λ, ∃ k : ℤ, (hermForm Hm a v).im = k) : DiscreteTopology Λ := by
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  have hfin : b.Finite := hli.setFinite
  have hop : IsOpen (⋂ a ∈ b, {v : Fin g → ℂ | |(hermForm Hm a v).im| < 1}) := by
    refine hfin.isOpen_biInter fun a _ => isOpen_lt ?_ continuous_const
    unfold hermForm
    fun_prop
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert hop.preimage (continuous_subtype_val (p := fun v => v ∈ Λ)) using 1
  ext v
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro rfl a _
    simp [hermForm]
  · intro h
    refine Subtype.ext (eq_zero_of_im Hm hpos (hsp.trans hS) fun a ha => ?_)
    obtain ⟨k, hk⟩ := hint a (hb ha) v v.2
    have h1 := h a ha
    rw [hk] at h1 ⊢
    have h2 : |k| < 1 := by exact_mod_cast h1
    rw [Int.abs_lt_one_iff.1 h2, Int.cast_zero]

end Forms

section Deriv

open scoped ContDiff

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffAt_of_entire [FiniteDimensional ℂ V] {F : V → ℂ} (hF : Differentiable ℂ F) (x : V) :
    ContDiffAt ℂ ω F x := by
  let e : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    (Module.finBasis ℂ V).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (F ∘ e.symm) := hF.comp e.symm.differentiable
  have h2 : AnalyticOnNhd ℂ (F ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ _ _ isOpen_univ h1.differentiableOn
  have h3 : ContDiff ℂ ω (F ∘ e.symm) := by
    rw [← contDiffOn_univ]
    exact h2.contDiffOn uniqueDiffOn_univ
  have : F = (F ∘ e.symm) ∘ e := by ext y; simp
  rw [this]
  exact (h3.comp e.contDiff).contDiffAt

open ReciprocityTheory.ChartRestriction.G.PullbackSections (mD mD_coe lD_eq) in
theorem polyDeriv_eq_mD {θ : V → ℂ} {x : V} (hθ : ContDiffAt ℂ ω θ x) {T₁ : Type} (P : MvPolynomial T₁ ℂ)
    (u : T₁ → V) :
    I2.polyDeriv P u θ x = ∑ m ∈ P.support, P.coeff m * mD θ x ((Finsupp.toMultiset m).map u) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hL : (((Finsupp.toMultiset m).toList.map u : List V) : Multiset V) =
      (Finsupp.toMultiset m).map u := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  rw [← hL, mD_coe hθ, lD_eq θ x _ (n := Multiset.card (Finsupp.toMultiset m))
    (by rw [List.length_map, Multiset.length_toList])]
  congr 1
  funext k
  simp [List.get_eq_getElem]

theorem polyDeriv_rename [FiniteDimensional ℂ V] {θ : V → ℂ} (hθ : Differentiable ℂ θ) (x : V) {T₁ T₂ : Type}
    (ρ : T₁ → T₂) (hρ : Function.Injective ρ) (P : MvPolynomial T₁ ℂ) (v : T₂ → V) :
    I2.polyDeriv (MvPolynomial.rename ρ P) v θ x = I2.polyDeriv P (v ∘ ρ) θ x := by
  have h := contDiffAt_of_entire hθ x
  rw [polyDeriv_eq_mD h, polyDeriv_eq_mD h, MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]

theorem polyDeriv_const_mul [FiniteDimensional ℂ V] {T₁ : Type} (P : MvPolynomial T₁ ℂ) (u : T₁ → V) (c : ℂ)
    {G : V → ℂ} (hG : Differentiable ℂ G) (x : V) :
    I2.polyDeriv P u (fun z => c * G z) x = c * I2.polyDeriv P u G x := by
  have := I2.polyDeriv_sum P u (Finset.univ : Finset Unit) (fun _ => c) (fun _ => G)
    (fun _ _ k => I2.contDiff_of_differentiable_fd hG k) x
  simpa using this

theorem polyDeriv_const_mul' [FiniteDimensional ℂ V] {T₁ : Type} (P : MvPolynomial T₁ ℂ) (u : T₁ → V) (c : ℂ)
    {G : V → ℂ} (hG : Differentiable ℂ fun z => c * G z) (x : V) :
    I2.polyDeriv P u (fun z => c * G z) x = c * I2.polyDeriv P u G x := by
  by_cases hc : c = 0
  · have := polyDeriv_const_mul P u 0 hG x
    simpa [hc] using this
  · have h : G = fun z => c⁻¹ * (c * G z) := by
      funext z; field_simp
    conv_rhs => rw [h]
    rw [polyDeriv_const_mul P u c⁻¹ hG x]
    field_simp

end Deriv

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem pv_add' (u v : Fin r → E) : pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  funext j
  simp [pv, per_add]

noncomputable def pvHom : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) (pv_add' idx x)

noncomputable def perGrp (L : Lt E r) : AddSubgroup (Fin g → ℂ) := L.toAddSubgroup.map (pvHom idx x)

theorem mem_perGrp {L : Lt E r} {z : Fin g → ℂ} : z ∈ perGrp idx x L ↔ ∃ u ∈ L, pv X idx x u = z := Iff.rfl

theorem pv_nsmul (k : ℕ) (v : Fin r → E) : pv X idx x (k • v) = (k : ℂ) • pv X idx x v := by
  rw [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (pvHom idx x) k v

variable {x}

theorem mem_perGrp_of_integral (hs : IsSympl X bas) (hx : x ∈ X.dom) {L : Lt E r} (hL : SelfD X L)
    {v : Fin g → ℂ}
    (hv : ∀ u ∈ L, ∃ k : ℤ, (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) v).im = k) : v ∈ perGrp idx x L := by
  choose k hk using hv
  let φ : L →+ ℤ := AddMonoidHom.mk' (fun u => k u u.2) fun a b => by
    have h : (hermForm (ThFr.Hm X bas idx x) (pv X idx x ((a : Fin r → E) + b)) v).im = k _ (a + b).2 :=
      hk _ (a + b).2
    rw [pv_add', hf_add_left, add_im, hk _ a.2, hk _ b.2] at h
    exact_mod_cast h.symm
  obtain ⟨u₀, hu₀, hφ⟩ := SelfTorus.perf hs hL φ
  have h0 : v + pv X idx x u₀ = 0 := by
    refine eq_zero_of_im _ (fun z hz => hermForm_Hm_pos idx hs hx hz)
      (span_image_pv idx hs hx L (TensLat.span_of_selfD X hL)) ?_
    rintro _ ⟨u, hu, rfl⟩
    have h1 : (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x u₀)).im = (EF X u u₀ : ℝ) :=
      im_hermForm_Hm idx hs hx u u₀
    have h2 : ((k u hu : ℤ) : ℚ) = EF X u₀ u := hφ ⟨u, hu⟩
    rw [hf_add_right, add_im, hk u hu, h1, TensLat.EF_swap, ← h2]
    push_cast
    ring
  rw [eq_neg_of_add_eq_zero_left h0]
  exact neg_mem ⟨u₀, hu₀, rfl⟩

theorem mem_smul_iff {L : Lt E r} (hL : SelfD X L) {M : ℕ} (hM : M ≠ 0) {P Q : Ideal (𝓞 E)}
    (cj : 𝓞 E → 𝓞 E) (hcj : ∀ a, ((cj a : 𝓞 E) : E) = cc (a : E)) (hPQ : Q * P = Ideal.span {(M : 𝓞 E)})
    (h1 : ∀ a ∈ P, cj a ∈ Q) (h2 : ∀ b ∈ Q, cj b ∈ P) {w : Fin r → E} (hw : w ∈ L) :
    (∀ u ∈ P • L, ∃ k : ℤ, EF X u w = M * k) ↔ w ∈ P • L := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMQ : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsm : ∀ (a : 𝓞 E) (u v : Fin r → E), EF X (a • u) v = EF X u (cj a • v) := fun a u v => by
    have := GlobalTheory.Dict.EF_smul_left (X := X) (a : E) u v
    rw [← hcj] at this
    exact this
  have hcc : ∀ a, cj (cj a) = a := fun a => RingOfIntegers.ext (by
    rw [hcj, hcj, cc, cc, IsCMField.complexConj_apply_apply])
  have hn : ∀ u v, EF X u (M • v) = M * EF X u v := fun u v => by
    exact (map_nsmul (EFBil X u) M v).trans (nsmul_eq_mul _ _)
  constructor
  · intro h
    have hb : ∀ b ∈ Q, ∃ u ∈ L, b • w = M • u := by
      intro b hb
      have e : b • w = M • ((M : E)⁻¹ • b • w) := by
        rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME, one_smul]
      refine ⟨_, (hL.2 _).2 fun y hy => ?_, e⟩
      obtain ⟨k, hk⟩ := h _ (Submodule.smul_mem_smul (h2 b hb) hy)
      rw [hsm, hcc, e, hn] at hk
      exact ⟨-k, by rw [TensLat.EF_swap, mul_left_cancel₀ hMQ hk, Int.cast_neg]⟩
    have hall : ∀ t ∈ Q * P, ∃ u ∈ P • L, t • w = M • u := by
      intro t ht
      refine Submodule.mul_induction_on ht (fun b hb' a ha => ?_) ?_
      · obtain ⟨u, hu, e⟩ := hb b hb'
        exact ⟨a • u, Submodule.smul_mem_smul ha hu, by rw [mul_comm, mul_smul, e, smul_comm]⟩
      · rintro s t ⟨u, hu, e⟩ ⟨u', hu', e'⟩
        exact ⟨u + u', add_mem hu hu', by rw [add_smul, e, e', smul_add]⟩
    obtain ⟨u, hu, e⟩ := hall M (hPQ ▸ Ideal.mem_span_singleton_self _)
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at e
    rwa [smul_right_injective _ hME e]
  · intro hwP u hu
    refine Submodule.smul_induction_on hu (fun a ha y hy => ?_) ?_
    · have h3 : cj a • w ∈ (Q * P) • L := by
        rw [mul_smul]
        exact Submodule.smul_mem_smul (h1 a ha) hwP
      rw [hPQ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
      obtain ⟨t, ht, e⟩ := h3
      obtain ⟨k, hk⟩ := (hL.2 y).1 hy t ht
      exact ⟨k, by rw [hsm, ← e, Nat.cast_smul_eq_nsmul, hn, hk]⟩
    · rintro s t ⟨k, hk⟩ ⟨k', hk'⟩
      refine ⟨k + k', ?_⟩
      have := LinearMap.map_add₂ (EFBil X) s t w
      change EF X (s + t) w = EF X s w + EF X t w at this
      rw [this, hk, hk']
      push_cast
      ring

open scoped ComplexOrder in

theorem exists_jet_ne_zero (hs : IsSympl X bas) (hd : x ∈ X.dom) {L : Lt E r} (hL : SelfD X L) {M : ℕ}
    (hM : M ≠ 0) {P Q : Ideal (𝓞 E)} (cj : 𝓞 E → 𝓞 E) (hcj : ∀ a, ((cj a : 𝓞 E) : E) = cc (a : E))
    (hPQ : Q * P = Ideal.span {(M : 𝓞 E)}) (h1 : ∀ a ∈ P, cj a ∈ Q) (h2 : ∀ b ∈ Q, cj b ∈ P) {w : E}
    {θ : (Fin g → ℂ) → ℂ} (hθ : IsTheta1 X bas idx w x L θ) (hθ0 : θ ≠ 0) {n : ℕ}
    (R : MvPolynomial (Fin n × Fin g) ℂ) (hR : R ≠ 0) (hdeg : R.totalDegree + 2 ≤ M) :
    ∃ u : Fin n → Fin r → E, (∀ b, u b ∈ P • L) ∧ ∀ Y : Fin n → Fin r → E, (∀ b, Y b - (M : E)⁻¹ • u b ∈ L) →
      I2.polyDeriv R (fun q => (Pi.single q.1 (Pi.single q.2 (1 : ℂ) : Fin g → ℂ) : Fin n → Fin g → ℂ))
        (fun z : Fin n → Fin g → ℂ => ∏ b, fock X bas idx x 1 (pv X idx x (Y b)) θ (z b)) 0 ≠ 0 := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMP : (M : 𝓞 E) ∈ P := (hPQ.ge.trans Ideal.mul_le_right) (Ideal.mem_span_singleton_self _)
  have hpos : ∀ z, z ≠ 0 → 0 < (hermForm (ThFr.Hm X bas idx x) z z).re := fun z hz => hermForm_Hm_pos idx hs hd hz
  have him : ∀ u v, (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ) :=
    fun u v => im_hermForm_Hm idx hs hd u v
  obtain ⟨hconj, -, -, -, -, hinj, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hd
  have hint : ∀ a ∈ perGrp idx x L, ∀ v ∈ perGrp idx x L, ∃ k : ℤ,
      (hermForm (ThFr.Hm X bas idx x) a v).im = k := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨k, hk⟩ := (hL.2 u).1 hu v hv
    exact ⟨k, (him u v).trans (by rw [hk, Rat.cast_intCast])⟩
  have hPD : (ThFr.Hm X bas idx x)ᵀ.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos (Hm_isHermitian idx hs hd).transpose fun z hz => ?_
    rw [hf_transpose, Complex.pos_iff]
    refine ⟨hpos z hz, ?_⟩
    have := hconj z z
    rw [hx_eq_hermForm] at this
    exact (Complex.conj_eq_iff_im.1 this.symm).symm
  obtain ⟨y, hy, hne⟩ := GlobalTheory.T.theta_function_isogeny_restriction g _ hPD (perGrp idx x L)
    (discrete_of_integral _ hpos _ (span_image_pv idx hs hd L (TensLat.span_of_selfD X hL)) hint)
    (fun v => by
      simp only [hf_transpose]
      exact ⟨fun h => mem_perGrp_of_integral idx hs hd hL fun u hu => h _ ⟨u, hu, rfl⟩,
        fun h a ha => hint a ha v h⟩)
    (fun a => (eps1 X w (Function.invFun (pv X idx x) a))⁻¹) θ hθ.1 hθ0
    (fun a _ => by
      rw [norm_inv, eps1, show ∀ q : ℚ, (Real.pi : ℂ) * I * (q : ℂ) = ((Real.pi * q : ℝ) : ℂ) * I from
        fun q => by push_cast; ring, norm_exp_ofReal_mul_I, inv_one])
    (by
      rintro _ ⟨u, hu, rfl⟩ z
      change θ (z + pv X idx x u) = (eps1 X w (Function.invFun (pv X idx x) (pv X idx x u)))⁻¹ *
        cexp (Real.pi * (star (pv X idx x u) ⬝ᵥ _ *ᵥ z) +
          Real.pi / 2 * (star (pv X idx x u) ⬝ᵥ _ *ᵥ pv X idx x u)) * θ z
      have h := congrFun (hθ.2 u hu) z
      simp only [Pi.smul_apply, smul_eq_mul, fock, hx_eq_hermForm, hf_add_left, hf_smul_left] at h
      have he : eps1 X w u ≠ 0 := exp_ne_zero _
      rw [Function.leftInverse_invFun hinj, hf_transpose, hf_transpose, ← h, Complex.exp_neg]
      have hA : ∀ A B : ℂ, (Real.pi : ℂ) * A + Real.pi / 2 * B = ((1 : ℕ) : ℂ) * Real.pi * (A + 1 / 2 * B) :=
        fun A B => by push_cast; ring
      rw [hA]
      field_simp)
    M (perGrp idx x (P • L)) (AddSubgroup.map_mono (fun _ h => Submodule.smul_le_right h))
    (fun v => by
      simp only [hf_transpose]
      constructor
      · intro h
        obtain ⟨t, ht, rfl⟩ : v ∈ perGrp idx x L := by
          refine mem_perGrp_of_integral idx hs hd hL fun u hu => ?_
          obtain ⟨k, hk⟩ := h _ ⟨_, Submodule.smul_mem_smul hMP hu, rfl⟩
          change (hermForm _ (pv X idx x ((M : 𝓞 E) • u)) v).im = _ at hk
          rw [Nat.cast_smul_eq_nsmul, pv_nsmul, hf_smul_left, ← ofReal_natCast, im_ofReal_mul] at hk
          exact ⟨k, mul_left_cancel₀ hMR hk⟩
        refine ⟨t, (mem_smul_iff hL hM cj hcj hPQ h1 h2 ht).1 fun u hu => ?_, rfl⟩
        obtain ⟨k, hk⟩ := h _ ⟨u, hu, rfl⟩
        exact ⟨k, by exact_mod_cast (him u t).symm.trans hk⟩
      · rintro ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
        obtain ⟨k, hk⟩ := (mem_smul_iff hL hM cj hcj hPQ h1 h2 (Submodule.smul_le_right ht)).2 ht u hu
        exact ⟨k, (him u t).trans (by exact_mod_cast hk)⟩)
    n R hR hdeg
  choose u hu huy using fun b => (mem_perGrp idx x).1 (hy b)
  refine ⟨u, hu, fun Y hY => ?_⟩
  have hyb : ∀ b, pv X idx x ((M : E)⁻¹ • u b) = y b := fun b => by
    refine smul_right_injective _ hMC ?_
    change (M : ℂ) • _ = (M : ℂ) • _
    rw [← pv_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME, one_smul, huy]
  obtain ⟨hcomp, -, -, hdiff, -⟩ := fock_laws E r X g bas idx 0 hs Even.zero x hd 1 θ
  have hrow : ∀ b, ∃ c : ℂ, ∀ z, cexp (-(Real.pi * (star (y b) ⬝ᵥ (ThFr.Hm X bas idx x)ᵀ *ᵥ z))) * θ (z + y b) =
      c * fock X bas idx x 1 (pv X idx x (Y b)) θ z := by
    intro b
    have e1 := hθ.2 _ (hY b)
    have e2 := hcomp (y b) (pv X idx x (Y b - (M : E)⁻¹ • u b))
    have e3 : y b + pv X idx x (Y b - (M : E)⁻¹ • u b) = pv X idx x (Y b) := by
      rw [← hyb, ← pv_add', add_sub_cancel]
    rw [e3] at e2
    have e4 : ∀ (e : ℂ) (a : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ),
        fock X bas idx x 1 a (e • φ) = e • fock X bas idx x 1 a φ := by
      intro e a φ
      funext z
      simp only [fock, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨c, hc⟩ : ∃ c : ℂ, fock X bas idx x 1 (y b) θ = c • fock X bas idx x 1 (pv X idx x (Y b)) θ :=
      ⟨_, by conv_lhs => rw [← e1, e4, e2, smul_smul]⟩
    refine ⟨cexp (Real.pi / 2 * hermForm (ThFr.Hm X bas idx x) (y b) (y b)) * c, fun z => ?_⟩
    have e5 := congrFun hc z
    rw [Pi.smul_apply, smul_eq_mul] at e5
    rw [_root_.mul_assoc, ← e5, fock, ← _root_.mul_assoc, ← Complex.exp_add, hf_transpose, hx_eq_hermForm,
      hf_add_left, hf_smul_left]
    congr 2
    push_cast
    ring
  choose c hc using hrow
  have hent : Differentiable ℂ
      fun z : Fin n → Fin g → ℂ => ∏ b, fock X bas idx x 1 (pv X idx x (Y b)) θ (z b) := by
    have hb : ∀ b, Differentiable ℂ fun z : Fin n → Fin g → ℂ =>
        fock X bas idx x 1 (pv X idx x (Y b)) θ (z b) := fun b =>
      (hdiff hθ.1 (pv X idx x (Y b))).comp (f := fun z : Fin n → Fin g → ℂ => z b) (differentiable_apply b)
    exact fun z => (HasFDerivAt.finset_prod (u := Finset.univ) fun b _ => (hb b z).hasFDerivAt).differentiableAt
  simp only [hc, Finset.prod_mul_distrib] at hne
  rw [polyDeriv_const_mul _ _ _ hent] at hne
  exact right_ne_zero_of_mul hne

end Lattice

section Geometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {r : ℕ}

theorem exists_root (l : Geo.Tor.Level H) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (hm : ∀ a, mk a ∈ L)
    (a : Dw.La) (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ Y : Fin r → E, Y - ((l.M : E)⁻¹) • mk a ∈ L ∧ ∀ s ∈ l.Mb ^ 2, ∃ u ∈ L, s • Y = (2 * l.M) • u := by
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  have hp : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} := l.prod
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := (hp.ge.trans Ideal.mul_le_left) (Ideal.mem_span_singleton_self _)
  have hc : l.Mb ⊔ Mfr l ^ 2 = ⊤ := Ideal.sup_pow_eq_top l.coprime
  obtain ⟨b, hb, t, ht, hbt⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hc)
  obtain ⟨k, hk⟩ := l.odd
  have hs : (-(2 * (k : 𝓞 E)) * t) - 1 ∈ l.Mb := by
    have e : (-(2 * (k : 𝓞 E)) * t) - 1 = -b - (l.M : 𝓞 E) * t := by
      rw [hk]; push_cast; linear_combination hbt
    rw [e]
    exact sub_mem (neg_mem hb) (l.Mb.mul_mem_right t hMb)
  refine ⟨(-(2 * (k : 𝓞 E)) * t) • ((l.M : E)⁻¹) • mk a, ?_, fun s hs' => ?_⟩
  · have h1 : ((-(2 * (k : 𝓞 E)) * t) - 1) • a ∈ (l.Mb * Mfr l) • (⊤ : Submodule (𝓞 E) Dw.La) := by
      rw [mul_smul]
      exact Submodule.smul_mem_smul hs ha
    rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨c, -, hc'⟩ := h1
    have h2 : ((-(2 * (k : 𝓞 E)) * t) - 1) • ((l.M : E)⁻¹ • mk a) = mk c := by
      rw [smul_comm, ← map_smul, ← hc', Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hM, one_smul]
    rw [sub_smul, one_smul] at h2
    rw [h2]
    exact hm c
  · have h1 : s * t ∈ Ideal.span {(l.M : 𝓞 E) ^ 2} := by
      rw [← Ideal.span_singleton_pow, ← hp, mul_pow]
      exact Ideal.mul_mem_mul hs' ht
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 h1
    refine ⟨(-(k : 𝓞 E) * d) • mk a, L.smul_mem _ (hm a), ?_⟩
    have hd' : (d : E) * (l.M : E) ^ 2 = (s : E) * (t : E) := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hd
    rw [← Nat.cast_smul_eq_nsmul E]
    change (s : E) • ((-(2 * (k : 𝓞 E)) * t : 𝓞 E) : E) • (l.M : E)⁻¹ • mk a =
      ((2 * l.M : ℕ) : E) • ((-(k : 𝓞 E) * d : 𝓞 E) : E) • mk a
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    have h3 : ((-(2 * (k : 𝓞 E)) * t : 𝓞 E) : E) = -(2 * (k : E)) * (t : E) := by
      change algebraMap (𝓞 E) E _ = _
      rw [map_mul, map_neg, map_mul, map_ofNat, map_natCast]
    rw [h3]
    push_cast
    field_simp
    linear_combination (k : E) * hd'

theorem exists_thGen_ne_zero (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {l : Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r) (k : U.Comp) (x : (U.X k).dom) (hx : IsUnitFr (U.X k) x.1)
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) : ThNe0 Xo c nab := by
  rintro a n hD - - hdeg ⟨P, hP, hP0⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W, Dc, A, θ, v, κ, he, -, -, hL, hmk, hA, hrd, hθ, hmean, hv, hκ⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr a n hD k x hx
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    obtain ⟨_, _, -, -, h⟩ := hmean
    simp at h
  let ρ : LtN Dw n → Fin n × Fin W.g := fun ℓ => (ℓ.2.2, W.e.symm ⟨ℓ.1, ℓ.2.1⟩)
  have hρ : Function.Injective ρ := by
    rintro ⟨τ, i, b⟩ ⟨τ', i', b'⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h3 := W.e.symm.injective h2
    cases h3
    cases h1
    rfl
  have hhom := (GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2 P hP.1
  have hR0 : MvPolynomial.rename ρ (MvPolynomial.map σ P) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (MvPolynomial.rename_injective ρ hρ),
      map_eq_zero_iff _ (MvPolynomial.map_injective σ σ.injective)]
    exact hP0
  have hRd : (MvPolynomial.rename ρ (MvPolynomial.map σ P)).totalDegree + 2 ≤ l.M := by
    have := ((hhom.map σ).rename_isHomogeneous (f := ρ)).totalDegree_le
    omega
  obtain ⟨u, hu, hjet⟩ := exists_jet_ne_zero Dc.idx Dc.sympl x.2 hL hM (P := Mfr l) (Q := l.Mb) H.bar H.bar_eq
    l.prod (fun b hb => by
      obtain ⟨t, ht, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hb
      have : H.bar ((H.bar : 𝓞 E →+* 𝓞 E) t) = t := RingOfIntegers.ext (by
        rw [H.bar_eq, RingHom.coe_coe, H.bar_eq, IsCMField.complexConj_apply_apply])
      rwa [this])
    (fun b hb => Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hb) hθ hθ0 _ hR0 hRd
  choose xs hxs t ht hut using fun b => hmk.surj (u b) (hu b)
  choose Y hY hY' using fun b => exists_root l (U.X k).Λ (W.mark k) hmk.mem (xs b) (hxs b)
  have hYu : ∀ b, Y b - (l.M : E)⁻¹ • u b ∈ (U.X k).Λ := fun b => by
    rw [hut b, smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hME, one_smul, ← sub_sub]
    exact sub_mem (hY b) (ht b)
  obtain ⟨⟨f, hf, -⟩, hev⟩ := GlobalTheory.thetaRule_exists_and_eval hC E H Dw l Xo c nab hnab a n xs P hP
  refine ⟨f, ⟨xs, P, hP, hf⟩, ?_⟩
  rintro rfl
  have hval := GlobalTheory.T.thetaValue_standardLattice_eq_classicalTheta hC E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x) A Dc.sympl x.2
    hL Dw.p n Dc.hr Dc.eL hU.1 hD.2 (fun ℓ => he ▸ Dc.dir_eq ℓ) nab hnab θ v κ hrd hv hκ (W.mark k) hmk hA xs
    (Matrix.of Y) (fun b => ⟨⟨xs b, hxs b, by rw [sub_self]; exact zero_mem _, hY b⟩, 2, hY' b⟩) a P hP _
    (hev 0 hf ℂ (unC U k x))
  rw [evR, evalAt_zero] at hval
  obtain ⟨-, -, -, hdiff, hprod⟩ := fock_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hD.2 x.1 x.2 1 θ
  have hfun := funext (hprod (fun _ => θ) κ v hv.1 hκ (Matrix.of Y))
  have hent : Differentiable ℂ fun z : Fin n → Fin W.g → ℂ =>
      ∏ b, fock (U.X k) Dc.bas Dc.idx x.1 1 (pv (U.X k) Dc.idx x.1 (Y b)) θ (z b) := by
    have hb : ∀ b, Differentiable ℂ fun z : Fin n → Fin W.g → ℂ =>
        fock (U.X k) Dc.bas Dc.idx x.1 1 (pv (U.X k) Dc.idx x.1 (Y b)) θ (z b) := fun b =>
      (hdiff hθ.1 _).comp (f := fun z : Fin n → Fin W.g → ℂ => z b) (differentiable_apply b)
    exact fun z => (HasFDerivAt.finset_prod (u := Finset.univ) fun b _ => (hb b z).hasFDerivAt).differentiableAt
  refine hjet Y hYu ?_
  rw [thP, ← polyDeriv_const_mul' _ _ _ (hfun ▸ hent), ← hfun] at hval
  have e1 := polyDeriv_rename hent 0 Dc.eL Dc.eL.injective (MvPolynomial.map σ P) (letterDir (U.X k) Dc.hr Dc.idx)
  rw [polyDeriv_rename hent 0 ρ hρ]
  rw [show letterDir (U.X k) Dc.hr Dc.idx ∘ Dc.eL = _ from funext Dc.dir_eq, he] at e1
  exact e1.symm.trans hval.symm

end Geometry

end GlobalTheory.ThetaNeZero

end Analytic

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta

theorem GlobalTheory.ThetaNeZero.thNe0_of_lawsM : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ (_ : StarRing (𝓞 D.host.E)) (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab → ThNe0 (T.Q.Xo j) T.Q.c nab := by
  intro hC D T h j hj _ nab hnab
  obtain ⟨_, _, -, hd⟩ := h.dictU j hj _ T.good_σ₀
  exact GlobalTheory.ThetaNeZero.exists_thGen_ne_zero hC (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))
    ((Formalism.L2.PjFree.goodEmb_iff _).2 T.good_σ₀) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj _ T.good_σ₀))
    ((GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins).2.2.2.2.2.2 j hj).2.1 (T.dict j T.σ₀ 1).1
    ⟨(T.dict j T.σ₀ 1).2, hd.2.2.2.1 1⟩ ((h.muUnit j hj _ T.good_σ₀).2.2.2 1) nab hnab
