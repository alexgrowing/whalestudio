import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMNormIdentity

theorem primeSpectrum_dualNumber_eq (x y : PrimeSpectrum (DualNumber ℂ)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber ℂ), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isDiff_of_isLieComb {w : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ)
    (hc : IsLieComb ![c] ![v] v') : u.IsDiff (c • w) v' := by
  obtain ⟨y, hy, hv'⟩ := hc
  have hl : v'.left = spMap (epsScaleR c) ≫ v.left := by
    have := hy 0
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one] at hv'
    rw [hv']
    simpa using this
  intro U
  rw [hl]
  intro hU f
  have hU' : ⊤ ≤ v.left ⁻¹ᵁ U := fun x _ => by
    have := hU (Set.mem_univ x)
    have hx : (spMap (epsScaleR c)) x = x := primeSpectrum_dualNumber_eq _ _
    change v.left ((spMap (epsScaleR c)) x) ∈ U at this
    rwa [hx] at this
  rw [map_smul, ← h U hU' f]
  have e : (spMap (epsScaleR c) ≫ v.left).appLE U ⊤ hU = v.left.appLE U ⊤ hU' ≫ (spMap (epsScaleR c)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (epsScaleR c)) v.left U ⊤ ⊤ hU' le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((v.left.appLE U ⊤ hU').hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (epsScaleR c)))
  rw [e]
  refine (congrArg TrivSqZeroExt.snd e2).trans ?_
  simp [epsScaleR]

theorem lift_unique {g₀ : ℕ} (F F' : (Fin g₀ → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (F' z)) :
    F = F' := by
  have hm : ∀ z, (F - F') z ∈ u.Λ := fun z => by
    rw [← u.ker]
    have h1 := u.ex_add ((F - F') z) (F' z)
    rw [LinearMap.sub_apply, sub_add_cancel, h z] at h1
    exact (right_eq_mul.1 h1)
  haveI := u.discrete
  have hc : Continuous (fun z => (⟨(F - F') z, hm z⟩ : u.Λ)) :=
    (LinearMap.continuous_of_finiteDimensional (F - F')).subtype_mk _
  refine LinearMap.ext fun z => ?_
  have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa [sub_eq_zero] using this

end Unif

theorem exists_eigen_components {E : Type} [Field E] [NumberField E] {L V : Type} [AddCommGroup L] [Module (𝓞 E) L]
    [AddCommGroup V] [Module ℂ V] (X : L →+ V) :
    ∃ x : (E →+* ℂ) → L →+ V, ∀ (s : 𝓞 E) a, X (s • a) = ∑ τ : E →+* ℂ, τ (s : E) • x τ a := by
  classical
  let b := RingOfIntegers.basis E
  have hli : LinearIndependent ℂ (fun (τ : E →+* ℂ) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) => τ (b i : E)) := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    refine EigenNorm.eq_zero_of_sum_embedding_mul f fun s => ?_
    have hb : ∀ i, ∑ τ : E →+* ℂ, τ (b i : E) * f τ = 0 := fun i => by
      simpa [mul_comm] using congrFun hf i
    rw [← b.sum_repr s]
    simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, map_zsmul, Finset.sum_mul, smul_mul_assoc] at hb ⊢
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, hb, smul_zero, Finset.sum_const_zero]
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Embeddings.card, Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank])
  have hc : ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 E), ∃ c : (E →+* ℂ) → ℂ,
      ∑ τ, c τ • (fun j => τ (b j : E)) = Pi.single i 1 := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsp ▸ Submodule.mem_top)
  choose c hc using hc
  refine ⟨fun τ => AddMonoidHom.mk' (fun a => ∑ i, c i τ • X (b i • a)) fun a a' => by
    simp [smul_add, Finset.sum_add_distrib], fun s a => ?_⟩
  have hb : ∀ j, X (b j • a) = ∑ τ : E →+* ℂ, τ (b j : E) • ∑ i, c i τ • X (b i • a) := fun j => by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ τ : E →+* ℂ, τ (b j : E) * c i τ = (Pi.single i 1 : _ → ℂ) j := fun i => by
      rw [← hc i]
      simp [mul_comm]
    simp only [← Finset.sum_smul, this]
    simp [Pi.single_apply]
  simp only [AddMonoidHom.mk'_apply]
  conv_lhs => rw [← b.sum_repr s]
  conv_rhs => rw [← b.sum_repr s]
  simp only [Finset.sum_smul, smul_assoc, map_sum, map_zsmul, RingOfIntegers.coe_eq_algebraMap] at hb ⊢
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.smul_sum, ← hb]

theorem eq_zero_of_sum_embedding_smul {E : Type} [Field E] [NumberField E] {g : ℕ} (f : (E →+* ℂ) → Fin g → ℂ)
    (hf : ∀ s : 𝓞 E, ∑ τ : E →+* ℂ, τ (s : E) • f τ = 0) (τ : E →+* ℂ) : f τ = 0 := by
  funext k
  exact EigenNorm.eq_zero_of_sum_embedding_mul (fun τ => f τ k) (fun s => by simpa using congrFun (hf s) k) τ

theorem quadratic_eq_zero {L : Type} [AddCommGroup L] (B : L → L → ℂ) (hl : ∀ a b c, B (a + b) c = B a c + B b c)
    (hr : ∀ a b c, B a (b + c) = B a b + B a c) {m : ℕ} (e : Fin m → L)
    (he : Submodule.span ℤ (Set.range e) = ⊤) (h1 : ∀ i, B (e i) (e i) = 0)
    (h2 : ∀ i j, B (e i + e j) (e i + e j) = 0) (a : L) : B a a = 0 := by
  let S : L →+ L →+ ℂ := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => B a b + B b a) fun b c => by
    rw [hl, hr]; ring) fun a b => by
      ext c
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, hl, hr]
      ring
  have hS : ∀ i, S (e i) = 0 := fun i => by
    have : (S (e i)).toIntLinearMap = 0 := by
      refine LinearMap.ext_on_range he fun j => ?_
      have := h2 i j
      rw [hl, hr, hr, h1, h1] at this
      simpa [S] using this
    exact AddMonoidHom.ext fun c => LinearMap.congr_fun this c
  have hS' : S.toIntLinearMap = 0 := LinearMap.ext_on_range he hS
  have h3 : S a = 0 := LinearMap.congr_fun hS' a
  have h4 : B a a + B a a = 0 := DFunLike.congr_fun h3 a
  linear_combination h4 / 2

theorem exists_eigen_hermForm_eq :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (P₀ P : Out.PolAV (Sp ℂ)), P₀.g = 1 →
  ∀ (u₀ : HolUnif P₀.A P₀.L P₀.g) (u : HolUnif P.A P.L P.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u₀.IsAH H₀ χ₀ → u.IsAH Hm χ →
  (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
  ∀ (act : OAct (𝓞 E) P.A) (L : Type) [AddCommGroup L] [Module (𝓞 E) L] (h : L → L → E) (ρ : ℂ) (φ : L → (P₀.A ⟶ P.A))
    (v₀ : epsR ℂ ⟶ P₀.A) (w₀ : Fin P₀.g → ℂ) (m : ℕ) (e : Fin m → L) (nn : L → ℕ),
  ρ ^ 2 = -(H.d : ℂ) → (∀ a b c, h (a + b) c = h a c + h b c) → (∀ (s : 𝓞 E) a c, h (s • a) c = s * h a c) →
  (∀ a b, h b a = IsCMField.complexConj E (h a b)) →
  (∀ a, (nn a : ℂ) = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a a)) →
  (∀ a, IsMonHom (φ a)) → (∀ a b, φ (a + b) = φ a * φ b) → (∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ act.act s) →
  IsTangent v₀ → u₀.IsDiff w₀ v₀ → (∀ a, IsLieComb ![ρ] ![v₀ ≫ φ a] (v₀ ≫ φ a ≫ act.act H.rt)) →
  Submodule.span ℤ (Set.range e) = ⊤ →
  (∀ a, ((∃ i, a = e i) ∨ ∃ i j, a = e i + e j) →
    ∃ N : ℕ, 1 ≤ N ∧ LBIso (lbPow (P.L.pull (φ a).left) N) (lbPow P₀.L (N * nn a))) →
  ∃ x : (E →+* ℂ) → L →+ (Fin P.g → ℂ), (∀ a, u.IsDiff (∑ τ, x τ a) (v₀ ≫ φ a)) ∧
    (∀ τ (s : 𝓞 E) a, x τ (s • a) = τ (s : E) • x τ a) ∧ (∀ τ, τ (H.rt : E) ≠ ρ → x τ = 0) ∧
    ∀ τ τ' a b, τ (H.rt : E) = ρ →
      hermForm Hm (x τ a) (x τ' b) = open Classical in if τ' = τ then hermForm H₀ w₀ w₀ * τ (h a b) else 0 := by
  intro E _ _ _ H P₀ P _ u₀ u H₀ χ₀ Hm χ hu₀ hu hT hT' act L _ _ h ρ φ v₀ w₀ m e nn hρ hadd hsmul hsymm hnn hφ hφa hφs
    hv₀ hw₀ hLie he hiso
  classical
  choose F hF _ hFd _ using fun a =>
    GlobalTheory.HomLinear.exists_linear_of_isMonHom P₀.A P.A P₀.isAb P.isAb P₀.L P.L P₀.g P.g u₀ u hT hT' (φ a) (hφ a)
  have hFa : ∀ a b, F (a + b) = F a + F b := fun a b => lift_unique u _ _ fun z => by
    rw [LinearMap.add_apply, u.ex_add, hF, hF, hF, hφa, MonObj.comp_mul]
  let X : L →+ (Fin P.g → ℂ) := AddMonoidHom.mk' (fun a => F a w₀) fun a b => by
    rw [hFa, LinearMap.add_apply]
  have hX : ∀ a, X a = F a w₀ := fun _ => rfl
  have hXd : ∀ a, u.IsDiff (X a) (v₀ ≫ φ a) := fun a => (hFd a w₀ v₀ hv₀ hw₀).2
  have hXrt : ∀ a, X (H.rt • a) = ρ • X a := fun a => by
    refine (hT _ (hFd (H.rt • a) w₀ v₀ hv₀ hw₀).1).unique (hXd _) ?_
    rw [hφs]
    exact isDiff_of_isLieComb u (hXd a) ρ (hLie a)
  obtain ⟨x, hx⟩ := exists_eigen_components (E := E) X
  have hsum : ∀ a, ∑ τ, x τ a = X a := fun a => by
    simpa using (hx 1 a).symm
  have hxs : ∀ τ (s : 𝓞 E) a, x τ (s • a) = τ (s : E) • x τ a := fun τ s a => by
    refine sub_eq_zero.1 (eq_zero_of_sum_embedding_smul (fun τ => x τ (s • a) - τ (s : E) • x τ a) (fun t => ?_) τ)
    have h1 := hx (t * s) a
    rw [mul_smul, hx] at h1
    simp only [smul_sub, Finset.sum_sub_distrib, h1, smul_smul]
    simp
  have hx0 : ∀ τ, τ (H.rt : E) ≠ ρ → x τ = 0 := fun τ hτ => by
    ext1 a
    have := eq_zero_of_sum_embedding_smul (fun τ => (τ (H.rt : E) - ρ) • x τ a) (fun t => by
      have h1 := hx (H.rt * t) a
      rw [mul_smul, hXrt, hx, Finset.smul_sum] at h1
      simp only [sub_smul, smul_sub, smul_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa [smul_smul, mul_comm] using h1.symm) τ
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hτ)
  have hc : (((hermForm H₀ w₀ w₀).re : ℝ) : ℂ) = hermForm H₀ w₀ w₀ :=
    Complex.conj_eq_iff_re.1 (EigenNorm.hermForm_conj H₀ hu₀.1 w₀ w₀).symm
  refine ⟨x, fun a => hsum a ▸ hXd a, hxs, hx0, ?_⟩
  rw [← hc]
  refine EigenNorm.hermForm_eigen E H P.g Hm hu.1 L h ρ _ x hρ hadd hsmul hsymm hxs hx0 fun a => ?_
  rw [hc, hsum]
  have haddr : ∀ a b c, h a (b + c) = h a b + h a c := fun a b c => by
    rw [hsymm (b + c) a, hsymm b a, hsymm c a, hadd, map_add]
  have key : ∀ a, ((∃ i, a = e i) ∨ ∃ i j, a = e i + e j) → hermForm Hm (X a) (X a) - hermForm H₀ w₀ w₀ *
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a a) = 0 := fun a ha => by
    obtain ⟨N, hN, hiso⟩ := hiso a ha
    have h1 := hermForm_pull_eq_of_lbIso_pow P₀.A P.A P₀.L P.L P₀.isLB P.isLB P₀.g P.g u₀ u H₀ χ₀ Hm χ hu₀ hu
      (φ a) (F a) (hF a) N (N * nn a) hiso w₀ w₀
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [← hnn, hX]
    apply mul_left_cancel₀ hN'
    push_cast at h1
    linear_combination h1
  exact sub_eq_zero.1 (quadratic_eq_zero (fun a b => hermForm Hm (X a) (X b) - hermForm H₀ w₀ w₀ *
      ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a b))
    (fun a b c => by
      simp only [map_add, EigenNorm.hermForm_add_left, hadd, Finset.sum_add_distrib]; ring)
    (fun a b c => by
      simp only [map_add, EigenNorm.hermForm_add_right, haddr, Finset.sum_add_distrib]; ring)
    e he (fun i => key _ (Or.inl ⟨i, rfl⟩)) (fun i j => key _ (Or.inr ⟨i, j, rfl⟩)) a)

end GlobalTheory.CMNormIdentity
