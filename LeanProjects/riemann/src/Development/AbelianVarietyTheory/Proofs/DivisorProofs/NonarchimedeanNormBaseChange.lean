import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompatStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.LocOrdUp

theorem exists_rightInverse {V K : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {m n : ℕ} (U : Matrix (Fin m) (Fin n) V)
    (h : ∀ (a : Fin n → V) (c : Fin m → K), c ᵥ* U.map (algebraMap V K) = (fun j => algebraMap V K (a j)) →
      ∃! b, b ᵥ* U = a) : ∃ R : Matrix (Fin n) (Fin m) V, U * R = 1 := by
  have inj : Function.Injective (Matrix.vecMulLinear U) := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun b hb => ?_)
    exact (h 0 0 (by ext j; simp)).unique hb (Matrix.zero_vecMul _)
  have tf : Module.IsTorsionFree V ((Fin n → V) ⧸ LinearMap.range (Matrix.vecMulLinear U)) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r y hy => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨b, hb⟩ := hy
    rw [or_iff_not_imp_left]
    intro hr
    rw [Submodule.Quotient.mk_eq_zero]
    have hr' : algebraMap V K r ≠ 0 := fun e => hr (IsFractionRing.injective V K (e.trans (map_zero _).symm))
    obtain ⟨b', hb', -⟩ := h a ((algebraMap V K r)⁻¹ • fun i => algebraMap V K (b i)) (by
      rw [Matrix.smul_vecMul]
      ext j
      have e : ((fun i => algebraMap V K (b i)) ᵥ* U.map (algebraMap V K)) j = algebraMap V K ((b ᵥ* U) j) :=
        (RingHom.map_vecMul (algebraMap V K) U b j).symm
      have e' : b ᵥ* U = r • a := hb
      rw [Pi.smul_apply, e, e', Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, inv_mul_cancel_left₀ hr'])
    exact ⟨b', hb'⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range (Matrix.vecMulLinear U)).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have ex : Function.Exact (Matrix.vecMulLinear U) (LinearMap.range (Matrix.vecMulLinear U)).mkQ :=
    LinearMap.exact_map_mkQ_range _
  have hs' : ∃ l, (LinearMap.range (Matrix.vecMulLinear U)).mkQ ∘ₗ l = LinearMap.id := ⟨s, hs⟩
  have hg' : ∃ l, l ∘ₗ Matrix.vecMulLinear U = LinearMap.id :=
    ((ex.split_tfae inj (Submodule.mkQ_surjective _)).out 0 1).1 hs'
  obtain ⟨g, hg⟩ := hg'
  refine ⟨LinearMap.toMatrixRight' g, ?_⟩
  apply Matrix.toLinearMapRight'.injective
  rw [Matrix.toLinearMapRight'_mul, Matrix.toLinearMapRight'_one]
  change Matrix.toLinearMapRight' (LinearMap.toMatrixRight' g) ∘ₗ Matrix.vecMulLinear U = _
  simpa using hg

theorem existsUnique_of_rightInverse {W L : Type} [CommRing W] [CommRing L] (φ : W →+* L) (hφ : Function.Injective φ)
    {m n : ℕ} {U : Matrix (Fin m) (Fin n) W} {R : Matrix (Fin n) (Fin m) W} (h : U * R = 1)
    (a : Fin n → W) (c : Fin m → L) (hc : c ᵥ* U.map φ = fun j => φ (a j)) : ∃! b, b ᵥ* U = a := by
  have h2 : U.map φ * R.map φ = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : c = fun i => φ ((a ᵥ* R) i) := by
    rw [← Matrix.vecMul_one c, ← h2, ← Matrix.vecMul_vecMul, hc]
    exact funext fun i => (RingHom.map_vecMul φ R a i).symm
  refine ⟨a ᵥ* R, funext fun j => hφ ?_, fun b hb => ?_⟩
  · rw [RingHom.map_vecMul, ← congrFun hc j, h3]; rfl
  · rw [← hb, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem isLocOrd_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (r : ℝ), Indep x → (∀ a, IsVecOver i n.φ (x a) (x' a)) → (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → EigenvectorLieDegree.IsLocOrd t.G x 𝔭 r → EigenvectorLieDegree.IsLocOrd t'.G x' 𝔓 (ε * r) := by
  intro E _ _ _ H k k' _ _ _ _ i t t' n m x x' 𝔭 𝔓 ε r hx hxx hval hr
  obtain ⟨V, K, _, _, _, _, _, _, em, e₀, G, _, A, _, φ, ψ, v, u, u', M, ν, he₀, hv, hG, hφ, hψ, hxv, hu, hb, hM, hν,
    rfl⟩ := hr
  obtain ⟨W, L, _, _, _, _, _, _, f, g, em', e₂, d, hfg, hem, he₂, hd, hv', hvg⟩ :=
    GlobalTheory.T.ramification_index_valuation_compat k k' i 𝔭 𝔓 ε V K em e₀ hval he₀ hv
  have hf' : (algebraMap W L).comp f = g.comp (algebraMap V K) := RingHom.ext hfg
  obtain ⟨G₁, _, χ, h', hG₁⟩ : ∃ (G₁ : Over (Sp W)) (_ : GrpObj G₁) (χ : G₁.left ⟶ G.left),
      IsGrpPullback G₁ G (spMap f) χ ∧ IsSemiAbelian G₁ :=
    ⟨_, _, _, isGrpPullback_pullback G (spMap f), IsSemiAbelian.pullback _ G hG⟩
  obtain ⟨A₁, _, ω, hω⟩ : ∃ (A₁ : Over (Sp L)) (_ : GrpObj A₁) (ω : A₁.left ⟶ A.left),
      IsGrpPullback A₁ A (spMap g) ω := ⟨_, _, _, isGrpPullback_pullback A (spMap g)⟩
  have := hG.comm
  have := hG₁.comm
  have := hG.smooth
  have := hG₁.smooth
  have := PolPull.isCommMonObj_of_isGrpPullback hφ
  have := PolPull.isCommMonObj_of_isGrpPullback hω
  have n' : IsGrpPullback A₁ G (spMap (algebraMap W L) ≫ spMap f) (ω ≫ φ) :=
    (hω.comp hφ).congr (by rw [spMap_comp_spMap, spMap_comp_spMap, hf']) rfl
  have w : (ω ≫ φ) ≫ G.hom = (A₁.hom ≫ spMap (algebraMap W L)) ≫ spMap f :=
    n'.1.w.trans (Category.assoc _ _ _).symm
  have q := h'.1.lift_fst _ _ w
  have hφ₁ := h'.cancel (n'.congr rfl q.symm) (h'.1.lift_snd _ _ w)
  have n'' : IsGrpPullback A₁ t.G (spMap em' ≫ spMap i) (ω ≫ ψ) :=
    (hω.comp hψ).congr (by rw [spMap_comp_spMap, spMap_comp_spMap, hem]) rfl
  have w' : (ω ≫ ψ) ≫ t.G.hom = (A₁.hom ≫ spMap em') ≫ spMap i :=
    n''.1.w.trans (Category.assoc _ _ _).symm
  have q' := n.cart.1.lift_fst _ _ w'
  have hψ₁ := n.cart.cancel (n''.congr rfl q'.symm) (n.cart.1.lift_snd _ _ w')
  have tv : ∀ a, IsTangent (v a) := fun a => (hxv a).isTangent hψ (hx.1 a)
  obtain ⟨N, e, e', -, he, he', h, -⟩ := exists_frame hG hφ tv
  choose e₁ h₁ _ using fun j => existsUnique_isVecOver h'.1 (e j)
  have he₁ := Chart.isLieBasis_baseChange f h' he h₁
  choose e₁' h₂ _ using fun j => existsUnique_isVecOver hω.1 (e' j)
  have h₃ := fun j => EllComp.isVecOver_cancel h'.1 hφ₁.1 (h₁ j)
    (by rw [q, hf']; exact EllComp.isVecOver_comp (h j) (h₂ j))
  have he₁' := Chart.isLieBasis_baseChange _ hφ₁ he₁ h₃
  choose u₁ k₁ _ using fun j => existsUnique_isVecOver h'.1 (u j)
  choose u₁' k₂ _ using fun j => existsUnique_isVecOver hω.1 (u' j)
  have k₃ := fun j => EllComp.isVecOver_cancel h'.1 hφ₁.1 (k₁ j)
    (by rw [q, hf']; exact EllComp.isVecOver_comp (hu j).2.1 (k₂ j))
  choose v₁ l₂ _ using fun j => existsUnique_isVecOver hω.1 (v j)
  have l₃ := fun j => EllComp.isVecOver_cancel n.cart.1 hψ₁.1 (hxx j)
    (by rw [q', hem]; exact EllComp.isVecOver_comp (hxv j) (l₂ j))
  choose U₀ hU₀ _ using fun a => he.2 _ (hu a).1
  let U : Matrix (Fin m) (Fin N) V := U₀
  have hU : ∀ a, IsLieComb (U a) e (u a) := hU₀
  have hU' : ∀ a, IsLieComb (U.map (algebraMap V K) a) e' (u' a) := fun a =>
    (lieComb_baseChange _ _ _ G A φ hφ N e (u a) (U a) e' (u' a) h (hU a)).1 (hu a).2.1
  have hU₁ : ∀ a, IsLieComb (U.map f a) e₁ (u₁ a) := fun a =>
    (lieComb_baseChange _ _ _ G G₁ χ h' N e (u a) (U a) e₁ (u₁ a) h₁ (hU a)).1 (k₁ a)
  have hU₁' : ∀ a, IsLieComb ((U.map f).map (algebraMap W L) a) e₁' (u₁' a) := fun a =>
    (lieComb_baseChange _ _ _ G₁ A₁ _ hφ₁ N e₁ (u₁ a) (U.map f a) e₁' (u₁' a) h₃ (hU₁ a)).1 (k₃ a)
  choose C₀ hC₀ using fun a => (hu a).2.2
  let C : Matrix (Fin m) (Fin m) K := C₀
  have hC : ∀ a, IsLieComb (C a) v (u' a) := hC₀
  have hM₁ : ∀ a, IsLieComb (M.map g a) u₁' (v₁ a) := fun a =>
    (lieComb_baseChange _ _ g A A₁ ω hω m u' (v a) (M a) u₁' (v₁ a) k₂ (hM a)).1 (l₂ a)
  have tu₁ : ∀ a, IsTangent (u₁ a) := fun a => (k₁ a).isTangent h' (hu a).1
  have tu₁' : ∀ a, IsTangent (u₁' a) := fun a => (k₃ a).isTangent hφ₁ (tu₁ a)
  obtain ⟨R, hR⟩ := exists_rightInverse (K := K) U fun a c hc => by
    obtain ⟨a₁, a₂, -⟩ := LieComb.lieComb_algebra _ G N e he.1
    obtain ⟨y, hy⟩ := (a₁ a).exists
    obtain ⟨z, hz, -⟩ := existsUnique_isVecOver hφ.1 y
    have hz' := (lieComb_baseChange _ _ _ G A φ hφ N e y a e' z h hy).1 hz
    rw [← hc, ← comb_comb he'.1 hU', comb_comb tv hC] at hz'
    refine (existsUnique_congr fun b => ?_).1 (hb y z (a₂ _ _ hy) hz ⟨_, hz'⟩)
    rw [comb_comb he.1 hU]
    exact ⟨fun hb => (Indep.of_basis he).2 _ _ y hb hy, fun hb => hb ▸ hy⟩
  have hR₁ : U.map f * R.map f = 1 := by
    rw [← Matrix.map_mul, hR, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨W, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, em', _,
    G₁, inferInstance, A₁, inferInstance, _, _, v₁, u₁, u₁', M.map g, d * ν, he₂, hv', hG₁, hφ₁, hψ₁, l₃,
    fun a => ⟨tu₁ a, k₃ a, _, (lieComb_baseChange _ _ g A A₁ ω hω m v (u' a) (C a) v₁ (u₁' a) l₂ (hC a)).1 (k₂ a)⟩,
    fun y z hy hz ⟨c, hc⟩ => ?_, hM₁, ?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := he₁.2 y hy
    have hz' := (lieComb_baseChange _ _ _ G₁ A₁ _ hφ₁ N e₁ y a e₁' z h₃ ha).1 hz
    rw [comb_comb tu₁' hM₁, comb_comb he₁'.1 hU₁'] at hc
    refine (existsUnique_congr fun b => ?_).1 (existsUnique_of_rightInverse (algebraMap W L)
      (IsFractionRing.injective W L) hR₁ a _ ((Indep.of_basis he₁').2 _ _ z hc hz'))
    rw [comb_comb he₁.1 hU₁]
    exact ⟨fun hb => hb ▸ ha, fun hb => (Indep.of_basis he₁).2 _ _ y hb ha⟩
  · have : (M.map g).det = g M.det := (RingHom.map_det g M).symm
    rw [this, hvg, hν, ← WithZero.exp_nsmul]
    congr 1
    simp
  · have a₁ : (e₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he₀.ne'
    have a₃ := congrArg (Nat.cast : ℕ → ℝ) hd
    have a₂ : (e₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he₂.ne'
    push_cast at a₃ ⊢
    rw [← mul_div_assoc, div_eq_div_iff a₁ a₂]
    linear_combination (ν : ℝ) * a₃

end GlobalTheory.LocOrdUp
