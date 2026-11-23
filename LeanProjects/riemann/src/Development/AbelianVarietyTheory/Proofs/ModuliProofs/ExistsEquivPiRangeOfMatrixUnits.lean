import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_equiv_pi_range_of_matrixUnits {R M n : Type} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype n] [DecidableEq n] (p q : n → M →ₗ[R] M) (P : M →ₗ[R] M)
    (hpq : ∀ u v x, p u (q v x) = if u = v then P x else 0)
    (hs : ∀ x, ∑ u, q u (p u x) = x) (hP : ∀ x, P (P x) = P x) :
    ∃ φ : M ≃ₗ[R] (n → LinearMap.range P), (∀ x u, (φ x u : M) = p u x) ∧
      ∀ x, x = ∑ u, q u (φ x u) := by
  have hmem : ∀ u x, p u x ∈ LinearMap.range P := fun u x => by
    refine ⟨p u x, ?_⟩
    conv_rhs => rw [← hs x]
    simp [map_sum, hpq]
  let f : M →ₗ[R] (n → LinearMap.range P) :=
    LinearMap.pi fun u => (p u).codRestrict _ (hmem u)
  have hf : ∀ x u, (f x u : M) = p u x := fun _ _ => rfl
  have hb : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ⟨∑ v, q v (y v), ?_⟩⟩
    · rw [← hs x]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [← hf, hx]; simp
    · funext u
      apply Subtype.ext
      rw [hf]
      obtain ⟨z, hz⟩ := (y u).2
      simp only [map_sum, hpq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← hz, hP]
  exact ⟨LinearEquiv.ofBijective f hb, hf, fun x => (hs x).symm⟩

theorem matrixUnits_apply {La : Type} [AddCommGroup La]
    (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La) :
    (∀ u v x, r (Matrix.single 0 u 1) (r (Matrix.single v 0 1) x) =
      if u = v then r (Matrix.single 0 0 1) x else 0) ∧
    (∀ x, ∑ u, r (Matrix.single u 0 1) (r (Matrix.single 0 u 1) x) = x) ∧
    (∀ x, r (Matrix.single 0 0 1) (r (Matrix.single 0 0 1) x) = r (Matrix.single 0 0 1) x) := by
  refine ⟨fun u v x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [← Module.End.mul_apply, ← map_mul]
    split_ifs with huv
    · subst huv; simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ huv]; simp
  · have : (∑ u : Fin 8, Matrix.single u 0 (1:ℤ) * Matrix.single (0 : Fin 8) u (1:ℤ)) = 1 := by
      ext i j
      simp only [Matrix.single_mul_single_same, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, mul_one]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij]
        refine Finset.sum_eq_zero fun u _ => if_neg ?_
        rintro ⟨rfl, rfl⟩; exact hij rfl
    simp only [← Module.End.mul_apply, ← map_mul]
    rw [← LinearMap.sum_apply, ← map_sum, this]; simp
  · rw [← Module.End.mul_apply, ← map_mul]; simp

theorem form_matrixUnits_eq {La : Type} [AddCommGroup La] (G : Matrix (Fin 8) (Fin 8) ℤ)
    (EF : LinearMap.BilinForm ℤ La) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La)
    (hdet : G.det = 1)
    (hadj : ∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) (u v : Fin 8)
    (x y : La) : EF (r (Matrix.single u 0 1) x) (r (Matrix.single v 0 1) y) =
      G u v * EF x (r (G⁻¹ * Matrix.single 0 0 1) y) := by
  have hu : IsUnit G.det := by simp [hdet]
  rw [hadj _ (G⁻¹ * ((Matrix.single u 0 1).transpose * G))
    (by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]),
    ← Module.End.mul_apply, ← map_mul]
  have : G⁻¹ * ((Matrix.single u (0 : Fin 8) (1:ℤ)).transpose * G) * Matrix.single v (0 : Fin 8) (1:ℤ) =
      G u v • (G⁻¹ * Matrix.single 0 0 1) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_smul, Matrix.transpose_single, Matrix.single_mul_mul_single]
    simp
  rw [this, map_zsmul]
  simp

theorem hermForm_pullback {g h : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (J : Matrix (Fin g) (Fin h) ℂ)
    (c : ℂ) (z w : Fin h → ℂ) :
    hermForm (c • (J.transpose * Hm * J.map star)) z w = c * hermForm Hm (J.mulVec z) (J.mulVec w) := by
  have : star (J.mulVec w) = (J.map star).mulVec (star w) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  simp only [hermForm, this, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose]

theorem exists_form_range_matrixUnit {La : Type} [AddCommGroup La] (G : Matrix (Fin 8) (Fin 8) ℤ)
    (EF : LinearMap.BilinForm ℤ La) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La)
    (hG : G 0 0 ≠ 0) (hdet : G.det = 1) (hb : Function.Bijective EF) (halt : ∀ x, EF x x = 0)
    (hadj : ∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) :
    ∃ (φ : La ≃ₗ[ℤ] (Fin 8 → LinearMap.range (r (Matrix.single 0 0 1))))
      (E : LinearMap.BilinForm ℤ (LinearMap.range (r (Matrix.single 0 0 1)))),
      (∀ x u, (φ x u : La) = r (Matrix.single 0 u 1) x) ∧ Function.Bijective E ∧ (∀ x, E x x = 0) ∧
      (∀ x y, EF x y = ∑ u, ∑ v, G u v * E (φ x u) (φ y v)) ∧
      ∀ x y : LinearMap.range (r (Matrix.single 0 0 1)), EF x y = G 0 0 * E x y := by
  obtain ⟨h1, h2, h3⟩ := matrixUnits_apply r
  obtain ⟨φ, hφ, hφ'⟩ := exists_equiv_pi_range_of_matrixUnits (fun u => r (Matrix.single 0 u 1))
    (fun u => r (Matrix.single u 0 1)) (r (Matrix.single 0 0 1)) h1 h2 h3
  have hu : IsUnit G.det := by simp [hdet]
  let E : LinearMap.BilinForm ℤ (LinearMap.range (r (Matrix.single 0 0 1))) :=
    EF.compl₁₂ (Submodule.subtype _) (r (G⁻¹ * Matrix.single 0 0 1) ∘ₗ Submodule.subtype _)
  have hE : ∀ x y, E x y = EF x (r (G⁻¹ * Matrix.single 0 0 1) y) := fun _ _ => rfl
  have hsum : ∀ x y, EF x y = ∑ u, ∑ v, G u v * E (φ x u) (φ y v) := fun x y => by
    conv_lhs => rw [hφ' x, hφ' y]
    simp only [map_sum, LinearMap.sum_apply, form_matrixUnits_eq G EF r hdet hadj, hE]
    rw [Finset.sum_comm]
  have hfix : ∀ x : LinearMap.range (r (Matrix.single 0 0 1)), r (Matrix.single 0 0 1) x = x := by
    rintro ⟨_, z, rfl⟩; exact h3 z
  have h00 : ∀ x y : LinearMap.range (r (Matrix.single 0 0 1)), EF x y = G 0 0 * E x y :=
    fun x y => by
      rw [hE, ← form_matrixUnits_eq G EF r hdet hadj, hfix, hfix]
  refine ⟨φ, E, hφ, ⟨(injective_iff_map_eq_zero E).2 fun x hx => ?_, fun f => ?_⟩, fun x => ?_,
    hsum, h00⟩
  · have : EF (φ.symm (Pi.single 0 x)) = 0 := by
      ext y
      rw [hsum]
      refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
      rw [LinearEquiv.apply_symm_apply]
      by_cases h : u = 0
      · subst h; simp [hx]
      · simp [h]
    have h0 := (injective_iff_map_eq_zero EF).1 hb.1 _ this
    have := congrFun (φ.symm.map_eq_zero_iff.1 h0) 0
    simpa using this
  · obtain ⟨x, hx⟩ := hb.2 (∑ v, G 0 v • (f ∘ₗ LinearMap.proj v ∘ₗ φ.toLinearMap))
    refine ⟨φ x 0, LinearMap.ext fun y => ?_⟩
    have key : ∀ v, ∑ u, E (φ x u) y * G u v = f y * G 0 v := fun v => by
      have := LinearMap.congr_fun hx (φ.symm (Pi.single v y))
      rw [hsum] at this
      simpa [Pi.single_apply, apply_ite, mul_comm] using this
    have k2 : Matrix.vecMul (fun u => E (φ x u) y) G = Matrix.vecMul (Pi.single 0 (f y)) G := by
      funext v
      rw [Matrix.single_vecMul]
      exact key v
    have k3 := congrArg (fun w => Matrix.vecMul w G⁻¹ 0) k2
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] at k3
    simpa using k3
  · have := h00 x x
    rw [halt] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hG

theorem polarised_lattice_eighth_power :
    ∀ (h g : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) (σ : Fin 8 × Fin h ≃ Fin g) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La), G.IsSymm → (G.map (Int.cast : ℤ → ℝ)).PosDef → G.det = 1 → Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ a, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (r a x)) → (∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (e : La ≃+ (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (hh : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (τ).IsSymm ∧ ((τ).map Complex.im).PosDef ∧ (∀ x u i, hh (Q x) (σ (u, i)) = τ.mulVec (fun i' => (e x u (.inl i') : ℂ)) i + (e x u (.inr i) : ℂ)) ∧ (∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (e x u) (e y v)) ∧ ∀ a x u, e (r a x) u = ∑ v, a u v • e x v := by
  intro h g G σ La _ EF Q Hm r _ hpos hdet hb hQ hF hadj
  obtain ⟨hfree, hfin, hrk, halt⟩ :=
    unimodular_symplectic_coordinates_and_lattice_rank.2 La EF g Q Hm hQ
  obtain ⟨hinj, hdisc, hspan, hherm, hHpos, hIm⟩ := hQ
  have hg : g = 8 * h := by simpa using (Fintype.card_congr σ).symm
  have hG : (0 : ℤ) < G 0 0 := by
    have := hpos.diag_pos (i := 0)
    simpa using this
  obtain ⟨φ, E, hφ, hEb, hEalt, hsum, h00⟩ :=
    exists_form_range_matrixUnit G EF r hG.ne' hdet hb halt hadj
  have hrk0 : Module.finrank ℤ (LinearMap.range (r (Matrix.single 0 0 1))) = 2 * h := by
    have := φ.finrank_eq
    rw [hrk, Module.finrank_pi_fintype] at this
    simp at this
    omega
  obtain ⟨bas, hbas⟩ := unimodular_symplectic_coordinates_and_lattice_rank.1 _ E h hEb hEalt hrk0
  choose F hF using hF
  have hspanC : Submodule.span ℂ (Set.range Q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    exact Submodule.span_subset_span ℝ ℂ _ (hspan ▸ Submodule.mem_top)
  obtain ⟨h1, h2, h3⟩ := matrixUnits_apply r
  obtain ⟨ψ, hψ, -⟩ := exists_equiv_pi_range_of_matrixUnits (fun u => F (Matrix.single 0 u 1))
    (fun u => F (Matrix.single u 0 1)) (F (Matrix.single 0 0 1))
    (fun u v => by
      have : F (Matrix.single 0 u 1) ∘ₗ F (Matrix.single v 0 1) =
          if u = v then F (Matrix.single 0 0 1) else 0 := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        simp only [LinearMap.comp_apply, hF, h1]
        split_ifs <;> simp [hF]
      intro x
      have := LinearMap.congr_fun this x
      rw [LinearMap.comp_apply] at this
      rw [this]; split_ifs <;> simp)
    (fun z => by
      have : ∑ u, F (Matrix.single u 0 1) ∘ₗ F (Matrix.single 0 u 1) = LinearMap.id := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, hF, ← map_sum, h2, LinearMap.id_apply]
      simpa using LinearMap.congr_fun this z)
    (fun z => by
      have : F (Matrix.single 0 0 1) ∘ₗ F (Matrix.single 0 0 1) = F (Matrix.single 0 0 1) := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        simp only [LinearMap.comp_apply, hF, h3]
      exact LinearMap.congr_fun this z)
  have hdim : Module.finrank ℂ (Fin h → ℂ) =
      Module.finrank ℂ (LinearMap.range (F (Matrix.single 0 0 1))) := by
    have := ψ.finrank_eq
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at this
    simp at this
    simp
    omega
  let j := LinearEquiv.ofFinrankEq _ _ hdim
  let T : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ) :=
    j.symm.toLinearMap ∘ₗ (F (Matrix.single 0 0 1)).rangeRestrict
  let Jl : (Fin h → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Submodule.subtype _ ∘ₗ j.toLinearMap
  have hJT : ∀ z, Jl (T z) = F (Matrix.single 0 0 1) z := fun z => by simp [Jl, T]
  have hJinj : Function.Injective Jl := Subtype.val_injective.comp j.injective
  have hTs : Function.Surjective T :=
    j.symm.surjective.comp (F (Matrix.single 0 0 1)).surjective_rangeRestrict
  let Q₀ : LinearMap.range (r (Matrix.single 0 0 1)) →+ (Fin h → ℂ) :=
    T.toAddMonoidHom.comp (Q.comp (Submodule.subtype _).toAddMonoidHom)
  have hQ₀ : ∀ x, Jl (Q₀ x) = Q x := by
    rintro ⟨_, z, rfl⟩
    change Jl (T (Q _)) = _
    rw [hJT, hF]
    exact congrArg Q (h3 z)
  let J := LinearMap.toMatrix' Jl
  have hJ : ∀ z, J.mulVec z = Jl z := fun z => LinearMap.toMatrix'_mulVec _ _
  have hGR : (0 : ℝ) < G 0 0 := by exact_mod_cast hG
  obtain ⟨m, τ, hm, -, -, hτs, hτp, -, hτ⟩ := GlobalTheory.SiegelPeriod.exists_siegel_form _ E h bas Q₀
    ((((G 0 0 : ℝ)⁻¹ : ℝ) : ℂ) • (J.transpose * Hm * J.map star)) hbas
    ⟨fun x y hxy => Subtype.ext (hinj (by rw [← hQ₀, ← hQ₀, hxy])),
      by
        let f : Q₀.range → Q.range := fun z => ⟨Jl z, by
          obtain ⟨x, hx⟩ := z.2
          exact ⟨x, by rw [← hx, hQ₀]⟩⟩
        exact DiscreteTopology.of_continuous_injective (f := f)
          ((Jl.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _)
          fun a b hab => Subtype.ext (hJinj (congrArg (fun z : Q.range => (z : Fin g → ℂ)) hab)),
      by
        rw [eq_top_iff]
        intro z _
        obtain ⟨w, rfl⟩ := hTs z
        have hw : w ∈ Submodule.span ℝ (Set.range Q) := hspan ▸ Submodule.mem_top
        refine Submodule.span_mono ?_
          (Submodule.apply_mem_span_image_of_mem_span (T.restrictScalars ℝ) hw)
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        refine ⟨⟨_, x, rfl⟩, hJinj ?_⟩
        rw [hQ₀, LinearMap.restrictScalars_apply, hJT, hF],
      by
        have e1 : J.map star = J.transpose.conjTranspose := by ext; simp
        rw [e1]
        have := Matrix.isHermitian_mul_mul_conjTranspose J.transpose hherm
        unfold Matrix.IsHermitian at this ⊢
        rw [Matrix.conjTranspose_smul, this]; simp,
      fun z hz => by
        rw [hermForm_pullback, Complex.re_ofReal_mul, hJ]
        exact mul_pos (inv_pos.2 hGR) (hHpos _ fun h0 => hz (hJinj (by rw [h0, map_zero]))),
      fun x y => by
        rw [hermForm_pullback, Complex.im_ofReal_mul, hJ, hJ, hQ₀, hQ₀, hIm, h00]
        push_cast
        field_simp⟩
  let mE : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ) := Matrix.toLinearEquiv' m hm.invertible
  have hmE : ∀ z, mE z = m.mulVec z := fun _ => rfl
  let e : La ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    φ ≪≫ₗ LinearEquiv.piCongrRight fun _ => bas.symm
  have he : ∀ x u, e x u = bas.symm (φ x u) := fun _ _ => rfl
  let hh : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    ψ ≪≫ₗ (LinearEquiv.piCongrRight fun _ => j.symm ≪≫ₗ mE) ≪≫ₗ
      (LinearEquiv.curry ℂ ℂ (Fin 8) (Fin h)).symm ≪≫ₗ LinearEquiv.funCongrLeft ℂ ℂ σ.symm
  have hhh : ∀ z u i, hh z (σ (u, i)) = m.mulVec (j.symm (ψ z u)) i := fun z u i => by
    simp [hh, hmE]
  refine ⟨τ, e.toAddEquiv, hh, hτs, hτp, fun x u i => ?_, fun x y => ?_, fun a x u => ?_⟩
  · have e1 : j.symm (ψ (Q x) u) = Q₀ (bas (e x u)) := by
      apply hJinj
      rw [hQ₀, he, LinearEquiv.apply_symm_apply, hφ, ← hF, ← hψ]
      simp [Jl]
    rw [hhh, e1, hτ]
    rfl
  · rw [hsum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    change G u v * E (φ x u) (φ y v) = G u v * omegaStd (bas.symm (φ x u)) (bas.symm (φ y v))
    rw [← hbas, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · change bas.symm (φ (r a x) u) = ∑ v, a u v • bas.symm (φ x v)
    simp only [← map_smul, ← map_sum]
    refine congrArg bas.symm (Subtype.ext ?_)
    have : Matrix.single (0 : Fin 8) u (1 : ℤ) * a = ∑ v, a u v • Matrix.single (0 : Fin 8) v (1 : ℤ) := by
      ext i k
      by_cases hi : i = 0
      · subst hi; simp [Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.sum_apply, Matrix.single_apply, hi, Ne.symm hi]
    rw [hφ, ← Module.End.mul_apply, ← map_mul, this, map_sum, LinearMap.sum_apply,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, Submodule.coe_smul, hφ]

end GlobalTheory
