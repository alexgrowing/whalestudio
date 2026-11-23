import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodThetaClassOfLatticeFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpClassPrimitiveIsoClosedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsEighthPowerEvenUnimodularBundleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveTensorOmegaStd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenPosDefOfContinuous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpGood

theorem exists_representatives {α β : Type} [Finite β] (f : α → β) (P : α → Prop) :
    ∃ (r : ℕ) (s : Fin r → α), (∀ i, P (s i)) ∧ ∀ x, P x → ∃ i, f x = f (s i) := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin {y : β // ∃ x, P x ∧ f x = y}
  refine ⟨r, fun i => (e.symm i).2.choose, fun i => (e.symm i).2.choose_spec.1, fun x hx => ?_⟩
  refine ⟨e ⟨f x, x, hx, rfl⟩, ?_⟩
  rw [(e.symm (e ⟨f x, x, hx, rfl⟩)).2.choose_spec.2, Equiv.symm_apply_apply]

theorem exists_hom_representatives {ν : Type} [Fintype ν] (k : ℕ) (hk : k ≠ 0)
    (P : ((ν → ℤ) →+ (ν → ℤ)) → Prop) :
    ∃ (r : ℕ) (s : Fin r → ((ν → ℤ) →+ (ν → ℤ))), (∀ i, P (s i)) ∧
      ∀ m, P m → ∃ i, ∀ x, ∃ y, m x = s i x + k • y := by
  classical
  haveI : NeZero k := ⟨hk⟩
  obtain ⟨r, s, hs, hm⟩ := exists_representatives
    (fun (m : (ν → ℤ) →+ (ν → ℤ)) (p q : ν) => ((m (Pi.single p 1) q : ℤ) : ZMod k)) P
  refine ⟨r, s, hs, fun m hP => ?_⟩
  obtain ⟨i, hi⟩ := hm m hP
  refine ⟨i, fun x => ?_⟩
  have hx : x = ∑ p, x p • (Pi.single p 1 : ν → ℤ) := by
    ext q; simp [Finset.sum_apply, Pi.single_apply]
  have key : ∀ q, ((m x q : ℤ) : ZMod k) = ((s i x q : ℤ) : ZMod k) := by
    intro q
    rw [hx, map_sum, map_sum]
    simp only [map_zsmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [congrFun (congrFun hi p) q]
  have key' : ∀ q, ∃ c : ℤ, m x q - s i x q = k * c := fun q =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (key q).symm
  choose y hy using key'
  refine ⟨y, funext fun q => ?_⟩
  have := hy q
  rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
  linarith

theorem zpow_finset_sum {ν : Type} (q : ℂ) (hq : q ≠ 0) (s : Finset ν) (f : ν → ℤ) :
    q ^ (∑ i ∈ s, f i) = ∏ i ∈ s, q ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq, ih]

theorem exp_sum_eq (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (G p q : Fin 8 → Fin 8 → ℤ)
    (hpq : ∀ u v, Complex.exp (-(2 * Real.pi * Complex.I) * (p u v : ℂ) / k) = ζ ^ q u v) :
    Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ u, ∑ v, G u v * p u v : ℤ) : ℂ) / k)
      = ζ ^ (∑ u, ∑ v, G u v * q u v) := by
  have h1 : ∀ n : ℤ, Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)
      = Complex.exp (-(2 * Real.pi * Complex.I) / k) ^ n := by
    intro n
    rw [← Complex.exp_int_mul]; congr 1; ring
  rw [h1, zpow_finset_sum _ (Complex.exp_ne_zero _), zpow_finset_sum _ hζ]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [zpow_finset_sum _ (Complex.exp_ne_zero _), zpow_finset_sum _ hζ]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [mul_comm (G u v), mul_comm (G u v), zpow_mul, zpow_mul, ← h1, hpq]

def omegaBil (h : ℕ) : LinearMap.BilinForm ℤ (Fin h ⊕ Fin h → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y => omegaStd x y)
    (fun x x' y => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

theorem omegaBil_apply {h : ℕ} (x y : Fin h ⊕ Fin h → ℤ) : omegaBil h x y = omegaStd x y := rfl

theorem exists_tensor_form (h : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) :
    ∃ EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ)),
      ∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v) := by
  refine ⟨∑ u, ∑ v, G u v • (omegaBil h).compl₁₂ (LinearMap.proj u) (LinearMap.proj v), fun x y => ?_⟩
  simp [LinearMap.sum_apply, omegaBil_apply]

theorem tensor_form_adjoint {h : ℕ} (G A A' : Matrix (Fin 8) (Fin 8) ℤ)
    (hA : A.transpose * G = G * A') (x y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, G u v * omegaStd (∑ s, A u s • x s) (y v)
      = ∑ u, ∑ v, G u v * omegaStd (x u) (∑ s, A' v s • y s) := by
  have h1 : ∑ u, ∑ v, G u v * omegaStd (∑ s, A u s • x s) (y v)
      = ∑ s, ∑ v, (A.transpose * G) s v * omegaStd (x s) (y v) := by
    simp only [← omegaBil_apply, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
      smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => by ring
  have h2 : ∑ u, ∑ v, G u v * omegaStd (x u) (∑ s, A' v s • y s)
      = ∑ u, ∑ s, (G * A') u s * omegaStd (x u) (y s) := by
    simp only [← omegaBil_apply, map_sum, map_zsmul,
      smul_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun v _ => by ring
  rw [h1, h2, hA]

theorem nonempty_index_equiv {h g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) :
    Nonempty (Fin 8 × Fin h ≃ Fin g) := by
  have := bas.finrank_eq
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at this
  simp at this
  refine ⟨Fintype.equivOfCardEq ?_⟩
  simp; omega

theorem action_on_basis {h g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (A : Matrix (Fin 8) (Fin 8) ℤ)
    (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (i : Fin (2 * g)) :
    (fun u => ∑ v, A u v • m (bas (Pi.single i 1) v))
      = ∑ i', bas.symm (fun u => ∑ v, A u v • bas (Pi.single i 1) v) i' •
          (fun u => m (bas (Pi.single i' 1) u)) := by
  set z := bas.symm (fun u => ∑ v, A u v • bas (Pi.single i 1) v) with hz
  have hx : z = ∑ p, z p • (Pi.single p 1 : Fin (2 * g) → ℤ) := by
    ext q; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : (fun u => ∑ v, A u v • bas (Pi.single i 1) v) = ∑ p, z p • bas (Pi.single p 1) := by
    have : bas z = (fun u => ∑ v, A u v • bas (Pi.single i 1) v) := by
      rw [hz, LinearEquiv.apply_symm_apply]
    rw [← this]
    conv_lhs => rw [hx]
    simp only [map_sum, map_zsmul]
  funext u
  have h2 := congrArg m (congrFun h1 u)
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul] at h2 ⊢
  exact h2

theorem goodClass_sharpClass : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), GoodClass em (SharpClass (b := b) W a bas em) Mat κ w w' (h * (h + 1) / 2) := by
  intro L₁ L₂ hgen hunif h g W J _ a w w' bas hE hbas hw hw' _
  classical
  obtain ⟨σ⟩ := nonempty_index_equiv bas
  obtain ⟨EF, hEF⟩ := exists_tensor_form h (W + W.transpose)
  have hGs : (W + W.transpose).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  obtain ⟨hbij, hdom, hinj, hκ⟩ :=
    GlobalTheory.TensorSiegel.tensor_siegel_lattices h g (W + W.transpose) σ EF hGs hE.1 hE.2 hEF
  choose κ₀ hκ₀ using hκ
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, ∀ j, κ₀ (a j) ≤ κ :=
    (Set.finite_range fun j => κ₀ (a j)).bddAbove.imp fun κ hκ j => hκ ⟨j, rfl⟩
  obtain ⟨B, τ, hBo, hBc, hτd, hτ, hτs⟩ := GlobalTheory.exists_siegel_coordinates h
  have hQ : ∀ bb, ∃ (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ))
      (Hm : Matrix (Fin g) (Fin g) ℂ), bb ∈ B →
      (∀ x u i, Q x (σ (u, i)) = (τ bb).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧
      (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧
        (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
        ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) := by
    intro bb
    by_cases hb : bb ∈ B
    · obtain ⟨Q, Hm, hh⟩ := hdom (τ bb) (hτ bb hb)
      exact ⟨Q, Hm, fun _ => hh⟩
    · exact ⟨0, 0, fun hb' => absurd hb' hb⟩
  choose Q Hm hQ using hQ
  have hsum : a w + a w' = 1 := by
    have hu : IsUnit (W + W.transpose) := by
      rw [Matrix.isUnit_iff_isUnit_det, hE.2]; exact isUnit_one
    apply hu.mul_left_cancel
    rw [_root_.mul_add, hw, hw', _root_.mul_one]
  have hadj : (a w).transpose * (W + W.transpose) = (W + W.transpose) * a w' := by
    rw [hw']
    conv_rhs => rw [← hw]
    rw [Matrix.transpose_mul, hGs.eq]
  refine ⟨fun j => Matrix.of fun i' i =>
    bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i', κ, fun n hn hodd => ?_⟩
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.goodThetaClass_of_lattice_families L₁ L₂ hgen hunif g J (fun j => Matrix.of fun i' i =>
    bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i') κ n w w' hn hodd
  refine ⟨j₀, fun j hj N' hN o _ b em => ?_⟩
  have hk : N' ^ 2 ≠ 0 := by
    rw [hN]; exact pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hζ : em (b.ζ : o) ≠ 0 := (b.ζ.isUnit.map em).ne_zero
  obtain ⟨r, ms, hms, hrep⟩ := exists_hom_representatives (ν := Fin h ⊕ Fin h) (N' ^ 2) hk
    (fun m => ∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ)
      / ((N' ^ 2 : ℕ) : ℂ)) = em (b.ζ : o) ^ omegaStd x y)
  refine hj₀ j hj N' hN o b em _ _ r (fun _ => Fin 8 → (Fin h ⊕ Fin h → ℤ)) (fun _ => EF)
    (fun p i u => ms p (bas (Pi.single i 1) u)) (fun _ j x u => ∑ v, a j u v • x v)
    (fun _ => B) (fun _ => Q) (fun _ => Hm) ?_ ?_ ?_ ?_
  · exact fun t t' ht hm => (GlobalTheory.T.sharpClass_prim_and_closed_under_tMap hgen o g _ J b em w w' h W a bas t ht).2 t' hm
  · exact fun t ht => (GlobalTheory.T.sharpClass_prim_and_closed_under_tMap hgen o g _ J b em w w' h W a bas t ht).1 hE hw hw'
  · intro p
    refine ⟨hbij, hBo, hBc.isPreconnected, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      refine differentiableOn_pi.2 fun c => ?_
      obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective c
      refine DifferentiableOn.congr
        (f := fun bb => ∑ i', τ bb i i' * (x u (.inl i') : ℂ) + (x u (.inr i) : ℂ)) ?_ ?_
      · refine Differentiable.differentiableOn ?_
        exact (Differentiable.fun_sum fun i' _ => (hτd i i').mul_const _).add_const _
      · intro bb hb
        exact (hQ bb hb).1 x u i
    · intro x
      funext u
      have h1 : ∀ v, a w u v + a w' u v = (1 : Matrix (Fin 8) (Fin 8) ℤ) u v := fun v => by
        rw [← hsum]; rfl
      show ∑ v, a w u v • x v + ∑ v, a w' u v • x v = x u
      rw [← Finset.sum_add_distrib]
      simp only [← add_smul, h1, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · intro x y
      rw [hEF, hEF]
      exact tensor_form_adjoint _ _ _ hadj x y
    · intro i₁ i₂
      rw [hEF, ← hbas i₁ i₂]
      exact exp_sum_eq _ _ hζ _ _ _ fun u v => hms p _ _
    · intro j₁ i₁
      refine ⟨0, ?_⟩
      rw [smul_zero, add_zero]
      exact action_on_basis bas (a j₁) (ms p) i₁
    · intro bb hb
      exact ⟨(hQ bb hb).2, fun j₁ =>
        hκ₀ (a j₁) κ (hκ j₁) (τ bb) (Q bb) (Hm bb) (hτ bb hb) (hQ bb hb).1 (hQ bb hb).2⟩
    · intro bb hb z' hz' he
      have h1 := hinj (τ bb) (τ z') (Q bb) (Q z') (hQ bb hb).1 (hQ z' hz').1 he
      exact (hτs (τ bb) (hτ bb hb).1 (hτ bb hb).2).unique ⟨hb, rfl⟩ ⟨hz', h1.symm⟩
    · intro bb hb t hu _
      exact GlobalTheory.T.eighthPower_theta_object_of_uniformisation L₁ L₂ hgen hunif o g _ J b em w w' h W a bas σ EF hE hbas hw hw' hEF t
        (τ bb) (ms p) (Q bb) (Hm bb) (hτ bb hb) (hms p) (hQ bb hb).1 (hQ bb hb).2 hu
  · intro t ht
    obtain ⟨τ₀, m, Q₀, H₀, hτ₀, hm, hQ₀, hpol, hu⟩ :=
      GlobalTheory.T.exists_periods_eighthPower_evenUnimodularBundle L₁ L₂ hgen hunif o g _ J b em w w' h W a bas σ EF hE hbas hw hw' hEF t ht
    obtain ⟨bb, ⟨hb, rfl⟩, -⟩ := hτs τ₀ hτ₀.1 hτ₀.2
    obtain ⟨p, hp⟩ := hrep m hm
    choose y hy using hp
    refine ⟨p, bb, hb, ?_⟩
    refine GlobalTheory.UnifTransport.transport_uniformisation o g _ J b em w w' t _ EF
      (fun i u => m (bas (Pi.single i 1) u)) (fun j x u => ∑ v, a j u v • x v) Q₀ H₀ _ EF
      (fun i u => ms p (bas (Pi.single i 1) u)) (fun j x u => ∑ v, a j u v • x v) (Q bb) (Hm bb)
      (AddEquiv.refl _) (LinearEquiv.refl _ _) hpol (hQ bb hb).2 ?_ (fun _ _ => rfl)
      (fun _ _ => rfl) ?_ hu
    · intro x
      funext c
      obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective c
      exact ((hQ bb hb).1 x u i).trans (hQ₀ x u i).symm
    · intro i
      exact ⟨fun u => y (bas (Pi.single i 1) u), funext fun u => hy _⟩

end GlobalTheory.SharpGood
