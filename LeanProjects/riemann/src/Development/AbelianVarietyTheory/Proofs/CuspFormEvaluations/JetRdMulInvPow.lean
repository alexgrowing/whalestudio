import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetD

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff

namespace GlobalTheory.AnVal.JetAlg

def AnO {n g : ℕ} (f : (Fin n → Fin g → ℂ) → ℂ) : Prop := ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0

private lemma jetN_eq_renN_psJet_tay {n g : ℕ} (m : ℕ) (f : (Fin n → Fin g → ℂ) → ℂ) :
    jetN m f = renN n g m (psJet m (tay (fun v => f (colsOf n g v)) 0)) := by
  rfl

theorem jetN_mul {n g : ℕ} (m : ℕ) {f h : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (hh : AnO h) :
    jetN m (fun w => f w * h w) = jetN m f * jetN m h := by
  rw [jetN_eq_renN_psJet_tay, jetN_eq_renN_psJet_tay, jetN_eq_renN_psJet_tay, ← map_mul, ← FBIdJet.psJet_mul]
  congr 2
  exact (TM.taylor_multiplication.1 _ _ _ hf hh).1

theorem jetN_one {n g : ℕ} (m : ℕ) : jetN m (fun _ : Fin n → Fin g → ℂ => (1 : ℂ)) = 1 := by
  have hc := TM.taylor_multiplication.2.1 (n * g) 1
  simp only [jetN, jetOf]
  rw [hc, map_one, FBIdJet.psJet_one, map_one]

theorem jetN_pow {n g : ℕ} (m : ℕ) {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (p : ℕ) :
    jetN m (fun w => f w ^ p) = jetN m f ^ p := by
  induction p with
  | zero =>
    simp only [pow_zero]
    exact jetN_one m
  | succ p ih =>
    have hp : AnO fun w => f w ^ p := by
      unfold AnO at hf ⊢
      exact hf.pow p
    rw [show (fun w => f w ^ (p + 1)) = fun w => f w ^ p * f w from funext fun w => pow_succ (f w) p,
      jetN_mul m hp hf, ih]
    exact (pow_succ _ _).symm

theorem jetN_inv_mul {n g : ℕ} (m : ℕ) {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (h0 : f (colsOf n g 0) ≠ 0) :
    jetN m (fun w => (f w)⁻¹) * jetN m f = 1 := by
  have hf' : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0 := hf
  have hinv : AnO fun w => (f w)⁻¹ := hf'.inv h0
  rw [← jetN_mul m hinv hf]
  have hev : (fun v => (f (colsOf n g v))⁻¹ * f (colsOf n g v)) =ᶠ[nhds 0] fun _ => (1 : ℂ) := by
    filter_upwards [hf'.continuousAt.eventually_ne h0] with v hv
    exact inv_mul_cancel₀ hv
  have h1 := jetN_one (n := n) (g := g) m
  simp only [jetN, jetOf] at h1 ⊢
  rw [TM.taylor_multiplication.2.2 _ _ _ hev]
  exact h1

theorem AnO.zpow {n g : ℕ} {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (h0 : f (colsOf n g 0) ≠ 0) (k : ℤ) :
    AnO fun w => f w ^ k := by
  have hf' : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0 := hf
  show ContDiffAt ℂ ω (fun v => f (colsOf n g v) ^ k) 0
  obtain ⟨p, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [zpow_natCast]
    exact hf'.pow p
  · simp only [zpow_neg, zpow_natCast]
    exact (hf'.pow p).inv (pow_ne_zero _ h0)

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {n m : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem origin_mem {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {U : A.left.Opens} (hU : ⊤ ≤ ψ ⁻¹ᵁ U) :
    ⊤ ≤ (Φ.e (Λ (colsOf n g 0))).left ⁻¹ᵁ U := by
  obtain ⟨hol, rfl⟩ := hψ
  have hz : IsLocalHom (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) := by
    unfold jetZero
    exact isLocalHom_jetMap _ _
  have hr : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) := by
    unfold renN
    exact isLocalHom_jetMap _ _
  have hc : ∀ F : (Fin (n * g) → ℂ) → ℂ, jetAug (jetOf m F) = F 0 := by
    intro F
    unfold jetOf psJet
    rw [jetAug_mk, FBIdJet.psTrunc_eq]
    show MvPolynomial.coeff 0 _ = _
    rw [MvPowerSeries.coeff_truncTotal _ (by simp), coeff_tay]
    simp [dirs, fct, TM.mD_zero]
  have hk : ∀ c : ℂ, jetOf m (fun _ : Fin (n * g) → ℂ => c) = algebraMap ℂ _ c := by
    intro c
    unfold jetOf psJet
    rw [TM.taylor_multiplication.2.1, ← MvPolynomial.coe_C, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
    rfl
  have key := jetPt_precomp _ (fun _ => (Φ.e (Λ (colsOf n g 0))).left) hol (isHolFam_const _) rfl m
    (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) (fun U _ f => by
      rw [AlgHom.coe_toRingHom, jetZero_eq, hc, hk])
  rw [← jetPt_const] at key
  intro p _
  have h1 := hU (show IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m) ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
  have h2 := congrArg (fun φ => φ (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m))) key
  unfold spMap at h1 h2
  simp only [Scheme.Hom.comp_apply] at h1 h2
  have hz' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
      (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m))) := hz
  have hr' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m))) := hr
  have q1 : (Spec.map (CommRingCat.ofHom (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m)))
      (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m)) = IsLocalRing.closedPoint _ :=
    AlgebraicGeometry.Spec_closedPoint
  have q2 : (Spec.map (CommRingCat.ofHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m)))
      (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) = IsLocalRing.closedPoint _ :=
    AlgebraicGeometry.Spec_closedPoint
  have hp : ∀ q r : PrimeSpectrum ℂ, q = r := fun q r =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
  show (Over.Hom.left (Φ.e (Λ (colsOf n g 0)))) p ∈ U
  rw [hp p ((Spec.map (CommRingCat.ofHom (algebraMap ℂ (Jet ℂ (Fin 1 × Fin (n * g)) m))))
    (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m)))]
  refine (congrArg (fun z => z ∈ U) h2).mp ?_
  exact (congrArg (fun z => (jetPt (fun v => Over.Hom.left (Φ.e (Λ (colsOf n g v)))) hol m) z ∈ U)
    (q1.trans q2.symm)).mpr h1

theorem anO_fr {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {j : L.L.ι} (hU : ⊤ ≤ ψ ⁻¹ᵁ L.L.U j) : AnO fun w => Φ.fr j (Λ w) := by
  have h0 := origin_mem Φ hψ hU
  have hopen := (Φ.hol (L.L.U j) 0).1
  have han : AnalyticAt ℂ (Φ.fr j) (Λ (colsOf n g 0)) :=
    ReciprocityTheory.AnForm.Osgood.osgood g _ _ hopen (Φ.fr_hol j) _ h0
  have hc : ContDiff ℂ ω (fun v : Fin (n * g) → ℂ => colsOf n g v) := by
    unfold colsOf
    fun_prop
  have hΛ : ContDiff ℂ ω (fun x : Fin n → Fin g → ℂ => Λ x) := (LinearMap.toContinuousLinearMap Λ).contDiff
  show ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0
  exact han.contDiffAt.comp (x := 0) (hΛ.comp hc).contDiffAt

variable {K : Type} [Fintype K] {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)}
  {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}

theorem anO_prod (hφ : ∀ k, Φ.JetMap m (φ k) (Λ k)) (ε : K → ℤ) {j : K → L.L.ι} (h : ⊤ ≤ LB.wchart L.L φ j) :
    AnO fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ε k := by
  classical
  have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ L.L.U (j k) := fun k x _ => by
    have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
    unfold LB.wchart at hx
    exact Set.mem_iInter.1 hx k
  have hne : ∀ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ≠ 0 := fun k => Φ.fr_ne _ _ (origin_mem Φ (hφ k) (hk k))
  have hfr : ∀ k, AnO fun w => Φ.fr (j k) (Λ k w) := fun k => anO_fr Φ (hφ k) (hk k)
  have key : ∀ s : Finset K,
      ContDiffAt ℂ ω (fun v => ∏ k ∈ s, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.prod_empty]
      exact contDiffAt_const
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact (show ContDiffAt ℂ ω (fun v => Φ.fr (j a) (Λ a (colsOf n g v)) ^ ε a) 0 from
        AnO.zpow (hfr a) (hne a) (ε a)).mul ih
  exact key Finset.univ

theorem prod_ne (hφ : ∀ k, Φ.JetMap m (φ k) (Λ k)) (ε : K → ℤ) {j : K → L.L.ι} (h : ⊤ ≤ LB.wchart L.L φ j) :
    ∏ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ^ ε k ≠ 0 := by
  have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ L.L.U (j k) := fun k x _ => by
    have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
    unfold LB.wchart at hx
    exact Set.mem_iInter.1 hx k
  have hne : ∀ k, Φ.fr (j k) (Λ k (colsOf n g 0)) ≠ 0 := fun k => Φ.fr_ne _ _ (origin_mem Φ (hφ k) (hk k))
  exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)

end

theorem map_res_val {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (h' : ⊤ ≤ V) (u : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h').op).hom (Semi.res h u).val =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom u.val := by
  unfold Semi.res
  show (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl

end GlobalTheory.AnVal.JetAlg

open GlobalTheory.AnVal.JetAlg in
set_option backward.isDefEq.respectTransparency false in

theorem GlobalTheory.AnVal.jetRd_mul_inv_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ) (τ' : LB.Gen (LB.LinComb L.L φ' ε')) (Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m φ' ε' τ' Λ' → Φ.JetRd m (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' τ τ') (Sum.elim Λ Λ') ∧ Φ.JetRd m φ (fun k => -ε k) (LB.invGen L.L φ ε τ) Λ ∧ ∀ p : ℕ, Φ.JetRd m φ (fun k => (p : ℤ) * ε k) ⟨fun j => τ.s j ^ p⟩ Λ := by
  intro S A _ _ L x0 g Φ n m K K' _ _ φ ε τ Λ φ' ε' τ' Λ' h1 h2
  refine ⟨⟨fun k => ?_, fun j h => ?_⟩, ⟨h1.1, fun j h => ?_⟩, fun p => ⟨h1.1, fun j h => ?_⟩⟩
  · cases k with
    | inl k => exact h1.1 k
    | inr k => exact h2.1 k
  · have hL : ⊤ ≤ LB.wchart L.L φ (j ∘ Sum.inl) := fun x _ => by
      have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
      unfold LB.wchart at hx ⊢
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k)
    have hR : ⊤ ≤ LB.wchart L.L φ' (j ∘ Sum.inr) := fun x _ => by
      have hx := h (show x ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
      unfold LB.wchart at hx ⊢
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k)
    unfold LB.mulGen
    rw [Units.val_mul, map_mul, map_res_val, map_res_val]
    refine (congrArg₂ (· * ·) (h1.2 (j ∘ Sum.inl) hL) (h2.2 (j ∘ Sum.inr) hR)).trans ?_
    rw [← map_mul, ← jetN_mul m (anO_prod Φ h1.1 ε hL) (anO_prod Φ h2.1 ε' hR)]
    refine congrArg (toΓ _) (congrArg (jetN m) (funext fun w => ?_))
    rw [Fintype.prod_sum_type]
    rfl
  · have e1 : ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom ((τ.s j)⁻¹).val *
        ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom (τ.s j).val = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1.2 j h] at e1
    have e2 := jetN_inv_mul m (anO_prod Φ h1.1 ε h) (prod_ne Φ h1.1 ε h)
    have hG : (fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ (-ε k)) = fun w => (∏ k, Φ.fr (j k) (Λ k w) ^ ε k)⁻¹ := by
      funext w
      simp only [zpow_neg, Finset.prod_inv_distrib]
    refine left_inv_eq_right_inv e1 ?_
    rw [mul_comm, ← map_mul]
    beta_reduce
    rw [hG, e2, map_one]
  · have hP : (fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ((p : ℤ) * ε k)) = fun w => (∏ k, Φ.fr (j k) (Λ k w) ^ ε k) ^ p := by
      funext w
      simp only [mul_comm (p : ℤ), zpow_mul, zpow_natCast, Finset.prod_pow]
    beta_reduce
    rw [hP, jetN_pow m (anO_prod Φ h1.1 ε h) p, map_pow, ← h1.2 j h, ← map_pow, ← Units.val_pow_eq_pow_val]
