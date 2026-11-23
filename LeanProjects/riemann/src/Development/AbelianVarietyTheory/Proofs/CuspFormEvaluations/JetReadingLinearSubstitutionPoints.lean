import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetLinSub

theorem tay_coord {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).contDiff.contDiffAt
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_tay, TM.mD_zero]
    simp
  · obtain ⟨⟨a, j⟩, hp⟩ : ∃ p, n p ≠ 0 := by
      by_contra hc; push Not at hc; exact hn (Finsupp.ext hc)
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + Finsupp.single ((0 : Fin 1), j) 1 :=
      ⟨n - Finsupp.single ((0 : Fin 1), j) 1, (tsub_add_cancel_of_le
        (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hp))).symm⟩
    have h1 := TM.pderiv_tay hθ j
    have h2 : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j 1 : Fin N → ℂ) k := by
      funext y
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)
      exact congrArg (fun T : (Fin N → ℂ) →L[ℂ] ℂ => T (Pi.single j 1)) this
    rw [h2, TM.tay_const] at h1
    have h3 : MvPowerSeries.pderiv ℂ ((0 : Fin 1), j) (MvPowerSeries.X ((0 : Fin 1), k) :
        MvPowerSeries (Fin 1 × Fin N) ℂ) = MvPowerSeries.C ((Pi.single j 1 : Fin N → ℂ) k) := by
      rw [MvPowerSeries.pderiv_X]
      by_cases h : k = j
      · subst h; simp
      · simp [Prod.ext_iff, h]
    have h4 := congrArg (MvPowerSeries.coeff n') (h1.trans h3.symm)
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv] at h4
    exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero _) h4

theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetOf_coord {N : ℕ} (m : ℕ) (k : Fin N) :
    jetOf m (fun v : Fin N → ℂ => v k) = Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), k)) := by
  rw [jetOf, tay_coord, psJet_X]

def flatL {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) :
    (Fin (n' * g) → ℂ) →L[ℂ] (Fin (n * g) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v k => B (colsOf n' g v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      map_add' := fun v w => by
        funext k
        have : colsOf n' g (v + w) = colsOf n' g v + colsOf n' g w := rfl
        rw [this, map_add]; rfl
      map_smul' := fun c v => by
        funext k
        have : colsOf n' g (c • v) = c • colsOf n' g v := rfl
        rw [this, map_smul]; rfl }

theorem flatL_apply {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (v : Fin (n' * g) → ℂ)
    (k : Fin (n * g)) :
    flatL B v k = B (colsOf n' g v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

theorem colsOf_flatL {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (v : Fin (n' * g) → ℂ) :
    colsOf n g (flatL B v) = B (colsOf n' g v) := by
  funext i j
  show flatL B v (finProdFinEquiv (i, j)) = _
  rw [flatL_apply, Equiv.symm_apply_apply]

theorem subst_renN {n n' g m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (a : Jet ℂ (Fin 1 × Fin (n * g)) m) :
    σ (renN n g m a) = renN n' g m (jetMap (anLin (flatL B)) (anLin_mem _) a) := by
  have key : (σ.comp (renN n g m)).comp (Ideal.Quotient.mkₐ ℂ _) =
      ((renN n' g m).comp (jetMap (m := m) (anLin (flatL B)) (anLin_mem _))).comp (Ideal.Quotient.mkₐ ℂ _) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, k⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have e1 : renN n g m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), k))) =
        psJet m (MvPowerSeries.X (finProdFinEquiv.symm k)) := by
      rw [psJet_X]
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
      rw [MvPolynomial.aeval_X]
    have hθ : ContDiffAt ℂ ω (fun v : Fin (n * g) → ℂ => v k) 0 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) k).contDiff.contDiffAt
    have e2 := jetOf_comp_anLin m hθ (flatL B)
    rw [jetOf_coord] at e2
    show σ (renN n g m (Ideal.Quotient.mk _ _)) =
      renN n' g m (jetMap (m := m) (anLin (flatL B)) (anLin_mem _) (Ideal.Quotient.mk _ _))
    rw [e1, hσ, ← e2]
    rfl
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact DFunLike.congr_fun key p

theorem subst_jetN {n n' g m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (f : (Fin n → Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0) :
    σ (jetN m f) = jetN m (fun w => f (B w)) := by
  rw [jetN, subst_renN B σ hσ, ← jetOf_comp_anLin m hf (flatL B), jetN]
  congr 2
  funext v
  simp only [Function.comp_apply, colsOf_flatL]

theorem isHolFam_clm {Y : Scheme.{0}} {N N' : ℕ} (e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (T : (Fin N' → ℂ) →L[ℂ] (Fin N → ℂ)) : IsHolFam (fun v => e (T v)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage T.continuous, h2.comp T.differentiable.differentiableOn fun _ hv => hv⟩

theorem jetPt_clm {Y : Scheme.{0}} {N N' : ℕ} (e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (T : (Fin N' → ℂ) →L[ℂ] (Fin N → ℂ)) (e' : (Fin N' → ℂ) → (Sp ℂ ⟶ Y)) (hol' : IsHolFam e')
    (he : ∀ v, e' v = e (T v)) (m : ℕ) :
    spMap ((jetMap (anLin T) (anLin_mem T) : Jet ℂ (Fin 1 × Fin N) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin N') m) :
      Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ (Fin 1 × Fin N') m) ≫ jetPt e hol m = jetPt e' hol' m := by
  obtain rfl : e' = fun v => e (T v) := funext he
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin T) (anLin_mem T)
  refine jetPt_precompD _ _ hol hol' (by show e (T 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) T).symm

set_option backward.isDefEq.respectTransparency false in
theorem spMap_closedPoint {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R')
    (hf : IsLocalHom f) : spMap f (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
  IsLocalRing.comap_closedPoint f

theorem appTop_toΓ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    ((spMap f).appTop).hom (toΓ R a) = toΓ R' (f a) := by
  simp only [toΓ, spMap]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem res_pull {Y Z : Scheme.{0}} (s : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : ⊤ ≤ W) (h' : ⊤ ≤ W')
    (le : W' ≤ s ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (Z.presheaf.map (homOfLE h').op).hom ((Z.presheaf.map (homOfLE le).op).hom ((s.app W).hom x)) =
      s.appTop.hom ((Y.presheaf.map (homOfLE h).op).hom x) := by
  obtain rfl : W = ⊤ := top_le_iff.1 h
  obtain rfl : W' = ⊤ := top_le_iff.1 h'
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  have e1 : Y.presheaf.map (homOfLE h).op = 𝟙 _ := Y.presheaf.map_id _
  have e2 : Z.presheaf.map ((homOfLE le).op ≫ (homOfLE h').op) = 𝟙 _ := Z.presheaf.map_id _
  rw [e1, e2]
  rfl

section Main

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem jetMap_sub {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetMap m ψ Λ) :
    Φ.JetMap m (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ ψ) (Λ ∘ₗ B) := by
  obtain ⟨hol, rfl⟩ := h
  have he : ∀ v : Fin (n' * g) → ℂ, (Φ.e ((Λ ∘ₗ B) (colsOf n' g v))).left =
      (Φ.e (Λ (colsOf n g (flatL B v)))).left := fun v => by rw [colsOf_flatL]; rfl
  have hol' : IsHolFam (fun v : Fin (n' * g) → ℂ => (Φ.e ((Λ ∘ₗ B) (colsOf n' g v))).left) := by
    rw [funext he]
    exact isHolFam_clm _ hol (flatL B)
  refine ⟨hol', ?_⟩
  rw [← jetPt_clm _ hol (flatL B) _ hol' he m, ← Category.assoc, ← Category.assoc, ← anSpMap_comp, ← anSpMap_comp]
  congr 2
  exact RingHom.ext fun a => subst_renN B σ hσ a

theorem jetMap_closedPoint {n m : ℕ} (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : Φ.JetMap m ψ Λ) :
    ψ (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) = (Φ.e 0).left PullbackSections.cpt := by
  obtain ⟨hol, rfl⟩ := h
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  refine (congrArg _ (spMap_closedPoint _ (isLocalHom_jetMap _ _))).trans ?_
  refine (jetPt_closedPoint _ hol m).trans ?_
  have : Λ (colsOf n g 0) = 0 := map_zero Λ
  simp only [this]

theorem contDiffAt_fr {n : ℕ} (j : L.L.ι) (hj : (Φ.e 0).left PullbackSections.cpt ∈ L.L.U j) (a : ℤ)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    ContDiffAt ℂ ω (fun v : Fin (n * g) → ℂ => Φ.fr j (Λ (colsOf n g v)) ^ a) 0 := by
  have h0 := top_le_of_mem hj
  have h1 : AnalyticAt ℂ (Φ.fr j) 0 :=
    ReciprocityTheory.AnForm.Osgood.osgood g _ _ (Φ.hol (L.L.U j) 0).1 (Φ.fr_hol j) 0 h0
  have h2 : AnalyticAt ℂ (fun z => Φ.fr j z ^ a) 0 := h1.fun_zpow (Φ.fr_ne j 0 h0)
  let T : (Fin (n * g) → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap
    (Λ ∘ₗ { toFun := colsOf n g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
  have h3 : AnalyticAt ℂ (fun z => Φ.fr j z ^ a) (T 0) := by rw [map_zero]; exact h2
  exact (h3.comp (T.analyticAt 0)).contDiffAt

theorem jetRd_sub {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    {K : Type} [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetRd m φ ε τ Λ) :
    Φ.JetRd m (fun k => spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε
      (LB.pullGen L.L φ ε τ (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m)))
      (fun k => Λ k ∘ₗ B) := by
  obtain ⟨h1, h2⟩ := h
  have h1' := fun k => jetMap_sub Φ B σ hσ (φ k) (Λ k) (h1 k)
  refine ⟨h1', fun j hj => ?_⟩
  have hU : ∀ k, (Φ.e 0).left PullbackSections.cpt ∈ L.L.U (j k) := fun k => by
    rw [← jetMap_closedPoint Φ _ _ (h1' k)]
    exact (hj.trans (LB.wchart_le _ _ j k)) (Set.mem_univ _)
  have hj0 : ⊤ ≤ LB.wchart L.L φ j := by
    intro y _
    refine Set.mem_iInter.2 fun k => ?_
    have hk : φ k (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) ∈ L.L.U (j k) := by
      rw [jetMap_closedPoint Φ _ _ (h1 k)]; exact hU k
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (Jet ℂ (Fin n × Fin g) m)) (φ k) hk).ge
      (Set.mem_univ y)
  refine (res_pull _ _ _ hj0 hj _ (τ.s j).val).trans ?_
  rw [h2 j hj0, appTop_toΓ]
  congr 1
  exact subst_jetN B σ hσ _ (contDiffAt_prod fun k _ => contDiffAt_fr Φ (j k) (hU k) (ε k) (Λ k))

end Main

theorem jetRd_linSubst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n n' m : ℕ) (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (sb : Fin n × Fin g → MvPolynomial (Fin n' × Fin g) ℂ), (∀ p, (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m) (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2)) → ∀ (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m (fun k => spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε (LB.pullGen L.L φ ε τ (spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m))) (fun k => Λ k ∘ₗ B) := by
  intro S A _ _ L x0 g Φ n n' m B sb hsb K _ φ ε τ Λ h
  exact jetRd_sub Φ B (jetSubstP m sb) hsb φ ε τ Λ h

end GlobalTheory.JetLinSub
