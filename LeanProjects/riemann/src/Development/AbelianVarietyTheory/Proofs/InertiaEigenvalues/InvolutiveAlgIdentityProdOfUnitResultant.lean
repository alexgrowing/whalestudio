import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramDetEqNormMulGramDetOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesOfSeparableCharPolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountProdOfIdempotentSeparableStatement

noncomputable section

namespace GlobalTheory.UnitLemma.ProdId

open GlobalTheory.UnitLemma Polynomial GlobalTheory.UnitLemma.Orbit

variable {K : UQ}

theorem val_mul {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy), neg_add]

theorem isUnit_of_val (u : K.O) (h0 : algebraMap K.O K.E u ≠ 0) (h : val K.O (algebraMap K.O K.E u) = 0) :
    IsUnit u := by
  unfold val at h
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) ≠ 0 := by
    simpa using h0
  have h2 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [← WithZero.exp_log h1, neg_eq_zero.1 h, WithZero.exp_zero]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem] at h2
  by_contra hn
  exact h2 ((IsLocalRing.mem_maximalIdeal u).2 hn)

theorem resultant_map (p q : K.O[X]) :
    resultant (p.map (algebraMap K.O K.E)) (q.map (algebraMap K.O K.E)) = algebraMap K.O K.E (resultant p q) := by
  have hinj := IsFractionRing.injective K.O K.E
  rw [resultant_map_map, natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]

theorem aeval_lift (B : InvAlg K) (p : K.O[X]) (hp : p.map (algebraMap K.O K.E) = B.P) : aeval B.g p = 0 := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g B.P
  have h0 : aeval (Algebra.lmul K.E B.A B.g) B.P = 0 := LinearMap.aeval_self_charpoly _
  rw [h0] at h
  rw [← aeval_map_algebraMap K.E B.g p, hp]
  exact Algebra.lmul_injective (h.symm.trans (map_zero _).symm)

theorem idem_mem (B C : InvAlg K) (p q : K.O[X]) (hp : p.map (algebraMap K.O K.E) = B.P)
    (hq : q.map (algebraMap K.O K.E) = C.P) (h : IsCoprime p q) :
    ((1, 0) : B.A × C.A) ∈ Algebra.adjoin K.O ({(B.g, C.g)} : Set (B.A × C.A)) := by
  obtain ⟨a, b, hab⟩ := h
  have e : ((1, 0) : B.A × C.A) = aeval ((B.g, C.g) : B.A × C.A) (b * q) := by
    have h1 := Polynomial.aeval_algHom_apply (AlgHom.fst K.O B.A C.A) (B.g, C.g) (b * q)
    have h2 := Polynomial.aeval_algHom_apply (AlgHom.snd K.O B.A C.A) (B.g, C.g) (b * q)
    refine Prod.ext ?_ ?_
    · refine Eq.trans ?_ h1
      have := congrArg (aeval B.g) hab
      rw [map_add, map_mul, aeval_lift B p hp, mul_zero, zero_add, map_one] at this
      exact this.symm
    · refine Eq.trans ?_ h2
      change 0 = aeval C.g (b * q)
      rw [map_mul, aeval_lift C q hq, mul_zero]
  rw [e]
  exact aeval_mem_adjoin_singleton _ _

theorem eta_gram' (B : InvAlg K) (x : B.A) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K.E B.A) :
    K.eta (Matrix.of fun i j => B.herm x (b i) (b j)).det = K.eta (B.gramDet x) := by
  let e : ι ≃ Fin (Module.finrank K.E B.A) := b.indexEquiv (Module.finBasis K.E B.A)
  rw [← eta_gram B x (b.reindex e), ← Matrix.det_submatrix_equiv_self e]
  congr 2
  ext i j
  simp

theorem eta_prod (B C : InvAlg K) (x : B.A) (y : C.A) (hx : B.gramDet x ≠ 0) (hy : C.gramDet y ≠ 0) :
    K.eta ((B.prod C).gramDet ((x, y) : B.A × C.A)) = K.eta (B.gramDet x) * K.eta (C.gramDet y) := by
  rw [← LieEnd.eta_mul K hx hy]
  refine (eta_gram' (B.prod C) _ ((Module.finBasis K.E B.A).prod (Module.finBasis K.E C.A))).symm.trans ?_
  congr 1
  unfold InvAlg.gramDet
  rw [← Matrix.det_fromBlocks_zero₂₁ _ 0]
  have hh : ∀ u v : B.A × C.A, (B.prod C).herm ((x, y) : B.A × C.A) u v =
      B.herm x u.1 v.1 + C.herm y u.2 v.2 := fun u v => LieEnd.trace_prod B C _
  set b : Module.Basis _ K.E (B.A × C.A) := (Module.finBasis K.E B.A).prod (Module.finBasis K.E C.A) with hb
  congr 1
  ext (i | i) (j | j) <;> refine (hh (b _) (b _)).trans ?_ <;> simp [InvAlg.herm, hb]

theorem gram_ne (B C : InvAlg K) (x : B.A) (y : C.A) (hx : IsUnit x)
    (h : (B.prod C).N ((x, y) : B.A × C.A) ≠ 0) : B.gramDet x ≠ 0 := by
  rw [GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul]
  refine mul_ne_zero (hx.map _).ne_zero fun hd => ?_
  obtain ⟨r, hr, hr0⟩ := LieEnd.exists_rad B hd
  refine LieEnd.X_empty (B.prod C) ((r, 0) : B.A × C.A) (fun h => hr (congrArg Prod.fst h)) (fun z => ?_) _
    (LieEnd.nonempty_of_N_ne_zero _ _ h)
  refine (LieEnd.trace_prod B C (r * z.1, 0 * z.2)).trans ?_
  simp [hr0]

def onCl (B : InvAlg K) (F : B.A → ℚ) (hF : ∀ (x : B.A) (u : B.Aˣ), F (x * (u * B.σ (u : B.A))) = F x) :
    B.Cl → ℚ :=
  Quot.lift (fun x => F x.1) (by
    rintro x y ⟨u, hu⟩
    simp only [hu, hF])

theorem onCl_rep (B : InvAlg K) (F : B.A → ℚ) (hF : ∀ (x : B.A) (u : B.Aˣ), F (x * (u * B.σ (u : B.A))) = F x)
    (k : B.Cl) : F k.rep = onCl B F hF k := by
  conv_rhs => rw [← Quot.out_eq k]
  rfl

def fixProd (B C : InvAlg K) : {x : (B.prod C).Aˣ // (B.prod C).σ (x : (B.prod C).A) = x} ≃
    {x : B.Aˣ // B.σ (x : B.A) = x} × {x : C.Aˣ // C.σ (x : C.A) = x} where
  toFun x := (⟨(MulEquiv.prodUnits (M := B.A) (N := C.A) x.1).1, congrArg Prod.fst x.2⟩,
    ⟨(MulEquiv.prodUnits (M := B.A) (N := C.A) x.1).2, congrArg Prod.snd x.2⟩)
  invFun y := ⟨(MulEquiv.prodUnits (M := B.A) (N := C.A)).symm (y.1.1, y.2.1), Prod.ext y.1.2 y.2.2⟩
  left_inv x := Subtype.ext (Units.ext rfl)
  right_inv y := Prod.ext (Subtype.ext (Units.ext rfl)) (Subtype.ext (Units.ext rfl))

def clProd (B C : InvAlg K) : (B.prod C).Cl ≃ B.Cl × C.Cl where
  toFun := Quot.lift (fun x => (Quot.mk _ (fixProd B C x).1, Quot.mk _ (fixProd B C x).2)) (by
    rintro x y ⟨u, hu⟩
    exact Prod.ext (Quot.sound ⟨(MulEquiv.prodUnits (M := B.A) (N := C.A) u).1, congrArg Prod.fst hu⟩)
      (Quot.sound ⟨(MulEquiv.prodUnits (M := B.A) (N := C.A) u).2, congrArg Prod.snd hu⟩))
  invFun k := Quot.lift₂ (fun x y => Quot.mk _ ((fixProd B C).symm (x, y)))
    (by
      rintro x y z ⟨u, hu⟩
      refine Quot.sound ⟨(MulEquiv.prodUnits (M := B.A) (N := C.A)).symm (1, u), Prod.ext ?_ hu⟩
      change (x.1 : B.A) = x.1 * (1 * B.σ 1)
      simp)
    (by
      rintro x y z ⟨u, hu⟩
      refine Quot.sound ⟨(MulEquiv.prodUnits (M := B.A) (N := C.A)).symm (u, 1), Prod.ext hu ?_⟩
      change (z.1 : C.A) = z.1 * (1 * C.σ 1)
      simp) k.1 k.2
  left_inv := by
    rintro ⟨x⟩
    exact congrArg (Quot.mk _) ((fixProd B C).left_inv x)
  right_inv := by
    rintro ⟨⟨x⟩, ⟨y⟩⟩
    rfl

theorem finsum_prod (B C : InvAlg K) [Finite B.Cl] [Finite C.Cl] (F : (B.prod C).A → ℚ) (G : B.A → ℚ)
    (H : C.A → ℚ)
    (hG : ∀ (x : B.A) (u : B.Aˣ), G (x * (u * B.σ (u : B.A))) = G x)
    (hH : ∀ (x : C.A) (u : C.Aˣ), H (x * (u * C.σ (u : C.A))) = H x)
    (h : ∀ (x : B.A) (y : C.A), IsUnit x → IsUnit y → B.σ x = x → C.σ y = y →
      F ((x, y) : B.A × C.A) = G x * H y) :
    ∑ᶠ k : (B.prod C).Cl, F k.rep = (∑ᶠ k : B.Cl, G k.rep) * ∑ᶠ k : C.Cl, H k.rep := by
  have e : ∀ k : (B.prod C).Cl, F k.rep = onCl B G hG (clProd B C k).1 * onCl C H hH (clProd B C k).2 := by
    intro k
    conv_rhs => rw [← Quot.out_eq k]
    exact h _ _ (Units.isUnit (fixProd B C k.out).1.1) (Units.isUnit (fixProd B C k.out).2.1)
      (fixProd B C k.out).1.2 (fixProd B C k.out).2.2
  haveI := Fintype.ofFinite B.Cl
  haveI := Fintype.ofFinite C.Cl
  simp only [e, onCl_rep B G hG, onCl_rep C H hH]
  rw [finsum_comp_equiv (clProd B C) (f := fun k => onCl B G hG k.1 * onCl C H hH k.2)]
  simp only [finsum_eq_sum_of_fintype]
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]

def swap4 (B₁ B₂ C₁ C₂ : InvAlg K) :
    ((B₁.prod B₂).prod (C₁.prod C₂)).A ≃ₐ[K.E] ((B₁.prod C₁).prod (B₂.prod C₂)).A :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.prodProdProdComm B₁.A B₂.A C₁.A C₂.A) fun _ => rfl

theorem isIso_swap4 (B₁ B₂ C₁ C₂ : InvAlg K) : IsIso (swap4 B₁ B₂ C₁ C₂) := ⟨fun _ => rfl, rfl⟩

theorem kap_inv (B C : InvAlg K) (x : (B.prod C).A) (u : (B.prod C).Aˣ) :
    K.eta (B.gramDet (x * (u * (B.prod C).σ (u : (B.prod C).A))).1) *
      (B.prod C).N (x * (u * (B.prod C).σ (u : (B.prod C).A))) = K.eta (B.gramDet x.1) * (B.prod C).N x := by
  rw [(GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (B.prod C) x u).1]
  congr 1
  exact (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B x.1 (MulEquiv.prodUnits (M := B.A) (N := C.A) u).1).2

theorem stSum_prod (B C : InvAlg K) (hs : (B.P * C.P).Separable)
    (he : ((1, 0) : B.A × C.A) ∈ Algebra.adjoin K.O ({(B.g, C.g)} : Set (B.A × C.A))) :
    (B.prod C).stSum = B.stSum * C.stSum := by
  haveI := GlobalTheory.T.finite_classes_of_separable_charPoly K B hs.of_mul_left
  haveI := GlobalTheory.T.finite_classes_of_separable_charPoly K C hs.of_mul_right
  exact finsum_prod B C (B.prod C).N B.N C.N (fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B x u).1)
    (fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C x u).1) (GlobalTheory.T.latticeCount_prod_of_idempotent_separable K B C he hs)

theorem kapSum_prod (B₁ B₂ C₁ C₂ : InvAlg K) (hs : ((B₁.prod B₂).P * (C₁.prod C₂).P).Separable)
    (he : ((1, 0) : (B₁.prod B₂).A × (C₁.prod C₂).A) ∈ Algebra.adjoin K.O
      ({((B₁.prod B₂).g, (C₁.prod C₂).g)} : Set ((B₁.prod B₂).A × (C₁.prod C₂).A))) :
    InvAlg.kapSum (B₁.prod C₁) (B₂.prod C₂) = InvAlg.kapSum B₁ B₂ * InvAlg.kapSum C₁ C₂ := by
  haveI := GlobalTheory.T.finite_classes_of_separable_charPoly K _ hs.of_mul_left
  haveI := GlobalTheory.T.finite_classes_of_separable_charPoly K _ hs.of_mul_right
  unfold InvAlg.kapSum
  rw [(isIso_swap4 B₁ B₂ C₁ C₂).finsum_eq
    (fun x => K.eta ((B₁.prod C₁).gramDet x.1) * ((B₁.prod C₁).prod (B₂.prod C₂)).N x) (kap_inv _ _)]
  refine finsum_prod (B₁.prod B₂) (C₁.prod C₂)
    (fun x => K.eta ((B₁.prod C₁).gramDet (swap4 B₁ B₂ C₁ C₂ x).1) *
      ((B₁.prod C₁).prod (B₂.prod C₂)).N (swap4 B₁ B₂ C₁ C₂ x))
    (fun x => K.eta (B₁.gramDet x.1) * (B₁.prod B₂).N x)
    (fun x => K.eta (C₁.gramDet x.1) * (C₁.prod C₂).N x) (kap_inv _ _) (kap_inv _ _) ?_
  intro x y hx hy sx sy
  refine (congrArg (HMul.hMul _) (((isIso_swap4 B₁ B₂ C₁ C₂).N_eq _).trans
    (GlobalTheory.T.latticeCount_prod_of_idempotent_separable K _ _ he hs x y hx hy sx sy))).trans ?_
  by_cases h1 : (B₁.prod B₂).N x = 0
  · simp [h1]
  by_cases h2 : (C₁.prod C₂).N y = 0
  · simp [h2]
  have e := eta_prod B₁ C₁ x.1 y.1 (gram_ne B₁ B₂ x.1 x.2 (hx.map (RingHom.fst B₁.A B₂.A)) h1)
    (gram_ne C₁ C₂ y.1 y.2 (hy.map (RingHom.fst C₁.A C₂.A)) h2)
  change K.eta ((B₁.prod C₁).gramDet ((x.1, y.1) : B₁.A × C₁.A)) * _ = _
  rw [e]
  ring

theorem resultant_four {R : Type} [CommRing R] {p₁ p₂ r₁ r₂ : R[X]} (h₁ : p₁.Monic) (h₂ : p₂.Monic)
    (k₁ : r₁.Monic) (k₂ : r₂.Monic) :
    resultant (p₁ * r₁) (p₂ * r₂) =
      resultant p₁ p₂ * resultant r₁ r₂ * (resultant p₁ r₂ * resultant r₁ p₂) := by
  nontriviality R
  have e := resultant_mul_left p₁ r₁ (p₂ * r₂) _ le_rfl
  rw [← h₁.natDegree_mul k₁] at e
  rw [e, h₂.natDegree_mul k₂, resultant_mul_right _ _ _ _ le_rfl, resultant_mul_right _ _ _ _ le_rfl]
  ring

theorem identity_prod : ∀ (K : UQ) (B₁ B₂ C₁ C₂ : InvAlg K), ((B₁.P * B₂.P) * (C₁.P * C₂.P)).Separable →
    IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsIntegral K.O C₁.g → IsIntegral K.O C₂.g →
    val K.O (resultant (B₁.P * B₂.P) (C₁.P * C₂.P)) = 0 → InvAlg.Identity B₁ B₂ → InvAlg.Identity C₁ C₂ →
    InvAlg.Identity (B₁.prod C₁) (B₂.prod C₂) := by
  intro K B₁ B₂ C₁ C₂ hs i₁ i₂ j₁ j₂ hv hB hC
  have sB := hs.of_mul_left
  have sC := hs.of_mul_right
  obtain ⟨p₁, m₁, e₁⟩ := exists_monic_map_eq_charpoly₂ B₁ sB.of_mul_left i₁
  obtain ⟨p₂, m₂, e₂⟩ := exists_monic_map_eq_charpoly₂ B₂ sB.of_mul_right i₂
  obtain ⟨r₁, n₁, f₁⟩ := exists_monic_map_eq_charpoly₂ C₁ sC.of_mul_left j₁
  obtain ⟨r₂, n₂, f₂⟩ := exists_monic_map_eq_charpoly₂ C₂ sC.of_mul_right j₂
  have eB : (p₁ * p₂).map (algebraMap K.O K.E) = B₁.P * B₂.P := by rw [Polynomial.map_mul, e₁, e₂]
  have eC : (r₁ * r₂).map (algebraMap K.O K.E) = C₁.P * C₂.P := by rw [Polynomial.map_mul, f₁, f₂]
  have hcop : IsCoprime (p₁ * p₂) (r₁ * r₂) := by
    have h0 := resultant_ne_zero _ _ hs.isCoprime
    rw [← eB, ← eC, resultant_map] at h0 hv
    exact (isUnit_resultant_iff_isCoprime (m₁.mul m₂)).1 (isUnit_of_val _ h0 hv)
  have s₁ : (B₁.P * C₁.P).Separable :=
    hs.of_dvd (mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _))
  have s₂ : (B₂.P * C₂.P).Separable :=
    hs.of_dvd (mul_dvd_mul (dvd_mul_left _ _) (dvd_mul_left _ _))
  have hk := kapSum_prod B₁ B₂ C₁ C₂ (by rw [prod_P, prod_P]; exact hs)
    (idem_mem _ _ _ _ (eB.trans (prod_P _ _).symm) (eC.trans (prod_P _ _).symm) hcop)
  have h₁ := stSum_prod B₁ C₁ s₁ (idem_mem _ _ _ _ e₁ f₁ hcop.of_mul_left_left.of_mul_right_left)
  have h₂ := stSum_prod B₂ C₂ s₂ (idem_mem _ _ _ _ e₂ f₂ hcop.of_mul_left_right.of_mul_right_right)
  have hr : val K.O (resultant (B₁.P * C₁.P) (B₂.P * C₂.P)) =
      val K.O (resultant B₁.P B₂.P) + val K.O (resultant C₁.P C₂.P) := by
    have u₁ : IsUnit (resultant p₁ r₂) :=
      (isUnit_resultant_iff_isCoprime m₁).2 hcop.of_mul_left_left.of_mul_right_right
    have u₂ : IsUnit (resultant r₁ p₂) :=
      (isUnit_resultant_iff_isCoprime n₁).2 hcop.of_mul_left_right.of_mul_right_left.symm
    have a₁ := resultant_ne_zero _ _ sB.isCoprime
    have a₂ := resultant_ne_zero _ _ sC.isCoprime
    have hu : resultant B₁.P C₂.P * resultant C₁.P B₂.P =
        algebraMap K.O K.E (resultant p₁ r₂ * resultant r₁ p₂) := by
      rw [map_mul, ← resultant_map, ← resultant_map, e₁, e₂, f₁, f₂]
    rw [resultant_four (p₁ := B₁.P) (p₂ := B₂.P) (r₁ := C₁.P) (r₂ := C₂.P) (LinearMap.charpoly_monic _)
      (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _), hu,
      val_mul (mul_ne_zero a₁ a₂) ((u₁.mul u₂).map _).ne_zero, val_mul a₁ a₂, val_unit _ (u₁.mul u₂), add_zero]
  have hq : (-(K.q : ℚ)) ≠ 0 := neg_ne_zero.2 (Nat.cast_ne_zero.2 (LieEnd.q_ne_zero K))
  unfold InvAlg.Identity at hB hC ⊢
  rw [prod_P, prod_P, hr, hk, h₁, h₂, neg_add, zpow_add₀ hq, mul_mul_mul_comm, hB, hC]
  ring

end GlobalTheory.UnitLemma.ProdId
