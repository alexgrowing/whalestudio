import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem exists_genHasVal (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) :
    ∃ n, GenHasVal ϖ L φ φ' hφ ε t n := by
  obtain rfl : φ' = fun k => jK V ≫ φ k := funext hφ
  obtain ⟨e, he⟩ := exists_gen_of_local L hL φ ε
  obtain ⟨j₀, htop⟩ := exists_chart_top L hL φ ε
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ k) j₀ := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L φ j₀ := by
      rw [htop]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k, (φ k).base ⁻¹' (L.U (j₀ k) : Set X)) := hy
    show y ∈ (⋂ k, (jK V ≫ φ k).base ⁻¹' (L.U (j₀ k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  have hP := pullGen_isGen L φ ε e he (jK V)
  have gen3 : ∀ {A : Scheme.{0}} {U U' U'' : A.Opens} (h1 : U' ≤ U) (h2 : U'' ≤ U') (x : Γ(A, U)ˣ),
      res h2 (res h1 x) = res (h2.trans h1) x := by
    intro A U U' U'' h1 h2 x
    apply Units.ext
    have hm : A.presheaf.map (homOfLE h1).op ≫ A.presheaf.map (homOfLE h2).op =
        A.presheaf.map (homOfLE (h2.trans h1)).op := by
      rw [← Functor.map_comp]
      rfl
    exact congrArg (fun m => m.hom x.val) hm
  have gen0 : ∀ {A : Scheme.{0}} {U : A.Opens} (h : U ≤ U) (x : Γ(A, U)ˣ), res h x = x := by
    intro A U h x
    apply Units.ext
    show (A.presheaf.map (homOfLE h).op).hom x.val = x.val
    rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from rfl, CategoryTheory.Functor.map_id]
    rfl
  have hle : ∀ j : Ix → L.ι, LB.wchart L (fun k => jK V ≫ φ k) j ≤ LB.wchart L (fun k => jK V ≫ φ k) j₀ :=
    fun j => le_top.trans hK
  have keyA : ∀ {W W0 : (Spec (CommRingCat.of (FractionRing V))).Opens} (hle : W ≤ W0)
      (hl : W ⊓ W0 ≤ W) (hr : W ⊓ W0 ≤ W0)
      (T P : Γ(Spec (CommRingCat.of (FractionRing V)), W)ˣ)
      (T0 P0 : Γ(Spec (CommRingCat.of (FractionRing V)), W0)ˣ)
      (g : Γ(Spec (CommRingCat.of (FractionRing V)), W ⊓ W0)ˣ),
      res hl T = g * res hr T0 → res hl P = g * res hr P0 → T = res hle (T0 / P0) * P := by
    intro W W0 hle hl hr T P T0 P0 g h1 h2
    have h3 : res hl (T / P) = res hr (T0 / P0) := by
      rw [map_div, map_div, h1, h2, mul_div_mul_left_eq_div]
    have h4 := congrArg (res (le_inf le_rfl hle : W ≤ W ⊓ W0)) h3
    rw [gen3, gen3, gen0] at h4
    exact div_eq_iff_eq_mul.1 h4
  set Dt : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)ˣ :=
    res hK (t.s j₀ / (LB.pullGen L φ ε e (jK V)).s j₀) with hDt
  set c : FractionRing V := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom Dt.val with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have hu : IsUnit c := Dt.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom
    rw [h0] at hu
    exact not_isUnit_zero hu
  obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hc0
  refine ⟨n, e, he, c, hn, fun (j : Ix → L.ι) => ?_⟩
  have hsc : scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c = Dt.val := by
    simp [scal, hc, Scheme.Hom.appTop]
  have hkey := keyA (hle j) inf_le_left inf_le_right (t.s j) ((LB.pullGen L φ ε e (jK V)).s j)
    (t.s j₀) ((LB.pullGen L φ ε e (jK V)).s j₀) _ (ht j j₀) (hP j j₀)
  refine (congrArg Units.val hkey).trans ?_
  have hA : (res (hle j) (t.s j₀ / (LB.pullGen L φ ε e (jK V)).s j₀)).val =
      resTop (LB.wchart L (fun k => jK V ≫ φ k) j) (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) := by
    rw [hsc, hDt]
    exact (congrArg Units.val (gen3 hK (le_top : LB.wchart L (fun k => jK V ≫ φ k) j ≤ ⊤) _)).symm
  exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) hA rfl)

def scalUnit (c : FractionRing V) (hc : c ≠ 0) : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom.toMonoidHom (Units.mk0 c hc)

lemma ne_zero_of_hasVal {c : FractionRing V} {n : ℤ} (hϖ : Irreducible ϖ) (hn : HasVal ϖ c n) : c ≠ 0 := by
  obtain ⟨u, hu⟩ := hn
  rw [hu]
  have hinj := IsFractionRing.injective V (FractionRing V)
  refine mul_ne_zero (zpow_ne_zero _ ?_) ?_
  · exact (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  · exact (map_ne_zero_iff _ hinj).2 u.ne_zero

theorem genHasVal_unique (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n m : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) (hm : GenHasVal ϖ L φ φ' hφ ε t m) : n = m := by
  obtain rfl : φ' = fun k => jK V ≫ φ k := funext hφ
  obtain ⟨j₀, htop⟩ := exists_chart_top L hL φ ε
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ k) j₀ := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L φ j₀ := by
      rw [htop]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k, (φ k).base ⁻¹' (L.U (j₀ k) : Set X)) := hy
    show y ∈ (⋂ k, (jK V ≫ φ k).base ⁻¹' (L.U (j₀ k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  obtain ⟨c1, hc1, u1, h1⟩ := genHasVal_top L φ ε t hn j₀ htop hK
  obtain ⟨c2, hc2, u2, h2⟩ := genHasVal_top L φ ε t hm j₀ htop hK
  have h12 : c1 * algebraMap V (FractionRing V) (u1 : V) = c2 * algebraMap V (FractionRing V) (u2 : V) :=
    h1.symm.trans h2
  refine hasVal_unique hϖ (hasVal_mul_unit hc1 u1) ?_
  rw [h12]
  exact hasVal_mul_unit hc2 u2

lemma sumElim_hφ {X : Scheme.{0}} {Ix Ix' : Type}
    {φ₁ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ₁' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ₁ : ∀ k, φ₁' k = jK V ≫ φ₁ k)
    {φ₂ : Ix' → (Spec (CommRingCat.of V) ⟶ X)} {φ₂' : Ix' → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ₂ : ∀ k, φ₂' k = jK V ≫ φ₂ k) :
    ∀ k, Sum.elim φ₁' φ₂' k = jK V ≫ Sum.elim φ₁ φ₂ k := by
  rintro (k | k)
  · exact hφ₁ k
  · exact hφ₂ k

set_option maxHeartbeats 1000000 in

theorem genHasVal_mulGen (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix Ix' : Type} [Fintype Ix] [Fintype Ix']
    (φ₁ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ₁' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₁ : ∀ k, φ₁' k = jK V ≫ φ₁ k) (ε₁ : Ix → ℤ)
    (φ₂ : Ix' → (Spec (CommRingCat.of V) ⟶ X)) (φ₂' : Ix' → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₂ : ∀ k, φ₂' k = jK V ≫ φ₂ k) (ε₂ : Ix' → ℤ)
    (t₁ : LB.Gen (LB.LinComb L φ₁' ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂' ε₂)) {n m : ℤ}
    (hn : GenHasVal ϖ L φ₁ φ₁' hφ₁ ε₁ t₁ n) (hm : GenHasVal ϖ L φ₂ φ₂' hφ₂ ε₂ t₂ m) :
    GenHasVal ϖ L (Sum.elim φ₁ φ₂) (Sum.elim φ₁' φ₂') (sumElim_hφ hφ₁ hφ₂) (Sum.elim ε₁ ε₂)
      (LB.mulGen L φ₁' ε₁ φ₂' ε₂ t₁ t₂) (n + m) := by
  obtain ⟨e₁, he₁, c₁, hc₁, hC₁⟩ := genHasVal_units L φ₁ φ₁' hφ₁ ε₁ t₁ hn
  obtain ⟨e₂, he₂, c₂, hc₂, hC₂⟩ := genHasVal_units L φ₂ φ₂' hφ₂ ε₂ t₂ hm
  refine ⟨LB.mulGen L φ₁ ε₁ φ₂ ε₂ e₁ e₂, mulGen_isGen L φ₁ ε₁ φ₂ ε₂ e₁ e₂ he₁ he₂, c₁ * c₂, ?_,
    fun (j : Ix ⊕ Ix' → L.ι) => ?_⟩
  · obtain ⟨u₁, hu₁⟩ := hc₁
    obtain ⟨u₂, hu₂⟩ := hc₂
    refine ⟨u₁ * u₂, ?_⟩
    have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
    rw [hu₁, hu₂, zpow_add₀ hπ, Units.val_mul, map_mul]
    ring
  · have gen1 : ∀ (W W' : (Spec (CommRingCat.of (FractionRing V))).Opens) (h : W' ≤ W)
        (x : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)),
        ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE h).op).hom (resTop W x) =
          resTop W' x := by
      intro W W' h x
      simp only [resTop]
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have gen2 : ∀ {A B : Scheme.{0}} (f : A ⟶ B) (U U' : B.Opens) (hU : U' ≤ U) (W : A.Opens)
        (hW : W ≤ f ⁻¹ᵁ U') (x : Γ(B, U)ˣ),
        res hW (pullU f U' (res hU x)) = res (fun y hy => hU (hW hy) : W ≤ f ⁻¹ᵁ U) (pullU f U x) := by
      intro A B f U U' hU W hW x
      apply Units.ext
      have hm : (B.presheaf.map (homOfLE hU).op ≫ f.app U') ≫ A.presheaf.map (homOfLE hW).op =
          f.app U ≫ A.presheaf.map (homOfLE (fun y hy => hU (hW hy) : W ≤ f ⁻¹ᵁ U)).op := by
        rw [Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
        rfl
      exact congrArg (fun m => m.hom x.val) hm
    have gen3 : ∀ {A : Scheme.{0}} {U U' U'' : A.Opens} (h1 : U' ≤ U) (h2 : U'' ≤ U') (x : Γ(A, U)ˣ),
        res h2 (res h1 x) = res (h2.trans h1) x := by
      intro A U U' U'' h1 h2 x
      apply Units.ext
      have hm : A.presheaf.map (homOfLE h1).op ≫ A.presheaf.map (homOfLE h2).op =
          A.presheaf.map (homOfLE (h2.trans h1)).op := by
        rw [← Functor.map_comp]
        rfl
      exact congrArg (fun m => m.hom x.val) hm
    have key2 : ∀ {W W1 W2 : (Spec (CommRingCat.of (FractionRing V))).Opens}
        {U U1 U2 : (Spec (CommRingCat.of V)).Opens} (a1 : W ≤ W1) (a2 : W ≤ W2)
        (b1 : W1 ≤ jK V ⁻¹ᵁ U1) (b2 : W2 ≤ jK V ⁻¹ᵁ U2) (m1 : U ≤ U1) (m2 : U ≤ U2)
        (h : W ≤ jK V ⁻¹ᵁ U) (E1 : Γ(Spec (CommRingCat.of V), U1)ˣ) (E2 : Γ(Spec (CommRingCat.of V), U2)ˣ)
        (T1 C1 : Γ(Spec (CommRingCat.of (FractionRing V)), W1)ˣ)
        (T2 C2 : Γ(Spec (CommRingCat.of (FractionRing V)), W2)ˣ) (c1 c2 : FractionRing V),
        T1 = C1 * res b1 (pullU (jK V) U1 E1) → T2 = C2 * res b2 (pullU (jK V) U2 E2) →
        C1.val = resTop W1 (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c1) →
        C2.val = resTop W2 (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c2) →
        (res a1 T1 * res a2 T2).val = resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) (c1 * c2)) *
          (res h (pullU (jK V) U (res m1 E1 * res m2 E2))).val := by
      intro W W1 W2 U U1 U2 a1 a2 b1 b2 m1 m2 h E1 E2 T1 C1 T2 C2 c1 c2 h1 h2 h3 h4
      have e1 : (res a1 C1).val = resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c1) := by
        rw [← gen1 W1 W a1, ← h3]
        rfl
      have e2 : (res a2 C2).val = resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c2) := by
        rw [← gen1 W2 W a2, ← h4]
        rfl
      have e3 : resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) (c1 * c2)) =
          resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c1) *
            resTop W (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c2) := by
        simp only [scal, resTop, map_mul]
      rw [h1, h2, map_mul, map_mul, gen3, gen3, map_mul (pullU (jK V) U), map_mul (res h), gen2, gen2]
      simp only [Units.val_mul]
      rw [e1, e2, e3]
      ring
    obtain ⟨C₁, hC₁v, hC₁e⟩ := hC₁ (j ∘ Sum.inl)
    obtain ⟨C₂, hC₂v, hC₂e⟩ := hC₂ (j ∘ Sum.inr)
    exact key2 _ _ _ _ _ _ _ _ _ _ C₁ _ C₂ _ _ hC₁e hC₂e hC₁v hC₂v

theorem genHasVal_invGen {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    GenHasVal ϖ L φ φ' hφ (fun k => - ε k) (LB.invGen L φ' ε t) (-n) := by
  obtain ⟨e, he, c, ⟨u, hu⟩, hj⟩ := hn
  refine ⟨LB.invGen L φ ε e, invGen_isGen L φ ε e he, c⁻¹, ⟨u⁻¹, ?_⟩, fun (j : Ix → L.ι) => ?_⟩
  · rw [hu, mul_inv, zpow_neg, map_units_inv]
  · have hT := hj j
    have hxy : resTop (LB.wchart L φ' j) (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
        resTop (LB.wchart L φ' j) (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c⁻¹) = 1 := by
      by_cases hc : c = 0
      · have h0 : (t.s j).val = 0 := by
          have hs0 : scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) (0 : FractionRing V) = 0 := by
            simp only [scal, map_zero]
          have hr0 : resTop (LB.wchart L φ' j)
              (0 : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)) = 0 := by
            simp only [resTop, map_zero]
          rw [hT, hc, hs0, hr0]
          exact zero_mul _
        have hu0 := (t.s j).isUnit
        rw [h0] at hu0
        exact eq_of_zero_eq_one (isUnit_zero_iff.1 hu0) _ _
      · simp only [resTop, scal, ← map_mul, mul_inv_cancel₀ hc, map_one]
    change ((t.s j)⁻¹).val = _
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hT, show (LB.invGen L φ ε e).s j = (e.s j)⁻¹ from rfl]
    have hRR : (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) (LB.wchart L φ j) (e.s j))).val *
        (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) (LB.wchart L φ j) (e.s j)⁻¹)).val = 1 := by
      have gen : ∀ {A B : Scheme.{0}} (f : A ⟶ B) (U : B.Opens) (W : A.Opens) (hW : W ≤ f ⁻¹ᵁ U)
          (x : Γ(B, U)ˣ), (res hW (pullU f U x)).val * (res hW (pullU f U x⁻¹)).val = 1 := by
        intro A B f U W hW x
        rw [map_inv, map_inv]
        exact Units.mul_inv _
      exact gen _ _ _ _ (e.s j)
    have key : ∀ (x y r r' : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)),
        x * y = 1 → r * r' = 1 → x * r * (y * r') = 1 := by
      intro x y r r' h1 h2
      calc x * r * (y * r') = (x * y) * (r * r') := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    exact key _ _ _ _ hxy hRR

theorem genHasVal_corr (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {Ix Ix' : Type}
    [Fintype Ix] [Fintype Ix'] (s : X ⟶ Spec (CommRingCat.of V)) [IsSeparated s]
    (φ₁ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ₁' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₁ : ∀ k, φ₁' k = jK V ≫ φ₁ k) (ε₁ : Ix → ℤ)
    (φ₂ : Ix' → (Spec (CommRingCat.of V) ⟶ X)) (φ₂' : Ix' → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ₂ : ∀ k, φ₂' k = jK V ≫ φ₂ k) (ε₂ : Ix' → ℤ)
    (hs₁ : ∀ k, φ₁ k ≫ s = 𝟙 _) (hs₂ : ∀ k, φ₂ k ≫ s = 𝟙 _)
    (t₁ : LB.Gen (LB.LinComb L φ₁' ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂' ε₂)) (ht₂ : t₂.IsGen)
    (hc : LB.Gen.Corr L φ₁' ε₁ φ₂' ε₂ t₁ t₂) {n : ℤ} (hn : GenHasVal ϖ L φ₁ φ₁' hφ₁ ε₁ t₁ n) :
    GenHasVal ϖ L φ₂ φ₂' hφ₂ ε₂ t₂ n := by
  obtain rfl : φ₁' = fun k => jK V ≫ φ₁ k := funext hφ₁
  obtain rfl : φ₂' = fun k => jK V ≫ φ₂ k := funext hφ₂
  have sep : ∀ (x x' : Spec (CommRingCat.of V) ⟶ X), jK V ≫ x = jK V ≫ x' → x ≫ s = 𝟙 _ →
      x' ≫ s = 𝟙 _ → x = x' := by
    intro x x' h hx hx'
    let S : ValuativeCommSq s :=
      { R := V, K := FractionRing V, i₁ := jK V ≫ x, i₂ := 𝟙 _,
        commSq := ⟨by rw [Category.assoc, hx]⟩ }
    have hU : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion s S
    exact congrArg CommSq.LiftStruct.l
      (@Subsingleton.elim _ hU (⟨x, rfl, hx⟩ : S.commSq.LiftStruct) (⟨x', h.symm, hx'⟩ : S.commSq.LiftStruct))
  have gen3 : ∀ {A : Scheme.{0}} {U U' U'' : A.Opens} (h1 : U' ≤ U) (h2 : U'' ≤ U') (x : Γ(A, U)ˣ),
      res h2 (res h1 x) = res (h2.trans h1) x := by
    intro A U U' U'' h1 h2 x
    apply Units.ext
    have hm : A.presheaf.map (homOfLE h1).op ≫ A.presheaf.map (homOfLE h2).op =
        A.presheaf.map (homOfLE (h2.trans h1)).op := by
      rw [← Functor.map_comp]
      rfl
    exact congrArg (fun m => m.hom x.val) hm
  have gen5 : ∀ {A : Scheme.{0}} {U1 U2 W : A.Opens} (l : U1 ⊓ U2 ≤ U1) (r : U1 ⊓ U2 ≤ U2)
      (h : W ≤ U1 ⊓ U2) (h1 : W ≤ U1) (h2 : W ≤ U2) (x : Γ(A, U1)ˣ) (y : Γ(A, U2)ˣ),
      res l x = res r y → res h1 x = res h2 y := by
    intro A U1 U2 W l r h h1 h2 x y H
    have H' := congrArg (res h) H
    rw [gen3, gen3] at H'
    exact H'
  have hch : ∀ y : Spec (CommRingCat.of V) ⟶ X, ∃ i : L.ι,
      y.base (IsLocalRing.closedPoint V) ∈ L.U i := by
    intro y
    have hmem : y.base (IsLocalRing.closedPoint V) ∈ ⨆ i, L.U i := by
      rw [hL.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hmem
  choose ich hich using hch
  have htop₁ : LB.wchart L φ₁ (fun k => ich (φ₁ k)) = ⊤ := by
    apply eq_top_of_closedPoint_mem
    show _ ∈ (⋂ k, (φ₁ k).base ⁻¹' (L.U (ich (φ₁ k)) : Set X))
    exact Set.mem_iInter.2 fun k => hich (φ₁ k)
  have htop₂ : LB.wchart L φ₂ (fun k => ich (φ₂ k)) = ⊤ := by
    apply eq_top_of_closedPoint_mem
    show _ ∈ (⋂ k, (φ₂ k).base ⁻¹' (L.U (ich (φ₂ k)) : Set X))
    exact Set.mem_iInter.2 fun k => hich (φ₂ k)
  have hK₁ : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ₁ k) (fun k => ich (φ₁ k)) := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L φ₁ (fun k => ich (φ₁ k)) := by
      rw [htop₁]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k, (φ₁ k).base ⁻¹' (L.U ((fun k => ich (φ₁ k)) k) : Set X)) := hy
    show y ∈ (⋂ k, (jK V ≫ φ₁ k).base ⁻¹' (L.U ((fun k => ich (φ₁ k)) k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  have hK₂ : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ₂ k) (fun k => ich (φ₂ k)) := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L φ₂ (fun k => ich (φ₂ k)) := by
      rw [htop₂]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k, (φ₂ k).base ⁻¹' (L.U ((fun k => ich (φ₂ k)) k) : Set X)) := hy
    show y ∈ (⋂ k, (jK V ≫ φ₂ k).base ⁻¹' (L.U ((fun k => ich (φ₂ k)) k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  obtain ⟨m, hm⟩ := exists_genHasVal hϖ L hL φ₂ _ hφ₂ ε₂ t₂ ht₂
  obtain ⟨c1, hc1, u1, h1⟩ := genHasVal_top L φ₁ ε₁ t₁ hn _ htop₁ hK₁
  obtain ⟨c2, hc2, u2, h2⟩ := genHasVal_top L φ₂ ε₂ t₂ hm _ htop₂ hK₂
  have hco := hc (fun k => ich (φ₁ k)) (fun k => ich (φ₂ k))
    (fun a b hab => congrArg ich (sep _ _ hab (hs₁ a) (hs₁ b)))
    (fun a b hab => congrArg ich (sep _ _ hab (hs₂ a) (hs₂ b)))
    (fun a b hab => congrArg ich (sep _ _ hab (hs₁ a) (hs₂ b)))
  have h3 := gen5 _ _ (le_inf hK₁ hK₂) hK₁ hK₂ _ _ hco
  have h4 := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom z.val) h3
  have h5 : c1 * algebraMap V (FractionRing V) (u1 : V) = c2 * algebraMap V (FractionRing V) (u2 : V) :=
    h1.symm.trans (h4.trans h2)
  have hnm : n = m := by
    refine hasVal_unique hϖ (hasVal_mul_unit hc1 u1) ?_
    rw [h5]
    exact hasVal_mul_unit hc2 u2
  rw [hnm]
  exact hm

theorem genHasVal_pullGen_of {X Y : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix] (φ : Ix → (Y ⟶ X))
    (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (p : Spec (CommRingCat.of V) ⟶ Y)
    (q : Spec (CommRingCat.of (FractionRing V)) ⟶ Y) (hq : q = jK V ≫ p) :
    GenHasVal ϖ L (fun k => p ≫ φ k) (fun k => q ≫ φ k) (fun k => by rw [hq, Category.assoc]) ε
      (LB.pullGen L φ ε t q) 0 := by
  subst hq
  have gen2 : ∀ {A B : Scheme.{0}} (f : A ⟶ B) (U U' : B.Opens) (hU : U' ≤ U) (W : A.Opens)
      (hW : W ≤ f ⁻¹ᵁ U') (x : Γ(B, U)ˣ),
      res hW (pullU f U' (res hU x)) = res (fun y hy => hU (hW hy) : W ≤ f ⁻¹ᵁ U) (pullU f U x) := by
    intro A B f U U' hU W hW x
    apply Units.ext
    have hm : (B.presheaf.map (homOfLE hU).op ≫ f.app U') ≫ A.presheaf.map (homOfLE hW).op =
        f.app U ≫ A.presheaf.map (homOfLE (fun y hy => hU (hW hy) : W ≤ f ⁻¹ᵁ U)).op := by
      rw [Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
      rfl
    exact congrArg (fun m => m.hom x.val) hm
  have gen4 : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens) (U' : B.Opens)
      (hU' : U' ≤ g ⁻¹ᵁ U) (W : A.Opens) (h1 : W ≤ (f ≫ g) ⁻¹ᵁ U) (h2 : W ≤ f ⁻¹ᵁ U')
      (x : Γ(C, U)ˣ), res h1 (pullU (f ≫ g) U x) = res h2 (pullU f U' (res hU' (pullU g U x))) := by
    intro A B C f g U U' hU' W h1 h2 x
    rw [pullU_comp, gen2]
    rfl
  refine ⟨LB.pullGen L φ ε t p, pullGen_isGen L φ ε t ht p, 1, ⟨1, by simp⟩, fun j => ?_⟩
  simp only [scal, resTop, map_one]
  refine Eq.trans ?_ (one_mul _).symm
  exact congrArg Units.val (gen4 (jK V) p (LB.wchart L φ j) (LB.wchart L (fun k => p ≫ φ k) j) _ _ _ _ (t.s j))

theorem genHasVal_isGen {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) : t.IsGen := by
  obtain rfl : φ' = fun k => jK V ≫ φ k := funext hφ
  obtain ⟨e, he, c, -, hC⟩ := genHasVal_units L φ _ hφ ε t hn
  have hP := pullGen_isGen L φ ε e he (jK V)
  have gen1 : ∀ (W W' : (Spec (CommRingCat.of (FractionRing V))).Opens) (h : W' ≤ W)
      (x : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)),
      ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE h).op).hom (resTop W x) =
        resTop W' x := by
    intro W W' h x
    simp only [resTop]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have key : ∀ {Wi Wj : (Spec (CommRingCat.of (FractionRing V))).Opens} (hl : Wi ⊓ Wj ≤ Wi)
      (hr : Wi ⊓ Wj ≤ Wj)
      (Ti Ci Pi : Γ(Spec (CommRingCat.of (FractionRing V)), Wi)ˣ)
      (Tj Cj Pj : Γ(Spec (CommRingCat.of (FractionRing V)), Wj)ˣ)
      (g : Γ(Spec (CommRingCat.of (FractionRing V)), Wi ⊓ Wj)ˣ)
      (x : Γ(Spec (CommRingCat.of (FractionRing V)), ⊤)),
      Ti = Ci * Pi → Tj = Cj * Pj → Ci.val = resTop Wi x → Cj.val = resTop Wj x →
      res hl Pi = g * res hr Pj → res hl Ti = g * res hr Tj := by
    intro Wi Wj hl hr Ti Ci Pi Tj Cj Pj g x h1 h2 h3 h4 h5
    have hCC : res hl Ci = res hr Cj := by
      have e1 : (res hl Ci).val = resTop (Wi ⊓ Wj) x := by
        rw [← gen1 Wi (Wi ⊓ Wj) hl x, ← h3]
        rfl
      have e2 : (res hr Cj).val = resTop (Wi ⊓ Wj) x := by
        rw [← gen1 Wj (Wi ⊓ Wj) hr x, ← h4]
        rfl
      exact Units.ext (e1.trans e2.symm)
    rw [h1, h2, map_mul, map_mul, hCC, h5]
    exact mul_left_comm _ _ _
  intro i j
  obtain ⟨Ci, hCi1, hCi2⟩ := hC i
  obtain ⟨Cj, hCj1, hCj2⟩ := hC j
  exact key _ _ _ Ci _ _ Cj _ _ _ hCi2 hCj2 hCi1 hCj1 (hP i j)

theorem genHasVal_ge_of_in (hϖ : Irreducible ϖ) {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (x : Spec (CommRingCat.of V) ⟶ X) (x' : Spec (CommRingCat.of (FractionRing V)) ⟶ X) (hx : x' = jK V ≫ x)
    (ε : ℤ) (t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε))) (k : ℕ)
    (hin : ∀ (j : PUnit → L.ι) (W : (Spec (CommRingCat.of V)).Opens), IsAffineOpen W →
      W ≤ x ⁻¹ᵁ L.U (j PUnit.unit) →
      ∀ h : jK V ⁻¹ᵁ W ≤ (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε)).U j,
        ∃ r ∈ (IsLocalRing.maximalIdeal V ^ k).map (DegPre.toOpen W),
          ((jK V).app W).hom r =
            ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE h).op).hom (t.s j).val)
    {n : ℤ} (hn : GenHasVal ϖ L (fun _ => x) (fun _ => x') (fun _ => hx) (fun _ => ε) t n) : (k : ℤ) ≤ n := by
  subst hx
  obtain ⟨j₀, htop⟩ := exists_chart_top L hL (fun _ : PUnit => x) (fun _ => ε)
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun _ : PUnit => jK V ≫ x) j₀ := by
    intro y _
    have hy : (jK V).base y ∈ LB.wchart L (fun _ : PUnit => x) j₀ := by
      rw [htop]
      trivial
    have hy' : (jK V).base y ∈ (⋂ k : PUnit, x.base ⁻¹' (L.U (j₀ k) : Set X)) := hy
    show y ∈ (⋂ k : PUnit, (jK V ≫ x).base ⁻¹' (L.U (j₀ k) : Set X))
    refine Set.mem_iInter.2 fun k => ?_
    have h1 := Set.mem_iInter.1 hy' k
    simpa using h1
  obtain ⟨c, hc, eV, hX⟩ := genHasVal_top L (fun _ : PUnit => x) (fun _ => ε) t hn j₀ htop hK
  have hW : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ x ⁻¹ᵁ L.U (j₀ PUnit.unit) := by
    intro y _
    have hy : y ∈ LB.wchart L (fun _ : PUnit => x) j₀ := by
      rw [htop]
      trivial
    have hy' : y ∈ (⋂ k : PUnit, x.base ⁻¹' (L.U (j₀ k) : Set X)) := hy
    exact Set.mem_iInter.1 hy' PUnit.unit
  obtain ⟨r, hrm, hr⟩ := hin j₀ ⊤ (isAffineOpen_top _) hW (le_top.trans hK)
  have hcomp : ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom).comp
      (DegPre.toOpen (⊤ : (Spec (CommRingCat.of V)).Opens)) = RingHom.id V := by
    ext v
    show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
      (((Spec (CommRingCat.of V)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom v)) = v
    rw [CategoryTheory.Functor.map_id]
    simp
  have hr' : (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r ∈ IsLocalRing.maximalIdeal V ^ k := by
    have h1 := Ideal.mem_map_of_mem ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) hrm
    rwa [Ideal.map_map, hcomp, Ideal.map_id] at h1
  have hval : algebraMap V (FractionRing V) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r) =
      c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hX]
    have e1 := congrArg (fun m => m.hom r)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    exact e1.symm.trans
      (congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom z) hr)
  set r' := (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r with hr'def
  rw [Irreducible.maximalIdeal_eq hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hr'
  obtain ⟨s, hs⟩ := hr'
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hc0 : c * algebraMap V (FractionRing V) (eV : V) ≠ 0 :=
    mul_ne_zero (ne_zero_of_hasVal hϖ hc)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 eV.ne_zero)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hc0
    rw [← hval, hs, mul_zero, map_zero]
  obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have hv1 : HasVal ϖ (algebraMap V (FractionRing V) r') ((k : ℤ) + (m : ℤ)) := by
    refine ⟨w, ?_⟩
    rw [hs, hw, zpow_add₀ hπ, zpow_natCast, zpow_natCast]
    simp only [map_mul, map_pow]
    ring
  have hv2 := hasVal_mul_unit hc eV
  rw [← hval] at hv2
  have h3 := hasVal_unique hϖ hv1 hv2
  omega

end ReciprocityTheory.ChartRestriction.G.DVR
