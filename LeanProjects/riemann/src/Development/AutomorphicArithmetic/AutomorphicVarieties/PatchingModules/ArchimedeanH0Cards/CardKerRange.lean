import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles

open ReciprocityTheory.Gal UpperTheory.V.Pa UpperTheory.V.Pa.B2

noncomputable section

namespace UpperTheory.V.Pa.B2

private theorem card_ker_range {A X Y : Type} [CommRing A] [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (f : X →ₗ[A] Y) : Nat.card X = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]

private theorem inj_of {A X Y Z : Type} [CommRing A] [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [AddCommGroup Z] [Module A Z] (q : X →ₗ[A] Y) (b : X →ₗ[A] Z) (K : Submodule A Z)
    (h1 : ∀ x, q x = 0 → b x = 0) (h2 : ∀ z ∈ K, ∃ x, b x = z) :
    ∃ f : K → Y, Function.Injective f := by
  choose s hs using h2
  refine ⟨fun z => q (s z.1 z.2), fun z z' hzz => ?_⟩
  have h := h1 (s z.1 z.2 - s z'.1 z'.2) (by rw [map_sub]; exact sub_eq_zero.2 hzz)
  rw [map_sub, hs, hs, sub_eq_zero] at h
  exact Subtype.ext h

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} (D : Dat A P)

private abbrev Tq : Type := ∀ w, H1 (D.Q w).ρ ⧸ H1ur (D.Q w).ρ (P.J w)

private def aMap : H1 D.M.ρ →ₗ[A] Tq D :=
  LinearMap.pi fun w => (H1ur (D.Q w).ρ (P.J w)).mkQ.comp (D.loc1 w)

private theorem ker_aMap : LinearMap.ker (aMap D) = D.Sel := by
  ext c
  simp only [LinearMap.mem_ker, Dat.Sel, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro h w
    have := congrFun h w
    simpa [aMap, Submodule.Quotient.mk_eq_zero] using this
  · intro h
    funext w
    simp [aMap, h w]

private def qMap : (∀ w, Z1 (D.Q w).ρ) →ₗ[A] Tq D ⧸ LinearMap.range (aMap D) :=
  (LinearMap.range (aMap D)).mkQ.comp (LinearMap.pi fun w =>
    (H1ur (D.Q w).ρ (P.J w)).mkQ.comp ((Submodule.mkQ _).comp (LinearMap.proj w)))

private def bZ : (∀ w, Z1 (D.Q w).ρ) →ₗ[A] D.selmerSecondCocycles where
  toFun y := ⟨(0, fun w => (y w).1), zero_mem _, fun w => ⟨(y w).2.1, fun g h => by
    simp [(y w).2.2]⟩⟩
  map_add' y y' := by ext <;> simp
  map_smul' c y := by ext <;> simp

private def bMap : (∀ w, Z1 (D.Q w).ρ) →ₗ[A] D.H2LocalConditions := (Submodule.mkQ _).comp (bZ D)

private def cZ : D.selmerSecondCocycles →ₗ[A] Z2 D.M.ρ where
  toFun p := ⟨p.1.1, p.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def cMap : D.H2LocalConditions →ₗ[A] H2 D.M.ρ :=
  Submodule.mapQ _ _ (cZ D) (by
    rintro p ⟨x, a1, a2, -⟩
    exact ⟨x, a1, a2.symm⟩)

private theorem range_cMap : LinearMap.range (cMap D) ≤ LinearMap.ker D.loc2 := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker]
  funext w
  simp only [cMap, Dat.loc2, LinearMap.pi_apply, compatiblePairH2, Submodule.mapQ_apply, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, separated_dvr_second_cohomology_mem]
  refine ⟨p.1.2 w, (p.2.2 w).1, ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  exact ((p.2.2 w).2 g h).symm

private theorem ker_qMap (y : ∀ w, Z1 (D.Q w).ρ) (hy : qMap D y = 0) : bMap D y = 0 := by
  simp only [qMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨c, hc⟩ := hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hw : ∀ w, ∃ Y, ∀ g ∈ P.J w, (y w).1 g - D.π w (x.1 (P.φ w g)) = (D.Q w).ρ g Y - Y := by
    intro w
    have e := congrFun hc w
    simp only [aMap, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.proj_apply, Dat.loc1, pairH1DecompositionMap, Submodule.mapQ_apply] at e
    rw [Submodule.Quotient.eq, ← Submodule.Quotient.mk_sub, H1ur, LinearMap.mem_ker] at e
    simp only [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at e
    obtain ⟨m, hm⟩ := e
    refine ⟨-m, fun g hg => ?_⟩
    have h3 := hm ⟨g, hg⟩
    change D.π w (x.1 (P.φ w g)) - (y w).1 g = (D.Q w).ρ g m - m at h3
    rw [map_neg, ← neg_sub (D.π w (x.1 (P.φ w g))) ((y w).1 g), h3]
    abel
  choose Y hY using hw
  simp only [bMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  refine ⟨x.1, x.2.1, ?_, fun w => ⟨sub_mem (y w).2
    (compatiblePairCocycles1 D.M.ρ (D.Q w).ρ (P.φ w) (P.cont w) (D.π w) continuous_of_discreteTopology (D.equiv w) x).2,
    Y w, hY w⟩⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [d1_apply, x.2.2 g h]
  show (0 : D.M.X) = _
  abel

private theorem ker_cMap (z : D.H2LocalConditions) (hz : z ∈ LinearMap.ker (cMap D)) : ∃ y, bMap D y = z := by
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker] at hz
  simp only [cMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, separated_dvr_second_cohomology_mem] at hz
  obtain ⟨x, hx, hdx⟩ := hz
  have hyZ : ∀ w, (p.1.2 w - fun g => D.π w (x (P.φ w g))) ∈ Z1 (D.Q w).ρ := by
    intro w
    refine ⟨(p.2.2 w).1.sub ((continuous_of_discreteTopology (f := D.π w)).comp (hx.comp (P.cont w))),
      fun g h => ?_⟩
    have e' : D.π w (d1 D.M.ρ x (P.φ w g, P.φ w h)) = d1 (D.Q w).ρ (p.1.2 w) (g, h) := by
      rw [hdx]
      exact (p.2.2 w).2 g h
    rw [d1_apply, d1_apply, ← (P.φ w).map_mul g h] at e'
    simp only [map_sub, map_add, D.equiv] at e'
    simp only [Pi.sub_apply, map_sub]
    rw [← sub_eq_zero] at e' ⊢
    rw [← e']
    abel
  refine ⟨fun w => ⟨_, hyZ w⟩, ?_⟩
  simp only [bMap, LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  refine ⟨-x, hx.neg, ?_, fun w => ?_⟩
  · rw [map_neg, hdx]
    exact zero_sub _
  · show ((p.1.2 w - fun g => D.π w (x (P.φ w g))) - p.1.2 w) - (fun g => D.π w ((-x) (P.φ w g))) ∈ D.abelian₂ w
    convert zero_mem (D.abelian₂ w) using 1
    funext g
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, map_neg]
    abel

end UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.count :
    ∀ (A Γ : Type) [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (P : Pl Γ) (D : Dat A P) (s : ℕ) (dw e : P.ι → ℕ), 0 < s → Finite (H1 D.M.ρ) → Finite (H2 D.M.ρ) → (∀ w, Finite (H1 (D.Q w).ρ) ∧ Finite (H2 (D.Q w).ρ)) → Nat.card (H2 D.M.ρ) * s ^ (∑ w, dw w) ≤ Nat.card (H1 D.M.ρ) → (∀ w, Nat.card (H1 (D.Q w).ρ) ≤ Nat.card (H1ur (D.Q w).ρ (P.J w)) * Nat.card (H2 (D.Q w).ρ) * e w * s ^ dw w) → Finite D.H2LocalConditions ∧ Nat.card D.H2LocalConditions ≤ Nat.card D.Sel * (∏ w, e w) * Nat.card D.Ck2 := by
  intro A Γ _ _ _ _ P D s dw e hs hH1 hH2 hQ hM hW
  haveI : ∀ w, Finite (H1 (D.Q w).ρ) := fun w => (hQ w).1
  haveI : ∀ w, Finite (H2 (D.Q w).ρ) := fun w => (hQ w).2
  haveI : ∀ w, Finite (H1 (D.Q w).ρ ⧸ H1ur (D.Q w).ρ (P.J w)) := fun w =>
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  haveI : Finite (Tq D) := Pi.finite
  haveI : Finite (Tq D ⧸ LinearMap.range (aMap D)) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  obtain ⟨ψ, hψ⟩ := inj_of (qMap D) (bMap D) (LinearMap.ker (cMap D)) (ker_qMap D) (ker_cMap D)
  haveI : Finite (LinearMap.ker (cMap D)) := Finite.of_injective ψ hψ
  have hK : Nat.card (LinearMap.ker (cMap D)) ≤ Nat.card (Tq D ⧸ LinearMap.range (aMap D)) :=
    Nat.card_le_card_of_injective ψ hψ
  have hR : Nat.card (LinearMap.range (cMap D)) ≤ Nat.card (LinearMap.ker D.loc2) :=
    Nat.card_le_card_of_injective (Submodule.inclusion (range_cMap D)) (Submodule.inclusion_injective _)
  have hH := card_ker_range (cMap D)
  have hA := card_ker_range (aMap D)
  rw [ker_aMap] at hA
  have hL := card_ker_range D.loc2
  have hT := Submodule.card_eq_card_quotient_mul_card (LinearMap.range (aMap D))
  have hP : Nat.card (∀ w, H2 (D.Q w).ρ) = Nat.card (LinearMap.range D.loc2) * Nat.card D.Ck2 :=
    Submodule.card_eq_card_quotient_mul_card _
  have hTq : Nat.card (Tq D) ≤ Nat.card (∀ w, H2 (D.Q w).ρ) * (∏ w, e w) * s ^ (∑ w, dw w) := by
    show Nat.card (∀ w, H1 (D.Q w).ρ ⧸ H1ur (D.Q w).ρ (P.J w)) ≤ _
    rw [Nat.card_pi, Nat.card_pi, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro w _
    have h1 := Submodule.card_eq_card_quotient_mul_card (H1ur (D.Q w).ρ (P.J w))
    have hpos : 0 < Nat.card (H1ur (D.Q w).ρ (P.J w)) := Nat.card_pos
    have h2 := hW w
    rw [h1, mul_assoc, mul_assoc] at h2
    rw [mul_assoc]
    exact Nat.le_of_mul_le_mul_left h2 hpos
  have key : ∀ a r q kl sel ra rl ck t pq E S h1 h2 nH : ℕ, nH = a * r → a ≤ q → r ≤ kl →
      h1 = sel * ra → h2 = kl * rl → t = ra * q → pq = rl * ck → t ≤ pq * E * S → h2 * S ≤ h1 →
      0 < h1 → 0 < pq → nH ≤ sel * E * ck := by
    intro a r q kl sel ra rl ck t pq E S h1 h2 nH en haq hrk e1 e2 et ep htp hhs p1 p2
    subst en e1 e2 et ep
    have hmain : a * r * ((sel * ra) * (rl * ck)) ≤ sel * E * ck * ((sel * ra) * (rl * ck)) := by
      calc a * r * ((sel * ra) * (rl * ck)) ≤ q * kl * ((sel * ra) * (rl * ck)) := by gcongr
        _ = (ra * q) * sel * (kl * rl) * ck := by ring
        _ ≤ (rl * ck * E * S) * sel * (kl * rl) * ck := by gcongr
        _ = rl * ck * E * sel * ck * (kl * rl * S) := by ring
        _ ≤ rl * ck * E * sel * ck * (sel * ra) := by gcongr
        _ = sel * E * ck * ((sel * ra) * (rl * ck)) := by ring
    exact Nat.le_of_mul_le_mul_right hmain (Nat.mul_pos p1 p2)
  have hpos : 0 < Nat.card D.H2LocalConditions := by
    rw [hH]
    exact Nat.mul_pos Nat.card_pos Nat.card_pos
  exact ⟨Nat.finite_of_card_ne_zero hpos.ne',
    key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH hK hR hA hL hT hP hTq hM Nat.card_pos Nat.card_pos⟩
