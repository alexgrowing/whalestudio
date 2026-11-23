import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplication
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryOfConjugateSplitPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeLinearMapConjugateSplitPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjSplitIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nsmul_cancel {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) {N : ℕ} (hN : 0 < N) {u u' : D.La} (h : N • u = N • u') : u = u' := by
  apply hP.2.1
  have h' := congrArg P h
  rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h'
  exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') h'

theorem form_nsmul_nsmul (D : Datum H) (N : ℕ) (x y : D.La) : D.EF (N • x) (N • y) = (N * N : ℤ) * D.EF x y := by
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  ring

end GlobalTheory.ConjSplitIndex

namespace GlobalTheory.CompRat

open ConjIsometry in

theorem exists_isometry_of_conj_split_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P') (N : ℕ), 0 < N → (∀ v : (F.Di i).La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → C.ActsBy τ io N (1, 0) → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) ∧ (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) ∧ ∀ n : ℕ, 0 < n → C.ActsBy τ io (N * n) (1, 0) → ∀ v, spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P v)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ v))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' N hN hNv hu hAN
  obtain ⟨f, hadd, hw, -, hact, hf⟩ := GlobalTheory.ConjSplit.exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := GlobalTheory.ConjSplitAnyLevel.exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε
    refine ⟨Φ, hΦ, fun n s hA a => ?_⟩
    rw [smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex,
      GlobalTheory.ConjSplit.ex_congr_type F hP ε a.2 (hact n s hA), one_div]
  obtain ⟨Φp, hp, tp⟩ := key 1 H.rt0 (by simp)
  obtain ⟨Φm, hm, tm⟩ := key (-1) (-H.rt0) (by simp)
  have hd := Submodule.disjoint_def.1 (disjoint_lat hP (GlobalTheory.ConjSplit.rt0_ne_neg (H := H)))

  have hsum : ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      U ≫ F.ex i P ((n : ℂ)⁻¹ • P (a.1 + b.1)) =
        F.ex i' P' ((n : ℂ)⁻¹ • P' (Φp (wE H s • a) + Φm (H.bar (wE H s) • b))) := by
    intro n s hA a b
    rw [map_smul, map_smul, map_add P', GlobalTheory.ConjSplit.period_wE hP' (hp a),
      GlobalTheory.ConjSplit.period_bar_wE hP' (hm b), smul_add, F.ex_add i' P' hP', ← tp n s hA, ← tm n s hA,
      ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]
  have hsum1 : ∀ n : ℕ, C.ActsBy τ io n (1, 0) → ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      U ≫ F.ex i P ((n : ℂ)⁻¹ • P (a.1 + b.1)) = F.ex i' P' ((n : ℂ)⁻¹ • P' (Φp a + Φm b)) := by
    intro n hA a b
    rw [hsum n (1, 0) hA a b]
    simp [wE]

  have hiso₀ : ∀ (a a' : lat hP H.rt0) (b b' : lat hP (-H.rt0)),
      (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') = (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1) := by
    intro a a' b b'
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') - (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1) := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.CompRat.Acts.main E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (congrArg (fun m => m.left) (hsum n s hs a b))
        (congrArg (fun m => m.left) (hsum n s hs a' b'))
      have hM := GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = M at hM hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = M := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP' H.rt0, ∀ v ∈ lat hP' (-H.rt0),
          (F.Di i').EF u v = 0 ∧ (F.Di i').EF v u = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' hu hv
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φp (wE H s • a) + Φm (H.bar (wE H s) • b)) (Φp (wE H s • a') + Φm (H.bar (wE H s) • b')) =
          M * (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') := by
        simp only [map_add, LinearMap.add_apply]
        rw [(o _ (hp _) _ (hm _)).1, (o _ (hp _) _ (hm _)).2, (o _ (hp a) _ (hm b')).1, (o _ (hp a') _ (hm b)).2,
          map_smul Φp, map_smul Φp, map_smul Φm, map_smul Φm, form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hM] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') - (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1)).natAbs + 1)
      (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this
      (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hdec : ∀ v, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v := fun v => by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hNv v)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
  have huniq : ∀ (a a' : lat hP H.rt0) (b b' : lat hP (-H.rt0)), a.1 + b.1 = a'.1 + b'.1 → a = a' ∧ b = b' := by
    intro a a' b b' h
    have e : a.1 - a'.1 = b'.1 - b.1 := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have z : a.1 - a'.1 = 0 := hd _ (sub_mem a.2 a'.2) (e ▸ sub_mem b'.2 b.2)
    exact ⟨Subtype.ext (sub_eq_zero.1 z), Subtype.ext (sub_eq_zero.1 (e ▸ z)).symm⟩
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hdiv : ∀ v, ∃ u : (F.Di i').La, ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v →
      Φp a + Φm b = N • u := by
    intro v
    obtain ⟨a, b, hab⟩ := hdec v
    have e := hsum1 N hAN a b
    rw [hab, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hNc, (F.ex_ker i P hP _).2 ⟨v, rfl⟩,
      MonObj.comp_one] at e
    obtain ⟨u, hu'⟩ := (F.ex_ker i' P' hP' _).1 e.symm
    refine ⟨u, fun a' b' h => ?_⟩
    obtain ⟨rfl, rfl⟩ := huniq a a' b b' (hab.trans h.symm)
    apply hP'.2.1
    rw [map_nsmul, hu', ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hNc]
  choose Ψ hΨ using hdiv
  let Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La :=
    { toFun := Ψ
      map_add' := fun v w => by
        obtain ⟨a, b, hab⟩ := hdec v
        obtain ⟨a', b', hab'⟩ := hdec w
        refine GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN ?_
        rw [smul_add, ← hΨ v a b hab, ← hΨ w a' b' hab', ← hΨ (v + w) (a + a') (b + b')
          (by rw [smul_add, ← hab, ← hab', Submodule.coe_add, Submodule.coe_add]; abel), map_add, map_add]
        abel
      map_smul' := fun c v => by
        obtain ⟨a, b, hab⟩ := hdec v
        refine GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN ?_
        rw [RingHom.id_apply, smul_comm N c, ← hΨ v a b hab, ← hΨ (c • v) (c • a) (c • b)
          (by rw [smul_comm N c, ← hab, Submodule.coe_smul, Submodule.coe_smul, smul_add]), map_smul, map_smul,
          smul_add] }
  have hΦ : ∀ v (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v → Φp a + Φm b = N • Φ v := hΨ
  have hiso : ∀ v w, (F.Di i').EF (Φ v) (Φ w) = (F.Di i).EF v w := by
    intro v w
    obtain ⟨a, b, hab⟩ := hdec v
    obtain ⟨a', b', hab'⟩ := hdec w
    have e := hiso₀ a a' b b'
    rw [hΦ v a b hab, hΦ w a' b' hab', hab, hab', GlobalTheory.ConjSplitIndex.form_nsmul_nsmul,
      GlobalTheory.ConjSplitIndex.form_nsmul_nsmul] at e
    have hz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact mul_left_cancel₀ (mul_ne_zero hz hz) e
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero _).2 fun v hv =>
    (F.Di i).unimod.1 (by
      ext z
      rw [← hiso, hv]; simp)
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, fun a ha => ?_, fun b hb => ?_, fun n hn hA v => ?_⟩
  · have e := hΦ a (N • ⟨a, ha⟩) 0 (by simp)
    rw [map_zero, add_zero, map_nsmul] at e
    show Φ a ∈ _
    rw [← GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN e]
    exact hp _
  · have e := hΦ b 0 (N • ⟨b, hb⟩) (by simp)
    rw [map_zero, zero_add, map_nsmul] at e
    show Φ b ∈ _
    rw [← GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN e]
    exact hm _
  · obtain ⟨a, b, hab⟩ := hdec v
    have e := hsum1 (N * n) hA a b
    have hc : ∀ x : Fin g → ℂ, ((N * n : ℕ) : ℂ)⁻¹ • N • x = (n : ℂ)⁻¹ • x := fun x => by
      rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_mul, mul_inv_rev, mul_smul, inv_smul_smul₀ hNc]
    rw [hΦ v a b hab, hab, map_nsmul, map_nsmul, hc, hc] at e
    exact congrArg (fun m => m.left) e

end GlobalTheory.CompRat
