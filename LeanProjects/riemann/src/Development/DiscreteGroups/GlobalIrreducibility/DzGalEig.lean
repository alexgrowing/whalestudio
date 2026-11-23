import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzLTame
import Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
import Development.DiscreteGroups.GlobalIrreducibility.DzGalFin

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_H_eigen {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn : 0 < n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal)
    (m : ℕ) (b : WDRep h (Fin m → ℂ)) (hb : b.ρ.IsIrreducible)
    (htame : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1) (hm : finrank ℂ (Fin m → ℂ) = n)
    (ξ : Kˣ →* ℂˣ)
    (hξf : ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (WD.mk b).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))) :
    ∃ (v₀ : Fin m → ℂ) (χH : Weil h → ℂ), v₀ ≠ 0 ∧
      (∀ σ : Weil h, (n : ℤ) ∣ deg σ → b.ρ σ v₀ = χH σ • v₀) ∧
      (∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        χH (ineIncl h (resI t)) = ((ξ z : ℂˣ) : ℂ)) ∧
      Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) = ⊤ := by
  classical
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hq' : normV w' = normV w ^ n := by rw [hq, hN]
  let I : Subgroup (Weil h) := (Ine (F := E) A).comap (Weil h).subtype
  haveI hInorm : I.Normal := ⟨fun t ht g0 => by
    show ((g0 * t * g0⁻¹ : Weil h) : G E Ω) ∈ Ine (F := E) A
    exact conj_mem_Ine (Weil_le_Dec h g0.2) ht⟩
  have hgen : ∀ σ : Weil h, ∃ k : ℤ, ∃ t ∈ I, σ = frob h ^ k * t := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    exact ⟨deg σ, ineIncl h τ, τ.2, hτ⟩
  have hcomm : ∀ s ∈ I, ∀ t ∈ I, b.ρ s * b.ρ t = b.ρ t * b.ρ s := by
    intro s hs t ht
    let s' : Ine (F := E) A := ⟨s, hs⟩
    let t' : Ine (F := E) A := ⟨t, ht⟩
    have h1 : b.ρ (ineIncl h (s' * t' * s'⁻¹ * t'⁻¹)) = 1 := htame _ (isWild_commutator s' t')
    have h2 : ineIncl h (s' * t' * s'⁻¹ * t'⁻¹) = s * t * s⁻¹ * t⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have hfrob : ∀ t ∈ I, b.ρ (frob h * t * (frob h)⁻¹) = b.ρ t ^ normV w := by
    intro t ht
    let t' : Ine (F := E) A := ⟨t, ht⟩
    let c' : Ine (F := E) A :=
      ⟨(frob h : G E Ω) * t' * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t'.2⟩
    have h1 : b.ρ (ineIncl h (c' * (t' ^ normV w)⁻¹)) = 1 :=
      htame _ (isWild_frob (isFrob_frob (h := h)) t')
    have h2 : ineIncl h (c' * (t' ^ normV w)⁻¹) = frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : frob h * t * (frob h)⁻¹ = (frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹) * t ^ normV w := by group
    rw [e, map_mul, h1, one_mul, map_pow]
  obtain ⟨η, u, c, hu, huI, hφn, hchar, hper, hmin⟩ :=
    DzCliff.clifford b.ρ hb I (frob h) (normV w) n hm hn hgen hcomm hfrob
  rw [hq] at hchar hper
  have hc0 : c ≠ 0 := fun h0 => DzCliff.rho_ne_zero b.ρ (frob h ^ n) hu (by rw [hφn, h0, zero_smul])
  have hcinv : b.ρ (frob h ^ n)⁻¹ u = c⁻¹ • u := by
    have h1 := DzCliff.rho_inv_apply b.ρ (frob h ^ n) u
    rw [hφn, map_smul] at h1
    calc b.ρ (frob h ^ n)⁻¹ u = c⁻¹ • (c • b.ρ (frob h ^ n)⁻¹ u) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  have hz : ∀ k : ℤ, b.ρ ((frob h ^ n) ^ k) u = c ^ k • u := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hφn, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, hcinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc0,
        mul_comm]
  have huH : ∀ σ : Weil h, (n : ℤ) ∣ deg σ → ∃ e : ℂ, b.ρ σ u = e • u := by
    intro σ hσ
    obtain ⟨k, hk'⟩ := hσ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    rw [hτ, hk', map_mul, Module.End.mul_apply, huI (ineIncl h τ) τ.2, map_smul,
      show frob h ^ ((n : ℤ) * k) = (frob h ^ n) ^ k by rw [zpow_mul, zpow_natCast], hz, smul_smul]
    exact ⟨_, rfl⟩
  obtain ⟨R, hR⟩ := exists_resHom (A := A) ha' hk
  obtain ⟨β, hβ⟩ := exists_eigenChar b.ρ ((ineIncl h).comp (resI (E := E) (E' := E') (Ω := Ω) (A := A))) hu
    (fun t => ⟨_, huI (ineIncl h (resI t)) (resI t).2⟩)
  have hβη : ∀ t : Ine (F := E') A, ((β t : ℂˣ) : ℂ) = η (ineIncl h (resI t)) := fun t =>
    DzCliff.eig_unique hu (hβ t) (huI (ineIncl h (resI t)) (resI t).2)
  have hpos : 0 < g ^ n := pow_pos (Fact.out : g.Prime).pos n
  have hzK : ∀ z : Kˣ, z ^ g ^ n = z := pow_card_units w' g n hN K red hr hk hpos
  have hα : ∀ t, ((ξ.comp R) t) ^ (g ^ n - 1) = 1 := by
    intro t
    rw [MonoidHom.comp_apply, ← map_pow]
    have : R t ^ (g ^ n - 1) = 1 := by
      have h1 := hzK (R t)
      have h2 : R t ^ (g ^ n - 1) * R t = 1 * R t := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos), h1, one_mul]
      exact mul_right_cancel h2
    rw [this, map_one]
  have h1 : ∀ t, ∃ j : ℕ, β t = (ξ.comp R) t ^ g ^ j := by
    intro t
    obtain ⟨x, hx⟩ := exists_int_approx_compl w' _ (val_artin_ine ha' t).le
    have hRx : R t = Units.mk0 (red x) (red_ne_zero_of_approx ha' hk hx) := Units.ext (hR t x hx)
    have hp := hξf t x (R t) (hR t x hx).symm hx
    rw [WD.inePol_of_mem_Ine _ (res_mem_Ine t.2), WD.charPol_mk,
      show ineIncl h ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩ = ineIncl h (resI t) from rfl,
      hchar _ (resI t).2] at hp
    have hroot := congrArg (Polynomial.eval (η (ineIncl h (resI t)))) hp
    rw [Polynomial.eval_prod, Polynomial.eval_prod] at hroot
    have hl : ∏ j ∈ Finset.range n, Polynomial.eval (η (ineIncl h (resI t)))
        (X - C (η (ineIncl h (resI t)) ^ g ^ j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by simp)
    rw [hl, eq_comm, Finset.prod_eq_zero_iff] at hroot
    obtain ⟨j, -, hj⟩ := hroot
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
    refine ⟨j, Units.ext ?_⟩
    rw [hβη, hj, MonoidHom.comp_apply, map_pow, Units.val_pow_eq_pow_val]
  obtain ⟨j₀, hj₀⟩ := char_orbit (ξ.comp R) β (g ^ n - 1) (Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne'
    (Fact.out : g.Prime).one_lt)) hα g h1
  have hαn : ∀ k t, ((ξ.comp R) t) ^ g ^ (k * n) = (ξ.comp R) t := by
    intro k t
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, pow_add, pow_mul, ih, MonoidHom.comp_apply, ← map_pow, hzK]
  set j : ℕ := n - j₀ % n with hj
  have hjn : j₀ + j = n * (j₀ / n + 1) := by
    have := Nat.div_add_mod j₀ n
    have := Nat.mod_lt j₀ hn
    rw [hj]; rw [Nat.mul_add, Nat.mul_one]; omega
  set v₀ := b.ρ (frob h ^ j)⁻¹ u with hv₀
  have hv₀0 : v₀ ≠ 0 := DzCliff.rho_ne_zero b.ρ _ hu
  have hv₀I : ∀ t ∈ I, b.ρ t v₀ = η t ^ g ^ j • v₀ :=
    DzCliff.eig_translate b.ρ I (frob h) g (by rw [← hq]; exact hfrob) huI j
  have hv₀H : ∀ σ : Weil h, ∃ e : ℂ, (n : ℤ) ∣ deg σ → b.ρ σ v₀ = e • v₀ := by
    intro σ
    by_cases hσ : (n : ℤ) ∣ deg σ
    · have hdeg : (n : ℤ) ∣ deg (frob h ^ j * σ * (frob h ^ j)⁻¹) := by simpa using hσ
      obtain ⟨e, he⟩ := huH _ hdeg
      refine ⟨e, fun _ => ?_⟩
      have e1 : σ * (frob h ^ j)⁻¹ = (frob h ^ j)⁻¹ * (frob h ^ j * σ * (frob h ^ j)⁻¹) := by group
      rw [hv₀, ← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply, he, map_smul]
    · exact ⟨0, fun h0 => absurd h0 hσ⟩
  choose χH hχH using hv₀H
  refine ⟨v₀, χH, hv₀0, fun σ hσ => hχH σ hσ, fun t x z hxz hx => ?_, ?_⟩
  · have hRz : R t = z := Units.ext (by rw [hR t x hx, hxz])
    have e1 := hχH (ineIncl h (resI t)) (by simp)
    have e2 := hv₀I (ineIncl h (resI t)) (resI t).2
    rw [DzCliff.eig_unique hv₀0 e1 e2, ← hβη]
    have h3 := hj₀ t
    have h4 : β t ^ g ^ j = (ξ.comp R) t := by
      rw [h3, ← pow_mul, ← pow_add, hjn, mul_comm, hαn]
    have h5 := congrArg Units.val h4
    rw [Units.val_pow_eq_pow_val] at h5
    rw [h5, MonoidHom.comp_apply, hRz]
  · apply DzCliff.eq_top_of_stable b.ρ hb
    · intro h0
      have hmem : b.ρ 1 v₀ ∈ Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) := Submodule.subset_span ⟨1, rfl⟩
      rw [h0, map_one, Module.End.one_apply, Submodule.mem_bot] at hmem
      exact hv₀0 hmem
    · intro τ v hv
      have hle : Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) ≤
          (Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀)).comap (b.ρ τ) := by
        rw [Submodule.span_le]
        rintro _ ⟨σ, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
        exact Submodule.subset_span ⟨τ * σ, rfl⟩
      exact hle hv

end DiscreteGroups.sglob.DzType

end
