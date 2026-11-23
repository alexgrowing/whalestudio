import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.TameRel

section Abstract

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

omit [IsTopologicalGroup Γ] in

theorem hom_trivial {l : ℕ} (hU : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → U.index.Coprime l)
    {C : Type} [Group C] (f : Γ →* C) (hf : IsOpen (f.ker : Set Γ)) (n : ℕ) (hC : ∀ x : C, x ^ l ^ n = 1) (j : Γ) :
    f j = 1 := by
  have h1 : f j ^ f.ker.index = 1 := by
    rw [← map_pow]
    exact f.ker.pow_index_mem j
  have h2 := (hU _ inferInstance hf).pow_right n
  have h3 := pow_gcd_eq_one.2 ⟨h1, hC (f j)⟩
  rwa [h2, pow_one] at h3

omit [IsTopologicalGroup Γ] in

theorem vanish_of_additive {l : ℕ} {J : Subgroup Γ}
    (hU : ∀ U : Subgroup J, U.Normal → IsOpen (U : Set J) → U.index.Coprime l)
    (K : Type) [Field K] [CharP K l] {W : Type} [AddCommGroup W] [Module K W] (w : Γ → W) (hw : IsLocallyConstant w)
    (hadd : ∀ g ∈ J, ∀ h ∈ J, w (g * h) = w g + w h) : ∀ j ∈ J, w j = 0 := by
  intro j hj
  let f : J →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  have hf : IsOpen (f.ker : Set J) := (hw {0}).preimage continuous_subtype_val
  refine hom_trivial hU f hf 1 (fun x => ?_) ⟨j, hj⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, pow_one, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul, toAdd_one]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in

theorem additive_zpow {D : Subgroup Γ} {W : Type} [AddCommGroup W] (w : Γ → W)
    (hadd : ∀ g ∈ D, ∀ h ∈ D, w (g * h) = w g + w h) {γ : Γ} (hγ : γ ∈ D) (k : ℤ) : w (γ ^ k) = k • w γ := by
  let f : D →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  exact congrArg Multiplicative.toAdd (map_zpow f ⟨γ, hγ⟩ k)

theorem vanish_closure {D J : Subgroup Γ} (hJ : J ≤ D) {W : Type} [AddCommGroup W] (w : Γ → W) (hw : IsLocallyConstant w)
    (hadd : ∀ g ∈ D, ∀ h ∈ D, w (g * h) = w g + w h) {γ : Γ} (hγ : γ ∈ D) (h0 : w γ = 0) (h1 : ∀ j ∈ J, w j = 0) :
    ∀ σ ∈ (Subgroup.zpowers γ ⊔ J).topologicalClosure, w σ = 0 := by
  let f : D →* Multiplicative W := MonoidHom.mk' (fun g => Multiplicative.ofAdd (w g)) fun a b => by
    rw [← ofAdd_add, ← hadd a a.2 b b.2]; rfl
  have hle : Subgroup.zpowers γ ⊔ J ≤ f.ker.map D.subtype := by
    refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨γ, hγ⟩, ?_, rfl⟩) fun j hj => ⟨⟨j, hJ hj⟩, ?_, rfl⟩
    · exact congrArg Multiplicative.ofAdd h0
    · exact congrArg Multiplicative.ofAdd (h1 j hj)
  have hsub : ((Subgroup.zpowers γ ⊔ J : Subgroup Γ) : Set Γ) ⊆ {x | w x = 0} := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hle hx
    exact congrArg Multiplicative.toAdd hy
  intro σ hσ
  exact closure_minimal hsub (hw.isClosed_fiber 0) hσ

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in

theorem second_pow {D : Subgroup Γ} {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] (z0 z1 : Γ → W)
    (lam : Γ → K) (hlam : ∀ g ∈ D, ∀ h ∈ D, lam (g * h) = lam g + lam h)
    (h1 : ∀ g ∈ D, ∀ h ∈ D, z1 (g * h) = z1 g + z1 h + lam g • z0 h) (h01 : z0 1 = 0) {γ : Γ} (hγ : γ ∈ D) (n : ℕ) :
    z1 (γ ^ n) = (n : K) • z1 γ + ((n.choose 2 : ℕ) : K) • lam γ • z0 γ := by
  induction n with
  | zero =>
    have := h1 1 D.one_mem 1 D.one_mem
    rw [mul_one, h01, smul_zero, add_zero] at this
    simpa using this
  | succ n ih =>
    have e : lam (γ ^ n) = (n : K) * lam γ := by
      have := additive_zpow lam hlam hγ n
      rwa [zpow_natCast, zsmul_eq_mul, Int.cast_natCast] at this
    rw [pow_succ, h1 _ (D.pow_mem hγ n) _ hγ, ih, e, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast
    module

end Abstract

theorem cast_of_mod {K : Type} [Field K] {l M q : ℕ} [CharP K l] (hM : 1 ≤ M) (hq : q % (2 * l ^ M) = 1) :
    (q : K) = 1 ∧ ((q.choose 2 : ℕ) : K) = 0 := by
  have h := Nat.div_add_mod q (2 * l ^ M)
  rw [hq] at h
  generalize q / (2 * l ^ M) = t at h
  have hl : ((l ^ M : ℕ) : K) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero K l, zero_pow (by omega)]
  refine ⟨?_, ?_⟩
  · rw [← h, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hl]
    simp
  · have : q.choose 2 = q * (l ^ M * t) := by
      rw [Nat.choose_two_right]
      have : q - 1 = 2 * (l ^ M * t) := by rw [← h, Nat.add_sub_cancel, mul_assoc]
      rw [this, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this, Nat.cast_mul, Nat.cast_mul, hl]
    simp

theorem tame_relation : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → 1 ≤ M → normV v % (2 * l ^ M) = 1 → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → (∀ c, ∃ σ ∈ Ine (F := F) A, d σ = c) → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∃ γ ∈ Ine (F := F) A, d γ = Multiplicative.ofAdd 1 ∧ ∀ (K : Type) [Field K] [CharP K l] (W : Type) [AddCommGroup W] [Module K W] (z0 : G F Ω → W), IsLocallyConstant z0 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z0 (g * h) = z0 g + z0 h) → (z0 γ = 0 → ∀ σ ∈ Ine (F := F) A, z0 σ = 0) ∧ ∀ (lam : G F Ω → K) (z1 : G F Ω → W), IsLocallyConstant lam → IsLocallyConstant z1 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, lam (g * h) = lam g + lam h) → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z1 (g * h) = z1 g + z1 h + lam g • z0 h) → lam γ • z0 φ = lam φ • z0 γ := by
  intro hT F Ω _ _ _ _ _ l _ M A v hA hl hM hq d hd hsurj φ hφ
  obtain ⟨-, -, hU, -, ⟨γ0, hγ0⟩, hrel⟩ := hT F Ω l A v hA hl
  have hID : Ine (F := F) A ≤ Dec (F := F) A := fun σ hσ => hσ.1
  have hJI := GlobalTheory.TameQuot.ineKer_le_Ine (F := F) A l
  have hJD := hJI.trans hID
  have hγD : γ0 ∈ Dec (F := F) A := hID hγ0.1
  have hφD : φ ∈ Dec (F := F) A := hφ.1
  have hdJ : ∀ j ∈ GlobalTheory.TameQuot.ineKer F A l, d j = 1 := fun j hj => by
    refine hom_trivial hU (d.comp (GlobalTheory.TameQuot.ineKer F A l).subtype) (hd.preimage continuous_subtype_val) M
      (fun x => ?_) ⟨j, hj⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, toAdd_one]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, d γ0 ^ k = Multiplicative.ofAdd 1 := by
    obtain ⟨σ, hσ, hσd⟩ := hsurj (Multiplicative.ofAdd 1)
    have ho : IsOpen (((Subgroup.zpowers (d γ0)).comap d : Subgroup (G F Ω)) : Set (G F Ω)) :=
      Subgroup.isOpen_mono (H₁ := d.ker) (fun x hx => by
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]; exact Subgroup.one_mem _) hd
    have hle : (Subgroup.zpowers γ0 ⊔ GlobalTheory.TameQuot.ineKer F A l).topologicalClosure ≤
        (Subgroup.zpowers (d γ0)).comap d := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ fun j hj => ?_) (Subgroup.isClosed_of_isOpen _ ho)
      · exact Subgroup.zpowers_le.2 (Subgroup.mem_zpowers _)
      · rw [Subgroup.mem_comap, hdJ j hj]; exact Subgroup.one_mem _
    obtain ⟨k, hk⟩ := hle (hγ0.2 hσ)
    exact ⟨k, hk.trans hσd⟩
  refine ⟨γ0 ^ k, Subgroup.zpow_mem _ hγ0.1 k, by rw [map_zpow, hk], ?_⟩
  intro K _ _ W _ _ z0 hz0 hadd0
  have hkK : (k : K) ≠ 0 := by
    intro h0
    have h1 : (k : ZMod (l ^ M)) * (d γ0).toAdd = 1 := by
      have := congrArg Multiplicative.toAdd hk
      rwa [toAdd_zpow, zsmul_eq_mul] at this
    have h2 := congrArg (ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) K) h1
    rw [map_mul, map_intCast, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  have hz0J := vanish_of_additive hU K z0 hz0 fun g hg h hh => hadd0 g (hJD hg) h (hJD hh)
  have e0 : z0 (γ0 ^ k) = (k : K) • z0 γ0 := by rw [additive_zpow z0 hadd0 hγD, Int.cast_smul_eq_zsmul]
  refine ⟨fun h σ hσ => ?_, fun lam z1 hlam hz1 haddl hadd1 => ?_⟩
  · rw [e0] at h
    exact vanish_closure hJD z0 hz0 hadd0 hγD ((smul_eq_zero.1 h).resolve_left hkK) hz0J σ (hγ0.2 hσ)
  · have hlJ := vanish_of_additive hU K lam hlam fun g hg h hh => haddl g (hJD hg) h (hJD hh)
    have hz1J := vanish_of_additive hU K z1 hz1 fun g hg h hh => by
      rw [hadd1 g (hJD hg) h (hJD hh), hz0J h hh, smul_zero, add_zero]
    have el : lam (γ0 ^ k) = (k : K) * lam γ0 := by rw [additive_zpow lam haddl hγD, zsmul_eq_mul]
    obtain ⟨hq1, hq2⟩ := cast_of_mod (K := K) hM hq
    have hj : (γ0 ^ normV v)⁻¹ * (φ * γ0 * φ⁻¹) ∈ GlobalTheory.TameQuot.ineKer F A l :=
      (hrel ⟨φ, hφD⟩ ⟨γ0, hγD⟩ hφ hγ0).2.1
    generalize hjj : (γ0 ^ normV v)⁻¹ * (φ * γ0 * φ⁻¹) = j at hj
    have hmul : φ * γ0 = γ0 ^ normV v * j * φ := by rw [← hjj]; group
    have hp : γ0 ^ normV v ∈ Dec (F := F) A := Subgroup.pow_mem _ hγD _
    have a1 := hadd1 φ hφD γ0 hγD
    have a2 : z1 (γ0 ^ normV v) = z1 γ0 := by
      rw [second_pow z0 z1 lam haddl hadd1 (hz0J 1 (Subgroup.one_mem _)) hγD, hq1, hq2, one_smul, zero_smul, add_zero]
    have a3 : lam (γ0 ^ normV v) = lam γ0 := by
      have := additive_zpow lam haddl hγD (normV v)
      rwa [zpow_natCast, zsmul_eq_mul, Int.cast_natCast, hq1, one_mul] at this
    rw [hmul, hadd1 _ (Subgroup.mul_mem _ hp (hJD hj)) φ hφD, hadd1 _ hp j (hJD hj), haddl _ hp j (hJD hj), a2, a3,
      hz0J j hj, hz1J j hj, hlJ j hj, smul_zero, add_zero, add_zero, add_zero, add_comm (z1 φ), add_right_inj] at a1
    rw [el, e0, mul_smul, a1, smul_comm]

end GlobalTheory.TameRel
