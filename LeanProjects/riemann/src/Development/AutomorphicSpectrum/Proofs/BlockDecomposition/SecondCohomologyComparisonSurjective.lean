import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfectSecondCohomology

section Alg

variable {R : Type} [CommRing R] {A₀ A₁ A₂ D₀ D₁ D₂ : Type}
  [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂]
  [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁] [Module R D₁] [AddCommGroup D₂] [Module R D₂]
  (k : Type) [AddCommGroup k] [Module R k]

theorem mem_range_of_closed (a : A₀ →ₗ[R] A₁) (b : A₁ →ₗ[R] A₂) (d : D₀ →ₗ[R] D₁) (d' : D₁ →ₗ[R] D₂)
    (ψ : A₁ →ₗ[R] D₁) (ψ' : A₂ →ₗ[R] D₂) (hψ : ψ' ∘ₗ b = d' ∘ₗ ψ) (S : Submodule R A₁)
    (haS : LinearMap.range a ≤ S) (hSb : S ≤ LinearMap.ker b)
    (hq : ∀ x, b.lTensor k x = 0 → (∃ y, d.lTensor k y = ψ.lTensor k x) → ∃ y, a.lTensor k y = x)
    (hs : ∀ z, d'.lTensor k z = 0 → ∃ (s : k ⊗[R] S) (y : k ⊗[R] D₀),
      ψ.lTensor k (S.subtype.lTensor k s) - z = d.lTensor k y)
    (x : k ⊗[R] A₁) (hx : b.lTensor k x = 0) : x ∈ LinearMap.range (S.subtype.lTensor k) := by
  have hbS : b ∘ₗ S.subtype = 0 := LinearMap.ext fun s ↦ hSb s.2
  have hbS' : ∀ s, b.lTensor k (S.subtype.lTensor k s) = 0 := fun s ↦ by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hbS, LinearMap.lTensor_zero]; rfl
  have hz : d'.lTensor k (ψ.lTensor k x) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← hψ, LinearMap.lTensor_comp,
      LinearMap.comp_apply, hx, map_zero]
  obtain ⟨s, y, hy⟩ := hs _ hz
  obtain ⟨u, hu⟩ := hq (S.subtype.lTensor k s - x) (by rw [map_sub, hbS', hx, sub_zero])
    ⟨y, by rw [map_sub, hy]⟩
  let a' : A₀ →ₗ[R] S := a.codRestrict S fun v ↦ haS ⟨v, rfl⟩
  have ha' : S.subtype ∘ₗ a' = a := LinearMap.ext fun _ ↦ rfl
  refine ⟨s - a'.lTensor k u, ?_⟩
  rw [map_sub, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ha', hu]
  abel

theorem lTensor_liftQ_injective (b : A₁ →ₗ[R] A₂) (S : Submodule R A₁) (hSb : S ≤ LinearMap.ker b)
    (h : ∀ x, b.lTensor k x = 0 → x ∈ LinearMap.range (S.subtype.lTensor k)) :
    Function.Injective ((S.liftQ b hSb).lTensor k) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective k (Submodule.mkQ_surjective S) x
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ] at hx
  obtain ⟨z, rfl⟩ := h y hx
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  have : S.mkQ ∘ₗ S.subtype = 0 := LinearMap.ext fun s ↦ by simp
  rw [this, LinearMap.lTensor_zero]; rfl

end Alg

section Split

variable {R : Type} [CommRing R] {A₁ A₂ : Type} [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂]

theorem eq_ker_and_split [Module.Finite R A₁] [Module.Finite R A₂] [Module.Projective R A₂] (b : A₁ →ₗ[R] A₂)
    (S : Submodule R A₁) (hSb : S ≤ LinearMap.ker b)
    (h : ∀ (m : Ideal R) [m.IsMaximal] (x : m.ResidueField ⊗[R] A₁), b.lTensor m.ResidueField x = 0 →
      x ∈ LinearMap.range (S.subtype.lTensor m.ResidueField)) :
    S = LinearMap.ker b ∧ ∃ r : A₂ →ₗ[R] A₁ ⧸ S, r ∘ₗ S.liftQ b hSb = LinearMap.id := by
  obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective (S.liftQ b hSb)
    fun m _ ↦ lTensor_liftQ_injective _ b S hSb (h m)
  refine ⟨le_antisymm hSb fun x hx ↦ ?_, r, hr⟩
  have : Submodule.Quotient.mk (p := S) x = 0 := by
    have h1 := LinearMap.congr_fun hr (Submodule.Quotient.mk x)
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, LinearMap.mem_ker.1 hx, map_zero,
      LinearMap.id_apply] at h1
    exact h1.symm
  exact (Submodule.Quotient.mk_eq_zero S).1 this

theorem ker_retract [Module.Projective R A₂] (b : A₁ →ₗ[R] A₂) (h0 : LinearMap.ker b ≤ LinearMap.ker b)
    (r : A₂ →ₗ[R] A₁ ⧸ LinearMap.ker b) (hr : r ∘ₗ (LinearMap.ker b).liftQ b h0 = LinearMap.id) :
    ∃ ρ : A₁ →ₗ[R] LinearMap.ker b, ρ ∘ₗ (LinearMap.ker b).subtype = LinearMap.id := by
  have : Module.Projective R (A₁ ⧸ LinearMap.ker b) :=
    Module.Projective.of_split ((LinearMap.ker b).liftQ b h0) r hr
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.ker b).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ x, (LinearMap.id - t ∘ₗ (LinearMap.ker b).mkQ : A₁ →ₗ[R] A₁) x ∈ LinearMap.ker b := fun x ↦ by
    have := LinearMap.congr_fun ht ((LinearMap.ker b).mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    refine (Submodule.Quotient.mk_eq_zero (LinearMap.ker b)).1 ?_
    have h2 : Submodule.Quotient.mk (p := LinearMap.ker b) ((LinearMap.id - t ∘ₗ (LinearMap.ker b).mkQ : A₁ →ₗ[R] A₁) x) =
        (LinearMap.ker b).mkQ x - (LinearMap.ker b).mkQ (t ((LinearMap.ker b).mkQ x)) := rfl
    rw [h2, this, sub_self]
  refine ⟨LinearMap.codRestrict _ _ hmem, LinearMap.ext fun ⟨x, hx⟩ ↦ Subtype.ext ?_⟩
  have : (LinearMap.ker b).mkQ x = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hx
  simp [this]

theorem finite_projective_of_split {Y H : Type} [AddCommGroup Y] [Module R Y] [AddCommGroup H] [Module R H]
    [Module.Finite R Y] [Module.Projective R Y] (θ : Y →ₗ[R] H) (hθ : Function.Surjective θ) (τ : Y →ₗ[R] Y)
    (h1 : ∀ y, θ y = 0 → τ y = 0) (h2 : ∀ y, θ (τ y) = θ y) : Module.Finite R H ∧ Module.Projective R H := by
  refine ⟨Module.Finite.of_surjective θ hθ, ?_⟩
  let e := θ.quotKerEquivOfSurjective hθ
  let σ : H →ₗ[R] Y := (LinearMap.ker θ).liftQ τ (fun y hy ↦ h1 y hy) ∘ₗ e.symm.toLinearMap
  refine Module.Projective.of_split σ θ (LinearMap.ext fun c ↦ ?_)
  obtain ⟨y, rfl⟩ := hθ c
  have : e.symm (θ y) = Submodule.Quotient.mk y := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [σ, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearMap.id_apply]
  exact h2 y

end Split

def Rep {R : Type} [CommRing R] (k : Type) [CommRing k] [Algebra R k] {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module k B] (c : A → B) : Prop :=
  ∃ e : k ⊗[R] A ≃ₗ[k] B, ∀ a, e (1 ⊗ₜ a) = c a

@[reducible] def Pm {J : Type} {A B : J → Type} (c : ∀ i, A i → B i) : (∀ i, A i) → ∀ i, B i := fun a i ↦ c i (a i)

theorem Rep.pi {R : Type} [CommRing R] (k : Type) [CommRing k] [Algebra R k] {J : Type} [Finite J]
    {A B : J → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module k (B i)] (c : ∀ i, A i → B i) (h : ∀ i, Rep (R := R) k (c i)) :
    Rep (R := R) k (Pm c) := by
  classical
  haveI := Fintype.ofFinite J
  choose e he using h
  refine ⟨(TensorProduct.piRight R k k A).trans (LinearEquiv.piCongrRight e), fun a ↦ ?_⟩
  funext i
  simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, he]

section Ladder

variable {R k : Type} [CommRing R] [CommRing k] [Algebra R k] {A A' B B' : Type}
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A'] [AddCommGroup B] [Module k B]
  [AddCommGroup B'] [Module k B']

theorem ladder {c : A → B} {c' : A' → B'} (e : k ⊗[R] A ≃ₗ[k] B) (e' : k ⊗[R] A' ≃ₗ[k] B')
    (he : ∀ a, e (1 ⊗ₜ a) = c a) (he' : ∀ a, e' (1 ⊗ₜ a) = c' a) (d : A →ₗ[R] A') (δ : B →ₗ[k] B')
    (h : ∀ a, c' (d a) = δ (c a)) (y : k ⊗[R] A) : e' (d.lTensor k y) = δ (e y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul l a =>
    have h1 : l ⊗ₜ[R] a = l • ((1 : k) ⊗ₜ[R] a) := by simp [TensorProduct.smul_tmul']
    have h2 : l ⊗ₜ[R] d a = l • ((1 : k) ⊗ₜ[R] d a) := by simp [TensorProduct.smul_tmul']
    rw [LinearMap.lTensor_tmul, h1, h2, map_smul, map_smul, map_smul, he, he', h]

end Ladder

section Deg

variable {R k : Type} [CommRing R] [CommRing k] [Algebra R k]
  {D₀ D₁ D₂ E₀ E₁ E₂ Hh Hh' X : Type}
  [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁] [Module R D₁] [AddCommGroup D₂] [Module R D₂]
  [AddCommGroup E₀] [Module k E₀] [AddCommGroup E₁] [Module k E₁] [AddCommGroup E₂] [Module k E₂]
  [AddCommGroup Hh] [Module R Hh] [AddCommGroup Hh'] [Module k Hh'] [AddCommGroup X] [Module R X]

theorem exists_cocycle (Z : Submodule R D₁) (Z' : Submodule k E₁) (mk : Z →ₗ[R] Hh) (mk' : Z' →ₗ[k] Hh')
    {c : D₁ → E₁} (e : k ⊗[R] D₁ ≃ₗ[k] E₁) (he : ∀ a, e (1 ⊗ₜ a) = c a) (hz : ∀ z ∈ Z, c z ∈ Z')
    (Φ : k ⊗[R] Hh →ₗ[k] Hh') (hΦ : ∀ z : Z, Φ (1 ⊗ₜ mk z) = mk' ⟨c z, hz z z.2⟩) (q : X →ₗ[R] Z)
    (v : k ⊗[R] X) :
    ∃ w : Z', w.1 = e ((Z.subtype ∘ₗ q).lTensor k v) ∧ mk' w = Φ ((mk ∘ₗ q).lTensor k v) := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | add a b ha hb =>
    obtain ⟨w, h1, h2⟩ := ha
    obtain ⟨w', h1', h2'⟩ := hb
    exact ⟨w + w', by simp [h1, h1'], by simp [h2, h2']⟩
  | tmul l x =>
    refine ⟨l • ⟨c (q x), hz _ (q x).2⟩, ?_, ?_⟩
    · have h1 : l ⊗ₜ[R] (Z.subtype ∘ₗ q) x = l • ((1 : k) ⊗ₜ[R] (q x).1) := by simp [TensorProduct.smul_tmul']
      rw [LinearMap.lTensor_tmul, h1, map_smul, he]; rfl
    · have h1 : l ⊗ₜ[R] (mk ∘ₗ q) x = l • ((1 : k) ⊗ₜ[R] mk (q x)) := by simp [TensorProduct.smul_tmul']
      rw [LinearMap.lTensor_tmul, h1, map_smul, map_smul, hΦ]

theorem closed_surj (d : D₀ →ₗ[R] D₁) (d' : D₁ →ₗ[R] D₂) (δ : E₀ →ₗ[k] E₁) (δ' : E₁ →ₗ[k] E₂)
    {c₀ : D₀ → E₀} {c₁ : D₁ → E₁} {c₂ : D₂ → E₂}
    (e₀ : k ⊗[R] D₀ ≃ₗ[k] E₀) (e₁ : k ⊗[R] D₁ ≃ₗ[k] E₁) (e₂ : k ⊗[R] D₂ ≃ₗ[k] E₂)
    (he₀ : ∀ a, e₀ (1 ⊗ₜ a) = c₀ a) (he₁ : ∀ a, e₁ (1 ⊗ₜ a) = c₁ a) (he₂ : ∀ a, e₂ (1 ⊗ₜ a) = c₂ a)
    (hd : ∀ a, c₁ (d a) = δ (c₀ a)) (hd' : ∀ a, c₂ (d' a) = δ' (c₁ a))
    (Z : Submodule R D₁) (Z' : Submodule k E₁) (hZ' : ∀ w, δ' w = 0 → w ∈ Z')
    (mk : Z →ₗ[R] Hh) (mk' : Z' →ₗ[k] Hh') (hmk' : ∀ w : Z', mk' w = 0 → ∃ y, δ y = w.1)
    (hz : ∀ z ∈ Z, c₁ z ∈ Z') (Φ : k ⊗[R] Hh →ₗ[k] Hh') (hΦ : ∀ z : Z, Φ (1 ⊗ₜ mk z) = mk' ⟨c₁ z, hz z z.2⟩)
    (q : X →ₗ[R] Z) (hsurj : ∀ c : Hh', ∃ s : k ⊗[R] X, Φ ((mk ∘ₗ q).lTensor k s) = c)
    (z : k ⊗[R] D₁) (hz0 : d'.lTensor k z = 0) :
    ∃ (s : k ⊗[R] X) (y : k ⊗[R] D₀), (Z.subtype ∘ₗ q).lTensor k s - z = d.lTensor k y := by
  have hw : δ' (e₁ z) = 0 := by rw [← ladder e₁ e₂ he₁ he₂ d' δ' hd' z, hz0, map_zero]
  let w : Z' := ⟨e₁ z, hZ' _ hw⟩
  obtain ⟨s, hs⟩ := hsurj (mk' w)
  obtain ⟨w', h1, h2⟩ := exists_cocycle Z Z' mk mk' e₁ he₁ hz Φ hΦ q s
  obtain ⟨y', hy'⟩ := hmk' (w' - w) (by rw [map_sub, h2, hs, sub_self])
  refine ⟨s, e₀.symm y', e₁.injective ?_⟩
  rw [ladder e₀ e₁ he₀ he₁ d δ hd, LinearEquiv.apply_symm_apply, hy', map_sub, ← h1]
  rfl

theorem phi_injective {A₀ A₁ A₂ : Type} [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁]
    [AddCommGroup A₂] [Module R A₂] (a : A₀ →ₗ[R] A₁) (b : A₁ →ₗ[R] A₂) (hab : ∀ x, a x ∈ LinearMap.ker b)
    (ψ : A₁ →ₗ[R] D₁) (d : D₀ →ₗ[R] D₁) (δ : E₀ →ₗ[k] E₁) {c₀ : D₀ → E₀} {c₁ : D₁ → E₁}
    (e₀ : k ⊗[R] D₀ ≃ₗ[k] E₀) (e₁ : k ⊗[R] D₁ ≃ₗ[k] E₁)
    (he₀ : ∀ a, e₀ (1 ⊗ₜ a) = c₀ a) (he₁ : ∀ a, e₁ (1 ⊗ₜ a) = c₁ a) (hd : ∀ a, c₁ (d a) = δ (c₀ a))
    (Z : Submodule R D₁) (Z' : Submodule k E₁)
    (mk : Z →ₗ[R] Hh) (mk' : Z' →ₗ[k] Hh') (hmk' : ∀ w : Z', mk' w = 0 → ∃ y, δ y = w.1)
    (hz : ∀ z ∈ Z, c₁ z ∈ Z') (Φ : k ⊗[R] Hh →ₗ[k] Hh') (hΦ : ∀ z : Z, Φ (1 ⊗ₜ mk z) = mk' ⟨c₁ z, hz z z.2⟩)
    (q : LinearMap.ker b →ₗ[R] Z) (hq : ∀ y, (q y).1 = ψ y.1) (hθ : Function.Surjective (mk ∘ₗ q))
    (hθa : ∀ x, mk (q ⟨a x, hab x⟩) = 0)
    (hqk : ∀ x, b.lTensor k x = 0 → (∃ y, d.lTensor k y = ψ.lTensor k x) → ∃ y, a.lTensor k y = x)
    (hinj : Function.Injective ((LinearMap.ker b).subtype.lTensor k)) : Function.Injective Φ := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨v, rfl⟩ := LinearMap.lTensor_surjective k hθ t
  obtain ⟨w, h1, h2⟩ := exists_cocycle Z Z' mk mk' e₁ he₁ hz Φ hΦ q v
  obtain ⟨y', hy'⟩ := hmk' w (h2.trans ht)
  have hψq : Z.subtype ∘ₗ q = ψ ∘ₗ (LinearMap.ker b).subtype := LinearMap.ext hq
  have hb0 : b ∘ₗ (LinearMap.ker b).subtype = 0 := LinearMap.ext fun y ↦ y.2
  have e1 : d.lTensor k (e₀.symm y') = ψ.lTensor k ((LinearMap.ker b).subtype.lTensor k v) := by
    apply e₁.injective
    rw [ladder e₀ e₁ he₀ he₁ d δ hd, LinearEquiv.apply_symm_apply, hy', h1, hψq, LinearMap.lTensor_comp]
    rfl
  obtain ⟨u, hu⟩ := hqk _ (by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hb0, LinearMap.lTensor_zero]; rfl) ⟨_, e1⟩
  let a' : A₀ →ₗ[R] LinearMap.ker b := a.codRestrict _ hab
  have ha' : (LinearMap.ker b).subtype ∘ₗ a' = a := LinearMap.ext fun _ ↦ rfl
  have hv : v = a'.lTensor k u := hinj (by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ha']; exact hu.symm)
  have h0 : (mk ∘ₗ q) ∘ₗ a' = 0 := LinearMap.ext hθa
  rw [hv, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero]; rfl

theorem fibre_generic {A₀ A₁ A₂ : Type} [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁]
    [AddCommGroup A₂] [Module R A₂] (a : A₀ →ₗ[R] A₁) (b : A₁ →ₗ[R] A₂)
    (ψ : A₁ →ₗ[R] D₁) (ψ' : A₂ →ₗ[R] D₂) (d : D₀ →ₗ[R] D₁) (d' : D₁ →ₗ[R] D₂) (hψ : ψ' ∘ₗ b = d' ∘ₗ ψ)
    (δ : E₀ →ₗ[k] E₁) (δ' : E₁ →ₗ[k] E₂) {c₀ : D₀ → E₀} {c₁ : D₁ → E₁} {c₂ : D₂ → E₂}
    (e₀ : k ⊗[R] D₀ ≃ₗ[k] E₀) (e₁ : k ⊗[R] D₁ ≃ₗ[k] E₁) (e₂ : k ⊗[R] D₂ ≃ₗ[k] E₂)
    (he₀ : ∀ a, e₀ (1 ⊗ₜ a) = c₀ a) (he₁ : ∀ a, e₁ (1 ⊗ₜ a) = c₁ a) (he₂ : ∀ a, e₂ (1 ⊗ₜ a) = c₂ a)
    (hd : ∀ a, c₁ (d a) = δ (c₀ a)) (hd' : ∀ a, c₂ (d' a) = δ' (c₁ a))
    (Z : Submodule R D₁) (Z' : Submodule k E₁) (hZ' : ∀ w, δ' w = 0 → w ∈ Z')
    (mk : Z →ₗ[R] Hh) (mk' : Z' →ₗ[k] Hh') (hmk' : ∀ w : Z', mk' w = 0 → ∃ y, δ y = w.1)
    (hz : ∀ z ∈ Z, c₁ z ∈ Z') (Φ : k ⊗[R] Hh →ₗ[k] Hh') (hΦ : ∀ z : Z, Φ (1 ⊗ₜ mk z) = mk' ⟨c₁ z, hz z z.2⟩)
    (S : Submodule R A₁) (haS : LinearMap.range a ≤ S) (hSb : S ≤ LinearMap.ker b)
    (q : S →ₗ[R] Z) (hq : ∀ y, (q y).1 = ψ y.1)
    (hsurj : ∀ c : Hh', ∃ s : k ⊗[R] S, Φ ((mk ∘ₗ q).lTensor k s) = c)
    (hqk : ∀ x, b.lTensor k x = 0 → (∃ y, d.lTensor k y = ψ.lTensor k x) → ∃ y, a.lTensor k y = x)
    (x : k ⊗[R] A₁) (hx : b.lTensor k x = 0) : x ∈ LinearMap.range (S.subtype.lTensor k) := by
  refine mem_range_of_closed k a b d d' ψ ψ' hψ S haS hSb hqk (fun z hz0 ↦ ?_) x hx
  obtain ⟨s, y, h⟩ := closed_surj d d' δ δ' e₀ e₁ e₂ he₀ he₁ he₂ hd hd' Z Z' hZ' mk mk' hmk' hz Φ hΦ q hsurj z hz0
  refine ⟨s, y, ?_⟩
  have hψq : Z.subtype ∘ₗ q = ψ ∘ₗ S.subtype := LinearMap.ext hq
  rw [← h, hψq, LinearMap.lTensor_comp]
  rfl

end Deg

theorem lid_lTensor {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (y : R ⊗[R] A) : TensorProduct.lid R B (f.lTensor R y) = f (TensorProduct.lid R A y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r a => simp

theorem qIso_unit {R A₀ A₁ A₂ B₀ B₁ B₂ : Type} [CommRing R] [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀]
    [Module R B₁] [Module R B₂] (a₀ : A₀ →ₗ[R] A₁) (a₁ : A₁ →ₗ[R] A₂) (b₀ : B₀ →ₗ[R] B₁) (b₁ : B₁ →ₗ[R] B₂)
    (f : A₁ →ₗ[R] B₁) (h : QIsoAt (a₀.lTensor R) (a₁.lTensor R) (b₀.lTensor R) (b₁.lTensor R) (f.lTensor R)) :
    QIsoAt a₀ a₁ b₀ b₁ f := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨u, hu⟩ := h.1 (1 ⊗ₜ x) (by simp [hx]) ⟨1 ⊗ₜ y, by simp [hy]⟩
    refine ⟨TensorProduct.lid R A₀ u, ?_⟩
    rw [← lid_lTensor, hu]; simp
  · obtain ⟨x, y, h1, h2⟩ := h.2 (1 ⊗ₜ z) (by simp [hz])
    refine ⟨TensorProduct.lid R A₁ x, TensorProduct.lid R B₀ y, ?_, ?_⟩
    · rw [← lid_lTensor, h1, map_zero]
    · have := congrArg (TensorProduct.lid R B₁) h2
      rw [map_sub, lid_lTensor, lid_lTensor] at this
      simpa using this

section Fib

variable {R k : Type} [CommRing R] [CommRing k] [Algebra R k] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} k} (m : BC F F')

def c0 : C0 F → C0 F' := Pm fun T ↦ m.α T

def c1 : C1 F → C1 F' := Pm fun T ↦ Pm fun T' ↦ Pm fun _ ↦ m.α T'

def c2 : C2 F → C2 F' := Pm fun T ↦ Pm fun T' ↦ Pm fun T'' ↦ Pm fun _ ↦ Pm fun _ ↦ m.α T''

def c3 : C3 F → C3 F' := Pm fun T ↦ Pm fun T' ↦ Pm fun T'' ↦ Pm fun T''' ↦ Pm fun _ ↦ Pm fun _ ↦ Pm fun _ ↦ m.α T'''

theorem rep0 [Finite C] : Rep (R := R) k (c0 m) := Rep.pi k _ fun T ↦ m.bij T

theorem rep1 [Finite C] [∀ T T' : C, Finite (T ⟶ T')] : Rep (R := R) k (c1 m) :=
  Rep.pi k _ fun T ↦ Rep.pi k _ fun T' ↦ Rep.pi k _ fun _ ↦ m.bij T'

theorem rep2 [Finite C] [∀ T T' : C, Finite (T ⟶ T')] : Rep (R := R) k (c2 m) :=
  Rep.pi k _ fun T ↦ Rep.pi k _ fun T' ↦ Rep.pi k _ fun T'' ↦ Rep.pi k _ fun _ ↦ Rep.pi k _ fun _ ↦ m.bij T''

theorem rep3 [Finite C] [∀ T T' : C, Finite (T ⟶ T')] : Rep (R := R) k (c3 m) :=
  Rep.pi k _ fun T ↦ Rep.pi k _ fun T' ↦ Rep.pi k _ fun T'' ↦ Rep.pi k _ fun T''' ↦ Rep.pi k _ fun _ ↦
    Rep.pi k _ fun _ ↦ Rep.pi k _ fun _ ↦ m.bij T'''

theorem d2_apply {S : Type} [CommRing S] (G : C ⥤ CommAlgCat.{0} S) (z : C2 G) {T T' T'' T''' : C} (φ : T ⟶ T')
    (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') : d2 G z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ +
      z T T' T''' φ (ψ ≫ χ) - mp G χ (z T T' T'' φ ψ) := rfl

theorem isOneCochain_diffZero (g : C0 F) : c1 m (d0 F g) = d0 F' (c0 m g) := by
  funext T T' φ
  simp only [c1, c0, Pm, amitsur_d0_apply, map_sub, m.naturality]

theorem isTwoCochain_diffOne (f : C1 F) : c2 m (d1 F f) = d1 F' (c1 m f) := by
  funext T T' T'' φ ψ
  simp only [c1, c2, Pm, d1_apply, map_sub, map_add, m.naturality]

theorem cochain_map_degree_three_d2 (z : C2 F) : c3 m (d2 F z) = d2 F' (c2 m z) := by
  funext T T' T'' T''' φ ψ χ
  simp only [c3, c2, Pm, d2_apply, map_sub, map_add, m.naturality]

theorem mem_Z2_iff {S : Type} [CommRing S] (G : C ⥤ CommAlgCat.{0} S) (z : C2 G) : z ∈ Z2 G ↔ d2 G z = 0 := by
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · funext T T' T'' T''' φ ψ χ
    have := h φ ψ χ
    rw [d2_apply]
    simp only [Pi.zero_apply]
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun h T) T') T'') T''') φ) ψ) χ
    rw [d2_apply] at this
    simp only [Pi.zero_apply] at this
    linear_combination -this

end Fib

section Model

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
  {P₀ P₁ P₂ P₃ : Type} [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
  [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
  (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (a₂ : P₂ →ₗ[R] P₃)
  (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (ψ₃ : P₃ →ₗ[R] C3 F)

def q1 (h : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁) : LinearMap.ker a₁ →ₗ[R] Z1 F :=
  (ψ₁ ∘ₗ (LinearMap.ker a₁).subtype).codRestrict (Z1 F) fun y ↦ by
    have h1 := LinearMap.congr_fun h y.1
    have h2 : a₁ y.1 = 0 := y.2
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
    simpa [h2] using h1.symm

def q2 (h : ψ₃ ∘ₗ a₂ = d2 F ∘ₗ ψ₂) : LinearMap.ker a₂ →ₗ[R] Z2 F :=
  (ψ₂ ∘ₗ (LinearMap.ker a₂).subtype).codRestrict (Z2 F) fun y ↦ by
    have h2 : a₂ y.1 = 0 := y.2
    rw [mem_Z2_iff]
    exact (LinearMap.congr_fun h y.1).symm.trans (by
      show ψ₃ (a₂ y.1) = 0
      rw [h2, map_zero])

variable {k : Type} [CommRing k] [Algebra R k] {F' : C ⥤ CommAlgCat.{0} k}

def Phi2 (m : BC F F') : k ⊗[R] H2 F →ₗ[k] H2 F' := GlobalTheory.DeRham.liftSemi m.coef.pull2

theorem Phi2_one (m : BC F F') (c : H2 F) : Phi2 m (1 ⊗ₜ c) = m.coef.pull2 c := by
  simp [Phi2]

theorem second_cohomology_comparison_surjective (m : BC F F') {X : Type} [AddCommGroup X] [Module R X] (q : X →ₗ[R] Z2 F)
    (hcup : ∀ a b, ∃ x, H2.mk F (q x) = cup F a b) (e : k ⊗[R] H1 F ≃ₗ[k] H1 F')
    (he : ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c) (hW : Wedge F') (c : H2 F') :
    ∃ s : k ⊗[R] X, Phi2 m ((H2.mk F ∘ₗ q).lTensor k s) = c := by
  let f : k ⊗[R] X →ₗ[k] H2 F' := Phi2 m ∘ₗ (H2.mk F ∘ₗ q).baseChange k
  have hf : ∀ s, f s = Phi2 m ((H2.mk F ∘ₗ q).lTensor k s) := fun s ↦ rfl
  have key0 : ∀ (l l' : k) (a b : H1 F), cup F' (e (l ⊗ₜ a)) (e (l' ⊗ₜ b)) ∈ LinearMap.range f := by
    intro l l' a b
    obtain ⟨x, hx⟩ := hcup a b
    have h1 : ∀ (l : k) (a : H1 F), e (l ⊗ₜ a) = l • m.coef.pull1 a := fun l a ↦ by
      rw [← he, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h1, h1, map_smul, map_smul, LinearMap.smul_apply, ← m.coef.pullCohomologyTwo_cup, ← hx, ← Phi2_one]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ⟨1 ⊗ₜ x, ?_⟩)
    simp [hf]
  have key : ∀ a b : H1 F', cup F' a b ∈ LinearMap.range f := by
    intro a b
    obtain ⟨ta, rfl⟩ := e.surjective a
    obtain ⟨tb, rfl⟩ := e.surjective b
    induction ta using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => rw [map_add, map_add, LinearMap.add_apply]; exact add_mem hu hv
    | tmul l a =>
      induction tb using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => rw [map_add, map_add]; exact add_mem hu hv
      | tmul l' b => exact key0 l l' a b
  obtain ⟨E, hE⟩ := hW
  have hall : (⊤ : Submodule k (⋀[k]^2 (H1 F'))) ≤ (LinearMap.range f).comap E.toLinearMap := by
    rw [← exteriorPower.ιMulti_span, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v = ![v 0, v 1] := by
      funext i; fin_cases i <;> rfl
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [hv, hE]
    exact key _ _
  obtain ⟨s, hs⟩ := hall (Submodule.mem_top (x := E.symm c))
  exact ⟨s, by rw [← hf, hs]; simp⟩

variable [Finite C] [∀ T T' : C, Finite (T ⟶ T')]

theorem fibre1 (m : BC F F') (h10 : a₁ ∘ₗ a₀ = 0) (hc2 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (e : k ⊗[R] H1 F ≃ₗ[k] H1 F') (he : ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c)
    (hs : Function.Surjective (H1.mk F ∘ₗ q1 a₁ ψ₁ ψ₂ hc2))
    (hq : ∀ x, a₁.lTensor k x = 0 → (∃ y, (d0 F).lTensor k y = ψ₁.lTensor k x) → ∃ y, a₀.lTensor k y = x)
    (x : k ⊗[R] P₁) (hx : a₁.lTensor k x = 0) :
    x ∈ LinearMap.range ((LinearMap.ker a₁).subtype.lTensor k) := by
  obtain ⟨e₀, he₀⟩ := rep0 m
  obtain ⟨e₁, he₁⟩ := rep1 m
  obtain ⟨e₂, he₂⟩ := rep2 m
  refine fibre_generic a₀ a₁ ψ₁ ψ₂ (d0 F) (d1 F) hc2 (d0 F') (d1 F') e₀ e₁ e₂ he₀ he₁ he₂ (isOneCochain_diffZero m) (isTwoCochain_diffOne m)
    (Z1 F) (Z1 F') (fun w hw ↦ by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hw) (H1.mk F) (H1.mk F')
    (fun w hw ↦ H1.mk_eq_zero.1 hw) (fun z hz ↦ (m.coef.pullbackOneCocycle ⟨z, hz⟩).2) e.toLinearMap (fun z ↦ he _)
    (LinearMap.ker a₁) (LinearMap.range_le_ker_iff.2 h10) le_rfl (q1 a₁ ψ₁ ψ₂ hc2) (fun _ ↦ rfl)
    (fun c ↦ ?_) hq x hx
  obtain ⟨s, hs'⟩ := LinearMap.lTensor_surjective k hs (e.symm c)
  exact ⟨s, by simp [hs']⟩

theorem fibre2 (m : BC F F') (hc2 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁) (hc3 : ψ₃ ∘ₗ a₂ = d2 F ∘ₗ ψ₂)
    (e : k ⊗[R] H1 F ≃ₗ[k] H1 F') (he : ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c) (hW : Wedge F')
    (S : Submodule R P₂) (haS : LinearMap.range a₁ ≤ S) (hSb : S ≤ LinearMap.ker a₂)
    (hcup : ∀ a b, ∃ x : S, H2.mk F (q2 a₂ ψ₂ ψ₃ hc3 (Submodule.inclusion hSb x)) = cup F a b)
    (hq : ∀ x, a₂.lTensor k x = 0 → (∃ y, (d1 F).lTensor k y = ψ₂.lTensor k x) → ∃ y, a₁.lTensor k y = x)
    (x : k ⊗[R] P₂) (hx : a₂.lTensor k x = 0) : x ∈ LinearMap.range (S.subtype.lTensor k) := by
  obtain ⟨e₁, he₁⟩ := rep1 m
  obtain ⟨e₂, he₂⟩ := rep2 m
  obtain ⟨e₃, he₃⟩ := rep3 m
  exact fibre_generic a₁ a₂ ψ₂ ψ₃ (d1 F) (d2 F) hc3 (d1 F') (d2 F') e₁ e₂ e₃ he₁ he₂ he₃ (isTwoCochain_diffOne m) (cochain_map_degree_three_d2 m)
    (Z2 F) (Z2 F') (fun w hw ↦ (mem_Z2_iff F' w).2 hw) (H2.mk F) (H2.mk F')
    (fun w hw ↦ H2.mk_eq_zero.1 hw) (fun z hz ↦ (m.coef.pullbackTwoCocycle ⟨z, hz⟩).2) (Phi2 m) (fun z ↦ Phi2_one m _)
    S haS hSb (q2 a₂ ψ₂ ψ₃ hc3 ∘ₗ Submodule.inclusion hSb) (fun _ ↦ rfl)
    (second_cohomology_comparison_surjective m _ hcup e he hW) hq x hx

theorem second_cohomology_comparison_injective (m : BC F F') (hc2 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁) (hc3 : ψ₃ ∘ₗ a₂ = d2 F ∘ₗ ψ₂)
    (h21 : a₂ ∘ₗ a₁ = 0) (hθ : Function.Surjective (H2.mk F ∘ₗ q2 a₂ ψ₂ ψ₃ hc3))
    (hq : ∀ x, a₂.lTensor k x = 0 → (∃ y, (d1 F).lTensor k y = ψ₂.lTensor k x) → ∃ y, a₁.lTensor k y = x)
    (hinj : Function.Injective ((LinearMap.ker a₂).subtype.lTensor k)) : Function.Injective (Phi2 m) := by
  obtain ⟨e₁, he₁⟩ := rep1 m
  obtain ⟨e₂, he₂⟩ := rep2 m
  have hab : ∀ x, a₁ x ∈ LinearMap.ker a₂ := fun x ↦ LinearMap.congr_fun h21 x
  refine phi_injective a₁ a₂ hab ψ₂ (d1 F) (d1 F') e₁ e₂ he₁ he₂ (isTwoCochain_diffOne m) (Z2 F) (Z2 F') (H2.mk F) (H2.mk F')
    (fun w hw ↦ H2.mk_eq_zero.1 hw) (fun z hz ↦ (m.coef.pullbackTwoCocycle ⟨z, hz⟩).2) (Phi2 m) (fun z ↦ Phi2_one m _)
    (q2 a₂ ψ₂ ψ₃ hc3) (fun _ ↦ rfl) hθ (fun x ↦ ?_) hq hinj
  exact H2.mk_eq_zero.2 ⟨ψ₁ x, (LinearMap.congr_fun hc2 x).symm⟩

end Model

section Core

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')]

theorem core (F : C ⥤ CommAlgCat.{0} R) (g : ℕ) (hP : Perf F) (hV : VB R (H1 F) g) (hBC : H1CommutesBaseChange F)
    (hW : ∀ (k : Type) [Field k] [Algebra R k], ∃ (F' : C ⥤ CommAlgCat.{0} k) (_ : BC F F'), Wedge F') :
    VB R (H2 F) (g.choose 2) ∧ Submodule.span R (Set.range fun x : H1 F × H1 F ↦ cup F x.1 x.2) = ⊤ := by
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f0, p0⟩, ⟨f1, p1⟩, ⟨f2, p2⟩, ⟨f3, p3⟩, h10, h21, hc1, hc2,
    ⟨ψ₃, hc3⟩, hQ⟩ := hP
  have hq1 : ∀ (k : Type) [CommRing k] [Algebra R k] (x : k ⊗[R] P₁), a₁.lTensor k x = 0 →
      (∃ y, (d0 F).lTensor k y = ψ₁.lTensor k x) → ∃ y, a₀.lTensor k y = x :=
    fun k _ _ ↦ (hQ (ModuleCat.of R k)).2.1.1
  have hq2 : ∀ (k : Type) [CommRing k] [Algebra R k] (x : k ⊗[R] P₂), a₂.lTensor k x = 0 →
      (∃ y, (d1 F).lTensor k y = ψ₂.lTensor k x) → ∃ y, a₁.lTensor k y = x :=
    fun k _ _ ↦ (hQ (ModuleCat.of R k)).2.2.1
  have hR1 : QIsoAt a₀ a₁ (d0 F) (d1 F) ψ₁ := qIso_unit _ _ _ _ _ (hQ (ModuleCat.of R R)).2.1
  have hR2 : QIsoAt a₁ a₂ (d1 F) (d2 F) ψ₂ := qIso_unit _ _ _ _ _ (hQ (ModuleCat.of R R)).2.2
  have hθ₁ : Function.Surjective (H1.mk F ∘ₗ q1 a₁ ψ₁ ψ₂ hc2) := fun c ↦ by
    obtain ⟨z, rfl⟩ := H1.mk_surjective F c
    have hz : z.1 ∈ LinearMap.ker (d1 F) := (commAlgFunctorCocyclesOne_eq_ker F).le z.2
    obtain ⟨x, y, hx, h⟩ := hR1.2 z.1 hz
    exact ⟨⟨x, hx⟩, H1.mk_eq_mk.2 ⟨y, h.symm⟩⟩
  have hθ₂ : Function.Surjective (H2.mk F ∘ₗ q2 a₂ ψ₂ ψ₃ hc3) := fun c ↦ by
    obtain ⟨z, rfl⟩ := H2.mk_surjective F c
    obtain ⟨x, y, hx, h⟩ := hR2.2 z.1 ((mem_Z2_iff F z.1).1 z.2)
    exact ⟨⟨x, hx⟩, H2.mk_eq_mk.2 ⟨y, h.symm⟩⟩
  set S' : Submodule R (H2 F) := Submodule.span R (Set.range fun x : H1 F × H1 F ↦ cup F x.1 x.2) with hS'
  set W : Submodule R P₂ := (S'.comap (H2.mk F ∘ₗ q2 a₂ ψ₂ ψ₃ hc3)).map (LinearMap.ker a₂).subtype with hWdef
  have hWle : W ≤ LinearMap.ker a₂ := Submodule.map_subtype_le _ _
  have haW : LinearMap.range a₁ ≤ W := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨a₁ x, LinearMap.congr_fun h21 x⟩, ?_, rfl⟩
    have : (H2.mk F ∘ₗ q2 a₂ ψ₂ ψ₃ hc3) ⟨a₁ x, LinearMap.congr_fun h21 x⟩ = 0 :=
      H2.mk_eq_zero.2 ⟨ψ₁ x, (LinearMap.congr_fun hc2 x).symm⟩
    exact Submodule.mem_comap.2 (this ▸ S'.zero_mem)
  have hcup : ∀ a b, ∃ x : W, H2.mk F (q2 a₂ ψ₂ ψ₃ hc3 (Submodule.inclusion hWle x)) = cup F a b := fun a b ↦ by
    obtain ⟨y, hy⟩ := hθ₂ (cup F a b)
    refine ⟨⟨y.1, y, ?_, rfl⟩, hy⟩
    exact (Submodule.mem_comap.2 (hy ▸ Submodule.subset_span ⟨(a, b), rfl⟩))
  have hk1 : ∀ (m : Ideal R) [m.IsMaximal] (x : m.ResidueField ⊗[R] P₁), a₁.lTensor m.ResidueField x = 0 →
      x ∈ LinearMap.range ((LinearMap.ker a₁).subtype.lTensor m.ResidueField) := fun m _ x hx ↦ by
    obtain ⟨F', bc, -⟩ := hW m.ResidueField
    obtain ⟨e, he⟩ := hBC m.ResidueField F' bc
    exact fibre1 a₀ a₁ ψ₁ ψ₂ bc h10 hc2 e he hθ₁ (hq1 _) x hx
  have hk2 : ∀ (m : Ideal R) [m.IsMaximal] (x : m.ResidueField ⊗[R] P₂), a₂.lTensor m.ResidueField x = 0 →
      x ∈ LinearMap.range (W.subtype.lTensor m.ResidueField) := fun m _ x hx ↦ by
    obtain ⟨F', bc, hw⟩ := hW m.ResidueField
    obtain ⟨e, he⟩ := hBC m.ResidueField F' bc
    exact fibre2 a₁ a₂ ψ₁ ψ₂ ψ₃ bc hc2 hc3 e he hw W haW hWle hcup (hq2 _) x hx
  obtain ⟨-, r₁, hr₁⟩ := eq_ker_and_split a₁ (LinearMap.ker a₁) le_rfl hk1
  obtain ⟨hWeq, -⟩ := eq_ker_and_split a₂ W hWle hk2
  have hk2' : ∀ (m : Ideal R) [m.IsMaximal] (x : m.ResidueField ⊗[R] P₂), a₂.lTensor m.ResidueField x = 0 →
      x ∈ LinearMap.range ((LinearMap.ker a₂).subtype.lTensor m.ResidueField) := by
    rw [← hWeq]; exact hk2
  obtain ⟨-, r₂, hr₂⟩ := eq_ker_and_split a₂ (LinearMap.ker a₂) le_rfl hk2'
  obtain ⟨ρ, hρ⟩ := ker_retract a₂ le_rfl r₂ hr₂
  have hYp : Module.Projective R (LinearMap.ker a₂) :=
    Module.Projective.of_split (LinearMap.ker a₂).subtype ρ hρ
  have hYf : Module.Finite R (LinearMap.ker a₂) :=
    Module.Finite.of_surjective ρ fun y ↦ ⟨y.1, LinearMap.congr_fun hρ y⟩

  let l₁ : P₁ ⧸ LinearMap.ker a₁ →ₗ[R] P₂ := (LinearMap.ker a₁).liftQ a₁ le_rfl
  let π : P₂ →ₗ[R] P₂ := l₁ ∘ₗ r₁
  have hπ1 : ∀ x, π (a₁ x) = a₁ x := fun x ↦ by
    have := LinearMap.congr_fun hr₁ (Submodule.Quotient.mk x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.liftQ_apply] at this
    simp only [π, LinearMap.comp_apply, this]
    rfl
  have hπ2 : ∀ y, ∃ x, π y = a₁ x := fun y ↦ by
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (r₁ y)
    exact ⟨x, by simp only [π, LinearMap.comp_apply, ← hx]; rfl⟩
  have hτ : ∀ y : LinearMap.ker a₂, ((LinearMap.id - π) ∘ₗ (LinearMap.ker a₂).subtype) y ∈ LinearMap.ker a₂ := fun y ↦ by
    obtain ⟨x, hx⟩ := hπ2 y.1
    have h1 : a₂ y.1 = 0 := y.2
    have h2 : a₂ (a₁ x) = 0 := LinearMap.congr_fun h21 x
    simp [hx, h1, h2]
  have hb0 : ∀ (x : P₁) (hx : a₁ x ∈ LinearMap.ker a₂), (H2.mk F ∘ₗ q2 a₂ ψ₂ ψ₃ hc3) ⟨a₁ x, hx⟩ = 0 := fun x _ ↦
    H2.mk_eq_zero.2 ⟨ψ₁ x, (LinearMap.congr_fun hc2 x).symm⟩
  have hFP : Module.Finite R (H2 F) ∧ Module.Projective R (H2 F) := by
    refine finite_projective_of_split (H2.mk F ∘ₗ q2 a₂ ψ₂ ψ₃ hc3) hθ₂
      (LinearMap.codRestrict _ _ hτ) (fun y hy ↦ ?_) (fun y ↦ ?_)
    · obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 hy
      obtain ⟨u, hu⟩ := hR2.1 y.1 y.2 ⟨f, hf⟩
      refine Subtype.ext ?_
      show y.1 - π y.1 = 0
      rw [← hu, hπ1, sub_self]
    · obtain ⟨x, hx⟩ := hπ2 y.1
      have hm : a₁ x ∈ LinearMap.ker a₂ := LinearMap.congr_fun h21 x
      have h1 : LinearMap.codRestrict _ _ hτ y = y - ⟨a₁ x, hm⟩ := Subtype.ext (by
        show y.1 - π y.1 = y.1 - a₁ x
        rw [hx])
      rw [h1, map_sub, hb0, sub_zero]
  obtain ⟨hfin, hproj⟩ := hFP
  refine ⟨⟨hfin, hproj, fun p ↦ ?_⟩, ?_⟩
  · obtain ⟨hf1, hp1, hr⟩ := hV
    obtain ⟨F', bc, hw⟩ := hW p.asIdeal.ResidueField
    obtain ⟨e, he⟩ := hBC _ F' bc
    have hinj : Function.Injective ((LinearMap.ker a₂).subtype.lTensor p.asIdeal.ResidueField) :=
      Function.LeftInverse.injective (g := ρ.lTensor _) fun x ↦ by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hρ, LinearMap.lTensor_id]; rfl
    have hΦi := second_cohomology_comparison_injective a₁ a₂ ψ₁ ψ₂ ψ₃ bc hc2 hc3 h21 hθ₂ (hq2 _) hinj
    have hΦs : Function.Surjective (Phi2 bc) := fun c ↦ by
      obtain ⟨s, hs⟩ := second_cohomology_comparison_surjective bc (q2 a₂ ψ₂ ψ₃ hc3) (fun a b ↦ hθ₂ (cup F a b)) e he hw c
      exact ⟨_, hs⟩
    let E := LinearEquiv.ofBijective (Phi2 bc) ⟨hΦi, hΦs⟩
    obtain ⟨E2, -⟩ := hw
    have h1 : Module.finrank p.asIdeal.ResidueField (H1 F') = g := by
      rw [← e.finrank_eq]
      have := Module.rankAtStalk_eq (M := H1 F) p
      rw [hr p] at this
      exact this.symm
    have hfin' : Module.Finite p.asIdeal.ResidueField (H1 F') := Module.Finite.equiv e
    rw [Module.rankAtStalk_eq p]
    show Module.finrank _ (p.asIdeal.ResidueField ⊗[R] H2 F) = _
    rw [E.finrank_eq, ← E2.finrank_eq, exteriorPower.finrank_eq, h1]
  · rw [eq_top_iff]
    intro c _
    obtain ⟨y, rfl⟩ := hθ₂ c
    have hy : y.1 ∈ W := hWeq.symm ▸ y.2
    obtain ⟨y', hy', he⟩ := hy
    have : y' = y := Subtype.ext he
    subst this
    exact hy'

end Core

theorem perfect_second_cohomology_from_fibres : PerfectH2FromFibres := by
  intro R _ P _ _ F g hP _ hV hBC hW
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ ↦ inferInstance
  exact core F g hP hV hBC hW

end GlobalTheory.CompanionTheory.PerfectSecondCohomology
