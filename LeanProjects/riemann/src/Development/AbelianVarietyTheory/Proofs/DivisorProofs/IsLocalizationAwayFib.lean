import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem isLocalization_away_eqLocus {A B C A' B' C' : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing A'] [CommRing B'] [CommRing C'] (f : B →+* A) (g : C →+* A)
    (f' : B' →+* A') (g' : C' →+* A') (ρA : A →+* A') (ρB : B →+* B') (ρC : C →+* C')
    (hB : f'.comp ρB = ρA.comp f) (hC : g'.comp ρC = ρA.comp g)
    (x : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)))
    (φ : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)) →+*
      RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')))
    (hφ : ∀ y, (φ y : B' × C') = (ρB (y : B × C).1, ρC (y : B × C).2))
    (hlB : letI := ρB.toAlgebra; IsLocalization.Away (x : B × C).1 B')
    (hlC : letI := ρC.toAlgebra; IsLocalization.Away (x : B × C).2 C')
    (hlA : letI := ρA.toAlgebra; IsLocalization.Away (f (x : B × C).1) A') :
    letI := φ.toAlgebra
    IsLocalization.Away x
      (RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C'))) := by
  letI := ρB.toAlgebra
  letI := ρC.toAlgebra
  letI := ρA.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨⟨b, c⟩, hx⟩ := x
  have hx' : f b = g c := hx
  have eB : ∀ y, f' (ρB y) = ρA (f y) := fun y ↦ RingHom.congr_fun hB y
  have eC : ∀ y, g' (ρC y) = ρA (g y) := fun y ↦ RingHom.congr_fun hC y
  have hfst : ∀ y, ((φ y : B' × C')).1 = ρB (y : B × C).1 := fun y ↦ by rw [hφ]
  have hsnd : ∀ y, ((φ y : B' × C')).2 = ρC (y : B × C).2 := fun y ↦ by rw [hφ]
  have hpow : ∀ (y : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)))
      (k : ℕ), ((y ^ k : RingHom.eqLocus (f.comp (RingHom.fst B C))
        (g.comp (RingHom.snd B C))) : B × C) = ((y : B × C).1 ^ k, (y : B × C).2 ^ k) :=
    fun y k ↦ by rw [SubmonoidClass.coe_pow, Prod.pow_def]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  ·
    have hu : IsUnit (φ ⟨(b, c), hx⟩) := by
      obtain ⟨u₁, hu₁⟩ := IsLocalization.Away.algebraMap_isUnit (S := B') b
      obtain ⟨u₂, hu₂⟩ := IsLocalization.Away.algebraMap_isUnit (S := C') c
      have hu₁' : (u₁ : B') = ρB b := hu₁
      have hu₂' : (u₂ : C') = ρC c := hu₂
      have e0 : f' u₁ = g' u₂ := by rw [hu₁', hu₂', eB, eC, hx']
      have e1 : f' ↑u₁⁻¹ = g' ↑u₂⁻¹ := by
        calc f' ↑u₁⁻¹ = f' ↑u₁⁻¹ * (g' u₂ * g' ↑u₂⁻¹) := by
                rw [← map_mul, Units.mul_inv, map_one, mul_one]
          _ = f' ↑u₁⁻¹ * f' u₁ * g' ↑u₂⁻¹ := by rw [e0, mul_assoc]
          _ = g' ↑u₂⁻¹ := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
      refine isUnit_iff_exists_inv.mpr ⟨⟨(↑u₁⁻¹, ↑u₂⁻¹), e1⟩, ?_⟩
      apply Subtype.ext
      change (φ ⟨(b, c), hx⟩ : B' × C') * ((↑u₁⁻¹ : B'), (↑u₂⁻¹ : C')) = (1 : B' × C')
      rw [hφ]
      ext
      · change ρB b * ↑u₁⁻¹ = 1
        rw [← hu₁', Units.mul_inv]
      · change ρC c * ↑u₂⁻¹ = 1
        rw [← hu₂', Units.mul_inv]
    rintro ⟨_, n, rfl⟩
    change IsUnit (φ (⟨(b, c), hx⟩ ^ n))
    rw [map_pow]
    exact hu.pow n
  ·
    rintro ⟨⟨z₁, z₂⟩, hz⟩
    have hz' : f' z₁ = g' z₂ := hz
    obtain ⟨n₁, y₁, h₁⟩ := IsLocalization.Away.surj b z₁
    obtain ⟨n₂, y₂, h₂⟩ := IsLocalization.Away.surj c z₂
    have h₁' : z₁ * ρB b ^ (n₁ + n₂) = ρB (y₁ * b ^ n₂) := by
      change z₁ * ρB b ^ n₁ = ρB y₁ at h₁
      rw [pow_add, ← mul_assoc, h₁, map_mul, map_pow]
    have h₂' : z₂ * ρC c ^ (n₁ + n₂) = ρC (y₂ * c ^ n₁) := by
      change z₂ * ρC c ^ n₂ = ρC y₂ at h₂
      rw [add_comm, pow_add, ← mul_assoc, h₂, map_mul, map_pow]
    have hA : algebraMap A A' (f (y₁ * b ^ n₂)) = algebraMap A A' (g (y₂ * c ^ n₁)) := by
      change ρA _ = ρA _
      have k₁ := congrArg f' h₁'
      have k₂ := congrArg g' h₂'
      rw [map_mul, map_pow, eB, eB] at k₁
      rw [map_mul, map_pow, eC, eC] at k₂
      rw [← k₁, ← k₂, hz', hx']
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (f b)) hA
    change f b ^ m * f (y₁ * b ^ n₂) = f b ^ m * g (y₂ * c ^ n₁) at hm
    have hmem : f (b ^ m * (y₁ * b ^ n₂)) = g (c ^ m * (y₂ * c ^ n₁)) := by
      rw [map_mul f (b ^ m), map_pow f, hm, map_mul g (c ^ m), map_pow g, hx']
    refine ⟨(⟨(b ^ m * (y₁ * b ^ n₂), c ^ m * (y₂ * c ^ n₁)), hmem⟩,
      ⟨⟨(b, c), hx⟩ ^ (m + (n₁ + n₂)), m + (n₁ + n₂), rfl⟩), ?_⟩
    apply Subtype.ext
    change ((⟨(z₁, z₂), hz⟩ : RingHom.eqLocus _ _) : B' × C') * (φ (⟨(b, c), hx⟩ ^ (m + (n₁ + n₂))) : B' × C') = (φ _ : B' × C')
    rw [hφ, hφ, hpow]
    ext
    · change z₁ * ρB (b ^ (m + (n₁ + n₂))) = ρB (b ^ m * (y₁ * b ^ n₂))
      rw [map_mul, ← h₁']
      simp only [map_pow]
      ring
    · change z₂ * ρC (c ^ (m + (n₁ + n₂))) = ρC (c ^ m * (y₂ * c ^ n₁))
      rw [map_mul, ← h₂']
      simp only [map_pow]
      ring
  ·
    intro y y' e
    have e' : φ y = φ y' := e
    have e₁ : algebraMap B B' (y : B × C).1 = algebraMap B B' (y' : B × C).1 := by
      change ρB _ = ρB _
      rw [← hfst, ← hfst]; exact congrArg (fun t : RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')) ↦ (t : B' × C').1) e'
    have e₂ : algebraMap C C' (y : B × C).2 = algebraMap C C' (y' : B × C).2 := by
      change ρC _ = ρC _
      rw [← hsnd, ← hsnd]; exact congrArg (fun t : RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')) ↦ (t : B' × C').2) e'
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers b) e₁
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers c) e₂
    change b ^ n * _ = b ^ n * _ at hn
    change c ^ k * _ = c ^ k * _ at hk
    refine ⟨⟨⟨(b, c), hx⟩ ^ (n + k), n + k, rfl⟩, ?_⟩
    apply Subtype.ext
    change ((⟨(b, c), hx⟩ ^ (n + k) : RingHom.eqLocus _ _) : B × C) * (y : B × C) =
      ((⟨(b, c), hx⟩ ^ (n + k) : RingHom.eqLocus _ _) : B × C) * (y' : B × C)
    rw [hpow]
    ext
    · change b ^ (n + k) * _ = b ^ (n + k) * _
      calc b ^ (n + k) * (y : B × C).1 = b ^ k * (b ^ n * (y : B × C).1) := by ring
        _ = b ^ k * (b ^ n * (y' : B × C).1) := by rw [hn]
        _ = _ := by ring
    · change c ^ (n + k) * _ = c ^ (n + k) * _
      calc c ^ (n + k) * (y : B × C).2 = c ^ n * (c ^ k * (y : B × C).2) := by ring
        _ = c ^ n * (c ^ k * (y' : B × C).2) := by rw [hk]
        _ = _ := by ring

end GlobalTheory.FerrandPush

namespace GlobalTheory.FerrandPush

section Geo
variable {Y₀ Y₁ Y₂ : Scheme.{0}}

theorem upOpen_basicOpen (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i] (U : Y₀.Opens)
    (s : Γ(Y₁, upOpen i U)) : upOpen i (Y₀.basicOpen ((res i U).hom s)) = Y₁.basicOpen s := by
  have h1 : Y₀.basicOpen ((res i U).hom s) = U ⊓ i ⁻¹ᵁ Y₁.basicOpen s :=
    Scheme.basicOpen_appLE i U (upOpen i U) (preimage_upOpen i U).ge s
  have h2 : i ⁻¹ᵁ Y₁.basicOpen s ≤ U :=
    le_trans ((Scheme.Hom.preimage_mono i) (Y₁.basicOpen_le s)) (preimage_upOpen i U).le
  rw [h1, inf_eq_right.mpr h2, upOpen_preimage]

variable (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁]
  [IsClosedImmersion i₂] [Surjective i₂]

theorem fibπ_apply (U : Y₀.Opens) (a : (fib i₁ i₂).obj (op U)) :
    ((fibπ i₁ i₂).app (op U)).hom a = (res i₁ U).hom ((cone i₁ i₂ U).fst.hom a) :=
  rfl

end Geo
end GlobalTheory.FerrandPush

namespace GlobalTheory.FerrandPush

theorem isLocalization_away_fib : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂],
    ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U),
    letI := ((GlobalTheory.FerrandPush.fib i₁ i₂).map (homOfLE (Y₀.basicOpen_le
      (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a))).op).hom.toAlgebra;
    IsLocalization.Away a ((GlobalTheory.FerrandPush.fib i₁ i₂).obj
      (op (Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a)))) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ _ U hU a
  obtain ⟨hU0, hU1, hU2⟩ := hU
  have hD : Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a) ≤ U := Y₀.basicOpen_le _
  have hs2 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₂ U).hom ((cone i₁ i₂ U).snd.hom a) := a.2
  have e1 : upOpen i₁ (Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a)) =
      Y₁.basicOpen ((cone i₁ i₂ U).fst.hom a) := upOpen_basicOpen i₁ U _
  have e2 : upOpen i₂ (Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a)) =
      Y₂.basicOpen ((cone i₁ i₂ U).snd.hom a) := by
    rw [hs2]; exact upOpen_basicOpen i₂ U _
  exact isLocalization_away_eqLocus (res i₁ U).hom (res i₂ U).hom (res i₁ _).hom (res i₂ _).hom
    (Y₀.presheaf.map (homOfLE hD).op).hom (Y₁.presheaf.map (homOfLE (upOpen_mono i₁ hD)).op).hom
    (Y₂.presheaf.map (homOfLE (upOpen_mono i₂ hD)).op).hom
    (congrArg CommRingCat.Hom.hom (res_naturality i₁ hD))
    (congrArg CommRingCat.Hom.hom (res_naturality i₂ hD)) a
    ((fib i₁ i₂).map (homOfLE hD).op).hom (fun _ ↦ rfl)
    (hU1.isLocalization_of_eq_basicOpen _ (homOfLE (upOpen_mono i₁ hD)) e1)
    (hU2.isLocalization_of_eq_basicOpen _ (homOfLE (upOpen_mono i₂ hD)) e2)
    (hU0.isLocalization_of_eq_basicOpen _ (homOfLE hD) rfl)

end GlobalTheory.FerrandPush
