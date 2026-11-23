import Mathlib
import Formalism.PeriodIntegrals.IsoDet

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs

section Gen

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]

def relative₂ (X Z : Submodule R W) : ℕ∞ := Module.length R (Z ⧸ X.comap Z.subtype)

theorem rlen_add {X Y Z : Submodule R W} (h1 : X ≤ Y) (h2 : Y ≤ Z) :
    relative₂ X Z = relative₂ X Y + relative₂ Y Z := by
  unfold relative₂
  let f : (Y ⧸ X.comap Y.subtype) →ₗ[R] (Z ⧸ X.comap Z.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion h2) (fun y hy => by simpa using hy)
  let g : (Z ⧸ X.comap Z.subtype) →ₗ[R] (Z ⧸ Y.comap Z.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun z hz => by
      simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.id_apply] at hz ⊢
      exact h1 hz)
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply, Submodule.coe_inclusion] at hq ⊢
      exact hq
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H z => exact ⟨Submodule.Quotient.mk z, rfl⟩
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · intro hz
        exact ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩
      · rintro ⟨q', hq'⟩
        induction q' using Submodule.Quotient.induction_on with
        | H y =>
          simp only [f, Submodule.mapQ_apply] at hq'
          rw [Submodule.Quotient.eq] at hq'
          simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
            Submodule.coe_inclusion] at hq'
          have h3 : (z : W) = (y : W) - ((y : W) - (z : W)) := by abel
          rw [h3]
          exact Y.sub_mem y.2 (h1 hq')

theorem rlen_mono {X X' Z Z' : Submodule R W} (hX : X' ≤ X) (hXZ : X ≤ Z) (hZ : Z ≤ Z') :
    relative₂ X Z ≤ relative₂ X' Z' := by
  rw [rlen_add hX (hXZ.trans hZ), rlen_add hXZ hZ]
  calc relative₂ X Z ≤ relative₂ X Z + relative₂ Z Z' := le_self_add
    _ ≤ relative₂ X' X + (relative₂ X Z + relative₂ Z Z') := le_add_self

theorem rlen_self (X : Submodule R W) : relative₂ X X = 0 := by
  unfold relative₂
  rw [Module.length_eq_zero_iff]
  constructor
  intro a b
  induction a using Submodule.Quotient.induction_on with
  | H x =>
  induction b using Submodule.Quotient.induction_on with
  | H y =>
    rw [Submodule.Quotient.eq]
    simp

theorem rlen_map {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f) (X Z : Submodule R W) :
    relative₂ (X.map f) (Z.map f) = relative₂ X Z := by
  unfold relative₂
  symm
  refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Z) ?_)
  ext ⟨w, hw⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨z', hz'⟩, hz'X, he⟩
    have : f z' = f z := congrArg Subtype.val he
    rw [← hf this]
    exact ⟨z', hz'X, rfl⟩
  · rintro ⟨z', hz'X, he⟩
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · have := hf he
      simpa [this] using hz'X
    · rfl

end Gen

section Loc

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]

theorem mem_locP {A : Submodule R W} {x : W} :
    x ∈ localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := Iff.rfl

theorem le_locP (A : Submodule R W) : A ≤ localization₂ p A :=
  fun x hx => ⟨1, p.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono {A B : Submodule R W} (h : A ≤ B) : localization₂ p A ≤ localization₂ p B :=
  fun _ ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩

theorem lidx_eq (A B : Submodule R W) :
    lidx p A B = ((relative₂ (localization₂ p (A ⊓ B)) (localization₂ p A)).toNat : ℤ) - (relative₂ (localization₂ p (A ⊓ B)) (localization₂ p B)).toNat :=
  rfl

theorem lidx_antisymm (A B : Submodule R W) : lidx p A B = - lidx p B A := by
  rw [lidx_eq, lidx_eq, inf_comm]; ring

theorem lidx_self (A : Submodule R W) : lidx p A A = 0 := by
  rw [lidx_eq]; ring

theorem lidx_eq_of_le {A B D : Submodule R W} (hD : D ≤ A ⊓ B)
    (hA : relative₂ (localization₂ p D) (localization₂ p A) ≠ ⊤) (hB : relative₂ (localization₂ p D) (localization₂ p B) ≠ ⊤) :
    lidx p A B = ((relative₂ (localization₂ p D) (localization₂ p A)).toNat : ℤ) - (relative₂ (localization₂ p D) (localization₂ p B)).toNat := by
  have e1 := rlen_add (localization_mono p hD) (localization_mono p (inf_le_left : A ⊓ B ≤ A))
  have e2 := rlen_add (localization_mono p hD) (localization_mono p (inf_le_right : A ⊓ B ≤ B))
  rw [e1] at hA ⊢
  rw [e2] at hB ⊢
  rw [lidx_eq]
  have l1 : ∀ a b : ℕ∞, a + b ≠ ⊤ → a ≠ ⊤ := fun a b h ha => h (by simp [ha])
  have l2 : ∀ a b : ℕ∞, a + b ≠ ⊤ → b ≠ ⊤ := fun a b h hb => h (by simp [hb])
  rw [ENat.toNat_add (l1 _ _ hA) (l2 _ _ hA), ENat.toNat_add (l1 _ _ hB) (l2 _ _ hB)]
  push_cast
  ring

theorem lidx_cocycle {A B C D : Submodule R W} (hDA : D ≤ A) (hDB : D ≤ B) (hDC : D ≤ C)
    (hA : relative₂ (localization₂ p D) (localization₂ p A) ≠ ⊤) (hB : relative₂ (localization₂ p D) (localization₂ p B) ≠ ⊤)
    (hC : relative₂ (localization₂ p D) (localization₂ p C) ≠ ⊤) :
    lidx p A C = lidx p A B + lidx p B C := by
  rw [lidx_eq_of_le p (le_inf hDA hDC) hA hC, lidx_eq_of_le p (le_inf hDA hDB) hA hB,
    lidx_eq_of_le p (le_inf hDB hDC) hB hC]
  ring

theorem localization_map₂ {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A : Submodule R W) : localization₂ p (A.map f) = (localization₂ p A).map f := by
  ext y
  simp only [mem_locP, Submodule.mem_map]
  constructor
  · rintro ⟨s, hs, a, ha, hay⟩
    obtain ⟨x, rfl⟩ := hsat s y hs ⟨a, hay⟩
    refine ⟨x, ⟨s, hs, ?_⟩, rfl⟩
    have : f (s • x) = f a := by rw [map_smul, hay]
    rw [hf this]; exact ha
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨s, hs, s • x, hx, by rw [map_smul]⟩

theorem lidx_map {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A B : Submodule R W) : lidx p (A.map f) (B.map f) = lidx p A B := by
  rw [lidx_eq, lidx_eq, ← Submodule.map_inf f hf, localization_map₂ p f hf hsat, localization_map₂ p f hf hsat,
    localization_map₂ p f hf hsat, rlen_map f hf, rlen_map f hf]

theorem relativeLength_localized_map {W' : Type*} [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W')
    (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A B : Submodule R W) :
    relative₂ (localization₂ p (A.map f)) (localization₂ p (B.map f)) = relative₂ (localization₂ p A) (localization₂ p B) := by
  rw [localization_map₂ p f hf hsat, localization_map₂ p f hf hsat, rlen_map f hf]

end Loc

section Sat

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
variable {W W' : Type*} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
  [AddCommGroup W'] [Module K W'] [Module R W'] [IsScalarTower R K W']

theorem sat_of_linear (p : Ideal R) [p.IsPrime] (f : W →ₗ[K] W') (s : R) (y : W')
    (hs : s ∈ p.primeCompl) (hy : s • y ∈ LinearMap.range (f.restrictScalars R)) :
    y ∈ LinearMap.range (f.restrictScalars R) := by
  have hs0 : algebraMap R K s ≠ 0 := by
    intro h
    have : s = 0 := (FaithfulSMul.algebraMap_injective R K) (by simpa using h)
    exact hs (this ▸ p.zero_mem)
  obtain ⟨x, hx⟩ := hy
  refine ⟨(algebraMap R K s)⁻¹ • x, ?_⟩
  simp only [LinearMap.coe_restrictScalars, map_smul] at hx ⊢
  rw [hx, ← algebraMap_smul K s y, smul_smul, inv_mul_cancel₀ hs0, one_smul]

end Sat

end PI.IsoDetW.Loc
