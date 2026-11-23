import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.HullClasses

variable {K : UQ} (B : InvAlg K)

abbrev abelian₂ : Submodule K.O B.A := Subalgebra.toSubmodule (integralClosure K.O B.A)

lemma mem_mulLat {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t y : A) (L : Submodule O A) :
    y ∈ mulLat O t L ↔ ∃ z ∈ L, t * z = y := by
  simp [mulLat]

lemma mulLat_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (s t : A) (L : Submodule O A) :
    mulLat O (s * t) L = mulLat O s (mulLat O t L) := by
  ext y; simp only [mem_mulLat]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨t * z, ⟨z, hz, rfl⟩, by ring⟩
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, by ring⟩

lemma mulLat_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) :
    mulLat O 1 L = L := by
  ext y; simp [mem_mulLat]

lemma mulLat_le_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (r s t : A) (L : Submodule O A)
    (h : mulLat O s L ≤ mulLat O t L) : mulLat O (r * s) L ≤ mulLat O (r * t) L := by
  rw [mulLat_mul, mulLat_mul]; exact Submodule.map_mono h

lemma one_mem_Lam : (1 : B.A) ∈ abelian₂ B := by
  simp [abelian₂]

lemma mem_Lam_iff (y : B.A) : y ∈ abelian₂ B ↔ IsIntegral K.O y := by
  simp [abelian₂, mem_integralClosure_iff]

lemma mulLat_intUnit (u : B.Aˣ) (hu : u ∈ intUnits K.O B.A) : mulLat K.O (u : B.A) (abelian₂ B) = abelian₂ B := by
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := (mem_mulLat _ _ _).1 hy
    rw [mem_Lam_iff] at hz ⊢
    exact hu.1.mul hz
  · intro y hy
    refine (mem_mulLat _ _ _).2 ⟨((u⁻¹ : B.Aˣ) : B.A) * y, ?_, ?_⟩
    · rw [mem_Lam_iff] at hy ⊢
      exact hu.2.mul hy
    · rw [← mul_assoc, Units.mul_inv, one_mul]

lemma intUnit_of_mulLat (v : B.Aˣ) (h : mulLat K.O (v : B.A) (abelian₂ B) = abelian₂ B) : v ∈ intUnits K.O B.A := by
  have h1 : (v : B.A) ∈ abelian₂ B := by
    rw [← h]; exact (mem_mulLat _ _ _).2 ⟨1, one_mem_Lam B, mul_one _⟩
  have h2 : (1 : B.A) ∈ mulLat K.O (v : B.A) (abelian₂ B) := by rw [h]; exact one_mem_Lam B
  obtain ⟨z, hz, hvz⟩ := (mem_mulLat _ _ _).1 h2
  have hz' : ((v⁻¹ : B.Aˣ) : B.A) = z := by
    calc ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) * ((v : B.A) * z) := by rw [hvz, mul_one]
      _ = z := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [mem_Lam_iff] at h1 hz
  exact ⟨h1, hz' ▸ hz⟩

lemma isLat_mulLat (u : B.Aˣ) {L : Submodule K.O B.A} (hL : IsLat K.O K.E L) :
    IsLat K.O K.E (mulLat K.O (u : B.A) L) := by
  refine ⟨hL.1.map _, ?_⟩
  have : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) =
      (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A) := by
    ext y; simp [mulLat]
  rw [this, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y; exact ⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp⟩

lemma sigma_algebraMap (c cb : K.O) (h : K.c (algebraMap K.O K.E c) = algebraMap K.O K.E cb) :
    B.σ (algebraMap K.O B.A c) = algebraMap K.O B.A cb := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, h, ← IsScalarTower.algebraMap_apply]

lemma key (x : B.A) (c cb : K.O) (hc : B.σ (algebraMap K.O B.A c) = algebraMap K.O B.A cb) (a b : B.Aˣ)
    (h4 : ∀ y ∈ mulLat K.O (a : B.A) (abelian₂ B), ∀ z ∈ mulLat K.O (a : B.A) (abelian₂ B),
      B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range)
    (h3 : ∀ y, (∀ z ∈ mulLat K.O (b : B.A) (abelian₂ B), B.herm x y z ∈ (algebraMap K.O K.E).range) →
      y ∈ mulLat K.O (b : B.A) (abelian₂ B)) :
    mulLat K.O (algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a)) (abelian₂ B) ≤
      mulLat K.O ((b : B.A) * B.σ b) (abelian₂ B) := by
  intro y hy
  obtain ⟨l, hl, rfl⟩ := (mem_mulLat _ _ _).1 hy
  have hb : B.σ (b : B.A) * B.σ ((b⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hy' : algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a) * l * B.σ ((b⁻¹ : B.Aˣ) : B.A) ∈
      mulLat K.O (b : B.A) (abelian₂ B) := by
    apply h3
    intro z hz
    obtain ⟨m, hm, rfl⟩ := (mem_mulLat _ _ _).1 hz
    have := h4 _ ((mem_mulLat _ _ _).2 ⟨l, hl, rfl⟩) _ ((mem_mulLat _ _ _).2 ⟨m, hm, rfl⟩)
    convert this using 1
    unfold InvAlg.herm
    congr 1
    simp only [map_mul, hc]
    linear_combination (x * algebraMap K.O B.A c * algebraMap K.O B.A cb * (a : B.A) * B.σ (a : B.A) * l *
      B.σ m) * hb
  obtain ⟨n, hn, hbn⟩ := (mem_mulLat _ _ _).1 hy'
  refine (mem_mulLat _ _ _).2 ⟨n, hn, ?_⟩
  linear_combination B.σ (b : B.A) * hbn +
    (algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a) * l) * hb

end GlobalTheory.HullClasses

noncomputable section
namespace GlobalTheory.HullClasses

theorem finite_mod_T_of (K : UQ) (B : InvAlg K)
    (hPr : ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
      ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)))
    (hNu : ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ, (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) →
      ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A)
    (hBe : ∀ (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 →
      {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite)
    (x : B.A) (c : K.O) (hc0 : c ≠ 0) :
    ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by
  classical
  obtain ⟨cb, hcb⟩ := K.c_int c
  have hσc := sigma_algebraMap B c cb hcb
  have hcb0 : cb ≠ 0 := by
    rintro rfl
    rw [map_zero, map_eq_zero_iff _ K.c.injective] at hcb
    exact hc0 ((IsFractionRing.injective K.O K.E) (by rw [hcb, map_zero]))
  set d : K.O := c * cb with hd
  have hd0 : d ≠ 0 := mul_ne_zero hc0 hcb0
  have hdd0 : d * d ≠ 0 := mul_ne_zero hd0 hd0
  have hDu : IsUnit (algebraMap K.O B.A d) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    refine (IsUnit.mk0 _ ?_).map _
    rw [Ne, ← map_zero (algebraMap K.O K.E)]
    exact (IsFractionRing.injective K.O K.E).ne hd0
  set D : B.Aˣ := hDu.unit
  have hDc : (D : B.A) = algebraMap K.O B.A d := hDu.unit_spec
  let σU : B.Aˣ →* B.Aˣ := Units.map B.σ.toMonoidHom
  have hσU : ∀ a : B.Aˣ, ((σU a : B.Aˣ) : B.A) = B.σ (a : B.A) := fun a => rfl
  let Nu : B.Aˣ → B.Aˣ := fun a => a * σU a
  have hNuc : ∀ a, ((Nu a : B.Aˣ) : B.A) = (a : B.A) * B.σ (a : B.A) := fun a => by simp [Nu, hσU]
  let Λ := abelian₂ B
  let adm : B.Aˣ → Prop := fun a =>
    (∀ y, (∀ z ∈ mulLat K.O (a : B.A) Λ, B.herm x y z ∈ (algebraMap K.O K.E).range) →
      y ∈ mulLat K.O (a : B.A) Λ) ∧
    (∀ y ∈ mulLat K.O (a : B.A) Λ, ∀ z ∈ mulLat K.O (a : B.A) Λ,
      B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range)
  by_cases hex : ∃ a₀ : B.Aˣ, IsLat K.O K.E (mulLat K.O (a₀ : B.A) Λ) ∧ adm a₀
  swap
  · refine ⟨∅, Set.finite_empty, by simp, ?_⟩
    intro J hJ hst h3 h4
    obtain ⟨a, rfl⟩ := hPr J hJ hst
    exact (hex ⟨a, hJ, h3, h4⟩).elim
  obtain ⟨a₀, hJ₀, hadm₀⟩ := hex
  have hΛ : IsLat K.O K.E Λ := by
    have := isLat_mulLat B a₀⁻¹ hJ₀
    rwa [← mulLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mulLat_one] at this
  let Mf : B.Aˣ → Submodule K.O B.A := fun a => mulLat K.O ((D * Nu a * (Nu a₀)⁻¹ : B.Aˣ) : B.A) Λ
  let Bset := {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (d * d)) Λ ≤ M ∧ M ≤ Λ}
  have hcancel : ∀ a : B.Aˣ, mulLat K.O (((a⁻¹ : B.Aˣ) : B.A) * a) Λ = Λ := fun a => by
    rw [Units.inv_mul, mulLat_one]
  have hM : ∀ a, adm a → Mf a ∈ Bset := by
    intro a ha
    have k1 := key B x c cb hσc a a₀ ha.2 hadm₀.1
    have k2 := key B x c cb hσc a₀ a hadm₀.2 ha.1
    constructor
    · have := mulLat_le_mul (((D * (Nu a₀)⁻¹ : B.Aˣ) : B.A)) _ _ Λ k2
      convert this using 2
      · rw [map_mul, ← hDc, ← hNuc]
        simp only [Units.val_mul]
        calc (D : B.A) * D = D * D * (((Nu a₀)⁻¹ : B.Aˣ) * (Nu a₀ : B.A)) := by rw [Units.inv_mul, mul_one]
          _ = _ := by ring
      · rw [← hNuc]; simp only [Units.val_mul, Mf]; ring
    · have := mulLat_le_mul ((((Nu a₀)⁻¹ : B.Aˣ)) : B.A) _ _ Λ k1
      rw [← hNuc, ← hNuc, hcancel] at this
      convert this using 2
      simp only [Units.val_mul]; rw [hDc, hd]; ring
  let gch : Submodule K.O B.A → B.Aˣ := fun M => if h : ∃ a, adm a ∧ Mf a = M then h.choose else 1
  obtain ⟨F, hF⟩ := hNu
  refine ⟨(fun p : Submodule K.O B.A × B.Aˣ => mulLat K.O ((gch p.1 * p.2 : B.Aˣ) : B.A) Λ) ''
    (Bset ×ˢ (F : Set B.Aˣ)), ((hBe Λ hΛ (d * d) hdd0).prod F.finite_toSet).image _, ?_, ?_⟩
  · rintro J ⟨p, -, rfl⟩
    exact isLat_mulLat B _ hΛ
  intro J hJ hst h3 h4
  obtain ⟨a, rfl⟩ := hPr J hJ hst
  have ha : adm a := ⟨h3, h4⟩
  have hex' : ∃ a', adm a' ∧ Mf a' = Mf a := ⟨a, ha, rfl⟩
  have hg : gch (Mf a) = hex'.choose := dif_pos hex'
  obtain ⟨ha', hMa'⟩ := hex'.choose_spec
  set a' := hex'.choose

  have hv : Nu a * (Nu a')⁻¹ ∈ intUnits K.O B.A := by
    apply intUnit_of_mulLat
    have e1 : ((Nu a * (Nu a')⁻¹ : B.Aˣ) : B.A) =
        (((D * Nu a' * (Nu a₀)⁻¹)⁻¹ : B.Aˣ) : B.A) * ((D * Nu a * (Nu a₀)⁻¹ : B.Aˣ) : B.A) := by
      rw [← Units.val_mul]; congr 1; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
    rw [e1, mulLat_mul]
    change mulLat K.O _ (Mf a) = Λ
    rw [← hMa']
    change mulLat K.O _ (mulLat K.O _ Λ) = Λ
    rw [← mulLat_mul, hcancel]
  set u : B.Aˣ := a * a'⁻¹
  have hu : ∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u := by
    refine ⟨_, hv, ?_⟩
    rw [← hNuc]; congr 1; simp only [Nu, u, map_mul, map_inv]; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
  obtain ⟨f, hf, t, ht, hw⟩ := hF u hu
  refine ⟨t⁻¹, B.T.inv_mem ht, ⟨(Mf a, f), ⟨hM a ha, hf⟩, ?_⟩⟩
  have e2 : t⁻¹ * a = a' * f * (u * f⁻¹ * t⁻¹) := by simp only [u]; (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)
  show mulLat K.O ((gch (Mf a) * f : B.Aˣ) : B.A) Λ = mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (a : B.A) Λ)
  rw [hg, ← mulLat_mul, ← Units.val_mul, e2, Units.val_mul (a' * f), mulLat_mul _ _ Λ, mulLat_intUnit B _ hw]

end GlobalTheory.HullClasses
