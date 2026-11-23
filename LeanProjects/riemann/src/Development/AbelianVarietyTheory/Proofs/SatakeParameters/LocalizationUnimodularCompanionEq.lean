import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
open NumberField Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F

noncomputable section

namespace GlobalTheory.CompanLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem locS_mono {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) {M M₁ : Submodule (𝓞 E) W}
    (h : M ≤ M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem le_locS {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) (M : Submodule (𝓞 E) W) :
    M ≤ Formalism.HermitianLatticesTheory.locS S M := fun x hx => ⟨1, S.one_mem, by simpa using hx⟩

theorem locS_le_of_le {W : Type*} [AddCommGroup W] [Module (𝓞 E) W] (S : Submonoid (𝓞 E)) {M M₁ : Submodule (𝓞 E) W}
    (h : M ≤ Formalism.HermitianLatticesTheory.locS S M₁) : Formalism.HermitianLatticesTheory.locS S M ≤ Formalism.HermitianLatticesTheory.locS S M₁ := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hx'⟩ := h hx
  refine ⟨t * s, S.mul_mem ht hs, ?_⟩
  rw [mul_smul]
  exact hx'

abbrev conjO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem conjO_mem_hcompl (Q : Ideal (𝓞 E)) {s : 𝓞 E} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q) :
    conjO s ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q := by
  have hle : Formalism.HermitianLatticesTheory.hcompl (K := E) Q ≤ (Formalism.HermitianLatticesTheory.hcompl (K := E) Q).comap (conjO (E := E)).toMonoidHom := by
    unfold Formalism.HermitianLatticesTheory.hcompl
    rw [Submonoid.closure_le]
    rintro s ⟨hs1, hs2⟩
    apply Submonoid.subset_closure
    refine ⟨?_, ?_⟩
    · exact hs2 _ rfl
    · intro t ht hm
      have : t = s := by
        apply RingOfIntegers.ext
        have h1 : (t : E) = star (star (s : E)) := ht
        simpa using h1
      exact hs1 (this ▸ hm)
  exact hle hs

theorem hform_smul_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (c : E) (x y : Fin N → E) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hform_smul_right {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (c : E) (x y : Fin N → E) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem hform_add_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (x x' y : Fin N → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add]
  ring

theorem hform_zero_left {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (y : Fin N → E) :
    Formalism.UG.hform σ J 0 y = 0 := by
  unfold Formalism.UG.hform
  simp

example {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ Formalism.BasicNotions.dualSet σ J L ↔ ∀ x ∈ L, Formalism.UG.hform σ J x y ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

theorem smul_coe {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (c : 𝓞 E) (w : W) :
    c • w = (c : E) • w := (algebraMap_smul E c w).symm

theorem span_dual_le {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E))
    (hfg : Λ₁.FG) (h : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ) :
    Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (starRingEnd E) J Λ) ≤
      Formalism.HermitianLatticesTheory.loc (K := E) Q (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (starRingEnd E) J Λ₁)) := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have hg : ∀ g ∈ s, ∃ t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q, t • g ∈ Λ := fun g hg => h (Submodule.subset_span hg)
  choose t ht hts using hg
  set u : 𝓞 E := ∏ g ∈ s.attach, conjO (t g.1 g.2) with hu
  have hu_mem : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) Q :=
    Submonoid.prod_mem _ fun g _ => conjO_mem_hcompl Q (ht g.1 g.2)
  rw [Submodule.span_le]
  intro y hy
  refine ⟨u, hu_mem, Submodule.subset_span ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hgs =>
    rw [smul_coe, hform_smul_right]
    have e : u = (∏ g' ∈ s.attach.erase ⟨g, hgs⟩, conjO (t g'.1 g'.2)) * conjO (t g hgs) := by
      rw [hu]
      exact (Finset.prod_erase_mul _ _ (Finset.mem_attach _ _)).symm
    have h2 : Formalism.UG.hform (starRingEnd E) J (t g hgs • g) y ∈ (algebraMap (𝓞 E) E).range := hy _ (hts g hgs)
    rw [smul_coe, hform_smul_left] at h2
    rw [e, show ∀ A B : 𝓞 E, ((A * B : 𝓞 E) : E) = (A : E) * (B : E) from fun _ _ => rfl, mul_assoc]
    refine Subring.mul_mem _ ⟨_, rfl⟩ ?_
    exact h2
  | zero => rw [hform_zero_left]; exact Subring.zero_mem _
  | add x x' _ _ hx hx' => rw [hform_add_left]; exact Subring.add_mem _ hx hx'
  | smul c x _ hx =>
    rw [smul_coe, hform_smul_left]
    exact Subring.mul_mem _ ⟨conjO c, rfl⟩ hx

theorem compan_le_loc {R : Ranks} {F : Type} [Field F] [NumberField F] [Algebra F E] (sp : Spaces R F E) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)) (hfg : Λ₁.FG)
    (h : Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁) (h₁ : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ) :
    compan (sp := sp) J a Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  have hσ : (sp.cm.sig : E →+* E) = starRingEnd E := RingHom.ext fun _ => rfl
  unfold compan
  rw [hσ]
  apply sup_le
  · exact h.trans (locS_mono _ le_sup_left)
  · rw [Submodule.smul_le]
    intro r hr n hn
    obtain ⟨s, hs, hsn⟩ := span_dual_le J Q Λ Λ₁ hfg h₁ hn
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsn)

end GlobalTheory.CompanLoc

namespace GlobalTheory

theorem loc_compan_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)),
    Λ.FG → Λ₁.FG → Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ →
    Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  intro R F E _ _ _ _ _ _ sp N J a Q Λ Λ₁ hfg hfg₁ h
  have h1 : Λ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ := (CompanLoc.le_locS _ Λ).trans h.le
  have h2 : Λ₁ ≤ Formalism.HermitianLatticesTheory.loc (K := E) Q Λ := (CompanLoc.le_locS _ Λ₁).trans h.ge
  exact le_antisymm (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ Λ₁ hfg₁ h1 h2))
    (CompanLoc.locS_le_of_le _ (CompanLoc.compan_le_loc sp J a Q Λ₁ Λ hfg h2 h1))

end GlobalTheory
