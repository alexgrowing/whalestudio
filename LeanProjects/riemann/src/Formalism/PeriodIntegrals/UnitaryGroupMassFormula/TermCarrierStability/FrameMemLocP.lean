import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem osmul (o : 𝓞 E) (v : S.V) : o • v = (o : E) • v :=
  (algebraMap_smul E o v).symm

theorem one_nmem (p : Ideal (𝓞 E)) [hp : p.IsPrime] : (1 : 𝓞 E) ∉ p :=
  (Ideal.ne_top_iff_one p).mp hp.ne_top

def locInt (p : Ideal (𝓞 E)) [hp : p.IsPrime] : Subring E where
  carrier := {c | ∃ s : 𝓞 E, s ∉ p ∧ ∃ a : 𝓞 E, (s : E) * c = a}
  mul_mem' := by
    rintro c₁ c₂ ⟨s₁, hs₁, a₁, h₁⟩ ⟨s₂, hs₂, a₂, h₂⟩
    refine ⟨s₁ * s₂, fun h => (hp.mem_or_mem h).elim hs₁ hs₂, a₁ * a₂, ?_⟩
    push_cast
    linear_combination ((s₂ : E) * c₂) * h₁ + (a₁ : E) * h₂
  one_mem' := ⟨1, one_nmem p, 1, by simp⟩
  add_mem' := by
    rintro c₁ c₂ ⟨s₁, hs₁, a₁, h₁⟩ ⟨s₂, hs₂, a₂, h₂⟩
    refine ⟨s₁ * s₂, fun h => (hp.mem_or_mem h).elim hs₁ hs₂, a₁ * s₂ + s₁ * a₂, ?_⟩
    push_cast
    linear_combination (s₂ : E) * h₁ + (s₁ : E) * h₂
  zero_mem' := ⟨1, one_nmem p, 0, by simp⟩
  neg_mem' := by
    rintro c ⟨s, hs, a, h⟩
    exact ⟨s, hs, -a, by push_cast; linear_combination -h⟩

theorem mem_locInt {p : Ideal (𝓞 E)} [p.IsPrime] {c : E} :
    c ∈ locInt p ↔ ∃ s : 𝓞 E, s ∉ p ∧ ∃ a : 𝓞 E, (s : E) * c = a := Iff.rfl

theorem coe_mem_locInt (p : Ideal (𝓞 E)) [p.IsPrime] (a : 𝓞 E) : (a : E) ∈ locInt p :=
  ⟨1, one_nmem p, a, by simp⟩

theorem approx (G : 𝓞 E) (μ : E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), G ∈ P.asIdeal → (haveI := P.isPrime; μ ∈ locInt P.asIdeal)) :
    ∃ c : 𝓞 E, ∀ P : HeightOneSpectrum (𝓞 E), G ∈ P.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ w : 𝓞 E, (s : E) * ((c : E) - μ) = (G : E) * w := by
  let J : Ideal (𝓞 E) :=
    { carrier := {s | ∃ a : 𝓞 E, (s : E) * μ = a}
      add_mem' := by
        rintro s t ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by push_cast; linear_combination ha + hb⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c s ⟨a, ha⟩
        exact ⟨c * a, by simp only [smul_eq_mul]; push_cast; linear_combination (c : E) * ha⟩ }
  have hJ : J ⊔ Ideal.span {G} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hne' : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
    let P : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hne'⟩
    have hG : G ∈ P.asIdeal := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self G))
    obtain ⟨s, hs, a, ha⟩ := h P hG
    have hsJ : s ∈ J := ⟨a, ha⟩
    exact hs (hle (Ideal.mem_sup_left hsJ))
  have h1 : (1 : 𝓞 E) ∈ J ⊔ Ideal.span {G} := hJ ▸ Submodule.mem_top
  obtain ⟨y, hyJ, w', hw', hyw⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, ha⟩ := hyJ
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hw'
  refine ⟨a, fun P hP => ?_⟩
  obtain ⟨s, hs, b, hb⟩ := h P hP
  refine ⟨s, hs, -(w * b), ?_⟩
  have hy : (y : E) = 1 - (w : E) * G := by
    have := congrArg (fun t : 𝓞 E => (t : E)) hyw
    push_cast at this
    linear_combination this
  push_cast
  linear_combination (-(s : E)) * ha + ((s : E) * μ) * hy - (G : E) * (w : E) * hb

theorem mem_locP {p : Ideal (𝓞 E)} [p.IsPrime] {L : Submodule (𝓞 E) S.V} {v : S.V} :
    v ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s : 𝓞 E, s ∉ p ∧ s • v ∈ L := by
  constructor
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, h⟩

theorem localization_mono {p : Ideal (𝓞 E)} [p.IsPrime] {L L' : Submodule (𝓞 E) S.V} (h : L ≤ L') {v : S.V}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  obtain ⟨s, hs, hv⟩ := mem_locP.mp hv
  exact mem_locP.mpr ⟨s, hs, h hv⟩

theorem smul_mem_locP {p : Ideal (𝓞 E)} [hp : p.IsPrime] {L : Submodule (𝓞 E) S.V} {c : E} {v : S.V}
    (hc : c ∈ locInt p) (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : c • v ∈ Formalism.HermitianLatticesTheory.localization₂ p L := by
  obtain ⟨s, hs, a, ha⟩ := hc
  obtain ⟨t, ht, hv⟩ := mem_locP.mp hv
  refine mem_locP.mpr ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
  have : (s * t) • (c • v) = a • (t • v) := by
    simp only [osmul, smul_smul]
    congr 1
    push_cast
    rw [← ha]; ring
  rw [this]; exact L.smul_mem a hv

theorem lin_osmul (β : S.V ≃ₗ[E] S.V) (s : 𝓞 E) (v : S.V) : β (s • v) = s • β v := by
  simp only [osmul, map_smul]

theorem localization_map₂ {p : Ideal (𝓞 E)} [p.IsPrime] {L : Submodule (𝓞 E) S.V} (β : S.V ≃ₗ[E] S.V)
    (hβ : ∀ y ∈ L, β y ∈ L) {v : S.V} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : β v ∈ Formalism.HermitianLatticesTheory.localization₂ p L := by
  obtain ⟨s, hs, hv⟩ := mem_locP.mp hv
  exact mem_locP.mpr ⟨s, hs, by rw [← lin_osmul]; exact hβ _ hv⟩

theorem mem_gsmul {G : 𝓞 E} {Λ : Submodule (𝓞 E) S.V} {v : S.V} :
    v ∈ Ideal.span {G} • Λ ↔ ∃ w ∈ Λ, G • w = v := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]

theorem gsmul_map {G : 𝓞 E} {Λ : Submodule (𝓞 E) S.V} (β : S.V ≃ₗ[E] S.V) (hβ : ∀ y ∈ Λ, β y ∈ Λ) :
    ∀ y ∈ Ideal.span {G} • Λ, β y ∈ Ideal.span {G} • Λ := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := mem_gsmul.mp hy
  exact mem_gsmul.mpr ⟨β w, hβ w hw, (lin_osmul β G w).symm⟩

theorem gsmem {p : Ideal (𝓞 E)} [hp : p.IsPrime] {G : 𝓞 E} {Λ : Submodule (𝓞 E) S.V} {d : E} {v : S.V}
    {s w : 𝓞 E} (hs : s ∉ p) (hd : (s : E) * d = (G : E) * w) (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ) :
    d • v ∈ Formalism.HermitianLatticesTheory.localization₂ p (Ideal.span {G} • Λ) := by
  obtain ⟨t, ht, hv⟩ := mem_locP.mp hv
  refine mem_locP.mpr ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
  have : (s * t) • (d • v) = G • (w • (t • v)) := by
    simp only [osmul, smul_smul]
    congr 1
    push_cast
    linear_combination (t : E) * hd
  rw [this]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self G) (Λ.smul_mem w hv)

def frE {n : ℕ} (f : Fin n → S.V) (A : Matrix (Fin n) (Fin n) E) : Fin n → S.V :=
  fun b => ∑ a, A a b • f a

theorem frE_mul {n : ℕ} (f : Fin n → S.V) (A B : Matrix (Fin n) (Fin n) E) :
    frE (frE f A) B = frE f (A * B) := by
  funext b
  simp only [frE, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

theorem frE_add {n : ℕ} (f h : Fin n → S.V) (A : Matrix (Fin n) (Fin n) E) (b : Fin n) :
    frE (fun a => f a + h a) A b = frE f A b + frE h A b := by
  simp only [frE, smul_add, Finset.sum_add_distrib]

theorem frE_map {n : ℕ} (β : S.V ≃ₗ[E] S.V) (f : Fin n → S.V) (A : Matrix (Fin n) (Fin n) E) (b : Fin n) :
    β (frE f A b) = frE (fun a => β (f a)) A b := by
  simp only [frE, map_sum, map_smul]

def UT {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : Prop := (∀ a b, b < a → A a b = 0) ∧ ∀ a, A a a = 1

theorem UT.mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : UT A) (hB : UT B) : UT (A * B) := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hba h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2, hB.2, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem mul_mem_locInt {p : Ideal (𝓞 E)} [p.IsPrime] {n : ℕ} {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ a b, A a b ∈ locInt p) (hB : ∀ a b, B a b ∈ locInt p) : ∀ a b, (A * B) a b ∈ locInt p := by
  intro a b
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hA a c) (hB c b)

theorem frame_castSucc {T : E} (F : LFlag S r T) (k : Fin r) : frame F k.castSucc = F.fl.e k := by
  simp [frame, FlagG.fvec]

theorem frame_last {T : E} (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem frame_mem_locP {T : E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (hz : F.fl.z ∈ Λ)
    (hc : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E)) (hP : (g : 𝓞 E) ∈ P.asIdeal) (a : Fin (r + 1)) :
    (haveI := P.isPrime; frame F a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  induction a using Fin.lastCases with
  | last => rw [frame_last]; exact mem_locP.mpr ⟨1, one_nmem _, by rw [one_smul]; exact hz⟩
  | cast k =>
    rw [frame_castSucc]
    obtain ⟨c, _, hc1, heq⟩ := hc.1 P
    have hk : F.fl.e k ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
      rw [heq]
      refine mem_locP.mpr ⟨1, one_nmem _, ?_⟩
      rw [one_smul]
      refine Submodule.subset_span ⟨k, ?_⟩
      simp [hc1 hP k]
    exact localization_mono inf_le_left hk

end Gen

end PI.TCS
