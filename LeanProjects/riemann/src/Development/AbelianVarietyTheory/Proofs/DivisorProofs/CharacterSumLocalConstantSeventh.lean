import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFourth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond

noncomputable section

namespace GlobalTheory.ColNorms.DatOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

section Generic

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem mem_lamY_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + c)) :
    v ∈ LocE.lamY P q n c ex ↔ ∀ l : Fin (n + c), Formalism.L2.Col.IntAt P (((q : E) ^ LocE.scE n ex l.1)⁻¹ * v l) := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap]
  exact mem_localization_standardLattice P _

theorem proj_mem {P : HeightOneSpectrum (𝓞 E)} {q n c : ℕ} {ex : ℕ → ℕ} {v : Sp E (n + c)} (hv : v ∈ LocE.lamY P q n c ex) :
    LinearMap.funLeft E E (Fin.castAdd c) v ∈ stdAt E n P := by
  refine (mem_localization_standardLattice P _).2 fun i => ?_
  have h := (mem_lamY_iff P q n c ex v).1 hv (Fin.castAdd c i)
  simpa [LocE.scE, LinearMap.funLeft_apply] using h

theorem proj_inX {n c : ℕ} (y : Sp E n) : LinearMap.funLeft E E (Fin.castAdd c) (Loc.inX E n c y) = y := by
  funext i
  simp [LinearMap.funLeft_apply, Loc.inX]

theorem inX_mem_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (y : Sp E n) :
    Loc.inX E n c y ∈ LocE.lamY P q n c ex ↔ y ∈ stdAt E n P := by
  constructor
  · intro h
    simpa [proj_inX] using proj_mem h
  · intro h
    refine (mem_lamY_iff P q n c ex _).2 fun l => ?_
    by_cases hl : l.1 < n
    · have := (mem_localization_standardLattice P _).1 h ⟨l.1, hl⟩
      simpa [LocE.scE, Loc.inX, hl] using this
    · have := Formalism.L2.Col.IntAt.coe P (0 : 𝓞 E)
      simpa [Loc.inX, hl] using this

theorem joinCol_inX {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (y : Sp E n') :
    (joinCol x₀ y' : HomE E (n' + c') (n + c)) (Loc.inX E n' c' y) = Loc.inX E n c (x₀ y) := by
  have h0 : atNL E (n' + c') n' (Loc.inX E n' c' y) = 0 := by
    unfold atNL
    split_ifs with h
    · simp [Loc.inX]
    · rfl
  simp [joinCol, proj_inX, h0]

theorem joinCol_add {n' c' n c : ℕ} (x₀ z : HomE E n' n) (t : E) (y' : Sp E n) :
    (joinCol (x₀ + t • z) y' : HomE E (n' + c') (n + c)) =
      joinCol x₀ y' + t • (Loc.inX E n c ∘ₗ z ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) := by
  refine LinearMap.ext fun v => ?_
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  abel

theorem locSmall_joinCol {P : HeightOneSpectrum (𝓞 E)} {q n' c' n c : ℕ} {ex' ex : ℕ → ℕ} {Φ : HomE E (n' + c') (n + c) → K} {β : ℝ}
    (h : LocSmall q (LocE.lamY P q n' c' ex') (LocE.lamY P q n c ex) Φ β) (y' : Sp E n) :
    LocSmall q (stdAt E n' P) (stdAt E n P) (fun x₀ => Φ (joinCol x₀ y')) β := by
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => h.2.2 σ _⟩
  · have := h.1 _ hx _ ((inX_mem_iff P q n' c' ex' y).2 hy)
    rw [joinCol_inX] at this
    exact (inX_mem_iff P q n c ex _).1 this
  · show Φ (joinCol (x + (q : E) • z) y') = Φ (joinCol x y')
    rw [joinCol_add]
    exact h.2.1 _ _ fun v hv => (inX_mem_iff P q n c ex _).2 (hz _ (proj_mem hv))

theorem smallDatum_of_frames {a b : ℕ} {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} [DecidableEq (HeightOneSpectrum (𝓞 E))]
    (d : Deco E a ST SG) (d' : DecoSet E b ST SG')
    (f : Frs E a SB) (f' : Frs E b SB) (hf : ∀ (P : SB) x, f P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1)
    (hf' : ∀ (P : SB) x, f' P x ∈ d'.1.at P.1 ↔ x ∈ stdAt E b P.1) (c : ℕ) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (hT : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (Ψ : SB → HomE E a b → K) (β : SB → ℝ)
    (hΨ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Ψ P) (β P)) :
    SmallDatum (ST ∪ SB) d.N d'.1.N c (fun x => phiT K d d'.1 x * ∏ P : SB, Ψ P (inFr (f P) (f' P) x)) (∏ P, β P) := by
  refine ⟨fun x hx P hP y hy => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rcases Finset.mem_union.1 hP with hP | hP
    · unfold phiT at h1
      split_ifs at h1 with h
      · exact (h ⟨P, hP⟩ y hy).1
      · exact absurd rfl h1
    · have h3 := Finset.prod_ne_zero_iff.1 h2 ⟨P, hP⟩ (Finset.mem_univ _)
      have h4 : (f ⟨P, hP⟩).symm y ∈ stdAt E a P := (hf ⟨P, hP⟩ _).1 (by simpa using hy)
      have h5 := (hf' ⟨P, hP⟩ _).2 ((hΨ ⟨P, hP⟩).1 _ h3 _ h4)
      simpa [inFr] using h5
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    have hz' : ∀ P ∈ ST ∪ SB, ∀ y ∈ d.at P, z y ∈ d'.1.at P := hz
    have e0 : (((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z) = (c : 𝓞 E) • z := rfl
    rw [e0]
    show phiT K d d'.1 _ * _ = phiT K d d'.1 _ * _
    congr 1
    · unfold phiT
      classical
      refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun P => forall_congr' fun y => forall_congr' fun hy => ?_) rfl rfl
      have hzy : z y ∈ d'.1.at P.1 := hz' P.1 (Finset.mem_union_left _ P.2) y hy
      have hc : (c : 𝓞 E) • z y ∈ d'.1.at P.1 := Submodule.smul_mem _ _ hzy
      have e : (x + (c : 𝓞 E) • z) y = x y + (c : 𝓞 E) • z y := rfl
      rw [e, Submodule.add_mem_iff_left _ hc]
      refine and_congr_right fun hx => ?_
      rw [d'.2.f_add P _ hx _ hc, d'.2.f_smul P _ _ hzy, Ideal.Quotient.eq_zero_iff_mem.2 (hT P.1 P.2), zero_mul, add_zero]
    · refine Finset.prod_congr rfl fun P _ => ?_
      obtain ⟨k, hk⟩ := hq P
      have e : inFr (f P) (f' P) (x + (c : 𝓞 E) • z) =
          inFr (f P) (f' P) x + (q P : E) • inFr (f P) (f' P) (k • z) := by
        refine LinearMap.ext fun v => ?_
        have : (c : 𝓞 E) • z = (q P : E) • (k • z) := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hk, mul_smul]
        rw [this]
        simp [inFr]
      rw [e]
      refine (hΨ P).2.1 _ _ fun v hv => (hf' P _).1 ?_
      have := nsmul_mem (hz' P.1 (Finset.mem_union_right _ P.2) _ ((hf P v).2 hv)) k
      simpa [inFr] using this
  · show ‖σ (phiT K d d'.1 x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ‖σ (phiT K d d'.1 x)‖ ≤ 1 := by
      unfold phiT
      split_ifs <;> simp
    have h2 : ∏ P : SB, ‖σ (Ψ P (inFr (f P) (f' P) x))‖ ≤ ∏ P, β P :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P _ => (hΨ P).2.2 σ _
    calc _ ≤ 1 * ∏ P, β P := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end Generic

end GlobalTheory.ColNorms.DatOne
