import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitelyManyIsoClassesProjectiveNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersProjectiveModuleIntFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesPolarizedFanLevelStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFunEqMinIntLinearFormsOnConesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsBalancedFormsUptoAutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportClassMinimisersAlongLinearEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.FinTypes

theorem single : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (ι : ℕ) (L : Finset ((Fin n → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  classical
  intro O _ bar φ Y _ _ _ _ hY n N _ hN3 hNo eb μ hμ b₀ hb₀ hpos hmin
  obtain ⟨p, m, γ, hcone, hcov⟩ := GlobalTheory.T.exists_finite_cones_polarized_fan_level_structure O bar φ Y hY n N hN3 eb μ hμ b₀ hb₀ hpos hmin
  obtain ⟨Nℓ, ℓ, hNℓ, hℓ⟩ := GlobalTheory.T.exists_invFun_eq_min_intLinearForms_on_cones O bar φ Y p m γ hcone
  choose D ν hD hν using fun i : Fin p => GlobalTheory.T.linForm_symmBilin_eq_sum_lifts_odd Y n N hN3 hNo eb μ hμ (ℓ i)
  obtain ⟨E, hDE⟩ : ∃ E : Fin p → ℕ, ∀ i, D i * E i = ∏ j, D j :=
    ⟨fun i => ∏ j ∈ Finset.univ.erase i, D j, fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)⟩
  have hDp : 0 < ∏ j, D j := Finset.prod_pos (fun j _ => hD j)
  refine ⟨Nℓ * ∏ j, D j, Finset.univ.image (fun i c => (E i : ℤ) * ν i c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hNℓ.ne' hDp.ne')
  intro b' hb' hp hm
  have hcv := hcov b' hb' hp hm
  obtain ⟨hle, i1, heq⟩ := hℓ b' hb' hp hcv
  have key : ∀ i, ∑ c, (((E i : ℤ) * ν i c : ℤ) : ℝ) * ((b' (μ c) (μ c) : ℤ) : ℝ)
      = ((E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := by
    intro i
    have h' : (((∑ c, ν i c * b' (μ c) (μ c) : ℤ)) : ℝ) = (((D i : ℤ) * ℓ i b' : ℤ) : ℝ) := by
      rw [hν i b' hb'.1]
    push_cast at h' ⊢
    calc ∑ c, (E i : ℝ) * (ν i c : ℝ) * (b' (μ c) (μ c) : ℝ)
        = (E i : ℝ) * ∑ c, (ν i c : ℝ) * (b' (μ c) (μ c) : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_); ring
      _ = _ := by rw [h']; ring
  have hι : ∀ i, ((Nℓ * ∏ j, D j : ℕ) : ℝ) = ((E i : ℝ) * (D i : ℝ)) * (Nℓ : ℝ) := by
    intro i; rw [← hDE i]; push_cast; ring
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hν'
    have hc : (0 : ℝ) ≤ (E i : ℝ) * (D i : ℝ) := by positivity
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * φ.evalZ b'
        = ((E i : ℝ) * (D i : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i]; ring
      _ ≤ ((E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := mul_le_mul_of_nonneg_left (hle i) hc
      _ = _ := (key i).symm
  · refine ⟨_, Finset.mem_image.mpr ⟨i1, Finset.mem_univ _, rfl⟩, ?_⟩
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * φ.evalZ b'
        = ((E i1 : ℝ) * (D i1 : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i1]; ring
      _ = ((E i1 : ℝ) * (D i1 : ℝ)) * ((ℓ i1 b' : ℤ) : ℝ) := by rw [heq]
      _ = _ := (key i1).symm

theorem P1 : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ (ι : ℕ) (𝓛₀ : Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y), ∀ b ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((ebX (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛₀, ∀ b' ∈ balForms bar X, (∀ x, 0 ≤ b' x x) → (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  classical
  intro O _ bar φ Y _ _ _ _ hY n N _ hN3 hNo ebY
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_minimiser_systems_balanced_forms_upto_aut O bar φ Y hY n N hN3 ebY
  have hP : ∀ μ' : (Fin n → ZMod N) → Y,
      ((∀ cl i, ((ebY (μ' cl) i : ℤ) : ZMod N) = cl i) ∧ ∃ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b₀ (μ' cl) (μ' cl) ≤ b₀ α α)) →
      ∃ (ι : ℕ) (L : Finset ((Fin n → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) →
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b' (μ' cl) (μ' cl) ≤ b' α α) →
        (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ' cl) (μ' cl)) ∧
          ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ' cl) (μ' cl) :=
    fun μ' ⟨h1, b₀, hb₀, h2, h3⟩ => single O bar φ Y hY n N hN3 hNo ebY μ' h1 b₀ hb₀ h2 h3
  choose! ιf Lf hιf hLf using hP
  set ι : ℕ := ∏ μ' ∈ S, max (ιf μ') 1 with hιdef
  refine ⟨ι, S.biUnion fun μ' => Finset.univ.image fun σ : Equiv.Perm (Fin n → ZMod N) =>
    (Lf μ').image fun ν c => ((ι / ιf μ' : ℕ) : ℤ) * ν (σ c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => by omega)
  intro X _ _ _ ebX f b hb hbp μ hμ hmin
  have hbY : pull f.symm.toLinearMap b ∈ balForms bar Y := pull_mem _ hb
  have hbYp : ∀ x, x ≠ 0 → 0 < pull f.symm.toLinearMap b x x := fun x hx => by
    simpa using hbp (f.symm x) (by simpa using hx)
  obtain ⟨e, he⟩ := hS _ hbY hbYp
  set g : Y ≃ₗ[O] X := e.trans f.symm with hg
  obtain ⟨σ, hσ1, hσ2⟩ := GlobalTheory.T.transport_classMinimisers_along_linearEquiv O Y X n N ebY ebX g μ hμ
  set μ' : (Fin n → ZMod N) → Y := fun c => g.symm (μ (σ c)) with hμ'
  have hpull : ∀ β : LinearMap.BilinForm ℤ X, pull e.toLinearMap (pull f.symm.toLinearMap β) = pull g.toLinearMap β :=
    fun β => LinearMap.ext₂ fun x y => rfl
  have hmem : μ' ∈ S := he μ' hσ1 (by rw [hpull]; exact hσ2 b hmin)
  have hgb : pull g.toLinearMap b ∈ balForms bar Y := pull_mem _ hb
  have hgp : ∀ x, x ≠ 0 → 0 < pull g.toLinearMap b x x := fun x hx => by
    simpa using hbp (g x) (by simpa using hx)
  have hPμ : (∀ cl i, ((ebY (μ' cl) i : ℤ) : ZMod N) = cl i) ∧ ∃ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b₀ (μ' cl) (μ' cl) ≤ b₀ α α) :=
    ⟨hσ1, _, hgb, hgp, hσ2 b hmin⟩
  have hι1 := hιf _ hPμ
  have hL := hLf _ hPμ
  have hdvd : ιf μ' ∣ ι := by
    have := Finset.dvd_prod_of_mem (fun μ'' => max (ιf μ'') 1) hmem
    simpa [max_eq_left hι1] using this
  set k : ℕ := ι / ιf μ' with hk
  have hkι : (ι : ℝ) = k * ιf μ' := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  refine ⟨(Lf μ').image fun ν c => ((k : ℕ) : ℤ) * ν (σ.symm c),
    Finset.mem_biUnion.2 ⟨μ', hmem, Finset.mem_image.2 ⟨σ.symm, Finset.mem_univ _, rfl⟩⟩, ?_⟩
  intro b' hb' hb'p hb'min
  have key := hL (pull g.toLinearMap b') (pull_mem _ hb') (fun x => hb'p _) (hσ2 b' hb'min)
  have hφ' : φ.evalZ (pull g.toLinearMap b') = φ.evalZ b' := evalZ_pull φ g.surjective b'
  have hq : ∀ c, pull g.toLinearMap b' (μ' c) (μ' c) = b' (μ (σ c)) (μ (σ c)) := fun c => by
    simp [μ']
  have hsum : ∀ ν : (Fin n → ZMod N) → ℤ,
      ∑ c, ((((k : ℕ) : ℤ) * ν (σ.symm c) : ℤ) : ℝ) * b' (μ c) (μ c) =
        k * ∑ c, (ν c : ℝ) * pull g.toLinearMap b' (μ' c) (μ' c) := fun ν => by
    rw [Finset.mul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hq]; simp; ring
  have hlhs : (ι : ℝ) * φ.evalZ b' = k * ((ιf μ' : ℝ) * φ.evalZ (pull g.toLinearMap b')) := by
    rw [hφ', hkι]; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
    rw [hsum, hlhs]
    exact mul_le_mul_of_nonneg_left (key.1 ν hν) hk0
  · obtain ⟨ν, hν, heq⟩ := key.2
    exact ⟨_, Finset.mem_image_of_mem _ hν, by rw [hsum, hlhs, heq]⟩

end GlobalTheory.UPoinc.FinTypes

theorem GlobalTheory.UPoinc.finite_types_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolFan H.bar q φ → ∀ (N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∃ (B ι : ℕ) (𝓛 : ∀ n : ℕ, Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (eb : X ≃ₗ[ℤ] (Fin n → ℤ)), n < B ∧ ∀ (b : LinearMap.BilinForm ℤ X), b ∈ balForms H.bar X → (∀ y, y ≠ 0 → 0 < b y y) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛 n, ∀ b' : LinearMap.BilinForm ℤ X, b' ∈ balForms H.bar X → (∀ y, 0 ≤ b' y y) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  intro E _ _ _ H q φ hφ N _ hN3 hNo
  classical
  obtain ⟨R, Y, hY⟩ := GlobalTheory.ProjModFinIso.finitely_many_iso_classes E q
  set B : ℕ := Module.finrank ℚ E * q + 1 with hB
  have hP : ∀ (n : ℕ) (k : Fin R), ∃ (ι : ℕ) (𝓛₀ : Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧
      ((Module.Finite (𝓞 E) (Y k) ∧ Module.Projective (𝓞 E) (Y k) ∧ Module.finrank (𝓞 E) (Y k) ≤ q ∧
        Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ))) →
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ))
        (f : X ≃ₗ[𝓞 E] Y k), ∀ b ∈ balForms H.bar X, (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin n → ZMod N) → X,
        (∀ cl i, ((ebX (μ cl) i : ℤ) : ZMod N) = cl i) →
        (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) →
        ∃ L ∈ 𝓛₀, ∀ b' ∈ balForms H.bar X, (∀ x, 0 ≤ b' x x) →
          (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) →
          (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧
            ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) := by
    intro n k
    by_cases hC : Module.Finite (𝓞 E) (Y k) ∧ Module.Projective (𝓞 E) (Y k) ∧ Module.finrank (𝓞 E) (Y k) ≤ q ∧
        Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ))
    · obtain ⟨h1, h2, h3, ⟨ebY⟩⟩ := hC
      obtain ⟨ι, 𝓛₀, hι, h⟩ := GlobalTheory.UPoinc.FinTypes.P1 (𝓞 E) H.bar φ (Y k) (hφ (Y k) h3) n N hN3 hNo ebY
      exact ⟨ι, 𝓛₀, hι, fun _ => h⟩
    · exact ⟨1, ∅, le_rfl, fun h => (hC h).elim⟩
  choose ιf 𝓛f hιf h𝓛f using hP
  set ι : ℕ := ∏ n ∈ Finset.range B, ∏ k, ιf n k with hιdef
  have hιpos : 0 < ι := Finset.prod_pos fun n _ => Finset.prod_pos fun k _ => hιf n k
  refine ⟨B, ι, fun n => Finset.univ.biUnion fun k =>
    (𝓛f n k).image fun L => L.image fun ν c => ((ι / ιf n k : ℕ) : ℤ) * ν c, hιpos, ?_⟩
  intro n X _ _ _ _ hXq eb
  obtain ⟨hfinZ, -, hrk⟩ := GlobalTheory.finite_projective_int_of_ringOfIntegers E X
  have hn : Module.finrank ℤ X = n := by rw [eb.finrank_eq, Module.finrank_fin_fun]
  have hnB : n < B := by
    rw [hB, ← hn, hrk]
    have := Nat.mul_le_mul_left (Module.finrank ℚ E) hXq
    omega
  refine ⟨hnB, ?_⟩
  intro b hb hbp μ hμ hmin
  obtain ⟨k, ⟨f⟩⟩ := hY X hXq
  haveI h1 : Module.Finite (𝓞 E) (Y k) := Module.Finite.equiv f
  haveI h2 : Module.Projective (𝓞 E) (Y k) := Module.Projective.of_equiv f
  have h3 : Module.finrank (𝓞 E) (Y k) ≤ q := f.finrank_eq ▸ hXq
  have h4 : Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ)) := ⟨f.symm.toAddEquiv.toIntLinearEquiv.trans eb⟩
  obtain ⟨L, hL, hLb⟩ := h𝓛f n k ⟨h1, h2, h3, h4⟩ X eb f b hb hbp μ hμ hmin
  have hdvd : ιf n k ∣ ι := by
    have h5 : ∏ k, ιf n k ∣ ι := Finset.dvd_prod_of_mem (fun n => ∏ k, ιf n k) (Finset.mem_range.2 hnB)
    exact (Finset.dvd_prod_of_mem (fun k => ιf n k) (Finset.mem_univ k)).trans h5
  set c : ℕ := ι / ιf n k with hc
  have hcι : (ι : ℝ) = c * ιf n k := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  refine ⟨L.image fun ν cl => ((c : ℕ) : ℤ) * ν cl,
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image.2 ⟨L, hL, rfl⟩⟩, ?_⟩
  intro b' hb' hb'p hb'min
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLb b' hb' hb'p hb'min
  have hsum : ∀ ν : (Fin n → ZMod N) → ℤ, ∑ cl, ((((c : ℕ) : ℤ) * ν cl : ℤ) : ℝ) * b' (μ cl) (μ cl) =
      c * ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := fun ν => by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun cl _ => ?_; push_cast; ring
  have hlhs : (ι : ℝ) * φ.evalZ b' = c * ((ιf n k : ℝ) * φ.evalZ b') := by rw [hcι]; ring
  refine ⟨fun ν' hν' => ?_, ⟨_, Finset.mem_image_of_mem _ hν₀, by rw [hsum, hlhs, heq]⟩⟩
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
  rw [hsum, hlhs]
  exact mul_le_mul_of_nonneg_left (hle ν hν) hc0
