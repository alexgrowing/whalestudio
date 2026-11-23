import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBCBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import GroundTheory.GlobalFields.CompletionAtPlace.Degree
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitPrime

variable {K : Type} [Field K] [NumberField K]
open GlobalTheory.CompanionTheory.SphTheta

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unr_mul {a b : Fˣ →* ℂˣ} (ha : IsUnramifiedChar a) (hb : IsUnramifiedChar b) :
    IsUnramifiedChar (a * b) := fun u hu => by
  have h1 : a u = 1 := MonoidHom.mem_ker.mp (ha hu)
  have h2 : b u = 1 := MonoidHom.mem_ker.mp (hb hu)
  exact MonoidHom.mem_ker.mpr (by simp [h1, h2])

theorem unr_inv {a : Fˣ →* ℂˣ} (ha : IsUnramifiedChar a) : IsUnramifiedChar a⁻¹ := fun u hu => by
  have h1 : a u = 1 := MonoidHom.mem_ker.mp (ha hu)
  exact MonoidHom.mem_ker.mpr (by simp [h1])

end Local

theorem places_of_two (h2 : Module.finrank ℚ K = 2) (v : Pl) (w₁ w₂ : PlK K)
    [h₁ : w₁.asIdeal.LiesOver v.asIdeal] [h₂ : w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) :
    (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → w = w₁ ∨ w = w₂) ∧
    ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal →
      w.asIdeal.ramificationIdx (𝓞 ℚ) * w.asIdeal.inertiaDeg (𝓞 ℚ) = 1 := by
  classical
  have hs := SemiLocal.sum_ramificationIdx_mul_inertiaDeg K v
  rw [h2] at hs
  set G : SemiLocal.PlacesOver K v → ℕ :=
    fun x => x.1.asIdeal.ramificationIdx (𝓞 ℚ) * x.1.asIdeal.inertiaDeg (𝓞 ℚ) with hG
  have hpos : ∀ x, 1 ≤ G x := fun x => by
    have h := finrank_adicCompletion v x.1
    have h3 : 0 < Module.finrank (v.adicCompletion ℚ) (x.1.adicCompletion K) := Module.finrank_pos
    rw [h] at h3
    exact h3
  set a : SemiLocal.PlacesOver K v := ⟨w₁, h₁⟩ with ha
  set b : SemiLocal.PlacesOver K v := ⟨w₂, h₂⟩ with hb
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  have hsum : ∑ x ∈ Finset.univ \ {a, b}, G x + (G a + G b) = 2 := by
    rw [← Finset.sum_pair hab, Finset.sum_sdiff (Finset.subset_univ _)]
    exact hs
  have ha1 := hpos a
  have hb1 := hpos b
  have hmem : ∀ x : SemiLocal.PlacesOver K v, x = a ∨ x = b := fun x => by
    by_contra hx
    have hx' : x ∈ Finset.univ \ ({a, b} : Finset (SemiLocal.PlacesOver K v)) := by
      simpa using hx
    have h4 := Finset.single_le_sum (f := G) (fun _ _ => Nat.zero_le _) hx'
    have h5 := hpos x
    omega
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rcases hmem ⟨w, hw⟩ with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · have h6 : G a = 1 := by omega
    have h7 : G b = 1 := by omega
    rcases hmem ⟨w, hw⟩ with h | h
    · have : G ⟨w, hw⟩ = 1 := h ▸ h6
      exact this
    · have : G ⟨w, hw⟩ = 1 := h ▸ h7
      exact this

section Place

variable (v : Pl) (w : PlK K) [hw : w.asIdeal.LiesOver v.asIdeal]

abbrev iota : (Qv v)ˣ →* (Kv K w)ˣ := Units.map (algebraMap (Qv v) (Kv K w)).toMonoidHom

theorem nrm_iota (hd : Module.finrank (Qv v) (Kv K w) = 1) (a : (Qv v)ˣ) :
    nrm v w (iota v w a) = a := by
  apply Units.ext
  show Algebra.norm (Qv v) (algebraMap (Qv v) (Kv K w) (a : Qv v)) = a
  rw [Algebra.norm_algebraMap, hd, pow_one]

theorem ord_iota (he : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) :
    ord ((iota v w (unifUnit (Qv v)) : (Kv K w)ˣ) : Kv K w) = 1 := by
  have hx : algebraMap (Qv v) (Kv K w) (unifUnit (Qv v) : Qv v) ≠ 0 := by simp
  have h1 := valued_algebraMap_adicCompletion v w (unifUnit (Qv v) : Qv v)
  rw [he, pow_one, valued_eq_exp_neg_ord hx, valued_eq_exp_neg_ord (Units.ne_zero _),
    ord_unifUnit] at h1
  exact neg_injective (WithZero.exp_injective h1)

theorem residueCard_eq (hf : w.asIdeal.inertiaDeg (𝓞 ℚ) = 1) :
    residueCard (Kv K w) = residueCard (Qv v) := by
  rw [residueCard_adicCompletion, residueCard_adicCompletion,
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg, hf, pow_one]

theorem localLFactor_place (he : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 ℚ) = 1) {μ : (Kv K w)ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ) (s : ℂ) :
    localLFactor μ s =
      (1 - ((μ (iota v w (unifUnit (Qv v))) : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactor_of_isUnramified hμ, quasiChar_apply_eq_of_isUnramified hμ (ord_iota v w he),
    residueCard_eq v w hf]

theorem local_L_factor_split_place (D : Dat) (DK : DatK K) (hBC : IsBC D DK) (hv : v ∉ D.bad)
    (hd : Module.finrank (Qv v) (Kv K w) = 1) (he : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 ℚ) = 1) {C : (Kv K w)ˣ →* ℂˣ} (hC : IsUnramifiedChar C) (s : ℂ) :
    lf3 (DK.ν w) C s = ∏ i : Fin 3,
      (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) *
        ((C (iota v w (unifUnit (Qv v))) : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  have hν : IsUnramifiedChar (DK.ν w) := by
    rw [hBC.nu v w]
    exact GlobalTheory.CompanionTheory.BaseChangeData.isUnramifiedChar_comp_nrm v w (D.unr v hv)
  have hval : DK.ν w (iota v w (unifUnit (Qv v))) = D.ν v (unifUnit (Qv v)) := by
    rw [hBC.nu v w, MonoidHom.comp_apply, nrm_iota v w hd]
  unfold lf3
  rw [localLFactor_place v w he hf (unr_mul hν hC), localLFactor_place v w he hf hC,
    localLFactor_place v w he hf (unr_mul (unr_inv hν) hC), Fin.prod_univ_three]
  simp [MonoidHom.mul_apply, MonoidHom.inv_apply, hval]

theorem isUnit1_cAt (c : HeckeCharacter K) : IsUnit1 (cAt c v w) := by
  refine ⟨(GodementSection.continuous_localChar c w).comp
    (Continuous.units_map _ (_root_.continuous_algebraMap (Qv v) (Kv K w))), fun x => ?_⟩
  show ‖((localChar c w _ : ℂˣ) : ℂ)‖ = 1
  rw [GodementSection.coe_localChar]
  exact Circle.norm_coe _

end Place

theorem localChar_inv (c : HeckeCharacter K) (w : PlK K) :
    localChar c⁻¹ w = (localChar c w)⁻¹ := by
  have h1 := GodementSection.localChar_mul_inv (1 : HeckeCharacter K) c w
  have h2 := GodementSection.localChar_mul_inv c c w
  rw [mul_inv_cancel, mul_inv_cancel] at h2
  rw [one_mul, h2, one_mul] at h1
  exact h1

theorem finprod_places (v : Pl) (w₁ w₂ : PlK K) (h₁ : w₁.asIdeal.LiesOver v.asIdeal)
    (h₂ : w₂.asIdeal.LiesOver v.asIdeal) (hne : w₁ ≠ w₂)
    (hall : ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → w = w₁ ∨ w = w₂)
    (f : {w : PlK K // w.asIdeal.LiesOver v.asIdeal} → ℂ) :
    ∏ᶠ w, f w = f ⟨w₁, h₁⟩ * f ⟨w₂, h₂⟩ := by
  classical
  have hab : (⟨w₁, h₁⟩ : {w : PlK K // w.asIdeal.LiesOver v.asIdeal}) ≠ ⟨w₂, h₂⟩ :=
    fun h => hne (congrArg Subtype.val h)
  rw [finprod_eq_prod_of_mulSupport_subset f (s := {⟨w₁, h₁⟩, ⟨w₂, h₂⟩}),
    Finset.prod_pair hab]
  intro x _
  rcases hall x.1 x.2 with h | h
  · exact Finset.mem_coe.2 (Finset.mem_insert.2 (Or.inl (Subtype.ext h)))
  · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_singleton.2 (Subtype.ext h)))

theorem split_lfV : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (D : Dat) (DK : DatK K), IsBC D DK → ∀ (c : HeckeCharacter K) (v : Pl), v ∉ D.bad → (∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (localChar c w) ∧ w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) → ∀ (w₁ w₂ : PlK K) [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal], w₁ ≠ w₂ → IsUnit1 (cAt c v w₁) ∧ IsUnit1 (cAt c v w₂) ∧ IsUnramifiedChar (cAt c v w₁) ∧ IsUnramifiedChar (cAt c v w₂) ∧ ∀ s : ℂ, lfV DK c v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((![cAt c v w₁ (unifUnit (Qv v)), cAt c v w₂ (unifUnit (Qv v))] : Fin 2 → ℂˣ) j : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ ∧ lfV DK c⁻¹ v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * ((((![cAt c v w₁ (unifUnit (Qv v)), cAt c v w₂ (unifUnit (Qv v))] : Fin 2 → ℂˣ) j)⁻¹ : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  intro K _ _ h2 D DK hBC c v hv hc w₁ w₂ h₁ h₂ hne
  obtain ⟨hall, hef⟩ := places_of_two h2 v w₁ w₂ hne
  have he : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], w.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    fun w _ => (hc w).2
  have hf : ∀ (w : PlK K) [hw : w.asIdeal.LiesOver v.asIdeal], w.asIdeal.inertiaDeg (𝓞 ℚ) = 1 :=
    fun w hw => Nat.eq_one_of_mul_eq_one_left (hef w hw)
  have hd : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], Module.finrank (Qv v) (Kv K w) = 1 :=
    fun w _ => by rw [finrank_adicCompletion v w, he w, hf w, one_mul]
  have hcu : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (cAt c v w) :=
    fun w _ => GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w) _ (hc w).1
  refine ⟨isUnit1_cAt v w₁ c, isUnit1_cAt v w₂ c, hcu w₁, hcu w₂, fun s => ⟨?_, ?_⟩⟩
  · unfold lfV
    rw [finprod_places v w₁ w₂ h₁ h₂ hne hall]
    simp only [Fin.prod_univ_two, Finset.prod_mul_distrib]
    rw [local_L_factor_split_place v w₁ D DK hBC hv (hd w₁) (he w₁) (hf w₁) (hc w₁).1,
      local_L_factor_split_place v w₂ D DK hBC hv (hd w₂) (he w₂) (hf w₂) (hc w₂).1]
    rfl
  · unfold lfV
    rw [finprod_places v w₁ w₂ h₁ h₂ hne hall]
    simp only [Fin.prod_univ_two, Finset.prod_mul_distrib, localChar_inv]
    rw [local_L_factor_split_place v w₁ D DK hBC hv (hd w₁) (he w₁) (hf w₁) (unr_inv (hc w₁).1),
      local_L_factor_split_place v w₂ D DK hBC hv (hd w₂) (he w₂) (hf w₂) (unr_inv (hc w₂).1)]
    rfl

end GlobalTheory.CompanionTheory.SplitPrime
