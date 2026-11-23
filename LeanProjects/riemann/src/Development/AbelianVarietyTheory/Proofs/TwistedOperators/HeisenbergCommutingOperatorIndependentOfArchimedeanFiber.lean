import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FinFibre

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def fin (x : κ → AF F) : κ → Af F := fun i => (x i).2

def mkv (a : κ → Ainf F) (w : κ → Af F) : κ → AF F := fun i => (a i, w i)

def chi (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (w : κ → Af F) : ℂ := GlobalTheory.HeisSchA.finChar ψ (w ⬝ᵥ q)

variable (κ) in

def alg (ψ : AddChar (AF F) ℂ) : Submodule ℂ ((κ → Af F) → ℂ) := Submodule.span ℂ (Set.range (chi (κ := κ) ψ))

theorem chi_zero (ψ : AddChar (AF F) ℂ) : chi (κ := κ) ψ 0 = 1 := by
  funext w; simp [chi]

theorem chi_add (ψ : AddChar (AF F) ℂ) (q q' : κ → Af F) : chi (κ := κ) ψ (q + q') = chi ψ q * chi ψ q' := by
  funext w; simp [chi, dotProduct_add, AddChar.map_add_eq_mul]

theorem one_mem (ψ : AddChar (AF F) ℂ) : (1 : (κ → Af F) → ℂ) ∈ alg κ ψ :=
  chi_zero (κ := κ) ψ ▸ Submodule.subset_span ⟨0, rfl⟩

theorem mul_mem (ψ : AddChar (AF F) ℂ) {C D : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) (hD : D ∈ alg κ ψ) :
    C * D ∈ alg κ ψ := by
  have h := Submodule.mul_mem_mul hC hD
  rw [alg, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨q, rfl⟩, _, ⟨q', rfl⟩, rfl⟩
  exact ⟨q + q', chi_add ψ q q'⟩

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {a : Af F}
    (ha : a ≠ 0) : ∃ b : Af F, GlobalTheory.HeisSchA.finChar ψ (a * b) ≠ 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, evalV F v a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (af_ext fun u => by rw [h u, map_zero])
  obtain ⟨t, ht⟩ := hψ v
  refine ⟨singleFin v (t / evalV F v a), ?_⟩
  have e : a * singleFin v (t / evalV F v a) = singleFin v t := by
    apply af_ext
    intro u
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [evalV_singleFin_self, evalV_singleFin_self]
      field_simp
    · rw [evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  rw [e]
  exact ht

theorem exists_chi_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {d : κ → Af F}
    (hd : d ≠ 0) : ∃ q : κ → Af F, chi ψ q d ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
  obtain ⟨b, hb⟩ := exists_ne_one ψ hψ hi
  exact ⟨Pi.single i b, by rw [chi, dotProduct_single]; exact hb⟩

theorem chi_mul_eq_schr (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (Φ : (κ → AF F) → ℂ) :
    (fun x => chi ψ q (fin x) * Φ x) =
      schr ψ ((GlobalTheory.HeisSchA.mk 0 1 : AF F) • (0 : κ → AF F),
        (GlobalTheory.HeisSchA.mk 0 1 : AF F) • fun i => GlobalTheory.HeisSchA.mk 0 (q i)) Φ := by
  funext x
  simp only [schr, smul_zero, zero_dotProduct, mul_zero, add_zero]
  congr 1
  rw [chi, GlobalTheory.HeisSchA.finChar_apply]
  congr 1
  symm
  refine Prod.ext ?_ ?_
  · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ _) = 0
    rw [RingHom.map_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    change GlobalTheory.HeisSchA.p1 (x i) * (0 * 0) = 0
    simp
  · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ _) = _
    rw [RingHom.map_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (x i).2 * (1 * q i) = (x i).2 * q i
    rw [one_mul]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem comm_alg (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    {C : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    T (fun x => C (fin x) * Φ x) = fun x => C (fin x) * T Φ x := by
  induction hC using Submodule.span_induction with
  | mem C h =>
    obtain ⟨q, rfl⟩ := h
    have h0 : evI F (GlobalTheory.HeisSchA.mk 0 1 : AF F) = 0 := by
      change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    rw [chi_mul_eq_schr, chi_mul_eq_schr]
    exact hT _ h0 _ _ Φ hΦ
  | zero =>
    have e : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * T Φ x) = 0 := by funext x; simp
    have e' : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * Φ x) = 0 := by funext x; simp
    rw [e, e', map_zero]
  | add C D _ _ hC hD =>
    have e : (fun x : κ → AF F => (C + D) (fin x) * Φ x) =
        (fun x => C (fin x) * Φ x) + fun x => D (fin x) * Φ x := by funext x; simp [add_mul]
    rw [e, map_add, hC, hD]
    funext x; simp [add_mul]
  | smul a C _ hC =>
    have e : (fun x : κ → AF F => (a • C) (fin x) * Φ x) = a • fun x => C (fin x) * Φ x := by
      funext x; simp [mul_assoc]
    rw [e, map_smul, hC]
    funext x; simp [mul_assoc]

theorem exists_sep (ψ : AddChar (AF F) ℂ) (hc : Continuous ψ)
    (hψ : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) (y₀ : κ → Af F) {S : Set (κ → Af F)} (hS : IsCompact S)
    (hy : y₀ ∉ S) : ∃ C ∈ alg κ ψ, C y₀ = 1 ∧ ∀ w ∈ S, C w = 0 := by
  have hlc := GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hc
  refine hS.induction_on (p := fun t => ∃ C ∈ alg κ ψ, C y₀ = 1 ∧ ∀ w ∈ t, C w = 0) ?_ ?_ ?_ ?_
  · exact ⟨1, one_mem ψ, rfl, fun _ h => h.elim⟩
  · rintro s t hst ⟨C, hC, h1, h0⟩
    exact ⟨C, hC, h1, fun w hw => h0 w (hst hw)⟩
  · rintro s t ⟨C, hC, h1, h0⟩ ⟨D, hD, h1', h0'⟩
    refine ⟨C * D, mul_mem ψ hC hD, by simp [h1, h1'], ?_⟩
    rintro w (hw | hw)
    · simp [h0 w hw]
    · simp [h0' w hw]
  · intro w hw
    have hne : w - y₀ ≠ 0 := sub_ne_zero.mpr fun h => hy (h ▸ hw)
    obtain ⟨q, hq⟩ := exists_chi_ne_one ψ hψ hne
    set ζ := chi ψ q (w - y₀)
    have hζ : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    let C : (κ → Af F) → ℂ := (1 - ζ)⁻¹ • (GlobalTheory.HeisSchA.finChar ψ (-(y₀ ⬝ᵥ q)) • chi ψ q - ζ • chi ψ 0)
    have hCv : ∀ w', C w' = (1 - ζ)⁻¹ * (chi ψ q (w' - y₀) - ζ) := by
      intro w'
      simp only [C, chi_zero, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
      congr 2
      rw [chi, chi, sub_dotProduct, sub_eq_neg_add, AddChar.map_add_eq_mul]
    have hCm : C ∈ alg κ ψ := Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)))
    have hcont : Continuous fun w' : κ → Af F => (w' - y₀) ⬝ᵥ q :=
      (continuous_id.sub continuous_const).dotProduct continuous_const
    have hev := (IsLocallyConstant.iff_eventually_eq _).mp (hlc.comp_continuous hcont) w
    refine ⟨{w' | chi ψ q (w' - y₀) = ζ}, mem_nhdsWithin_of_mem_nhds hev, C, hCm, ?_, ?_⟩
    · rw [hCv, sub_self]
      have h1 : chi ψ q 0 = 1 := by simp [chi]
      rw [h1]
      exact inv_mul_cancel₀ hζ
    · intro w' hw'
      rw [hCv, show chi ψ q (w' - y₀) = ζ from hw', sub_self, mul_zero]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_struct {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∃ K : Set (κ → Af F), IsCompact K ∧ ∀ x, fin x ∉ K → Φ x = 0) ∧
      ∀ w₀ : κ → Af F, ∀ᶠ w in nhds w₀, ∀ a : κ → Ainf F, Φ (mkv a w) = Φ (mkv a w₀) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨⟨tsupport g, hg.2, fun x hx => ?_⟩, fun w₀ => ?_⟩
    · change _ * g (fin x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    · filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp hg.1 w₀] with w hw a
      change _ * g w = _ * g w₀
      rw [hw]
      rfl
  | zero => exact ⟨⟨∅, isCompact_empty, fun _ _ => rfl⟩, fun _ => Filter.Eventually.of_forall fun _ _ => rfl⟩
  | add Φ Ψ _ _ hΦ hΨ =>
    obtain ⟨⟨K, hK, h0⟩, h1⟩ := hΦ
    obtain ⟨⟨K', hK', h0'⟩, h1'⟩ := hΨ
    refine ⟨⟨K ∪ K', hK.union hK', fun x hx => ?_⟩, fun w₀ => ?_⟩
    · simp only [Set.mem_union, not_or] at hx
      simp [h0 x hx.1, h0' x hx.2]
    · filter_upwards [h1 w₀, h1' w₀] with w hw hw' a
      simp [hw a, hw' a]
  | smul c Φ _ hΦ =>
    obtain ⟨⟨K, hK, h0⟩, h1⟩ := hΦ
    refine ⟨⟨K, hK, fun x hx => by simp [h0 x hx]⟩, fun w₀ => ?_⟩
    filter_upwards [h1 w₀] with w hw a
    simp [hw a]

theorem main (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (hψ : IsStd ψ)
    (hnd : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1)
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (y : κ → AF F) (hy : ∀ z, At (evI F) z → Φ (y + z) = 0) :
    T Φ y = 0 := by
  obtain ⟨⟨K, hK, h0⟩, h1⟩ := schA_struct hΦ
  set U := {w : κ → Af F | ∀ a : κ → Ainf F, Φ (mkv a w) = Φ (mkv a (fin y))}
  have hU : U ∈ nhds (fin y) := h1 (fin y)
  obtain ⟨C, hC, hC1, hC0⟩ := exists_sep ψ hψ.1 hnd (fin y) (hK.diff isOpen_interior)
    (fun h => h.2 (mem_interior_iff_mem_nhds.mpr hU))
  have hzero : (fun x => C (fin x) * Φ x) = 0 := by
    funext x
    by_cases hxK : fin x ∈ K
    · by_cases hxU : fin x ∈ interior U
      · have hx := interior_subset hxU (fun i => (x i).1)
        have e1 : mkv (fun i => (x i).1) (fin x) = x := rfl
        rw [e1] at hx
        have e2 : mkv (fun i => (x i).1) (fin y) = y + fun i => GlobalTheory.HeisSchA.mk ((x i).1 - (y i).1) 0 := by
          funext i
          refine Prod.ext ?_ ?_
          · change (x i).1 = (y i).1 + ((x i).1 - (y i).1)
            abel
          · change (y i).2 = (y i).2 + 0
            rw [add_zero]
        rw [hx, e2, hy _ (fun u hu => funext fun i => GlobalTheory.HeisSchA.at_mk _ u hu)]
        simp
      · simp [hC0 _ ⟨hxK, hxU⟩]
    · simp [h0 x hxK]
  have h := congrFun (comm_alg ψ T hT hC hΦ) y
  rw [hzero, map_zero, hC1, one_mul] at h
  exact h.symm

end GlobalTheory.FinFibre

open GlobalTheory.FinFibre in

theorem GlobalTheory.FinFibre.fibre_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ, T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 :=
  fun ψ T hψ _ hT Φ hΦ y hy => main ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hT Φ hΦ y hy
