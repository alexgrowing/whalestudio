import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

namespace GlobalTheory
namespace LagrFrame

variable {k : Type} [Field k] {κ : Type} [Fintype κ]

def form : ((κ → k) × (κ → k)) →ₗ[k] ((κ → k) × (κ → k)) →ₗ[k] k :=
  LinearMap.mk₂ k (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)
    (by intro a b c; simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (by intro c a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]; ring)
    (by intro a b c; simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (by intro c a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]; ring)

lemma form_apply (w w' : (κ → k) × (κ → k)) :
    form w w' = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := rfl

lemma form_self (w : (κ → k) × (κ → k)) : form w w = 0 := by
  rw [form_apply]; ring

lemma form_swap (w w' : (κ → k) × (κ → k)) : form w' w = - form w w' := by
  rw [form_apply, form_apply]; ring

lemma eq_zero_of_form (w : (κ → k) × (κ → k)) (h : ∀ v, form v w = 0) : w = 0 := by
  classical
  ext i
  · have := h (0, Pi.single i 1)
    rw [form_apply] at this
    simpa [dotProduct_single] using this
  · have := h (Pi.single i 1, 0)
    rw [form_apply] at this
    simpa [single_dotProduct] using this

def pairMap {m : ℕ} (g : Fin m → (κ → k) × (κ → k)) :
    ((κ → k) × (κ → k)) →ₗ[k] (Fin m → k) :=
  LinearMap.pi (fun j => (form (k := k) (κ := κ)).flip (g j))

lemma pairMap_apply {m : ℕ} (g : Fin m → (κ → k) × (κ → k)) (v) (j : Fin m) :
    pairMap g v j = form v (g j) := rfl

lemma pairMap_surjective {m : ℕ} (g : Fin m → (κ → k) × (κ → k)) (hg : LinearIndependent k g) :
    Function.Surjective (pairMap g) := by
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ hψ
  have key : ∑ j, ψ (fun j' => if j = j' then 1 else 0) • g j = 0 := by
    apply eq_zero_of_form
    intro v
    have h1 := LinearMap.congr_fun hψ v
    rw [LinearMap.dualMap_apply, LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ] at h1
    rw [map_sum]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans h1
    rw [map_smul, smul_eq_mul, smul_eq_mul, pairMap_apply, mul_comm]
  have hz := (Fintype.linearIndependent_iff.1 hg) _ key
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ ψ x]
  simp [hz]

lemma finrank_space : Module.finrank k ((κ → k) × (κ → k)) = Fintype.card κ + Fintype.card κ := by
  simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

lemma finrank_ker_pairMap {m : ℕ} (g : Fin m → (κ → k) × (κ → k)) (hg : LinearIndependent k g) :
    Module.finrank k (LinearMap.ker (pairMap g)) + m = Fintype.card κ + Fintype.card κ := by
  have h := LinearMap.finrank_range_add_finrank_ker (pairMap g)
  rw [LinearMap.range_eq_top.2 (pairMap_surjective g hg), finrank_top, Module.finrank_fin_fun,
    finrank_space] at h
  omega

def Iso {m : ℕ} (g : Fin m → (κ → k) × (κ → k)) : Prop := ∀ i j, form (g i) (g j) = 0

lemma span_le_ker {m : ℕ} (g : Fin m → (κ → k) × (κ → k)) (hi : Iso g) :
    Submodule.span k (Set.range g) ≤ LinearMap.ker (pairMap g) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  funext j
  exact hi i j

lemma le_card {m : ℕ} (g : Fin m → (κ → k) × (κ → k)) (hg : LinearIndependent k g) (hi : Iso g) :
    m ≤ Fintype.card κ := by
  have h1 := Submodule.finrank_mono (span_le_ker g hi)
  rw [finrank_span_eq_card hg, Fintype.card_fin] at h1
  have h2 := finrank_ker_pairMap g hg
  omega

lemma exists_extend_one {m : ℕ} (g : Fin m → (κ → k) × (κ → k)) (hg : LinearIndependent k g)
    (hi : Iso g) (hm : m < Fintype.card κ) :
    ∃ v, LinearIndependent k (Fin.snoc g v : Fin (m + 1) → _) ∧ Iso (Fin.snoc g v : Fin (m + 1) → _) := by
  have hnot : ¬ LinearMap.ker (pairMap g) ≤ Submodule.span k (Set.range g) := by
    intro hle
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hg, Fintype.card_fin] at h1
    have h2 := finrank_ker_pairMap g hg
    omega
  obtain ⟨v, hv, hvs⟩ := SetLike.not_le_iff_exists.1 hnot
  refine ⟨v, linearIndependent_finSnoc.2 ⟨hg, hvs⟩, ?_⟩
  rw [LinearMap.mem_ker] at hv
  have hvg : ∀ j, form v (g j) = 0 := fun j => by
    have := congr_fun hv j; rwa [pairMap_apply] at this
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [form_self]
    | cast j => simp [hvg]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [form_swap, hvg, neg_zero]
    | cast j => simp only [Fin.snoc_castSucc]; exact hi i j

lemma exists_extend (d : ℕ) : ∀ (m : ℕ) (g : Fin m → (κ → k) × (κ → k)),
    LinearIndependent k g → Iso g → ∀ hmd : m + d = Fintype.card κ,
    ∃ f : Fin (Fintype.card κ) → (κ → k) × (κ → k), LinearIndependent k f ∧ Iso f ∧
      ∀ i : Fin m, f ⟨i, by omega⟩ = g i := by
  induction d with
  | zero =>
    intro m g hg hi hm
    refine ⟨g ∘ Fin.cast (by omega), hg.comp _ (Fin.cast_injective _), fun i j => hi _ _,
      fun i => rfl⟩
  | succ d ih =>
    intro m g hg hi hm
    obtain ⟨v, hv1, hv2⟩ := exists_extend_one g hg hi (by omega)
    obtain ⟨f, hf1, hf2, hf3⟩ := ih (m + 1) _ hv1 hv2 (by omega)
    refine ⟨f, hf1, hf2, fun i => ?_⟩
    have := hf3 (Fin.castSucc i)
    simpa using this

end LagrFrame
end GlobalTheory

namespace GlobalTheory
namespace LagrFrame

variable {k : Type} [Field k] {κ : Type} [Fintype κ]

lemma exists_dual {n : ℕ} (f : Fin n → (κ → k) × (κ → k)) (hf : LinearIndependent k f)
    (hfi : Iso f) :
    ∃ e : Fin n → (κ → k) × (κ → k), (∀ i j, form (e i) (e j) = 0) ∧
      (∀ i j, form (e i) (f j) = if i = j then 1 else 0) := by
  classical
  have hs := pairMap_surjective f hf
  choose e0 he0 using fun i : Fin n => hs (fun j => if i = j then (1 : k) else 0)
  have h0 : ∀ i j, form (e0 i) (f j) = if i = j then 1 else 0 := fun i j => by
    rw [← pairMap_apply, he0 i]
  have hf' : ∀ a b, form (f a) (f b) = 0 := hfi
  obtain ⟨c, hc⟩ : ∃ c : Fin n → Fin n → k,
      c = fun i a => if i < a then form (e0 i) (e0 a) else 0 := ⟨_, rfl⟩
  have hA : ∀ i w, form (e0 i + ∑ a, c i a • f a) w = form (e0 i) w + ∑ a, c i a * form (f a) w :=
    fun i w => by simp [map_add, map_sum, map_smul, LinearMap.sum_apply]
  have hB : ∀ j w, form w (e0 j + ∑ b, c j b • f b) = form w (e0 j) + ∑ b, c j b * form w (f b) :=
    fun j w => by simp [map_add, map_sum, map_smul]
  refine ⟨fun i => e0 i + ∑ a, c i a • f a, ?_, ?_⟩
  · intro i j
    have h1 : ∀ a, form (f a) (e0 j) = - if j = a then 1 else 0 := fun a => by rw [form_swap, h0]
    rw [hA]
    simp only [hB, h0, h1, hf', mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      mul_neg, Finset.sum_ite_eq, Finset.sum_neg_distrib, Finset.mem_univ, if_true]
    subst hc
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt]
    · subst h; simp [form_self]
    · simp [h, h.not_gt, form_swap (e0 i) (e0 j)]
  · intro i j
    rw [hA]
    simp [h0, hf']

theorem exists_frame : ∀ {k : Type} [Field k] {κ : Type} [Fintype κ] (U : Submodule k ((κ → k) × (κ → k))),
    (∀ u ∈ U, ∀ u' ∈ U, u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 = 0) →
    ∃ (n : ℕ) (wT wM : (Fin n → k) →ₗ[k] (κ → k) × (κ → k)) (I : Finset (Fin n)),
      (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) ∧
      (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) ∧
      (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = Y ⬝ᵥ z) ∧
      (∀ w, ∃ Y z, wT Y + wM z = w) ∧
      (∀ u, u ∈ U ↔ ∃ z : Fin n → k, (∀ i ∉ I, z i = 0) ∧ wM z = u) := by
  intro k _ κ _ U hU
  classical
  let bU := Module.finBasis k U
  let g : Fin (Module.finrank k U) → (κ → k) × (κ → k) := fun i => (bU i : (κ → k) × (κ → k))
  have hg : LinearIndependent k g := bU.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hgi : Iso g := fun i j => hU _ (bU i).2 _ (bU j).2
  have hr : Module.finrank k U ≤ Fintype.card κ := le_card g hg hgi
  obtain ⟨f, hf, hfi, hfg⟩ := exists_extend (Fintype.card κ - Module.finrank k U) _ g hg hgi
    (by omega)
  obtain ⟨e, he, hef⟩ := exists_dual f hf hfi
  have hT : ∀ Y Y', form (Fintype.linearCombination k e Y) (Fintype.linearCombination k e Y') = 0 := by
    intro Y Y'
    simp [Fintype.linearCombination_apply, map_sum, map_smul, he]
  have hM : ∀ z z', form (Fintype.linearCombination k f z) (Fintype.linearCombination k f z') = 0 := by
    intro z z'
    have hf' : ∀ a b, form (f a) (f b) = 0 := hfi
    simp [Fintype.linearCombination_apply, map_sum, map_smul, hf']
  have hTM : ∀ Y z, form (Fintype.linearCombination k e Y) (Fintype.linearCombination k f z)
      = Y ⬝ᵥ z := by
    intro Y z
    simp [Fintype.linearCombination_apply, map_sum, map_smul, hef, dotProduct, mul_comm]
  refine ⟨Fintype.card κ, Fintype.linearCombination k e, Fintype.linearCombination k f,
    Finset.univ.filter (fun j : Fin (Fintype.card κ) => (j : ℕ) < Module.finrank k U),
    hT, hM, hTM, ?_, ?_⟩
  · have hinj : Function.Injective
        ((Fintype.linearCombination k e).coprod (Fintype.linearCombination k f)) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨Y, z⟩ h0
      rw [LinearMap.coprod_apply] at h0
      have hY : ∀ j, Y j = 0 := fun j => by
        have := congrArg (fun w => form w (Fintype.linearCombination k f (Pi.single j 1))) h0
        simpa only [map_add, LinearMap.add_apply, hTM, hM, map_zero, LinearMap.zero_apply,
          add_zero, dotProduct_single, mul_one] using this
      have hz : ∀ j, z j = 0 := fun j => by
        have := congrArg (fun w => form (Fintype.linearCombination k e (Pi.single j 1)) w) h0
        simpa only [map_add, hTM, hT, map_zero, zero_add, single_dotProduct, one_mul] using this
      ext j <;> simp [hY, hz]
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card])).1 hinj
    intro w
    obtain ⟨⟨Y, z⟩, h⟩ := hsurj w
    exact ⟨Y, z, h⟩
  · intro u
    constructor
    · intro hu
      let cc := bU.repr ⟨u, hu⟩
      refine ⟨fun j => if h : (j : ℕ) < Module.finrank k U then cc ⟨j, h⟩ else 0, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [hi]
      · have hsum : ∑ i, cc i • g i = u := by
          calc ∑ i, cc i • g i = ((∑ i, cc i • bU i : U) : (κ → k) × (κ → k)) := by
                simp only [Submodule.coe_sum, Submodule.coe_smul, g]
            _ = u := by rw [bU.sum_repr]
        rw [Fintype.linearCombination_apply, ← hsum]
        symm
        refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_
        · intro b hb
          have : ¬ (b : ℕ) < Module.finrank k U := by
            intro hlt; exact hb ⟨⟨b, hlt⟩, rfl⟩
          simp [this]
        · intro a
          have := hfg a
          simp only [Fin.val_castLE, Fin.is_lt, dite_true]
          congr 1
          exact this.symm
    · rintro ⟨z, hz, rfl⟩
      rw [Fintype.linearCombination_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases h : (j : ℕ) < Module.finrank k U
      · have := hfg ⟨j, h⟩
        simp only [Fin.eta] at this
        rw [this]
        exact U.smul_mem _ (bU _).2
      · rw [hz j (by simp [h]), zero_smul]
        exact U.zero_mem

end LagrFrame
end GlobalTheory
