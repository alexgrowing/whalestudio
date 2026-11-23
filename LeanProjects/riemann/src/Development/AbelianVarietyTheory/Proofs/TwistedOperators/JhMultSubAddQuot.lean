import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.JHMult

variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem exists_factor (g : V →ₗ[F] V₁) (h : V →ₗ[F] W) (hk : ∀ v, g v = 0 → h v = 0) :
    ∃ k : V₁ →ₗ[F] W, ∀ v, k (g v) = h v := by
  obtain ⟨k, hk'⟩ := LinearMap.exists_extend
    ((LinearMap.ker g).liftQ h hk ∘ₗ g.quotKerEquivRange.symm.toLinearMap)
  refine ⟨k, fun v => ?_⟩
  have := congr($hk' (g.quotKerEquivRange (Submodule.Quotient.mk v)))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
  exact this

def subMap {ρ : Representation F G V} {ρ₁ : Representation F G V₁} (p : ρ.IntertwiningMap ρ₁)
    (S : Subrepresentation ρ) : Subrepresentation ρ₁ :=
  ⟨S.toSubmodule.map p.toLinearMap, by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, p.isIntertwining _ _ g v⟩⟩

def subComap {ρ : Representation F G V} {ρ₁ : Representation F G V₁} (p : ρ.IntertwiningMap ρ₁)
    (S : Subrepresentation ρ₁) : Subrepresentation ρ :=
  ⟨S.toSubmodule.comap p.toLinearMap, fun g v hv => by
    show p (ρ g v) ∈ S.toSubmodule
    rw [p.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩

theorem subMap_mono {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    (p : ρ.IntertwiningMap ρ₁) {S T : Subrepresentation ρ} (h : S ≤ T) : subMap p S ≤ subMap p T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem subComap_mono {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    (p : ρ.IntertwiningMap ρ₁) {S T : Subrepresentation ρ₁} (h : S ≤ T) :
    subComap p S ≤ subComap p T := fun _ hv => h hv

def Step (σ : Representation F G W) {ρ : Representation F G V} (S T : Subrepresentation ρ) : Prop :=
  ∃ f : V →ₗ[F] W, (∀ w, ∃ v ∈ S.toSubmodule, f v = w) ∧
    (∀ g, ∀ v ∈ S.toSubmodule, f (ρ g v) = σ g (f v)) ∧
    ∀ v ∈ S.toSubmodule, (f v = 0 ↔ v ∈ T.toSubmodule)

theorem step_iff {σ : Representation F G W} {ρ : Representation F G V} {S T : Subrepresentation ρ} :
    Nonempty ((subQuot S T).Equiv σ) ↔ Step σ S T := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨f, hf⟩ := LinearMap.exists_extend (e.toLinearEquiv.toLinearMap ∘ₗ Submodule.mkQ _)
    have hf' : ∀ v (hv : v ∈ S.toSubmodule), f v = e.toLinearEquiv (Submodule.Quotient.mk ⟨v, hv⟩) :=
      fun v hv => congr($hf ⟨v, hv⟩)
    refine ⟨f, fun w => ?_, fun g v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective w
      obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨v, hv, hf' v hv⟩
    · rw [hf' v hv, hf' _ (S.apply_mem_toSubmodule g hv)]
      exact e.toIntertwiningMap.isIntertwining _ _ g (Submodule.Quotient.mk ⟨v, hv⟩)
    · rw [hf' v hv, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
      rfl
  · rintro ⟨f, h1, h2, h3⟩
    have hs : Function.Surjective (f ∘ₗ S.toSubmodule.subtype) := fun w => by
      obtain ⟨v, hv, rfl⟩ := h1 w
      exact ⟨⟨v, hv⟩, rfl⟩
    have hk : T.toSubmodule.comap S.toSubmodule.subtype =
        LinearMap.ker (f ∘ₗ S.toSubmodule.subtype) := by
      ext v
      exact (h3 v.1 v.2).symm
    refine ⟨.mk ((Submodule.quotEquivOfEq _ _ hk).trans
      (LinearMap.quotKerEquivOfSurjective _ hs)) fun g => ?_⟩
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    exact h2 g v.1 v.2

theorem occurs_of_finset {σ : Representation F G W} {ρ : Representation F G V} {r : ℕ}
    (A : Finset (Fin r)) (S T : Fin r → Subrepresentation ρ) (h1 : ∀ i, T i ≤ S i)
    (h2 : ∀ i j, i < j → S i ≤ T j) (h3 : ∀ i ∈ A, Step σ (S i) (T i)) :
    OccursTimes σ ρ A.card :=
  ⟨fun i => S (A.orderEmbOfFin rfl i), fun i => T (A.orderEmbOfFin rfl i), fun _ => h1 _,
    fun _ _ h => h2 _ _ ((A.orderEmbOfFin rfl).strictMono h),
    fun _ => step_iff.2 (h3 _ (A.orderEmbOfFin_mem rfl _))⟩

theorem occurs_zero (σ : Representation F G W) (ρ : Representation F G V) : OccursTimes σ ρ 0 :=
  ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

section Exact

variable {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
  {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)

theorem step_dichotomy (hσ : σ.IsIrreducible) (hker : ∀ v, p v = 0 → ∃ u, ι u = v)
    {S T : Subrepresentation ρ} (hTS : T ≤ S) (h : Step σ S T) :
    Step σ (subComap ι S) (subComap ι T) ∨ Step σ (subMap p S) (subMap p T) := by
  obtain ⟨f, h1, h2, h3⟩ := h
  let R : Subrepresentation σ := ⟨(subComap ι S).toSubmodule.map (f ∘ₗ ι.toLinearMap), by
    rintro g _ ⟨u, hu, rfl⟩
    refine ⟨ρ₁ g u, (subComap ι S).apply_mem_toSubmodule g hu, ?_⟩
    show f (ι (ρ₁ g u)) = σ g (f (ι u))
    rw [ι.isIntertwining, h2 g (ι u) hu]⟩
  rcases eq_bot_or_eq_top R with hR | hR
  · right
    obtain ⟨k, hk⟩ := exists_factor (p.toLinearMap ∘ₗ S.toSubmodule.subtype)
      (f ∘ₗ S.toSubmodule.subtype) (by
        rintro ⟨v, hv⟩ h0
        obtain ⟨u, rfl⟩ := hker v h0
        have : f (ι u) ∈ R.toSubmodule := ⟨u, hv, rfl⟩
        rw [hR] at this
        exact this)
    have hk' : ∀ v ∈ S.toSubmodule, k (p v) = f v := fun v hv => hk ⟨v, hv⟩
    refine ⟨k, fun w => ?_, ?_, ?_⟩
    · obtain ⟨v, hv, rfl⟩ := h1 w
      exact ⟨p v, ⟨v, hv, rfl⟩, hk' v hv⟩
    · rintro g _ ⟨v, hv, rfl⟩
      show k (ρ₂ g (p v)) = σ g (k (p v))
      rw [← p.isIntertwining, hk' v hv, hk' _ (S.apply_mem_toSubmodule g hv), h2 g v hv]
    · rintro _ ⟨v, hv, rfl⟩
      constructor
      · intro h0
        exact ⟨v, (h3 v hv).1 ((hk' v hv).symm.trans h0), rfl⟩
      · rintro ⟨t, ht, h0⟩
        rw [← h0]
        exact (hk' t (hTS ht)).trans ((h3 t (hTS ht)).2 ht)
  · left
    refine ⟨f ∘ₗ ι.toLinearMap, fun w => ?_, fun g u hu => ?_, fun u hu => h3 _ hu⟩
    · have : w ∈ R.toSubmodule := by rw [hR]; trivial
      exact this
    · show f (ι (ρ₁ g u)) = σ g (f (ι u))
      rw [ι.isIntertwining, h2 g (ι u) hu]

theorem step_map (hι : Function.Injective ι) {S T : Subrepresentation ρ₁} (h : Step σ S T) :
    Step σ (subMap ι S) (subMap ι T) := by
  obtain ⟨f, h1, h2, h3⟩ := h
  obtain ⟨k, hk⟩ := exists_factor ι.toLinearMap f (fun v hv => by
    have : v = 0 := hι (hv.trans (map_zero ι).symm)
    rw [this, map_zero])
  have hk' : ∀ v, k (ι v) = f v := hk
  refine ⟨k, fun w => ?_, ?_, ?_⟩
  · obtain ⟨v, hv, rfl⟩ := h1 w
    exact ⟨ι v, ⟨v, hv, rfl⟩, hk v⟩
  · rintro g _ ⟨v, hv, rfl⟩
    show k (ρ g (ι v)) = σ g (k (ι v))
    rw [← ι.isIntertwining, hk', hk', h2 g v hv]
  · rintro _ ⟨v, hv, rfl⟩
    rw [hk, h3 v hv]
    constructor
    · exact fun h => ⟨v, h, rfl⟩
    · rintro ⟨t, ht, h0⟩
      exact (hι h0 : t = v) ▸ ht

theorem step_comap (hp : Function.Surjective p) {S T : Subrepresentation ρ₂} (h : Step σ S T) :
    Step σ (subComap p S) (subComap p T) := by
  obtain ⟨f, h1, h2, h3⟩ := h
  refine ⟨f ∘ₗ p.toLinearMap, fun w => ?_, fun g u hu => ?_, fun u hu => h3 _ hu⟩
  · obtain ⟨v, hv, rfl⟩ := h1 w
    obtain ⟨u, rfl⟩ := hp v
    exact ⟨u, hv, rfl⟩
  · show f (p (ρ g u)) = σ g (f (p u))
    rw [p.isIntertwining, h2 g (p u) hu]

theorem occurs_add (hι : Function.Injective ι) (hp : Function.Surjective p)
    (h0 : ∀ u, p (ι u) = 0) {a b : ℕ} (ha : OccursTimes σ ρ₁ a) (hb : OccursTimes σ ρ₂ b) :
    OccursTimes σ ρ (a + b) := by
  obtain ⟨S, T, h1, h2, h3⟩ := ha
  obtain ⟨S', T', h1', h2', h3'⟩ := hb
  refine ⟨Fin.append (fun i => subMap ι (S i)) (fun i => subComap p (S' i)),
    Fin.append (fun i => subMap ι (T i)) (fun i => subComap p (T' i)), fun i => ?_,
    fun i j => ?_, fun i => step_iff.2 ?_⟩
  · induction i using Fin.addCases with
    | left i => simpa using subMap_mono ι (h1 i)
    | right i => simpa using subComap_mono p (h1' i)
  · induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        intro h
        simpa using subMap_mono ι (h2 i j h)
      | right j =>
        intro _
        simp only [Fin.append_left, Fin.append_right]
        rintro _ ⟨u, _, rfl⟩
        show p (ι u) ∈ (T' j).toSubmodule
        rw [h0]
        exact zero_mem _
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        intro h
        have := j.2
        simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
        omega
      | right j =>
        intro h
        have h' : i < j := by
          simp only [Fin.lt_def, Fin.val_natAdd] at h ⊢
          omega
        simpa using subComap_mono p (h2' i j h')
  · induction i using Fin.addCases with
    | left i => simpa using step_map ι hι (step_iff.1 (h3 i))
    | right i => simpa using step_comap p hp (step_iff.1 (h3' i))

theorem jhMult_exact (hσ : σ.IsIrreducible) (hι : Function.Injective ι)
    (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) (hker : ∀ v, p v = 0 → ∃ u, ι u = v) :
    jhMult σ ρ = jhMult σ ρ₁ + jhMult σ ρ₂ := by
  classical
  apply le_antisymm
  · refine iSup₂_le ?_
    rintro r ⟨S, T, h1, h2, h3⟩
    let A : Finset (Fin r) :=
      Finset.univ.filter fun i => Step σ (subComap ι (S i)) (subComap ι (T i))
    have hA := occurs_of_finset (σ := σ) A (fun i => subComap ι (S i)) (fun i => subComap ι (T i))
      (fun i => subComap_mono ι (h1 i)) (fun i j h => subComap_mono ι (h2 i j h))
      (fun i hi => (Finset.mem_filter.1 hi).2)
    have hB := occurs_of_finset (σ := σ) Aᶜ (fun i => subMap p (S i)) (fun i => subMap p (T i))
      (fun i => subMap_mono p (h1 i)) (fun i j h => subMap_mono p (h2 i j h))
      (fun i hi => (step_dichotomy ι p hσ hker (h1 i) (step_iff.1 (h3 i))).resolve_left
        fun h => Finset.mem_compl.1 hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
    have hc : (r : ℕ∞) = (A.card : ℕ∞) + (Aᶜ.card : ℕ∞) := by
      rw [← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
    rw [hc]
    exact add_le_add (le_iSup₂_of_le _ hA le_rfl) (le_iSup₂_of_le _ hB le_rfl)
  · refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
    rw [← Nat.cast_add]
    exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl

end Exact

theorem jhMult_sub_add_quot {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) (S : Subrepresentation ρ) :
    jhMult σ ρ = jhMult σ S.toRepresentation + jhMult σ (subQuot ⊤ S) := by
  let ι : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let p : ρ.IntertwiningMap (subQuot ⊤ S) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  refine jhMult_exact ι p hσ Subtype.val_injective (fun x => ?_) (fun u => (hp _).2 u.2)
    fun v hv => ⟨⟨v, (hp v).1 hv⟩, rfl⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨v.1, rfl⟩

theorem Step.not_le {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) {S T : Subrepresentation ρ} (h : Step σ S T) : ¬ S ≤ T := by
  intro hle
  obtain ⟨f, h1, -, h3⟩ := h
  refine (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤) (le_antisymm bot_le fun w _ => ?_)
  obtain ⟨v, hv, rfl⟩ := h1 w
  exact (h3 v hv).2 (hle hv)

theorem jhMult_ne_top {σ : Representation F G W} {ρ : Representation F G V}
    (hσ : σ.IsIrreducible) (h : HasFiniteLength ρ) : jhMult σ ρ ≠ ⊤ := by
  have hl : Module.length (MonoidAlgebra F G) ρ.asModule ≠ ⊤ := Module.length_ne_top_iff.2 h
  refine ne_top_of_le_ne_top (b := Module.length (MonoidAlgebra F G) ρ.asModule + 1)
    (by simpa using hl) (iSup₂_le ?_)
  rintro r ⟨S, T, h1, h2, h3⟩
  rcases r with _ | n
  · simp
  have hm : StrictMono fun i => Subrepresentation.subrepresentationSubmoduleOrderIso (S i) := by
    intro i j hij
    refine Subrepresentation.subrepresentationSubmoduleOrderIso.strictMono
      ((h2 i j hij).trans_lt (lt_of_le_not_ge (h1 j) ((step_iff.1 (h3 j)).not_le hσ)))
  have := Order.LTSeries.length_le_krullDim (LTSeries.mk n _ hm)
  rw [← Module.coe_length] at this
  have h' : (n : ℕ∞) ≤ Module.length (MonoidAlgebra F G) ρ.asModule := by
    exact WithBot.coe_le_coe.1 this
  push_cast
  exact add_le_add h' le_rfl

theorem jhMult_ne_zero_iff {σ : Representation F G W} {ρ : Representation F G V} :
    jhMult σ ρ ≠ 0 ↔ IsSubquotient σ ρ := by
  constructor
  · intro h
    by_contra hn
    refine h (le_antisymm (iSup₂_le ?_) zero_le)
    rintro r ⟨S, T, -, -, h3⟩
    rcases r with _ | n
    · simp
    obtain ⟨f, h1, h2, -⟩ := step_iff.1 (h3 0)
    refine absurd ⟨S 0, ⟨f ∘ₗ (S 0).toSubmodule.subtype, fun g => ?_⟩, fun w => ?_⟩ hn
    · exact LinearMap.ext fun v => h2 g v.1 v.2
    · obtain ⟨v, hv, rfl⟩ := h1 w
      exact ⟨⟨v, hv⟩, rfl⟩
  · rintro ⟨S, f, hf⟩
    let ι : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hs : Step σ (⊤ : Subrepresentation S.toRepresentation) f.ker :=
      ⟨f.toLinearMap, fun w => by
        obtain ⟨v, rfl⟩ := hf w
        exact ⟨v, trivial, rfl⟩, fun g v _ => f.isIntertwining _ _ g v, fun v _ => Iff.rfl⟩
    have h1 : OccursTimes σ ρ 1 := ⟨fun _ => subMap ι ⊤, fun _ => subMap ι f.ker,
      fun _ => subMap_mono ι le_top, fun i j h => absurd (Subsingleton.elim i j) h.ne,
      fun _ => step_iff.2 (step_map ι Subtype.val_injective hs)⟩
    have : ((1 : ℕ) : ℕ∞) ≤ jhMult σ ρ := le_iSup₂_of_le 1 h1 le_rfl
    intro h0
    rw [h0] at this
    simp at this

end GlobalTheory.JHMult
