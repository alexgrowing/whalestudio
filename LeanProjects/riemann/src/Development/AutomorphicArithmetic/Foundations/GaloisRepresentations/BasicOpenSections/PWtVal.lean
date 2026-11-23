import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (resPt)

namespace UpperTheory.Gal.Mod

private theorem pt_comp {Ω : Type} [Field Ω] {X X' : Scheme.{0}} (x : gp Ω ⟶ X) (f : X ⟶ X') :
    pt (x ≫ f) = f (pt x) := rfl

private theorem finsum_single {α : Type*} {s : Set α} {f : α → ℤ} {a : α} (ha : a ∈ s)
    (h : ∀ b ∈ s, b ≠ a → f b = 0) : ∑ᶠ b ∈ s, f b = f a := by
  have : ∑ᶠ b ∈ s, f b = ∑ᶠ b ∈ ({a} : Set α), f b := by
    apply finsum_mem_inter_support_eq
    ext b
    simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hb, hf⟩
      refine ⟨?_, hf⟩
      by_contra hne
      exact hf (h b hb hne)
    · rintro ⟨rfl, hf⟩
      exact ⟨ha, hf⟩
  rw [this, finsum_mem_singleton]

private theorem finsum_count {α : Type*} {s : Set α} (hs : s.Finite) (P : α → Prop) [DecidablePred P] :
    ∑ᶠ b ∈ s, (if P b then (1 : ℤ) else 0) = ((s ∩ {b | P b}).ncard : ℤ) := by
  have hB : (s ∩ {b | P b}).Finite := hs.subset Set.inter_subset_left
  have : ∑ᶠ b ∈ s, (if P b then (1 : ℤ) else 0) = ∑ᶠ b ∈ s ∩ {b | P b}, (if P b then (1 : ℤ) else 0) := by
    apply finsum_mem_inter_support_eq
    ext b
    simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
    by_cases hb : P b <;> simp [hb]
  rw [this, finsum_mem_eq_finite_toFinset_sum _ hB, Set.ncard_eq_toFinset_card _ hB]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ))]
  · simp
  · intro b hb
    have := (hB.mem_toFinset.1 hb).2
    simp only [Set.mem_setOf_eq] at this
    simp [this]

theorem wtVal : FibExt → SecGen → ClopenAt → WtVal := by
  intro hF hS hC p Y T w hw V _ _ _ _ _ hp y
  have hTfin : IsFinite T.p := T.fin
  let K := FractionRing V
  let η : gp K ⟶ Spec (CommRingCat.of V) := sp (algebraMap V K)
  have hSy := hS T.p V y
  refine ⟨?_, ?_⟩
  · have hfinite : (fib T.p (η ≫ y)).Finite := (hF T.p K K (RingHom.id K) (η ≫ y)).1
    have : {z : Spec (CommRingCat.of V) ⟶ T.Z | z ≫ T.p = y}.Finite :=
      Set.Finite.of_injOn hSy.mapsTo hSy.injOn hfinite
    exact this.to_subtype
  intro z₀ hz₀
  classical
  let r : pullback T.p y ⟶ Spec (CommRingCat.of V) := pullback.snd T.p y
  let v : pullback T.p y ⟶ T.Z := pullback.fst T.p y
  have hrfin : IsFinite r := inferInstance
  have hcond : v ≫ T.p = r ≫ y := pullback.condition
  let z₁ : gp (IsLocalRing.ResidueField V) ⟶ pullback T.p y := pullback.lift z₀ (resPt V) hz₀
  have hz₁r : z₁ ≫ r = resPt V := pullback.lift_snd _ _ _
  have hz₁v : z₁ ≫ v = z₀ := pullback.lift_fst _ _ _
  obtain ⟨U, hU, hUz⟩ := hC V r z₁ hz₁r
  let φ : _ → ℤ := fun x => if x ∈ U then 1 else 0
  have hφ : IsLocallyConstant φ := by
    have h := (LocallyConstant.charFn ℤ hU).isLocallyConstant
    convert h using 1
    funext x
    by_cases hx : x ∈ U
    · exact (if_pos hx).trans ((LocallyConstant.charFn_eq_one (Y := ℤ) x hU).2 hx).symm
    · exact (if_neg hx).trans ((LocallyConstant.charFn_eq_zero (Y := ℤ) x hU).2 hx).symm
  obtain ⟨ψ, hψ, hsum⟩ : ∃ ψ : Spec (CommRingCat.of V) → ℤ, IsLocallyConstant ψ ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ Spec (CommRingCat.of V)),
        ψ (pt x) = ∑ᶠ z ∈ fib r x, w Ω (z ≫ v) * φ (pt z) := hw.1 (TranscendenceTraces.Sq.of T.p y) φ hφ
  have hconn : PreconnectedSpace (Spec (CommRingCat.of V)) := inferInstance
  have hψc : ψ (pt η) = ψ (pt (resPt V)) := hψ.apply_eq_of_preconnectedSpace _ _

  have hcl : ψ (pt (resPt V)) = w _ z₀ := by
    rw [hsum]
    have hmem : z₁ ∈ fib r (resPt V) := hz₁r
    rw [finsum_single hmem]
    · have : pt z₁ ∈ U := (hUz z₁ hz₁r).2 rfl
      simp [φ, this, hz₁v]
    · intro b hb hne
      have : pt b ∉ U := fun h => hne ((hUz b hb).1 h)
      simp [φ, this]

  have hconst : ∀ σ : Spec (CommRingCat.of V) ⟶ pullback T.p y,
      pt (η ≫ σ) ∈ U ↔ pt (resPt V ≫ σ) ∈ U := by
    intro σ
    have h := (hφ.comp_continuous σ.continuous).apply_eq_of_preconnectedSpace (pt η) (pt (resPt V))
    simp only [Function.comp_apply] at h
    rw [pt_comp, pt_comp]
    by_cases h1 : σ (pt η) ∈ U <;> by_cases h2 : σ (pt (resPt V)) ∈ U <;> simp_all [φ]
  have hpK : (p : K) ≠ 0 := by
    intro h0
    apply hp
    apply IsFractionRing.injective V K
    simpa using h0
  have hfibfin : (fib r η).Finite := (hF r K K (RingHom.id K) η).1
  have hgen : ψ (pt η) = ((fib r η ∩ {z | pt z ∈ U}).ncard : ℤ) := by
    rw [hsum, ← finsum_count hfibfin]
    refine finsum_mem_congr rfl ?_
    intro z _
    rw [hw.2 K (z ≫ v) hpK]
    simp [φ]

  let sec : T.Sec y → (Spec (CommRingCat.of V) ⟶ pullback T.p y) := fun s =>
    pullback.lift s.1 (𝟙 _) (by rw [s.2, Category.id_comp])
  have hsecr : ∀ s, sec s ≫ r = 𝟙 _ := fun s => pullback.lift_snd _ _ _
  have hsecv : ∀ s, sec s ≫ v = s.1 := fun s => pullback.lift_fst _ _ _
  let e : {z : T.Sec y // resPt V ≫ z.1 = z₀} → (gp K ⟶ pullback T.p y) := fun s => η ≫ sec s.1
  have he : Function.Injective e := by
    intro s s' h
    apply Subtype.ext
    apply Subtype.ext
    apply hSy.injOn s.1.2 s'.1.2
    have := congrArg (· ≫ v) h
    simpa [e, hsecv] using this
  have hrange : Set.range e = fib r η ∩ {z | pt z ∈ U} := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨?_, ?_⟩
      · change (η ≫ sec s.1) ≫ r = η
        rw [Category.assoc, hsecr, Category.comp_id]
      · change pt (η ≫ sec s.1) ∈ U
        rw [hconst]
        have hs : resPt V ≫ sec s.1 = z₁ := by
          apply pullback.hom_ext
          · change (resPt V ≫ sec s.1) ≫ v = z₁ ≫ v
            rw [Category.assoc, hsecv, hz₁v, s.2]
          · change (resPt V ≫ sec s.1) ≫ r = z₁ ≫ r
            rw [Category.assoc, hsecr, Category.comp_id, hz₁r]
        rw [hs]
        exact (hUz z₁ hz₁r).2 rfl
    · rintro ⟨hz, hzU⟩
      have hz' : z ∈ fib r (sp (algebraMap V (FractionRing V)) ≫ 𝟙 _) := by
        change z ≫ r = η ≫ 𝟙 _
        rw [Category.comp_id]
        exact hz
      obtain ⟨σ, hσ, rfl⟩ := (hS r V (𝟙 _)).surjOn hz'
      have hσ' : σ ≫ r = 𝟙 _ := hσ
      have hσU : pt (η ≫ σ) ∈ U := hzU
      rw [hconst] at hσU
      have hσ₀ : resPt V ≫ σ = z₁ := by
        apply (hUz _ _).1 hσU
        rw [Category.assoc, hσ', Category.comp_id]
      let s : T.Sec y := ⟨σ ≫ v, by rw [Category.assoc, hcond, ← Category.assoc, hσ', Category.id_comp]⟩
      have hsσ : sec s = σ := by
        apply pullback.hom_ext
        · change sec s ≫ v = σ ≫ v
          rw [hsecv]
        · change sec s ≫ r = σ ≫ r
          rw [hsecr, hσ']
      refine ⟨⟨s, ?_⟩, ?_⟩
      · change resPt V ≫ σ ≫ v = z₀
        rw [← Category.assoc, hσ₀, hz₁v]
      · change η ≫ sec s = η ≫ σ
        rw [hsσ]
  rw [← hcl, ← hψc, hgen, ← hrange, ← Nat.card_coe_set_eq, Nat.card_congr (Equiv.ofInjective e he).symm]

end UpperTheory.Gal.Mod

end
