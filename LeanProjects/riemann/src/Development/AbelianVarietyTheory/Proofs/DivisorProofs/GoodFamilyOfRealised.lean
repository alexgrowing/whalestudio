import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula

noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues Formalism.MainNotions.PrimeDegreeVariant

section Conclusion

variable {K G : Type} [Field K] [Group G]

def ConclFinset (emb : K →+* ℂ) (Y : Set (G → ℂ)) : Prop :=
  ∃ Xg : Finset (G → K), (∀ ch, ch ∈ Y ↔ ∃ c ∈ Xg, ∀ t, ch t = emb (c t)) ∧ (∀ c ∈ Xg, IsAbsIrrChar c) ∧
    ∃ T : GoodSet K G, ∀ c, c ∈ Xg ↔ ∃ s : T.S, ∀ t, c t = LinearMap.trace K (T.W s) (T.tau s t)

def ConclRange (σ : K →+* ℂ) (Y : Set (G → ℂ)) : Prop :=
  (∀ Θ ∈ Y, ∃ ΘK : G → K, (∀ t, σ (ΘK t) = Θ t) ∧ IsAbsIrrChar ΘK) ∧
    ∃ T : GoodSet K G, (Set.range fun (s : T.S) (t : G) => σ (LinearMap.trace K (T.W s) (T.tau s t))) = Y

theorem ConclRange.mono {σ : K →+* ℂ} {Y Y' : Set (G → ℂ)} (h : ConclRange σ Y) (hY : Y' ⊆ Y) : ConclRange σ Y' := by
  classical
  obtain ⟨h1, T, rfl⟩ := h
  let T' : GoodSet K G :=
    { S := {s : T.S // (fun t => σ (LinearMap.trace K (T.W s) (T.tau s t))) ∈ Y'}
      W := fun s => T.W s.1
      tau := fun s => T.tau s.1
      irr := fun s => T.irr s.1
      inj := fun s s' e => Subtype.ext (T.inj e) }
  refine ⟨fun Θ hΘ => h1 Θ (hY hΘ), T', Set.ext fun Θ => ⟨?_, fun hΘ => ?_⟩⟩
  · rintro ⟨s, rfl⟩
    exact s.2
  · obtain ⟨s, rfl⟩ := hY hΘ
    exact ⟨⟨s, hΘ⟩, rfl⟩

end Conclusion

section OnePrime

variable {g : ℕ} [Fact g.Prime] {P : Type} {r m : ℕ}

def FullGood (ω : P → Fbar g →*₀ ℂ) (η : P → Fin m → (ZMod g)ˣ → ℂ) (τ : P → GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (f : P → (ZMod g)[X]) (c : P → Fin m → (ZMod g)ˣ), (∀ v j, IsTameLabel (ω v) (η v j) (c v j)) ∧
    IsGood r g f (fun v (js : Fin m × Bool) => if js.2 then c v js.1 else (c v js.1)⁻¹) ∧
    ∀ v, IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar (ω v) (f v) (τ v)

def TorusGood (ι : P → (Fbar g)ˣ →* ℂˣ) (η : P → Fin m × Bool → (ZMod g)ˣ → ℂ)
    (τ : P → GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (f : P → (ZMod g)[X]) (c : P → Fin m × Bool → (ZMod g)ˣ), (∀ v j, IsCharLabel (ι v) (η v j) (c v j)) ∧
    IsGood r g f c ∧ ∀ v, IndefiniteRowSideFullHecke.TameCharacterTorusValues.IsTypeChar (ι v) (f v) (τ v)

theorem FullGood.change {ω ω' : P → Fbar g →*₀ ℂ} (hω : ∀ v, Function.Injective (ω v))
    (hω' : ∀ v, Function.Injective (ω' v)) {η : P → Fin m → (ZMod g)ˣ → ℂ} {τ : P → GL (Fin r) (ZMod g) → ℂ}
    (h : FullGood ω' η τ) : FullGood ω η τ := by
  obtain ⟨f, c, h1, h2, h3⟩ := h
  choose β hβ using fun v => exists_beta (hω v) (hω' v)
  choose f' hf' using fun v => exists_tr (β v) _ (f v) (h2.1 v).1 rfl
  choose c' hc' using fun v j => exists_unit_of_pow (y := β v (algebraMap (ZMod g) (Fbar g) (c v j)))
    (by rw [← map_pow, unit_pow, map_one])
  refine ⟨f', c', fun v j z => ?_, isGood_tr β hf' (fun v js => ?_) h2,
    fun v => isTypeChar_tr (hβ v) (h2.1 v).2.2 (hf' v) (h3 v)⟩
  · rw [h1 v j z, hβ v 1 one_pos _ _ (unit_pow _) (unit_pow _), hc']
  · split_ifs
    · exact hc' v js.1
    · rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, map_inv₀, hc']

theorem FullGood.reindex {P' : Type} (e : P' ≃ P) {ω : P → Fbar g →*₀ ℂ} {η : P → Fin m → (ZMod g)ˣ → ℂ}
    {τ : P → GL (Fin r) (ZMod g) → ℂ} (h : FullGood ω η τ) :
    FullGood (fun v => ω (e v)) (fun v => η (e v)) (fun v => τ (e v)) := by
  obtain ⟨f, c, h0, ⟨h1, h2, h3, h4, h5, v, h6⟩, h7⟩ := h
  refine ⟨fun v => f (e v), fun v => c (e v), fun v => h0 _, ⟨fun v => h1 _, fun v => h2 _,
    fun l hl hb v => h3 l hl hb _, fun l hl hb v => h4 l hl hb _, fun a ha hb => ?_, e.symm v, by simpa using h6⟩,
    fun v => h7 _⟩
  obtain ⟨v, hv⟩ := h5 a ha hb
  exact ⟨e.symm v, by simpa using hv⟩

theorem TorusGood.full (H : CuspidalCharacterFormula) {ι : P → (Fbar g)ˣ →* ℂˣ} {ω : P → Fbar g →*₀ ℂ}
    (hι : ∀ v, Function.Injective (ι v))
    (hω : ∀ v, Function.Injective (ω v)) {η : P → Fin m → (ZMod g)ˣ → ℂ} {η' : P → Fin m × Bool → (ZMod g)ˣ → ℂ}
    (ht : ∀ v j, η' v (j, true) = η v j) (hf : ∀ v j, η' v (j, false) = fun z => (η v j z)⁻¹)
    {τ : P → GL (Fin r) (ZMod g) → ℂ} (h : TorusGood ι η' τ) : FullGood ω η τ := by
  choose ω' hω' he using fun v => exists_ext (hι v)
  obtain ⟨f, c, h1, h2, h3⟩ := h
  have a1 : ∀ v j, IsTameLabel (ω' v) (η v j) (c v (j, true)) := fun v j => ht v j ▸ (label_iff (he v) _ _).1 (h1 v _)
  refine FullGood.change hω hω' ⟨f, fun v j => c v (j, true), a1, ?_,
    fun v => typeChar_full_of_torus H (hω' v) (he v) (h3 v)⟩
  convert h2 using 3 with v js
  obtain ⟨j, _ | _⟩ := js
  · exact label_unique (hω' v) (label_inv (a1 v j)) (hf v j ▸ (label_iff (he v) _ _).1 (h1 v _))
  · rfl

end OnePrime

section Global

variable {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} [∀ i, Fact (gp i).Prime]
  {pb : Fin 2 → 𝓞 E} {K : Type} [Field K]

def placeEquiv (hT : IsTypeDatum gp pb) (i : Fin 2) : PlacesOver pb i ≃ ↥(primesOf (pb i)) where
  toFun v := ⟨v.1.1, mem_primesOf.2 ⟨pb_ne_zero hT i, v.2⟩⟩
  invFun v := ⟨toBoth hT i v, (mem_primesOf.1 v.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def eta (hT : IsTypeDatum gp pb) (m : ℕ) (σ : K →+* ℂ) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ) (i : Fin 2)
    (v : ↥(primesOf (pb i))) (j : Fin m) (z : (ZMod (gp i))ˣ) : ℂ :=
  σ (χ (j.val + 1) v.1 (Units.map ((resIso hT i v : ZMod (gp i) →+* kP v.1) : ZMod (gp i) →* kP v.1) z) : Kˣ)

end Global

end GlobalTheory.GoodCharsCompare
