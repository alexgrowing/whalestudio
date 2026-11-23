import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SumThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CountSys
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

namespace UpperTheory.GalN.V.Win

structure EigData (n q : ℕ) (m : Fin n → ℤ) (wt : ℤ) where

  S : Type
  fin : Finite S

  β : S → Multiset ℂ
  card : ∀ s, (β s).card = n
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, β (e s) = (β s).map σ
  pure : ∀ s, Win q wt (β s)
  int : ∀ a : ℤ, (∀ i, -a ≤ m i) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b)
  intInv : ∀ a : ℤ, (∀ i, m i ≤ a) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)

instance {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} : Inhabited (EigData n q m wt) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim,
    fun _ _ s => s.elim, fun _ _ s => s.elim⟩⟩

def EigData.Classifies {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n q : ℕ}
    {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F))
    (admitted : (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, FrobEig ι r.1 w ((D.β (cl r)).map (·⁻¹))

def CountK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → (∀ i, m i + m i.rev = 1 - n) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m (1 - n), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmK ι M m)

def CountQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal → ¬ p ∣ M →
      ∃ D : EigData n p m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmR ι M m wt)

def CountP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmP ι M m)

def RootSum : Prop :=
  ∀ (n p : ℕ), 0 < p → ∀ (m : Fin n → ℤ) (wt : ℤ) (I : Type) [Fintype I] (q f : I → ℕ), (∀ i, 1 ≤ f i ∧ f i ≤ 2 ∧ q i = p ^ f i) →
    ∀ D : ∀ i, EigData n (q i) m wt, ∃ D' : EigData n p m wt, Nat.card D'.S ≤ 2 ^ (n + 1) * ∑ i, Nat.card (D i).S ∧
      ∃ e : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) → D'.S,
        Function.Injective e ∧ ∀ x, D'.β (e x) = x.2.1.1.2

structure TrData (q e : ℕ) where

  S : Type
  fin : Finite S

  t : S → ℂ
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ u : S ≃ S, ∀ s, t (u s) = σ (t s)
  bd : ∀ s, ‖t s‖ ≤ Real.sqrt q + 2
  int : ∀ s, IsIntegral ℤ ((q : ℂ) ^ e * t s)

instance {q e : ℕ} : Inhabited (TrData q e) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim, fun s => s.elim⟩⟩

namespace TrData

variable {q e : ℕ}

def Classifies {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (D : TrData q e) (ι : Qbar l ≃+* ℂ) (g : Γ)
    (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, (r.1 g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace = ι.symm (D.t (cl r))

def sum (D D' : TrData q e) : TrData q e where
  S := D.S ⊕ D'.S
  fin := by have := D.fin; have := D'.fin; infer_instance
  t := Sum.elim D.t D'.t
  conj σ := by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨u', hu'⟩ := D'.conj σ
    exact ⟨u.sumCongr u', fun s => by cases s <;> simp [hu, hu']⟩
  bd s := by cases s; exacts [D.bd _, D'.bd _]
  int s := by cases s; exacts [D.int _, D'.int _]

theorem card_sum (D D' : TrData q e) : Nat.card (D.sum D').S = Nat.card D.S + Nat.card D'.S := by
  have := D.fin; have := D'.fin
  exact Nat.card_sum

theorem Classifies.sum {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {D D' : TrData q e} {ι : Qbar l ≃+* ℂ} {g : Γ}
    {P P' : (Γ →* GL (Fin 3) (Qbar l)) → Prop} (h : D.Classifies ι g P) (h' : D'.Classifies ι g P') :
    (D.sum D').Classifies ι g fun r => P r ∨ P' r := by
  classical
  obtain ⟨cl, h1, h2⟩ := h
  obtain ⟨cl', h1', h2'⟩ := h'
  let F : {r // P r ∨ P' r} → D.S ⊕ D'.S :=
    fun r => if hr : P r.1 then Sum.inl (cl ⟨r.1, hr⟩) else Sum.inr (cl' ⟨r.1, r.2.resolve_left hr⟩)
  have e1 : ∀ r (hr : P r.1), F r = Sum.inl (cl ⟨r.1, hr⟩) := fun r hr => dif_pos hr
  have e2 : ∀ r (hr : ¬ P r.1), F r = Sum.inr (cl' ⟨r.1, r.2.resolve_left hr⟩) := fun r hr => dif_neg hr
  refine ⟨F, fun r r' (H : F r = F r') => ?_, fun r => ?_⟩
  · by_cases hr : P r.1 <;> by_cases hr' : P r'.1
    · rw [e1 r hr, e1 r' hr'] at H; exact h1 _ _ (Sum.inl.inj H)
    · rw [e1 r hr, e2 r' hr'] at H; cases H
    · rw [e2 r hr, e1 r' hr'] at H; cases H
    · rw [e2 r hr, e2 r' hr'] at H; exact h1' _ _ (Sum.inr.inj H)
  · change _ = ι.symm (Sum.elim D.t D'.t (F r))
    by_cases hr : P r.1
    · rw [e1 r hr]; exact h2 ⟨r.1, hr⟩
    · rw [e2 r hr]; exact h2' ⟨r.1, _⟩

end TrData

theorem exists_eigData {P W : Type} (Sig : Set P) (Iso : P → P → Prop) (sys : P → W → Multiset ℂ)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → sys a = sys b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N)
    (hconj : ∀ σ : ℂ ≃+* ℂ, ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ v, sys b v = (sys a v).map σ)
    (w : W) {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (hn : ∀ a ∈ Sig, (sys a w).card = n)
    (hq : 0 < q) (hpure : ∀ a ∈ Sig, Win q (-(wt : ℝ)) (sys a w))
    (hint : ∀ a ∈ Sig, SlopesIn q m (sys a w)) :
    ∃ D : EigData n q m wt, Nat.card D.S ≤ N ∧ ∃ cl : ↥Sig → D.S, (∀ a b, cl a = cl b → sys a = sys b) ∧
      ∀ a, (D.β (cl a)).map (·⁻¹) = sys a w := by
  obtain ⟨hfin, hN⟩ := finite_image_of_card_le Sig Iso sys hiso N hcard
  refine ⟨⟨↥(sys '' Sig), hfin, fun s => (s.1 w).map (·⁻¹), ?_, ?_, ?_, ?_, ?_⟩, hN,
    fun a => ⟨sys a, a, a.2, rfl⟩, fun a b h => congrArg Subtype.val h, fun a => ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    simpa using hn a ha
  · intro σ
    have hmem : ∀ s : ↥(sys '' Sig), (fun v => (s.1 v).map σ) ∈ sys '' Sig := by
      rintro ⟨_, a, ha, rfl⟩
      obtain ⟨b, hb, h⟩ := hconj σ a ha
      exact ⟨b, hb, funext h⟩
    let F : ↥(sys '' Sig) → ↥(sys '' Sig) := fun s => ⟨_, hmem s⟩
    have hF : Function.Injective F := by
      intro s s' h
      refine Subtype.ext (funext fun v => ?_)
      exact Multiset.map_injective σ.injective (congrFun (congrArg Subtype.val h) v)
    refine ⟨Equiv.ofBijective F (Finite.injective_iff_bijective.1 hF), fun s => ?_⟩
    simp [F, Multiset.map_map]
  · rintro ⟨_, a, ha, rfl⟩
    exact (hpure a ha).inv hq
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    exact (hint a ha c hc).1 k hk
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [inv_inv]
    exact (hint a ha c hc).2 k hk
  · simp [Multiset.map_map]

end UpperTheory.GalN.V.Win
