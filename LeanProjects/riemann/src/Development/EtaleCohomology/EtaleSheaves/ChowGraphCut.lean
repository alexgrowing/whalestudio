import Development.EtaleCohomology.EtaleSheaves.ChowLCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.ChowGraphCut

theorem iterLine_isProper {P S : Scheme.{0}} {q : P ⟶ S} (h : IterLine q) : IsProper q := by
  induction h with
  | iso e he => exact inferInstance
  | comp l k hl _ ih =>
    have := hl.1
    exact inferInstance

def Cover : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact p],
  Nonempty X → ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ j, IsAffineOpen (U j)) ∧ (∀ j, (U j : Set X).Nonempty) ∧
    ∀ x : X, ∃ j, x ∈ U j

def Embed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType p]
  (V : X.Opens), IsAffineOpen V → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (W : P.Opens)
    (e : V.toScheme ⟶ W.toScheme), IterLine q ∧ IsClosedImmersion e ∧ e ≫ W.ι ≫ q = V.ι ≫ p

def IterComp : Prop := ∀ {P T S : Scheme.{0}} (l : P ⟶ T) (k : T ⟶ S), IterLine l → IterLine k → IterLine (l ≫ k)

def Prod : Prop := ∀ {S : Scheme.{0}} (n : ℕ) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S), (∀ j, IterLine (qj j)) →
  ∃ (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j), IterLine q ∧ (∀ j, π j ≫ qj j = q) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
      ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j

def Core : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁], IsIntegral X₁ →
  ∀ (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ j, (U j : Set X₁).Nonempty) → (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    (∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
      ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j) →
    ∃ (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q) (V : X₁.Opens) (s : V.toScheme ⟶ X'),
      IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧ (V : Set X₁).Nonempty ∧
      s ≫ i ≫ pullback.fst p₁ q = V.ι

theorem goal_of (hC : Cover) (hE : Embed) (hP : Prod) (hK : Core) : ChowGraph := by
  intro A _ X₁ p₁ _ hX
  have := hX
  obtain ⟨n, U, hUa, hUn, hUc⟩ := hC A p₁ inferInstance
  choose Pj qj W e hq he hc using fun j => hE A p₁ (U j) (hUa j)
  obtain ⟨P, q, π, hq', hπ, hUP⟩ := hP n Pj qj hq
  have hsep : ∀ j, IsSeparated (qj j) := fun j => by
    have := iterLine_isProper (hq j)
    infer_instance
  obtain ⟨X', i, V, s, h1, h2, h3, h4⟩ := hK p₁ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  exact ⟨P, q, X', i, V, s, hq', h1, h2, h3, h4⟩

end LateralTheory.E.ChowGraphCut

end
