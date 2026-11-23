import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraicStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteExtensionCoordsCompare
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

namespace PositivityTheory.UnitarySelfGeneration

set_option linter.unusedSectionVars false

namespace JN

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω Ω' : Type} [Field Ω] [Field Ω']

def Q (y : (Σ k, ι k) → Ω) (s : Ω) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧ aeval y g = s * aeval y h

theorem hom_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm
  exact (Finset.mem_union.1 (MvPolynomial.support_add hm)).elim (hf m) (hg m)

theorem hom_C (n : ℤ) : IsMultiHomog (MvPolynomial.C n : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, if_neg (Ne.symm h)] at hm
    exact hm rfl
  simp [this]

theorem hom_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hf hg

theorem Q_chart (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : (∏ k, y ⟨k, c k⟩) ≠ 0) :
    ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → ι k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩), Q y a := by
  classical
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨fun _ => 1, _, _, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow j _,
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c _, ?_, ?_⟩
    · simpa [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow] using hc
    · simp only [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow, pow_one, map_prod, aeval_X]
      rw [div_mul_cancel₀ _ hc]
  | algebraMap n => exact ⟨0, MvPolynomial.C n, MvPolynomial.C 1, hom_C n, hom_C 1, by simp, by simp⟩
  | add a b _ _ h1 h2 =>
    obtain ⟨d, g, h, hg, hh, h0, e⟩ := h1
    obtain ⟨d', g', h', hg', hh', h0', e'⟩ := h2
    refine ⟨d + d', g * h' + h * g', h * h', hom_add (hom_mul hg hh') (hom_mul hh hg'), hom_mul hh hh', ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero h0 h0'
    · simp only [map_add, map_mul, e, e']; ring
  | mul a b _ _ h1 h2 =>
    obtain ⟨d, g, h, hg, hh, h0, e⟩ := h1
    obtain ⟨d', g', h', hg', hh', h0', e'⟩ := h2
    refine ⟨d + d', g * g', h * h', hom_mul hg hg', hom_mul hh hh', ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero h0 h0'
    · simp only [map_mul, e, e']; ring

theorem exists_chart {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {y : (Σ k, ι k) → Ω}
    (h : CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩)) :
    ∃ c : (k : K) → ι k, (∏ k, y ⟨k, c k⟩) ≠ 0 := by
  obtain ⟨c, hc⟩ := h.cover ⟨genPt ξ, specializes_rfl⟩
  exact ⟨c, hc.1⟩

theorem birational_of_tie {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {y : (Σ k, ι k) → Ω}
    (h : CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩)) : Birational y := by
  intro s
  obtain ⟨c, hc⟩ := exists_chart h
  obtain ⟨t, ht, ht0, hts⟩ := GlobalTheory.CompanionTheory.Ar.HtJoin.exists_mul_mem h hc s
  obtain ⟨d, g, k, hg, hk, k0, e⟩ := Q_chart y c hc _ ht
  obtain ⟨d', g', k', hg', hk', k0', e'⟩ := Q_chart y c hc _ hts
  refine ⟨d' + d, g' * k, k' * g, hom_mul hg' hk, hom_mul hk' hg, ?_, ?_⟩
  · rw [map_mul, e]; exact mul_ne_zero k0' (mul_ne_zero ht0 k0)
  · simp only [map_mul, e, e']; ring

theorem aeval_mem [CharZero Ω] (F : IntermediateField ℚ Ω) {σ : Type} (r : σ → Ω) (hr : ∀ p, r p ∈ F)
    (g : MvPolynomial σ ℤ) : aeval r g ∈ F := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (hr i)

theorem aeval_map (i : Ω →+* Ω') {σ : Type} (r : σ → Ω) (g : MvPolynomial σ ℤ) :
    aeval (fun p => i (r p)) g = i (aeval r g) := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X]

theorem blockFnField_eq [CharZero Ω'] (i : Ω →+* Ω') (y : (Σ k, ι k) → Ω) (hb : Birational y)
    (c : (k : K) → ι k) (hc : (∏ k, y ⟨k, c k⟩) ≠ 0) :
    (blockFnField (fun p => i (y p))).toSubfield = i.fieldRange := by
  have hck : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  apply le_antisymm
  · intro t ht
    change t ∈ blockFnField (fun p => i (y p)) at ht
    unfold blockFnField at ht
    induction ht using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, q, -, rfl⟩ := hx
      exact ⟨y p / y q, by simp⟩
    | algebraMap x => simp
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | inv _ _ h => exact inv_mem h
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  · rintro _ ⟨s, rfl⟩
    change i s ∈ blockFnField (fun p => i (y p))
    obtain ⟨d, g, h, hg, hh, h0, e⟩ := hb s
    let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
    have ey : y = fun p => y ⟨p.1, c p.1⟩ * r p := funext fun p => (mul_div_cancel₀ _ (hck p.1)).symm
    have e1 := aeval_blockScale hg (fun k => y ⟨k, c k⟩) r
    have e2 := aeval_blockScale hh (fun k => y ⟨k, c k⟩) r
    rw [← ey] at e1 e2
    have hP : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hck k)
    have h0' : aeval r h ≠ 0 := fun h' => h0 (by rw [e2, h', mul_zero])
    have es : s = aeval r g / aeval r h := by
      rw [eq_div_iff h0']
      apply mul_left_cancel₀ hP
      rw [← e1, e, e2]; ring
    have hr : ∀ p, i (r p) ∈ blockFnField (fun p => i (y p)) := fun p =>
      IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, by simp [r]⟩
    rw [es, map_div₀, ← aeval_map, ← aeval_map]
    exact div_mem (aeval_mem _ _ hr g) (aeval_mem _ _ hr h)

theorem mCoordIdeal_map (i : Ω →+* Ω') (y : (Σ k, ι k) → Ω) :
    mCoordIdeal (fun p => i (y p)) = mCoordIdeal y := by
  have key : ∀ s : MRing ι, mConeMap (fun p => i (y p)) s = MvPolynomial.map i (mConeMap y s) := by
    intro s
    unfold mConeMap
    induction s using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp => simp only [map_mul, hp, aeval_X, map_C, map_X]
  ext s
  simp only [mCoordIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective i i.injective)

theorem finite_of (i : Ω →+* Ω') (h : FiniteDimensional i.fieldRange Ω') :
    letI := i.toAlgebra; Module.Finite Ω Ω' := by
  have h1 : (algebraMap i.fieldRange Ω').Finite := RingHom.finite_algebraMap.2 h
  have h2 : i.rangeRestrictField.Finite := RingHom.Finite.of_surjective _ i.rangeRestrictField_bijective.2
  exact RingHom.Finite.comp h1 h2

theorem relfinrank_eq [CharZero Ω'] (i : Ω →+* Ω') (A B : IntermediateField ℚ Ω') (hA : A.toSubfield = i.fieldRange)
    (hB : B.toSubfield = (RingHom.id Ω').fieldRange) :
    IntermediateField.relfinrank A B = Module.finrank i.fieldRange Ω' := by
  have : (RingHom.id Ω').fieldRange = ⊤ := by
    ext x
    simp
  unfold IntermediateField.relfinrank
  rw [hA, hB, this, Subfield.relfinrank_top_right]

end JN

open JN in
theorem j_normal_of (hjoin : ∀ (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (J₁ : K₁ → Type) (J₂ : K₂ → Type) [∀ k, Fintype (J₁ k)] [∀ k, Fintype (J₂ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (y₂ : (Σ k, J₂ k) → Ω₂) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), (letI := i₁.toAlgebra; Module.Finite Ω₁ Ω) → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (m : ℕ) (w : Fin m → Ω) (y : (Σ k : K₁ ⊕ K₂ ⊕ Unit, Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), (∀ k a, y ⟨.inl k, a⟩ = i₁ (y₁ ⟨k, a⟩)) ∧ (∀ k a, y ⟨.inr (.inl k), a⟩ = i₂ (y₂ ⟨k, a⟩)) ∧ (∀ a, y ⟨.inr (.inr ()), a⟩ = w a) ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Z, IsDomain (Z.presheaf.stalk q) ∧ IsIntegrallyClosed (Z.presheaf.stalk q)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂) : ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), IsArithVar (mCoordIdeal y₁) d → IsArithVar (mCoordIdeal y₂) d → Birational y₁ → Birational y₂ → FiniteDimensional i₁.fieldRange Ω → FiniteDimensional i₂.fieldRange Ω → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (y : (Σ k, ι k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧ y ∘ v₁ = (fun p => i₁ (y₁ p)) ∧ y ∘ v₂ = (fun p => i₂ (y₂ p)) ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = Module.finrank i₁.fieldRange Ω ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = Module.finrank i₂.fieldRange Ω := by
  intro K₁ _ ι₁ _ K₂ _ ι₂ _ Ω₁ Ω₂ Ω _ _ _ _ i₁ i₂ y₁ y₂ d X₁ X₂ ξ₁ ξ₂ ha₁ ha₂ hb₁ hb₂ hf₁ hf₂ hg₁ hg₂ ht₁ ht₂
  obtain ⟨m, w, y, Z, ξ, h₁, h₂, e₁, e₂, -, hg, ht, hN, hd₁, hd₂⟩ :=
    hjoin Ω₁ Ω₂ Ω i₁ i₂ K₁ K₂ ι₁ ι₂ y₁ y₂ X₁ X₂ ξ₁ ξ₂ (finite_of i₁ hf₁) hg₁ hg₂ ht₁ ht₂
  let ι : K₁ ⊕ K₂ ⊕ Unit → Type := Sum.elim ι₁ (Sum.elim ι₂ fun _ => Fin m)
  have fin : ∀ k, Finite (ι k) := by
    rintro (k | k | k)
    · change Finite (ι₁ k); infer_instance
    · change Finite (ι₂ k); infer_instance
    · change Finite (Fin m); infer_instance
  let inst : ∀ k, Fintype (ι k) := fun k => Fintype.ofFinite _
  let v₁ : (Σ k, ι₁ k) → Σ k, ι k := fun p => ⟨.inl p.1, p.2⟩
  let v₂ : (Σ k, ι₂ k) → Σ k, ι k := fun p => ⟨.inr (.inl p.1), p.2⟩
  have hv₁ : IsBlockMap (ι' := ι) Sum.inl v₁ := by
    refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, a⟩ ⟨k', a'⟩ h
      cases h
      rfl
    · rintro ⟨_, a⟩ ⟨k, rfl⟩
      exact ⟨⟨k, a⟩, rfl⟩
  have hv₂ : IsBlockMap (ι' := ι) (fun k => .inr (.inl k)) v₂ := by
    refine ⟨fun _ _ h => Sum.inl_injective (Sum.inr_injective h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, a⟩ ⟨k', a'⟩ h
      cases h
      rfl
    · rintro ⟨_, a⟩ ⟨k, rfl⟩
      exact ⟨⟨k, a⟩, rfl⟩
  have y1 : y ∘ v₁ = fun p => i₁ (y₁ p) := funext fun p => e₁ p.1 p.2
  have y2 : y ∘ v₂ = fun p => i₂ (y₂ p) := funext fun p => e₂ p.1 p.2
  have hb : Birational (ι := ι) y := birational_of_tie (ι := ι) ht
  obtain ⟨c, hc⟩ := exists_chart (ι := ι) ht
  obtain ⟨c₁, hc₁⟩ := exists_chart ht₁
  obtain ⟨c₂, hc₂⟩ := exists_chart ht₂
  have F : (blockFnField (ι := ι) y).toSubfield = (RingHom.id Ω).fieldRange :=
    blockFnField_eq (ι := ι) (RingHom.id Ω) y hb c hc
  have F₁ : (blockFnField (y ∘ v₁)).toSubfield = i₁.fieldRange := by
    rw [y1]; exact blockFnField_eq i₁ y₁ hb₁ c₁ hc₁
  have F₂ : (blockFnField (y ∘ v₂)).toSubfield = i₂.fieldRange := by
    rw [y2]; exact blockFnField_eq i₂ y₂ hb₂ c₂ hc₂
  have fd : FiniteDimensional (blockFnField (y ∘ v₁)) Ω := by
    have : FiniteDimensional (blockFnField (y ∘ v₁)).toSubfield Ω := by rw [F₁]; exact hf₁
    exact this
  refine ⟨K₁ ⊕ K₂ ⊕ Unit, inferInstance, ι, inst, Sum.inl, v₁, fun k => .inr (.inl k), v₂, y, Z, ξ, h₁, h₂, hv₁, hv₂,
    y1, y2, ?_, hb, hg, ht, hN, hd₁, hd₂, relfinrank_eq i₁ _ _ F₁ F, relfinrank_eq i₂ _ _ F₂ F⟩
  refine GlobalTheory.T.isArithVar_of_block_algebraic K₁ ι₁ _ ι Sum.inl v₁ Ω y d hv₁
    (fun k => ⟨c k, Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)⟩) ?_
    (fun t _ => Algebra.IsAlgebraic.isAlgebraic t)
  rw [y1, mCoordIdeal_map]
  exact ha₁

theorem j_normal : ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), IsArithVar (mCoordIdeal y₁) d → IsArithVar (mCoordIdeal y₂) d → Birational y₁ → Birational y₂ → FiniteDimensional i₁.fieldRange Ω → FiniteDimensional i₂.fieldRange Ω → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (y : (Σ k, ι k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧ y ∘ v₁ = (fun p => i₁ (y₁ p)) ∧ y ∘ v₂ = (fun p => i₂ (y₂ p)) ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = Module.finrank i₁.fieldRange Ω ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) = Module.finrank i₂.fieldRange Ω :=
  j_normal_of GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join

end PositivityTheory.UnitarySelfGeneration
