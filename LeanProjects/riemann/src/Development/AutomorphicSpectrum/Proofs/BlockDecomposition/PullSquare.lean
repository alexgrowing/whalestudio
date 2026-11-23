import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FResProof

theorem pull_square {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] {σ : R₀ →+* R₁} {C₀ C₁ : Type 1}
    [Category.{0} C₀] [Category.{0} C₁] {F₀ : C₀ ⥤ ModuleCat.{0} R₀} {F₁ : C₀ ⥤ ModuleCat.{0} R₁}
    {F₀' : C₁ ⥤ ModuleCat.{0} R₀} {F₂ : C₁ ⥤ ModuleCat.{0} R₁} (m₁ : Mor F₀ F₁ σ) (e : Mor F₁ F₂ (RingHom.id R₁))
    (a : Mor F₀ F₀' (RingHom.id R₀)) (m₂ : Mor F₀' F₂ σ) (j : ℕ)
    (h : ∀ z : Cn F₀ j, e.pullC j (m₁.pullC j z) = m₂.pullC j (a.pullC j z)) (y : CH.H F₀ j) :
    e.pull j (m₁.pull j y) = m₂.pull j (a.pull j y) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z))

theorem lcRes_id (q : ℕ) {U : Scheme.{0}} (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext x; rfl

theorem primRes_id {q : ℕ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : primRes (𝟙 U) ζ = ζ :=
  Subtype.ext (by
    change (𝟙 U : U ⟶ U).appTop.hom ζ.1 = ζ.1
    simp)

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def mG (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) :
    Mor (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).L (probe H r (G ⋙ CategoryOfElements.π _) n).L
      (RingHom.id ℤ) where
  G := G
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem square (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P)
    (n j : ℕ) (y : CH.H (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).L j) :
    (Mor.restrict (modF (AcrEl M.P n)) G).pull j ((lcMor hN H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).pull j y) =
      (lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j ((mG H r M G n).pull j y) :=
  pull_square (lcMor hN H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n) (Mor.restrict (modF (AcrEl M.P n)) G)
    (mG H r M G n) (lcMor hN H r (G ⋙ CategoryOfElements.π _) n) j (fun z => rfl) y

theorem pull_sch_id (q : ℕ) (i : ℤ) (j : ℕ) (X : Scheme.{0}) (x : Ht q (sch.obj X) j i) :
    pull _ (sch.map (𝟙 X)) _ j x = x := by
  rw [CategoryTheory.Functor.map_id, GlobalTheory.EtC.pull_id]

set_option maxHeartbeats 1000000 in

theorem et_restrict (hE : EtNat) (hg : InGen) (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C]
    (G : C ⥤ El M.P) (n : ℕ) (i : ℤ) (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j i) :
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    (mG H r M G n).pull j ((pts H r M (𝟭 _) n).et i j x) = (pts H r M G n).et i j x := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine (hE hg (l ^ n) (El M.P) C (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n)
    (probe H r (G ⋙ CategoryOfElements.π _) n) (gb M) (gb M) (pts H r M (𝟭 _) n) (pts H r M G n) (𝟙 _)
    (mG H r M G n) (fun c => 𝟙 _) (fun φ => ?_)
    (fun c f => (lcRes_id _ f).symm) (fun c => ?_) i
    (Or.inr fun c => primRes_id _) j x).trans (congrArg _ (pull_sch_id _ _ _ _ x))
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

end GlobalTheory.CompanionTheory.FResProof

theorem GlobalTheory.CompanionTheory.FResProof.fRes : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.FRes := by
  intro hE E hN l _ H r K M C _ G n i j x
  exact (GlobalTheory.CompanionTheory.FResProof.square hN H r M G n j _).trans
    (congrArg _ (GlobalTheory.CompanionTheory.FResProof.et_restrict hE E.gen H r M G n i j x))
