import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfSval
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorOnPullbackEqSum

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.OneGenerator

theorem transport_level {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
    (P : PELUnif (maximalIdeal V) t) {F : Type} [Field F] [Algebra (FractionRing V) F] {n m : ℕ} (h : n = m)
    (θ r₀ r : Fam P.D.toPre F n) (p : QkPt P.D.toPre F n)
    (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε n))) (ζ : F)
    (x : TFK (R := V) F ⟶ P.A.A) (hx : P.ToA F n p x) (hw : w.IsGen) (hf : FinOrd P.D F n p w ζ)
    (hΦ : PhiRel P.D.toPre F n p w θ r₀) (hs : Fam.IsSmul P.D.toPre F ζ r₀ r) :
    ∃ (θ' r₀' r' : Fam P.D.toPre F m) (p' : QkPt P.D.toPre F m)
      (w' : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p'.g.b) (DegPre.lineε m))),
      HEq θ θ' ∧ P.ToA F m p' x ∧ w'.IsGen ∧ FinOrd P.D F m p' w' ζ ∧ PhiRel P.D.toPre F m p' w' θ' r₀' ∧
        Fam.IsSmul P.D.toPre F ζ r₀' r' ∧ HEq r r' := by
  subst h
  exact ⟨θ, r₀, r, p, w, HEq.rfl, hx, hw, hf, hΦ, hs, HEq.rfl⟩

end GlobalTheory.OneGenerator

namespace GlobalTheory

open OneGenerator in

theorem descent_one_generator : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (g g' : ℕ), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' → a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1) (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα → ∀ (pb : QkPt P.D.toPre F (1 * g')) (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g')))) (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')), P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 → FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ → Fam.IsSmul P.D.toPre F ζb tb₀ tb → ∀ (p : QkPt P.D.toPre F (1 * g' * g)) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * g' * g)))) (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (1 * g' * g) p w ζ → P.ToA F (1 * g' * g) p x → x ≫ P.oA.act (star a) = 1 → ∀ (s₂ t₀ r : Fam P.D.toPre F (1 * g' * g)), PullAl P.D F P.oD a (1 * g') g tb s₂ → PhiRel P.D.toPre F (1 * g' * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r → ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g))) (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g))))) (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))), PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  intro hL _ _ _ V _ _ _ _ E _ _ _ H t P hT
  letI := H.starRing
  intro a a' g g' hg hg' hco haa haa' F _ _ _ θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
    p w ζ x hw hζ hf hx hxa s₂ t₀ r hs₂ hΦ hr
  have hk : 1 ≤ 1 * g' := by omega
  have hkN : 1 ≤ 1 * g' * g := Nat.mul_pos hk hg
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a g (1 * g') hg hk haa
  have key : ∃ (p₂ : QkPt P.D.toPre F (1 * g' * g))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * g' * g))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ : Fam P.D.toPre F (1 * g' * g)),
      P.ToA F (1 * g' * g) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a' * a)) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧
        FinOrd P.D F (1 * g' * g) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * g' * g) p₂ w₂ (π θα) r₀ ∧
        Fam.IsSmul P.D.toPre F ζ₂ r₀ r := by
    by_cases h0 : θα = 0
    · obtain ⟨Φ, hΦ'⟩ := phiFun_of hL V _ P.D F (1 * g') hk pb wb hwb
      have e₀ : tb = 0 := by
        rw [(DVR.isSmul_iff _ _ _).1 hsb, (hΦ' _ _).1 hΦb, h0, map_zero, smul_zero]
      have e₁ : s₂ = π θα := by rw [(hπ _ _).1 hs₂, e₀, h0]
      refine ⟨p, w, ζ, x, t₀, hx, ?_, hw, hζ, hf, e₁ ▸ hΦ, hr⟩
      have := P.oA.hom (star a')
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa, MonObj.one_comp]
    · obtain ⟨p₂, x₂, w₂, ζ₂, t₂, k₁, k₂, k₃, k₄, k₅⟩ := operator_on_pullback_eq_sum hL E H V t P hT a a' g g'
        hg hg' hco haa haa' F θα tb (π θα) s₂ t₀ r h0 ((hπ _ _).2 rfl) hs₂ 1 (fun _ => 1) (fun _ => pb)
        (fun _ => xb) (fun _ => wb) (fun _ => ζb) (fun _ => tb)
        ⟨fun _ => hxb, fun _ => hxba, fun _ => ⟨hwb, hζb, hfb⟩, fun _ => ⟨tb₀, hΦb, hsb⟩, by simp⟩
        p x w ζ hx hxa hw hζ hf hΦ hr
      obtain ⟨r₀, l₁, l₂⟩ := k₄ 0
      have e : r = t₂ 0 := by simpa using k₅
      exact ⟨p₂ 0, w₂ 0, ζ₂ 0, x₂ 0, r₀, k₁ 0, k₂ 0, (k₃ 0).1, (k₃ 0).2.1, (k₃ 0).2.2, l₁, e ▸ l₂⟩
  obtain ⟨p₂, w₂, ζ₂, x₂, r₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := key
  obtain ⟨θ', r₀', r', p', w', m₁, m₂, m₃, m₄, m₅, m₆, m₇⟩ :=
    transport_level P (Nat.mul_assoc 1 g' g) (π θα) r₀ r p₂ w₂ ζ₂ x₂ k₁ k₃ k₅ k₆ k₇
  have hc := pullAl_comp hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a a' g g' 1 hg hg' le_rfl haa haa' θ θα (π θα) θ' hθ
    ((hπ _ _).2 rfl) m₁
  rw [_root_.mul_comm a' a] at hc k₂
  exact ⟨θ', p', w', ζ₂, x₂, r₀', r', hc, m₂, k₂, m₃, k₄, m₄, m₅, m₆, m₇⟩

end GlobalTheory
