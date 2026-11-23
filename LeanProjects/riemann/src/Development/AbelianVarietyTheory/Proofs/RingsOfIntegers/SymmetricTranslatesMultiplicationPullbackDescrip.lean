import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT IsNormEnd zCast)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt.TwoLifts

section General
variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

omit [IsCommMonObj A] in

theorem normEnd_iff (N : ℕ)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])) :
    IsNormEnd A L (mulA A N) ((N : ℤ) ^ 2) 1 α₀ ↔ IsNormMul A L.L L.rig N α₀ := by
  have h : rigPow A L.L L.rig (-1) = LB.invGen L.L (fun _ : PUnit => eSec A) (fun _ => 1) L.rig := by
    unfold rigPow LB.invGen
    congr 1
    funext j
    exact zpow_neg_one _
  unfold IsNormEnd IsNormMul
  rw [h]

theorem normPull_iff (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T))
    (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) :
    IsNormPull A L (mulA A N) ((N : ℤ) ^ 2) 1 s s₁ ↔
    ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
      (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1])),
      α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧
      LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
      IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ := by
  have e : snd T A ≫ mulA A N = snd T A ^ N := by rw [MonObj.comp_pow, Category.comp_id]
  unfold IsNormPull mulT endT
  simp only [normEnd_iff]
  generalize snd T A ^ N = m at e ⊢
  subst e
  rfl

theorem uu_iff (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (x₁ x₂ : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (k : ℤ) (h : (N : ℤ) ^ 2 = k) :
    IsUUOver A L N s x₁ x₂ F ↔ ∃ F₀ F₁ : LB.Sec (LPow A L.L k T), IsNormPull A L (mulA A N) k 1 s F₀ ∧
      (∃ U : ThetaGrp A L.L k T, SymLift A L.L k (N ^ 2) x₁ U ∧ IsActOf A L.L k U F₀ F₁) ∧
      ∃ U : ThetaGrp A L.L k T, SymLift A L.L k (N ^ 2) x₂ U ∧ IsActOf A L.L k U F₁ (zCast A h F) := by
  subst h
  simp only [normPull_iff]
  exact ⟨fun ⟨α₀, α, s₁, s₂, U₁, U₂, a1, a2, a3, a4, a5, a6, a7, a8⟩ =>
      ⟨s₁, s₂, ⟨α₀, α, a1, a2, a3, a4⟩, ⟨U₁, a5, a6⟩, U₂, a7, a8⟩,
    fun ⟨s₁, s₂, ⟨α₀, α, a1, a2, a3, a4⟩, ⟨U₁, a5, a6⟩, U₂, a7, a8⟩ =>
      ⟨α₀, α, s₁, s₂, U₁, U₂, a1, a2, a3, a4, a5, a6, a7, a8⟩⟩

theorem triv_cast {T : Over X} (n : ℕ) {k k' : ℤ} (h : k = k')
    (hk : ∀ F : LB.Sec (LPow A L.L k T), ∃ U : ThetaGrp A L.L k T, SymLift A L.L k n 1 U ∧ IsActOf A L.L k U F F)
    (F : LB.Sec (LPow A L.L k' T)) : ∃ U : ThetaGrp A L.L k' T, SymLift A L.L k' n 1 U ∧ IsActOf A L.L k' U F F := by
  subst h
  exact hk F

end General

theorem act_natCast_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (n : ℕ) : t.act.act (n : 𝓞 E) = mulA t.G n := by
  induction n with
  | zero =>
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h1 : t.act.act 0 = 1 := by simpa using h
    simp [h1]
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, mulA, mulA, pow_succ]

end GlobalTheory.PlaceInt.TwoLifts

namespace GlobalTheory.PlaceInt
open TwoLifts

theorem uu_through_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (N : ℕ), Odd N → ∀ (s : SecN Xo x 1), (∀ (x₁ x₂ : (ptO Xo x ⟶ Xo.univ.t.G)) (F), x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → (IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F ↔ ∃ F₀ F₁ : SecN Xo x (N ^ 2), Pulls Xo (N : 𝓞 E) s F₀ ∧ Moves Xo x₁ F₀ F₁ ∧ Moves Xo x₂ F₁ (sqN Xo N F))) ∧ ∀ (ok : (ptO Xo x ⟶ Xo.univ.t.G) → Prop) (t : (ptO Xo x ⟶ Xo.univ.t.G)) (F), t ^ N = 1 → IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F → ∃ t' : (ptO Xo x ⟶ Xo.univ.t.G), t' ^ N = t ∧ ok t' ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N s 1 t' F := by
  intro E _ _ _ H Dw l Xo S _ x N hN s
  refine ⟨fun x₁ x₂ F h₁ h₂ => ?_, fun ok t F _ hV => ?_⟩
  · rw [uu_iff _ _ N s x₁ x₂ F ((N ^ 2 : ℕ) : ℤ) (Nat.cast_pow N 2).symm]
    unfold Pulls Moves IsSymAct sqN
    rw [act_natCast_eq]
    exact ⟨fun ⟨F₀, F₁, a, b, c⟩ => ⟨F₀, F₁, a, ⟨h₁, b⟩, h₂, c⟩,
      fun ⟨F₀, F₁, a, ⟨_, b⟩, _, c⟩ => ⟨F₀, F₁, a, b, c⟩⟩
  · obtain ⟨t', α₀, α, s₁, U, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hV
    obtain ⟨U₁, b1, b2⟩ := triv_cast Xo.univ.t.G Xo.univ.t.PP (N ^ 2) (Nat.cast_pow N 2)
      (fun G => (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN.pow 1 (one_pow _) G).2.2) s₁
    exact ⟨t', a1, a2, α₀, α, s₁, s₁, U₁, U, a3, a4, a5, a6, b1, b2, a7, a8⟩

end GlobalTheory.PlaceInt
