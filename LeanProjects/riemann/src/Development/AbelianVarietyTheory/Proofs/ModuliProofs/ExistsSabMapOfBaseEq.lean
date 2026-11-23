import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

theorem zeta_eq_pow_div_of_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨c, rfl⟩ := h
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  have hc : 0 < c := Nat.pos_of_mul_pos_left hb
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c ha, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem levelField_le_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [zeta_eq_pow_div_of_dvd l₂.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) (by simp)) _

def baseOfFinerLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := IntermediateField.inclusion (levelField_le_of_dvd h) (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (IntermediateField.inclusion_injective (levelField_le_of_dvd h))

def levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l →+* KA l₂ :=
  (IntermediateField.inclusion (levelField_le_of_dvd h)).toRingHom

theorem coe_levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) (x : KA l) : ((levelFieldIncl h x : KA l₂) : ℂ) = (x : ℂ) :=
  IntermediateField.coe_inclusion (levelField_le_of_dvd h) x

theorem coe_baseKA_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem levelFieldIncl_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : levelFieldIncl h (baseKA l).ρ = (baseOfFinerLevel h).ρ :=
  Subtype.ext ((coe_levelFieldIncl h _).trans ((coe_baseKA_rho l).trans (coe_baseKA_rho l₂).symm))

theorem levelFieldIncl_zeta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : levelFieldIncl h (baseKA l).ζ = (baseOfFinerLevel h).ζ := rfl

theorem baseOfFinerLevel_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ρ = (baseKA l₂).ρ := rfl

theorem baseOfFinerLevel_zeta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, ← levelFieldIncl_zeta, coe_levelFieldIncl]
  exact zeta_eq_pow_div_of_dvd l₂.A_pos h

theorem exists_sabMap_of_base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S} (n : SABMap t' t f) (h : f = g) :
    ∃ n' : SABMap t' t g, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

theorem exists_levelMap : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) := by
  intro hsm _ hlow hrep E _ _ _ H D l l₂ Xo Xo₂ _ hd
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o, m₁, h₁, h₁A⟩ := hlow E H D l l₂ (KA l₂) (baseOfFinerLevel hA) (baseKA l₂) Xo₂.X Xo₂.s Xo₂.univ hd
    (baseOfFinerLevel_rho hA) (baseOfFinerLevel_zeta hA)
  have hred : IsReduced Xo₂.X := by
    have := Xo₂.smooth
    exact (hsm _ _ Xo₂.s (SmoothOfRelativeDimension.smooth D.dim Xo₂.s)).1
  obtain ⟨r, ⟨hr, ⟨m₂⟩⟩, -⟩ := hrep E H D l Xo (KA l₂) (baseOfFinerLevel hA) (levelFieldIncl hA) Xo₂.X Xo₂.s o hred
    (levelFieldIncl_rho hA) (levelFieldIncl_zeta hA)
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₂.toSABMap m₁
  obtain ⟨n, hn⟩ := exists_sabMap_of_base_eq m (Category.id_comp r)
  have hφ : n.φ = m₁.φ ≫ m₂.toSABMap.φ := hn.trans hm
  refine ⟨r, levelFieldIncl hA, n, coe_levelFieldIncl hA, hr, fun a => ?_, fun a => ?_⟩
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁ a).trans (Category.id_comp _))).trans (m₂.eta a)))
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁A a).trans (Category.id_comp _))).trans (m₂.etaA a)))

end GlobalTheory
