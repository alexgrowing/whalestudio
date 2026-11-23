import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelTheta

theorem series_eq_unit_mul_theta : Laws → TXSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (m : ℕ), Odd m → ∀ (p : D.La → QkPt M.P.D.toPre C (m ^ 2)) (q : D.La → N'.QT (m ^ 2)) (v : D.La → C), (∀ x (z : TFK (R := M.W) C ⟶ M.P.A.A), z.left = (o.I.ev (m ^ 2) x).left ≫ M.φ → M.P.ToA C (m ^ 2) (p x) z) → (∀ x, ν'.QPt (p x) (q x)) → o.Theta m v → (∃ c : Cˣ, ∀ x, N'.tx m (q x) = c * v x) ∧ (3 ≤ m → v ≠ 0) := by
  intro hL hTX E _ _ _ H D C _ _ _ _ _ o M N' ν' m hm p q v hpz hq hv
  let x : D.La → (TFK (R := M.W) C ⟶ M.P.A.A) := fun i =>
    Over.homMk ((o.I.ev (m ^ 2) i).left ≫ M.φ) (by
      rw [Category.assoc, M.cart.1.w, ← Category.assoc, Over.w]
      simp)
  have key := hTX M.W (IsLocalRing.maximalIdeal M.W) M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' m hm
    D.La p q x (fun i => hpz i (x i) rfl) hq
  have hm0 : (m : C) ≠ 0 := Nat.cast_ne_zero.mpr hm.pos.ne'
  have hmu : IsUnit ((m : ℕ) : Γ(Sp C, ⊤)) := by
    have h1 : ((m : ℕ) : Γ(Sp C, ⊤)) = fnOf (m : C) := (map_natCast _ m).symm
    rw [h1]
    exact (IsUnit.mk0 _ hm0).map _
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  have htors : ∀ i, o.I.ev (m ^ 2) i ^ (m ^ 2) = 1 := fun i => (o.I.onto (m ^ 2) hm2 _).2 ⟨i, rfl⟩
  have : Subsingleton (TFK (R := M.W) C).left := by
    change Subsingleton (PrimeSpectrum C)
    exact ⟨fun a b => PrimeSpectrum.ext (by
      have := a.isPrime
      have := b.isPrime
      rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])⟩
  have : Nonempty (TFK (R := M.W) C).left := by
    change Nonempty (PrimeSpectrum C)
    exact ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  have c1 := (GlobalTheory.CoordSep.isThetaPt_iff (T := TFK (R := M.W) C) hm hmu x _).1 key
  have hτ : 𝟙 (Sp C) ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := by simp
  have hβ : 𝟙 (Sp C) ≫ Over.Hom.left (𝟙 (TFK (R := M.W) C)) = 𝟙 (Sp C) := by simp
  have hx : ∀ i, 𝟙 (Sp C) ≫ (x i).left = (o.I.ev (m ^ 2) i).left ≫ M.φ := fun i => Category.id_comp _
  have hz := GlobalTheory.ThetaPtMove.over_one (T := baseOver (Sp C)) (T₀ := TFK (R := M.W) C) M.cart (𝟙 (Sp C)) hτ
  have hg : ∀ th₀, IsGenSec M.P.A.A M.P.A.L 1 th₀ →
      IsGenSec M.P.A.A M.P.A.L 1 (VVRank.pullS M.P.A.A 1 (𝟙 (TFK (R := M.W) C)) th₀) :=
    fun th h => GlobalTheory.ThetaCoord.isGenSec_pullS M.P.A.isLB (𝟙 _) (𝟙 _) (by simp) h
  have hσ : IsIso (𝟙 (Sp C) : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left) := IsIso.id (Sp C)
  have c2 := GlobalTheory.FullExtend.isCoordPt_move (S := Sp (FractionRing M.W)) (S' := Sp C) (f := jFK (R := M.W) C)
    (T := baseOver (Sp C)) (T₀ := TFK (R := M.W) C) (𝟙 (Sp C)) (P₀ := M.P.A) (P := o.P) (φ := M.φ) M.cart M.lb
    (B := TFK (R := M.W) C) (𝟙 (Sp C)) (𝟙 _) hβ hτ hg (k := m) (I := D.La) (x := o.I.ev (m ^ 2)) (x₀ := x) hx htors
    (z := 1) (z₀ := 1) hz (v₀ := fun i => fnOf (N'.tx m (q i))) c1
  have e1 : ∀ y : Γ(Sp C, ⊤), (𝟙 (Sp C) : Sp C ⟶ Sp C).appTop.hom y = y := fun y => by simp
  simp only [e1] at c2
  obtain ⟨-, huniq, hthc, hsep⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate hL C (Sp C) o.P (𝟙 (Sp C)) m hm hm0
    D.La (o.I.ev (m ^ 2)) htors
  have hv1 : IsCoordPt o.P m (o.I.ev (m ^ 2)) 1 (fun i => fnOf (v i)) := (hthc v).1 hv
  obtain ⟨c, hc⟩ := (huniq 1 v (fun i => N'.tx m (q i)) hv1).1 c2
  refine ⟨⟨c, fun i => ?_⟩, fun h3 => ?_⟩
  · have := congrFun hc i
    simpa using this
  · have hall : ∀ y : Over.mk (𝟙 (Sp C)) ⟶ o.P.A, y ^ m ^ 2 = 1 → ∃ i, o.I.ev (m ^ 2) i = y :=
      fun y hy => (o.I.onto (m ^ 2) hm2 y).1 hy
    exact (hsep h3 hall 1 1 v hv1 hv1).2

end GlobalTheory.ModelTheta
