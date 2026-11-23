import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinateSumDifferenceAdditionFactor
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecFinsum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RepSymInv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddCoeff
open ReciprocityTheory.ChartRestriction.G.DVR

theorem sum_diff_inj {X : Type} [AddCommGroup X] [Module.Free ℤ X] {a b a' b' : X} (h₁ : a + b = a' + b')
    (h₂ : a - b = a' - b') : a = a' ∧ b = b' := by
  have e : (2 : ℤ) • a = (2 : ℤ) • a' := by
    rw [two_smul, two_smul]
    calc a + a = (a + b) + (a - b) := by abel
      _ = a' + a' := by rw [h₁, h₂]; abel
  have ha : a = a' := smul_right_injective X two_ne_zero e
  subst ha
  exact ⟨rfl, add_left_cancel h₁⟩

theorem reindex {X R : Type} [AddCommGroup X] [Module.Free ℤ X] [CommRing R] (s₀ s : Finset X)
    (hs : ∀ a ∈ s₀, ∀ b ∈ s₀, a + b ∈ s ∧ a - b ∈ s) (F g c : X → X → R)
    (hF : ∀ a b, a ∉ s₀ ∨ b ∉ s₀ → F a b = 0) (g₁ : ∀ a b, g (a + b) (a - b) = F a b)
    (g₀ : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → g α β = 0) :
    ∑ α ∈ s, ∑ β ∈ s, g α β * c α β = ∑ a ∈ s₀, ∑ b ∈ s₀, F a b * c (a + b) (a - b) := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_product']
  symm
  refine Finset.sum_of_injOn (fun p : X × X => (p.1 + p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
  · intro p _ q _ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (sum_diff_inj h₁ h₂).1 (sum_diff_inj h₁ h₂).2
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
    exact Finset.mem_product.2 (hs _ h₁ _ h₂)
  · rintro ⟨α, β⟩ _ hp
    by_cases h : ∃ a b, α = a + b ∧ β = a - b
    · obtain ⟨a, b, rfl, rfl⟩ := h
      have : a ∉ s₀ ∨ b ∉ s₀ := by
        by_contra hc
        push Not at hc
        exact hp ⟨(a, b), Finset.mem_coe.2 (Finset.mem_product.2 hc), rfl⟩
      simp only [g₁, hF a b this, zero_mul]
    · simp only [g₀ α β h, zero_mul]
  · intro p _
    simp only [g₁]

section
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_zero_of (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_sub_scale (s t : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval s r z J - gs r z ⊤ c * sval t r z J := by
  refine ⟨SecOps.secAdd s (SecOps.secNeg (SecOps.secScale c t)), fun Z r z J hJ => ?_⟩
  have hm := hJ.mem φ r
  have e : sval (SecOps.secScale c t) r z J = gs r z ⊤ c * sval t r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm c))
  have e' : ∀ u : LB.Sec (LB.LinComb L φ ε), sval (SecOps.secNeg u) r z J = - sval u r z J := fun u =>
    (gs_eq r z _ hm _).trans (((congrArg _ (map_neg _ _)).trans (map_neg _ _)).trans
      (congrArg Neg.neg (gs_eq r z _ hm _).symm))
  refine (gs_add r z _ hm _ _).trans ?_
  rw [sub_eq_add_neg, ← e, ← e']
  rfl
end

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → AddB D (𝟙_ _) f₀ r f f') := by
  classical
  intro hGF V _ _ _ hV D A G _ _ U θ f₀ r n σ σ' f f' hA hθ hσ
  have hlev := GlobalTheory.addition_formula_expanded_at_level hGF V hV D A G U θ f₀ r n σ σ' f f' hA hθ hσ
  have hbox := GlobalTheory.UU.BoxSec.main V D (𝟙_ _) (toUnit _)
  have hd : ∀ p : D.X × D.X, ∃ d : LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε 2) (DegPre.famε 2))),
      ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        (∀ a b, p.1 = a + b → p.2 = a - b → sval d (lift x y).left z J =
          ∑ i, sval (f i p.1) (lift (toUnit T) x).left z J * sval (f' i p.2) (lift (toUnit T) y).left z J -
          gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
            (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J)) ∧
        ((¬ ∃ a b, p.1 = a + b ∧ p.2 = a - b) → sval d (lift x y).left z J =
          ∑ i, sval (f i p.1) (lift (toUnit T) x).left z J * sval (f' i p.2) (lift (toUnit T) y).left z J) := by
    rintro ⟨α, β⟩
    obtain ⟨d₁, h₁⟩ := (hbox α β).1 n (fun i => f i α) (fun i => f' i β)
    simp only [comp_toUnit] at h₁
    by_cases h : ∃ a b, α = a + b ∧ β = a - b
    · obtain ⟨a, b, ha, hb⟩ := h
      obtain ⟨d₂, h₂⟩ := (hbox α β).2 a b (f₀ a) (f₀ b) ha hb
      simp only [comp_toUnit] at h₂
      obtain ⟨d, hd⟩ := exists_sub_scale d₁ d₂ (scal (D.P.A ⊗ D.P.A).hom r)
      refine ⟨d, fun T x y z J hJ => ⟨fun a' b' ha' hb' => ?_, fun h => absurd ⟨a, b, ha, hb⟩ h⟩⟩
      obtain ⟨rfl, rfl⟩ := sum_diff_inj (ha.symm.trans ha') (hb.symm.trans hb')
      rw [hd _ _ z J hJ, h₁ T x y z J hJ, h₂ T x y z J hJ, gs_scal, Over.w, _root_.mul_assoc]
    · exact ⟨d₁, fun T x y z J hJ => ⟨fun a b ha hb => absurd ⟨a, b, ha, hb⟩ h, fun _ => h₁ T x y z J hJ⟩⟩
  choose d hd using hd
  have h0 := GlobalTheory.WeightTwo.main V hV D A G U 2 2 d (fun e => by
    obtain ⟨s₀, H⟩ := hlev e
    refine ⟨s₀ ∪ Finset.image₂ (· + ·) s₀ s₀ ∪ Finset.image₂ (· - ·) s₀ s₀,
      fun s hs T x y xe ye hx hy hxy z J hJ => ?_⟩
    obtain ⟨H₁, H₂⟩ := H T x y xe ye hx hy hxy z J hJ
    have hs₀ : s₀ ⊆ s := (Finset.subset_union_left.trans Finset.subset_union_left).trans hs
    have R := reindex s₀ s (fun a ha b hb =>
        ⟨hs (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image₂_of_mem ha hb))),
          hs (Finset.mem_union_right _ (Finset.mem_image₂_of_mem ha hb))⟩)
      (fun a b => gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
        (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J))
      (fun α β => ∑ i, sval (f i α) (lift (toUnit T) x).left z J * sval (f' i β) (lift (toUnit T) y).left z J -
        sval (d (α, β)) (lift x y).left z J)
      (fun α β => (val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val)
      (by
        rintro a b (h | h)
        · rw [(H₁ a h).1, zero_mul, mul_zero]
        · rw [(H₁ b h).2, mul_zero, mul_zero])
      (fun a b => by rw [(hd (a + b, a - b) T x y z J hJ).1 a b rfl rfl, sub_sub_cancel])
      (fun α β h => by rw [(hd (α, β) T x y z J hJ).2 h, sub_self])
    rw [← H₂ s hs₀] at R
    simp only [sub_mul, Finset.sum_sub_distrib] at R
    exact sub_eq_self.1 R)
  intro T ρ x y z J hJ
  obtain rfl : ρ = toUnit T := toUnit_unique _ _
  refine ⟨fun a b α β hα hβ => ?_, fun α β h => ?_⟩
  · exact sub_eq_zero.1 (((hd (α, β) T x y z J hJ).1 a b hα hβ).symm.trans (sval_zero_of _ (h0 _) _ z hJ))
  · exact ((hd (α, β) T x y z J hJ).2 h).symm.trans (sval_zero_of _ (h0 _) _ z hJ)

end GlobalTheory.AddCoeff
