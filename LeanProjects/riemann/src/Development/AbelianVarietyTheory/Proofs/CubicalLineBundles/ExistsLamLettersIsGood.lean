import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueHomOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieCombAddPowMap
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_lieComb_image {R R' : Type} [CommRing R] [CommRing R'] (A B : Out.PolAV (Sp R)) (x y : KeyIn R')
    (f : Sp R' ⟶ Sp R) (φ : x.P.A.left ⟶ A.A.left) (ψ : y.P.A.left ⟶ B.A.left)
    (hx : IsFibreOf A x f φ) (hy : IsFibreOf B y f ψ) (F : A.A ⟶ B.A) (hF : IsMonHom F) (i : Fin x.P.g) :
    ∃ (u : Fin y.P.g → R') (w : epsR R' ⟶ y.P.A), w.left ≫ ψ = (x.v i).left ≫ φ ≫ F.left ∧ IsLieComb u y.v w := by
  obtain ⟨⟨F', hF', -⟩, hmon⟩ := existsUnique_hom_of_isGrpPullback _ _ f A.A B.A x.P.A y.P.A φ ψ hx.1 hy.1 F
  have hm : IsMonHom F' := hmon F' hF' hF
  have ht : IsTangent (x.v i ≫ F') :=
    ((GlobalTheory.LieCombHom.lieComb_add_pow_map R' x.P.A y.P.A x.P.g x.v x.basis.1).2.2.2 F' hm).1 i
  obtain ⟨u, hu, -⟩ := y.basis.2 _ ht
  exact ⟨u, x.v i ≫ F', by rw [Over.comp_left, Category.assoc, hF'], hu⟩

def blockEquiv {T : Type} (p : T → Prop) [DecidablePred p] (a b : ℕ) {α β : Type} (s : α ≃ {t // p t})
    (s' : β ≃ {t // ¬ p t}) : (Σ t, Fin (if p t then a else b)) ≃ (Fin a × α) ⊕ (Fin b × β) where
  toFun z := if h : p z.1 then Sum.inl (z.2.cast (if_pos h), s.symm ⟨z.1, h⟩)
    else Sum.inr (z.2.cast (if_neg h), s'.symm ⟨z.1, h⟩)
  invFun
    | Sum.inl q => ⟨(s q.2).1, q.1.cast (if_pos (s q.2).2).symm⟩
    | Sum.inr q => ⟨(s' q.2).1, q.1.cast (if_neg (s' q.2).2).symm⟩
  left_inv := by
    rintro ⟨t, i⟩
    by_cases h : p t
    · simp only [dif_pos h]
      refine Sigma.ext (by simp) ?_
      exact (Fin.heq_ext_iff (by simp)).2 rfl
    · simp only [dif_neg h]
      refine Sigma.ext (by simp) ?_
      exact (Fin.heq_ext_iff (by simp)).2 rfl
  right_inv := by
    rintro (q | q)
    · simp [dif_pos (s q.2).2]
    · simp [dif_neg (s' q.2).2]

theorem exists_lamLetters_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∃ L : LamLetters o, L.IsGood ∧ ∀ b : E →+* ℂ, (b (H.rt : E) = H.rt0 → L.m b = nΨ) ∧ (b (H.rt : E) ≠ H.rt0 → L.m b = n') := by
  intro E _ _ _ _ H l c nΨ n' f o La hg
  classical
  obtain ⟨-, -, -, hB, hΨ, h', g1, g2, g3, -, -, -, -, ⟨m1, m2, -⟩, -⟩ := hg
  let p : (E →+* ℂ) → Prop := fun b => b (H.rt : E) = H.rt0
  let ε := blockEquiv p nΨ n' o.τΨ o.τ'
  have hc : Fintype.card ((Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g)) = o.xB.P.g := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [g1, g2, g3]; ring
  let κ := Fintype.equivFinOfCardEq hc
  have hU : ∀ q : (Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g),
      ∃ (u : Fin o.xB.P.g → o.K₁) (w : epsR o.K₁ ⟶ o.xB.P.A),
        (match q with
          | Sum.inl q => w.left ≫ o.φB = (o.xΨ.v q.2).left ≫ o.φΨg ≫ (o.φΨ q.1).left
          | Sum.inr q => w.left ≫ o.φB = (o.x'.v q.2).left ≫ o.φ'g ≫ (o.φ' q.1).left) ∧ IsLieComb u o.xB.v w := by
    rintro (q | q)
    · exact exists_lieComb_image _ _ _ _ _ _ _ hΨ hB _ (m1 q.1) q.2
    · exact exists_lieComb_image _ _ _ _ _ _ _ h' hB _ (m2 q.1) q.2
  choose u w hw hu using hU
  refine ⟨⟨fun b => if p b then nΨ else n', ε.trans κ, κ.symm, fun k => u (κ.symm k),
    fun k => Sum.elim (fun q => o.ℓΨ q.2) (fun q => o.ℓ' q.2) (κ.symm k)⟩, ⟨κ.symm.bijective, ?_, ?_, ?_⟩, ?_⟩
  · intro b i
    have : κ.symm ((ε.trans κ) ⟨b, i⟩) = ε ⟨b, i⟩ := by simp
    simp only [this]
    by_cases h : p b
    · have e1 : ε ⟨b, i⟩ = Sum.inl (i.cast (if_pos h), o.τΨ.symm ⟨b, h⟩) := dif_pos h
      rw [e1]; simp
    · have e1 : ε ⟨b, i⟩ = Sum.inr (i.cast (if_neg h), o.τ'.symm ⟨b, h⟩) := dif_neg h
      rw [e1]; simp
  · intro k
    refine ⟨w (κ.symm k), ?_, hu _⟩
    have := hw (κ.symm k)
    unfold LamLetters.IsLetter
    dsimp only
    generalize κ.symm k = q at this ⊢
    cases q <;> exact this
  · intro k
    dsimp only
    generalize κ.symm k = q
    cases q <;> rfl
  · intro b
    exact ⟨fun h => if_pos h, fun h => if_neg h⟩

end GlobalTheory.LamF
