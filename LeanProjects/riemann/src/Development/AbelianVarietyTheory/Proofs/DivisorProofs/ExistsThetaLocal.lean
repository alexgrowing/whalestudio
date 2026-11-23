import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_theta_local {S : Scheme.{0}} (G : Over S) [GrpObj G] (hA : IsAbelianScheme G)
    (L : LB G.left) (hL : L.IsLB) (U : Type) [CommRing U] [IsLocalRing U] (u : Sp U ⟶ S) (n : ℕ)
    (x : Over.mk u ⟶ G) (hx : x ^ n = 1) : ∃ θ : ThetaGrp G L (n : ℤ) (Over.mk u), θ.pt = x := by
  have := hA.comm
  set a : Over.mk u ⊗ G ⟶ G := fst (Over.mk u) G ≫ x with ha
  set y : Over.mk u ⊗ G ⟶ G := snd (Over.mk u) G with hy
  have cube := GlobalTheory.CubeTop.cubeTheorem S G hA L hL (Over.mk u ⊗ G)
  have key : ∀ m : ℕ, ∃ t : LB.Gen (LB.LinComb L
      ![(a ^ m * y).left, (a ^ m).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left]
      ![1, -1, -(m : ℤ), (m : ℤ), (m : ℤ) - 1, 1 - (m : ℤ)]), t.IsGen := by
    intro m
    induction m with
    | zero =>
      obtain ⟨t, ht⟩ := cube 1 a y
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ 0 * y).left, (a ^ 0).left, (a * y).left, a.left, y.left, (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ) - 1, 1 - ((0 : ℕ) : ℤ)]) (fun V _ g => by
          simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
            Matrix.cons_val_one, pow_zero, _root_.one_mul]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module) t ht
      exact ⟨t', ht'⟩
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨c, hc⟩ := cube (a ^ m) a y
      have e₁ : a ^ m * a * y = a ^ (m + 1) * y := by rw [pow_succ]
      have e₂ : a ^ m * a = a ^ (m + 1) := by rw [pow_succ]
      obtain ⟨t', ht', -⟩ := Geo.Tor.exists_gen hL (K' := Fin 6)
        (φ' := ![(a ^ (m + 1) * y).left, (a ^ (m + 1)).left, (a * y).left, a.left, y.left,
          (1 : Over.mk u ⊗ G ⟶ G).left])
        (ε' := ![1, -1, -((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ) - 1, 1 - ((m + 1 : ℕ) : ℤ)])
        (fun V _ g => by
          rw [Fintype.prod_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
            Matrix.cons_val_succ, Matrix.cons_val_one, e₁, e₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_zpow, ofMul_one]
          push_cast
          module)
        (LB.mulGen L _ _ _ _ t c) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hc)
      exact ⟨t', ht'⟩
  obtain ⟨t, ht⟩ := key n
  have han : a ^ n = 1 := by rw [ha, ← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := U) L hL (K := Fin 2)
    ![x.left, (1 : Over.mk u ⟶ G).left] ![-(n : ℤ), n]
  have h1 : (fst (Over.mk u) G).left ≫ (1 : Over.mk u ⟶ G).left = (1 : Over.mk u ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk u) G).left ≫ x.left = a.left := rfl
  have h3 : translPt G x = a * y := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen hL (K' := Fin 2)
    (φ' := ![(snd (Over.mk u) G).left, (translPt G x).left]) (ε' := ![(n : ℤ), -(n : ℤ)]) (fun V _ g => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, han, h1, h2, h3, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ e (fst (Over.mk u) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.WeilSpecialise

namespace GlobalTheory.WeilSpecialise

open ReciprocityTheory.ChartRestriction.G.Out

theorem unitOn_surjective {R : Type} [CommRing R] : Function.Surjective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective.2

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_specialise : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (Lb : LB G.left), Lb.IsLB → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ (P Q : Over.mk u ⟶ G) (c : Uˣ), P ^ n = 1 → Q ^ n = 1 → ∀ (P' Q' : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), P'.left = spMap (algebraMap U Ω) ≫ P.left → Q'.left = spMap (algebraMap U Ω) ≫ Q.left → Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → ∀ (k : Type) [Field k] (h : U →+* k) (P₀ Q₀ : Over.mk (spMap h ≫ u) ⟶ G), P₀.left = spMap h ≫ P.left → Q₀.left = spMap h ≫ Q.left → Out.WeilIs G Lb n P₀ Q₀ (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω _ _ _ _ _ _ S G _ hA Lb hLb u n _ P Q c hP hQ P' Q' hP' hQ' HΩ k _ h P₀ Q₀ hP₀ hQ₀
  have hG := globalFns_holds
  have loc : ∀ z : Over.mk u ⟶ G, z ^ n = 1 → ∀ p : (Over.mk u).left, ∃ V : (Over.mk u).left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp G Lb (n : ℤ) (overRes V), θ.pt = overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_local G hA Lb hLb U u n z hz
    obtain ⟨θ', h'⟩ := GlobalTheory.CommutatorPairing.exists_pull hLb θ (overResι (⊤ : (Over.mk u).left.Opens))
    exact ⟨⊤, trivial, θ', h'.trans (by rw [hθ])⟩
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.CommutatorPairing.exists_weilIs hG hA hLb (loc P hP) (loc Q hQ)
  obtain ⟨c₁, rfl⟩ := unitOn_surjective c₀
  let iΩ : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ Over.mk u := Over.homMk (spMap (algebraMap U Ω)) rfl
  have eP : P' = iΩ ≫ P := Over.OverMorphism.ext hP'
  have eQ : Q' = iΩ ≫ Q := Over.OverMorphism.ext hQ'
  have H₁ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb iΩ hc₀
  rw [← eP, ← eQ] at H₁
  have H₁' : Out.WeilIs G Lb n P' Q' (unitOn (Units.map (algebraMap U Ω).toMonoidHom c₁)) := by
    rw [← map_unitOn]; exact H₁
  have e := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hLb H₁' HΩ
  have e' := unitOn_inj e
  have hc : c₁ = c := Units.ext (IsFractionRing.injective U Ω (congrArg Units.val e'))
  subst hc
  let ik : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  have eP₀ : P₀ = ik ≫ P := Over.OverMorphism.ext hP₀
  have eQ₀ : Q₀ = ik ≫ Q := Over.OverMorphism.ext hQ₀
  have H₂ := GlobalTheory.CommPairing.weilIs_pull hG hA hLb ik hc₀
  rw [← eP₀, ← eQ₀] at H₂
  have := map_unitOn h c₁
  exact this ▸ H₂

end GlobalTheory.WeilSpecialise
