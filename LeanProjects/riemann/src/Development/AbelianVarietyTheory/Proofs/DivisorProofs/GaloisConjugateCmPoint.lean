import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotWeilIsGrpPullbackNoncomm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannFormStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjWeil

theorem unitOn_spMap (g : ℂ →+* ℂ) (c : ℂˣ) :
    Units.map (spMap g).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map g.toMonoidHom c) := by
  apply Units.ext
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
  exact (congrArg (fun q => q.hom (c : ℂ)) this).symm

theorem diag_lbIso {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S}
    {X' : Obj F 𝔠 S'} {b : S' ⟶ S} {p : X'.A.left ⟶ X.A.left} (hX : X'.IsPullBy X b p) (c : 𝔠.elt) :
    LBIso (X'.diag c) ((X.diag c).pull p) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact LBIso.trans (pull_isLB (X'.isLB c) _) (pull_isLB (X.isLB c) _) (pull_isLB (pull_isLB (X.isLB c) _) _) hI
    (GlobalTheory.GenSpread.lbIso_pull_pull (X.isLB c) p rfl)

theorem weil_transport : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (g : ℂ ≃+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
      X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
      ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
        (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
        ∀ (u₀ : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (Hm : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ) (χ : u₀.Λ → ℂ),
          u₀.ex = u'.ex → u₀.IsAH Hm χ →
          ∀ (k : ℕ) (w w' z z' : E), 0 < k → w ∈ lattice c y → w' ∈ lattice c y →
            z ∈ lattice c (y * (upIdele K E t)⁻¹) → z' ∈ lattice c (y * (upIdele K E t)⁻¹) →
            ((upIdele K E t : Af E) * algebraMap E (Af E) (z / k) - algebraMap E (Af E) (w / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            ((upIdele K E t : Af E) * algebraMap E (Af E) (z' / k) - algebraMap E (Af E) (w' / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            g (Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im : ℝ) : ℂ) / k)) =
              Complex.exp (-(2 * Real.pi * Complex.I) * ((((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im : ℝ) : ℂ) / k) := by
  intro _ _ _ K _ _ t E _ _ _ _ I _ φ g c y _ 𝔠 T X' p hp u' hlat hex u₀ Hm χ hex₀ hAH k w w' z z' hk hw hw' hz hz' hwz hwz'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hL : (T.X.diag T.U.c).IsLB := pull_isLB (T.X.isLB T.U.c) _
  have hL' : (X'.diag T.U.c).IsLB := pull_isLB (X'.isLB T.U.c) _

  obtain ⟨χX, hχX⟩ := T.U.ah
  have mem : ∀ v, v ∈ lattice c y → (fun j ↦ φ (T.U.e j) v) ∈ T.U.u.Λ := fun v hv ↦
    (T.U.lat _).2 ⟨v, hv, funext fun j ↦ by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have divk : ∀ v : E, (fun j ↦ φ (T.U.e j) (v / k)) = (k : ℂ)⁻¹ • fun j ↦ φ (T.U.e j) v := by
    intro v; funext j; simp [map_div₀, div_eq_inv_mul]
  set c₁ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) *
    ((((fun j ↦ φ (T.U.e j) w) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec
      (star fun j ↦ φ (T.U.e j) w')).im : ℝ) : ℂ) / k)) with hc₁
  have H1 := GlobalTheory.T.weil_pairing_torsion_points T.X.A T.X.ab _ hL _ T.U.u _ χX hχX k _ _ c₁ hk (mem w hw) (mem w' hw') rfl
  rw [← divk, ← divk] at H1

  let T₁ : Over (Sp ℂ) := Over.mk (𝟙 (Sp ℂ) ≫ spMap (g : ℂ →+* ℂ))
  let h : T₁ ⟶ 𝟙_ (Over (Sp ℂ)) := Over.homMk (spMap (g : ℂ →+* ℂ)) (by simp [T₁])
  have H2 := GlobalTheory.CommPairing.weilIs_pull globalFns_holds T.X.ab hL h H1
  rw [show h.left = spMap (g : ℂ →+* ℂ) from rfl, unitOn_spMap] at H2

  have H3 := (GlobalTheory.weilIs_baseChange_of_comm (Sp ℂ) (Sp ℂ) T.X.A X'.A (spMap (g : ℂ →+* ℂ)) p hp.grp _ _ hL hL'
    (diag_lbIso hp T.U.c) ℂ (𝟙 (Sp ℂ)) k (u'.ex (fun j ↦ g (φ (T.U.e j) (z / k))))
    (u'.ex (fun j ↦ g (φ (T.U.e j) (z' / k)))) _ _ _ (hex _ _ hwz).symm (hex _ _ hwz').symm).2 H2

  have memg : ∀ v, v ∈ lattice c (y * (upIdele K E t)⁻¹) → (fun j ↦ g (φ (T.U.e j) v)) ∈ u₀.Λ := by
    intro v hv
    rw [← u₀.ker, hex₀, u'.ker]
    exact (hlat _).2 ⟨v, hv, funext fun j ↦ by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have divg : ∀ v : E, (fun j ↦ g (φ (T.U.e j) (v / k))) = (k : ℂ)⁻¹ • fun j ↦ g (φ (T.U.e j) v) := by
    intro v; funext j; simp [map_div₀, div_eq_inv_mul]
  set c₂ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) *
    ((((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im : ℝ) : ℂ) / k)) with hc₂
  have H4 := GlobalTheory.T.weil_pairing_torsion_points X'.A X'.ab _ hL' _ u₀ Hm χ hAH k _ _ c₂ hk (memg z hz) (memg z' hz') rfl
  rw [hex₀, ← divg, ← divg] at H4
  have e := congrArg Units.val (GlobalTheory.weilIs_unique_fieldPoint (Sp ℂ) X'.A _ hL' ℂ (𝟙 (Sp ℂ)) k _ _ _ _ H4 H3)
  simp only [hc₁, hc₂, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe] at e
  have hs : ((fun j ↦ φ (T.U.e j) w) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec
      (star fun j ↦ φ (T.U.e j) w')).im = ∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def, Complex.im_sum]
    rw [← Equiv.sum_comp T.U.e]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [hs] at e
  exact e.symm

end GlobalTheory.ConjWeil
