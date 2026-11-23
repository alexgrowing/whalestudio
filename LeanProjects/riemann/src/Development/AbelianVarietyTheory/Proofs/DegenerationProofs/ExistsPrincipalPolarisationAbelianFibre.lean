import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

theorem lbIso_of_refines {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K']
    [Fintype K''] {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') {ψ : K'' → (Y ⟶ X)} {δ : K'' → ℤ}
    (t : LB.Gen (LB.LinComb L ψ δ)) (ht : t.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (ψ k) ^ δ k) * ∏ k, f (φ k) ^ ε k = ∏ k, f (φ' k) ^ ε' k) : LBIso M M' := by
  refine (h'.div h).exists_gen hL (fun U _ f => ?_) t ht
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [← hF U f, mul_inv_cancel_right]

theorem refines_npw {X : Scheme.{0}} (L : LB X) (N : ℕ) :
    Refines (npw L N) L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ)) := by
  refine ⟨fun i _ => i, fun i y hy => Set.mem_iInter.2 fun _ => hy, fun Z r z i j _ _ => ?_⟩
  refine (map_pow _ _ _).trans (Eq.symm ((Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)))
  rw [Category.comp_id]
  rfl

theorem npw_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (N : ℕ) :
    LBIso (npw L N) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ))) :=
  lbIso_of_refines hL (refines_npw L N) (refines_self _ _) _ isGen_one fun U _ f => by
    rw [Fintype.prod_empty, _root_.one_mul]

theorem lbIso_drop {k : Type} [Field k] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ Sp k) (a b : Sp k ⟶ X)
    (u v : Y ⟶ X) (φ : Fin 4 → (Y ⟶ X)) (h₀ : φ 0 = u) (h₁ : φ 1 = p ≫ a) (h₂ : φ 2 = v) (h₃ : φ 3 = p ≫ b) :
    LBIso (LB.LinComb L φ Oε) (LB.LinComb L (K := Fin 2) ![u, v] ![1, -1]) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := k) L hL (K := Fin 2) ![a, b] ![1, -1]
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ (DVR.pullGen_isGen _ _ _ e he p) fun U _ f => ?_
  rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, h₀, h₁, h₂, h₃]
  change f (p ≫ a) ^ (1 : ℤ) * f (p ≫ b) ^ (-1 : ℤ) *
    (f u ^ (1 : ℤ) * f (p ≫ a) ^ (-1 : ℤ) * f v ^ (-1 : ℤ) * f (p ≫ b) ^ (1 : ℤ)) = f u ^ (1 : ℤ) * f v ^ (-1 : ℤ)
  simp only [zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_pol : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  rintro hB k _ Φ R _ _ D s π hπ xe hO N ⟨cp⟩
  obtain ⟨P', g, hg, hdim, hm, t, ht⟩ := hB _ _ s D.P
  have gp : IsGrpPullback P'.A D.P.A s g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨β, hβ, hβπ⟩ := grpPullback_iso hπ gp
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  have hL := D.P.isLB
  have hL' := P'.isLB
  have key : ∀ {K : Type} [Fintype K] (φ' : K → (Φ.E.B.left ⟶ P'.A.left)) (φ : K → (Φ.E.B.left ⟶ D.P.A.left))
      (ε : K → ℤ), (∀ a, φ a = φ' a ≫ g) → LBIso (LB.LinComb D.P.L φ ε) (LB.LinComb P'.L φ' ε) := by
    intro K _ φ' φ ε h
    obtain rfl : φ = fun a => φ' a ≫ g := funext h
    exact (iso_linComb ((isGen_iff w).1 hw) φ' ε).symm
  have hc : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, (s ≫ x.left) ≫ D.P.A.hom = 𝟙 _ ≫ s := fun x => by
    rw [Category.assoc, Over.w x, Category.id_comp]
    exact Category.comp_id _
  let c : Φ.E.X → (baseOver (Sp k) ⟶ P'.A) := fun χ =>
    Over.homMk (hg.lift (s ≫ (D.c (xe χ)).left) (𝟙 _) (hc _)) (hg.lift_snd _ _ _)
  have hcg : ∀ χ, (c χ).left ≫ g = s ≫ (D.c (xe χ)).left := fun χ => hg.lift_fst _ _ _
  have hu : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, π ≫ (toUnit D.P.A ≫ x).left = Φ.E.B.hom ≫ s ≫ x.left := fun x => by
    rw [← Category.assoc, ← hπ.1.w, Category.assoc]
    rfl
  refine ⟨⟨P', β, hβ, c, ?_, fun χ => ?_⟩, hdim⟩
  · have h₁ : LBIso Φ.N₀ (LB.LinComb D.P.L (K := PUnit) (fun _ => π) (fun _ => (N : ℤ))) :=
      LBIso.chartPull cp (chartPullSame _ _ _ _ π fun _ => (Category.comp_id _).symm) (npw_iso hL N)
    have h₂ := key (K := PUnit) (fun _ => β.hom.left) (fun _ => π) (fun _ => (N : ℤ)) fun _ => hβπ.symm
    have h₃ : LBIso (LB.LinComb P'.L (K := PUnit) (fun _ => β.hom.left) (fun _ => (N : ℤ)))
        ((lbPow P'.L N).pull β.hom.left) :=
      LBIso.chartPull (chartPullId _) (chartPullOut P'.L _ _ β.hom.left _ fun _ => (Category.comp_id _).symm)
        (exists_iso hL' rfl _)
    exact LBIso.trans Φ.isLB (DVR.linComb_isLB _ hL _ _) (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₁
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
        (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₂ h₃)
  · let q : Φ.E.B ⟶ baseOver (Sp k) := Over.homMk Φ.E.B.hom (Category.comp_id _)
    have e₀ : π ≫ D.Oφ (𝟙 D.P.A) (xe χ) 0 = (β.hom * (q ≫ c χ)).left ≫ g := by
      let ρ : Over.mk (Φ.E.B.hom ≫ s) ⟶ D.P.A := Over.homMk π hπ.1.w
      refine Eq.trans ?_ (gp.2 Φ.E.B β.hom (q ≫ c χ) (ρ ≫ 𝟙 _) (ρ ≫ toUnit _ ≫ D.c (xe χ))
        ((Category.comp_id _).trans hβπ.symm) ?_)
      · exact congrArg (fun f => f.left) (MonObj.comp_mul ρ (𝟙 _) (toUnit _ ≫ D.c (xe χ)))
      · refine (hu _).trans ?_
        rw [← hcg]
        exact (Category.assoc _ _ _).symm
    have h₁ := lbIso_drop hL Φ.E.B.hom (s ≫ (D.c (xe χ)).left) (s ≫ (η[D.P.A]).left) _ π
      (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) e₀ (hu _) (Category.comp_id _) (hu _)
    have h₂ := key (K := Fin 2) ![(β.hom * (q ≫ c χ)).left, β.hom.left] ![(β.hom * (q ≫ c χ)).left ≫ g, π] ![1, -1]
      (fun a => by
        fin_cases a
        · rfl
        · exact hβπ.symm)
    exact LBIso.trans (Φ.E.O χ).isLB (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) (hO χ)
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) h₁ h₂)

end GlobalTheory.ZH.UFib
end
