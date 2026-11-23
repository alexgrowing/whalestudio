import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetRatio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {σ σ' : Rule t π p q}

theorem sec_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) (a : ∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left)
    (b : ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left) : σ R' x' v' w' = g (σ R x v w) :=
  hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v' w'
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h' hx a b

theorem ratio_frame (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') {j : c.F →+* R} {x : Sp R ⟶ X} {v w v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w') {a : R}
    (e : σ' R x v w = a * σ R x v w) : σ' R x v' w' = a * σ R x v' w' := by
  have h₁ : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w := ⟨h.1, h.2.1, h'.2.2.1, h.2.2.2⟩
  choose M hM using fun i => (h.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  have ow : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin q) (Fin q) R) i) w (w i) :=
    fun i => DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have ov : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin p) (Fin p) R) i) v' (v' i) :=
    fun i => DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
  have e1 := hσ.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e1' := hσ'.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e2 := hσ.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  have e2' := hσ'.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  rw [Matrix.det_one, _root_.one_mul] at e1 e1' e2 e2'
  have hu : IsUnit (Matrix.of M).det := isUnit_of_mul_isUnit_left (e1 ▸ hn R j x v w h)
  have e3 : σ' R x v' w = a * σ R x v' w := by
    refine hu.mul_left_cancel ?_
    rw [← e1', e, e1]; ring
  rw [← e2', ← e2, e3]; ring

theorem ratio_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) {a : R} (e : σ' R x v w = a * σ R x v w) :
    σ' R' x' v' w' = g a * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h hx
  obtain rfl := (exists_chg g h h' hx).1
  refine ratio_frame hσ hn hσ' h₁ h' ?_
  rw [sec_pull hσ g h h₁ hx a₁ b₁, sec_pull hσ' g h h₁ hx a₁ b₁, e, map_mul]

theorem exists_ratio_affine (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ)
    (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ) (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ')
    {W : X.Opens} (hW : IsAffineOpen W) {j₀ : c.F →+* Γ(X, W)} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v₀ w₀) :
    ∃ f : Γ(X, W), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, ⊤ ≤ x ⁻¹ᵁ W →
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x W f * σ R x v w := by
  obtain ⟨u, hu⟩ := hn _ j₀ _ v₀ w₀ h₀
  refine ⟨σ' _ _ v₀ w₀ * u.inv, fun R _ j x v w hx h => ?_⟩
  rw [Points.valR_eq x W hx]
  refine ratio_pull hσ hn hσ' (Points.valMap x W hx).hom h₀ h (Points.specMap_valMap_fromSpec hW x hx).symm ?_
  rw [← hu, _root_.mul_assoc, u.inv_val, _root_.mul_one]

theorem valR_fromSpec {A : X.Opens} (hA : IsAffineOpen A) (f : Γ(X, A)) :
    valR (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A f = f := by
  have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
  rw [Points.valR_eq _ A hx]
  have : Points.valMap (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A hx = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono hA.fromSpec, Points.specMap_valMap_fromSpec]
    exact ((congrArg (· ≫ hA.fromSpec) (Spec.map_id _)).trans (Category.id_comp _)).symm
  rw [this]
  rfl

end GlobalTheory.DetRatio

open GlobalTheory.DetRatio in

theorem GlobalTheory.detLine_exists_ratio (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ)
    (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q) (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q)
    (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') :
    ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  choose W hW j₀ v₀ w₀ hz h₀ using fun z : V => hc z z.2
  choose f hf using fun z : V => exists_ratio_affine hσ hn hσ' (hW z) (h₀ z)
  have hle : ∀ z, W z ≤ V := fun z y hy => (h₀ z).2.1 (by
    change y ∈ Set.range (hW z).fromSpec
    rw [(hW z).range_fromSpec]; exact hy)
  have hcov : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hz _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf W f := by
    intro a b
    refine X.sheaf.eq_of_locally_eq' (fun A : {A : X.affineOpens // A.1 ≤ W a ⊓ W b} => A.1.1) (W a ⊓ W b)
      (fun A => homOfLE A.2) (fun y hy => ?_) _ _ fun A => ?_
    · obtain ⟨_, ⟨A, hA, rfl⟩, hy', hA'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy (W a ⊓ W b).2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨A, hA⟩, hA'⟩, hy'⟩
    · obtain ⟨⟨A, hA⟩, hAle⟩ := A
      replace hA : IsAffineOpen A := hA
      have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
      have hxa := Points.le_preimage_mono _ (hAle.trans inf_le_left) hx
      have hxb := Points.le_preimage_mono _ (hAle.trans inf_le_right) hx
      have hxab := Points.le_preimage_mono _ hAle hx
      obtain ⟨v, w, h, -, -⟩ := exists_pull (Points.valMap _ (W a) hxa).hom (h₀ a)
        (Points.specMap_valMap_fromSpec (hW a) _ hxa).symm
      have e := (hn _ _ _ v w h).mul_right_cancel ((hf a _ _ _ v w hxa h).symm.trans (hf b _ _ _ v w hxb h))
      refine (valR_fromSpec hA _).symm.trans (Eq.trans ?_ (valR_fromSpec hA _))
      refine (Points.valR_res _ hAle hx _).trans (Eq.trans ?_ (Points.valR_res _ hAle hx _).symm)
      exact (Points.valR_res _ inf_le_left hxab _).trans (e.trans (Points.valR_res _ inf_le_right hxab _).symm)
  obtain ⟨F, hF, -⟩ := X.sheaf.existsUnique_gluing' W V (fun z => homOfLE (hle z)) hcov f hcomp
  refine ⟨F, fun R _ j x v w h => ?_⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := fun y _ => h.2.1 ⟨y, rfl⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_localization _ fun J hJ => ?_
  let g := algebraMap R (Localization.AtPrime J)
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h rfl
  let z : V := ⟨(spMap g ≫ x) (IsLocalRing.closedPoint (Localization.AtPrime J)), h₁.2.1 ⟨_, rfl⟩⟩
  have hxW : ⊤ ≤ (spMap g ≫ x) ⁻¹ᵁ W z := (Points.le_preimage_iff _ _).2 (hz z)
  have e := hf z _ _ _ v₁ w₁ hxW h₁
  rw [sec_pull hσ g h h₁ rfl a₁ b₁, sec_pull hσ' g h h₁ rfl a₁ b₁, ← hF z] at e
  have e' := (Points.valR_res _ (hle z) hxW F).trans (Points.valR_spMap_comp g x V hxV F)
  change g _ = 0
  rw [map_sub, map_mul, ← e', sub_eq_zero]
  exact e
