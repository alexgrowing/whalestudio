import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem eq_zero_of_cst_eq_zero {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} (p : X ⟶ Sp S) [Flat p] (x : X)
    (hx : p x = IsLocalRing.closedPoint S) {a : S} (ha : cst p x a = 0) : a = 0 := by
  let φ : S →+* X.presheaf.stalk x := (p.stalkMap x).hom.comp
    (((Sp S).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
  have hφ : ∀ c, φ c = cst p x c := fun c => by
    rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  have fl : φ.Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)) ?_) (Flat.stalkMap p x)
    have hU := isAffineOpen_top (Sp S)
    let _ := (Sp S).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
    have := hU.isLocalization_stalk ⟨p x, trivial⟩
    exact IsLocalization.flat ((Sp S).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp S).Opens)) : Sp S))
      (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl
  let _ := φ.toAlgebra
  have : Module.Flat S (X.presheaf.stalk x) := fl
  have : IsLocalHom (algebraMap S (X.presheaf.stalk x)) := ⟨fun c hc => by
    by_contra h
    exact cst_not_isUnit p x hx h (hφ c ▸ hc)⟩
  have : Module.FaithfullyFlat S (X.presheaf.stalk x) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective S (X.presheaf.stalk x) ((hφ a).trans (ha.trans (map_zero _).symm))

theorem coef_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  intro R _ _ _ I hI D A G _ _ U σ f th hE hth e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun χ hχ u b hb => ?_⟩
  have hI' : I ^ (e + 1) ≠ ⊤ := fun h => hI (top_unique (h ▸ Ideal.pow_le_self e.succ_ne_zero))
  haveI : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  haveI : IsLocalRing (R ⧸ I ^ (e + 1)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk (I ^ (e + 1))) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcl : thick R I e (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (I ^ (e + 1)))
  haveI := U.semi.smooth
  haveI : Flat (thickObj R I e G).hom := inferInstanceAs (Flat (pullback.snd G.hom (thick R I e)))
  obtain ⟨z₀, hz₀, hnz⟩ := hth (IsLocalRing.closedPoint R)
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let y : T ⟶ D.P.A := (U.gt e).pG
  let m : 𝟙_ _ ⊗ D.P.A ⟶ D.P.A := snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹
  let τ : D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (toUnit _) (𝟙 _ * cT D _ χ)
  have hc : ∀ {T₁ T₂ : Over (Spec (CommRingCat.of R))} (g : T₁ ⟶ T₂), g ≫ cT D _ χ = cT D _ χ := fun g => by
    rw [cT, ← Category.assoc, toUnit_unique (g ≫ toUnit _) (toUnit _)]
  have hmτ : m ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, inv_mul_cancel_right, Category.id_comp]
  have hyτ : y ≫ τ = lift (toUnit T) (y * cT D T χ) := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, lift_snd]
  have h1 : D.P.A.hom (m.left z₀) = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, Over.w m]; exact hz₀
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.P.A.hom) (g := thick R I e)
    (m.left z₀) (IsLocalRing.closedPoint (R ⧸ I ^ (e + 1))) (h1.trans hcl.symm)
  obtain ⟨z, rfl⟩ := (U.gt e).q_surj.1 w
  have hy : y.left z = m.left z₀ := hw
  have hz : (thickObj R I e G).hom z = IsLocalRing.closedPoint _ := by
    rw [← Over.w (U.gt e).q, Scheme.Hom.comp_apply]; exact hw'
  have h2 : (lift (toUnit T) (y * cT D T χ)).left z = z₀ := by
    rw [← hyτ, Over.comp_left, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, ← Over.comp_left, hmτ]
    rfl
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  have hu := (MulPullSec.mem_nonzeroLocus_iff th (lift (toUnit T) (y * cT D T χ)).left z hJ).1 (h2 ▸ hnz)
  have h0 := (hs T.left (𝟙 _) (lift (toUnit T) (fstG I e G)).left (lift (toUnit T) y).left
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z JG J hJG hJ).1 χ hχ
  have h3 := hb T y z J hJ
  rw [h0] at h3
  have h4 : cst T.hom z b = 0 := ((Units.isUnit _).mul hu).mul_left_eq_zero.1 h3.symm
  have h5 : cst (thickObj R I e G).hom z (Ideal.Quotient.mk _ b) = 0 :=
    (cst_comp (thickObj R I e G).hom (Ideal.Quotient.mk (I ^ (e + 1))) z b).symm.trans h4
  exact Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_cst_eq_zero _ z hz h5)

end GlobalTheory.PsiRing
