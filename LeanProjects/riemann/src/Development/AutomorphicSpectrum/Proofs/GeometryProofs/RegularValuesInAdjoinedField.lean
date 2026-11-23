import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem valR_mem_adjoin_of_affine {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} (ξ : Sp Ω ⟶ X)
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ξ W₀ h₀).hom = A) {O : X.Opens} (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (t : Γ(X, O)) :
    valR ξ O t ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  have hmem : ∀ a : Γ(X, W₀), valR ξ W₀ a ∈ IntermediateField.adjoin ℚ (A : Set Ω) := fun a => by
    apply IntermediateField.subset_adjoin
    rw [valR_eq ξ W₀ h₀, ← hA]
    exact ⟨a, rfl⟩
  let z : Sp Ω := IsLocalRing.closedPoint Ω
  obtain ⟨b, hbO, hxb⟩ := hW₀.exists_basicOpen_le (V := O) ⟨ξ z, hO trivial⟩ (h₀ trivial)
  have hD : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen b := fun y _ => by
    rw [Subsingleton.elim y z]
    exact hxb
  have hloc := hW₀.isLocalization_basicOpen b
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers b)
    ((X.presheaf.map (homOfLE hbO).op).hom t)
  have hres : ∀ c : Γ(X, W₀), valR ξ (X.basicOpen b) (algebraMap Γ(X, W₀) Γ(X, X.basicOpen b) c) =
      valR ξ W₀ c := fun c => valR_res ξ (X.basicOpen_le b) hD c
  have hv := congrArg (valR ξ (X.basicOpen b)) h
  simp only at hv
  rw [valR_mul ξ _ hD, valR_res ξ hbO hD, hres, hres, valR_pow ξ _ h₀] at hv
  have hunit : valR ξ W₀ b ≠ 0 := ((le_preimage_basicOpen_iff ξ h₀ b).1 hD).ne_zero
  have e : valR ξ O t = valR ξ W₀ a / valR ξ W₀ b ^ n := by
    rw [eq_div_iff (pow_ne_zero n hunit)]
    exact hv
  rw [e]
  exact div_mem (hmem a) (pow_mem (hmem b) n)

theorem valR_appIso_inv {C : Type} [CommRing C] {X Y : Scheme.{0}} (r : Y ⟶ X) [IsOpenImmersion r] (y : Sp C ⟶ Y)
    (V : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V) (t : Γ(Y, V)) :
    valR (y ≫ r) (r ''ᵁ V) ((r.appIso V).inv.hom t) = valR y V t := by
  rw [← valR_appLE y r (r.preimage_image_eq V).ge h, ← Scheme.Hom.appIso_hom']
  congr 1
  exact congrArg (fun φ => φ.hom t) (r.appIso V).inv_hom_id

theorem valR_mem_adjoin_of_modification : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  intro Ω _ _ X X' ξ _ _ f U _ ζ hζ hU W₀ hW₀ h₀ A hA W' h' s
  haveI : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hr : Set.range ζ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hU (Set.mem_univ y)
  let y : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι ζ hr
  have hy : y ≫ (f ⁻¹ᵁ U).ι = ζ := IsOpenImmersion.lift_fac _ _ _
  have hyr : y ≫ ((f ⁻¹ᵁ U).ι ≫ f) = ξ := by rw [← Category.assoc, hy, hζ]
  have hV : ⊤ ≤ y ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ W') := fun z hz => by
    have : z ∈ ζ ⁻¹ᵁ W' := h' hz
    rw [← hy] at this
    exact this
  have e1 : valR ζ W' s = valR y _ (((f ⁻¹ᵁ U).ι.app W').hom s) := by
    conv_lhs => rw [← hy]
    exact valR_comp y _ W' s
  rw [e1, ← valR_appIso_inv ((f ⁻¹ᵁ U).ι ≫ f) y _ hV]
  subst hyr
  exact valR_mem_adjoin_of_affine _ hW₀ h₀ A hA (fun z hz => ((( (f ⁻¹ᵁ U).ι ≫ f).preimage_image_eq _).ge (hV hz) : _)) _

end GlobalTheory.CompanionTheory.Ar.SncRes
