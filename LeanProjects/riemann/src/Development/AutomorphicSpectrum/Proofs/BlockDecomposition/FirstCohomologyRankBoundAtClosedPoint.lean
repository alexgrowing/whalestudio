import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq.FibreRed

open GlobalTheory.SmallExtLift

theorem app_eq_zero_of_mem_ext {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}}
    {s : X ⟶ Sp R} {ι : Y ⟶ X} {f : Y ⟶ Sp (IsLocalRing.ResidueField R)}
    (w : ι ≫ s = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) (U : X.Opens)
    {z : Γ(X, U)} (hz : z ∈ ext s (IsLocalRing.maximalIdeal R) U) : (ι.app U).hom z = 0 := by
  have key : Ideal.map (GlobalTheory.SmallExtLift.cst s U) (IsLocalRing.maximalIdeal R) ≤
      RingHom.ker (ι.app U).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, GlobalTheory.SmallExtLift.app_cst w U r,
      (IsLocalRing.residue_eq_zero_iff r).mpr hr, map_zero]
  exact key hz

private theorem app_rs_eq_rs_app {X Y : Scheme.{0}} (φ : Y ⟶ X) {U W : X.Opens} (h : W ≤ U)
    (h' : φ ⁻¹ᵁ W ≤ φ ⁻¹ᵁ U) (x : Γ(X, U)) :
    (φ.app W).hom (rs X h x) = rs Y h' ((φ.app U).hom x) := by
  have := congrArg (fun q => q.hom x) (φ.naturality (homOfLE h).op)
  exact this

theorem dep_fibre : DepSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s →
    ∀ n r : ℕ, n < r →
    (∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ X),
      IsPullback φ s' s (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
      Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
        Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ n) →
    ∀ (A : Type) (V : A → X.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
      (∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d)) →
      ∃ (e : Fin r → R) (β : ∀ a, Γ(X, V a)), (∃ l, IsUnit (e l)) ∧ ∀ a c,
        ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
          ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c) := by
  intro hD R _ _ X s hs n r hnr hfib A V hV hVa b hb
  let g := spMap (algebraMap R (IsLocalRing.ResidueField R))
  let φ := pullback.fst s g
  let s' := pullback.snd s g
  have hpb : IsPullback φ s' s g := IsPullback.of_hasPullback _ _
  have hpb' : IsPullback φ s' s (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := hpb
  have hw : φ ≫ s = s' ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := hpb.w
  have hsurj : Function.Surjective (IsLocalRing.residue R) := Ideal.Quotient.mk_surjective
  obtain ⟨hfin, hrank⟩ := hfib _ s' φ hpb
  have hSp : ∀ (T : Type) [CommRing T], (Sp T).IsSeparated := fun T _ => by unfold Sp; infer_instance
  haveI hXsep : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  haveI hsep : (pullback s g).IsSeparated := ⟨by rw [← terminal.comp_from s']; infer_instance⟩
  haveI hg : IsAffineHom g := by
    show IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
    infer_instance
  haveI haff : IsAffineHom φ := MorphismProperty.pullback_fst (P := @IsAffineHom) s g hg
  let V' : A → (pullback s g).Opens := fun a => φ ⁻¹ᵁ V a
  have hV' : ⨆ a, V' a = ⊤ := by
    have h1 : ⨆ a, V' a = φ ⁻¹ᵁ (⨆ a, V a) := (TopologicalSpace.Opens.map_iSup φ.base V).symm
    rw [h1, hV]
    rfl
  have hV'a : ∀ a, IsAffineOpen (V' a) := fun a => (hVa a).preimage φ
  let α : Fin r → ∀ a c, Γ(pullback s g, V' a ⊓ V' c) := fun i a c => (φ.app (V a ⊓ V c)).hom (b i a c)
  have hα : ∀ i a c d, rs _ (le₁₂ V' a c d) (α i a c) + rs _ (le₂₃ V' a c d) (α i c d) =
      rs _ (le₁₃ V' a c d) (α i a d) := by
    intro i a c d
    have h0 := app_eq_zero_of_mem_ext hw (V a ⊓ V c ⊓ V d) (hb i a c d)
    rw [map_sub, map_add, app_rs_eq_rs_app φ (le₁₂ V a c d) (le₁₂ V' a c d),
      app_rs_eq_rs_app φ (le₂₃ V a c d) (le₂₃ V' a c d), app_rs_eq_rs_app φ (le₁₃ V a c d) (le₁₃ V' a c d)] at h0
    exact sub_eq_zero.mp h0
  obtain ⟨c, ψ, hc0, hcψ⟩ := hD (IsLocalRing.ResidueField R) (pullback s g) s' hsep n r hfin hrank hnr A V'
    hV' hV'a α hα
  choose e he using fun i => hsurj (c i)
  choose β hβ using fun a => app_surj hsurj hpb' (hVa a) (ψ a)
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hc0
  have hlu : IsUnit (e l) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [he l]; exact hl)
  refine ⟨e, β, ⟨l, hlu⟩, fun a c' => ?_⟩
  show _ ∈ Ideal.map (cst s (V a ⊓ V c')) (IsLocalRing.maximalIdeal R)
  rw [← IsLocalRing.ker_residue]
  apply mem_of_app_eq_zero hsurj hpb' ((hVa a).inf (hVa c'))
  rw [map_sub, map_sum, map_sub, app_rs_eq_rs_app φ inf_le_left (inf_le_left : V' a ⊓ V' c' ≤ V' a),
    app_rs_eq_rs_app φ inf_le_right (inf_le_right : V' a ⊓ V' c' ≤ V' c'), hβ, hβ]
  simp only [map_mul, app_cst hw, he]
  exact sub_eq_zero.mpr (hcψ a c')

end GlobalTheory.CompanionTheory.FewEq.FibreRed
