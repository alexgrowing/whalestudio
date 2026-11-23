import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagDeg

theorem presents_triv_pull {k : Type} [CommRing k] {X Z : Scheme.{0}} [IsIntegral Z] (p : X ⟶ Sp k) (j : Z ⟶ X) :
    Presents (0 : CartierDiv Z) ((HermLB.triv p).B.pull j) fun _ => 1 := by
  have hL := LB.isLB_pull (HermLB.triv p).isLB j
  refine ⟨hL, fun a b h => ?_, fun _ x _ => CartierDiv.isEqn_zero x⟩
  obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
  have := congrArg (fun u : Γ(Z, _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)
  rw [Units.val_one, map_one] at this
  exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm

theorem presents_zp_pull {k : Type} [CommRing k] {X Z : Scheme.{0}} [IsIntegral Z] {p : X ⟶ Sp k} (L : HermLB p)
    (j : Z ⟶ X) {Δ : CartierDiv Z} {r : (L.B.pull j).ι → Z.functionFieldˣ} (hr : Presents Δ (L.B.pull j) r) (m : ℤ) :
    ∃ s, Presents (m • Δ) ((zp L m).B.pull j) s := by
  have h₁ := TrueGeo.InducedPow.presents_pow L.B j m.toNat L.isLB hr
  have h₂ := LineNorm.Neg.presents_neg (L.pow (-m).toNat).isLB j
    (TrueGeo.InducedPow.presents_pow L.B j (-m).toNat L.isLB hr)
  have h₃ := LineNorm.Add.presents_tens (L.pow m.toNat).isLB (L.pow (-m).toNat).dual.isLB j h₁ h₂
  have e : m.toNat • Δ + -((-m).toNat • Δ) = m • Δ := by
    conv_rhs => rw [← Int.toNat_sub_toNat_neg m]
    rw [sub_smul, natCast_zsmul, natCast_zsmul, sub_eq_add_neg]
  rw [e] at h₃
  exact ⟨_, h₃⟩

theorem presents_foldr_pull {k : Type} [CommRing k] {X Z : Scheme.{0}} [IsIntegral Z] {p : X ⟶ Sp k} {κ : Type}
    (L : κ → HermLB p) (n : κ → ℤ) (j : Z ⟶ X) (Δ : κ → CartierDiv Z)
    (hΔ : ∀ x, ∃ r, Presents (Δ x) ((L x).B.pull j) r) :
    ∀ l : List κ, ∃ s, Presents ((l.map fun x => n x • Δ x).sum)
      ((l.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p)).B.pull j) s
  | [] => ⟨_, presents_triv_pull p j⟩
  | i :: l => by
    obtain ⟨s, hs⟩ := presents_foldr_pull L n j Δ hΔ l
    obtain ⟨r, hr⟩ := hΔ i
    obtain ⟨t, ht⟩ := presents_zp_pull (L i) j hr (n i)
    rw [List.map_cons, List.sum_cons, List.foldr_cons]
    exact ⟨_, LineNorm.Add.presents_tens (zp (L i) (n i)).isLB
      (l.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p)).isLB j ht hs⟩

theorem presents_comb_pull {k : Type} [CommRing k] {X Z : Scheme.{0}} [IsIntegral Z] {p : X ⟶ Sp k} {κ : Type}
    [Fintype κ] (L : κ → HermLB p) (n : κ → ℤ) (j : Z ⟶ X) (Δ : κ → CartierDiv Z)
    (hΔ : ∀ x, ∃ r, Presents (Δ x) ((L x).B.pull j) r) :
    ∃ s, Presents (∑ x, n x • Δ x) ((comb L n).B.pull j) s := by
  obtain ⟨s, hs⟩ := presents_foldr_pull L n j Δ hΔ (Finset.univ : Finset κ).toList
  rw [Finset.sum_map_toList] at hs
  exact ⟨s, hs⟩

theorem exists_homeomorph_int {X Y : Scheme.{0}} (p : X ⟶ Sp ℤ) (q : Y ⟶ Sp ℚ) (j : Y ⟶ X)
    (pb : IsPullback j q p (spMap (algebraMap ℤ ℚ))) (σ : ℚ →+* ℂ) :
    ∃ Φ : CxPts q σ ≃ₜ CxPts p (σ.comp (algebraMap ℤ ℚ)), ∀ z, (Φ z).1 = z.1 ≫ j := by
  have e : spMap σ ≫ spMap (algebraMap ℤ ℚ) = spMap (σ.comp (algebraMap ℤ ℚ)) := by
    rw [← Spec.map_comp]; rfl
  have h₁ (z : CxPts q σ) : (z.1 ≫ j) ≫ p = spMap (σ.comp (algebraMap ℤ ℚ)) := by
    rw [Category.assoc, pb.w, ← Category.assoc, z.2, e]
  have h₂ : Continuous fun y : CxPts p (σ.comp (algebraMap ℤ ℚ)) =>
      pb.lift y.1 (spMap σ) (y.2.trans e.symm) := by
    rw [(Points.isEmbedding_of_isPullback pb).continuous_iff]
    refine (continuous_subtype_val.prodMk (continuous_const (y := spMap σ))).congr fun y => ?_
    exact (Prod.ext (pb.lift_fst _ _ _) (pb.lift_snd _ _ _)).symm
  exact ⟨{ toFun := fun z => ⟨z.1 ≫ j, h₁ z⟩
           invFun := fun y => ⟨pb.lift y.1 (spMap σ) (y.2.trans e.symm), pb.lift_snd _ _ _⟩
           left_inv := fun z => Subtype.ext (pb.hom_ext (pb.lift_fst _ _ _)
             ((pb.lift_snd _ _ _).trans z.2.symm))
           right_inv := fun y => Subtype.ext (pb.lift_fst _ _ _)
           continuous_toFun := ((Points.continuous_comp j).comp continuous_subtype_val).subtype_mk h₁
           continuous_invFun := h₂.subtype_mk fun y => pb.lift_snd _ _ _ }, fun _ => rfl⟩

theorem dim_eq_of_smooth (Y : Var ℚ) (d : ℕ) (h : SmoothOfRelativeDimension d Y.str) : d = Y.dim := by
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint Y.X))
  have h₁ := SmoothDim.ringKrullDim_affineOpen ℚ _ Y.str d h U hU ⟨_, hx⟩
  have h₂ := SmoothDim.ringKrullDim_affineOpen ℚ _ Y.str Y.dim inferInstance U hU ⟨_, hx⟩
  exact_mod_cast h₁.symm.trans h₂

end GlobalTheory.FlagDeg

namespace GlobalTheory.FlagDeg

theorem gdeg_comb_grLine : GlobalTheory.Published.ChernDegree → ∀ (ι : Type) [Fintype ι] (N : ℕ) (Y : GlobalTheory.ProjVar.Var ℚ)
    (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N), IsPullback j Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) →
    ∀ (gr : ι × Fin N → Y.Dv), (∀ x, ∃ r, GlobalTheory.Cartier.Presents (gr x) ((GlobalTheory.FlagZ.grLine x).B.pull j) r) →
    ∀ n : ι × Fin N → ℤ, gdeg (comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n) Y.dim =
      ((Y.inter fun _ => ∑ x, n x • gr x : ℤ) : ℝ) := by
  intro hd ι _ N Y j pb gr hgr n
  obtain ⟨s, hs⟩ := presents_comb_pull (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n j gr hgr
  obtain ⟨hsm, -, hav⟩ := GlobalTheory.FlagZ.smooth_dim_isArithVar_part ι (ι × Fin (N + 1)) N Prod.fst Prod.snd
  have hY : SmoothOfRelativeDimension (Nat.card (GlobalTheory.FlagZ.CellVar (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))
      Y.str := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0}
      (Nat.card (GlobalTheory.FlagZ.CellVar (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension _) pb hsm
  have hdim := dim_eq_of_smooth Y _ hY
  rw [hdim] at hsm
  let σ' : ℚ →+* ℂ := Rat.castHom ℂ
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_int (GlobalTheory.FlagZ.flStr ι N) Y.str j pb σ'
  have := CxPts.secondCountableTopology_of_isProjOver (σ'.comp (algebraMap ℤ ℚ)) hav.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ' Y.isProjOver
  obtain ⟨h₁, h₂⟩ := GlobalTheory.chernInt_transfer ℤ ℚ _ _ (GlobalTheory.FlagZ.flStr ι N) Y.str _ σ' Y.dim j Φ hΦ
    inferInstance inferInstance _ _ ((comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n).cInf _)
  have h₃ := (hd ℚ Y σ' _ _ s hs _ h₁).2
  rw [gdeg, chInt, finsum_eq_single _ (σ'.comp (algebraMap ℤ ℚ)) fun τ hτ => absurd (RingHom.ext_int _ _) hτ]
  exact h₂.symm.trans h₃

end GlobalTheory.FlagDeg
