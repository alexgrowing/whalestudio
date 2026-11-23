import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.UnitAct

section Ring

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F (Om l)] [ValuativeExtension F (Om l)]

theorem valuation_le_one_iff (x : F) :
    valuation F x ≤ 1 ↔ ‖algebraMap F (Om l) x‖ ≤ 1 := by
  rw [← map_one (valuation F), ← (valuation F).vle_iff_le, ← ValuativeExtension.vle_iff_vle (B := Om l),
    GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, map_one, norm_one]

theorem exists_ringEquiv (hR : Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l))) :
    ∃ ρ : 𝒪[F] ≃+* ↥(OL K), ∀ a : 𝒪[F],
      (((ρ a : ↥(OL K)) : ↥K.1) : Om l) = algebraMap F (Om l) (a : F) := by
  have hmem : ∀ a : 𝒪[F], algebraMap F (Om l) (a : F) ∈ K.1 := fun a => by
    have h : algebraMap F (Om l) (a : F) ∈ (K.1 : Set (Om l)) := hR ▸ ⟨_, rfl⟩
    exact h
  have hO : ∀ a : 𝒪[F], (⟨_, hmem a⟩ : ↥K.1) ∈ OL K := fun a =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr ((valuation_le_one_iff (a : F)).mp a.2)
  let f : 𝒪[F] →+* ↥(OL K) :=
    { toFun := fun a => ⟨⟨_, hmem a⟩, hO a⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (by simp))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun a b => Subtype.ext (Subtype.ext (by simp)) }
  have hinj : Function.Injective f := fun a b hab => by
    have h : algebraMap F (Om l) (a : F) = algebraMap F (Om l) (b : F) :=
      congrArg (fun c : ↥(OL K) => ((c : ↥K.1) : Om l)) hab
    exact Subtype.ext ((algebraMap F (Om l)).injective h)
  have hsurj : Function.Surjective f := fun b => by
    have hb : ((b : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) := (b : ↥K.1).2
    rw [← hR] at hb
    obtain ⟨y, hy⟩ := hb
    have hn : ‖algebraMap F (Om l) y‖ ≤ 1 := by
      rw [hy]
      exact (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mp b.2
    exact ⟨⟨y, (valuation_le_one_iff y).mpr hn⟩, Subtype.ext (Subtype.ext hy)⟩
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hsurj⟩, fun a => rfl⟩

theorem card_quot (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    Nat.card (↥(OL K) ⧸ Ideal.span {ρ π}) = Nat.card 𝓀[F] := by
  have e1 : (𝒪[F] ⧸ Ideal.span {π}) ≃ (↥(OL K) ⧸ Ideal.span {ρ π}) :=
    (Ideal.quotientEquiv (Ideal.span {π}) (Ideal.span {ρ π}) ρ
      (by rw [Ideal.map_span, Set.image_singleton]; simp)).toEquiv
  have e2 : 𝓀[F] ≃ (𝒪[F] ⧸ Ideal.span {π}) :=
    (Ideal.quotEquivOfEq hπ.maximalIdeal_eq).toEquiv
  exact Nat.card_congr (e2.trans e1).symm

theorem map_ltPoly (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F]) = ltSeries (ρ π) := by
  rw [ltSeries, card_quot ρ hπ, ltPoly]
  simp

end Ring

theorem main : ∀ {l : ℕ} [Fact l.Prime] {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ}, IsLTChar K χ →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [Algebra.IsAlgebraic F (Om l)],
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) →
    ∃ (π : 𝒪[F]) (hπ : Irreducible π), ∀ (g : Om l ≃ₐ[F] Om l) (g' : ↥(GK K)), (∀ y, g y = (g' : GQ l) y) →
      ∃ u : 𝒪[F]ˣ, algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∧
        ∀ n, ∀ x ∈ lubinTateTorsion (Om l) (hπ := hπ) (isLubinTateSeries_ltPoly π) n,
          lubinTateGalPointMap (hπ := hπ) (isLubinTateSeries_ltPoly π) g x = (u : 𝒪[F]) • x := by
  intro l _ K χ hχ F _ _ _ _ _ _ _ hR
  obtain ⟨πK, z, hπK, h0, h1, hs, hch⟩ := hχ
  obtain ⟨ρ, hρ⟩ := exists_ringEquiv (K := K) (F := F) hR
  have hρπ : ρ (ρ.symm πK) = πK := ρ.apply_symm_apply πK
  obtain ⟨π, hπdef⟩ : ∃ π : 𝒪[F], π = ρ.symm πK := ⟨_, rfl⟩
  rw [← hπdef] at hρπ
  have hπ : Irreducible π := hπdef ▸ (MulEquiv.irreducible_iff ρ.symm).mpr hπK
  have hf := isLubinTateSeries_ltPoly π
  have hcard : Nat.card (↥(OL K) ⧸ Ideal.span {πK}) = Nat.card 𝓀[F] := by
    have h := card_quot ρ hπ
    rwa [hρπ] at h
  have hcoe : ((πK : ↥K.1) : Om l) = algebraMap F (Om l) (π : F) := by
    rw [← hρ π, hρπ]
  have hs' : ∀ n, algebraMap F (Om l) (π : F) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[F] = z n :=
    fun n => by
      rw [← hcoe, ← hcard, add_comm]
      exact hs n
  have hv : ∀ n, valuation (Om l) (z n) < 1 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => exact CharEx.valuation_lt_one_of_eq hπ ih (hs' n)
  let Z : ℕ → IdealPoint (Om l) (lubinTateFormalGroup hπ hf) := fun n => IdealPoint.mk (z n) (hv n)
  have heval : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) →
      ∀ n, (a • Z n).val = (h : GQ l) (z n) := by
    intro a h ha n
    let Φ : PowerSeries 𝒪[F] := (lubinTateHom hπ hf hf a).toPowerSeries
    let ψ : PowerSeries ↥(OL K) := PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) Φ
    have hΦ0 : PowerSeries.constantCoeff Φ = 0 := (lubinTateHom hπ hf hf a).constantCoeff_eq_zero'
    have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0, map_zero]
    have hψ1 : ((PowerSeries.coeff 1 ψ : ↥(OL K)) : ↥K.1) = ((χ h : (↥K.1)ˣ) : ↥K.1) := by
      rw [PowerSeries.coeff_map, coeff_one_lubinTateHom]
      exact ha
    have hF0 : PowerSeries.constantCoeff (ltPoly π : PowerSeries 𝒪[F]) = 0 :=
      hf.constantCoeff_eq_zero
    have hsub : PowerSeries.subst ψ (ltSeries πK) = PowerSeries.subst (ltSeries πK) ψ := by
      have h2 := congrArg (MvPowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)))
        (subst_lubinTateHom hπ hf hf a)
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hΦ0),
        PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0)] at h2
      change PowerSeries.subst ψ (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) =
        PowerSeries.subst (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) ψ at h2
      rwa [map_ltPoly ρ hπ, hρπ] at h2
    have hsum := hch h ψ hψ0 hψ1 hsub n
    have hsum2 := CharEx.hasSum_coeff_mul_pow (K := F) Φ (hv n)
    rw [lubinTate_smul_val]
    refine hsum2.unique ?_
    convert hsum using 2 with k
    simp only [ψ, PowerSeries.coeff_map]
    rw [← hρ]
    rfl
  have hZ0 : Z 0 = 0 := IdealPoint.ext h0
  have hZ1 : Z 1 ≠ 0 := fun h => h1 (congrArg IdealPoint.val h)
  have hstep : ∀ n, π • Z (n + 1) = Z n := fun n => IdealPoint.ext (by
    rw [lubinTate_uniformizer_smul_val]
    change psEval ((ltPoly π : Polynomial 𝒪[F]) : PowerSeries 𝒪[F]) (fun _ => z (n + 1)) = z n
    rw [psEval_polynomial, aeval_ltPoly]
    exact hs' n)
  have hpow : ∀ n, π ^ n • Z (n + 1) = Z 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hstep, ih]
  have hunit : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) → IsUnit a := by
    intro a h ha
    by_contra hnu
    have hm := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
    obtain ⟨b, rfl⟩ := hm
    have h2 : (b * π) • Z 1 = 0 := by rw [mul_smul, hstep, hZ0, smul_zero]
    have h3 := heval _ h ha 1
    rw [h2] at h3
    exact h1 ((map_eq_zero_iff _ (h : GQ l).injective).mp h3.symm)
  refine ⟨π, hπ, fun g g' hg => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : 𝒪[F]ˣ,
      algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) := by
    have hy : (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) :=
      ((χ g' : (↥K.1)ˣ) : ↥K.1).2
    rw [← hR] at hy
    obtain ⟨y, hy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (χ g').ne_zero (Subtype.ext hy.symm)
    rcases le_total (valuation F y) 1 with hle | hle
    · obtain ⟨w, hw⟩ := hunit ⟨y, hle⟩ g' (Subtype.ext (by rw [hρ]; exact hy))
      exact ⟨w, by rw [hw]; exact hy⟩
    · have hle' : valuation F y⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ hle
      have hinv : (((χ (g'⁻¹) : (↥K.1)ˣ) : ↥K.1) : Om l) = algebraMap F (Om l) y⁻¹ := by
        rw [map_inv, map_inv₀, hy, Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      obtain ⟨w, hw⟩ := hunit ⟨y⁻¹, hle'⟩ g'⁻¹ (Subtype.ext (by rw [hρ, hinv]))
      refine ⟨w⁻¹, ?_⟩
      have hw2 : ((w : 𝒪[F]) : F) = y⁻¹ := by rw [hw]
      have hw3 : (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * ((w : 𝒪[F]) : F) = 1 := by
        have h5 : ((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (w : 𝒪[F]) = 1 := Units.inv_mul w
        exact congrArg Subtype.val h5
      rw [hw2] at hw3
      rw [← hy, (eq_of_mul_inv_eq_one hw3)]
  refine ⟨u, hu, fun n x hx => ?_⟩
  have hgZ : lubinTateGalPointMap (hπ := hπ) hf g (Z (n + 1)) = (u : 𝒪[F]) • Z (n + 1) :=
    IdealPoint.ext (by
      rw [lubinTateGalPointMap_val, heval (u : 𝒪[F]) g' (Subtype.ext (by rw [hρ]; exact hu))]
      exact hg _)
  have hZt : Z (n + 1) ∈ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1) :=
    CharEx.mem_torsion hπ h0 hs' (n + 1) _ rfl
  have hZn : Z (n + 1) ∉ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1 - 1) := by
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, hpow]
    exact hZ1
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hZt hZn
  obtain ⟨a, rfl⟩ := hgen x (lubinTateTorsion_mono hπ hf n.le_succ hx)
  rw [map_smul, hgZ, smul_smul, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.LTHodge.UnitAct
