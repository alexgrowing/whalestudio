import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.DepthZeroInertiaBigOfNarrowBig
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzMatchCut
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
open DiscreteGroups.sglob.DzType
namespace UpperTheory.Lit.Dz
open GlobalTheory.DepthZeroBridge
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise in
theorem depthZeroInertiaBig_of_narrowBig_m_alt : _root_.DiscreteGroups.sglob.DzType.NarrowBigAlt → GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.Zero.LLC.RecTExists →
    _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt := by
  intro HT HG HL
  intro E Ω _ _ _ _ _ _ g _ A w h rc hrc i hi κ L t ht hTC n hbig σ _ τ P hP hinf
  have hn : 0 < n := hP.2.1.1
  obtain ⟨E', _, _, _, _, _, _, _, w', h', hg0, hg1, hN, ⟨ζ, hζ⟩, hfix⟩ := GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots E Ω g A w h i hi n hn
  let t' : Ω ≃ₐ[E'] Ω := { t with commutes' := fun e => hfix t ht e }
  have htt : ∀ z, t' z = t z := fun _ => rfl
  have hdec : t' • A = A := by
    have h0 : t • A = A := ht.1
    ext z
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    conv_rhs => rw [← h0]
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    rfl
  have ht' : t' ∈ Ine (F := E') A := ⟨hdec, fun z hz => ht.2 z hz⟩
  have hres : AlgEquiv.restrictScalars E t' = t := by ext z; rfl
  obtain ⟨a', ha'⟩ : ∃ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' := by
    exact _root_.UpperTheory.One.M.New.artin HL h'
  obtain ⟨art, hart⟩ := HG E' Ω
  set u := a' (ineIncl h' ⟨t', ht'⟩) with hu_def
  have hu : IsUnitAt w' u := GlobalTheory.T.localArtin_inertia_isUnitAt h' a' ha' ⟨t', ht'⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_integer_approx_unit_adicCompletion w' u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hq : 0 < g ^ n - 1 := by
    have : 2 ≤ g ^ n := le_trans hg2 (Nat.le_self_pow hn.ne' g)
    omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hq
  have hy' : y ^ (normV w' - 1) = algebraMap E' Ω ((((g : ℕ) : 𝓞 E')) : E') := by
    rw [hN, hy]; simp
  obtain ⟨σ', hσ'I, hσ'ab, hσ'v⟩ :=
    GlobalTheory.TameRecip.exists_ine_of_unit HG E' Ω art hart w' A h' ((g : ℕ) : 𝓞 E') hg0 hg1 y hy' u x hu hx
  have hab : toAb E' Ω σ' = toAb E' Ω t' := by
    rw [hσ'ab]; exact ha'.glob art hart _
  have hgE : ((g : ℕ) : E') ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  have hkum := GlobalTheory.T.kummerCharacter_factors_absoluteGaloisAbelianization E' Ω (g ^ n - 1) hq ζ hζ ((g : ℕ) : E') hgE y (by rw [hy, map_natCast]) σ' t' hab
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap E' Ω)]; exact (_root_.map_ne_zero _).mpr hgE
  have h1 := hTC n hn y hy
  have h2 : redThrough A κ (algebraMap E' Ω ((x : 𝓞 E') : E')) = L.gen n := by
    rw [← h1]
    have e : t y / y = σ' y / y := by rw [hkum]; rfl
    rw [e]
    exact (redThrough_eq_of_val_sub_lt_one A κ (tameQuot_mem A σ' hq hgΩ hy) hσ'v).symm
  haveI := w'.isMaximal
  letI : Field (𝓞 E' ⧸ w'.asIdeal) := Ideal.Quotient.field _
  have hgK : (((g : ℕ) : 𝓞 E' ⧸ w'.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w'.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hg0
  haveI : CharP (𝓞 E' ⧸ w'.asIdeal) g := (CharP.charP_iff_prime_eq_zero (Fact.out : g.Prime)).mpr hgK
  letI : Algebra (ZMod g) (𝓞 E' ⧸ w'.asIdeal) := ZMod.algebra _ g
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_residueField_embedding_place_over E' Ω g A w' h' κ
  have hcard : Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n := hN
  haveI : Finite (𝓞 E' ⧸ w'.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨θ, hreg, ⟨x0, hx0, hθ⟩, hprod⟩ := GlobalTheory.T.exists_regularCharacter_labelRoot_product g L n hn P hP.1 _ hcard ι
  have hιz : ι (Ideal.Quotient.mk _ x) = L.gen n := by rw [hι]; exact h2
  have hgen0 : L.gen n ≠ 0 := by
    intro e
    have ho := L.gen_order n hn
    rw [e, orderOf_eq_zero_iff'.mpr (fun k hk => by simp [zero_pow hk.ne'])] at ho
    omega
  have hz0 : (Ideal.Quotient.mk w'.asIdeal x) ≠ 0 := by
    intro e; rw [e, map_zero] at hιz; exact hgen0 hιz.symm
  set z : (𝓞 E' ⧸ w'.asIdeal)ˣ := Units.mk0 _ hz0 with hz
  have hform : ∀ y' : Gn g n, Irreducible (y' : Mt g n).charpoly → ∀ z' : (𝓞 E' ⧸ w'.asIdeal)ˣ,
      aeval (z' : 𝓞 E' ⧸ w'.asIdeal) (y' : Mt g n).charpoly = 0 →
      τ.character y' = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z' ^ g ^ j) : ℂˣ) : ℂ) := by
    intro y' hy' z' hz'
    have hmem : ι z' ∈ Formalism.CyclotomicNorms.rootsBar (y' : Mt g n).charpoly := by
      unfold Formalism.CyclotomicNorms.rootsBar
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Matrix.charpoly_monic _).ne_zero), Polynomial.IsRoot.def,
        Polynomial.eval_map]
      have hc : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) = ι.comp (algebraMap (ZMod g) (𝓞 E' ⧸ w'.asIdeal)) :=
        RingHom.ext_zmod _ _
      rw [hc, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hz', map_zero]
    rw [hP.2.2 x0 hx0 y' hy' (ι z') hmem]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hθ, Units.val_pow_eq_pow_val, map_pow]
  have H := HT E E' Ω g A w h w' h' rc hrc i hi n hn hbig hg1 hN a' ha' (𝓞 E' ⧸ w'.asIdeal) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective (Ideal.mk_ker) θ hreg τ hP.2.1 hform σ hinf ⟨t', ht'⟩ x z rfl hx
  rw [← hres, H]
  exact hprod z hιz
end UpperTheory.Lit.Dz
end
end
end
