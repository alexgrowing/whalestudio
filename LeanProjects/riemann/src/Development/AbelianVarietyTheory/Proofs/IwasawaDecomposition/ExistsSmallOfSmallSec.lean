import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuativeExtensionPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

namespace GlobalTheory.SmallInduced

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    TrueGeo.valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [TrueGeo.valAt, dif_pos h]
  congr 1
  exact IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    TrueGeo.valAt y (f * g) = TrueGeo.valAt y f * TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_ne_zero {f : Z.functionField} (hf : UnitAt (below y) f) : TrueGeo.valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map _).ne_zero

omit [IsIntegral Z] in

theorem top_le_of_below {U : Z.Opens} (hy : below y ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
  have : x = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]
  exact hy

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    TrueGeo.valAt y (fnOf U h a) = valR y U a := by
  rw [← algebraMap_germ hy, valAt_algebraMap, valR, dif_pos (top_le_of_below y hy)]
  have := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  exact this

end Val

theorem valR_spMap_comp {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) {X : Scheme.{0}}
    (x : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valR (spMap φ ≫ x) U a = φ (valR x U a) := by
  rw [← valR_appLE (spMap φ) x h le_top, valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from le_top), valR, dif_pos h]
  have := congrArg (fun ψ => ψ.hom ((x.appLE U ⊤ h).hom a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  refine Eq.trans ?_ this
  exact congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (ψ.hom ((x.appLE U ⊤ h).hom a)))
    (Scheme.Hom.appLE_eq_app (spMap φ) (U := ⊤))

theorem exists_small_of_smallSec : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p), A.n = 1 → A.ci = 0 → A.Induced M L 1 0 → ∀ s ∈ L.smallSec, ∃ f ∈ A.small 1, ∀ x : Y.X, A.D.GeneratesAt x f ↔ M.j x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := by
  intro F _ _ C Y A M L hn hc ⟨_, r, h, hinf, hfin⟩ s hs
  have hD : (((1 : ℕ+) : ℕ) • A.D) = A.D := one_nsmul _
  have hval {K : Type} [Field K] (y : Sp K ⟶ Y.X) (i : (L.B.pull M.j).ι) (hi : ⊤ ≤ y ⁻¹ᵁ (L.B.pull M.j).U i) :
      valR y _ ((Cartier.secPull s M.j).f i) = valR (y ≫ M.j) _ (s.f (i PUnit.unit)) :=
    valR_appLE y M.j (LB.pull_U M.j i).le hi _
  refine ⟨h.rat (Cartier.secPull s M.j), ⟨?_, fun σ y => ?_, fun v e y => ?_⟩, fun x => ?_⟩
  · change h.rat (Cartier.secPull s M.j) ^ (A.n : ℕ) ∈ Y.H0 (1 • A.D)
    rw [show (A.n : ℕ) = 1 from congrArg _ hn, pow_one]
    exact Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 (mem_sections.1 (h.rat_mem _))
  · obtain ⟨i, hi⟩ := exists_chart h.isLB (under y)
    have hy' : (y.1 ≫ M.j) ≫ M.p = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
      rw [Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp]
      rfl
    have h1 := hinf σ y ⟨_, hy'⟩ i _ rfl hi (mem_sections.1 (h.rat_mem (Cartier.secPull s M.j)) _)
    have hi' : (⟨_, hy'⟩ : CxPts M.p _) ∈ ptsIn M.p _ (L.B.U (i PUnit.unit)) :=
      mem_ptsIn.2 ((LB.pull_U M.j i).le hi)
    have h2 := hs _ ⟨_, hy'⟩
    rw [(L.φ _).nsq_eq (secVal_mem s) hi'] at h2
    rw [h.rat_mul _ i (gen_mem hi), ratVal_fnOf (mem_ptsIn.2 hi), ev, hval y.1 i (mem_ptsIn.2 hi), hc] at h1
    replace h2 := h1.trans_le h2
    have h3 : (0 : ℝ) ≤ _ := h1.ge.trans' (by positivity)
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul] at h2 h3
    unfold Adl.nrmInf
    rw [hc, hn]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul, PNat.one_coe, pow_one]
    exact Real.rpow_le_one h3 h2 (by positivity)
  · obtain ⟨yt, hyt, hU⟩ := GlobalTheory.T.valuative_extension_point F Y M v e y
    obtain ⟨j, hj⟩ := exists_chart L.isLB (yt (IsLocalRing.closedPoint e.O))
    obtain ⟨hU1, hU2⟩ := hU _ hj
    let i : (L.B.pull M.j).ι := fun _ => j
    have hi : below y.1 ∈ (L.B.pull M.j).U i := (LB.pull_U M.j i).ge hU2
    have h1 := hfin v e y yt i hyt hU1
    have he : A.D.IsEqn (below y.1) (eqn A.D (below y.1)) := (A.D.exists_isEqn _).choose_spec
    have hr : A.D.IsEqn (below y.1) (r i) := hD ▸ h.isEqn i _ hi
    have hu := he.iff_unitAt.1 hr
    have hreg : RegAt (below y.1) (h.rat (Cartier.secPull s M.j) * (eqn A.D (below y.1) : Y.Fn)) :=
      he.regularAt_iff.1 ((congrArg (fun D => CartierDiv.RegularAt D _ _) hD).mp
        (mem_sections.1 (h.rat_mem (Cartier.secPull s M.j)) _))
    simp only [PNat.one_coe, pow_one, Nat.cast_one, one_mul, Pi.zero_apply, mul_zero, sub_zero,
      Units.val_mul, Units.val_inv_eq_inv_val] at h1
    rw [← div_eq_inv_mul] at h1
    unfold Adl.nrmFin
    rw [hn, h1]
    simp only [PNat.one_coe, pow_one, Nat.cast_one, one_mul, div_one, Real.rpow_one]
    rw [Real.exp_log (e.w.pos (valAt_ne_zero _ hu)), ← map_mul]
    refine (congrArg e.w (valAt_mul _ hreg hu.regAt)).ge.trans ?_
    rw [← mul_eqn_eq, h.rat_mul _ i (gen_mem hi), valAt_fnOf _ hi, hval _ i (top_le_of_below _ hi),
      ← hyt, valR_spMap_comp _ _ hU1]
    exact (e.mem_O _).1 (Subtype.prop _)
  · refine (congrArg (fun D => CartierDiv.GeneratesAt D _ _) hD).symm.to_iff.trans ?_
    rw [h.generatesAt_rat_iff, Cartier.nonzeroLocus_secPull]
    rfl

end GlobalTheory.SmallInduced
