import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.CovCmp
import Development.AutomorphicArithmetic.DivisorFrames.PullbackDegreeOfLineBundles
import Development.AutomorphicArithmetic.DivisorFrames.PullbackDegreeGenericResidue
import Development.AutomorphicArithmetic.DivisorFrames.ComparisonOfLineBundleSections
import Development.AutomorphicArithmetic.DivisorFrames.NormalModelComplexCompatAlt
import Development.AutomorphicArithmetic.DivisorFrames.PdegEqOfIsDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open scoped Classical

open private comb from Development.AutomorphicArithmetic.DivisorFrames.NormalModelComplexCompatAlt

namespace GlobalTheory.CovCmp

private theorem pdeg_nsmul {R : Type} [CommRing R] {X : Scheme.{0}} {q : X ⟶ Sp R} {D : ℕ} (hX : IsArithVar q D) (p : ℕ)
    [Fact p.Prime] {d : ℕ} (m : ℕ) {L N : Fin d → LB X} (hL : ∀ k, (L k).IsLB) (hN : ∀ k, (N k).IsLB)
    (e : ∀ k, cls (N k) (hN k) = m • cls (L k) (hL k)) (ζ : X) : pdeg p N ζ = (m : ℤ) ^ d * pdeg p L ζ := by
  by_cases h : ∃ a, IsDeg p L ζ a
  · obtain ⟨a, Z, i, hi, hZ, alg, hz, hd, ha⟩ := h
    rw [UpperTheory.pdeg_eq_of_isDeg p X d L hL ζ _ ⟨Z, i, hi, hZ, alg, hz, hd, rfl⟩,
      UpperTheory.pdeg_eq_of_isDeg p X d N hN ζ _ ⟨Z, i, hi, hZ, alg, hz, hd, rfl⟩]
    obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver (GlobalTheory.T.closed_subscheme_mod_l_projective _ _ _ _ hX _ i p)
    have H := hA.diffVanish_chiPic_of_isProper
      (algebraMap_eq_strHom (ZMod p) Z) (structureModule Z) (d := d) (by rw [GlobalTheory.QCoh.suppDim_structureModule, hd])
    rw [H.interNum_of_cls_eq_zsmul (P := fun j => (L j).pull i) (Q := fun j => (N j).pull i)
      (fun j => pull_isLB (hL j) i) (fun j => pull_isLB (hN j) i) (fun _ => (m : ℤ)) fun j => by
        rw [CechPic.cls_pull (hN j), CechPic.cls_pull (hL j), e, map_nsmul, natCast_zsmul]]
    simp
  · have h' : ¬ ∃ a, IsDeg p N ζ a := fun ⟨_, Z, i, hi, hZ, alg, hz, hd, _⟩ =>
      h ⟨_, Z, i, hi, hZ, alg, hz, hd, rfl⟩
    rw [pdeg, pdeg, dif_neg h, dif_neg h', mul_zero]

private theorem nsmul_div_eq {X : Scheme.{0}} [IsIntegral X] {L N : LB X} (hL : L.IsLB) (hN : N.IsLB)
    {s : L.ι → X.functionFieldˣ} {t : N.ι → X.functionFieldˣ} (hs : IsRatSec L s) (ht : IsRatSec N t) (a b : ℕ)
    (h : ∀ x i j, x ∈ L.U i → x ∈ N.U j → UnitAt x ((s i : X.functionField) ^ a / (t j : X.functionField) ^ b)) :
    a • divOfRatSec hL hs = b • divOfRatSec hN ht := by
  refine CartierDiv.ext_of_isEqn fun x => ?_
  obtain ⟨i, hi⟩ := exists_chart hL x
  obtain ⟨j, hj⟩ := exists_chart hN x
  refine ⟨_, ((presents_divOfRatSec hL hs).isEqn i x hi).nsmul a,
    (((presents_divOfRatSec hN ht).isEqn j x hj).nsmul b).iff_unitAt.2 ?_⟩
  simpa only [Units.val_pow_eq_pow_val] using h x i j hi hj

private theorem mult_nsmul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X) (a : ℕ) (x : X) :
    (a • D).mult x = (a : ℤ) * D.mult x := by
  induction a with
  | zero => simpa using (CartierDiv.isEqn_zero x).mult_eq.trans (unitAt_one x).ord_eq_zero
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

private theorem proj {R : Type} [CommRing R] {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsLocallyNoetherian X]
    [IsLocallyNoetherian X'] {q : X ⟶ Sp R} {q' : X' ⟶ Sp R} {d : ℕ} (hX : IsArithVar q d) (hX' : IsArithVar q' d)
    (nX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (nX' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') (g : X' ⟶ X)
    (w : g ≫ q = q') (hg : g (genericPoint X') ⤳ genericPoint X) (hn : g.residueDegree (genericPoint X') ≠ 0)
    (p : ℕ) [Fact p.Prime] (I : Ideal R) (hp : (p : R) ∈ I) {N : Fin d → LB X} (hN : ∀ k, (N k).IsLB)
    {M : LB X} (hM : M.IsLB) {r : M.ι → X.functionFieldˣ} (hr : IsRatSec M r) :
    ((∑ᶠ ζ : X', (if (q' ζ).asIdeal = I then (divOfRatSec (LB.isLB_pull hM g) (isRatSec_pullSec g hg hr)).mult ζ else 0) *
      pdeg p (fun k => (N k).pull g) ζ : ℤ) : ℝ) = (g.residueDegree (genericPoint X') : ℝ) *
      ∑ᶠ η : X, if (q η).asIdeal = I then (((divOfRatSec hM hr).mult η * pdeg p N η : ℤ) : ℝ) else 0 := by
  have := hX.isNoetherian
  have := hX'.isNoetherian
  have hq (ζ : X') : q (g ζ) = q' ζ := by rw [← w, Scheme.Hom.comp_apply]
  have key := comb (J := Unit) (X := fun _ => X') (fun _ => g)
    (fun _ ζ => if (q' ζ).asIdeal = I then (divOfRatSec (LB.isLB_pull hM g) (isRatSec_pullSec g hg hr)).mult ζ else 0)
    (fun _ => pdeg p (fun k => (N k).pull g)) (fun _ ζ => (g.residueDegree ζ : ℤ))
    (fun _ => (CartierDiv.finite_support_mult (divOfRatSec (LB.isLB_pull hM g) (isRatSec_pullSec g hg hr))).subset
      fun ζ h h0 => h (by simp [h0]))
    (divOfRatSec hM hr).mult (pdeg p N) (CartierDiv.finite_support_mult _)
    (fun η => (q η).asIdeal = I) (fun η => Order.coheight η = 1) 1 (g.residueDegree (genericPoint X') : ℝ) 1 d
    (fun _ ζ h => by
      rw [hq]
      by_contra h'
      exact h (if_neg h'))
    (fun _ ζ h => by
      have h₁ : (q' ζ).asIdeal = I := by
        by_contra h'
        exact h (if_neg h')
      rw [if_pos h₁] at h
      rw [Nat.cast_one, one_pow, one_mul]
      convert UpperTheory.pullback_degree_of_line_bundles R X X' q q' d hX hX' g w p N hN ζ (h₁ ▸ hp) (CartierDiv.coheight_eq_one_of_mult_ne_zero h))
    (fun η h => CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    (fun η hη hη' => by
      obtain ⟨i, hi⟩ := exists_chart hM η
      rw [((presents_divOfRatSec hM hr).isEqn i η hi).mult_eq, one_mul, Fintype.sum_unique,
        ← Int.cast_natCast (g.residueDegree (genericPoint X')),
        ← Int.cast_mul, ← UpperTheory.pullback_degree_generic_residue R X X' q q' d hX hX' nX nX' g w hg hn η hη' (r i) (r i).ne_zero]
      congr 1
      refine finsum_congr fun ζ => ?_
      by_cases h : g ζ = η
      · rw [if_pos h, if_pos h, if_pos (by rw [← hq, h, hη]), Nat.cast_one, one_mul,
          ((presents_divOfRatSec (LB.isLB_pull hM g) (isRatSec_pullSec g hg hr)).isEqn (fun _ => i) ζ
            (mem_pull.2 (by rw [h]; exact hi))).mult_eq]
        rfl
      · rw [if_neg h, if_neg h])
  rw [Nat.cast_one, one_pow, one_mul, one_mul, Fintype.sum_unique] at key
  convert key

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

private theorem map_gen {V' V : Mean4O.Cover Y} (g : V'.G ⟶ V.G) (h : g ≫ V.π = V'.π) :
    g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Mean4O.Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

def vsum (V : Mean4O.Cover Y) (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime] {d : ℕ} (N : Fin d → LB V.X)
    {M : LB V.X} (hM : M.IsLB) {r : M.ι → V.X.functionFieldˣ} (hr : IsRatSec M r) : ℝ :=
  ∑ᶠ η : V.X, if (V.p η).asIdeal = v.asIdeal then
    (((haveI := V.ar.isLocallyNoetherian; (divOfRatSec hM hr).mult η) * pdeg p N η : ℤ) : ℝ) else 0

theorem vsum_cmp (V₁ V₂ : Mean4O.Cover Y) (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 F) ∈ v.asIdeal) {d : ℕ} (hd : Y.dim = d) (m₁ m₂ : ℕ) (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (l₀ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ)
    (l : Fin d → ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ)
    {N₁ : Fin d → LB V₁.X} (hN₁ : ∀ k, (N₁ k).IsLB) (s₁ : ∀ k, (N₁ k).ι → V₁.X.functionFieldˣ)
    (hs₁ : ∀ k v, CRead V₁ v (N₁ k) (s₁ k) fun e y => (m₁ : ℝ) * l k v e y)
    {M₁ : LB V₁.X} (hM₁ : M₁.IsLB) {r₁ : M₁.ι → V₁.X.functionFieldˣ} (hr₁ : IsRatSec M₁ r₁)
    (a₁ : ∀ v, CRead V₁ v M₁ r₁ fun e y => (m₁ : ℝ) * l₀ v e y)
    {N₂ : Fin d → LB V₂.X} (hN₂ : ∀ k, (N₂ k).IsLB) (s₂ : ∀ k, (N₂ k).ι → V₂.X.functionFieldˣ)
    (hs₂ : ∀ k v, CRead V₂ v (N₂ k) (s₂ k) fun e y => (m₂ : ℝ) * l k v e y)
    {M₂ : LB V₂.X} (hM₂ : M₂.IsLB) {r₂ : M₂.ι → V₂.X.functionFieldˣ} (hr₂ : IsRatSec M₂ r₂)
    (a₂ : ∀ v, CRead V₂ v M₂ r₂ fun e y => (m₂ : ℝ) * l₀ v e y) :
    vsum V₁ v p N₁ hM₁ hr₁ / ((V₁.deg : ℝ) * (m₁ : ℝ) ^ (d + 1)) =
      vsum V₂ v p N₂ hM₂ hr₂ / ((V₂.deg : ℝ) * (m₂ : ℝ) ^ (d + 1)) := by
  subst hd
  obtain ⟨V, π₁, π₂, w₁, w₂, b₁, b₂⟩ := GlobalTheory.CoverCommon.exists_cover_dominating_two F Y V₁ V₂
  have := V.ar.isLocallyNoetherian
  have := V₁.ar.isLocallyNoetherian
  have := V₂.ar.isLocallyNoetherian
  have hdeg : ∀ (V' : Mean4O.Cover Y) (π : V.X ⟶ V'.X), π ≫ V'.p = V.p → Lies V V' π →
      π (genericPoint V.X) = genericPoint V'.X ∧ π.residueDegree (genericPoint V.X) * V'.deg = V.deg :=
    fun V' π w ⟨g, c₁, c₂⟩ => GlobalTheory.CoverDeg.map_genericPoint_and_deg F Y V' V π w g c₁.symm c₂ (map_gen g c₂)
  obtain ⟨e₁, d₁⟩ := hdeg V₁ π₁ w₁ b₁
  obtain ⟨e₂, d₂⟩ := hdeg V₂ π₂ w₂ b₂
  have g₁ := specializes_of_eq e₁
  have g₂ := specializes_of_eq e₂
  have n₁ : π₁.residueDegree (genericPoint V.X) ≠ 0 := left_ne_zero_of_mul (d₁ ▸ V.deg_pos.ne')
  have n₂ : π₂.residueDegree (genericPoint V.X) ≠ 0 := left_ne_zero_of_mul (d₂ ▸ V.deg_pos.ne')
  have P₁ := proj V₁.ar V.ar V₁.normal V.normal π₁ w₁ g₁ n₁ p _ hp hN₁ hM₁ hr₁
  have P₂ := proj V₂.ar V.ar V₂.normal V.normal π₂ w₂ g₂ n₂ p _ hp hN₂ hM₂ hr₂
  have hdiv : ∀ {L₁ : LB V₁.X} (hL₁ : L₁.IsLB) {t₁ : L₁.ι → V₁.X.functionFieldˣ} (ht₁ : IsRatSec L₁ t₁)
      {L₂ : LB V₂.X} (hL₂ : L₂.IsLB) {t₂ : L₂.ι → V₂.X.functionFieldˣ} (ht₂ : IsRatSec L₂ t₂)
      (l : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ),
      (∀ v, CRead V₁ v L₁ t₁ fun e y => (m₁ : ℝ) * l v e y) → (∀ v, CRead V₂ v L₂ t₂ fun e y => (m₂ : ℝ) * l v e y) →
      m₂ • divOfRatSec (LB.isLB_pull hL₁ π₁) (isRatSec_pullSec π₁ g₁ ht₁) =
        m₁ • divOfRatSec (LB.isLB_pull hL₂ π₂) (isRatSec_pullSec π₂ g₂ ht₂) :=
    fun hL₁ t₁ _ _ hL₂ t₂ _ l c₁ c₂ => nsmul_div_eq _ _ _ _ _ _ fun x i j hi hj =>
      UpperTheory.comparison_of_line_bundle_sections F Y V V₁ V₂ π₁ π₂ b₁ b₂ g₁ g₂ _ hL₁ t₁ _ hL₂ t₂ l m₁ m₂ c₁ c₂ x _ _ (mem_pull.1 hi) (mem_pull.1 hj)
  have hcls (k : Fin Y.dim) : m₂ • cls _ (LB.isLB_pull (hN₁ k) π₁) = m₁ • cls _ (LB.isLB_pull (hN₂ k) π₂) := by
    have h := congrArg toPic (hdiv (hN₁ k) (hs₁ k v).1 (hN₂ k) (hs₂ k v).1 (l k) (hs₁ k) (hs₂ k))
    rwa [map_nsmul, map_nsmul, (presents_divOfRatSec _ _).toPic_eq, (presents_divOfRatSec _ _).toPic_eq] at h
  choose P hP eP using fun k => cls_surj (m₂ • cls _ (LB.isLB_pull (hN₁ k) π₁))
  have hw (ζ : V.X) : (m₂ : ℤ) ^ Y.dim * pdeg p (fun k => (N₁ k).pull π₁) ζ =
      (m₁ : ℤ) ^ Y.dim * pdeg p (fun k => (N₂ k).pull π₂) ζ :=
    (pdeg_nsmul V.ar p m₂ _ hP eP ζ).symm.trans (pdeg_nsmul V.ar p m₁ _ hP (fun k => (eP k).trans (hcls k)) ζ)
  have hμ (ζ : V.X) : (m₂ : ℤ) * (divOfRatSec (LB.isLB_pull hM₁ π₁) (isRatSec_pullSec π₁ g₁ hr₁)).mult ζ =
      (m₁ : ℤ) * (divOfRatSec (LB.isLB_pull hM₂ π₂) (isRatSec_pullSec π₂ g₂ hr₂)).mult ζ := by
    have h := congrArg (fun D => CartierDiv.mult D ζ) (hdiv hM₁ hr₁ hM₂ hr₂ l₀ a₁ a₂)
    simpa only [mult_nsmul] using h
  have key : (m₂ : ℝ) ^ (Y.dim + 1) * ((π₁.residueDegree (genericPoint V.X) : ℝ) * vsum V₁ v p N₁ hM₁ hr₁) =
      (m₁ : ℝ) ^ (Y.dim + 1) * ((π₂.residueDegree (genericPoint V.X) : ℝ) * vsum V₂ v p N₂ hM₂ hr₂) := by
    refine (congrArg _ P₁.symm).trans (Eq.trans ?_ (congrArg _ P₂))
    rw [← Int.cast_natCast m₂, ← Int.cast_natCast m₁, ← Int.cast_pow, ← Int.cast_pow, ← Int.cast_mul, ← Int.cast_mul,
      mul_finsum, mul_finsum]
    congr 1
    refine finsum_congr fun ζ => ?_
    split_ifs
    · linear_combination ((m₂ : ℤ) ^ Y.dim * pdeg p (fun k => (N₁ k).pull π₁) ζ) * hμ ζ +
        ((m₁ : ℤ) * (divOfRatSec (LB.isLB_pull hM₂ π₂) (isRatSec_pullSec π₂ g₂ hr₂)).mult ζ) * hw ζ
    · simp
  have D₁ : (π₁.residueDegree (genericPoint V.X) : ℝ) * V₁.deg = V.deg := by exact_mod_cast d₁
  have D₂ : (π₂.residueDegree (genericPoint V.X) : ℝ) * V₂.deg = V.deg := by exact_mod_cast d₂
  have z₀ : (V.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 V.deg_pos.ne'
  have z₁ : (V₁.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 V₁.deg_pos.ne'
  have z₂ : (V₂.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 V₂.deg_pos.ne'
  rw [div_eq_div_iff (mul_ne_zero z₁ (pow_ne_zero _ (Nat.cast_ne_zero.2 h₁)))
    (mul_ne_zero z₂ (pow_ne_zero _ (Nat.cast_ne_zero.2 h₂)))]
  refine mul_left_cancel₀ z₀ ?_
  linear_combination (V₁.deg * V₂.deg : ℝ) * key -
    (vsum V₁ v p N₁ hM₁ hr₁ * V₂.deg * (m₂ : ℝ) ^ (Y.dim + 1)) * D₁ +
    (vsum V₂ v p N₂ hM₂ hr₂ * V₁.deg * (m₁ : ℝ) ^ (Y.dim + 1)) * D₂

end GlobalTheory.CovCmp

end
