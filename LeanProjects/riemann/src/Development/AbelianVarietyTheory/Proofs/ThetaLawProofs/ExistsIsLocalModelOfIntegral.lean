import Mathlib
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_sec_fibre_ne_zero (hT : Out.SecTwistSt) {S X : Scheme.{0}} (P : Out.PolAV S) {R : Type} [CommRing R]
    [IsLocalRing R] {t : Sp R ⟶ S} {φ : X ⟶ P.A.left} {q : X ⟶ Sp R} (hp : IsPullback φ q P.A.hom t) :
    ∃ th : (P.L.pull φ).Sec, ∀ s : Sp R, ∃ z : X, q z = s ∧ z ∈ Out.nonzeroLocus th := by
  have := P.isAb.comm
  have := P.isAb.smooth
  let k := IsLocalRing.ResidueField R
  let T : Over S := Over.mk t
  let T' : Over S := Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ t)
  let ν : T' ⟶ T := Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) rfl
  have e : ∀ T : Over S, Out.translPt P.A (1 : T ⟶ P.A) = snd T P.A := fun T => by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ P 1 le_rfl k (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ t) 1
  obtain ⟨-, hl⟩ := hT _ P 1 le_rfl R t 1
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  have nz : ∃ j, (b i₀).f j ≠ 0 := by
    by_contra b0
    push Not at b0
    obtain ⟨r, -, hu⟩ := hb (b i₀)
    have := (hu (fun _ => 0) fun k => (b0 k).trans ((su _).trans
      ((congrArg (_ * ·) (b0 k)).trans (mul_zero _))).symm).trans (hu (fun _ => 1) fun k => (b0 k).trans
      ((su _).trans ((congrArg (_ * ·) (b0 k)).trans (mul_zero _))).symm).symm
    exact zero_ne_one ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective
      ((map_zero _).trans ((congrFun this i₀).trans (map_one _).symm)))
  have : Smooth (fst T' P.A).left := inferInstanceAs (Smooth (pullback.fst T'.hom P.A.hom))
  have : IsReduced (T' ⊗ P.A).left := isReduced_scheme_of_smooth_of_isIntegrallyClosed k (fst T' P.A).left
  obtain ⟨j, hj⟩ := nz
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (T' ⊗ P.A).left.basicOpen ((b i₀).f j) := by
    by_contra hn
    exact hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, hz⟩))
  have hν : (ν ▷ P.A).left ≫ (snd T P.A).left = (snd T' P.A).left := congrArg (fun q => q.left) (whiskerRight_snd ν P.A)
  have hν' : (ν ▷ P.A).left ≫ (fst T P.A).left = (fst T' P.A).left ≫ ν.left :=
    congrArg (fun q => q.left) (whiskerRight_fst ν P.A)
  obtain ⟨sb, hsb⟩ := exists_sec P.isLB (K' := Fin 2)
    (φ' := fun k => (ν ▷ P.A).left ≫ ![(snd T P.A).left, (Out.translPt P.A (1 : T ⟶ P.A)).left] k)
    (ε' := ![((1 : ℕ) : ℤ) - 1, 1]) (fun U _ k => by
      rw [e, e, Fin.prod_univ_two, Fin.prod_univ_two]
      exact congrArg₂ (· * ·) (congrArg (fun f => k f ^ _) hν.symm) (congrArg (fun f => k f ^ _) hν.symm)) (b i₀)
  obtain ⟨s, hs⟩ := hl sb
  have hz' : (ν ▷ P.A).left z ∈ Out.nonzeroLocus s := by
    choose J hJ using fun χ : (T' ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ z)
    have u := (MulPullSec.mem_nonzeroLocus_iff (b i₀) (𝟙 _) z hJ).1 (Opens.mem_iSup.2 ⟨j, hz⟩)
    rw [← hsb _ _ z J hJ] at u
    have hm := Good.mem hJ (fun k => (ν ▷ P.A).left ≫ ![(snd T P.A).left, (Out.translPt P.A (1 : T ⟶ P.A)).left] k) (𝟙 _)
    have hm' := Out.wchart_comp_le P.L _ _ _ hm
    have u' := (congrArg IsUnit ((congrArg (gs _ z _) (hs _)).trans
      ((gs_res _ z _ hm _).trans (gs_pull (𝟙 _) (ν ▷ P.A).left z _ hm' _)))).mp u
    exact Opens.mem_iSup.2 ⟨_, (MulPullSec.isUnit_gs_iff (𝟙 _ ≫ (ν ▷ P.A).left) z _ hm' _).1 u'⟩
  let ρ : X ⟶ (T ⊗ P.A).left := pullback.lift q φ hp.w.symm
  have ρ₂ : ρ ≫ (snd T P.A).left = φ := pullback.lift_snd _ _ _
  have ρ₁ : ρ ≫ (fst T P.A).left = q := pullback.lift_fst _ _ _
  let σ : (T ⊗ P.A).left ⟶ X := hp.lift (snd T P.A).left (fst T P.A).left pullback.condition.symm
  have σ₂ : σ ≫ φ = (snd T P.A).left := hp.lift_fst _ _ _
  have σ₁ : σ ≫ q = (fst T P.A).left := hp.lift_snd _ _ _
  have σρ : σ ≫ ρ = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ρ₁).trans (σ₁.trans (Category.id_comp _).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ρ₂).trans (σ₂.trans (Category.id_comp _).symm))
  have h1 : (LB.oneGen P.L (Y := X)).IsGen := fun i j =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨th, hth⟩ := exists_sec P.isLB (K' := PUnit) (φ' := fun _ => φ) (ε' := fun _ => 1) (fun U _ k => by
      rw [e, Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_empty, Fintype.prod_unique]
      show k (ρ ≫ (snd T P.A).left) ^ (((1 : ℕ) : ℤ) - 1) * k (ρ ≫ (snd T P.A).left) ^ (1 : ℤ) * 1 = k φ ^ (1 : ℤ)
      rw [ρ₂]; simp) (pullMulSec s ρ _ h1)
  have hy : σ ((ν ▷ P.A).left z) ∈ Out.nonzeroLocus th := by
    choose J hJ using fun χ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ ((ν ▷ P.A).left z))
    refine (MulPullSec.mem_nonzeroLocus_iff th σ _ hJ).2 ?_
    rw [hth _ _ _ J hJ, sval_pullMulSec s ρ _ _ _ _ hJ, Units.isUnit_mul_units, σρ]
    exact (MulPullSec.mem_nonzeroLocus_iff s (𝟙 _) _ hJ).1 hz'
  have hc : q (σ ((ν ▷ P.A).left z)) = IsLocalRing.closedPoint R := by
    refine (congrArg (fun f => f z) ((congrArg ((ν ▷ P.A).left ≫ ·) σ₁).trans hν')).trans ?_
    refine Eq.trans ?_ (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))
    exact congrArg (PrimeSpectrum.comap (IsLocalRing.residue R)) (Subsingleton.elim (α := PrimeSpectrum k) _ _)
  have : Smooth q := MorphismProperty.of_isPullback (P := @Smooth) hp ‹_›
  have ht := (IsLocalRing.closedPoint_mem_iff (R := R) ⟨_, q.isOpenMap _ (Out.nonzeroLocus th).isOpen⟩).1 ⟨_, hy, hc⟩
  refine ⟨th, fun s => ?_⟩
  obtain ⟨y, h₁, h₂⟩ := (congrArg (fun U => s ∈ U) ht).mpr trivial
  exact ⟨y, h₂, h₁⟩

theorem exists_rescale {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : X' ⟶ X}
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) {e : Y ⟶ X} {e' : Y' ⟶ X'} {p : X' ⟶ Y'} (hp : e' ≫ p = 𝟙 _) {h : Y' ⟶ Y}
    (he : e' ≫ F = h ≫ e) {a : LB.Gen (L'.pull e')} (ha : a.IsGen) {t : LB.Gen (L.pull e)} (ht : t.IsGen) :
    ∃ w' : LB.Iso L' (L.pull F), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) a t h := by
  have m : ∀ (y : Y') j, F (e' y) ∈ L.U j → h y ∈ LB.wchart L (fun _ : PUnit => e) (fun _ => j) := fun y j hj =>
    Set.mem_iInter.2 fun _ => (congrArg (fun f => f y ∈ L.U j) he).mp hj
  let W : L.ι × L'.ι → Y'.Opens := fun i => e' ⁻¹ᵁ (F ⁻¹ᵁ L.U i.1 ⊓ L'.U i.2)
  have l₁ : ∀ i, W i ≤ h ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => i.1) := fun i y hy => m y _ hy.1
  have l₂ : ∀ i, W i ≤ e' ⁻¹ᵁ ((L.pull F).U (fun _ => i.1) ⊓ L'.U i.2) := fun i y hy => ⟨mem_pull.2 hy.1, hy.2⟩
  have l₃ : ∀ i, W i ≤ LB.wchart L' (fun _ : PUnit => e') (fun _ => i.2) := fun i y hy => Set.mem_iInter.2 fun _ => hy.2
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y', W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i, r z ∈ W i →
      gm r z (W i) (u i) = gm (r ≫ h) z (LB.wchart L (fun _ : PUnit => e) (fun _ => i.1)) (t.s fun _ => i.1) *
        (gw w (r ≫ e') z i.1 i.2 * gm r z (LB.wchart L' (fun _ : PUnit => e') (fun _ => i.2)) (a.s fun _ => i.2))⁻¹ :=
    ⟨fun i => res (l₁ i) (pullU h _ (t.s fun _ => i.1)) *
        (res (l₂ i) (pullU e' _ (w.s (fun _ => i.1, i.2))) * res (l₃ i) (a.s fun _ => i.2))⁻¹, fun Z r z i hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z (l₁ i) hz _).trans (gm_pull r h z _ (l₁ i hz) _))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res r z (l₂ i) hz _).trans (gm_pull r e' z _ (l₂ i hz) _)) (gm_res r z (l₃ i) hz _))))))⟩
  obtain ⟨c, hc⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F (e' y))
      obtain ⟨k, hk⟩ := exists_chart hL' (e' y)
      exact Opens.mem_iSup.2 ⟨(j, k), hj, hk⟩) u (fun i i' y hy => by
      rw [hu _ _ y i hy.1, hu _ _ y i' hy.2, gen_trans ht (𝟙 Y' ≫ h) y (l₁ i hy.1) (l₁ i' hy.2),
        gen_trans ha (𝟙 Y') y (l₃ i hy.1) (l₃ i' hy.2),
        hw _ (𝟙 Y' ≫ e') y i.1 i'.1 i.2 i'.2 hy.1.1 hy.2.1 hy.1.2 hy.2.2]
      simp only [trF, Fintype.prod_unique, zpow_one, Category.assoc, he]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  let w' : LB.Iso L' (L.pull F) := ⟨fun i => res (le_top : _ ≤ p ⁻¹ᵁ ⊤) (pullU p ⊤ c) * w.s i⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w' r z j k = gm (r ≫ p) z ⊤ c * gw w r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) ((gm_res r z _ (⟨mem_pull.2 hj, hk⟩ : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k)
      _).trans (gm_pull r p z ⊤ trivial c)))
  refine ⟨w', fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k hj hk => ?_⟩
  · rw [v Z r z j k hj hk, v Z r z j' k' hj' hk', hw Z r z j j' k k' hj hj' hk hk', mul_left_comm]
  · have hz : r z ∈ W (j PUnit.unit, k PUnit.unit) := ⟨hj _, hk _⟩
    rw [Fintype.prod_unique, zpow_one, v Z (r ≫ e') z _ _ (hj _) (hk _), Category.assoc, hp, Category.comp_id,
      ← gm_res r z le_top hz c, hc, hu Z r z _ hz, _root_.mul_assoc]
    exact (inv_mul_cancel_right _ _).symm

theorem exists_keyPB_of_isGrpPullback {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] (f : R →+* R')
    (x : KeyIn R') (y : KeyIn R) {φ : x.P.A.left ⟶ y.P.A.left} (h : IsGrpPullback x.P.A y.P.A (spMap f) φ)
    {w : LB.Iso x.P.L (y.P.L.pull φ)} (hw : PGen w) (hg : x.P.g = y.P.g) :
    ∃ th' hth' v' hv', KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hth', v', hv'⟩ y f := by
  have he : eSec x.P.A ≫ φ = spMap f ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  obtain ⟨w', g', m'⟩ := exists_rescale y.P.isLB x.P.isLB hw (p := x.P.A.hom) (Over.w η[x.P.A]) he x.rig_gen y.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down g' y.P.isLB x.P.isLB y.th
  have sq : ∀ i, (spMap (Chart.dualMapR f) ≫ (y.v i).left) ≫ y.P.A.hom = (epsR R').hom ≫ spMap f := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR R' ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (y.v i).left := fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange f h y.basis hv'
  refine ⟨th', SectionBaseChange.fibre_nonzero_of_pull x.P.isLB hth' h.1 y.th_ne, _, hb hg, φ, he, w', hg,
    Chart.dualMapR f, h, (isGen_iff _).2 g',
    (maps_iff w' _ (fun _ => eSec y.P.A) _ x.rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2 m',
    appLE_eq_of_stalk _ y.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_keyIn_pullback (hT : Out.SecTwistSt) {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (f : O →+* R)
    (P : Out.PolAV (Sp O)) (hg : 1 ≤ P.g) : ∃ (y : KeyIn R) (ψ : y.P.A.left ⟶ P.A.left) (w : LB.Iso y.P.L (P.L.pull ψ)),
      y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap f) ψ ∧ PGen w := by
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R) :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  obtain ⟨rig, hr⟩ := P'.rigid
  obtain ⟨th, hth⟩ := exists_sec_fibre_ne_zero hT P h.1
  obtain ⟨v, hv⟩ := exists_isLieBasis P'.A P'.smoothDim
  exact ⟨⟨P', hg, rig, hr, th, hth, v, hv⟩, φ, _, rfl, h, hw⟩

theorem exists_isLocalModel_of_integral : Out.SecTwistSt → ∀ (K : Type) [Field K] [NumberField K]
    (P₀ : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ P₀.A.left) (w : LB.Iso x.P.L (P₀.L.pull φ)),
    x.P.g = P₀.g → IsGrpPullback x.P.A P₀.A (spMap (algebraMap (𝓞 K) K)) φ → w.IsGen →
    ∃ oa od : HeightOneSpectrum (𝓞 K) → ℤ, ∀ 𝔭, ∃ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K),
      GlobalTheory.KeyPow.IsLocalModel x 𝔭 a M ∧ 𝔭.valuation K a = WithZero.exp (-oa 𝔭) ∧
        𝔭.valuation K M.det = WithZero.exp (-od 𝔭) := by
  intro hT K _ _ P₀ x φ w hg hφ hw
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ∃ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K),
      IsLocalModel x 𝔭 a M ∧ a ≠ 0 ∧ M.det ≠ 0 := fun 𝔭 => by
    let R := (𝔭.valuation K).integer
    let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => 𝔭.valuation_le_one r
    have hf : spMap (algebraMap R K) ≫ spMap f = spMap (algebraMap (𝓞 K) K) := (Spec.map_comp _ _).symm
    obtain ⟨y, ψ, w₀, hg₀, hψ, hw₀⟩ := exists_keyIn_pullback hT f P₀ (hg ▸ x.g_pos)
    have sq : φ ≫ P₀.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap f := by rw [Category.assoc, hf, hφ.1.w]
    obtain ⟨φ', rfl, h₂⟩ : ∃ φ' : x.P.A.left ⟶ y.P.A.left, φ' ≫ ψ = φ ∧
        φ' ≫ y.P.A.hom = x.P.A.hom ≫ spMap (algebraMap R K) := ⟨hψ.1.lift _ _ sq, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
    obtain ⟨w', T⟩ := exists_cancel P₀.isLB w₀ w hw₀ ((isGen_iff _).1 hw) y.P.isLB x.P.isLB
    obtain ⟨th', hth', v', hv', hPB⟩ := exists_keyPB_of_isGrpPullback (algebraMap R K) x y
      (hψ.cancel (hφ.congr hf.symm rfl) h₂) (T.pgen_cancel P₀.isLB hw₀ ((isGen_iff _).1 hw)) (hg.trans hg₀.symm)
    obtain ⟨a, M, ha, hM⟩ := exists_scalar_matrix hT x.P x.th th' x.th_ne x.basis hv'
    have := x.P.isAb.comm
    refine ⟨a, M, ⟨R, _, inferInstance, inferInstance, _,
      inferInstanceAs (IsFractionRing (𝔭.valuation K).valuationSubring K), y, th', hth', v', hv', fun r => r.2, ha, hM, hPB⟩,
      ?_, (((LieComb.lieComb_algebra K x.P.A _ x.v x.basis.1).2.2.2.2 M v' x.basis hM).1 hv').ne_zero⟩
    rintro rfl
    obtain ⟨z, -, hz⟩ := hth' (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hz
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  choose a M h ha hM using key
  refine ⟨fun 𝔭 => -WithZero.log (𝔭.valuation K (a 𝔭)), fun 𝔭 => -WithZero.log (𝔭.valuation K (M 𝔭).det),
    fun 𝔭 => ⟨a 𝔭, M 𝔭, h 𝔭, ?_, ?_⟩⟩
  · rw [neg_neg, WithZero.exp_log (by simpa using ha 𝔭)]
  · rw [neg_neg, WithZero.exp_log (by simpa using hM 𝔭)]

end GlobalTheory.KeyPow
