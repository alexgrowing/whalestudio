import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.ThetaDegree

def IsPullOf {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (t : LB.Gen (P.L.pull (eSec P.A))) (θ : P.L.Sec) (y : KeyIn R) : Prop :=
  ∃ (ψ : y.P.A.left ⟶ P.A.left) (w : LB.Iso y.P.L (P.L.pull ψ)), y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap f) ψ ∧
    PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec y.P.A) (fun _ => eSec P.A) (fun _ => 1) y.rig t (spMap f) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ y.P.A.left) (z : Z) j k, ψ (r z) ∈ P.L.U j → r z ∈ y.P.L.U k →
      gs (r ≫ ψ) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (y.th.f k)

theorem exists_isPullOf {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (hg : 1 ≤ P.g) {t : LB.Gen (P.L.pull (eSec P.A))} (ht : t.IsGen) (θ : P.L.Sec)
    (hθ : ∀ s : Sp R, ∃ z, P.A.hom z = spMap f s ∧ z ∈ Out.nonzeroLocus θ) : ∃ y : KeyIn R, IsPullOf f P t θ y := by
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
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he P.L t).IsGen :=
    Out.LBxP.isGen_pullAlong P.L φ (spMap f) (fun _ : PUnit => eSec P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) t ht
  obtain ⟨th', hth'⟩ := sec_pull_down hw P.isLB hL' θ
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis P'.A P'.smoothDim
  refine ⟨⟨P', hg, _, hr, th', fun s => ?_, v, hv⟩, φ, idIso _, rfl, h, hw,
    (maps_iff (idIso _) (fun _ => eSec P'.A) (fun _ => eSec P.A) _ _ t (spMap f) _ (rigPull_le φ (spMap f) he P.L)
      (fun _ => rfl)).1 (fun p => hr p.1 p.2), hth'⟩
  obtain ⟨z, hz, hz'⟩ := hθ s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (θ.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem IsPullOf.exists_keyPB {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [CommRing R'] {f : O →+* R}
    {g : R →+* R'} {P : Out.PolAV (Sp O)} {t : LB.Gen (P.L.pull (eSec P.A))} {θ : P.L.Sec} {y : KeyIn R} {x : KeyIn R'}
    (hy : IsPullOf f P t θ y) (hx : IsPullOf (g.comp f) P t θ x) :
    ∃ v' hv', KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv'⟩ y g := by
  obtain ⟨ψ, w, hg, hc, hw, hr, hs⟩ := hy
  obtain ⟨φ'', w'', hg'', hc'', hw'', hr'', hs''⟩ := hx
  have hsp : spMap (g.comp f) = spMap g ≫ spMap f := (spMap_comp_spMap f g).symm
  obtain ⟨φ, rfl, hw0⟩ : ∃ φ : x.P.A.left ⟶ y.P.A.left, φ ≫ ψ = φ'' ∧ φ ≫ y.P.A.hom = x.P.A.hom ≫ spMap g :=
    ⟨hc.1.lift φ'' (x.P.A.hom ≫ spMap g) (by rw [hc''.1.w, Category.assoc, hsp]), hc.1.lift_fst _ _ _,
      hc.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap g) φ := hc.cancel (hc''.congr hsp rfl) hw0
  have he : eSec x.P.A ≫ φ = spMap g ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' hw hw'' y.P.isLB x.P.isLB
  rw [hsp] at hr''
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR g) ≫ (y.v i).left) ≫ y.P.A.hom = (epsR R').hom ≫ spMap g := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR R' ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR g) ≫ (y.v i).left := fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange g h y.basis hv'
  have hg' : x.P.g = y.P.g := hg''.trans hg.symm
  refine ⟨_, hb hg', φ, he, w', hg', Chart.dualMapR g, h, (isGen_iff _).2 (T.pgen_cancel P.isLB hw hw''),
    (maps_iff w' _ (fun _ => eSec y.P.A) _ x.rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2
      (T.pmaps_cancel P.isLB (fun _ => he) hr hr''),
    KeyPow.appLE_eq_of_stalk _ y.th x.th fun z i k hi hk => ?_, fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨j, hj⟩ := exists_chart P.isLB (ψ (φ z))
    have a := hs _ (𝟙 _ ≫ φ) z j i hj hi
    have b := hs'' _ (𝟙 _) z j k hj hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_sec_generic (hT : Out.SecTwistSt) {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (P : Out.PolAV (Sp O)) {X : Scheme.{0}} {φ : X ⟶ P.A.left} {q : X ⟶ Sp K}
    (hp : IsPullback φ q P.A.hom (spMap (algebraMap O K))) : ∃ (θ : P.L.Sec) (z : X), φ z ∈ Out.nonzeroLocus θ := by
  have := P.isAb.smooth
  have := P.isAb.proper
  obtain ⟨s, hs⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨d, hd, θ, hθ⟩ := SecSpread.exists_spread hp P.isLB s
  obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hk' : φ z ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  have hu : IsUnit (gs φ z _ (θ.f (k PUnit.unit))) := by
    rw [hθ _ z hk']
    exact (SecSpread.isUnit_cst hp.w z hd).mul u
  rw [gs_stalkMap φ z _ hk', isUnit_map_iff] at hu
  exact ⟨θ, z, (mem_nonzeroLocus _ _).2 ⟨_, hk', hu⟩⟩

variable {K : Type} [Field K] [NumberField K]

theorem exists_scalar (hT : Out.SecTwistSt) (P : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ P.A.left)
    (w : LB.Iso x.P.L (P.L.pull φ)) (hg : x.P.g = P.g)
    (hφ : IsGrpPullback x.P.A P.A (spMap (algebraMap (𝓞 K) K)) φ) (hw : w.IsGen) :
    ∃ a : K, a ≠ 0 ∧ {𝔭 | ¬ ∃ M, KeyPow.IsLocalModel x 𝔭 a M}.Finite := by
  have := P.isAb.smooth
  obtain ⟨θ, z₀, hz₀⟩ := exists_sec_generic hT P hφ.1
  obtain ⟨t, ht⟩ := P.rigid
  obtain ⟨w', g', m'⟩ := KeyPow.exists_rescale P.isLB x.P.isLB ((isGen_iff _).1 hw) (p := x.P.A.hom) (Over.w η[x.P.A])
    (PolBaseChange.eSec_comm hφ) x.rig_gen ht
  obtain ⟨th', hth'⟩ := sec_pull_down g' P.isLB x.P.isLB θ
  have hne : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th' := fun s => by
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz₀
    obtain ⟨k, hk⟩ := exists_chart x.P.isLB z₀
    refine ⟨z₀, Subsingleton.elim (α := PrimeSpectrum K) _ _, (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ z₀ _ (θ.f j)) := by rw [gs_stalkMap φ z₀ _ hj]; exact u.map _
    have e := hth' _ (𝟙 _) z₀ j k hj hk
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  let x' : KeyIn K := ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hne, x.v, x.basis⟩
  have hx' : IsPullOf (algebraMap (𝓞 K) K) P t θ x' := ⟨φ, w', hg, hφ, g', m', hth'⟩
  obtain ⟨a, -, ha, -⟩ := KeyPow.exists_scalar_matrix hT x.P x.th th' x.th_ne x.basis x.basis
  obtain ⟨_, ⟨d, rfl⟩, hd, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_image_of_mem P.A.hom hz₀) (P.A.hom.isOpenMap _ (Out.nonzeroLocus θ).isOpen)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hd (Ideal.zero_mem _)
  refine ⟨a, ?_, (Ideal.finite_factors (I := Ideal.span {d}) (by simpa using hd0)).subset fun 𝔭 h𝔭 => ?_⟩
  · rintro rfl
    obtain ⟨z, -, hz⟩ := hne (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  by_contra hn
  refine h𝔭 ?_
  have hv : 𝔭.valuation K (algebraMap (𝓞 K) K d) = 1 := by
    refine (𝔭.valuation_le_one d).antisymm (not_lt.1 fun h => hn ?_)
    exact (𝔭.valuation_lt_one_iff_dvd d).1 h
  let R := (𝔭.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => 𝔭.valuation_le_one r
  have hu : IsUnit (f d) := (Valuation.integer.integers (𝔭.valuation K)).isUnit_iff_valuation_eq_one.2 hv
  obtain ⟨y, hy⟩ := exists_isPullOf f P (hg ▸ x.g_pos) ht θ fun s => by
    have hs : spMap f s ∈ (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum (𝓞 K))) := fun h =>
      s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f d ∈ s.asIdeal from h) hu)
    obtain ⟨z, h₁, h₂⟩ := hsub hs
    exact ⟨z, h₂, h₁⟩
  obtain ⟨v', hv', hPB⟩ := hy.exists_keyPB (g := algebraMap R K) (x := x') hx'
  choose M hM using fun i => (x.basis.2 _ (hv'.1 i)).exists
  exact ⟨M, R, _, inferInstance, inferInstance, _,
    inferInstanceAs (IsFractionRing (𝔭.valuation K).valuationSubring K), y, th', hne, v', hv', fun r => r.2, ha, hM, hPB⟩

theorem exists_isThetaDeg : Out.SecTwistSt → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K]
    (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth), ∃ δ : ℝ, IsThetaDeg (F.key hg rig hr th hth) δ := by
  intro hT hU K _ _ P F hg rig hr th hth
  classical
  obtain ⟨e, hφ, hL⟩ := F.fib
  obtain ⟨w, hw⟩ := LBIso.symm hL
  let x := F.key hg rig hr th hth
  obtain ⟨oa, od, hloc⟩ := KeyPow.exists_isLocalModel_of_integral hT K P x F.φ w e hφ hw
  obtain ⟨a, ha, hfin⟩ := exists_scalar hT P x F.φ w e hφ hw
  obtain ⟨nth, nη, hn⟩ := KeyPow.exists_archNorms hU x
  have hv : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.valuation K a = WithZero.exp (- -WithZero.log (𝔭.valuation K a)) :=
    fun 𝔭 => by rw [neg_neg, WithZero.exp_log (by simpa using ha)]
  refine ⟨_, fun 𝔭 => if ∃ M, KeyPow.IsLocalModel x 𝔭 a M then -WithZero.log (𝔭.valuation K a) else oa 𝔭, nth,
    fun 𝔭 => ?_, fun σ => ?_, (hfin.union (KeyPow.sum_log_norm_eq_finsum ha _ hv).1).subset fun 𝔭 h => ?_, rfl⟩
  · by_cases h : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · obtain ⟨M, hM⟩ := id h
      exact ⟨a, M, hM, by beta_reduce; rw [if_pos h]; exact hv 𝔭⟩
    · obtain ⟨a', M, hM, h₁, -⟩ := hloc 𝔭
      exact ⟨a', M, hM, by beta_reduce; rw [if_neg h]; exact h₁⟩
  · obtain ⟨x', h₁, h₂⟩ := hn σ
    exact ⟨x', _, h₁, h₂⟩
  · by_cases h' : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · exact Or.inr (by simpa only [Function.mem_support, if_pos h'] using h)
    · exact Or.inl h'

end GlobalTheory.ThetaDegree

end
