import Mathlib
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomogenisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HilbEqFinrankQuotPiece
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValHomEq
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.DegreeFormsDimensionAbelianConeLe
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.MemVanishingIdealOfFormVanishingTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsoOfEqualCoordinateConesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsClosedImmersionOfSpanLinePowerSectionsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.HomogeneousCoordsOfIsValueAtFrameStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoPullOfHomPreservingCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCosetStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LevelBasisEqOfSameThetaPtStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelThetaPtOfPolarisedIsoStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDet

theorem cone_subset (h : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) {g N k : ℕ}
    (hg : P.g = g) (hg' : P'.g = g) (hN : 4 ≤ N) (hk : (k : K) ≠ 0) (hb : N ^ g * g.factorial < k) {J : Type}
    [Fintype J] {s : J → (lbPow P.L N).Sec} {s' : J → (lbPow P'.L N).Sec}
    (hs : ImmBy P.A.hom _ s Set.univ) (hs' : ImmBy P'.A.hom _ s' Set.univ)
    (hx : ∀ x : Out.baseOver (Sp K) ⟶ P'.A, x ^ k = 1 →
      ∃ v : J → K, Crd (lbPow P'.L N) s' (x.left : Sp K ⟶ P'.A.left) v ∧ v ∈ cone P.A.hom _ s) :
    cone P'.A.hom _ s' ⊆ cone P.A.hom _ s := by
  intro w hw
  have hLB : (lbPow P.L N).IsLB := isLB_lbPow P.isLB N
  have hsm : SmoothOfRelativeDimension g P.A.hom := by
    rw [← hg]
    exact P.smoothDim
  obtain ⟨hpr, hhom, hX, hdim⟩ := ZH.ConePrime.isPrime_vanishingIdeal_cone K P.A.left P.A.hom (lbPow P.L N) J s
    Set.univ hLB hs (polAV_isIntegral_of_isAlgClosed K P) g hsm
  have hnz : ∃ i ∈ (Set.univ : Set J), w i ≠ 0 := by
    obtain ⟨x, -, hxw⟩ := hw
    have h1 : ⊤ ≤ x ⁻¹ᵁ (⨆ i ∈ (Set.univ : Set J), Out.nonzeroLocus (s' i)) := by
      rw [hs'.1]
      simp
    simp only [Set.mem_univ, iSup_pos] at h1
    have h2 := (ZH.CrdCalc.top_le_iff x _).1 h1
    rw [TopologicalSpace.Opens.mem_iSup] at h2
    obtain ⟨i, hi⟩ := h2
    exact ⟨i, Set.mem_univ _, ((ZH.CrdCalc.crd_isUnit_iff i hxw).2 ((ZH.CrdCalc.top_le_iff x _).2 hi)).ne_zero⟩
  refine ZH.ConeClosed.mem_cone_of_vanishing K P.A.left P.A.hom (lbPow P.L N) J s Set.univ hLB hs w hnz ?_
  intro Pf hPf
  refine ZH.eval_eq_zero_of_hilb_le K J _ g N hpr hhom hX hdim ?_ w ?_ Pf hPf
  · intro d hd
    have := AbelianFormCount.hilb_cone_le h K P N J s d (by omega) hd
    rwa [hg] at this
  · intro d F hd hF hFI
    have hFI' : F ∈ MvPolynomial.vanishingIdeal K (cone P'.A.hom (lbPow P'.L N) s') := by
      refine T.mem_vanishingIdeal_of_form_vanishing_torsion h K P' N d k J s' F hN hk ?_ hF ?_
      · rw [hg']
        calc N ^ g * g.factorial * d ≤ N ^ g * g.factorial * (N ^ g * g.factorial) := Nat.mul_le_mul_left _ hd
          _ < k * k := Nat.mul_self_lt_mul_self hb
          _ = k ^ 2 := (sq k).symm
      · intro x hx1
        obtain ⟨v, hv, hvC⟩ := hx x hx1
        exact ⟨v, hv, MvPolynomial.mem_vanishingIdeal_iff.1 hFI v hvC⟩
    exact MvPolynomial.mem_vanishingIdeal_iff.1 hFI' w hw

theorem levelPoint_zero {S : Scheme.{0}} {P : Out.PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Out.Level P M ze) {g : ℕ}
    (hg : P.g = g) : levelPoint lev hg 0 = 1 := by
  rw [ThetaPtDet.levelPoint_eq]
  simp [ReciprocityTheory.ChartRestriction.G.Out.linComb]

theorem levelPoint_single {S : Scheme.{0}} {P : Out.PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Out.Level P M ze) {g : ℕ}
    (hg : P.g = g) (i : Fin (2 * g)) : levelPoint lev hg (Pi.single i 1) = levelBasis lev hg i := by
  rw [ThetaPtDet.levelPoint_eq, ReciprocityTheory.ChartRestriction.G.Out.linComb, List.prod_ofFn,
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  have ht : levelBasis lev hg i ^ M = 1 := lev.torsion _
  rw [Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 ht, pow_one]

theorem exists_embedding (h : Out.Laws) {g m r N N' : ℕ} (hN : N = m ^ 2) (hN' : N' = r * m) (h4 : 4 ≤ N) {K : Type}
    [Field K] [IsAlgClosed K] (hK : (N' : K) ≠ 0) [NeZero (N' ^ 2)] (P : Out.PolAV (Sp K)) (hg : P.g = g)
    {ze : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ} (lev : Out.Level P (N' ^ 2) ze)
    {v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)}
    (hv : Out.IsThetaPt P N' (levelPoint lev hg) v) :
    ∃ (s : (Fin (2 * g) → ZMod (N' ^ 2)) → (lbPow P.L N).Sec) (θ : (lbPow P.L 1).Sec),
      ImmBy P.A.hom _ s Set.univ ∧
      (∀ c, Crd (lbPow P.L N) s ((levelPoint lev hg c ^ N').left : Sp K ⟶ P.A.left)
        fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
          ((ze ^ thetaCoordExp m r a c).val * v (thetaCoordIdx m r a c))) ∧
      (∃ l, θ.f l ≠ 0) ∧ ∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l →
        Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s 0).f k))
          (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) (θ.f l)) := by
  have hodd : Odd N' := hv.1
  obtain ⟨⟨th, t, hth, htf⟩, hform⟩ := (theta_coordinates h g m r N N' hN hN').1 (Sp K) P hg ze lev v hv
  obtain ⟨hcoord, -⟩ := hform th t hth htf
  obtain ⟨-, -, hrest⟩ := (theta_coordinates h g m r N N' hN hN').2 K hodd hK P hg ze lev
  obtain ⟨hspan, -, -⟩ := hrest th t hth htf
  obtain ⟨ρ, e⟩ : ∃ ρ : P.A.left ⟶ (Out.baseOver (Sp K) ⊗ P.A).left,
      ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left :=
    ⟨(lift (Over.homMk P.A.hom (by simp [Out.baseOver])) (𝟙 P.A)).left, by rw [← Over.comp_left, lift_snd]; rfl⟩
  obtain ⟨hθ, hassoc⟩ := T.thetaFamily_origin_germ_of_multiplication h K P N m _ (fun a => levelPoint lev hg a ^ r ^ 2) th t ρ e 0 hth htf
    (by rw [levelPoint_zero, one_pow])
  refine ⟨fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e (N : ℤ) (t a),
    PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) th,
    T.isClosedImmersion_of_span_linePowerSections h K P N _ t ρ e h4 hspan, ?_, hθ, hassoc⟩
  intro c
  obtain ⟨u, hu⟩ := hcoord c _ (DVR.exists_gen_of_local (V := K) P.L P.isLB _ _).choose_spec
  have hc := T.homogeneousCoords_of_isValueAt_frame K P N _ t ρ e (levelPoint lev hg c ^ N') _ _ hu
  set φ := CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of K)).hom with hφ
  have hu1 : φ ((u⁻¹ : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ) : Γ((Out.baseOver (Sp K)).left, ⊤)) * φ (u : Γ((Out.baseOver (Sp K)).left, ⊤)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  convert ZH.CrdCalc.crd_smul (Units.map φ.toMonoidHom u⁻¹) hc using 1
  funext a
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_mul, map_mul]
  linear_combination (-(φ ((ze ^ thetaCoordExp m r a c : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ) : Γ((Out.baseOver (Sp K)).left, ⊤)) * φ (v (thetaCoordIdx m r a c)))) * hu1

end GlobalTheory.ThetaDet

namespace GlobalTheory

open ThetaDet in

theorem thetaPt_determines : Out.Laws → ThetaPtDeterminesSt := by
  intro h g n k j N N' hn hodd hk hN hN' hb K _ _ hn0 P P' hg hg' ze lev lev' v hv hv'
  haveI := P.isAb
  haveI := P'.isAb
  haveI : IsProper P.A.hom := IsAbelianScheme.proper
  haveI : IsProper P'.A.hom := IsAbelianScheme.proper
  haveI : AlgebraicGeometry.IsIntegral P.A.left := polAV_isIntegral_of_isAlgClosed K P
  haveI : AlgebraicGeometry.IsIntegral P'.A.left := polAV_isIntegral_of_isAlgClosed K P'
  have hN'' : N' = n ^ j * n ^ k * n ^ k := by rw [hN', hN]; ring
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := by
      rintro rfl
      exact (by decide : ¬ Odd 2) hodd
    omega
  have h4 : 4 ≤ N := by
    have h1 : 3 ≤ n ^ k := le_trans hn3 (Nat.le_self_pow (by omega) n)
    rw [hN]
    nlinarith
  have hK : ((N' : ℕ) : K) ≠ 0 := by
    rw [hN'']
    push_cast
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn0) (pow_ne_zero _ hn0)) (pow_ne_zero _ hn0)
  have hN'0 : N' ≠ 0 := by
    rintro h0
    rw [h0, Nat.cast_zero] at hK
    exact hK rfl
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hN'0⟩
  have hoddN' : Odd N' := hv.1
  obtain ⟨s, θ, hs, hcrd, hθ, hass⟩ := ThetaDet.exists_embedding h hN hN'' h4 hK P hg lev hv
  obtain ⟨s', θ', hs', hcrd', hθ', hass'⟩ := ThetaDet.exists_embedding h hN hN'' h4 hK P' hg' lev' hv'
  have hcone1 : cone P'.A.hom _ s' ⊆ cone P.A.hom _ s := by
    refine ThetaDet.cone_subset h P P' hg hg' h4 hK hb hs hs' ?_
    intro x hx
    obtain ⟨c, rfl⟩ := ((theta_coordinates h g (n ^ k) (n ^ j * n ^ k) N N' hN hN'').2 K hoddN' hK P' hg' ze
      lev').2.1 x |>.1 hx
    exact ⟨_, hcrd' c, _, Over.w _, hcrd c⟩
  have hcone2 : cone P.A.hom _ s ⊆ cone P'.A.hom _ s' := by
    refine ThetaDet.cone_subset h P' P hg' hg h4 hK hb hs' hs ?_
    intro x hx
    obtain ⟨c, rfl⟩ := ((theta_coordinates h g (n ^ k) (n ^ j * n ^ k) N N' hN hN'').2 K hoddN' hK P hg ze
      lev).2.1 x |>.1 hx
    exact ⟨_, hcrd c, _, Over.w _, hcrd' c⟩
  obtain ⟨φ, hφ⟩ := T.exists_iso_of_equal_coordinateCones K P.A P'.A (lbPow P.L N) (lbPow P'.L N) _ s s' (isLB_lbPow P.isLB N)
    (isLB_lbPow P'.isLB N) hs hs' (Set.Subset.antisymm hcone2 hcone1)
  have heq : ∀ c, (levelPoint lev hg c ^ N') ≫ φ.hom = levelPoint lev' hg' c ^ N' := by
    intro c
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact ZH.ImmSep.eq_of_crd_eq K P'.A.left P'.A.hom (lbPow P'.L N) _ s' Set.univ (isLB_lbPow P'.isLB N) hs' K
      _ _ _ (by rw [Category.assoc, Over.w φ.hom, Over.w, Over.w]) (hφ K _ _ (hcrd c)) (hcrd' c)
  have hη : η ≫ φ.hom = η := by
    have h0 := heq 0
    rw [ThetaDet.levelPoint_zero, ThetaDet.levelPoint_zero, one_pow, one_pow] at h0
    have e1 : (1 : Out.baseOver (Sp K) ⟶ P.A) = η := Over.OverMorphism.ext rfl
    have e2 : (1 : Out.baseOver (Sp K) ⟶ P'.A) = η := Over.OverMorphism.ext rfl
    rw [e1, e2] at h0
    exact h0
  haveI hmon : IsMonHom φ.hom := h.rigidity (Sp K) P.A P'.A P.isAb P'.isAb φ.hom hη
  have hLBiso := T.lbIso_pull_of_hom_preserving_coordinates h K P P' N (n ^ k) _ s s' 0 θ θ' φ.hom
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by omega))) hmon
    (by simpa only [Set.mem_univ, iSup_pos] using hs.1) (fun F _ y w hw => hφ F y w hw) hθ hass hass'
  have hpol : IsPolIso P P' φ := ⟨hmon, hLBiso⟩
  obtain ⟨lev'', hb'', hv''⟩ := T.exists_level_thetaPt_of_polarisedIso h g N' K P P' hg hg' φ hpol ze lev' v hv'
  have hnv := T.thetaPt_support_meets_every_coset h g n N' hn.two_le (by rw [hN'']; exact Dvd.dvd.mul_left (pow_dvd_pow n hk) _) K P hg ze
    lev v hv
  have hpowN : N' = n ^ (j + 2 * k) := by rw [hN'']; ring
  have hpw : ∀ i, levelBasis lev hg i ^ N' = levelBasis lev'' hg i ^ N' := by
    intro i
    apply (cancel_mono φ.hom).1
    rw [pow_comp, pow_comp, hb'' i, ← pow_comp, ← ThetaDet.levelPoint_single lev hg i, heq,
      ThetaDet.levelPoint_single]
  refine ⟨φ, hpol, fun i => ?_⟩
  rw [T.levelBasis_eq_of_same_thetaPt h g n (j + 2 * k) N' hodd hpowN K P hg ze lev lev'' v hv hv'' hpw hnv i, hb'' i]

end GlobalTheory
