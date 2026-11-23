import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsSameScaleAtTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPointsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThInt

theorem spMap_comp_ring' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self' {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq' {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp' {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq' (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr' {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem thList_pull_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec G))} {m : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {K : Type} [Field K]
    (x : Sp R ⟶ S) (θ : SecAt G L x) (i : R →+* R') (j : R' →+* K) {N : ℕ}
    {pt : Fin N → (Over.mk (spMap j ≫ spMap i ≫ x) ⟶ G)} {c : Fin N → K}
    (H : ThList G L ρ m (spMap j ≫ spMap i ≫ x) (SecAt.pull G L (SecAt.pull G L θ i) j) pt c) :
    ∃ pt' : Fin N → (Over.mk (spMap (j.comp i) ≫ x) ⟶ G), ThList G L ρ m (spMap (j.comp i) ≫ x)
      (SecAt.pull G L θ (j.comp i)) pt' c := by
  simp only [SecAt.pull] at H ⊢
  rw [pullS_comp' G hL] at H
  refine thList_congr' θ (by rw [← Category.assoc, spMap_comp_ring']) _ _ ?_ H
  simp only [Over.comp_left, Over.homMk_left]
  rw [spMap_comp_ring']

end GlobalTheory.UMin.ThInt

namespace GlobalTheory.UMin

open GlobalTheory.UMin.ThInt in

theorem thetaInt_hasDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u → ∀ (M : RatModel o' Ω) (g : M.Z ⟶ PSpace o n), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ g = spMap (ratHull S.R).val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf o' Ω _ _ _ _ S ρ u hu M g hnorm hg
  haveI : CharZero Ω := ArithBase.char o'
  haveI : IsDedekindDomain o' := ArithBase.ded Ω
  haveI : IsAbelianScheme ρ.P.A := ρ.P.isAb
  haveI : IsCommMonObj ρ.P.A := IsAbelianScheme.comm
  set gd := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgd
  let vH : ratHull S.R →+* Ω := (ratHull S.R).val.toRingHom
  let v : S.R →+* Ω := S.R.val.toRingHom
  have hv : vH.comp (toRat S.R) = v := RingHom.ext fun _ => rfl
  let x₀ : Sp Ω ⟶ Sp S.R := spMap v ≫ 𝟙 (Sp S.R)
  let θ : SecAt ρ.P.A ρ.P.L x₀ := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o' Ω S ρ Ω v
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := hu
  haveI : IsAbelianScheme G := PolPull.isAbelianScheme_of_isGrpPullback ρ.P.isAb hα
  haveI : IsCommMonObj G := IsAbelianScheme.comm
  have hLG : (ρ.P.L.pull α).IsLB := pull_isLB ρ.P.isLB α
  have hU := Xo.univ.t.PP.isLB
  have hUr := Xo.univ.t.PP.rigGen

  have hdim := GlobalTheory.UMin.polFib_univ E H Dw l Xo c Ω (spMap vH ≫ u ≫ pullback.fst _ _)
  have hmv1 := GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback Xo.X (Sp (ratHull S.R)) Xo.univ.t.G Xo.univ.t.PP.L G (ρ.P.L.pull α) (u ≫ pullback.fst _ _) β
    hU hLG hβ hL gd Ω (spMap vH)
  have hmv2 := GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp (ratHull S.R)) ρ.P.A ρ.P.L G (ρ.P.L.pull α) (spMap (toRat S.R)) α
    ρ.P.isLB hLG hα (PolBaseChange.lbIso_refl hLG) gd Ω (spMap vH)
  have hPG : PolFib G (ρ.P.L.pull α) gd (spMap vH) := hmv1.1.2 hdim
  have hPF : PolFib ρ.P.A ρ.P.L gd x₀ := by
    have h := hmv2.1.1 hPG
    rwa [spMap_comp_ring', hv, ← Category.comp_id (spMap v)] at h

  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) Ω x₀ θ hm hn hPF

  obtain ⟨P', φG, hgP, hφG, hφGL⟩ := hPG
  have hPL : P'.L.IsLB := P'.isLB
  have hφGα : IsGrpPullback P'.A ρ.P.A x₀ (φG ≫ α) :=
    (hφG.comp hα).congr (by rw [spMap_comp_ring', hv]; exact (Category.comp_id _).symm) rfl
  have hφGβ : IsGrpPullback P'.A Xo.univ.t.G ((spMap vH ≫ u) ≫ pullback.fst _ _) (φG ≫ β) :=
    (hφG.comp hβ).congr (by rw [Category.assoc]) rfl
  have hLα : LBIso P'.L (ρ.P.L.pull (φG ≫ α)) :=
    LBIso.trans hPL (pull_isLB hLG φG) (pull_isLB ρ.P.isLB _) hφGL
      (GenSpread.lbIso_pull_of_lbIso (PolBaseChange.lbIso_refl hLG) φG rfl)
  have hLβ : LBIso P'.L (Xo.univ.t.PP.L.pull (φG ≫ β)) :=
    LBIso.trans hPL (pull_isLB ρ.P.isLB _) (pull_isLB hU _) hLα (GenSpread.lbIso_pull_comp φG rfl rfl hL)
  have hcrd := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr gd m n o (Xo.XF c)
    (pullback.fst _ _) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig Ω (spMap vH ≫ u) x₀ P' (φG ≫ β) (φG ≫ α) θ e hm hn hf
    ρ.P.isLB ρ.rig_gen hgP hφGβ hLβ hφGα hLα hθ he
  have hdiv : M.HasDiv e := by
    refine GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords o' Ω o M n g e ?_
    rw [hg, ← Category.assoc]
    exact hcrd

  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hkodd : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact (ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)
  have hk3 : 3 ≤ S.r * S.N := by
    have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
    obtain ⟨t, ht⟩ := hkodd
    omega
  refine GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points o' Ω M S.Gam (Fin (n + 1)) S.th e (n + 1).factorial (Nat.factorial_pos _) hnorm hdiv ?_
  intro V _ _ _ hV ξ emb _ j₀ hj₀ hej
  haveI : IsDiscreteValuationRing V := hV.1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let i : Ω →+* K := io.comp emb
  have hcast : ∀ t : ℕ, t ≠ 0 → (t : K) ≠ 0 := fun t ht => by
    rw [← map_natCast i t]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 ht)
  have hmV : IsUnit (m : V) := by
    simpa using hmu.map (Spec.preimage (ξ ≫ g ≫ PSpace.str o n)).hom
  have hkV : IsUnit ((S.r * S.N : ℕ) : V) := by
    simpa using S.unit.map (Spec.preimage (ξ ≫ M.s)).hom

  have hPK : PolFib ρ.P.A ρ.P.L gd (spMap i ≫ x₀) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self' _)
      (ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) gd Ω x₀).2 K i hPF
  have hθK := (GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable (Sp S.R) ρ.P.A ρ.P.L ρ.P.isLB gd Ω x₀ hPF).2 θ hθ K i
  obtain ⟨pt, d, hd⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) K (spMap i ≫ x₀)
    (SecAt.pull ρ.P.A ρ.P.L θ i) hm (hcast m hm.pos.ne') hn hPK
  obtain ⟨pt', d', hd'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd (S.r * S.N)
    ((S.r * S.N) ^ (4 * gd)) K (spMap i ≫ x₀) (SecAt.pull ρ.P.A ρ.P.L θ i) hkodd (hcast _ (NeZero.ne _)) rfl hPK
  have hsym : ∀ j, io (emb (e j)) = symTup d j := he K i pt d hd
  obtain ⟨pt'', hd''⟩ := thList_pull_pull ρ.P.isLB (𝟙 (Sp S.R)) ρ.th₁ v i hd'
  have hT := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o' Ω S ρ K (i.comp v) _ pt'' d' hd''

  have h₁ : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap i ≫ x₀) d d' := ⟨_, pt, pt', hθK, hd, hd'⟩
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hLG
  obtain ⟨ρG, hρG, -⟩ := exists_rigidificationPullbackCompatibleIso hα hw ρ.P.isLB hLG ρ.rig_gen
  let xV : Sp K ⟶ Sp (ratHull S.R) := spMap io ≫ spMap emb ≫ spMap vH
  have hxV : spMap i ≫ x₀ = xV ≫ spMap (toRat S.R) := by
    simp only [xV, x₀, i, Category.comp_id, Category.assoc, spMap_comp_ring', ← hv, RingHom.comp_assoc]
  rw [hxV] at h₁
  have h₂ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (spMap (toRat S.R)) α hLG hρG hα (PolBaseChange.lbIso_refl hLG) m (S.r * S.N) (n + 1) _ K xV d d').2 h₁
  have h₃ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (u ≫ pullback.fst _ _) β hLG hρG hβ hL m (S.r * S.N) (n + 1) _ K xV d d').1 h₂
  let y : Sp (FractionRing V) ⟶ Xo.XF c := spMap emb ≫ spMap vH ≫ u
  have h₄ : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (S.r * S.N) (spMap io ≫ y ≫ pullback.fst _ _) d d' := by
    have e₄ : spMap io ≫ y ≫ pullback.fst _ _ = xV ≫ u ≫ pullback.fst _ _ := by
      simp only [xV, y, Category.assoc]
    rw [e₄]
    exact h₃
  obtain ⟨a, ha, hPa, hPa'⟩ := GlobalTheory.T.thetaConstants_two_levels_same_scale_at_trait E H Dw l Xo c V hV y K io m (S.r * S.N) (n + 1) _ d d' hm hm3 hmV hkodd hk3
    hkV h₄
  have hP := GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare V K io (n + 1) _ ((S.r * S.N) ^ 2) S.Gam d d' a (fun j => emb (e j)) (fun b => emb (S.th b)) ha
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne _))) hPa hPa' hsym hT.1 hT.2 j₀ ((map_ne_zero emb).2 hj₀)
    (fun j => by simpa [map_div₀] using hej j)
  refine ⟨fun b => by simpa [map_div₀, map_pow] using hP.1 b, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hP.2
  exact ⟨b, fun h0 => hb (by simp [h0]), by simpa [map_div₀, map_pow] using hb'⟩

end GlobalTheory.UMin
