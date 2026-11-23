import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_keyPB_ring {R R' : Type} [CommRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R') :
    ∃ x' : KeyIn R', KeyPB x' x f := by
  have h := isGrpPullback_pullback x.P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left := pullback.fst x.P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB x.P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj x.P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb
      g := x.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 x.P.smoothDim
      L := x.P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h x.P.rigid
      sym := PolBaseChange.sym_pull h x.P.sym
      ample := relAmple_pull h.1 x.P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
      ktriv := kTriv_pull h x.P.isLB hL' hw x.P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R R' f x.P.A P'.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  refine ⟨⟨P', x.g_pos, _, hr, th', fun s => ?_, v', hb'⟩,
    φ, he, idIso _, rfl, Chart.dualMapR f, h, idIso_isGen hL', fun p => hr p.1 p.2,
    appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, hv'⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem keyIn_baseChange : Out.PolBaseChangeSt → ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R'),
    ∃ x' : KeyIn R', KeyPB x' x f :=
  fun _ _ _ _ _ x f => exists_keyPB_ring x f

end GlobalTheory.KeyPow
