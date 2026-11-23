import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.BaseCh

variable {K K' : Type} [Field K] [Field K']

abbrev prj (x : KeyIn K) (f : K →+* K') : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left :=
  pullback.fst x.P.A.hom (spMap f)

theorem isGrpPullback_prj (x : KeyIn K) (f : K →+* K') :
    IsGrpPullback ((Over.pullback (spMap f)).obj x.P.A) x.P.A (spMap f) (prj x f) :=
  isGrpPullback_pullback x.P.A (spMap f)

def pol (x : KeyIn K) (f : K →+* K') : Out.PolAV (Sp K') :=
  { A := (Over.pullback (spMap f)).obj x.P.A
    isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb
    g := x.P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (isGrpPullback_prj x f).1
      x.P.smoothDim
    L := x.P.L.pull (prj x f)
    isLB := pull_isLB x.P.isLB (prj x f)
    rigid := PolBaseChange.rigidified_pull (isGrpPullback_prj x f) x.P.rigid
    sym := PolBaseChange.sym_pull (isGrpPullback_prj x f) x.P.sym
    ample := relAmple_pull (isGrpPullback_prj x f).1 x.P.isLB (pull_isLB x.P.isLB (prj x f))
      ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
    ktriv := kTriv_pull (isGrpPullback_prj x f) x.P.isLB (pull_isLB x.P.isLB (prj x f))
      ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) x.P.ktriv }

theorem eSec_prj (x : KeyIn K) (f : K →+* K') : eSec (pol x f).A ≫ prj x f = spMap f ≫ eSec x.P.A :=
  PolBaseChange.eSec_comm (isGrpPullback_prj x f)

theorem exists_th (x : KeyIn K) (f : K →+* K') :
    ∃ s' : (pol x f).L.Sec, ∀ (Z : Scheme) (r : Z ⟶ (pol x f).A.left) (z : Z) (j : x.P.L.ι) (k : (pol x f).L.ι),
      prj x f (r z) ∈ x.P.L.U j → r z ∈ (pol x f).L.U k →
        gs (r ≫ prj x f) z (x.P.L.U j) (x.th.f j) = ↑(gw (idIso (pol x f).L) r z j k) * gs r z ((pol x f).L.U k) (s'.f k) :=
  sec_pull_down ((isGen_iff _).1 (idIso_isGen (pull_isLB x.P.isLB (prj x f)))) x.P.isLB (pull_isLB x.P.isLB (prj x f)) x.th

def th (x : KeyIn K) (f : K →+* K') : (pol x f).L.Sec := Classical.choose (exists_th x f)

theorem th_spec (x : KeyIn K) (f : K →+* K') (Z : Scheme) (r : Z ⟶ (pol x f).A.left) (z : Z) (j : x.P.L.ι)
    (k : (pol x f).L.ι) (hj : prj x f (r z) ∈ x.P.L.U j) (hk : r z ∈ (pol x f).L.U k) :
    gs (r ≫ prj x f) z (x.P.L.U j) (x.th.f j) = ↑(gw (idIso (pol x f).L) r z j k) * gs r z ((pol x f).L.U k) ((th x f).f k) :=
  Classical.choose_spec (exists_th x f) Z r z j k hj hk

def rig (x : KeyIn K) (f : K →+* K') : ((pol x f).L.pull (eSec (pol x f).A)).Gen :=
  rigPullOf (G' := (pol x f).A) (G := x.P.A) (prj x f) (spMap f) (eSec_prj x f) x.P.L x.rig

theorem rig_isGen (x : KeyIn K) (f : K →+* K') : (rig x f).IsGen :=
  Out.LBxP.isGen_pullAlong x.P.L (prj x f) (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1)
    (fun _ => eSec (pol x f).A) (fun _ => eSec_prj x f) x.rig x.rig_gen

theorem vec_sq (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) :
    (spMap (Chart.dualMapR f) ≫ (x.v i).left) ≫ x.P.A.hom = (epsR K').hom ≫ spMap f := by
  rw [Category.assoc, Over.w]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

def vec (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) : epsR K' ⟶ (pol x f).A :=
  Over.homMk ((isGrpPullback_prj x f).1.lift _ _ (vec_sq x f i)) ((isGrpPullback_prj x f).1.lift_snd _ _ _)

theorem vec_prj (x : KeyIn K) (f : K →+* K') (i : Fin x.P.g) :
    (vec x f i).left ≫ prj x f = spMap (Chart.dualMapR f) ≫ (x.v i).left :=
  (isGrpPullback_prj x f).1.lift_fst _ _ _

theorem th_ne (x : KeyIn K) (f : K →+* K') (s : Sp K') :
    ∃ y, (pol x f).A.hom y = s ∧ y ∈ nonzeroLocus (th x f) := by
  have h := isGrpPullback_prj x f
  obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs (prj x f) y _ (x.th.f k)) := by rw [gs_stalkMap (prj x f) y _ hk]; exact u.map _
  have e := th_spec x f _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  erw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

def key (x : KeyIn K) (f : K →+* K') : KeyIn K' :=
  ⟨pol x f, x.g_pos, rig x f, rig_isGen x f, th x f, th_ne x f, vec x f,
    by have := x.P.isAb.smooth; exact Chart.isLieBasis_baseChange f (isGrpPullback_prj x f) x.basis (vec_prj x f)⟩

theorem powIso_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (n : ℕ)
    (p : (LB.div (lbPow (L.pull φ) n) ((lbPow L n).pull φ)).ι) :
    (LB.div (lbPow (L.pull φ) n) ((lbPow L n).pull φ)).U p ≤
      φ ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p.2 PUnit.unit PUnit.unit)) := by
  intro y hy
  obtain ⟨h1, h2⟩ := hy
  have a1 := Set.mem_iInter.1 (Set.mem_iInter.1 h1 PUnit.unit) PUnit.unit
  have a2 := Set.mem_iInter.1 (Set.mem_iInter.1 h2 PUnit.unit) PUnit.unit
  exact ⟨a1, a2⟩

def powIso {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (n : ℕ) : LB.Iso ((lbPow L n).pull φ) (lbPow (L.pull φ) n) :=
  ⟨fun p => res (powIso_le L φ n p)
      (pullU φ _ (L.g (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit PUnit.unit))) ^ (n : ℤ)⟩

end GlobalTheory.MBLow.BaseCh
