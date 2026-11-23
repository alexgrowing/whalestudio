import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Pass.LocPush
open GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

instance eOsurj : RingHomSurjective (D.nbr i w hw).eO.toRingHom := ⟨(D.nbr i w hw).eO.surjective⟩

theorem toLLv_add {a n : ℕ} (u v : Fin a → Fin n → KK D.nd i) :
    toLLv i w hw (u + v) = toLLv i w hw u + toLLv i w hw v := by
  funext j m; simp [toLLv]

theorem toLLv_smul {a n : ℕ} (c : D.nd.O i) (u : Fin a → Fin n → KK D.nd i) :
    toLLv i w hw (c • u) = (D.nbr i w hw).eO c • toLLv i w hw u := by
  funext j m
  simp only [toLLv, Pi.smul_apply, Algebra.smul_def, map_mul, Br.toLLK_alg]

theorem toLLv_inj {a n : ℕ} : Function.Injective (toLLv (D := D) i w hw (a := a) (n := n)) := by
  intro u v h
  funext j m
  exact (Br.toLLK (D.nbr i w hw)).injective (congrFun (congrFun h j) m)

section Lat
variable {a : ℕ} (x : Fin a → D.nd.X i)
  (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
  (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
  (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
    (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)

def toX : ↥Y →ₛₗ[(D.nbr i w hw).eO.toRingHom] (Xgrep i w hw r x hc Y hst).V where
  toFun y := (⟨toLLv i w hw y.1, Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩ : ↥(XV i w hw Y))
  map_add' u v := Subtype.ext (toLLv_add i w hw u.1 v.1)
  map_smul' c u := Subtype.ext (toLLv_smul i w hw c u.1)

theorem toX_inj : Function.Injective (toX i w hw r x hc Y hst) := fun u v h =>
  Subtype.ext (toLLv_inj i w hw (congrArg (fun z : ↥(XV i w hw Y) => (z : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)) h))

theorem rho_toX (g : Br.G D.nbr i w hw) (y : ↥Y) :
    (Xgrep i w hw r x hc Y hst).ρ g (toX i w hw r x hc Y hst y) =
      toX i w hw r x hc Y hst ⟨_, hst ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) y.1 y.2⟩ := by
  apply Subtype.ext
  funext j
  change sumRho (fun j : Fin a => fam i w hw r (x j)) id g (toLLv i w hw y.1) j = _
  rw [sumRho_apply]
  exact loc_mulVec i w hw (rTwO D.nd i r (x j)) g (y.1 j)

end Lat

section Lat2
variable {a : ℕ} (x : Fin a → D.nd.X i)
  (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
  (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
  (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
    (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)

theorem noZero : NoZeroSMulDivisors (Br.OLL D.nbr i w hw) (Xgrep i w hw r x hc Y hst).V := by
  refine ⟨fun {c v} h => ?_⟩
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  right
  apply Subtype.ext
  funext j m
  have h2 := congrFun (congrFun (congrArg (fun z : ↥(XV i w hw Y) => z.1) h) j) m
  change c • (show ↥(XV i w hw Y) from v).1 j m = 0 at h2
  change (show ↥(XV i w hw Y) from v).1 j m = 0
  rw [Subalgebra.smul_def, smul_eq_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left (fun h0 => hc0 (Subtype.ext h0))

theorem range_fg (hY : Y.FG) : (LinearMap.range (toX i w hw r x hc Y hst)).FG := by
  rw [LinearMap.range_eq_map]
  exact ((Submodule.fg_top Y).2 hY).map _

def latY (hY : Y.FG) : Lattice (O := Br.OLL D.nbr i w hw) (Xgrep i w hw r x hc Y hst).ρ where
  T := LinearMap.range (toX i w hw r x hc Y hst)
  stable g := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, (rho_toX i w hw r x hc Y hst g y).symm⟩
  fg := range_fg i w hw r x hc Y hst hY
  free := by
    obtain ⟨hO, hD, -⟩ := (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).1
    haveI := hD.toIsPrincipalIdealRing
    haveI := noZero i w hw r x hc Y hst
    haveI : Module.Finite (Br.OLL D.nbr i w hw) ↥(LinearMap.range (toX i w hw r x hc Y hst)) :=
      Module.Finite.iff_fg.2 (range_fg i w hw r x hc Y hst hY)
    exact Module.free_of_finite_type_torsion_free'
  span := by
    change Submodule.span (Br.LL D.nbr i w hw) (show Set ↥(XV i w hw Y) from (LinearMap.range (toX i w hw r x hc Y hst) : Set (Xgrep i w hw r x hc Y hst).V)) = ⊤
    apply Submodule.map_injective_of_injective (XV i w hw Y).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    conv_rhs => rw [XV]
    congr 1
    ext u
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, rfl⟩

end Lat2

instance eOinv : RingHomInvPair (D.nbr i w hw).eO.toRingHom (D.nbr i w hw).eO.symm.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

instance eOinv' : RingHomInvPair (D.nbr i w hw).eO.symm.toRingHom (D.nbr i w hw).eO.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

theorem phi_WKG {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (z : KOG (D.nd.O i) k) :
    Br.phi (D.nbr i w hw) k (WKG M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) z) =
      repD (Br.locLat D.nbr i w hw M) g (Br.phi (D.nbr i w hw) k z) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change Submodule.Quotient.mk (Br.vecS (D.nbr i w hw) k ((matRep (mapM (toK D.nd i) M) _) u)) =
    Submodule.Quotient.mk ((matRep (Br.loc D.nbr i w hw M) g) (Br.vecS (D.nbr i w hw) k u))
  congr 1
  exact (loc_mulVec i w hw M g u).symm

section Phi
variable {a : ℕ} (x : Fin a → D.nd.X i)
  (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
  (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
  (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
    (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
  (hY : Y.FG) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g)

def eY : ↥Y ≃ₛₗ[(D.nbr i w hw).eO.toRingHom] ↥(LinearMap.range (toX i w hw r x hc Y hst)) :=
  LinearEquiv.ofInjective _ (toX_inj i w hw r x hc Y hst)

def phiY (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k) :
    ↥(latY i w hw r x hc Y hst hY).T →ₗ[Br.OLL D.nbr i w hw]
      ((ModuleGaloisRepresentation i w hw M hM).V ⧸ (Br.locLat D.nbr i w hw M).T) :=
  ((Br.phi (D.nbr i w hw) k).comp φ).comp (eY i w hw r x hc Y hst).symm.toLinearMap

theorem phiY_toX (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k) (y : ↥Y)
    (h : toX i w hw r x hc Y hst y ∈ (latY i w hw r x hc Y hst hY).T) :
    phiY i w hw r x hc Y hst hY M hM φ ⟨_, h⟩ = Br.phi (D.nbr i w hw) k (φ y) := by
  have e : (eY i w hw r x hc Y hst).symm ⟨_, h⟩ = y :=
    (eY i w hw r x hc Y hst).symm_apply_eq.2 (Subtype.ext rfl)
  change Br.phi (D.nbr i w hw) k (φ ((eY i w hw r x hc Y hst).symm ⟨_, h⟩)) = _
  rw [e]

theorem phiY_gmap (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k)
    (hφ : ∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) :
    BlochKatoDuality.IsGMapD (latY i w hw r x hc Y hst hY) (Br.locLat D.nbr i w hw M) (phiY i w hw r x hc Y hst hY M hM φ) := by
  intro g v
  obtain ⟨v, y, rfl⟩ := v
  have e1 : actT (latY i w hw r x hc Y hst hY) g ⟨_, ⟨y, rfl⟩⟩ =
      ⟨toX i w hw r x hc Y hst ⟨_, hst ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) y.1 y.2⟩, ⟨_, rfl⟩⟩ :=
    Subtype.ext (rho_toX i w hw r x hc Y hst g y)
  refine (congrArg (phiY i w hw r x hc Y hst hY M hM φ) e1).trans ?_
  refine (phiY_toX i w hw r x hc Y hst hY M hM φ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (repD (Br.locLat D.nbr i w hw M) g) (phiY_toX i w hw r x hc Y hst hY M hM φ y ⟨y, rfl⟩).symm)
  rw [hφ]
  exact phi_WKG i w hw M g (φ y)

end Phi

section Coc
variable {a : ℕ} (x : Fin a → D.nd.X i)
  (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
  (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
  (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
    (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
  (E : Fin a → Fin D.R.nV → KK D.nd i)
  (hE : ∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)

def cocY (g : Br.G D.nbr i w hw) : (Xgrep i w hw r x hc Y hst).V :=
  toX i w hw r x hc Y hst ⟨_, hE ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)⟩

theorem cocY_val (g : Br.G D.nbr i w hw) :
    (show ↥(XV i w hw Y) from cocY i w hw r x hc Y hst E hE g).1 =
      sumRho (fun j : Fin a => fam i w hw r (x j)) id g (toLLv i w hw E) - toLLv i w hw E := by
  funext j m
  rw [Pi.sub_apply, Pi.sub_apply, sumRho_apply]
  have h1 := congrFun (loc_mulVec i w hw (rTwO D.nd i r (x j)) g (E j)) m
  change Br.toLLK (D.nbr i w hw) (((mapM (toK D.nd i) (rTwO D.nd i r (x j)) _).mulVec (E j) - E j) m) = _
  rw [Pi.sub_apply, map_sub, ← h1]
  rfl

end Coc

section Crys
variable {a : ℕ} (x : Fin a → D.nd.X i)
  (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)

include hc in

theorem sum_crys (hAdm : FontaineAtPlacesOverL (D := D)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (hpot : ∀ j, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (fam i w hw r (x j)))) :
    IsCrys ((D.loc (D.nd.l i)).PD K')
      ((sumRho (fun j : Fin a => fam i w hw r (x j)) id).comp (Subgroup.inclusion (GK_le h))) := by
  haveI := isTopRing i w hw
  have hc' : ∀ (j : Fin a) (v : Fin D.R.nV → Br.LL D.nbr i w hw),
      Continuous fun g => ((fam i w hw r (x j)).comp (Subgroup.inclusion (GK_le h)) g).mulVec v :=
    fun j v => ((hc j).comp (continuous_inclusion (GK_le h))).matrix_mulVec continuous_const
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hcr : ∀ j, IsCrys ((D.loc (D.nd.l i)).PD K')
      (matRep ((fam i w hw r (x j)).comp (Subgroup.inclusion (GK_le h)))) := fun j =>
    ((GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (fam i w hw r (x j)))).2.1 (hpot j))
  exact (cj_sum (Qp := ℚ_[D.nd.l i]) (O := ↥(OL (D.nbr i w hw).LL))
    (fun j : Fin a => (fam i w hw r (x j)).comp (Subgroup.inclusion (GK_le h))) hc' hF' (S := fun _ => Set.univ)
    (fun j => ⟨hcr j, fun τ b _ => Set.mem_univ _⟩) a id).1

variable (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
  (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
    (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
  (E : Fin a → Fin D.R.nV → KK D.nd i)
  (hE : ∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)

theorem pushoutCocycle_mem_blochKatoSelmer (hAdm : FontaineAtPlacesOverL (D := D)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (hpot : ∀ j, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (fam i w hw r (x j)))) :
    cocY i w hw r x hc Y hst E hE ∈ finiteCocycles (Br.PD D.loc D.nbr i w hw) (Xgrep i w hw r x hc Y hst).ρ := by
  haveI := isTopRing i w hw
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  exact GlobalTheory.Pass.FinDesc.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF
    (fun A₀ A₁ A₂ ι π h1 h2 h3 h4 h5 hA =>
      ⟨((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).1, ((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).2.1⟩)
    (GRep.sum (Qp := ℚ_[D.nd.l i]) (O := Br.OLL D.nbr i w hw) (fun j : Fin a => fam i w hw r (x j))
      (fun j v => (hc j).matrix_mulVec continuous_const) id)
    (Xgrep i w hw r x hc Y hst) (XV i w hw Y).subtype (XV i w hw Y).injective_subtype (fun g v => rfl)
    (sum_crys i w hw r x hc hAdm K' h hN hF hS hpot) (toLLv i w hw E) (cocY i w hw r x hc Y hst E hE)
    (cocY_val i w hw r x hc Y hst E hE)

end Crys

theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (a : ℕ) (x : Fin a → D.nd.X i), (∀ j, x j ∈ Xs) → ∀ (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g) (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)), Y.FG → ∀ (hst : (∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)) (hE : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)), ∀ c ∈ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE, c ∈ BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) (GlobalTheory.Pass.LocDirect.Xgrep i w hw r x hc Y hst) (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM) (Br.locLat D.nbr i w hw M) := by
  intro D hAdm i r _ Xs w hw n hpf k M hM a x hx hc E Y hY hst hE c hcm
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hall⟩ := hpf
  obtain ⟨φ, hφ, rfl⟩ := hcm
  have hz := pushoutCocycle_mem_blochKatoSelmer i w hw r x hc Y hst E hE hAdm K' h hN hF hS (fun j => (hall ⟨x j, hx j⟩).1)
  have hT : cocY i w hw r x hc Y hst E hE ∈ latticeCocycles (latY i w hw r x hc Y hst hY) :=
    ⟨hz.1, fun g _ => ⟨_, rfl⟩⟩
  apply Submodule.subset_span
  refine ⟨latY i w hw r x hc Y hst hY, phiY i w hw r x hc Y hst hY M hM φ,
    phiY_gmap i w hw r x hc Y hst hY M hM φ hφ, ⟨_, hT⟩, ⟨hT, hz⟩, ?_⟩
  funext g
  exact (phiY_toX i w hw r x hc Y hst hY M hM φ _ _).symm
end GlobalTheory.Pass.LocPush
