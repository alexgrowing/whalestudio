import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PhiTTmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuMor
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.FlatAcr
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem κm_eq (r : Res l K) (n : ℕ) (x : OK l K) (w : WittVector l r.k) (hw : WittVector.constantCoeff w = r.ρ x) :
    Mid.κm r n x = Ideal.Quotient.mk _ ((base l).cris n (r.w w)) := by
  change Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n) (Wc.res l r.k n (r.ρ x)) = _
  rw [← hw, Wc.res_coeff, Ideal.quotientMap_mk, Mid.wn_mk]

theorem red_κm (r : Res l K) {m n : ℕ} (h : n ≤ m) :
    (Ideal.quotientMap _ ((base l).red h) (B.red_le true h)).comp (Mid.κm r m) = Mid.κm r n := RingHom.ext fun x => by
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective l (r.ρ x)
  rw [RingHom.comp_apply, κm_eq r m x w hw, κm_eq r n x w hw, Ideal.quotientMap_mk, B.red_cris]

theorem gal_κm (r : Res l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) :
    (Ideal.quotientMap _ (galBase σ n) (B.gal_le σ true n)).comp (Mid.κm r n) = Mid.κm r n := RingHom.ext fun x => by
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective l (r.ρ x)
  rw [RingHom.comp_apply, κm_eq r n x w hw, Ideal.quotientMap_mk, galBase_cris, hσ]

abbrev OT (r : Res l K) (M : Model l K) (n : ℕ) : Thick (Mid.Lm r M n) ⥤ ModuleCat.{0} (Acris l) :=
  B.OM (Mid.Lm r M n) ((base l).cris n)

def redT (r : Res l K) (M : Model l K) {m n : ℕ} (h : n ≤ m) : CH.Mor (OT r M m) (OT r M n) (RingHom.id _) :=
  B.omMor (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (red_κm r h)) fun _ _ _ => rfl) (RingHom.id _) (B.red_cris _ h)

def HMS (r : Res l K) (M : Model l K) (j : ℕ) : Sys.{1} (Acris l) where
  M n := Mid.HM r M n j
  r n := (redT r M n.le_succ).pull j

def galT' (r : Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) :
    CH.Mor (OT r M n) (OT r M n) (ACris.galCris σ) :=
  B.omMor (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl) (ACris.galCris σ) (galBase_cris σ n)

def phiPtT {O : Type} [CommRing O] (F : B.Fn O) (n : ℕ) (κ₁ : O →+* (B.bs l true n).R ⧸ (B.bs l true n).I) :
    F.ptK κ₁ ⟶ F.ptK κ₁ where
  app B₀ := TypeCat.ofHom fun z => (F.ptK _).map (CommRingCat.ofHom (B.frb (B.l_zero z.1.1))) z
  naturality B₀ B' φ := by
    ext z
    exact B.map_sq (F.ptK _) φ (CommRingCat.ofHom (B.frb (B.l_zero (φ.hom.comp z.1.1))))
      (CommRingCat.ofHom (B.frb (B.l_zero z.1.1))) φ (RingHom.ext fun x => (map_pow φ.hom x l).symm) z

def phiT' (r : Res l K) (M : Model l K) (n : ℕ) : CH.Mor (OT r M n) (OT r M n) (ACris.phi ℂ_[l] l) :=
  B.omMor (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).phi n) rfl ((base l).dpP_phi n) (phiPtT _ n _) fun _ y r =>
      ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm) (ACris.phi ℂ_[l] l) ((base l).phi_cris n)

def pullT' (r : Res l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) :
    CH.Mor (OT r N n) (OT r M n) (RingHom.id _) :=
  B.omMor (B.crMor (F := B.schFn N.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl) (RingHom.id _) fun _ => rfl

def phiM (r : Res l K) (M : Model l K) (n j : ℕ) : Mid.HM r M n j →ₛₗ[ACris.phi ℂ_[l] l] Mid.HM r M n j := (phiT' r M n).pull j

def galM (r : Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) :
    Mid.HM r M n j →ₛₗ[ACris.galCris σ] Mid.HM r M n j := (galT' r M σ hσ n).pull j

def pullM (r : Res l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) :
    Mid.HM r N n j →ₗ[Acris l] Mid.HM r M n j := (pullT' r u hu n).pull j

def bWMor (r : Res l K) (M : Model l K) (n : ℕ) : CH.Mor (Wc.OM l (B.schFn M.p) r.ρ n) (OT r M n) r.w :=
  B.omMor (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    r.w (Mid.wn_mk r n)

abbrev HSW (r : Res l K) (M : Model l K) (j : ℕ) : Sys.{1} (WittVector l r.k) := Wc.HS l (B.schFn M.p) r.ρ j

def bW (r : Res l K) (M : Model l K) (n j : ℕ) : (HSW r M j).M n →ₛₗ[r.w] Mid.HM r M n j := (bWMor r M n).pull j

def LS (r : Res l K) : Prop := ∀ M : Model l K, M.Sm → ∀ j,
  Nonempty (Tw.LSeq l (HSW r M j) (HSW r M (j + 1))) ∧ IsFiniteLength (WittVector l r.k) ((HSW r M j).M 1)

def GalW (r : Res l K) : Prop := ∀ (σ : Gal(PadicAlgCl l/K)) w, ACris.galCris σ (r.w w) = r.w w

end CrystallineSemistableComparison.Pb
