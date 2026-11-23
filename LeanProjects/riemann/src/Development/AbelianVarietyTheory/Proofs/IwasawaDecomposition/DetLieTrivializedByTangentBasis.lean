import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmpStOfSabExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFiberNormalReduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolFin

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM)

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {W : Scheme.{0}} {p : W ⟶ Z.X} {G : Over W} [GrpObj G] [IsCommMonObj G] {ψ : G.left ⟶ Z.t.G.left}
  (h : IsGrpPullback G Z.t.G p ψ) {d : ℕ}
  (B : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ W), Module.Basis (Fin d) S (TanM x G))

def frameChg (M : MChart Z) {A : W.Opens} (hA : IsAffineOpen A) (hle : A ≤ p ⁻¹ᵁ M.U) :
    Matrix (Fin M.n) (Fin d) Γ(W, A) :=
  (lieBasis M (tau hA ≫ p) (le_preimage_map p hle (tau_le hA le_rfl))).toMatrix
    ((B _ (tau hA)).map (tanEquiv h (tau hA)))

theorem frameChg_map (hB : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ W) (x' : Sp S' ⟶ W)
      (e : spMap φ ≫ x = x') (j : Fin d), tanPull φ e (B S x j) = B S' x' j)
    (M : MChart Z) {A : W.Opens} (hA : IsAffineOpen A) (hle : A ≤ p ⁻¹ᵁ M.U) {S : Type} [CommRing S]
    (z : Sp S ⟶ W) (hz : ⊤ ≤ z ⁻¹ᵁ A) (hM : ⊤ ≤ (z ≫ p) ⁻¹ᵁ M.U) :
    (frameChg h B M hA hle).map (ev z A hz) =
      (lieBasis M (z ≫ p) hM).toMatrix ((B S z).map (tanEquiv h z)) := by
  have e : spMap (ev z A hz) ≫ tau hA = z := spMap_ev z hA hz
  have e' : spMap (ev z A hz) ≫ tau hA ≫ p = z ≫ p := by rw [← Category.assoc, e]
  ext i j
  have h1 := (lieBasis M (tau hA ≫ p) (le_preimage_map p hle (tau_le hA le_rfl))).sum_toMatrix_smul_self
    ((B _ (tau hA)).map (tanEquiv h (tau hA))) j
  have h2 := congrArg (tanPull (G := Z.t.G) _ e') h1
  rw [map_sum] at h2
  simp only [map_smulₛₗ, Module.Basis.map_apply, tanPull_tanEquiv h _ e e', hB _ _ _ _ _ e,
    tanPull_lieBasis M _ e' _ hM] at h2
  rw [Module.Basis.toMatrix_apply, Module.Basis.map_apply, ← h2, Module.Basis.repr_sum_self]
  rfl

def frameUnit (M : MChart Z) {A : W.Opens} (hA : IsAffineOpen A) (hle : A ≤ p ⁻¹ᵁ M.U) : Γ(W, A)ˣ :=
  (show IsUnit (rdet (frameChg h B M hA hle)) from isUnit_rdet_toMatrix _ _).unit

theorem ev_frameUnit (hB : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ W) (x' : Sp S' ⟶ W)
      (e : spMap φ ≫ x = x') (j : Fin d), tanPull φ e (B S x j) = B S' x' j)
    (M : MChart Z) {A : W.Opens} (hA : IsAffineOpen A) (hle : A ≤ p ⁻¹ᵁ M.U) {S : Type} [CommRing S]
    (z : Sp S ⟶ W) (hz : ⊤ ≤ z ⁻¹ᵁ A) (hM : ⊤ ≤ (z ≫ p) ⁻¹ᵁ M.U) :
    ev z A hz (frameUnit h B M hA hle).val = rdet ((lieBasis M (z ≫ p) hM).toMatrix ((B S z).map (tanEquiv h z))) := by
  rw [← frameChg_map h B hB M hA hle z hz hM, ← map_rdet]
  rfl

theorem exists_frameGlue (hB : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ W) (x' : Sp S' ⟶ W)
      (e : spMap φ ≫ x = x') (j : Fin d), tanPull φ e (B S x j) = B S' x' j) (J : PUnit → MChart Z) :
    ∃ s : Γ(W, ((detLie Z).pull p).U J)ˣ, ∀ (A : W.Opens) (hA : IsAffineOpen A) (hAJ : A ≤ ((detLie Z).pull p).U J),
      res hAJ s = frameUnit h B (J PUnit.unit) hA (hAJ.trans (LB.wchart_le (detLie Z) (fun _ : PUnit => p) J PUnit.unit)) := by
  have le := LB.wchart_le (detLie Z) (fun _ : PUnit => p) J PUnit.unit
  have hc : ((detLie Z).pull p).U J ≤ ⨆ a : {A : W.Opens // IsAffineOpen A ∧ A ≤ ((detLie Z).pull p).U J}, a.1 := by
    intro x hx
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hle⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open hx (((detLie Z).pull p).U J).isOpen
    exact Opens.mem_iSup.2 ⟨⟨A, hA, hle⟩, hxA⟩
  have compat : ∀ (a b : {A : W.Opens // IsAffineOpen A ∧ A ≤ ((detLie Z).pull p).U J}), ∀ x ∈ a.1 ⊓ b.1,
      gm (𝟙 W) x a.1 (frameUnit h B (J PUnit.unit) a.2.1 (a.2.2.trans le)) =
        gm (𝟙 W) x b.1 (frameUnit h B (J PUnit.unit) b.2.1 (b.2.2.trans le)) := by
    intro a b x hx
    have e : res (inf_le_left : a.1 ⊓ b.1 ≤ a.1) (frameUnit h B (J PUnit.unit) a.2.1 (a.2.2.trans le)) =
        res inf_le_right (frameUnit h B (J PUnit.unit) b.2.1 (b.2.2.trans le)) := by
      refine Units.ext (ext_ev fun S _ z hz => ?_)
      have ha := le_preimage_mono inf_le_left hz
      have hb := le_preimage_mono inf_le_right hz
      have hM := le_preimage_map p (a.2.2.trans le) ha
      exact ((ev_res z _ hz ha _).trans (ev_frameUnit h B hB _ a.2.1 _ z ha hM)).trans
        ((ev_res z _ hz hb _).trans (ev_frameUnit h B hB _ b.2.1 _ z hb hM)).symm
    have := congrArg (gm (𝟙 W) x _) e
    rwa [gm_res _ x _ hx, gm_res _ x _ hx] at this
  obtain ⟨s, hs⟩ := glue_unit (X := W) (((detLie Z).pull p).U J) (fun a : {A : W.Opens // IsAffineOpen A ∧ A ≤ ((detLie Z).pull p).U J} => a.1)
    (fun a => a.2.2) hc (fun a => frameUnit h B (J PUnit.unit) a.2.1 (a.2.2.trans le)) compat
  exact ⟨s, fun A hA hAJ => hs ⟨A, hA, hAJ⟩⟩

include h in
theorem exists_gen_pull_detLie (hB : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ W) (x' : Sp S' ⟶ W)
      (e : spMap φ ≫ x = x') (j : Fin d), tanPull φ e (B S x j) = B S' x' j) : ∃ t : LB.Gen ((detLie Z).pull p), t.IsGen := by
  have le : ∀ J : ((detLie Z).pull p).ι, ((detLie Z).pull p).U J ≤ p ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z) (fun _ : PUnit => p) J PUnit.unit
  choose s hs using exists_frameGlue h B hB
  refine ⟨⟨s⟩, fun J J' => Units.ext (ext_ev_loc fun q hq => ?_)⟩
  obtain ⟨_, ⟨A, hA, rfl⟩, hqA, hle⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open hq
    (((detLie Z).pull p).U J ⊓ ((detLie Z).pull p).U J').isOpen
  refine ⟨A, hqA, fun S _ z hz hzA => ?_⟩
  have hAJ : A ≤ ((detLie Z).pull p).U J := fun x hx => (hle hx).1
  have hAJ' : A ≤ ((detLie Z).pull p).U J' := fun x hx => (hle hx).2
  have hJ := le_preimage_mono inf_le_left hz
  have hJ' := le_preimage_mono inf_le_right hz
  have hM := le_preimage_map p (le J) hJ
  have hM' := le_preimage_map p (le J') hJ'
  have vJ : ev z _ hJ (s J).val =
      rdet ((lieBasis (J PUnit.unit) (z ≫ p) hM).toMatrix ((B S z).map (tanEquiv h z))) :=
    (ev_res z hAJ hzA hJ _).symm.trans ((congrArg (fun u => ev z A hzA (Units.val u)) (hs J A hA hAJ)).trans
      (ev_frameUnit h B hB _ hA _ z hzA hM))
  have vJ' : ev z _ hJ' (s J').val =
      rdet ((lieBasis (J' PUnit.unit) (z ≫ p) hM').toMatrix ((B S z).map (tanEquiv h z))) :=
    (ev_res z hAJ' hzA hJ' _).symm.trans ((congrArg (fun u => ev z A hzA (Units.val u)) (hs J' A hA hAJ')).trans
      (ev_frameUnit h B hB _ hA _ z hzA hM'))
  have g := ev_pull_g (detLie Z) p z J J' hz (le_preimage_inf hM hM')
  refine ((ev_res z _ hz hJ _).trans vJ).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (g.trans (ev_detChg _ _ _ hM hM' _)) ((ev_res z _ hz hJ' _).trans vJ')).symm
  exact (rdet_toMatrix_mul _ _ _).symm

end Frame

theorem pull_cls_detLie_eq_zero_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β)
    (hL : (GlobalTheory.FlagMod.detLie Z).IsLB) (W : Scheme.{0}) (p : W ⟶ Z.X) (G : Over W) [GrpObj G] [IsCommMonObj G]
    (ψ : G.left ⟶ Z.t.G.left), IsGrpPullback G Z.t.G p ψ → ∀ (d : ℕ)
    (B : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ W), Module.Basis (Fin d) S (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x G)),
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ W) (x' : Sp S' ⟶ W)
      (e : spMap φ ≫ x = x') (j : Fin d), tanPull φ e (B S x j) = B S' x' j) →
    GlobalTheory.CechPic.pull p (GlobalTheory.CechPic.cls _ hL) = 0 := by
  intro E _ _ _ H D l Xo c O _ β Z hL W p G _ _ ψ h d B hB
  obtain ⟨t, ht⟩ := exists_gen_pull_detLie h B hB
  rw [← CechPic.cls_pull hL p (pull_isLB hL p), CechPic.cls_eq_zero_iff]
  exact ⟨t, ht⟩

end GlobalTheory.PolFin
