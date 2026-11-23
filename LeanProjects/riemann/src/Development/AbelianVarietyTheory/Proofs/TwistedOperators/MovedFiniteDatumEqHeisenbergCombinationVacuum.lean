import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedComb

open GlobalTheory.FinPl (Moves Lat)

variable {D : D7}

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ M : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M) :
    Moves V g Λ M (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := fun i => GlobalTheory.VacMove.mulVec_mem_idAt _ hy i
  constructor
  · intro hyΛ
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V M _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y hyΛ)
  · intro hyM
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ y hy ?_
    refine (h _).2 ?_
    rw [← GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact GlobalTheory.LatVHat.latV_mem_hatL D V M _ _ hyM

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  rw [GfC, MonoidHom.mem_ker] at hg ⊢
  exact hg

theorem datum_fixed {S T : HSp D} {e a a' : AE D} (ha : e * (a + cA D a) = 0) (ha' : e * (a' + cA D a') = 0)
    {b : GA D S} {b' : GA D T} (hb : SuppAt a S b) (hb' : SuppAt a' T b') {Φ : WO S T → ℂ} (hΦ : ∀ x, Φ x ≠ 0 → IsHalf e x) :
    (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) = Φ := by
  funext x
  by_cases hx : IsHalf e x
  · rw [GlobalTheory.StdHalfLat.actO_eq_self_of_half ha ha' (GlobalTheory.StdHalfLat.suppAt_inv' hb) (GlobalTheory.StdHalfLat.suppAt_inv' hb') hx]
  · have h0 : Φ x = 0 := by
      by_contra hne
      exact hx (hΦ x hne)
    rw [h0]
    by_contra hne
    exact hx (GlobalTheory.MovedVac.halfBack D S T _ _ e x (hΦ _ hne))

private theorem actO_actO_inv_inv (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  have h1 : mt T h * mt T h⁻¹ = 1 := by
    rw [← GlobalTheory.VacMove.mt_mul₀, mul_inv_cancel, GlobalTheory.VacMove.mt_one₀]
  have h2 : mt S g * mt S g⁻¹ = 1 := by
    rw [← GlobalTheory.VacMove.mt_mul₀, mul_inv_cancel, GlobalTheory.VacMove.mt_one₀]
  rw [GlobalTheory.VacMove.actO_eq, GlobalTheory.VacMove.actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
    Matrix.mul_assoc, h2, Matrix.mul_one]

private theorem actO_two_nsmul' (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (2 • x) = 2 • actO S T g h x := by
  rw [two_nsmul, two_nsmul, GlobalTheory.VacMove.actO_eq, GlobalTheory.VacMove.actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem isLatVac_move {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : Moves S b Λ M fun _ => True)
    (hb' : Moves T b' Λ' M' fun _ => True) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f₀) :
    IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) (om (b, b') f₀) := by
  obtain ⟨hv1, hv2⟩ := hv
  have key : ∀ w c : WO S T, actO S T b b' c = w → heisO ψ S T c f₀ = f₀ →
      heisO ψ S T w (om (b, b') f₀) = om (b, b') f₀ := by
    intro w c hc hfix
    rw [← hc, ← hW.om_heis b b' c f₀ hf, hfix]
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · have hu0 := GlobalTheory.VacMove.actO_mem_latO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb') hu
    refine key _ (2 • actO S T b⁻¹ b'⁻¹ u) ?_ (hv1 _ hu0)
    rw [actO_two_nsmul', actO_actO_inv_inv]
  · have hu0 := GlobalTheory.VacMove.actO_mem_latO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb') hu
    have hc : IsHalf e (actO S T b⁻¹ b'⁻¹ u) := by
      apply GlobalTheory.MovedVac.halfBack D S T b b' e
      rw [actO_actO_inv_inv]
      exact hue
    exact key u _ (actO_actO_inv_inv S T b b' u) (hv2 e he _ hu0 hc)

theorem om_eq_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hbf : b ∈ GfC S) (hbf' : b' ∈ GfC T)
    (hb : Moves S b Λ M fun _ => True) (hb' : Moves T b' Λ' M' fun _ => True) {e a a' : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (ha : e * (a + cA D a) = 0) (ha' : e * (a' + cA D a') = 0) (hs : SuppAt a S b) (hs' : SuppAt a' T b')
    {Φ f₀ f g : WO S T → ℂ} (hΦ : IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f)
    (hg : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀) Φ g) :
    om (b, b') f = g := by
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨θ, hθ⟩ := hstd.2.1
  have hfT : IsThetaFunO ψ S T f := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hstd hθ hf hf₀
  have hth := GlobalTheory.VacMove.isThetaAt_moveLat D ψ S T χS χT om hW Λ M Λ' M' hΛ hM hΛ' hM' b hbf b' hbf' hb hb' e Φ f₀ f
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum he) hf₀ hfT hf
  rw [datum_fixed ha ha' hs hs' hΦ.1] at hth
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  rw [hall Tm hTm, hg.2 Tm hTm]

private theorem isThetaFunO_and_isLatVac_of_isVacO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT ΛS ΛT f) :
    IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f := by
  exact ⟨h.2.theta, h.2.lat⟩

private theorem moves_negSp_negGA_of_moves {V : HSp D} {g : GA D V} {Λ M : Lat V} (h : Moves V g Λ M fun _ => True) :
    Moves (negSp V) (negGA V g) Λ M fun _ => True := by
  intro y hy
  rw [GlobalTheory.ChiGrid.mt_negGA]
  exact h y hy

private theorem suppAt_negSp_negGA_of_suppAt {V : HSp D} {a : AE D} {g : GA D V} (h : SuppAt a V g) :
    SuppAt a (negSp V) (negGA V g) := by
  intro i j
  rw [GlobalTheory.ChiGrid.mt_negGA]
  exact h i j

private theorem moved_core_lemma_3 {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hbf : b ∈ GfC S) (hbf' : b' ∈ GfC T)
    (hb : Moves S b Λ M fun _ => True) (hb' : Moves T b' Λ' M' fun _ => True) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (hk : ∃ a, e * (a + cA D a) = 0 ∧ SuppAt a S b)
    (hk' : ∃ a', e * (a' + cA D a') = 0 ∧ SuppAt a' T b') {Φ f₀ f : WO S T → ℂ}
    (hΦ : IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f)
    (c : WO S T →₀ ℂ)
    (hc : ∀ g₀, IsThetaFunO ψ S T g₀ → IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) g₀ →
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 g₀ Φ (comb ψ S T c g₀)) :
    om (b, b') f = comb ψ S T c (om (b, b') f₀) := by
  obtain ⟨a, ha, hs⟩ := hk
  obtain ⟨a', ha', hs'⟩ := hk'
  exact om_eq_of_isThetaAt hW hΛ hM hΛ' hM' hbf hbf' hb hb' he ha ha' hs hs' hΦ hf₀ hf
    (hc _ (hW.om_pres _ _ hf₀) (isLatVac_move hW hΛ hM hΛ' hM' hb hb' hf₀ hv))

theorem movedVec_eq_comb : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (d : FinDatum ch.G t p) (c : WO (ch.G.pS p) (ch.G.pT p) →₀ ℂ), d.z = 1 → ch.S.Z.HasVec d → IsCombOf ch.W d c → movedVec t ch.S.toGridChoice d = comb ch.W.ψ _ _ c (ch.W.om p (ch.G.toPair p (ch.S.N.u p.small).1 (ch.S.N.u p.big).1) (ch.S.Z.vac p)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hset ch _ t p hp d c hz hvec hcomb
  have hL := hset.core.lev
  have hnodes := GlobalTheory.FunObj.DefPair.nodes hp
  obtain ⟨f, hf⟩ := hvec
  have hvd : ch.S.Z.vec d = f := by
    unfold GlobalTheory.FunObj.Normal.vec
    rw [GlobalTheory.FunObj.FinDatum.vec_eq ch.W hf, hz, ← Prod.one_eq_mk, map_one]
    rfl
  unfold movedVec
  rw [hvd]
  cases p with
  | chi i j =>
    have hX := hnodes.1
    have hY := hnodes.2
    obtain ⟨hf₀, hv⟩ := isThetaFunO_and_isLatVac_of_isVacO (ch.S.Z.vac_is (.chi i j) hp)
    exact moved_core_lemma_3 (ch.W.om_is (.chi i j) (by simp only [DefPair, Pair.InRange, Node.InRange] at hp ⊢; omega))
      (GlobalTheory.ChiGrid.isSelfDualC_neg (GlobalTheory.FunObj.Std.selfDual ch.S.N hY))
      (GlobalTheory.ChiGrid.isSelfDualC_neg (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hY))
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hX) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hX)
      (negGA_mem_GfC _ (ch.S.N.u _).2) (ch.S.N.u _).2
      (moves_negSp_negGA_of_moves (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hY))) (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hX))
      d.e_is
      (by
        obtain ⟨a, ha, hs⟩ := GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hY
        exact ⟨a, ha, suppAt_negSp_negGA_of_suppAt hs⟩)
      (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hX)
      d.sb hf₀ hv hf c hcomb.2.2
  | mu t' i j => exact False.elim hp
  | core i => exact False.elim hp
  | top t' j =>
    have hX := hnodes.1
    have hY := hnodes.2
    obtain ⟨hf₀, hv⟩ := isThetaFunO_and_isLatVac_of_isVacO (ch.S.Z.vac_is (.top t' j) hp)
    exact moved_core_lemma_3 (ch.W.om_is (.top t' j) (by simp only [DefPair, Pair.InRange, Node.InRange] at hp ⊢; omega))
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hX) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hX)
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hY) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hY)
      (ch.S.N.u _).2 (ch.S.N.u _).2
      (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hX)) (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hY))
      d.e_is (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hX)
      (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hY)
      d.sb hf₀ hv hf c hcomb.2.2

end GlobalTheory.MovedComb

end
