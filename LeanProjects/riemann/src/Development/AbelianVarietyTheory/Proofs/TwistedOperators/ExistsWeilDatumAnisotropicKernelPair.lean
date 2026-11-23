import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

def lam (σ : ℕ) : Fin σ → D.host.E := fun a => D.host.xi0 ^ (a : ℕ)

theorem lam_ne (σ : ℕ) (a : Fin σ) : lam (D := D) σ a ≠ 0 := pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)

def besDecAt (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) :
    HypDec (G.V (.grid D.R.m j)) (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ :=
  diagDec (rowBes G j (by omega) σ (by omega)) (lam σ) (lam_ne σ)

variable {G t M} in

def volAt (hM : M.Is t) (X : Node) (hX : X.InRange D.R.m) : GlobalTheory.Unf.Vol (G.V X) :=
  ⟨M.ν X, M.fd X, (hM.vtx X hX).haar_fund.1, (hM.vtx X hX).haar_fund.2⟩

variable {t M} in

def besAt (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) : BesLev D σ where
  V := G.V (.grid D.R.m j)
  V₀ := GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
  A := G.V (.top j)
  L := GlobalTheory.SeeSaw.Model.nLine D
  d := besDecAt G j σ hj
  o := GlobalTheory.OrthSumExists.orthDecHsum D _ _
  ζ := fun _ => D.host.xi0 ^ σ
  line := GlobalTheory.SeeSaw.Model.isLineVec_nLine (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D))
  cpt := cocpt_top G (by omega)
  vA := volAt hM (.top j) (by show j ≤ D.R.m; omega)
  vN := vN

variable {t M} in

def jacAt (hM : M.Is t) (n σ : ℕ) (hn : n + 2 * σ + 1 = D.R.m) : JacLev D σ where
  W := G.V (.grid D.R.m n)
  W₀ := G.V (.top n)
  d := rowJac G n (by omega) σ (by omega)
  cpt := cocpt_top G (by omega)
  v0 := volAt hM (.top n) (by show n ≤ D.R.m; omega)
  vN := (GlobalTheory.Unf.Inhab.nonempty_volN _).some

theorem exists_weilDatum_anisotropicKernelPair {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) :
    ∃ om₀ : Om V₀ W₀, IsWeilDatumO ψ V₀ W₀ χV χW om₀ := by
  obtain ⟨om₁, h₁⟩ := (GlobalTheory.Desc.weil_data_descend D ψ V W χV χW om h).1 V₀ ρ dV
  exact (GlobalTheory.Desc.weil_data_descend D ψ V₀ W χV χW om₁ h₁).2 W₀ σ dW

variable {M} in

def stepAt (hM : M.Is t) (j : ℕ) (hj : j + 1 ≤ D.R.m) {V₀ W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec (G.V (.grid D.R.m j)) V₀ ρ)
    (dW : HypDec (G.V (.grid D.R.m (j + 1))) W₀ σ) :
    Step Wl.ψ (G.V (.grid D.R.m j)) V₀ (G.V (.grid D.R.m (j + 1))) W₀ ρ σ where
  χV := G.chrS (.mu t D.R.m j)
  χW := G.chrT (.mu t D.R.m j)
  om := Wl.om (.mu t D.R.m j)
  om₀ := (exists_weilDatum_anisotropicKernelPair dV dW (Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩)).choose
  weil := Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩
  weil₀ := (exists_weilDatum_anisotropicKernelPair dV dW (Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩)).choose_spec
  vW := volAt hM (.grid D.R.m (j + 1)) ⟨le_rfl, hj⟩
  vS := (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some
  vT := (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some
  vU := (GlobalTheory.Unf.Inhab.nonempty_volU D _).some

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

theorem link_map {n : ℕ} (σ : ℕ) :
    (-(D.host.xi0 • (1 : Matrix (Fin n) (Fin n) D.host.E))) *ᵥ (fun _ => D.host.xi0 ^ σ) = -fun _ => D.host.xi0 ^ (σ + 1) := by
  rw [neg_mulVec, smul_mulVec, one_mulVec]
  funext i
  simp [pow_succ, mul_comm]

theorem link_norm (L : HSp D) (σ : ℕ) :
    star (fun _ : Fin L.rank => D.host.xi0 ^ (σ + 1)) ⬝ᵥ L.gram *ᵥ (fun _ => D.host.xi0 ^ (σ + 1)) =
      D.host.xi0 * star D.host.xi0 * (star (fun _ : Fin L.rank => D.host.xi0 ^ σ) ⬝ᵥ L.gram *ᵥ (fun _ => D.host.xi0 ^ σ)) := by
  have e : (fun _ : Fin L.rank => D.host.xi0 ^ (σ + 1)) = D.host.xi0 • fun _ => D.host.xi0 ^ σ := by
    funext i
    simp [pow_succ, mul_comm]
  rw [e, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

variable {G t M} in

def linkAt (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : VolN (besDecAt G j (σ + 1) hj))
    (hj' : j + 1 + 1 + 2 * σ + 2 = D.R.m) (vN' : VolN (besDecAt G (j + 1 + 1) σ hj')) :
    Link (besAt G hM j (σ + 1) hj vN) (besAt G hM (j + 1 + 1) σ hj' vN').L (besAt G hM (j + 1 + 1) σ hj' vN').ζ where
  τ := -(D.host.xi0 • (1 : Matrix (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) D.host.E))
  map := link_map σ
  norm := link_norm _ σ

theorem cocpt_last : CoCpt (G.V (.grid D.R.m D.R.m)) := by
  have hm := D.R.two_le_m
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
    injection e with e1
    omega
  refine GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite h.sigOK fun τ => Or.inl ?_
  rw [h.sig τ, h.rank]
  simp [Node.neg]

def castOm {V : HSp D} {n n' : ℕ} (h : n = n') (om : Om V (G.V (.grid D.R.m n))) : Om V (G.V (.grid D.R.m n')) :=
  Eq.rec (motive := fun k _ => Om V (G.V (.grid D.R.m k))) om h

theorem castOm_weil {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {n n' : ℕ} (h : n = n') {χV χW : (AE D)ˣ →* Circle}
    {om : Om V (G.V (.grid D.R.m n))} (hom : IsWeilDatumO ψ V _ χV χW om) :
    IsWeilDatumO ψ V (G.V (.grid D.R.m n')) χV χW (castOm G h om) := by
  subst h
  exact hom

def castSch {V : HSp D} {n n' : ℕ} (h : n = n') (f : WO V (G.V (.grid D.R.m n)) → ℂ) : WO V (G.V (.grid D.R.m n')) → ℂ :=
  Eq.rec (motive := fun k _ => WO V (G.V (.grid D.R.m k)) → ℂ) f h

theorem castSch_theta {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {n n' : ℕ} (h : n = n') {f : WO V (G.V (.grid D.R.m n)) → ℂ}
    (hf : IsThetaFunO ψ V _ f) : IsThetaFunO ψ V (G.V (.grid D.R.m n')) (castSch G h f) := by
  subst h
  exact hf

variable {M} in

def lastAt (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) :
    Last Wl.ψ (G.V (.grid D.R.m D.R.m)) (besAt G hM j 0 hj vN) where
  J := jacAt G hM (j + 1) 0 (by omega)
  s := stepAt G Wl t hM j (by omega) (besDecAt G j 0 hj) (rowJac G (j + 1) (by omega) 0 (by omega))
  cptS := GlobalTheory.LastRed.cocpt_zero (rowJac G (j + 1) (by omega) 0 (by omega)) (cocpt_top G (j := j + 1) (by omega))
  cptT := cocpt_last G
  χS := G.chrS (.mu t D.R.m (j + 1))
  χT := G.chrT (.mu t D.R.m (j + 1))
  om := castOm G (show j + 1 + 1 = D.R.m by omega) (Wl.om (.mu t D.R.m (j + 1)))
  weil := castOm_weil G (show j + 1 + 1 = D.R.m by omega) (Wl.om_is (.mu t D.R.m (j + 1)) ⟨le_rfl, by omega⟩)
  vT := volAt hM (.grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩

variable {M} in

noncomputable def chainFrom (hM : M.Is t) : (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) →
    Chain Wl.ψ (G.V (.grid D.R.m D.R.m)) σ (besAt G hM j σ hj vN)
  | 0, j, hj, vN => .last (lastAt G Wl t hM j hj vN)
  | σ + 1, j, hj, vN =>
    .step (jacAt G hM (j + 1) (σ + 1) (by omega)) (besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
      (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
        (besDecAt G (j + 1 + 1) σ (by omega)))
      (linkAt hM j σ hj vN (by omega) _) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
      (chainFrom hM σ (j + 1 + 1) (by omega) _)

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

theorem top_idx : 0 + 2 * ((D.R.m - 2) / 2) + 2 = D.R.m := by
  have := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  omega

variable {G t M} in

def topVN (hM : M.Is t) : VolN (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) :=
  volNOf (d := rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2) (by have := top_idx (D := D); omega))
    (nFlag_diag _ (lam _) (lam_ne _)).symm
    (topVolN G M hM.isRow (by have := D.R.two_le_m; omega) (by have := top_idx (D := D); omega))

variable {t M} in

def topLev (hM : M.Is t) : BesLev D ((D.R.m - 2) / 2) := besAt G hM 0 ((D.R.m - 2) / 2) top_idx (topVN hM)

variable {M} in

noncomputable def chain (hM : M.Is t) : Chain Wl.ψ (G.V (.grid D.R.m D.R.m)) ((D.R.m - 2) / 2) (topLev G hM) :=
  chainFrom G Wl t hM _ 0 top_idx (topVN hM)

variable {M} in

noncomputable def dataFrom (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) :
    (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) → (chainFrom G Wl t hM σ j hj vN).Data
  | 0, j, hj, _ => (getD t D.R.m D.R.m d j (by omega),
      castSch G (show j + 1 + 1 = D.R.m by omega) (getD t D.R.m D.R.m d (j + 1) (by omega)))
  | σ + 1, j, hj, _ => (getD t D.R.m D.R.m d j (by omega), getD t D.R.m D.R.m d (j + 1) (by omega),
      dataFrom hM d σ (j + 1 + 1) (by omega) _)

def AllTheta (d : PureT G (downPath t D.R.m D.R.m)) : Prop :=
  Path.Fam.All (fun a (f : Sch G a) => IsThetaFunO Wl.ψ (G.pS a.pair) (G.pT a.pair) f) d

variable {M} in
theorem dataFrom_isTheta (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)),
      (chainFrom G Wl t hM σ j hj vN).IsTheta (dataFrom G Wl t hM d σ j hj vN)
  | 0, j, hj, _ => ⟨getD_all _ t D.R.m D.R.m d hd j (by omega),
      castSch_theta G _ (getD_all _ t D.R.m D.R.m d hd (j + 1) (by omega))⟩
  | σ + 1, j, hj, _ => ⟨getD_all _ t D.R.m D.R.m d hd j (by omega), getD_all _ t D.R.m D.R.m d hd (j + 1) (by omega),
      dataFrom_isTheta hM d hd σ (j + 1 + 1) (by omega) _⟩

variable {M} in

noncomputable def chainData (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) : (chain G Wl t hM).Data :=
  dataFrom G Wl t hM d _ 0 top_idx (topVN hM)

variable {M} in

theorem chainData_isTheta (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) :
    (chain G Wl t hM).IsTheta (chainData G Wl t hM d) :=
  dataFrom_isTheta G Wl t hM d hd _ 0 top_idx (topVN hM)

end GlobalTheory.RowChain
