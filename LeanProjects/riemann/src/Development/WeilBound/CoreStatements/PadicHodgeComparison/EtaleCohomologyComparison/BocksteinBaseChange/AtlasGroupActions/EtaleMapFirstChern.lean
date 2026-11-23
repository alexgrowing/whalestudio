import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.TowerSmulZero

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueE

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem kill_acr (P : PAlg l ⥤ Type) (n : ℕ) (T : El P) (x : (CH.modF (AcrEl P n)).obj T) :
    ((l : Acris l) ^ n) • x = 0 :=
  modF_smul (AcrEl P n) _ (fun T => show algebraMap (Acris l) (((elπ P).obj T).Acr n) ((l : Acris l) ^ n) = 0 by
    rw [map_pow, map_natCast]; exact ((elπ P).obj T).pow_l_acr n) T x

theorem kill_MS (P : PAlg l ⥤ Type) (n j : ℕ) (x : (MSys P j).M n) : ((l : Acris l) ^ n) • x = 0 :=
  tower_smul_zero (fun n => CH.modF (AcrEl P n)) (fun n => redEl P n.le_succ) j n _ (fun T y => kill_acr P n T y) x

variable (e : E.EtFam l K) (he : e.Red)

def eMap (M : Model l K) (j : ℕ) : M.T j →+ (M.MS j).lim where
  toFun v := ⟨fun n => e M n j (v.lev n), fun n => (he M n j _).trans (congrArg (e M n j) (v.2 n))⟩
  map_zero' := Subtype.ext (funext fun n => map_zero (e M n j))
  map_add' v w := Subtype.ext (funext fun n => map_add (e M n j) (v.lev n) (w.lev n))

theorem eMap_lin_lev (M : Model l K) (j : ℕ) (f : ℤ_[l] →+* Acris l) (z : ℤ_[l]) (v : M.T j) (n : ℕ) :
    (eMap e he M j (z • v)).1 n = f z • (eMap e he M j v).1 n :=
  ((congrArg (e M n j) (GlobalTheory.EtC.HtL.smul_eq l n n le_rfl M.spc j 0 z (v.1 n))).trans
    (map_nsmul (e M n j) _ _)).trans (padic_smul f n ((eMap e he M j v).1 n) (kill_MS M.P n j _) z).symm

theorem eMap_lin (M : Model l K) (j : ℕ) (f : ℤ_[l] →+* Acris l) (z : ℤ_[l]) (v : M.T j) :
    eMap e he M j (z • v) = f z • eMap e he M j v :=
  lim_ext fun n => (eMap_lin_lev e he M j f z v n).trans (lim_smul_val _ _ _ n).symm

theorem eMap_act (hq : e.Equi) (M : Model l K) (j : ℕ) (σ : Gal(PadicAlgCl l/K)) (v : M.T j) :
    eMap e he M j (GlobalTheory.EtC.galHl l (PadicAlgCl l) M.q j 0 σ v) = (M.galS j σ).lim (eMap e he M j v) :=
  lim_ext fun n => hq M n j σ (v.lev n)

theorem eMap_phi (hp : e.Phi) (M : Model l K) (j : ℕ) (v : M.T j) :
    (M.phiS j).lim (eMap e he M j v) = eMap e he M j v :=
  lim_ext fun n => hp M n j (v.lev n)

theorem eMap_nat (hn : e.Natu) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (j : ℕ) (v : N.T j) :
    eMap e he M j (Model.pullT u hu j v) = (Model.pullS u hu j).lim (eMap e he N j v) :=
  lim_ext fun n => hn M N u hu n j (v.lev n)

theorem eMap_cup (hc : e.Cup) (M : Model l K) {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)) (h : M.CupT x y z)
    (n : ℕ) : (eMap e he M (i + j) z).1 n = (CH.mulP (AcrEl M.P n)).cup rfl ((eMap e he M i x).1 n) ((eMap e he M j y).1 n) :=
  (congrArg (e M n (i + j)) (h n)).trans (hc M n i j (x.lev n) (y.lev n))

theorem eMap_one (ho : e.One) (M : Model l K) : ∃ v : M.T 0, ∀ n, (eMap e he M 0 v).1 n = CH.oneH (AcrEl M.P n) :=
  (ho M).elim fun v hv => ⟨v, hv⟩

theorem etale_map_first_chern (h1 : e.C1) (M : Model l K) (D : E.LineData M.X) (c : Acris l)
    (hc : c = ACris.periodT (untilt_epsilon (p := l))) :
    ∃ v : M.T 2, E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (c • eMap e he M 2 v).1 := by
  subst hc
  exact (h1 M D).elim fun v hv => ⟨v, by rw [lim_smul_fun]; exact hv⟩

def emap (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (e : E.EtFam l K) (he : e.Good) : EMap Model.Sm (dat Amp) where
  e {M} _ j := eMap e he.red M j
  lin {M} _ _ j z v := eMap_lin e he.red M j (per l K).z z v
  act {M} _ _ j _ v := eMap_act e he.red he.equi M j _ v
  phi {M} _ _ j v := eMap_phi e he.red he.phi M j v
  nat {_ _ u hu _ _} _ _ _ j v := eMap_nat e he.red he.nat u hu j v
  cup {M} _ _ _ _ x y z h := eMap_cup e he.red he.cup M x y z h
  one {M} _ _ := eMap_one e he.red he.one M
  c1 {M} a _ := etale_map_first_chern e he.red he.c1 M a.1 (per l K).t rfl

end GlueE

theorem glueE : GlueE := fun _ _ _ Amp hE => hE.elim fun e he => ⟨GlueE.emap Amp e he⟩

end CrystallineSemistableComparison
