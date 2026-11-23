import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.TieAlg

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section act

variable (P : M.Par)

theorem act_diag (d : M.Ty P → (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (Matrix.diagonal d) f = fun ρ => (d ρ).1 (f ρ) := by
  funext ρ
  show ∑ π', (Matrix.diagonal d ρ π').1 (f π') = (d ρ).1 (f ρ)
  rw [Finset.sum_eq_single ρ (fun b _ hb => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hb)]; rfl)
    (fun h => absurd (Finset.mem_univ ρ) h), Matrix.diagonal_apply_eq]

theorem act_sc (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := by
  rw [MA.sc, Matrix.scalar_apply, act_diag]

theorem act_smul (c : ℂ) (a : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • a) f = c • MA.actA P a f := by
  rw [Algebra.smul_def, Gauge.actA_mul, Matrix.algebraMap_eq_diagonal, act_diag]
  rfl

theorem sc_star (w : (MA.DQ P).Pr) : star (MA.sc P (MA.DQ P) w) = MA.sc P (MA.DQ P) (star w) := by
  rw [MA.sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, MA.sc,
    Matrix.scalar_apply]
  rfl

def opA (l : Fin P.r) : Fin 6 → MA.A P (MA.DQ P) :=
  ![MA.pA P (MA.DQ P) l, MA.cA P (MA.DQ P) l, MA.ciA P (MA.DQ P) l, MA.pbA P (MA.DQ P) l, MA.cbA P (MA.DQ P) l,
    MA.cbiA P (MA.DQ P) l]

def fnA : Fin 6 → MA.A P (MA.DQ P) :=
  ![MA.zA P (MA.DQ P), MA.ziA P (MA.DQ P), MA.zbA P (MA.DQ P), MA.zbiA P (MA.DQ P), MA.ggA P (MA.DQ P),
    MA.ggiA P (MA.DQ P)]

def gM (l : ℕ) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Wd.Letter ℂ S)) (e : Wd.Ix S) : MA.A P (MA.DQ P) :=
  ∑ e', (Fr.ofWord L (MA.startM P (MA.DQ P) l) w).F e e' * Wd.uw (MA.sites P (MA.DQ P)) w e'

end act

section tied

variable {P : M.Par} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : V →ₗ[ℂ] (M.Ty P → MA.SmQ P.r P.TT))

def IsIntertwinedEndomorphism (X : Module.End ℂ V) (am : MA.A P (MA.DQ P)) : Prop := ∀ Φ, τ (X Φ) = MA.actA P am (τ Φ)

def intertwiningRelation : SRel (Q.Pr V) (MA.A P (MA.DQ P)) where
  r a am := IsIntertwinedEndomorphism τ a.1 am ∧ IsIntertwinedEndomorphism τ (star a).1 (star am)
  zero := by
    refine ⟨fun Φ => ?_, fun Φ => ?_⟩
    · rw [Gauge.actA_zero]; exact map_zero τ
    · rw [star_zero, star_zero, Gauge.actA_zero]; exact map_zero τ
  one := by
    refine ⟨fun Φ => ?_, fun Φ => ?_⟩
    · rw [jdh_actA_one]; rfl
    · rw [star_one, star_one, jdh_actA_one]; rfl
  add {a a' b b'} h h' := by
    refine ⟨fun Φ => ?_, fun Φ => ?_⟩
    · rw [Gauge.actA_add, ← h.1, ← h'.1, ← map_add]; rfl
    · rw [star_add, star_add, Gauge.actA_add, ← h.2, ← h'.2, ← map_add]; rfl
  mul {a a' b b'} h h' := by
    refine ⟨fun Φ => ?_, fun Φ => ?_⟩
    · rw [Gauge.actA_mul, ← h'.1, ← h.1]; rfl
    · rw [star_mul, star_mul, Gauge.actA_mul, ← h.2, ← h'.2]; rfl
  smul c a a' h := by
    refine ⟨fun Φ => ?_, fun Φ => ?_⟩
    · rw [act_smul, ← h.1, ← map_smul]; rfl
    · rw [star_smul, star_smul, act_smul, ← h.2, ← map_smul]; rfl
  star {a a'} h := ⟨h.2, by rw [star_star, star_star]; exact h.1⟩

theorem tiedOp_inv {a b : Q.Pr V} {a' b' : MA.A P (MA.DQ P)} (h : IsIntertwinedEndomorphism τ a.1 a') (h1 : a * b = 1)
    (h2 : b' * a' = 1) : IsIntertwinedEndomorphism τ b.1 b' := fun Φ => by
  have e : a.1 (b.1 Φ) = Φ := by
    have : (a * b).1 Φ = Φ := by rw [h1]; rfl
    exact this
  rw [← jdh_actA_one P (τ (b.1 Φ)), ← h2, Gauge.actA_mul, ← h, e]

theorem tiedRel_invClosed : (intertwiningRelation τ).InvClosed := fun a a' b b' h h1 h2 h3 h4 =>
  ⟨tiedOp_inv τ h.1 h1 h4, tiedOp_inv τ h.2 (by rw [← star_mul, h2, star_one]) (by rw [← star_mul, h3, star_one])⟩

variable {τ}

theorem tied_mkP {X Xs : Module.End ℂ V} {am : MA.A P (MA.DQ P)} (h : IsIntertwinedEndomorphism τ X am) (hs : IsIntertwinedEndomorphism τ Xs (star am)) :
    (intertwiningRelation τ).r (Q.mkP X Xs) am := ⟨h, hs⟩

theorem tiedOp_neg_sc {X : Module.End ℂ V} {w w' : (MA.DQ P).Pr} (h : IsIntertwinedEndomorphism τ X (MA.sc P (MA.DQ P) w))
    (hw : w'.1 = -w.1) : IsIntertwinedEndomorphism τ (-X) (MA.sc P (MA.DQ P) w') := fun Φ => by
  rw [LinearMap.neg_apply, map_neg, h, act_sc, act_sc, hw]
  rfl

end tied

section radial

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)}

structure BaseTie (X : Q.ActualOps P.k P.r z z' π π')
    (τ : Q.RadSp P.k P.r z z' π π' →ₗ[ℂ] (M.Ty P → MA.SmQ P.r P.TT)) : Prop where
  op : ∀ l j, IsIntertwinedEndomorphism τ (X.op l j) (opA P l j)
  fn : ∀ j, IsIntertwinedEndomorphism τ (X.fn j) (fnA P j)
  t : ∀ (Y : ℝ) a b, IsIntertwinedEndomorphism τ (X.t (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)

omit [FiniteDimensional ℂ Wp] in

theorem word_tied {X : Q.ActualOps P.k P.r z z' π π'} {μ : Measure (Mt P.k P.r)}
    {L : R.LevelData (Q.Pr (Q.RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Q.Pr (Q.RadSp P.k P.r z z' π π'))}
    {l0 : ℕ} (hD : P5.IsData P z z' π π' X μ L st l0)
    {τ : Q.RadSp P.k P.r z z' π π' →ₗ[ℂ] (M.Ty P → MA.SmQ P.r P.TT)} (hB : BaseTie X τ)
    {Lm : R.LevelData (MA.A P (MA.DQ P)) P.r} (hM : MA.IsModelLevel P (MA.DQ P) Lm) (hMs : Fr.IsStarLevel Lm)
    (hMst : Fr.IsLevelStart Lm (MA.startM P (MA.DQ P) l0))
    {S : Type} [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (hw : Fr.admitted st w)
    (Φ : Q.RadSp P.k P.r z z' π π') (e : Wd.Ix S) :
    τ (P5.act ((Fr.ofWord L st w).F * P5.bTall L w) (Top.firstStateVector Φ) e) = MA.actA P (gM P l0 Lm w e) (τ Φ) := by
  obtain ⟨-, -, hA, hQ, hq, hinv, hSL, hst⟩ := hD
  obtain ⟨ap, -, ac, aci, -, -, aζ, aζi, aζb, aζbi, aG, aGi, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, mζ, mζi, mζb, mζbi, mG, mGi, -⟩ := hM
  have hF : FnRel (intertwiningRelation τ) L Lm := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [aζ, mζ]; exact tied_mkP (hB.fn 0) (by rw [MA.zA, sc_star]; exact hB.fn 2)
    · rw [aζi, mζi]; exact tied_mkP (hB.fn 1) (by rw [MA.ziA, sc_star]; exact hB.fn 3)
    · rw [aζb, mζb]; exact tied_mkP (hB.fn 2) (by rw [MA.zbA, sc_star]; exact hB.fn 0)
    · rw [aζbi, mζbi]; exact tied_mkP (hB.fn 3) (by rw [MA.zbiA, sc_star]; exact hB.fn 1)
    · rw [aG, mG]; exact tied_mkP (hB.fn 4) (by rw [MA.ggA, sc_star]; exact hB.fn 4)
    · rw [aGi, mGi]; exact tied_mkP (hB.fn 5) (by rw [MA.ggiA, sc_star]; exact hB.fn 5)
  have hQQ : ∀ Y, star Y = Y →
      ((intertwiningRelation τ).mat (Fin 2)).r (st.QQ Y) ((MA.startM P (MA.DQ P) l0).QQ Y) := by
    intro Y hY
    obtain ⟨y, rfl⟩ : ∃ y : ℝ, Y = (y : ℂ) := ⟨Y.re, (Complex.conj_eq_iff_re.1 hY).symm⟩
    have one : ∀ a b, IsIntertwinedEndomorphism τ (st.QQ y a b).1 ((MA.startM P (MA.DQ P) l0).QQ y a b) := fun a b Φ => by
      rw [hQ]
      show τ (M.sgn P l0 • X.t (y : ℂ) a b Φ) = MA.actA P (M.sgn P l0 • MA.QQr P (MA.DQ P) (y : ℂ) a b) (τ Φ)
      rw [map_smul, act_smul, hB.t y a b]
    intro a b
    refine ⟨one a b, ?_⟩
    have h1 : star (st.QQ y a b) = st.QQ y b a := by
      have := congrFun (congrFun (hst.start.herm _ hY) b) a
      rwa [Matrix.conjTranspose_apply] at this
    have h2 : star ((MA.startM P (MA.DQ P) l0).QQ y a b) = (MA.startM P (MA.DQ P) l0).QQ y b a := by
      have := congrFun (congrFun (hMst.start.herm _ hY) b) a
      rwa [Matrix.conjTranspose_apply] at this
    rw [h1, h2]
    exact one b a
  have hrec := admissible_rec_of_admissible _ S _ L st w hw
  have hfr := (ofWord_rel (tiedRel_invClosed τ) hF hSL hMs hst hMst hq hinv hQQ w hrec).2
  have hsite : ∀ l, (intertwiningRelation τ).Site (P5.site L l) (MA.siteA P (MA.DQ P) l) := fun l => by
    refine ⟨?_, ?_, ?_⟩
    · show (intertwiningRelation τ).r (L.p l) (MA.pA P (MA.DQ P) l)
      rw [ap]
      exact tied_mkP (hB.op l 0) (by rw [MA.pA, sc_star]; exact tiedOp_neg_sc (hB.op l 3) rfl)
    · show (intertwiningRelation τ).r (L.c l) (MA.cA P (MA.DQ P) l)
      rw [ac]
      exact tied_mkP (hB.op l 1) (by rw [MA.cA, sc_star]; exact hB.op l 4)
    · show (intertwiningRelation τ).r (L.ci l) (MA.ciA P (MA.DQ P) l)
      rw [aci]
      exact tied_mkP (hB.op l 2) (by rw [MA.ciA, sc_star]; exact hB.op l 5)
  have hbT : ((intertwiningRelation τ).mat (Wd.Ix S)).r (P5.bTall L w)
      ((MA.sites P (MA.DQ P)).map fun σ => Wd.bT σ w).prod := by
    have e1 : ((MA.sites P (MA.DQ P)).map fun σ => Wd.bT σ w) =
        (List.finRange P.r).reverse.map fun l => Wd.bT (MA.siteA P (MA.DQ P) l) w := by
      simp [MA.sites, List.ofFn_eq_map, List.map_reverse, Function.comp_def]
    rw [e1]
    exact SRel.listProd _ fun l _ => SRel.bT (hsite l) w
  have hall := (SRel.mul _ hfr.F hbT e Wd.e1).1 Φ
  have eL : P5.act ((Fr.ofWord L st w).F * P5.bTall L w) (Top.firstStateVector Φ) e =
      (((Fr.ofWord L st w).F * P5.bTall L w) e Wd.e1).1 Φ := by
    unfold P5.act
    rw [Finset.sum_eq_single Wd.e1]
    · congr 1
      exact if_pos rfl
    · intro b _ hb
      have : Top.firstStateVector (S := S) Φ b = 0 := if_neg hb
      rw [this, map_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [eL, hall, Matrix.mul_apply]
  rfl

end radial

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
