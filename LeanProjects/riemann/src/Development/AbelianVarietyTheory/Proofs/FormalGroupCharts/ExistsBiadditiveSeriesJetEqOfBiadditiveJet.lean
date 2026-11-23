import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetEqBilinearSeriesOfBiadditiveStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculus
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLogEndomorphismLinear

set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin IsInvPair)
open GlobalTheory.ChartCmp GlobalTheory.FBMap

namespace GlobalTheory.ChartBilin

variable {k : Type} [CommRing k] {d : ℕ}

def evP {m n : ℕ} (b : Fin m → Pt k n d) (u : Pt k m d) : Pt k n d := fun i => ev b (u i)

def lin {n : ℕ} (A : Matrix (Fin d) (Fin d) k) (u : Pt k n d) : Pt k n d := fun i => ∑ j, C (A i j) * u j

theorem nc1 {n : ℕ} {u : Pt k n d} (hu : NoConst u) : ∀ j, NoConst (![u] j) := by
  intro j; fin_cases j; exact hu

theorem nc2 {n : ℕ} {u v : Pt k n d} (hu : NoConst u) (hv : NoConst v) : ∀ j, NoConst (![u, v] j) := by
  intro j; fin_cases j; exacts [hu, hv]

theorem nc3 {n : ℕ} {u v w : Pt k n d} (hu : NoConst u) (hv : NoConst v) (hw : NoConst w) :
    ∀ j, NoConst (![u, v, w] j) := by
  intro j; fin_cases j; exacts [hu, hv, hw]

theorem nc_add {n : ℕ} {u v : Pt k n d} (hu : NoConst u) (hv : NoConst v) : NoConst (u + v) :=
  fun i => by simp [hu i, hv i]

theorem ev_ev {l m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) {a : Fin l → Pt k m d}
    (ha : ∀ j, NoConst (a j)) (f : PS k l d) : ev b (ev a f) = ev (fun j => evP b (a j)) f :=
  subst_comp_subst_apply (hasSubst_of ha) (hasSubst_of hb) f

theorem germEv_germEv_two_points {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) {u v : Pt k m d}
    (hu : NoConst u) (hv : NoConst v) (f : PS k 2 d) : ev b (ev ![u, v] f) = ev ![evP b u, evP b v] f := by
  rw [ev_ev hb (nc2 hu hv)]
  congr 1; funext j; fin_cases j <;> rfl

theorem evalPoints_comp {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (φ : Pt k 1 d) {u : Pt k m d}
    (hu : NoConst u) : evP b (comp1 φ u) = comp1 φ (evP b u) := by
  funext i
  change ev b (ev ![u] (φ i)) = ev ![evP b u] (φ i)
  rw [ev_ev hb (nc1 hu)]
  congr 1; funext j; fin_cases j; rfl

theorem evalPoints_formalGroupAdd {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (F : Pt k 2 d) {u v : Pt k m d}
    (hu : NoConst u) (hv : NoConst v) : evP b (addOf F u v) = addOf F (evP b u) (evP b v) :=
  funext fun i => germEv_germEv_two_points hb hu hv (F i)

theorem evalPoints_coordinatePoint {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (j : Fin m) :
    evP b (pt k d j) = b j :=
  funext fun i => subst_X (hasSubst_of hb) (j, i)

theorem ev_add' {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (f g : PS k m d) :
    ev b (f + g) = ev b f + ev b g := subst_add (hasSubst_of hb) f g

theorem evalPoints_add {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (u v : Pt k m d) :
    evP b (u + v) = evP b u + evP b v := funext fun i => ev_add' hb (u i) (v i)

theorem evalPoints_linear {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (A : Matrix (Fin d) (Fin d) k)
    (u : Pt k m d) : evP b (lin A u) = lin A (evP b u) := by
  funext i
  simp only [evP, lin, ev]
  rw [← coe_substAlgHom (hasSubst_of hb), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom, subst_C]

theorem ev_bilSer {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (β : Matrix (Fin d) (Fin d) k)
    (u v : Pt k m d) : ev b (bilSer β u v) = bilSer β (evP b u) (evP b v) := by
  simp only [evP, bilSer, ev]
  rw [← coe_substAlgHom (hasSubst_of hb), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, coe_substAlgHom, subst_C]

theorem ev_self2 (f : PS k 2 d) : ev (n := 2) ![pt k d 0, pt k d 1] f = f := by
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [ev, e, subst_self]
  rfl

theorem germComp1_germComp1_eq_substitute {n : ℕ} (φ : Pt k 1 d) {ψ : Pt k 1 d} (hψ : NoConst ψ) {u : Pt k n d} (hu : NoConst u) :
    comp1 φ (comp1 ψ u) = evP ![u] (comp1 φ ψ) := (evalPoints_comp (nc1 hu) φ hψ).symm

theorem germComp1_cancel_of_inverse {n : ℕ} {φ ψ : Pt k 1 d} (hψ : NoConst ψ) (h : comp1 φ ψ = pt k (n := 1) d 0) {u : Pt k n d}
    (hu : NoConst u) : comp1 φ (comp1 ψ u) = u := by
  rw [germComp1_germComp1_eq_substitute φ hψ hu, h, evalPoints_coordinatePoint (nc1 hu)]
  rfl

theorem germComp1_zero_of_noConstantCoeff {n : ℕ} {φ : Pt k 1 d} (hφ : NoConst φ) : comp1 φ (0 : Pt k n d) = 0 := by
  funext i
  change subst (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) (φ i) = 0
  have e : (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) = 0 := by
    funext p; simp
  rw [e]
  exact subst_zero_of_constantCoeff_zero (hφ i)

theorem bilSer_zero_left {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (v : Pt k n d) : bilSer β 0 v = 0 := by
  simp [bilSer]

theorem bilSer_zero_right {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (u : Pt k n d) : bilSer β u 0 = 0 := by
  simp [bilSer]

theorem bilSer_add_left {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (u u' v : Pt k n d) :
    bilSer β (u + u') v = bilSer β u v + bilSer β u' v := by
  simp only [bilSer, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

theorem bilSer_add_right {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (u v v' : Pt k n d) :
    bilSer β u (v + v') = bilSer β u v + bilSer β u v' := by
  simp only [bilSer, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem bilSer_swap {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (u v : Pt k n d) :
    bilSer β v u = bilSer β.transpose u v := by
  simp only [bilSer, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bilSer_lin_right {n : ℕ} (β A : Matrix (Fin d) (Fin d) k) (u v : Pt k n d) :
    bilSer β u (lin A v) = bilSer (β * A) u v := by
  simp only [bilSer, lin, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem bilSer_lin_left {n : ℕ} (β A : Matrix (Fin d) (Fin d) k) (u v : Pt k n d) :
    bilSer β (lin A u) v = bilSer (A.transpose * β) u v := by
  rw [bilSer_swap, bilSer_lin_right, bilSer_swap, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem coeff_bilSer (β : Matrix (Fin d) (Fin d) k) (i j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)
      (bilSer β (pt k (n := 2) d 0) (pt k d 1)) = β i j := by
  classical
  have key : ∀ i' j' : Fin d, (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 : Fin 2 × Fin d →₀ ℕ) =
      Finsupp.single ((0 : Fin 2), i') 1 + Finsupp.single ((1 : Fin 2), j') 1 ↔ i = i' ∧ j = j' := by
    intro i' j'
    refine ⟨fun h => ⟨?_, ?_⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
    · have := DFunLike.congr_fun h (0, i)
      by_contra hne
      simp [Finsupp.single_apply, Ne.symm hne] at this
    · have := DFunLike.congr_fun h (1, j)
      by_contra hne
      simp [Finsupp.single_apply, Ne.symm hne] at this
  simp only [bilSer, pt, map_sum, coeff_C_mul, X_def, monomial_mul_monomial, coeff_monomial, key]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem eq_of_jEq_bilSer {m : ℕ} (hm : 2 ≤ m) {β γ : Matrix (Fin d) (Fin d) k}
    (h : JEq m (bilSer β (pt k (n := 2) d 0) (pt k d 1)) (bilSer γ (pt k (n := 2) d 0) (pt k d 1))) : β = γ := by
  ext i j
  rw [← coeff_bilSer β i j, ← coeff_bilSer γ i j]
  exact h _ (by simpa using hm)

theorem jEq_symm {σ : Type} {m : ℕ} {f g : MvPowerSeries σ k} (h : JEq m f g) : JEq m g f :=
  fun e he => (h e he).symm

theorem jEq_trans {σ : Type} {m : ℕ} {f g h : MvPowerSeries σ k} (h1 : JEq m f g) (h2 : JEq m g h) : JEq m f h :=
  fun e he => (h1 e he).trans (h2 e he)

theorem jEq_of_eq {σ : Type} {m : ℕ} {f g : MvPowerSeries σ k} (h : f = g) : JEq m f g := h ▸ JEq.refl m f

theorem jEq_ev {m l n : ℕ} {b : Fin l → Pt k n d} (hb : ∀ j, NoConst (b j)) {f g : PS k l d} (h : JEq m f g) :
    JEq m (ev b f) (ev b g) :=
  (GlobalTheory.ChartCmp.JCalc.jeq_calculus k m).2.2.2.1 d l n b b f g hb hb (fun _ _ => JEq.refl _ _) h

theorem exists_biadd_jEq : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (m : ℕ), 2 ≤ m → ∀ g : PS k 2 d, Biadd m B k g → ∃ g' : PS k 2 d, (∀ m', Biadd m' B k g') ∧ JEq m g g' := by
  intro R _ d O _ _ B k _ _ _ m hm g hg
  set G : FGLaw k d := mapLaw (algebraMap R k) B.G with hG
  set A : OAct O G := mapAct (algebraMap R k) B.A with hA
  obtain ⟨ℓ, hℓ, hlin, hadd⟩ := GlobalTheory.FormalLog.logSt k d G
  obtain ⟨e, -, he, hle, hel⟩ := GlobalTheory.ChartInv.exists_isInvPair k d ℓ hℓ
    (by rw [hlin, Matrix.det_one]; exact isUnit_one)
  replace hℓ : NoConst ℓ := hℓ
  replace he : NoConst e := he
  have hF : NoConst (B.FK k) := G.const
  have hα : ∀ a, NoConst (B.actK k a) := A.const
  have hp : ∀ {n : ℕ} (j : Fin n), NoConst (pt k d j) := nc_pt
  have hlog : ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      comp1 ℓ (addOf (B.FK k) u v) = comp1 ℓ u + comp1 ℓ v := by
    intro n u v hu hv
    have h0 : comp1 ℓ (addOf (B.FK k) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) := hadd
    have hb := nc2 hu hv
    have h1 := congrArg (evP ![u, v]) h0
    rw [evalPoints_add hb, evalPoints_comp hb ℓ (nc_addOf hF (hp 0) (hp 1)), evalPoints_formalGroupAdd hb _ (hp 0) (hp 1),
      evalPoints_comp hb ℓ (hp 0), evalPoints_comp hb ℓ (hp 1), evalPoints_coordinatePoint hb, evalPoints_coordinatePoint hb] at h1
    exact h1
  have hexp : ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      addOf (B.FK k) (comp1 e u) (comp1 e v) = comp1 e (u + v) := by
    intro n u v hu hv
    have h1 := hlog (nc_comp1 he hu) (nc_comp1 he hv)
    rw [germComp1_cancel_of_inverse he hle hu, germComp1_cancel_of_inverse he hle hv] at h1
    rw [← h1, germComp1_cancel_of_inverse hℓ hel (nc_addOf hF (nc_comp1 he hu) (nc_comp1 he hv))]
  have hact : ∀ (a : O) {n : ℕ} {u : Pt k n d}, NoConst u →
      comp1 ℓ (comp1 (B.actK k a) u) = lin (dLin (B.actK k a)) (comp1 ℓ u) := by
    intro a n u hu
    have h0 : comp1 ℓ (B.actK k a) = lin (dLin (B.actK k a)) ℓ :=
      funext (GlobalTheory.LogLinear.formalGroup_log_endomorphism_linear k d G ℓ (B.actK k a) hℓ hlin hadd (hα a) (A.hom a))
    rw [germComp1_germComp1_eq_substitute ℓ (hα a) hu, h0, evalPoints_linear (nc1 hu)]
    rfl
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : PS k 2 d, ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      ev ![u, v] g₀ = ev ![comp1 e u, comp1 e v] g := by
    refine ⟨ev (n := 2) ![comp1 e (pt k d 0), comp1 e (pt k d 1)] g, ?_⟩
    intro n u v hu hv
    have hb := nc2 hu hv
    rw [germEv_germEv_two_points hb (nc_comp1 he (hp 0)) (nc_comp1 he (hp 1)), evalPoints_comp hb e (hp 0), evalPoints_comp hb e (hp 1),
      evalPoints_coordinatePoint hb, evalPoints_coordinatePoint hb]
    rfl
  have hb3 := nc3 (nc_comp1 he (hp (n := 3) 0)) (nc_comp1 he (hp (n := 3) 1)) (nc_comp1 he (hp (n := 3) 2))
  obtain ⟨β, hβ⟩ : ∃ β : Matrix (Fin d) (Fin d) k, JEq m g₀ (bilSer β (pt k (n := 2) d 0) (pt k d 1)) := by
    refine ⟨_, GlobalTheory.T.jetEq_bilinearSeries_of_biadditive k d m g₀ ?_ ?_⟩
    · have h1 := jEq_ev hb3 hg.add1
      rw [ev_add' hb3, germEv_germEv_two_points hb3 (nc_addOf hF (hp 0) (hp 1)) (hp 2), germEv_germEv_two_points hb3 (hp 0) (hp 2),
        germEv_germEv_two_points hb3 (hp 1) (hp 2), evalPoints_formalGroupAdd hb3 _ (hp 0) (hp 1), evalPoints_coordinatePoint hb3, evalPoints_coordinatePoint hb3, evalPoints_coordinatePoint hb3] at h1
      rw [hg₀ (nc_add (hp 0) (hp 1)) (hp 2), hg₀ (hp 0) (hp 2), hg₀ (hp 1) (hp 2), ← hexp (hp 0) (hp 1)]
      exact h1
    · have h1 := jEq_ev hb3 hg.add2
      rw [ev_add' hb3, germEv_germEv_two_points hb3 (hp 0) (nc_addOf hF (hp 1) (hp 2)), germEv_germEv_two_points hb3 (hp 0) (hp 1),
        germEv_germEv_two_points hb3 (hp 0) (hp 2), evalPoints_formalGroupAdd hb3 _ (hp 1) (hp 2), evalPoints_coordinatePoint hb3, evalPoints_coordinatePoint hb3, evalPoints_coordinatePoint hb3] at h1
      rw [hg₀ (hp 0) (nc_add (hp 1) (hp 2)), hg₀ (hp 0) (hp 1), hg₀ (hp 0) (hp 2), ← hexp (hp 1) (hp 2)]
      exact h1
  have hmain : ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      JEq m (ev ![u, v] g) (bilSer β (comp1 ℓ u) (comp1 ℓ v)) := by
    intro n u v hu hv
    have hb := nc2 (nc_comp1 hℓ hu) (nc_comp1 hℓ hv)
    have h1 := jEq_ev hb hβ
    rw [hg₀ (nc_comp1 hℓ hu) (nc_comp1 hℓ hv), germComp1_cancel_of_inverse hℓ hel hu, germComp1_cancel_of_inverse hℓ hel hv,
      ev_bilSer hb, evalPoints_coordinatePoint hb, evalPoints_coordinatePoint hb] at h1
    exact h1
  have he0 := nc_comp1 he (hp (n := 2) 0)
  have he1 := nc_comp1 he (hp (n := 2) 1)
  have hb2 := nc2 he0 he1
  have hsym : β.transpose = β := by
    have h1 := jEq_ev hb2 hg.sym
    rw [germEv_germEv_two_points hb2 (hp 1) (hp 0), evalPoints_coordinatePoint hb2, evalPoints_coordinatePoint hb2] at h1
    have h2 := jEq_trans (jEq_symm (hmain he1 he0)) (jEq_trans h1 (hmain he0 he1))
    rw [germComp1_cancel_of_inverse he hle (hp 0), germComp1_cancel_of_inverse he hle (hp 1), bilSer_swap] at h2
    exact eq_of_jEq_bilSer hm h2
  have hbal : ∀ a : O, (dLin (B.actK k a)).transpose * β = β * dLin (B.actK k (star a)) := by
    intro a
    have h1 := jEq_ev hb2 (hg.bal a)
    rw [germEv_germEv_two_points hb2 (nc_comp1 (hα a) (hp 0)) (hp 1), germEv_germEv_two_points hb2 (hp 0) (nc_comp1 (hα _) (hp 1)),
      evalPoints_comp hb2 _ (hp 0), evalPoints_comp hb2 _ (hp 1), evalPoints_coordinatePoint hb2, evalPoints_coordinatePoint hb2] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have h2 := jEq_trans (jEq_symm (hmain (nc_comp1 (hα a) he0) he1))
      (jEq_trans h1 (hmain he0 (nc_comp1 (hα (star a)) he1)))
    rw [hact a he0, hact _ he1, germComp1_cancel_of_inverse he hle (hp 0), germComp1_cancel_of_inverse he hle (hp 1), bilSer_lin_left,
      bilSer_lin_right] at h2
    exact eq_of_jEq_bilSer hm h2
  have hg' : ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      ev ![u, v] (bilSer β (comp1 ℓ (pt k (n := 2) d 0)) (comp1 ℓ (pt k d 1))) = bilSer β (comp1 ℓ u) (comp1 ℓ v) := by
    intro n u v hu hv
    have hb := nc2 hu hv
    rw [ev_bilSer hb, evalPoints_comp hb ℓ (hp 0), evalPoints_comp hb ℓ (hp 1), evalPoints_coordinatePoint hb, evalPoints_coordinatePoint hb]
    rfl
  refine ⟨bilSer β (comp1 ℓ (pt k (n := 2) d 0)) (comp1 ℓ (pt k d 1)), fun m' => ⟨jEq_of_eq ?_, jEq_of_eq ?_,
    jEq_of_eq ?_, jEq_of_eq ?_, jEq_of_eq ?_, fun a => jEq_of_eq ?_⟩, ?_⟩
  · rw [hg' nc_zero (hp 0), germComp1_zero_of_noConstantCoeff hℓ, bilSer_zero_left]
  · rw [hg' (hp 0) nc_zero, germComp1_zero_of_noConstantCoeff hℓ, bilSer_zero_right]
  · rw [hg' (nc_addOf hF (hp 0) (hp 1)) (hp 2), hg' (hp 0) (hp 2), hg' (hp 1) (hp 2), hlog (hp 0) (hp 1),
      bilSer_add_left]
  · rw [hg' (hp 0) (nc_addOf hF (hp 1) (hp 2)), hg' (hp 0) (hp 1), hg' (hp 0) (hp 2), hlog (hp 1) (hp 2),
      bilSer_add_right]
  · rw [hg' (hp 1) (hp 0), bilSer_swap, hsym]
  · rw [hg' (nc_comp1 (hα a) (hp 0)) (hp 1), hg' (hp 0) (nc_comp1 (hα _) (hp 1)), hact a (hp 0), hact _ (hp 1),
      bilSer_lin_left, bilSer_lin_right, hbal]
  · have h1 := hmain (hp (n := 2) 0) (hp 1)
    rwa [ev_self2] at h1

end GlobalTheory.ChartBilin
