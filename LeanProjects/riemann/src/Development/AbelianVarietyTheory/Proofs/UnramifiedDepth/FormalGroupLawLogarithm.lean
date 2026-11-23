import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.LawLog

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

def twoVars (k : Type) [CommRing k] (d : ℕ) : Fin 2 × Fin d → MvPowerSeries (Fin d ⊕ Fin d) k :=
  fun q => X (if q.1 = 0 then Sum.inl q.2 else Sum.inr q.2)

def oneVar (k : Type) [CommRing k] (d : ℕ) : Fin 1 × Fin d → MvPowerSeries (Fin d) k :=
  fun q => X q.2

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_twoVars (q : Fin 2 × Fin d) : constantCoeff (twoVars k d q) = 0 := by simp [twoVars]

theorem cc_oneVar (q : Fin 1 × Fin d) : constantCoeff (oneVar k d q) = 0 := by simp [oneVar]

theorem hs_twoVars : HasSubst (twoVars k d) := hasSubst_of_constantCoeff_zero cc_twoVars

theorem hs_oneVar : HasSubst (oneVar k d) := hasSubst_of_constantCoeff_zero cc_oneVar

def sndEmb (d : ℕ) : Fin 1 × Fin d ↪ Fin d :=
  ⟨Prod.snd, fun _ _ h => Prod.ext (Subsingleton.elim _ _) h⟩

theorem coeff_single_oneVar (f : PS k 1 d) (b : Fin d) :
    coeff (Finsupp.single b 1) (subst (oneVar k d) f) = coeff (Finsupp.single ((0 : Fin 1), b) 1) f := by
  have h1 : subst (oneVar k d) f = rename (sndEmb d) f := by
    rw [rename_eq_subst]; rfl
  have h2 : Finsupp.single b 1 = Finsupp.embDomain (sndEmb d) (Finsupp.single ((0 : Fin 1), b) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  rw [h1, h2, coeff_embDomain_rename]

theorem subst_oneVar {n : ℕ} {τ : Type} [Finite τ] (T : Fin n × Fin d → MvPowerSeries τ k)
    (hT : ∀ q, constantCoeff (T q) = 0) (a : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (f : PS k 1 d) :
    subst (fun i => subst T (a i)) (subst (oneVar k d) f) = subst T (ev ![a] f) := by
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h1 : HasSubst (fun i => (subst T (a i) : MvPowerSeries τ k)) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hTs hT (ha i)
  have h2 : HasSubst (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt k n d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j; exact ha i
  unfold ev
  rw [subst_comp_subst_apply hs_oneVar h1, subst_comp_subst_apply h2 hTs]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  simp only [oneVar]
  rw [subst_X h1]
  rfl

theorem add_pt (G : FGLaw k d) : G.add (pt k (n := 2) d 0) (pt k d 1) = G.F := by
  funext c
  show ev (n := 2) ![pt k d 0, pt k d 1] (G.F c) = G.F c
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) p.1 p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  unfold ev
  rw [e, subst_self]
  rfl

theorem exists_logFGL :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (R : Type) [CommRing R] [Algebra R C], (∀ r : R, IsIntV v (algebraMap R C r)) →
    ∀ (d : ℕ) (G : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FGLaw R d), ∃ L : LogFGL v d, ∀ a,
      L.F a = subst (fun q : Fin 2 × Fin d => (X (if q.1 = 0 then Sum.inl q.2 else Sum.inr q.2) : MvPowerSeries (Fin d ⊕ Fin d) C))
        (MvPowerSeries.map (algebraMap R C) (G.F a))) := by
  intro C _ _ v R _ _ hR d G
  set G' : FGLaw C d := GlobalTheory.FBMap.mapLaw (algebraMap R C) G with hG'
  obtain ⟨ℓ, h0, h1, hadd⟩ := GlobalTheory.FormalLog.logSt C d G'
  rw [add_pt] at hadd
  refine ⟨{ lg := fun a => subst (oneVar C d) (ℓ a)
            lg_const := fun a => constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (h0 a)
            lg_lin := fun a b => ?_
            F := fun a => subst (twoVars C d) (G'.F a)
            F_int := fun a α => ?_
            F_const := fun a => constantCoeff_subst_eq_zero hs_twoVars cc_twoVars (G'.const a)
            lg_F := fun a => ?_ }, fun a => rfl⟩
  · rw [coeff_single_oneVar]
    have := congrFun (congrFun h1 a) b
    rw [Matrix.one_apply] at this
    exact this
  · have e : subst (twoVars C d) (G'.F a) =
        MvPowerSeries.map (algebraMap R C) (subst (twoVars R d) (G.F a)) := by
      rw [MvPowerSeries.map_subst hs_twoVars]
      congr 1
      funext q
      simp [twoVars]
    rw [e, coeff_map]
    exact hR _
  · have hp : ∀ (j : Fin 2) i, constantCoeff (pt C (n := 2) d j i) = 0 := fun j i => by simp [pt]
    have e0 : (fun b => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
        fun i => subst (twoVars C d) (pt C (n := 2) d 0 i) := by
      funext i; rw [pt, subst_X hs_twoVars]; simp [twoVars]
    have e1 : (fun b => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
        fun i => subst (twoVars C d) (pt C (n := 2) d 1 i) := by
      funext i; rw [pt, subst_X hs_twoVars]; simp [twoVars]
    rw [e0, e1, subst_oneVar _ cc_twoVars _ G'.const, subst_oneVar _ cc_twoVars _ (hp 0),
      subst_oneVar _ cc_twoVars _ (hp 1), ← subst_add hs_twoVars]
    congr 1
    exact congrFun hadd a

end GlobalTheory.LawLog
