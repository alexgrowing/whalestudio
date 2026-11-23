import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinMComp

variable {D : D7}

theorem eq_zero_of_le_exp (x : WithZero (Multiplicative ℤ)) (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  have h1 := h (Int.toNat (-(Multiplicative.toAdd m)) + 1)
  have e : ((m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd m) := rfl
  rw [e, WithZero.exp_le_exp] at h1
  omega

theorem afIso_indP (w : GlobalTheory.FinPl.Pl D) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = w) :
    GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w)) P = 1 := by
  have hs := fun n =>
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E).choose_spec.2.2.2
      (GlobalTheory.FinPl.KOpen.indP D (· = w)) 1 P n
  have h0 : (GlobalTheory.FinPl.KOpen.indP D (· = w)) (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ 1 = 0 := by
    have := GlobalTheory.FinPl.KOpen.evalV_indP (D := D) (· = w) (P.under (𝓞 D.host.F))
    rw [if_pos hP] at this
    rw [map_one, sub_eq_zero]
    exact this
  have h1 : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E
      ((1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w)) P
      - algebraMap D.host.E _ (algebraMap D.host.F D.host.E 1)) ≤ WithZero.exp (-(n : ℤ)) := fun n =>
    hs n (by rw [h0, Valuation.map_zero]; exact zero_le')
  have h2 := eq_zero_of_le_exp _ h1
  rw [Valuation.zero_iff, map_one, map_one, sub_eq_zero] at h2
  exact h2

theorem indicatorAdele_mul_eq_zero (w : GlobalTheory.FinPl.Pl D) (z : Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w z = 0) :
    (GlobalTheory.FinPl.KOpen.indP D (· = w) ⊗ₜ[D.host.F] (1 : D.host.E)) * z = 0 := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v 0
  rw [map_mul, map_zero, GlobalTheory.FinPl.KOpen.compFin_e]
  by_cases hv : v = w
  · subst hv; rw [hz, mul_zero]
  · rw [if_neg hv, zero_mul]

theorem adAt_toEAf_eq_zero (w : GlobalTheory.FinPl.Pl D) (a : AE D) (ha : GlobalTheory.FinPl.compAt D w a = 0)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = w) :
    GlobalTheory.Mem.Col2.adAt D.host.F P (toEAf D a) = 0 := by
  have h0 := congrArg (fun y => GlobalTheory.Mem.Col2.adAt D.host.F P
    ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom y))
    (indicatorAdele_mul_eq_zero w (finPart D a) ha)
  simp only [map_mul, map_zero] at h0
  have e1 : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom
      (GlobalTheory.FinPl.KOpen.indP D (· = w) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      (1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w) := rfl
  rw [e1, GlobalTheory.Mem.Col2.adAt_apply D.host.F P ((1 : D.host.E) ⊗ₜ[D.host.F] _), afIso_indP w P hP, one_mul] at h0
  exact h0

theorem adAt_finM_eq_one : ∀ (D : D7) (V : HSp D) {n : ℕ} (hn : V.rank = n) (Pset : GlobalTheory.FinPl.Pl D → Prop) (h : GA D V),
    h ∈ GlobalTheory.FinPl.grpAt V Pset → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ Pset (P.under (𝓞 D.host.F)) → ∀ r k,
      adAt D.host.F P (finM V hn h r k) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion D.host.E)) r k := by
  intro D V n hn Pset h hh P hP r k
  subst hn
  rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply]
  have hmem := (GlobalTheory.FinPl.SetCut.mem_congGrp_iff V _ h).1 hh r k
  have hz := adAt_toEAf_eq_zero _ _ (((GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D Pset _).1 hmem).2 _ hP) P rfl
  have e : Formalism.L2.Theta.mt V h r k = (Formalism.L2.Theta.mt V h - 1) r k + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r k := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [e, RingHom.map_add (toEAf D), RingHom.map_add (GlobalTheory.Mem.Col2.adAt D.host.F P), hz, zero_add]
  by_cases hrk : r = k
  · subst hrk; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, hrk]

end GlobalTheory.FinMComp
