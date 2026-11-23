import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlacesStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

variable {D : D7}

theorem isRes_one {χ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} (h : χ.UnrAt PP) : IsRes χ PP 1 := by
  intro a k u hk hu
  have ha : a ∉ PP.asIdeal := by
    intro hmem
    have h0 : (u : kP PP) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact u.ne_zero h0
  have hv : Formalism.L2.Host.IsUnitAt PP (Formalism.L2.Host.atFin PP k) := by
    show Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (k : D.host.E)) = 1
    first
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
      | erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [hk, Algebra.algebraMap_self, RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).mpr ha
  have := h _ hv
  rw [MonoidHom.one_apply]
  exact this.symm

theorem tameAt_of_unrAt {χ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} (h : χ.UnrAt PP) : χ.TameAt PP := by
  intro x hx _
  exact h x hx

theorem UnrOff.mul {b : AE D} {χ χ' : (AE D)ˣ →* Circle} (h : UnrOff b χ) (h' : UnrOff b χ') : UnrOff b (χ * χ') := by
  intro x h1 h2 h3 h4
  rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, one_mul]

theorem UnrOff.inv {b : AE D} {χ : (AE D)ˣ →* Circle} (h : UnrOff b χ) : UnrOff b χ⁻¹ := by
  intro x h1 h2 h3 h4
  rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

theorem unrOff_mu (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) {P : Finset (Pl D.host.E)} {e : AE D}
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) :
    UnrOff (e + cA D e) (L.mu t ((j : ℕ) + 1)) ∧ UnrOff (e + cA D e) L.eta := by
  obtain ⟨-, hQ, -, hoff⟩ := GlobalTheory.T.levelCharacters_ramification_levelPlaces D T0 L μ0 hL t j
  have hsub : ∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') →
      PP' ∉ L.Pg ∧ PP' ∉ L.Q t ∧ (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') ∧
        ∀ PP ∈ L.Q t, ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
    intro PP' hn hc
    exact ⟨fun hm => hn ((hP PP').mpr (Or.inl hm)), fun hm => hn ((hP PP').mpr (Or.inr hm)),
      fun PP hm => hc PP ((hP PP).mpr (Or.inl hm)), fun PP hm => hc PP ((hP PP).mpr (Or.inr hm))⟩
  have h0 : UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ (L.C.mu0 j) P e (hL.mu0 j) he
      (fun PP' hn hc => hoff PP' (hsub PP' hn hc).1 (hsub PP' hn hc).2.2.1)
  have h1 : UnrOff (e + cA D e) (L.xi t) := by
    refine GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ (L.xiH t) P e (hL.xi t) he (fun PP' hn hc => ?_)
    by_contra hr
    rcases (hL.Q_ram t PP').mp hr with hm | ⟨PP, hm, hcj⟩
    · exact (hsub PP' hn hc).2.1 hm
    · exact (hsub PP' hn hc).2.2.2 PP hm hcj
  refine ⟨?_, GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ L.C.eta P e hL.eta he
    (fun PP' _ _ => L.C.isEta.unr PP')⟩
  show UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1) * L.xi t)
  exact h0.mul h1

theorem mu_val (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) {P : Finset (Pl D.host.E)} {e : AE D}
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) (x : (AE D)ˣ) (a : AE D)
    (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ) (hx : (x : AE D) = e * a + (1 - e))
    (ha : (a' : Lev.EAf D) = toEAf D a) (hu : ∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') :
    ((L.mu t ((j : ℕ) + 1) x : Circle) : ℂ) =
        (((∏ PP ∈ L.Pg, (L.chi ((j : ℕ) + 1) PP (u PP))⁻¹) * ∏ PP ∈ L.Q t, L.xiR t PP (u PP) : ℂˣ) : ℂ) ∧
      L.eta x = 1 := by
  classical
  obtain ⟨hdisj, hQ, hPg, -⟩ := GlobalTheory.T.levelCharacters_ramification_levelPlaces D T0 L μ0 hL t j
  have hPu : P = L.Pg ∪ L.Q t := by
    ext PP
    rw [hP PP, Finset.mem_union]
  have hA := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D (L.mu0 ((j : ℕ) + 1)) (L.C.mu0 j) P e
    (fun PP => if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) (hL.mu0 j) he
    (fun PP hm => by
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        exact ⟨(L.C.isMu0 j).tame PP, hL.chi j PP hg⟩
      · simp only [if_neg hg]
        have hq : PP ∈ L.Q t := ((hP PP).mp hm).resolve_left hg
        exact ⟨tameAt_of_unrAt (hQ PP hq), isRes_one (hQ PP hq)⟩) x a a' u hx ha hu
  have hB := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D (L.xi t) (L.xiH t) P e
    (fun PP => if PP ∈ L.Q t then L.xiR t PP else 1) (hL.xi t) he
    (fun PP hm => by
      by_cases hq : PP ∈ L.Q t
      · simp only [if_pos hq]
        exact ⟨hL.xi_tame t PP, hL.xiR t PP hq⟩
      · simp only [if_neg hq]
        have hg : PP ∈ L.Pg := ((hP PP).mp hm).resolve_right hq
        exact ⟨tameAt_of_unrAt (hPg PP hg), isRes_one (hPg PP hg)⟩) x a a' u hx ha hu
  have hC := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D L.eta L.C.eta P e (fun _ => 1) hL.eta he
    (fun PP _ => ⟨tameAt_of_unrAt (L.C.isEta.unr PP),
      isRes_one (L.C.isEta.unr PP)⟩) x a a' u hx ha hu
  rw [hPu, Finset.prod_union hdisj] at hA hB
  have hA' : ((L.mu0 ((j : ℕ) + 1) x : Circle) : ℂ) =
      ∏ PP ∈ L.Pg, (((L.chi ((j : ℕ) + 1) PP (u PP))⁻¹ : ℂˣ) : ℂ) := by
    rw [hA, Finset.prod_eq_one (s := L.Q t) (fun PP hm => ?_), mul_one]
    · exact Finset.prod_congr rfl (fun PP hm => by simp only [if_pos hm, MonoidHom.inv_apply])
    · simp only [if_neg (Finset.disjoint_right.mp hdisj hm), MonoidHom.one_apply, Units.val_one]
  have hB' : ((L.xi t x : Circle) : ℂ) = ∏ PP ∈ L.Q t, ((L.xiR t PP (u PP) : ℂˣ) : ℂ) := by
    rw [hB, Finset.prod_eq_one (s := L.Pg) (fun PP hm => ?_), one_mul]
    · exact Finset.prod_congr rfl (fun PP hm => by simp only [if_pos hm])
    · simp only [if_neg (Finset.disjoint_left.mp hdisj hm), MonoidHom.one_apply, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.coe_prod, Units.coe_prod]
    show ((L.mu0 ((j : ℕ) + 1) x * L.xi t x : Circle) : ℂ) = _
    rw [Circle.coe_mul, hA', hB']
  · have hC' : ((L.eta x : Circle) : ℂ) = 1 := by
      rw [hC]
      exact Finset.prod_eq_one (fun PP _ => by simp only [MonoidHom.one_apply, Units.val_one])
    exact Circle.ext (by rw [hC', Circle.coe_one])

end GlobalTheory.VecInv
