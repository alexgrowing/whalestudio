import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.LevRowSucc

open GlobalTheory.AdIsom GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

theorem mem_O_iff {w : Pl D.host.E} (a : Kw w) : a ∈ 𝒪[Kw w] ↔ Valued.v a ≤ 1 := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw w)) Valued.v).le_one_iff_le_one

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).val i j = cpt w ((β⁻¹ * x * β).val (Fin.cast h i) (Fin.cast h j)) := by
  simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

theorem ent_of_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (hx : inBasis h β w x ∈ KO (Kw w) (Fin n')) :
    (∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) ∧ ∀ i j, Valued.v (cpt w ((β⁻¹ * x⁻¹ * β).val i j)) ≤ 1 := by
  subst h
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := (mem_O_iff _).1 (h1 i j)
    rwa [inBasis_val] at this
  · have := (mem_O_iff _).1 (h2 i j)
    rwa [← map_inv, inBasis_val] at this

theorem KO_of_St {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x : GL (Fin n) (Lev.EAf D)}
    (hx : x ∈ St β) : inBasis h β w x ∈ KO (Kw w) (Fin n') := by
  subst h
  obtain ⟨z, rfl⟩ := hx
  have e1 : β⁻¹ * frGL β z * β = intGL D.host.F D.host.E _ z := by
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z * β⁻¹) * β = _
    group
  have e2 : β⁻¹ * (frGL β z)⁻¹ * β = intGL D.host.F D.host.E _ z⁻¹ := by
    rw [← map_inv]
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z⁻¹ * β⁻¹) * β = _
    group
  refine (mem_KO_iff _).2 ⟨fun i j => (mem_O_iff _).2 ?_, fun i j => (mem_O_iff _).2 ?_⟩
  · rw [inBasis_val, e1]
    exact (mem_OA _).1 (z.val _ _).2 w
  · rw [← map_inv, inBasis_val, e2]
    exact (mem_OA _).1 ((z⁻¹).val _ _).2 w

theorem idem_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (Lev.EAf D)}
    (hβ : IsFrame β Λ) {w : Pl D.host.E} {x : GL (Fin n) (Lev.EAf D)}
    (hx : ∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) {y : Fin n → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem w • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat, hβ] at hy ⊢
  intro i
  have e : (β⁻¹).val *ᵥ (idem w • (x.val *ᵥ y)) = idem w • ((β⁻¹ * x * β).val *ᵥ ((β⁻¹).val *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem ((idem_mul_mem_iff w _).2 (hx i j)) (hy j)

theorem hA_unitary {V : HSp D} {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ UA D.sp.cm V.gram)
    (a b : Fin V.rank → Lev.EAf D) : hA V (x.val *ᵥ a) (x.val *ᵥ b) = hA V a b := by
  have hx' : Formalism.UG.cT (cjA D) x.val * V.gram.map (inc D) * x.val = V.gram.map (inc D) := hx
  have e2 : ∀ u v : Fin V.rank → Lev.EAf D,
      Formalism.UG.hform (cjA D) (V.gram.map (inc D)) u v = (cjA D ∘ u) ⬝ᵥ (V.gram.map (inc D) *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : cjA D ∘ (x.val *ᵥ b) = (cjA D ∘ b) ᵥ* Formalism.UG.cT (cjA D) x.val := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [hA_eq, hA_eq, e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hx']

theorem transfer {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hsd : IsSelfDualC V Λ)
    {x : GL (Fin V.rank) (Lev.EAf D)} (hU : x ∈ UA D.sp.cm V.gram) {w : Pl D.host.E}
    (h : ∀ y ∈ hat Λ, idem w • ((x⁻¹).val *ᵥ y) ∈ hat Λ) {y : Fin V.rank → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem (GlobalTheory.IdemSupport.cP w) • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat_iff_of_selfDual hsd]
  intro z hz
  have e : z = x.val *ᵥ ((x⁻¹).val *ᵥ z) := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  rw [hA_smul_right, cjA_idem, GlobalTheory.StdFrames.cP_cP, e, hA_unitary hU, ← hA_smul_left]
  exact (mem_hat_iff_of_selfDual hsd y).1 hy _ (h z hz)

theorem givenLevel_succ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (a : ℕ) :
    ∀ b, b ≠ 0 → givenLevel G t w (a + 1, b) = KO (Kw w) (Fin ((locGrid G t w).rank (a + 1, b)))
  | 0, h => absurd rfl h
  | _ + 1, _ => rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem prodLev_inf_UA {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hβ : IsFrame β Λ) (hsd : IsSelfDualC V Λ) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, K w = KO (Kw w.1) (Fin (n' w))) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = congLev D.sp.cm V.gram Λ ⊤ := by
  rw [congLev_top]
  have key : ∀ g ∈ prodLev β P hn K ⊓ UA D.sp.cm V.gram, ∀ (Q : Pl D.host.E), ∀ y ∈ hat Λ,
      idem Q • (g.val *ᵥ y) ∈ hat Λ := by
    rintro g hg Q y hy
    obtain ⟨hg, hU⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hA', hB'⟩ := Subgroup.mem_inf.1 hg
    have hA : ∀ w : P, (∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g * β).val i j)) ≤ 1) ∧
        ∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g⁻¹ * β).val i j)) ≤ 1 := fun w => by
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hA' w)
      rw [hK] at this
      exact ent_of_KO _ β g w.1 this
    by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
    · obtain ⟨w, hw, hQw⟩ := hQ
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hQw with rfl | rfl
      · exact idem_smul_mem hβ (hA ⟨Q, hw⟩).1 hy
      · exact transfer hsd hU (fun y hy => idem_smul_mem hβ (hA ⟨w, hw⟩).2 hy) hy
    · push_neg at hQ
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hB' Q) hQ)
      exact idem_smul_mem hβ (ent_of_KO _ β g Q this).1 hy
  ext x
  constructor
  · intro hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x hx Q y hy,
        fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x⁻¹ (inv_mem hx) Q y hy⟩
    obtain ⟨h1, h2⟩ := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).1 hS
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, ?_⟩
    intro y
    refine ⟨fun hy => h1 y hy, fun hy => ?_⟩
    have := h2 _ hy
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
    exact this
  · intro hx
    obtain ⟨hU, hst⟩ := Subgroup.mem_inf.1 hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => (hst y).1 hy, fun y hy => (hst _).2 (by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]; exact hy)⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => ?_⟩, hU⟩
    · rw [Subgroup.mem_comap, hK]
      exact KO_of_St _ β w.1 hS
    · rw [Subgroup.mem_comap]
      exact KO_of_St _ β w' hS

end GlobalTheory.FunObj.LevRowSucc

namespace GlobalTheory.FunObj.GridChoice

open GlobalTheory.FunObj.LevRowSucc

theorem levRow_succ_inf_UA {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (i : ℕ) (h : i + 1 ≤ D.R.m) :
    S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram = G.levMax (.grid (i + 1) D.R.m) := by
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  rw [GridData.levMax]
  exact prodLev_inf_UA (S.B.isFrame (i + 1) D.R.m (by omega) h le_rfl)
    (G.isV (X := .grid (i + 1) D.R.m) ⟨h, le_rfl⟩ fun j e => by cases e).sd (locPl G t) _ _
    fun w => givenLevel_succ G t w.1 i D.R.m hm

end GlobalTheory.FunObj.GridChoice
