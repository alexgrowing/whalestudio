import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset

noncomputable section

namespace GlobalTheory.HfCharProof

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem act_chiRat (c : ℕ) (g : Br.G D.nbr i w hw) (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x =
      (D.nbr i w hw).toLL (((chiU D.nd i c * (chiU D.nd i 1)⁻¹)
        (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) • x := by
  funext b
  rw [Subsingleton.elim b 0]
  change (Br.loc D.nbr i w hw (chiRatO D.nd i c) g).mulVec x 0 = _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
  congr 1
  change (D.nbr i w hw).toLL (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0) = _
  congr 1
  simp [chiRatO, twistM]

theorem cont_chiRat (c : ℕ) (x : Fin 1 → Br.LL D.nbr i w hw) :
    Continuous fun g => matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x := by
  simp only [act_chiRat]
  have hs : Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  have hL : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => (D.nbr i w hw).toLL
      ((D.nd.chi i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      (D.nbr i w hw).toLL
      ((D.nd.chi i 1 (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) : (D.nd.O i)ˣ) : D.nd.O i) :=
    (hL.comp ((D.nd.chi_cont i c).comp hs)).mul
      (hL.comp ((D.nd.chi_cont i 1).comp (hs.comp continuous_inv)))
  refine Continuous.smul (h1.congr fun g => ?_) continuous_const
  rw [← map_mul, ← Units.val_mul, map_inv, map_inv, map_inv]
  rfl

theorem chiRat_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Formalism.MainNotions.N.GE D.nd) :
    (chiU D.nd i (n + 1) * (chiU D.nd i 1)⁻¹) g = (epsU D.nd i g)⁻¹ ^ n := by
  rcases hn with rfl | hc
  · simp
  · have h := D.nd.chi_def i (n + 1) (by omega) hc
    change D.nd.chi i (n + 1) g * (D.nd.chi i 1)⁻¹ g = _
    rw [mul_comm, h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl

theorem eps_eq (g : Br.G D.nbr i w hw) :
    (D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  rw [Br.PD, (D.loc _).PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
  exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)

theorem act_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Br.G D.nbr i w hw)
    (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i (n + 1))) g x =
      ((algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹) ^ n • x := by
  rw [act_chiRat, chiRat_eq D i n hn, Units.val_pow_eq_pow_val, map_pow, map_units_inv, eps_eq]

def chiLat (c : ℕ) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) where
  V := Fin 1 → Br.LL D.nbr i w hw
  ρ := matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c))
  cont := cont_chiRat D i w hw c
  L := Br.locLat D.nbr i w hw (chiRatO D.nd i c)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem hfChar : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LocalSituation.Conclusion4 D HW F → InertEq D →
    ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      D.nd.l i ≠ 2 → (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 → HfChar i w hw := by
  intro D HW F h4 hI i w hw h2 hK
  have hs := (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 hK
  have hT := (h4 (D.nd.l i) _ 1 _ hs).2
  have hr : ∀ c, finrank (Br.LL D.nbr i w hw) (chiLat D i w hw c).V = 1 := fun c =>
    Module.finrank_fin_fun _
  refine ⟨fun c hc => ?_, fun f hf => ?_⟩
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    exact ((hT n (chiLat D i w hw (n + 1)) (hr _) (act_eq D i w hw n (Or.inr hc2))).2.1 (by omega)).le
  · obtain ⟨-, x, hx⟩ :=
      ((hT 0 (chiLat D i w hw 1) (hr _) (act_eq D i w hw 0 (Or.inl rfl))).2.2 rfl f).1 hf
    refine ⟨x, fun g hg => hx g ?_⟩
    rw [hI i w hw] at hg
    exact hg

end GlobalTheory.HfCharProof

end
