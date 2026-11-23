import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtPLoc
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.W2.Seed

open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open GroundTheory.Global.SemiLocal (completionMap)

private theorem eq_zero_of_small {E : Type} [Field E] [NumberField E] {w : Plc E}
    (z : w.adicCompletion E) (h : ∀ n : ℕ, Valued.v z ≤ WithZero.exp (-(n : ℤ))) : z = 0 := by
  by_contra hz
  have h0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m :=
    ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
  have := h (1 - m).toNat
  rw [hm, WithZero.exp_le_exp] at this
  omega

private theorem valued_completionMap_le {E : Type} [Field E] [NumberField E] (P : Plc E)
    (t : (below ℚ P).adicCompletion ℚ) (n : ℕ) (ht : Valued.v t ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (completionMap (below ℚ P) P t) ≤ WithZero.exp (-(n : ℤ)) := by
  have he : P.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 0 := by
    intro h0
    have h := GroundTheory.Global.SemiLocal.valued_completionMap (below ℚ P) P
      (0 : (below ℚ P).adicCompletion ℚ)
    rw [map_zero, map_zero, map_zero, h0, pow_zero] at h
    exact zero_ne_one h
  rw [GroundTheory.Global.SemiLocal.valued_completionMap]
  refine le_trans ?_ ht
  refine pow_le_of_le_one zero_le' (ht.trans ?_) he
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private theorem ringHom_eq {E : Type} [Field E] [NumberField E] (P : Plc E) (v : Plc ℚ)
    (φ ψ : v.adicCompletion ℚ →+* P.adicCompletion E)
    (hφ : ∀ (n : ℕ) (a : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (φ a) ≤ WithZero.exp (-(n : ℤ)))
    (hψ : ∀ (n : ℕ) (a : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (ψ a) ≤ WithZero.exp (-(n : ℤ))) (x : v.adicCompletion ℚ) : φ x = ψ x := by
  have aux : ∀ q : ℚ →+* v.adicCompletion ℚ, DenseRange q → φ x = ψ x := by
    intro q hd
    rw [← sub_eq_zero]
    refine eq_zero_of_small _ fun n => ?_
    have hopen : IsOpen {y : v.adicCompletion ℚ | Valued.v (y - x) ≤ WithZero.exp (-(n : ℤ))} :=
      (GlobalTheory.Idele.isOpen_valued_le (K := ℚ) v (-(n : ℤ))).preimage
        (continuous_id.sub continuous_const)
    obtain ⟨k, hk⟩ := hd.exists_mem_open hopen ⟨x, by simp⟩
    have hk' : Valued.v (q k - x) ≤ WithZero.exp (-(n : ℤ)) := by
      simpa only [Set.mem_setOf_eq] using hk
    have h : φ (q k) = ψ (q k) := RingHom.congr_fun (Subsingleton.elim (φ.comp q) (ψ.comp q)) k
    have e : φ x - ψ x = ψ (q k - x) - φ (q k - x) := by
      rw [map_sub φ, map_sub ψ, h]
      abel
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le (hψ n _ hk') (hφ n _ hk'))
  exact aux _ (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) v)

private theorem locMap_eq {E : Type} [Field E] [NumberField E] (P : Plc E)
    (x : (below ℚ P).adicCompletion ℚ) :
    GlobalTheory.AdeleBaseChange.locMap ℚ P x = completionMap (below ℚ P) P x :=
  ringHom_eq P (below ℚ P) (GlobalTheory.AdeleBaseChange.locMap ℚ P) (completionMap (below ℚ P) P)
    (fun n a ha => GlobalTheory.AdeleBaseChange.locMap_valued P n a ha)
    (fun n a ha => valued_completionMap_le P a n ha) x

private theorem ringHom_eq_of_continuous {R : Type} [Ring R] [TopologicalSpace R] [T2Space R]
    (v : Plc ℚ) (φ ψ : v.adicCompletion ℚ →+* R) (hφ : Continuous φ) (hψ : Continuous ψ)
    (x : v.adicCompletion ℚ) : φ x = ψ x := by
  have aux : ∀ q : ℚ →+* v.adicCompletion ℚ, DenseRange q → φ x = ψ x := fun q hd =>
    congrFun (hd.equalizer hφ hψ (funext fun k =>
      RingHom.congr_fun (Subsingleton.elim (φ.comp q) (ψ.comp q)) k)) x
  exact aux _ (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) v)

private theorem adMap_eq {E : Type} [Field E] [NumberField E] (a : AfQ) :
    GlobalTheory.AdeleBaseChange.adMap ℚ E a = finiteAdeleMap ℚ E a :=
  FiniteAdeleRing.ext _ fun P => locMap_eq P _

private theorem below_conjSrc {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Plc E) :
    below ℚ (conjSrc (conjE E) w) = below ℚ w := by
  have h := conjPl_conjSrc (conjE E) w
  refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
  change algebraMap (𝓞 ℚ) (𝓞 E) y ∈ (conjSrc (conjE E) w).asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) y ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : conjE E ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) = ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) := by
    change conjE E (algebraMap ℚ E (y : ℚ)) = algebraMap ℚ E (y : ℚ)
    simp [eq_ratCast]
  rw [this]

private theorem conj_finiteAdeleMap {E : Type} [Field E] [NumberField E] [IsCMField E] (a : AfQ) :
    conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a := by
  refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
  rw [pLoc_conjFin]
  have hb := below_conjSrc w
  have key : ∀ (u : Plc E) (_ : below ℚ u = below ℚ w) (f : u.adicCompletion E →+* w.adicCompletion E),
      Continuous f → f (pLoc E u (finiteAdeleMap ℚ E a)) = pLoc E w (finiteAdeleMap ℚ E a) := by
    intro u hu f hf
    haveI : w.asIdeal.LiesOver (below ℚ u).asIdeal := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w _).1 hu.symm
    change f (completionMap (below ℚ u) u (a (below ℚ u))) = completionMap (below ℚ w) w (a (below ℚ w))
    rw [← GroundTheory.Global.AdeleBaseChange.completionMap_congr hu w a]
    exact ringHom_eq_of_continuous (below ℚ u) (f.comp (completionMap (below ℚ u) u)) (completionMap (below ℚ u) w)
      (hf.comp (GroundTheory.Global.SemiLocal.continuous_completionMap _ _))
      (GroundTheory.Global.SemiLocal.continuous_completionMap _ _) _
  exact key _ hb _ (conjLoc_spec (conjE E) w).1

end UpperTheory.Gal.W2.Seed

open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)

theorem UpperTheory.Gal.W2.Seed.pAdTensor :
    AdTensor := by
  intro E _ _ _
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd ℚ E
  let c : AfQ ⊗[ℚ] E ≃+* Formalism.L2.DIV.AfE ℚ E :=
    (Algebra.TensorProduct.comm ℚ AfQ E).toRingEquiv
  have hc : ∀ a x, c (a ⊗ₜ[ℚ] x) = x ⊗ₜ[ℚ] a := fun a x => rfl
  have hc' : ∀ a x, c.symm (x ⊗ₜ[ℚ] a) = a ⊗ₜ[ℚ] x := fun a x => rfl
  let j := c.trans (RingEquiv.ofBijective ι
    ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩)
  have hj : ∀ y, j y = ι (c y) := fun y => rfl
  refine ⟨j, fun a x => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, conj_finiteAdeleMap⟩
  · rw [hj, hc, hι, adMap_eq, mul_comm]
  · have : j y ∈ Formalism.UG.intAd E := by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, x, ha, rfl⟩ := hy
        rw [hj, hc]
        exact GlobalTheory.AdeleBaseChange.map_mem_int hι (Formalism.UG.P.levelaf_tmul_mem x ha)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    exact this
  · have h : c y ∈ Formalism.L2.DIV.RInt ℚ E := GlobalTheory.AdeleBaseChange.mem_int_of_map hι hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg h
    have e' : y = c.symm (c y) := (c.symm_apply_apply y).symm
    rw [e', e, map_sum]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, g i, hr i, ?_⟩
    rw [hc']
