import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SuppIntCong

set_option maxHeartbeats 2000000 in

theorem cong_one_of_suppAt : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (hQ : GA D V) (a : ℕ), 0 < a → SplitSet Q → SuppAt (idem Q) V hQ → ∃ c : ℕ, ∀ i j, (∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * ((finHom V hQ).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w) ∧ (∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * ((finHom V hQ)⁻¹.val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w) := by
  intro D V Q hQ a ha hQs hs
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.ConjVal.components_and_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ P : HeightOneSpectrum (𝓞 D.host.E), AE D →+* P.adicCompletion D.host.E,
      ∀ P z, ev P z = ι (finPart D z) P :=
    ⟨fun P => ((GlobalTheory.CharLocProd.evalAt P).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  obtain ⟨evf, hevf⟩ : ∃ evf : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (Af D.host.F ⊗[D.host.F] D.host.E) →+* P.adicCompletion D.host.E, ∀ P y, evf P y = ι y P :=
    ⟨fun P => (GlobalTheory.CharLocProd.evalAt P).comp ι.toRingHom, fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hQs.isIdemSum
  have e2 : ∀ P, P ∉ Q → ev P (idem Q) = 0 := fun P hP => by
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 P fun hh => hP (hh ▸ h')
  have hA1 : ∀ P, P ∉ Q → GlobalTheory.IdemSupport.cP P ∉ Q → (ev P).mapMatrix (mt V hQ) = 1 := fun P hP hP' => by
    have hc := hcj (idem Q) (GlobalTheory.IdemSupport.cP P)
    rw [e2 _ hP', map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at hc
    have hu : ev P (idem Q + cA D (idem Q)) = 0 := by rw [map_add, e2 P hP, hc, add_zero]
    have : (ev P).mapMatrix (mt V hQ - 1) = 0 := by
      refine Matrix.ext fun i j => ?_
      change ev P ((mt V hQ - 1) i j) = 0
      rw [← hs i j, map_mul, hu, zero_mul]
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  have hinv : ∀ P, (ev P).mapMatrix (mt V hQ) * (ev P).mapMatrix (mt V hQ⁻¹) = 1 := fun P => by
    rw [← map_mul, show mt V hQ * mt V hQ⁻¹ = 1 by unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.mul_inv _, map_one]
  have hB1 : ∀ P, P ∉ Q → GlobalTheory.IdemSupport.cP P ∉ Q → (ev P).mapMatrix (mt V hQ⁻¹) = 1 := fun P hP hP' => by
    have := hinv P
    rwa [hA1 P hP hP', one_mul] at this
  set S := Q ∪ Q.image GlobalTheory.IdemSupport.cP with hS
  have hout : ∀ P, P ∉ S → P ∉ Q ∧ GlobalTheory.IdemSupport.cP P ∉ Q := fun P hP =>
    ⟨fun h' => hP (Finset.mem_union_left _ h'), fun h' => hP (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨_, h', GlobalTheory.ClassScalarValue.cP_cP P⟩))⟩

  have hN : ∀ P ∈ S, ((normProd Q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have key : ∀ P' ∈ Q, ((normProd Q : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal := fun P' hP' => by
      show ((∏ v ∈ Q, Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 D.host.E) => Ideal.absNorm v.asIdeal) hP'
      rw [hr, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    intro P hP
    rcases Finset.mem_union.1 hP with h | h
    · exact key P h
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact key P' hP'
  have hvN : ∀ P ∈ S, ∀ c : ℕ, Valued.v (evf P ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E)) ≤
      WithZero.exp (-(c : ℤ)) := by
    intro P hP c
    have he : evf P ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) = algebraMap D.host.E (P.adicCompletion D.host.E)
        (algebraMap (𝓞 D.host.E) D.host.E (((normProd Q : ℕ) : 𝓞 D.host.E) ^ c)) := by
      simp only [map_natCast, map_pow, Nat.cast_pow]
    rw [he, GlobalTheory.CharLocProd.val_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (Ideal.pow_mem_pow (hN P hP) c)
  have hlog : ∀ x : WithZero (Multiplicative ℤ), ∃ n : ℕ, x ≤ WithZero.exp (n : ℤ) := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, hx ▸ zero_le'⟩
    · exact ⟨(WithZero.log x).toNat, by
        rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩
  choose fn hfn using hlog
  have ha0 : (a : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'

  have hgen : ∀ y : Af D.host.F ⊗[D.host.F] D.host.E, (∀ P, P ∉ S → evf P y = 0) → ∃ c0 : ℕ, ∀ c, c0 ≤ c →
      ∃ w ∈ intAE D, ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * y =
        ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    intro y hy
    set u : Af D.host.F ⊗[D.host.F] D.host.E :=
      Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E) ((a : D.host.E)⁻¹ ^ 2) with hu
    have hau : ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * u = 1 := by
      rw [hu, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E)),
        ← map_mul, Nat.cast_pow, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, map_one]
    let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => fn (Valued.v (evf P u)) + fn (Valued.v (evf P y))
    refine ⟨S.sup f, fun c hc => ⟨u * ((normProd Q ^ c : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * y, ?_, ?_⟩⟩
    · refine (h2 _).2 fun P => ?_
      rw [← hevf, map_mul, map_mul, map_mul, map_mul]
      by_cases hP : P ∈ S
      · have hle : f P ≤ c := (Finset.le_sup hP).trans hc
        calc _ ≤ WithZero.exp (fn (Valued.v (evf P u)) : ℤ) * WithZero.exp (-(c : ℤ)) *
              WithZero.exp (fn (Valued.v (evf P y)) : ℤ) :=
              mul_le_mul' (mul_le_mul' (hfn _) (hvN P hP c)) (hfn _)
          _ = WithZero.exp ((fn (Valued.v (evf P u)) : ℤ) + -(c : ℤ) + fn (Valued.v (evf P y))) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ 1 := by
              rw [← WithZero.exp_zero]
              exact WithZero.exp_le_exp.2 (by simp only [f] at hle; omega)
      · rw [hy P hP, map_zero, mul_zero]; exact zero_le'
    · rw [← mul_assoc, ← mul_assoc, hau, one_mul]
  have hone : ∀ P i j, evf P ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) i j := fun P i j => by
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have hy1 : ∀ i j P, P ∉ S → evf P ((finHom V hQ).val i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = 0 := by
    intro i j P hP
    obtain ⟨o1, o2⟩ := hout P hP
    have h' := congrFun (congrFun (hA1 P o1 o2) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    have hk : (finHom V hQ).val i j = finPart D (mt V hQ i j) := rfl
    rw [map_sub, hone, hk, hevf, ← hev, h', sub_self]
  have hy2 : ∀ i j P, P ∉ S → evf P ((finHom V hQ)⁻¹.val i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) = 0 := by
    intro i j P hP
    obtain ⟨o1, o2⟩ := hout P hP
    have h' := congrFun (congrFun (hB1 P o1 o2) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    have hk : (finHom V hQ)⁻¹.val i j = finPart D (mt V hQ⁻¹ i j) := by rw [← map_inv]; rfl
    rw [map_sub, hone, hk, hevf, ← hev, h', sub_self]
  choose c1 hc1 using fun i j => hgen _ (hy1 i j)
  choose c2 hc2 using fun i j => hgen _ (hy2 i j)
  let g : Fin V.rank × Fin V.rank → ℕ := fun p => c1 p.1 p.2 + c2 p.1 p.2
  refine ⟨Finset.univ.sup g, fun i j => ⟨hc1 i j _ ?_, hc2 i j _ ?_⟩⟩
  · exact le_trans (Nat.le_add_right _ _) (Finset.le_sup (f := g) (Finset.mem_univ (i, j)))
  · exact le_trans (Nat.le_add_left _ _) (Finset.le_sup (f := g) (Finset.mem_univ (i, j)))

end GlobalTheory.SuppIntCong
