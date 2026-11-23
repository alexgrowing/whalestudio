import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAdjoinOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralIndicatorEqLatticeCountStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIffGLintCosetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCompletionLatticeEqColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsMulLeftMatrixEqMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormIntegralIffLatticeUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceNormGramInverseEqMulMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableElementBasisIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEquivNormOneTorusNonsplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedConjDeltaOfUnitModNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIffMulNormInvAlgStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMulLeftGeneratorEqMapSymmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIntegralMatrixCharpolyRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfPreservesFullLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwistedOrbitalIntegralsEqFinsumParametrisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceGLConjMaxCompactIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfClassOfFixedUnitsEqStatement

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwOrbLevel

open GlobalTheory.TwLat

theorem twOrb_level_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K), Q.Monic → Q.natDegree = m → Q.Separable → IsCsr w Q → Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ → aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 → stTw m w Q (fun y : GLw m w => if y ∈ GlobalTheory.LFun.KGL w m ∧ nrmL m w y ∈ {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) = ((B.stSum : ℚ) : ℂ) := by
  intro E _ _ _ hE w hw K e hc hint hval hq k t ht htk m Q B hQm hQd hQs hQc hadj hQu hfin huσ
  set u : B.A := 1 + algebraMap K.O B.A t * B.g with hu_def
  obtain ⟨-, -, hθK, hnrm, -, -, -, -, -, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hE m w
  set cong : Set (GLw m w) := {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (g.val i j -
    (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} with hcong
  set f : GLw m w → ℂ := fun y => if y ∈ GlobalTheory.LFun.KGL w m ∧ nrmL m w y ∈ cong then 1 else 0 with hf
  set S : Set (GLw m w) := {y | (nrmL m w y).val.charpoly = Q} with hS
  show clSum (thL m w) (GlobalTheory.LFun.KGL w m) S (fun _ => 1) f = _
  have hfK : ∀ c ∈ GlobalTheory.LFun.KGL w m, ∀ y, f (c⁻¹ * y * thL m w c) = f y := by
    intro c hcK y
    have h1 : c⁻¹ * y * thL m w c ∈ GlobalTheory.LFun.KGL w m ↔ y ∈ GlobalTheory.LFun.KGL w m := by
      constructor
      · intro h
        have := mul_mem (mul_mem hcK h) (inv_mem (hθK c hcK))
        simpa [mul_assoc] using this
      · intro h
        exact mul_mem (mul_mem (inv_mem hcK) h) (hθK c hcK)
    have h2 : nrmL m w (c⁻¹ * y * thL m w c) ∈ cong ↔ nrmL m w y ∈ cong := by
      rw [hnrm]; exact GlobalTheory.T.principalCongruenceGL_conj_maxCompact_iff E w m k c _ hcK
    simp only [hf, h1, h2]
  have hf01 : ∀ y, f y = 0 ∨ f y = 1 := by
    intro y; simp only [hf]; split_ifs <;> simp
  have hSinv : ∀ y g, g⁻¹ * y * thL m w g ∈ S ↔ y ∈ S := by
    intro y g
    simp only [hS, Set.mem_setOf_eq, hnrm, Units.val_mul]
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hrstab : ∀ (δ x : GLw m w), (rStab fun k : GlobalTheory.LFun.KGL w m => f ((x * k)⁻¹ * δ * thL m w (x * k))).index ≠ 0 := by
    intro δ x
    have : rStab (fun k : GlobalTheory.LFun.KGL w m => f ((x * k)⁻¹ * δ * thL m w (x * k))) = ⊤ := by
      refine eq_top_iff.2 fun k' _ z => ?_
      have := hfK (k' : GLw m w) k'.2 ((x * ↑z)⁻¹ * δ * thL m w (x * ↑z))
      show f ((x * ↑(z * k'))⁻¹ * δ * thL m w (x * ↑(z * k'))) = f ((x * ↑z)⁻¹ * δ * thL m w (x * ↑z))
      rw [← this]
      congr 1
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [this, Subgroup.index_top]; exact one_ne_zero
  have htwinv : ∀ y g, twOrb (thL m w) (GlobalTheory.LFun.KGL w m) (g⁻¹ * y * thL m w g) f = twOrb (thL m w) (GlobalTheory.LFun.KGL w m) y f :=
    fun y g => GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g f (hrstab y)
  have hrank : Module.finrank K.E B.A = m := hfin.trans hQd
  let b : Module.Basis (Fin m) K.E B.A := Module.finBasisOfFinrankEq K.E B.A hrank
  have hgu : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ y ∈ L, u * y ∈ L := by
    intro L hg y hy
    rw [hu_def, add_mul, one_mul, mul_assoc]
    refine L.add_mem hy ?_
    rw [← Algebra.smul_def]
    exact L.smul_mem t (hg y hy)
  by_cases hui : IsIntegral K.O u
  · let Bu : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
    have hP : (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom :=
      GlobalTheory.T.charpoly_mulLeft_generator_eq_map_symm K B _ e u Q hQm hadj hQu hfin
    have hsep : (Q.map e.symm.toRingHom).Separable := hQs.map
    obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.UnitLemma.TwistUnit.twisted_unit_eq_unit K Bu huσ
      (by show (LinearMap.mulLeft K.E u).charpoly.Separable; rw [hP]; exact hsep) hui ((-1) ^ (m - 1))
      (neg_one_pow_eq_or B.A (m - 1))
    have hβ₀' : B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) := hβ₀
    have hgram : ∀ x : B.Aˣ, IsUnit (gram e b ((β₀ : B.A) * x)) := fun x =>
      GlobalTheory.T.separable_element_basis_integral E hE w hw K e hc hint hval B m b u _ hsep hQu hadj _ (β₀.isUnit.mul x.isUnit)
    have hσβ : ∀ x : B.Aˣ, B.σ (x : B.A) = x → B.σ ((β₀ : B.A) * x) = (β₀ * x) * ((-1) ^ (m - 1) * u) := by
      intro x hx
      rw [map_mul, hβ₀', hx]; ring
    have hN : ∀ x : B.Aˣ, B.σ (x : B.A) = x → (nrmL m w (dlt e b ((β₀ : B.A) * x))).val = mulMat e b u :=
      fun x hx => GlobalTheory.T.inertPlace_norm_gramInverse_eq_mulMatrix E hE w hw K e hc hint hval B m b u _ (hgram x) (hσβ x hx)
    have hcp : (mulMat e b u).charpoly = Q := by
      have h1 := Matrix.charpoly_map (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)) (e : K.E →+* w.adicCompletion E)
      have h2 : mulMat e b u = (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map (e : K.E →+* w.adicCompletion E) := rfl
      rw [h2, h1, LinearMap.charpoly_toMatrix, hP, Polynomial.map_map]
      ext n
      simp [Polynomial.coeff_map]
    obtain ⟨hΛK, hlat⟩ := GlobalTheory.T.latticeSpannedByGLColumns_eq_iff_GLint_coset E hE w hw K e hc hint hval B m b
    have hOrb : ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        twOrb (thL m w) (GlobalTheory.LFun.KGL w m) (dlt e b ((β₀ : B.A) * x)) f = ((B.N x : ℚ) : ℂ) := by
      intro x hx
      obtain ⟨φ, hφv, hφc⟩ := GlobalTheory.T.twistedCentralizer_equiv_normOneTorus_nonsplit E hE w hw K e hc hint hval B m b u _ (β₀.isUnit.mul x.isUnit)
        (hσβ x hx) hadj (hgram x)
      refine GlobalTheory.T.twistedOrbitalIntegral_indicator_eq_latticeCount K B x (GLw m w) (thL m w) (GlobalTheory.LFun.KGL w m) _ f φ (lat e b) hfK hf01 hφc hΛK ?_ ?_
        (fun L hL => GlobalTheory.T.exists_GL_completion_lattice_eq_columns E hE w hw K e hc hint hval B m b L hL.1)
      · intro t' q
        refine GlobalTheory.T.latticeSpannedByGLColumns_mulLeftMatrix_eq_mul E hE w hw K e hc hint hval B m b _ q _ ?_
        rw [Units.val_mul, hφv t']
      · intro q
        have hf1 : f (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q) = 1 ↔
            (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q ∈ GlobalTheory.LFun.KGL w m ∧
              nrmL m w (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q) ∈ cong) := by
          simp only [hf]; split_ifs with h <;> simp [h]
        rw [hf1, hnrm, GlobalTheory.T.twistedNorm_integral_iff_lattice_unimodular E hE w hw K e hc hint hval B m b _ (hgram x) q]
        have hlev : q⁻¹ * nrmL m w (dlt e b ((β₀ : B.A) * x)) * q ∈ cong ↔
            ∀ y ∈ lat e b q, B.g * y ∈ lat e b q :=
          GlobalTheory.T.principalCongruenceLevel_iff_lattice_stable E hE w hw K e hc hint hval B m b t k ht htk q _ (hN x hx)
        rw [hlev]
        have hXiff : (GlobalTheory.UnitLemma.IsLat K.O K.E (lat e b q) ∧ ∀ z, z ∈ lat e b q ↔
            ∀ y ∈ lat e b q, B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range) ↔ lat e b q ∈ Bu.X x := by
          rw [← hX x hx]; rfl
        constructor
        · rintro ⟨hL, hg, hsd⟩
          exact ⟨(hXiff.2 ⟨hL, hgu _ hg, hsd⟩).2, hg⟩
        · rintro ⟨hun, hg⟩
          obtain ⟨hL, -, hsd⟩ := hXiff.1 ⟨hlat q, hun⟩
          exact ⟨hL, hg, hsd⟩
    have hsum := GlobalTheory.T.sum_twistedOrbitalIntegrals_eq_finsum_parametrised (GLw m w) (thL m w) (GlobalTheory.LFun.KGL w m) S f B.Cl
      (fun c => dlt e b ((β₀ : B.A) * ((Quot.out c).1 : B.Aˣ))) (fun c => ((B.N c.rep : ℚ) : ℂ))
      (fun c => by show (nrmL m w _).val.charpoly = Q; rw [hN _ (Quot.out c).2]; exact hcp)
      (by
        intro y hy
        obtain ⟨x, hx, g, rfl⟩ := GlobalTheory.T.exists_twistedConj_delta_of_unit_mod_norms E hE w hw K e hc hint hval B m b u Q hQs hQu hadj β₀ hβ₀' hgram y hy
        let c : B.Cl := Quot.mk _ ⟨x, hx⟩
        obtain ⟨a, ha⟩ := GlobalTheory.T.exists_norm_of_classOfFixedUnits_eq K B ⟨x, hx⟩ (Quot.out c) (Quot.out_eq c).symm
        obtain ⟨g', hg'⟩ := (GlobalTheory.T.twistedConj_iff_mul_norm_invAlg E hE w hw K e hc hint hval B m b u hadj β₀ hβ₀' hgram x (Quot.out c).1 hx
          (Quot.out c).2).2 ⟨a, ha⟩
        refine ⟨c, g'⁻¹ * g, ?_⟩
        show _ = _ * dlt e b ((β₀ : B.A) * ((Quot.out c).1 : B.Aˣ)) * _
        rw [hg']
        simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left])
      (by
        intro c c' hcc
        obtain ⟨a, ha⟩ := (GlobalTheory.T.twistedConj_iff_mul_norm_invAlg E hE w hw K e hc hint hval B m b u hadj β₀ hβ₀' hgram (Quot.out c).1
          (Quot.out c').1 (Quot.out c).2 (Quot.out c').2).1 hcc
        rw [← Quot.out_eq c, ← Quot.out_eq c']
        exact Quot.sound ⟨a, ha⟩)
      hSinv htwinv (fun c => hOrb _ (Quot.out c).2)
    rw [hsum]
    show _ = ((∑ᶠ c : B.Cl, B.N c.rep : ℚ) : ℂ)
    by_cases hfs : (Function.support fun c : B.Cl => B.N c.rep).Finite
    · exact (map_finsum (Rat.castHom ℂ) hfs).symm
    · have hfs' : ¬ (Function.support fun c : B.Cl => ((B.N c.rep : ℚ) : ℂ)).Finite := by
        simpa [Function.support] using hfs
      rw [finsum_of_infinite_support hfs, finsum_of_infinite_support hfs']
      simp
  · have hX0 : ∀ x : B.A, B.X x = ∅ := by
      intro x
      ext L
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hL, hg, -⟩
      exact hui (GlobalTheory.T.isIntegral_of_preserves_fullLattice K B u L hL (hgu L hg))
    have hN0 : ∀ x : B.A, B.N x = 0 := by
      intro x
      unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
      haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) := by
        constructor
        intro o
        induction o using Quot.ind with
        | mk L =>
          have h := (hX0 x).subset L.2
          simp at h
      exact finsum_of_isEmpty _
    have hf0 : ∀ y ∈ S, ∀ q : GLw m w, f (q⁻¹ * y * thL m w q) = 0 := by
      intro y hy q
      simp only [hf]
      rw [if_neg]
      rintro ⟨-, hn, -⟩
      exact hui (GlobalTheory.T.isIntegral_of_integral_matrix_charpoly_root E hE w hw K e hc hint hval B m b u Q hQm hQu _ hn ((hSinv y q).2 hy))
    have hst : B.stSum = 0 := by
      unfold GlobalTheory.UnitLemma.InvAlg.stSum
      simp [hN0]
    rw [hst, Rat.cast_zero]
    unfold clSum
    refine (finsum_congr fun c => ?_).trans finsum_zero
    split_ifs with hc'
    · have h0 := hf0 _ hc'
      simp only [twOrb, avg, h0, finsum_zero, mul_zero]
    · rfl

end GlobalTheory.TwOrbLevel
