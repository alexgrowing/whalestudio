import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.GenSectT

noncomputable section

namespace GlobalTheory.CurveRecord

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

theorem finite_reduced_of_eq {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
    [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K'] [CharZero K] {Dd m : ℕ}
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = Dd)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = Dd)
    (t : Fin (Dd + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    FiniteDimensional K' (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) ∧
      IsReduced (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) := by
  have e : a = GenSect.tsec K Kl t v := funext fun i => ha i
  subst e
  have := GenSect.s1T (Kl := Kl) hfg htr v k₀ hv₀ hbig t ht
  unfold GenSect.tJ at this
  exact this

set_option maxHeartbeats 1000000 in

theorem tv_indep {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) [Algebra B.KO (Kp X la N)]
    [IsScalarTower B.KO (X.Kl la) (Kp X la N)] :
    AlgebraicIndependent B.KO (fun p : Idx D j N => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have h0 := (MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)).map' hinj
  have h1 := h0.map' (f := IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N))
    (IsFractionRing.injective (Op X la N) (Kp X la N))
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic _ (nonZeroDivisors (X.Ol la))
  have h2 := (Algebra.IsAlgebraic.algebraicIndependent_iff (X.Ol la) (X.Kl la)).mp h1
  have h3 := h2.restrictScalars (R := B.KO) (algebraMap B.KO (X.Kl la)).injective
  have hfun : (fun p : Idx D j N => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) =
      ⇑(IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)) ∘
        (⇑(IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) ∘ MvPolynomial.X) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, Tv]
  rw [hfun]
  exact h3

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem rzMap_sec_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem map_Jid_eq : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

theorem finite_reduced_record
    (hfg : (⊤ : IntermediateField B.KO Ω).FG) (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j)
    (v : Fin N → Ω) (hv : ∀ k, gF (X.inc wL (w k)) = v k) (k₀ : Fin N) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun k => v k / v k₀)) =
      WeightFamilies.dimY D j) :
    FiniteDimensional (Kp X la N) (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) ∧
      IsReduced (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) := by
  let iK : Algebra B.KO (Kp X la N) :=
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la N) := IsScalarTower.of_algebraMap_eq' rfl
  rw [map_Jid_eq]
  exact finite_reduced_of_eq hfg htr v k₀ hv₀ hbig _ (tv_indep X la N)
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i)) (fun i => by rw [rzMap_sec_eq]; simp only [hv])

end Rec

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 1000000 in

theorem finite_reduced_section (hfg : FnFG (T.Q.Xo j) T.Q.c) (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨-, ⟨-, hB2⟩, -, -⟩ := hH
  obtain ⟨k₀, hk₀, htrZ⟩ := hB2 Z
  exact finite_reduced_record (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w (hfg Z) (htr Z)
    (fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun k => formsEvR_single j hG hT Z _ _) k₀ hk₀ htrZ

end GlobalTheory.CurveRecord
