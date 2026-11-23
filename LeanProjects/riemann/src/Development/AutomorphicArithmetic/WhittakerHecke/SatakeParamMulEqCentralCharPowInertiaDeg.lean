import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

private theorem sc_comm {R : Type} [CommRing R] (y : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) y * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) y :=
  Units.ext (Matrix.scalar_commute (y : R) (fun _ => Commute.all _ _) g.val).eq

private theorem val_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← _root_.zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [h2, toAdd_pow, nsmul_eq_mul]

private theorem norm_loc {E : Type} [Field E] [NumberField E] (w : H.P E) (x : (H.Kv w)ˣ) (f : ℕ)
    (hf : normV w = normV (w.under (𝓞 ℚ)) ^ f) :
    ∃ y : (H.Kv (w.under (𝓞 ℚ)))ˣ, ideleNorm ℚ E (localIdele E w x) = localIdele ℚ (w.under (𝓞 ℚ)) y ∧
      Valued.v (y : H.Kv (w.under (𝓞 ℚ))) = Valued.v (x : H.Kv w) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := ℚ) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, h, val_of_norm _ w _ x hm' _ hf⟩

private theorem val_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) (hb : ((n : 𝓞 K)) ∉ v.asIdeal) :
    Valued.v ((n : ℕ) : H.Kv v) = 1 := by
  have h1 : v.valuation K (((n : 𝓞 K)) : K) = 1 := by
    refine le_antisymm (v.valuation_le_one _) (not_lt.1 fun h => hb ?_)
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) v _).1 h
  have h2 : Valued.v (algebraMap K (H.Kv v) (((n : 𝓞 K)) : K)) = v.valuation K (((n : 𝓞 K)) : K) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h1] at h2
  rw [← h2]
  simp

private theorem unr_of_ok {ω : HChar ℚ} {L : ℕ} (hc : ChOk ω⁻¹ L) {v : H.P ℚ} (hb : ¬ Bad L v) : ω.UnrAt v := by
  intro x hx
  have hL : Valued.v ((L : ℕ) : H.Kv v) = 1 := val_nat v L hb
  have hs : ∀ w : H.P ℚ, w ≠ v → (localIdele ℚ v x).val.2 w = 1 := fun w h => Pi.mulSingle_eq_of_ne h _
  have he : (localIdele ℚ v x).val.2 v = x := Pi.mulSingle_eq_same v _
  have hU : (localIdele ℚ v x : (A ℚ)ˣ) ∈ UU := by
    refine ⟨rfl, fun w => ?_⟩
    by_cases h : w = v
    · subst h
      exact (congrArg Valued.v he).trans hx
    · exact (congrArg Valued.v (hs w h)).trans (map_one _)
  have hD : ∀ w, Dv L w (((localIdele ℚ v x : (A ℚ)ˣ) : A ℚ) - 1) := fun w => by
    unfold Dv
    by_cases h : w = v
    · subst h
      have e : H.cp w (((localIdele ℚ w x : (A ℚ)ˣ) : A ℚ) - 1) = (x : H.Kv w) - 1 := by
        rw [map_sub, map_one]
        exact congrArg (· - 1) he
      rw [e, hL]
      have h1 := Valuation.map_sub (Valued.v (R := H.Kv w)) (x : H.Kv w) 1
      have hx' : Valued.v (x : H.Kv w) = 1 := hx
      rwa [hx', map_one, max_self] at h1
    · have e : H.cp w (((localIdele ℚ v x : (A ℚ)ˣ) : A ℚ) - 1) = 0 := by
        rw [map_sub, map_one, sub_eq_zero]
        exact hs w h
      rw [e, map_zero]
      exact zero_le'
  have h : (ω.1 (localIdele ℚ v x))⁻¹ = 1 := hc _ hU hD
  exact inv_eq_one.1 h

theorem UpperTheory.satake_param_mul_eq_central_char_pow_inertiaDeg :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ) (L : ℕ), CenN P ω → ChOk ω⁻¹ L →
        ∀ (w : H.P E) (α β : ℂˣ) (f : ℕ), ¬ Bad L (w.under (𝓞 ℚ)) → normV w = normV (w.under (𝓞 ℚ)) ^ f →
          (CG.mk P).HasSat w {α, β} → α * β = ω.val (w.under (𝓞 ℚ)) ^ f := by
  intro E _ _ _ P ω L hC hO w α β f hb hf hS
  have hU := unr_of_ok hO hb
  obtain ⟨p, hp⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  have hϖ : H.IsU (Units.mk0 p hp0) := hp
  have hB := (CG.hasSat_mk P w _).1 hS
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  obtain ⟨g, hg⟩ : ∃ g, x.1.1 g ≠ 0 := by
    by_contra! hn
    exact hx.1 (Subtype.ext (Subtype.ext (funext hn)))
  have hfix : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w 2, x.1.1 (g * finGL E 2 (locGL E 2 w k)) = x.1.1 g := fun g k hk =>
    congrFun (congrArg (fun y : P.V => y.1.1) (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)) g
  have hEig : UpperTheory.V.Af.Smo.EigAt w {α, β} x.1.1 := UpperTheory.V.Af.StrongMultiplicityOne.eigOfSat E 2 P w _ hB x.1 x.2 hfix
  obtain ⟨R, -, -, hR⟩ := H.heckeExpl E w _ hϖ
  have hc := (hR α β _ (hEig g) 1).2
  have hc' : x.1.1 (g * Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl w (Units.mk0 p hp0))) = (α : ℂ) * β * x.1.1 g := by
    simp only [one_mul, map_one, mul_one] at hc
    rw [← (H.lcLaws E w).2.2.2.2.1]
    exact hc
  have h2 := hC x.1 x.2 (H.idl w (Units.mk0 p hp0)) g
  rw [sc_comm, hc'] at h2
  have h3 := mul_right_cancel₀ hg h2
  obtain ⟨y, hy, hv⟩ := norm_loc w (Units.mk0 p hp0) f hf
  have hu : IsUnitAt (w.under (𝓞 ℚ)) (y * (atFin (w.under (𝓞 ℚ)) (unif (w.under (𝓞 ℚ))) ^ f)⁻¹) := by
    have hun := unif_spec (w.under (𝓞 ℚ))
    have hp' : Valued.v ((Units.mk0 p hp0 : (H.Kv w)ˣ) : H.Kv w) = WithZero.exp (-1 : ℤ) := hp
    unfold IsUnitAt
    unfold IsUnifAt at hun
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, hp', hun]
    exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
  have h4 := hU _ hu
  rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h4
  have h5 : ω.1 (ideleNorm ℚ E (H.idl w (Units.mk0 p hp0))) = ω.val (w.under (𝓞 ℚ)) ^ f :=
    (congrArg ω.1 hy).trans h4
  rw [h5] at h3
  exact Units.ext (by simpa using h3)
