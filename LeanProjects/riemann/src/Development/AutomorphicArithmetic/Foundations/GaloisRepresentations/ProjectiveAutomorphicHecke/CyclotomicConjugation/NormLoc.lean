import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal GroundTheory.Global.IdeleGroup

private theorem fN_sgl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : Plc L) (y : (w.adicCompletion L)ˣ) : ∃ n : ((below K w).adicCompletion K)ˣ,
      ((fN K L (sgl w y) : (Af K)ˣ) : Af K) = finiteAdeleSingle (below K w) (n : (below K w).adicCompletion K) ∧
      ∀ f : ℕ, Ideal.absNorm w.asIdeal = Ideal.absNorm (below K w).asIdeal ^ f →
        Valued.v (n : (below K w).adicCompletion K) = Valued.v (y : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w y
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  refine ⟨_, ?_, fun f hf => GlobalTheory.LiftPolar.val_of_norm _ w _ y hm' f hf⟩
  have h0 : Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (sgl w y) = finiteEmbedding w y := by
    apply Units.ext
    rfl
  show (Units.val (GroundTheory.Global.ideleNorm K L (Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (sgl w y)))).2 = _
  rw [h0, h]
  rfl

private theorem v_single {K : Type} [Field K] [NumberField K] {v p : Plc K} (h : p = v) (n : v.adicCompletion K) :
    Valued.v (finiteAdeleSingle v n p) = Valued.v n := by
  subst h
  rw [finiteAdeleSingle_apply_self]

private theorem v_nat {K : Type} [Field K] [NumberField K] {v p : Plc K} (h : p = v) (m : ℕ) :
    Valued.v ((m : ℕ) : p.adicCompletion K) = Valued.v ((m : ℕ) : v.adicCompletion K) := by
  subst h
  rfl

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.normLoc :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormLoc := by
  intro K L _ _ _ _ _ w y u
  obtain ⟨n, hn, hv⟩ := fN_sgl K L w y
  have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm (below K w).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K) :=
    GlobalTheory.LiftPolar.normV_under (K := K) w
  have hu' : ∀ h : below K u = below K w, Valued.v (finiteAdeleMap K L (finiteAdeleSingle (below K w) (n : (below K w).adicCompletion K)) u) =
      (Valued.v (y : w.adicCompletion L) ^ w.asIdeal.inertiaDeg (𝓞 K)) ^ u.asIdeal.ramificationIdx (𝓞 K) := fun h => by
    rw [finiteAdeleMap_apply, valued_completionMap, v_single h, hv _ hN]
  rw [hn]
  refine ⟨fun h => ?_, fun h => ?_, fun h hu hq => ?_⟩
  · rw [finiteAdeleMap_apply]
    rw [finiteAdeleSingle_apply_of_ne (show below K u ≠ below K w from h), map_one]
  · by_cases hu : below K u = below K w
    · rw [hu' hu, show Valued.v (y : w.adicCompletion L) = 1 from h, one_pow, one_pow]
    · rw [finiteAdeleMap_apply, finiteAdeleSingle_apply_of_ne hu, map_one, map_one]
  · have hb : below K u = below K w := hu
    have e : ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion L) =
        completionMap (below K u) u ((Ideal.absNorm w.asIdeal : ℕ) : (below K u).adicCompletion K) :=
      (map_natCast _ _).symm
    rw [hu' hb, e, valued_completionMap, v_nat hb, hN, Nat.cast_pow, map_pow,
      show Valued.v (y : w.adicCompletion L) = WithZero.exp (-1 : ℤ) from h]
    congr 2
    exact hq.symm
