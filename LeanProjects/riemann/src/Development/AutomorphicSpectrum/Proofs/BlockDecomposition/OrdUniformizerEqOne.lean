import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

open Ad3 Ad3.S
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)
open GroundTheory.Global.RationalSymbol (prime)

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegral

theorem pOf_eq_prime (v : Pl) : pOf v = prime v := by
  show Ideal.absNorm v.asIdeal = prime v
  rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
  have h : ((prime v : ℕ) : NumberField.RingOfIntegers ℚ) =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) ((prime v : ℕ) : ℤ) := by
    simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
  simp

theorem ord_uniformizer_eq_one (v : Pl) :
    ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = 1 := by
  have h1 : Valued.v ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) = WithZero.exp (-1) :=
    DirichletHecke.valued_uniformizer v
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord (K := ℚ) (v := v)
    (x := ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (Units.ne_zero _)
  have h3 : WithZero.exp (-ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v)) = WithZero.exp (-1) :=
    h2.symm.trans h1
  have h4 := WithZero.exp_injective h3
  omega

theorem coe_localChar_unifUnit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (v : Pl)
    (hv : ¬ prime v ∣ N) :
    χ (prime v : ZMod N) = (localChar (DirichletHecke.heckeCharacter χ) v (unifUnit (Qv v)) : ℂ) := by
  obtain ⟨a, ha⟩ : ∃ a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ,
      a = unifUnit (Qv v) * (DirichletHecke.uniformizer v)⁻¹ := ⟨_, rfl⟩
  have h1 := ord_units_mul (K := Qv v) (unifUnit (Qv v)) (DirichletHecke.uniformizer v)⁻¹
  have h2 := ord_units_inv (K := Qv v) (DirichletHecke.uniformizer v)
  have h3 := ord_unifUnit (K := Qv v)
  have h4 := ord_uniformizer_eq_one v
  have hord : ord ((unifUnit (Qv v) * (DirichletHecke.uniformizer v)⁻¹ : (Qv v)ˣ) : Qv v) = 0 := by
    rw [h1, h2, h3, h4]; norm_num
  have hval : Valued.v ((a : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) = 1 := by
    rw [ha]
    exact (GroundTheory.Global.valued_eq_one_iff_ord (Units.ne_zero _)).2 hord
  have hmem : a ∈ (Submonoid.ofClass
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)).units := by
    simp only [Submonoid.mem_units_iff, Units.val_inv_eq_inv_val]
    constructor
    · change ((a : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hval.le
    · change ((a : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))⁻¹ ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hnorm := DirichletHecke.norm_padicRingEquiv_eq_one hmem
  have htriv := DirichletHecke.heckeCharacter_finiteEmbedding_of_not_dvd χ hv hnorm
  have hunif := DirichletHecke.coe_heckeCharacter_uniformizer χ hv
  have hπ : (unifUnit (Qv v) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) =
      a * DirichletHecke.uniformizer v := by
    rw [ha]; simp
  have key : ((localChar (DirichletHecke.heckeCharacter χ) v (unifUnit (Qv v)) : ℂˣ) : ℂ) =
      ((DirichletHecke.heckeCharacter χ (IdeleClassGroup.mk ℚ
        (IdeleGroup.finiteEmbedding v (a * DirichletHecke.uniformizer v))) : Circle) : ℂ) := by
    rw [← hπ]; rfl
  rw [key, map_mul, map_mul, map_mul, Circle.coe_mul, htriv, hunif]
  simp

theorem e1 : E1 := by
  unfold E1
  intro c hc M₀ hM₀
  obtain ⟨N, hN, χ, -, hχ⟩ := DirichletHecke.exists_heckeCharacter_eq hc
  haveI : NeZero (N * M₀) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Nat.pos_iff_ne_zero.mp hM₀)⟩
  refine ⟨N * M₀, inferInstance, DirichletCharacter.changeLevel (dvd_mul_right N M₀) χ,
    dvd_mul_left M₀ N, ?_⟩
  intro v hv
  rw [pOf_eq_prime] at hv ⊢
  rw [coe_localChar_unifUnit _ v hv, DirichletHecke.heckeCharacter_changeLevel, hχ]

end GlobalTheory.CompanionTheory.HalfIntegral
