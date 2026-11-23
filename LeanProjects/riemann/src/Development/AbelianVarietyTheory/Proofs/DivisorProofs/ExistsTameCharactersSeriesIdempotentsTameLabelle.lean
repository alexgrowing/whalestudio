import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSumOfNoConj
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TameTieOfGood

variable {D : D7}

theorem exists_div (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) : ∃ w, P.Div k w := by
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) (P.pb k).asIdeal (by
    have : RingHom.ker (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective _ _)
    rw [this]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, ?_⟩
  · rintro rfl
    apply (P.pb k).ne_bot
    rw [← hQ']
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  · exact HeightOneSpectrum.ext hQ'

theorem tameTie_of_given {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hG : Given R F) : GlobalTheory.DimPartsCompare.TameTie D R.C.W.om := by
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hL := hG.core.lev
  obtain ⟨L, h1, h2, h3⟩ := hG.types k
  refine ⟨L, h1, h2, fun v j => ?_⟩
  obtain ⟨PP, hPP⟩ := exists_div R.C.P k
  obtain ⟨u0, hu0, -⟩ := GlobalTheory.GLp.Model.exists_gen L
  have hp := D.host.g_prime k
  set a : ℕ := (u0 : ZMod (D.host.g k)).val with ha_def
  have haz : ((a : ℕ) : ZMod (D.host.g k)) = u0 := ZMod.natCast_zmod_val _
  have ha : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = L.gen 1 := by
    rw [← hu0, ← haz, map_natCast]
  have ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0 := by
    rw [ha, ← hu0]; simp
  have hcop : a.Coprime (D.host.g k) := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)
  have han : a ≠ 0 := by rintro h; rw [h] at ha0; exact ha0 (by simp)
  have hE : (a : D.host.E) ≠ 0 := by exact_mod_cast han
  have hgPP := Formalism.IndefR.Fin.g_mem_of_div R.C hPP
  have hk0 : IsUnit ((a : ℕ) : kP PP) := by
    have hc : IsCoprime ((a : ℕ) : kP PP) ((D.host.g k : ℕ) : kP PP) := by
      have := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (kP PP))
      simpa using this
    have hg0 : ((D.host.g k : ℕ) : kP PP) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hgPP
    rw [hg0] at hc
    exact isCoprime_zero_right.1 hc
  set u : (kP PP)ˣ := hk0.unit with hu_def
  have key := h3 v j PP hPP a u ha hk0.unit_spec
  have h2' := (R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl
  have h3' := hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu_def, hk0.unit_spec, map_natCast])
  rw [h2', MonoidHom.inv_apply, _root_.inv_inj] at h3'
  have hw : ZMod.unitOfCoprime a hcop = u0 := Units.ext (by rw [ZMod.coe_unitOfCoprime, haz])
  have hχ : (R.chi ((j : ℕ) + 1) PP u : ℂˣ) = GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.chiTame R.C.W.om k j u0 := by
    rw [h3', ← hw]; rfl
  have hgen : ∀ w : (ZMod (D.host.g k))ˣ, algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) w = L.gen 1 → w = u0 :=
    fun w hw' => Units.ext ((algebraMap _ _).injective (hw'.trans hu0.symm))
  rcases key with e | e
  · refine ⟨_, Or.inl rfl, fun b => GlobalTheory.Mem.TypePl.thetaOf_of_isCharLab L ⟨(D.nd.chiT k v j).ne_zero, fun w hw' => ?_⟩ b⟩
    rw [hgen w hw', e, hχ]
  · refine ⟨_, Or.inr rfl, fun b => GlobalTheory.Mem.TypePl.thetaOf_of_isCharLab L ⟨(D.nd.chiT k v j).ne_zero, fun w hw' => ?_⟩ b⟩
    rw [hgen w hw', e, hχ, MonoidHom.inv_apply]

theorem exists_tameTie_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∃ om, GlobalTheory.DimPartsCompare.TameTie D om :=
  fun R F hG => ⟨_, tameTie_of_given R F hG⟩

end GlobalTheory.TameTieOfGood

end
