import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

noncomputable section

namespace GlobalTheory.CompanionTheory.DictLoc

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

def Cp (A : Type) : Type := A

section Model

theorem exists_model_field {K A : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [Field A] [Algebra K A] [FiniteDimensional K A] [TopologicalSpace A] [IsModuleTopology K A] :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (e : A ≃+* L),
      Continuous e ∧ Continuous e.symm ∧ ∀ (c : A ≃ₐ[K] A) (x : A), ‖e (c x)‖ = ‖e x‖ := by
  haveI : CompleteSpace K := inferInstance
  letI fL : Field (Cp A) := ‹Field A›
  letI aL : Algebra K (Cp A) := ‹Algebra K A›
  haveI : FiniteDimensional K (Cp A) := ‹FiniteDimensional K A›
  haveI : Algebra.IsAlgebraic K (Cp A) := Algebra.IsAlgebraic.of_finite K (Cp A)
  letI nL : NontriviallyNormedField (Cp A) := spectralNorm.nontriviallyNormedField K (Cp A)
  letI mL : NormedAlgebra K (Cp A) := spectralNorm.normedAlgebra K (Cp A)
  haveI uL : IsUltrametricDist (Cp A) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := Cp A))
  haveI pL : ProperSpace (Cp A) := FiniteDimensional.proper K (Cp A)
  haveI : IsModuleTopology K (Cp A) := isModuleTopologyOfFiniteDimensional
  haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  let f : A ≃ₗ[K] Cp A := LinearEquiv.refl K A
  refine ⟨Cp A, nL, uL, pL, RingEquiv.refl A, IsModuleTopology.continuous_of_linearMap f.toLinearMap,
    IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap, fun c x => ?_⟩
  exact (spectralNorm_eq_of_equiv (K := K) (L := Cp A) c x).symm

theorem isField_tensor_of_no_algHom {F K E : Type} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    (h2 : Module.finrank F E = 2) (hn : IsEmpty (E →ₐ[F] K)) : IsField (K ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hA : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, h2]
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[F] E)
  by_cases hb : m = ⊥
  · subst hb
    exact ((RingEquiv.quotientBot (K ⊗[F] E)).symm.toMulEquiv.isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient ⊥).1 hm))
  · exfalso
    letI := Ideal.Quotient.field m
    let φ : (K ⊗[F] E) →ₐ[K] (K ⊗[F] E) ⧸ m := Ideal.Quotient.mkₐ K m
    have hs : Function.Surjective φ := Ideal.Quotient.mkₐ_surjective K m
    have h3 := LinearMap.finrank_range_add_finrank_ker φ.toLinearMap
    rw [LinearMap.range_eq_top.2 hs, finrank_top, hA] at h3
    have hk : 0 < Module.finrank K (LinearMap.ker φ.toLinearMap) := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
      haveI : Nontrivial (LinearMap.ker φ.toLinearMap) :=
        ⟨⟨⟨x, (Ideal.Quotient.eq_zero_iff_mem.2 hx)⟩, 0, fun e => hx0 (congrArg Subtype.val e)⟩⟩
      exact Module.finrank_pos
    haveI : Module.Finite K ((K ⊗[F] E) ⧸ m) := Module.Finite.of_surjective φ.toLinearMap hs
    have hq : 0 < Module.finrank K ((K ⊗[F] E) ⧸ m) := Module.finrank_pos
    have h1 : Module.finrank K ((K ⊗[F] E) ⧸ m) = 1 := by omega
    have hbj : Function.Bijective (Algebra.ofId K ((K ⊗[F] E) ⧸ m)) :=
      ⟨(algebraMap K _).injective, fun y => by
        have : (⊥ : Subalgebra K ((K ⊗[F] E) ⧸ m)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
        have hy : y ∈ (⊥ : Subalgebra K ((K ⊗[F] E) ⧸ m)) := this ▸ Algebra.mem_top
        obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hy
        exact ⟨a, ha⟩⟩
    let ε : K ≃ₐ[K] (K ⊗[F] E) ⧸ m := AlgEquiv.ofBijective _ hbj
    exact hn.false (((ε.symm.toAlgHom.comp φ).restrictScalars F).comp Algebra.TensorProduct.includeRight)

end Model

section Main

theorem exists_model {K A : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [TopologicalSpace A] [IsModuleTopology K A] (hA : IsField A) :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (e : A ≃+* L),
      Continuous e ∧ Continuous e.symm ∧ ∀ (c : A ≃ₐ[K] A) (x : A), ‖e (c x)‖ = ‖e x‖ :=
  letI := hA.toField
  exists_model_field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

def sigEquiv (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) : (K ⊗[F] E) ≃ₐ[K] (K ⊗[F] E) :=
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) σ) (Algebra.TensorProduct.map (AlgHom.id K K) σ)
    (by ext x; simp [h]) (by ext x; simp [h])

theorem sigEquiv_apply (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) (y : K ⊗[F] E) :
    sigEquiv K h y = sigR K σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem sigR_sigR (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) (y : K ⊗[F] E) :
    sigR K σ (sigR K σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h x)

theorem properSpace_Fv (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (Fv F v) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.tjcosets_finite v

theorem charZero_Fv : CharZero (Fv F v) :=
  ((algebraMap F (Fv F v)).charZero_iff (algebraMap F (Fv F v)).injective).1 inferInstance

end Main

section Dict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

open Formalism.UG (bc UJ cT) in

theorem exists_equiv_UG {L : Type} [Field L] [TopologicalSpace L] (e : (Fv F v ⊗[F] E) ≃+* L) (he : Continuous e)
    (he' : Continuous e.symm) :
    Nonempty (GLoc σ J v ≃ₜ* CompanionTheory.Rg.Fl.UG (e.toRingHom.comp ((sigR (Fv F v) σ).comp e.symm.toRingHom))
      ((JR (Fv F v) J).map e)) := by
  set s : L →+* L := e.toRingHom.comp ((sigR (Fv F v) σ).comp e.symm.toRingHom) with hs
  have e1 : ∀ x : GL (Fin n) L, bc e.toRingHom (bc e.symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => e.apply_symm_apply _)
  have e2 : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), bc e.symm.toRingHom (bc e.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => e.symm_apply_apply _)
  have key : ∀ x : GL (Fin n) (Fv F v ⊗[F] E),
      (cT (sigR (Fv F v) σ) x.1 * JR (Fv F v) J * x.1).map e =
        (((bc e.toRingHom x).1.map s).transpose * (JR (Fv F v) J).map e * (bc e.toRingHom x).1) := fun x => by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    exact Matrix.ext fun i j => by simp [cT, hs, bc]
  have mem : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), x ∈ HR (Fv F v) σ J ↔
      bc e.toRingHom x ∈ CompanionTheory.Rg.Fl.UG s ((JR (Fv F v) J).map e) := fun x => by
    change cT (sigR (Fv F v) σ) x.1 * JR (Fv F v) J * x.1 = JR (Fv F v) J ↔
      ((bc e.toRingHom x).1.map s).transpose * (JR (Fv F v) J).map e * (bc e.toRingHom x).1 = (JR (Fv F v) J).map e
    rw [← key]
    exact (Matrix.map_injective e.injective).eq_iff.symm
  have c1 : Continuous (bc (n := Fin n) e.toRingHom) := GlobalTheory.LFun.SplitChart.continuous_bc he
  have c2 : Continuous (bc (n := Fin n) e.symm.toRingHom) := GlobalTheory.LFun.SplitChart.continuous_bc he'
  have hemb := isEmbedding_matHom (Fv F v) σ J
  exact ⟨{ toFun := fun g => ⟨bc e.toRingHom (matHom _ σ J g), (mem _).1 g.2⟩
           invFun := fun u => (⟨bc e.symm.toRingHom u.1, (mem _).2 (by rw [e1]; exact u.2)⟩ : HR (Fv F v) σ J)
           left_inv := fun g => matHom_injective _ σ J (e2 _)
           right_inv := fun u => Subtype.ext (e1 _)
           map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul])
           continuous_toFun := (c1.comp hemb.continuous).subtype_mk _
           continuous_invFun := hemb.continuous_iff.2 (c2.comp continuous_subtype_val) }⟩

end Dict

open GlobalTheory.LFun.InertChart in

theorem stDict : CompanionTheory.Rg.Fl.StDict := by
  intro F E _ _ _ _ _ σ h n J hJ v
  letI nf : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI pf : ProperSpace (Fv F v) := properSpace_Fv v
  haveI uf : IsUltrametricDist (Fv F v) := inferInstance
  haveI cf : CharZero (Fv F v) := charZero_Fv
  by_cases hs : Nonempty (E →ₐ[F] Fv F v)
  · obtain ⟨τ⟩ := hs
    exact ⟨Fv F v, nf, uf, pf, cf, Or.inl ⟨splitEquiv h hJ τ⟩⟩
  · have hf : IsField (Fv F v ⊗[F] E) := isField_tensor_of_no_algHom h.2.2.1 (not_nonempty_iff.1 hs)
    haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    obtain ⟨L, nL, uL, pL, e, he, he', hn⟩ := exists_model (K := Fv F v) (A := Fv F v ⊗[F] E) hf
    have hcc : ∀ x, σ (σ x) = x := conj_conj h
    have hss : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := sigR_sigR _ hcc
    have hi : ∀ x : E, sigR (Fv F v) σ (inclR (Fv F v) x) = inclR (Fv F v) (σ x) := fun _ => rfl
    have hinj : Function.Injective (e.toRingHom.comp (inclR (Fv F v))) := RingHom.injective (e.toRingHom.comp (inclR (Fv F v)))
    have hL : CharZero L :=
      let ϕ : Fv F v →+* L := e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom
      (ϕ.charZero_iff ϕ.injective).1 cf
    refine ⟨L, nL, uL, pL, hL, Or.inr ⟨_, (JR (Fv F v) J).map e, fun x => ?_, fun x => ?_, ?_, ?_, ?_,
      exists_equiv_UG e he he'⟩⟩
    · simp [hss]
    · have := hn (sigEquiv (Fv F v) hcc) (e.symm x)
      simpa [sigEquiv_apply] using this
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := not_forall.1 (conj_ne h)
      refine ⟨e (inclR (Fv F v) x), fun ee => hx (hinj ?_)⟩
      simpa [hi] using ee
    · refine Matrix.ext fun i j => ?_
      simp [JR, hi, hJ.1 i j]
    · have : ((JR (Fv F v) J).map e).det = (e.toRingHom.comp (inclR (Fv F v))) J.det := by
        rw [RingHom.map_det]; rfl
      rw [this]
      exact (map_ne_zero_iff _ hinj).2 hJ.2

end GlobalTheory.CompanionTheory.DictLoc

end
