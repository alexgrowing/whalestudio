import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetAvg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ClassSumLevel

def levG {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) :
    Subgroup (GA D V) where
  carrier := {g | ∃ κ : S.U, κ.1.1 = finM V hn g}
  one_mem' := ⟨1, by rw [GlobalTheory.AdForm.Model.finM_one]; rfl⟩
  mul_mem' := by
    rintro a b ⟨κ, hκ⟩ ⟨κ', hκ'⟩
    exact ⟨κ * κ', by rw [GlobalTheory.AdForm.Model.finM_mul, ← hκ, ← hκ']; rfl⟩
  inv_mem' := by
    rintro a ⟨κ, hκ⟩
    refine ⟨κ⁻¹, ?_⟩
    have h1 : finM V hn a⁻¹ * κ.1.1 = 1 := by
      rw [hκ, ← GlobalTheory.AdForm.Model.finM_mul, inv_mul_cancel, GlobalTheory.AdForm.Model.finM_one]
    have h2 : κ.1.1 * (κ.1⁻¹ : GL (Fin n) _).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (κ⁻¹ : S.U).1.1 = (κ.1⁻¹ : GL (Fin n) _).1 := rfl
      _ = (finM V hn a⁻¹ * κ.1.1) * (κ.1⁻¹ : GL (Fin n) _).1 := by rw [h1, Matrix.one_mul]
      _ = finM V hn a⁻¹ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem mem_levG {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (g : GA D V) :
    g ∈ levG V hn S ↔ ∃ κ : S.U, κ.1.1 = finM V hn g := Iff.rfl

section Swap
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (topTens)

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

def swapL : letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
    (E ⊗[F] FiniteAdeleRing (𝓞 F) F) ≃ₗ[FiniteAdeleRing (𝓞 F) F] (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
  { (Algebra.TensorProduct.comm F E (FiniteAdeleRing (𝓞 F) F)).toLinearEquiv with
    map_smul' := by
      intro a x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul e b =>
        rw [Algebra.smul_def, show algebraMap (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) a = (1 : E) ⊗ₜ a from rfl,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp [mul_comm]
        rw [TensorProduct.smul_tmul', smul_eq_mul]
      | add x y hx hy => simp_all [smul_add] }

theorem swapL_continuous : letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous (swapL F E) ∧ Continuous (swapL F E).symm := by
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)
  haveI := IsModuleTopology.toContinuousSMul (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  haveI := IsModuleTopology.toContinuousSMul (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  exact ⟨IsModuleTopology.continuous_of_linearMap (swapL F E).toLinearMap,
    IsModuleTopology.continuous_of_linearMap (swapL F E).symm.toLinearMap⟩

end Swap

theorem finM_inv_mul {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (a : GA D V) : finM V hn a⁻¹ * finM V hn a = 1 := by
  rw [← GlobalTheory.AdForm.Model.finM_mul, inv_mul_cancel, GlobalTheory.AdForm.Model.finM_one]

theorem finM_mul_inv {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (a : GA D V) : finM V hn a * finM V hn a⁻¹ = 1 := by
  rw [← GlobalTheory.AdForm.Model.finM_mul, mul_inv_cancel, GlobalTheory.AdForm.Model.finM_one]

theorem finM_eq_one_of_mem_GinfC {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {k : GA D V} (hk : k ∈ GinfC V) :
    finM V hn k = 1 := by
  subst hn
  have h1 : finHom V k = 1 := hk
  have h2 : (Lev.finE V k : GL (Fin V.rank) (Lev.EAf D)) = 1 := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = 1
    rw [h1, map_one]
  have h3 : finM V rfl k = (Lev.finE V k : GL (Fin V.rank) (Lev.EAf D)).1 := rfl
  rw [h3, h2]
  rfl

set_option maxHeartbeats 4000000 in

theorem ncard_stab {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (a : GA D V)
    (y : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (ha : finM V hn a = y.1.1) :
    {γ : GA D V | γ ∈ GQ V ∧ a⁻¹ * γ * a ∈ levG V hn S}.ncard =
      Nat.card {γ : GQ V // ∃ κ : S.U, finM V hn γ.1 * y.1.1 = y.1.1 * κ.1.1} := by
  have e : {γ : GA D V | γ ∈ GQ V ∧ a⁻¹ * γ * a ∈ levG V hn S} =
      Subtype.val '' {γ : GQ V | a⁻¹ * γ.1 * a ∈ levG V hn S} := by
    ext γ
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨γ, h1⟩, h2, rfl⟩
    · rintro ⟨δ, h2, rfl⟩
      exact ⟨δ.2, h2⟩
  rw [e, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  have h1 := finM_inv_mul V hn a
  have h2 := finM_mul_inv V hn a
  rw [ha] at h1 h2
  have key : ∀ γ : GQ V, a⁻¹ * γ.1 * a ∈ levG V hn S ↔ ∃ κ : S.U, finM V hn γ.1 * y.1.1 = y.1.1 * κ.1.1 := by
    intro γ
    simp only [mem_levG, GlobalTheory.AdForm.Model.finM_mul, ha]
    constructor
    · rintro ⟨κ, hκ⟩
      refine ⟨κ, ?_⟩
      rw [hκ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    · rintro ⟨κ, hκ⟩
      refine ⟨κ, ?_⟩
      rw [Matrix.mul_assoc, hκ, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  exact Nat.card_congr (Equiv.subtypeEquivRight key)

def finGLHom {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) :
    GA D V →* GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) where
  toFun := GlobalTheory.AdForm.Model.finGL V hn
  map_one' := Units.ext (GlobalTheory.AdForm.Model.finM_one V hn)
  map_mul' a b := Units.ext (GlobalTheory.AdForm.Model.finM_mul V hn a b)

theorem mem_levG_iff {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (g : GA D V) :
    g ∈ levG V hn S ↔ finGLHom V hn g ∈ S.U := by
  constructor
  · rintro ⟨κ, hκ⟩
    have : finGLHom V hn g = κ.1 := Units.ext hκ.symm
    rw [this]
    exact κ.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

theorem finM_apply {D : D7} (V : HSp D) (g : GA D V) (i j : Fin V.rank) :
    finM V rfl g i j = (swapL D.host.F D.host.E).symm ((finHom V g).1 i j) := rfl

theorem continuous_finM {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) :
    letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    Continuous (finM V hn) := by
  subst hn
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  refine continuous_matrix fun i j => ?_
  simp only [finM_apply]
  exact (swapL_continuous D.host.F D.host.E).2.comp ((GlobalTheory.Member.continuous_finHom_val D V).matrix_elem i j)

theorem continuous_finGLHom {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) :
    letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    Continuous (finGLHom V hn) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  exact Units.continuous_iff.2 ⟨continuous_finM V hn, (continuous_finM V hn).comp continuous_inv⟩

theorem isOpen_levG {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) :
    IsOpen ((levG V hn S : Subgroup (GA D V)) : Set (GA D V)) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have hc := (continuous_finGLHom V hn).subtype_mk (GlobalTheory.AdForm.Model.finGL_mem V hn)
  have := S.U_open.preimage hc
  convert this using 1
  ext g
  exact mem_levG_iff V hn S g

theorem isCompact_levG {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad)
    (hV : ∀ τ, (gramAt D V τ).PosDef) :
    IsCompact ((levG V hn S : Subgroup (GA D V)) : Set (GA D V)) := by
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  have hcl := Subgroup.isClosed_of_isOpen _ (isOpen_levG V hn S)
  subst hn
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have hC : IsCompact (⋃ p : Fin V.rank × Fin V.rank,
      (fun x : GL (Fin V.rank) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) =>
        swapL D.host.F D.host.E (x.1 p.1 p.2)) '' (S.U : Set _)) :=
    isCompact_iUnion fun p => S.U_compact.image
      ((swapL_continuous D.host.F D.host.E).1.comp (Units.continuous_val.matrix_elem p.1 p.2))
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.RepsObj.exists_compact_of_fin V hV hC
  refine hK.of_isClosed_subset hcl fun k hk => hKe k fun i j => ?_
  obtain ⟨κ, hκ⟩ := hk
  refine Set.mem_iUnion.2 ⟨(i, j), κ.1, κ.2, ?_⟩
  simp only [hκ, finM_apply]
  exact LinearEquiv.apply_symm_apply _ _

theorem finGLHom_mem_ratPts {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {γ : GA D V} (hγ : γ ∈ GQ V) :
    finGLHom V hn γ ∈ ratPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have e' : mt V γ = δ.1.map (incA D) := congrArg Units.val e.symm
  refine ⟨δ, hδ, Units.ext ?_⟩
  change _ = finM V rfl γ
  simp only [finM, e', finCongr_refl, Matrix.reindex_refl_refl]
  rfl

theorem exists_GQ_of_mem_ratPts {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n)
    {x : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (hx : x ∈ ratPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ γ ∈ GQ V, finGLHom V hn γ = x := by
  subst hn
  obtain ⟨δ, hδ, rfl⟩ := hx
  have hδ' : cT (sigD D : D.host.E →+* D.host.E) δ.1 * V.gram * δ.1 = V.gram := hδ
  have hm : bc (incA D) δ ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    have h2 := congrArg (fun M => M.map (incA D)) hδ'
    simp only [Matrix.map_mul] at h2
    exact h2
  exact ⟨⟨bc (incA D) δ, hm⟩, Subgroup.mem_subgroupOf.2 ⟨δ, hδ, rfl⟩, Units.ext rfl⟩

theorem existsUnique_class {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
    (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hy : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S))) (h : cl → GA D V)
    (hh : ∀ c, finM V hn (h c) = (yc c).1.1) (x : GA D V) :
    ∃! c, ∃ γ ∈ GQ V, ∃ k ∈ levG V hn S, x = γ * h c * k := by
  have hh' : ∀ c, finGLHom V hn (h c) = (yc c).1 := fun c => Units.ext (hh c)
  have key : ∀ c, (∃ γ ∈ GQ V, ∃ k ∈ levG V hn S, x = γ * h c * k) ↔
      (Quotient.mk'' (yc c) : Cls S) = Quotient.mk'' ⟨finGLHom V hn x, GlobalTheory.AdForm.Model.finGL_mem V hn x⟩ := by
    intro c
    refine Iff.trans ?_ (DoubleCoset.eq _ _ (yc c) _).symm
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨⟨finGLHom V hn γ, GlobalTheory.AdForm.Model.finGL_mem V hn γ⟩, finGLHom_mem_ratPts V hn hγ,
        ⟨finGLHom V hn k, GlobalTheory.AdForm.Model.finGL_mem V hn k⟩, (mem_levG_iff V hn S k).1 hk, Subtype.ext ?_⟩
      show finGLHom V hn (γ * h c * k) = finGLHom V hn γ * (yc c).1 * finGLHom V hn k
      simp only [map_mul, hh']
    · rintro ⟨a, ha, b, hb, e⟩
      obtain ⟨γ, hγ, eγ⟩ := exists_GQ_of_mem_ratPts V hn (Subgroup.mem_subgroupOf.1 ha)
      have e' : finGLHom V hn x = a.1 * (yc c).1 * b.1 := congrArg Subtype.val e
      refine ⟨γ, hγ, (γ * h c)⁻¹ * x, (mem_levG_iff V hn S _).2 ?_, (mul_inv_cancel_left _ _).symm⟩
      simp only [map_mul, map_inv, hh', eγ, e', inv_mul_cancel_left]
      exact Subgroup.mem_subgroupOf.1 hb
  simp only [key]
  exact hy.existsUnique _

theorem integral_eq_classSum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E), J = V.gram.reindex (finCongr hn) (finCongr hn) → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (cl : Type) (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → V.SigOK → (∀ τ, (gramAt D V τ).PosDef) → ∀ [Fintype cl] (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ h : cl → GA D V, (∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (yc c).1.1) → ∃ (vol : ℝ) (ν : Measure (GinfC V)), 0 < vol ∧ ν.IsHaarMeasure ∧ ν Set.univ = 1 ∧ ∀ Φ : GA D V → ℂ, Continuous Φ → (∀ γ ∈ GQ V, ∀ x, Φ (γ * x) = Φ x) → (∀ k ∈ GfC V, (∃ κ : S.U, κ.1.1 = finM V hn k) → ∀ x, Φ (x * k) = Φ x) → ∫ x in 𝓕, Φ x ∂μ = (vol : ℂ) * ∑ c, ((Nat.card {γ : GQ V // ∃ κ : S.U, finM V hn γ.1 * (yc c).1.1 = (yc c).1.1 * κ.1.1} : ℕ) : ℂ)⁻¹ * ∫ k, Φ (h c * k.1) ∂ν := by
  intro D θ hθ V n hn J hJ T f bad S cl yc hbij hSig hPD _ μ 𝓕 hμ h𝓕 h hh
  subst hJ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  haveI : μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have hKo := isOpen_levG V hn S
  have hKc := isCompact_levG V hn S hPD
  have hGK : GinfC V ≤ levG V hn S := by
    intro k hk
    exact ⟨1, (finM_eq_one_of_mem_GinfC V hn hk).symm⟩
  haveI : CompactSpace (GinfC V) :=
    isCompact_iff_compactSpace.mp (hKc.of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) hGK)
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  have hsplit : ∀ g : GA D V, ∃ a ∈ GfC V, ∃ b ∈ GinfC V, g = a * b := by
    intro g
    have h1 : g ∈ ((⊤ : Subgroup (GL (Fin V.rank) (Lev.EAf D))).comap (Lev.finE V)) := trivial
    rw [GlobalTheory.Mass.Levels.comap_finE] at h1
    have h2 : g ∈ ((Lev.levA V ⊤ ⊔ GinfC V : Subgroup (GA D V)) : Set (GA D V)) := h1
    rw [Subgroup.mul_normal] at h2
    obtain ⟨a, ha, b, hb, e⟩ := h2
    exact ⟨a, ha.1, b, hb, e.symm⟩
  have hdec : ∀ k ∈ levG V hn S, ∃ k' ∈ GfC V ⊓ levG V hn S, ∃ w : GinfC V, k = k' * (GinfC V).subtype w := by
    intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit k
    refine ⟨a, ⟨ha, ?_⟩, ⟨b, hb⟩, rfl⟩
    have := (levG V hn S).mul_mem hk ((levG V hn S).inv_mem (hGK hb))
    rwa [mul_inv_cancel_right] at this
  have hcomm : ∀ k ∈ GfC V ⊓ levG V hn S, ∀ w : GinfC V, k * (GinfC V).subtype w = (GinfC V).subtype w * k :=
    fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 hk.1).symm
  have hne : μ (levG V hn S) ≠ 0 := hKo.measure_ne_zero μ ⟨1, (levG V hn S).one_mem⟩
  have htop : μ (levG V hn S) ≠ ⊤ := hKc.measure_lt_top.ne
  have hu := existsUnique_class V hn S yc hbij h (fun c => (hh c).2)
  have hfin : ∀ i, {γ : GA D V | γ ∈ GQ V ∧ (h i)⁻¹ * γ * h i ∈ levG V hn S}.Finite := by
    intro i
    have := GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ V) (levG V hn S) h𝓕 hne htop (h i)
    refine (this.image Subtype.val).subset ?_
    rintro γ ⟨hγ, h2⟩
    exact ⟨⟨γ, hγ⟩, h2, rfl⟩
  have hν : ∃ ν : Measure (GinfC V), ν.IsHaarMeasure ∧ ν Set.univ = 1 := by
    refine ⟨Measure.haarMeasure ⊤, inferInstance, ?_⟩
    have := Measure.haarMeasure_self (G := GinfC V) (K₀ := ⊤)
    simpa using this
  obtain ⟨ν, hνH, hν1⟩ := hν
  haveI : IsProbabilityMeasure ν := ⟨hν1⟩
  refine ⟨(μ (levG V hn S)).toReal, ν, ENNReal.toReal_pos hne htop, hνH, hν1, fun Φ hΦc hΦl hΦr => ?_⟩
  obtain ⟨-, he⟩ := GlobalTheory.integral_fundamentalDomain_eq_sum_doubleCoset_avg (GA D V) μ (GQ V) (levG V hn S)
    (GfC V ⊓ levG V hn S) 𝓕 h𝓕 hKo htop
    (GinfC V) ν (GinfC V).subtype continuous_subtype_val hdec hcomm cl h hu hfin Φ hΦc hΦl
    (fun k hk x => hΦr k hk.1 hk.2 x)
  refine he.trans ?_
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  exact congrArg (fun m : ℕ => ((m : ℂ))⁻¹ * ∫ v, Φ (h c * (GinfC V).subtype v) ∂ν) (ncard_stab V hn S (h c) (yc c) (hh c).2)

end GlobalTheory.ClassSumLevel

end
