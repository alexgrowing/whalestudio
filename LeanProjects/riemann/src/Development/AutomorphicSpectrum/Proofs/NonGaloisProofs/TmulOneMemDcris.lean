import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComponentEquiv
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LinearRelationExactSequenceDimStatement

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open TensorProduct

namespace GlobalTheory.CompanionTheory.BKDim

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem φVB_tmul_one (v : V) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : B) := by
  simp [φVB]

theorem ιV_tmul_one (v : V) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : BdR) := by
  simp [ιV]

theorem actVB_tmul_one (g : G) (v : V) :
    actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem actVdR_tmul_one (g : G) (v : V) :
    actVdR PD ρ g (v ⊗ₜ[Qp] (1 : BdR)) = ρ g v ⊗ₜ[Qp] (1 : BdR) := by
  simp [actVdR]

theorem mem_H0V_iff {v : V} : v ∈ H0V ρ ↔ ∀ g, ρ g v = v := by
  simp [H0V, Submodule.mem_iInf, sub_eq_zero]

theorem mem_Dcris_iff {x : V ⊗[Qp] B} : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_DdR_iff {x : V ⊗[Qp] BdR} : x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem tmul_one_mem_Dcris {v : V} (hv : v ∈ H0V ρ) : v ⊗ₜ[Qp] (1 : B) ∈ Dcris PD ρ :=
  (mem_Dcris_iff PD ρ).2 fun g => by rw [actVB_tmul_one, (mem_H0V_iff ρ).1 hv g]

theorem tmul_one_mem_DdR {v : V} (hv : v ∈ H0V ρ) : v ⊗ₜ[Qp] (1 : BdR) ∈ DdR PD ρ :=
  (mem_DdR_iff PD ρ).2 fun g => by rw [actVdR_tmul_one, (mem_H0V_iff ρ).1 hv g]

theorem tmul_one_mem_FilV (v : V) : v ⊗ₜ[Qp] (1 : BdR) ∈ FilV PD (LL := LL) (V := V) 0 :=
  GlobalTheory.CobCrisLift.tmul_mem PD v PD.one_mem

theorem sub_φVB_mem_Dcris {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ :=
  GlobalTheory.CobCrisLift.sub_φ_mem_Dcris PD ρ 0 x fun g => by
    rw [(mem_Dcris_iff PD ρ).1 hx g]; simp

def aMap : ↥(H0V ρ) →ₗ[LL]
    ↥(Dcris PD ρ) × ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) where
  toFun v := (⟨(v : V) ⊗ₜ[Qp] (1 : B), tmul_one_mem_Dcris PD ρ v.2⟩,
    ⟨(v : V) ⊗ₜ[Qp] (1 : BdR), tmul_one_mem_DdR PD ρ v.2, tmul_one_mem_FilV PD (v : V)⟩)
  map_add' u v := by
    ext <;> simp [add_tmul]
  map_smul' c v := by
    ext <;> simp [smul_tmul']

def bMap : (↥(Dcris PD ρ) × ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0)) →ₗ[LL]
    ↥(Dcris PD ρ) × ↥(DdR PD ρ) where
  toFun p := (⟨(p.1 : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) p.1, sub_φVB_mem_Dcris PD ρ p.1.2⟩,
    ⟨ιV PD (LL := LL) (V := V) p.1 - p.2, Submodule.sub_mem _ (GlobalTheory.DRFil.ιV_mem_DdR PD ρ p.1.2) p.2.2.1⟩)
  map_add' p q := by
    ext
    · simp only [Prod.fst_add, Submodule.coe_add, map_add]; abel
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]; abel
  map_smul' c p := by
    ext
    · simp [smul_sub]
    · simp [smul_sub]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def relR : Submodule LL ((↥(Dcris PD ρ) × ↥(DdR PD ρ)) × FiniteCohomology PD ρ) where
  carrier := {p | ∃ (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (c : ↥(finiteCocycles PD ρ)),
    y ∈ FilV PD (LL := LL) (V := V) 0 ∧ x - φVB PD (LL := LL) (V := V) x = p.1.1 ∧
    ιV PD (LL := LL) (V := V) x - y = p.1.2 ∧
    (∀ g, (c : G → V) g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) ∧
    Submodule.Quotient.mk c = p.2}
  add_mem' := by
    rintro p q ⟨x, y, c, hy, h1, h2, h3, h4⟩ ⟨x', y', c', hy', h1', h2', h3', h4'⟩
    refine ⟨x + x', y + y', c + c', add_mem hy hy', ?_, ?_, fun g => ?_, ?_⟩
    · simp only [Prod.fst_add, Submodule.coe_add, map_add, ← h1, ← h1']; abel
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, ← h2, ← h2']; abel
    · simp only [Submodule.coe_add, Pi.add_apply, add_tmul, h3, h3', map_add]; abel
    · simp only [Prod.snd_add, ← h4, ← h4']; rfl
  zero_mem' := ⟨0, 0, 0, zero_mem _, by simp, by simp, by simp, rfl⟩
  smul_mem' := by
    rintro t p ⟨x, y, c, hy, h1, h2, h3, h4⟩
    refine ⟨t • x, t • y, t • c, Submodule.smul_mem _ t hy, ?_, ?_, fun g => ?_, ?_⟩
    · simp only [Prod.smul_fst, Submodule.coe_smul, map_smul, ← h1, smul_sub]
    · simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul, ← h2, smul_sub]
    · simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, ← smul_sub, ← h3]; rfl
    · simp only [Prod.smul_snd, ← h4]; rfl

include PD in
theorem cocycle_eq_cob {c : G → V} {v : V} {x : V ⊗[Qp] B}
    (hc : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (hx : x = v ⊗ₜ[Qp] (1 : B)) :
    c ∈ B1 ρ := by
  refine ⟨v, funext fun g => GlobalTheory.BKRightExact.tmul_one_injective PD ?_⟩
  have : cob ρ v g = ρ g v - v := rfl
  rw [this, hc g, hx, actVB_tmul_one, sub_tmul]

theorem finrank_eq (hD : FiniteDimensional LL ↥(Dcris PD ρ)) (hR : FiniteDimensional LL ↥(DdR PD ρ))
    (hfund : ∀ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x →
      ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B))
    (hconn : ∀ d₁ ∈ Dcris PD ρ, ∀ d₂ ∈ DdR PD ρ, ∃ (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (c : G → V),
      y ∈ FilV PD (LL := LL) (V := V) 0 ∧ x - φVB PD (LL := LL) (V := V) x = d₁ ∧
      ιV PD (LL := LL) (V := V) x - y = d₂ ∧ c ∈ finiteCocycles PD ρ ∧
      ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x)
    (hlift : ∀ (c : G → V) (x : V ⊗[Qp] B), (∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) →
      x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ ∧ ∃ d ∈ DdR PD ρ,
        ιV PD (LL := LL) (V := V) x - d ∈ FilV PD (LL := LL) (V := V) 0) :
    (finrank LL (FiniteCohomology PD ρ) : ℤ) = finrank LL ↥(H0V ρ) +
      ((finrank LL ↥(DdR PD ρ) : ℤ) - finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0)) := by
  have hker : ∀ p : ↥(Dcris PD ρ) × ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0),
      bMap PD ρ p = 0 → p ∈ LinearMap.range (aMap PD ρ) := by
    rintro ⟨⟨d, hd⟩, ⟨e, he, hef⟩⟩ h
    have h1 : d - φVB PD (LL := LL) (V := V) d = 0 := congrArg (fun z => (z.1 : V ⊗[Qp] B)) h
    have h2 : ιV PD (LL := LL) (V := V) d - e = 0 := congrArg (fun z => (z.2 : V ⊗[Qp] BdR)) h
    have h2' := sub_eq_zero.1 h2
    obtain ⟨v, rfl⟩ := hfund d (sub_eq_zero.1 h1).symm (h2' ▸ hef)
    have hv : v ∈ H0V ρ := (mem_H0V_iff ρ).2 fun g =>
      GlobalTheory.BKRightExact.tmul_one_injective PD (by
        rw [← actVB_tmul_one PD ρ]; exact (mem_Dcris_iff PD ρ).1 hd g)
    refine ⟨⟨v, hv⟩, ?_⟩
    ext
    · rfl
    · simpa [aMap, ιV_tmul_one] using (ιV_tmul_one PD v).symm.trans h2'
  have hRan : LinearMap.range (aMap PD ρ) = LinearMap.ker (bMap PD ρ) := by
    refine le_antisymm ?_ fun p hp => hker p hp
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    ext
    · simp [aMap, bMap, φVB_tmul_one]
    · simp [aMap, bMap, ιV_tmul_one]
  have hInj : Function.Injective (aMap PD ρ) := by
    intro u v h
    exact Subtype.ext (GlobalTheory.BKRightExact.tmul_one_injective PD
      (congrArg (fun z => (z.1 : V ⊗[Qp] B)) h))
  have hAll : ∀ n, ∃ q, (n, q) ∈ relR PD ρ := by
    rintro ⟨⟨d₁, h₁⟩, ⟨d₂, h₂⟩⟩
    obtain ⟨x, y, c, hy, e1, e2, hc, hcx⟩ := hconn d₁ h₁ d₂ h₂
    exact ⟨Submodule.Quotient.mk ⟨c, hc⟩, x, y, ⟨c, hc⟩, hy, e1, e2, hcx, rfl⟩
  have hOnto : ∀ q, ∃ n, (n, q) ∈ relR PD ρ := by
    intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨-, x, hx⟩ := c.2
    obtain ⟨h1, d, hd, hy⟩ := hlift c x hx
    exact ⟨(⟨_, h1⟩, ⟨d, hd⟩), x, _, c, hy, rfl, by simp, hx, rfl⟩
  have hZero : ∀ q, ((0 : ↥(Dcris PD ρ) × ↥(DdR PD ρ)), q) ∈ relR PD ρ → q = 0 := by
    rintro q ⟨x, y, c, hy, e1, e2, hc, rfl⟩
    have e1' : x - φVB PD (LL := LL) (V := V) x = 0 := e1
    have e2' : ιV PD (LL := LL) (V := V) x - y = 0 := e2
    obtain ⟨v, hv⟩ := hfund x (sub_eq_zero.1 e1').symm (sub_eq_zero.1 e2' ▸ hy)
    exact (Submodule.Quotient.mk_eq_zero _).2 (cocycle_eq_cob PD ρ hc hv)
  have hBack : ∀ n, (n, (0 : FiniteCohomology PD ρ)) ∈ relR PD ρ ↔ n ∈ LinearMap.range (bMap PD ρ) := by
    intro n
    constructor
    · rintro ⟨x, y, c, hy, e1, e2, hc, hq⟩
      obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq
      have hcv : ∀ g, actVB PD ρ g (x - v ⊗ₜ[Qp] (1 : B)) = x - v ⊗ₜ[Qp] (1 : B) := by
        intro g
        have h1 : (c : G → V) g = ρ g v - v := (congrFun hv g).symm
        have h2 := hc g
        rw [h1, sub_tmul, ← actVB_tmul_one PD ρ] at h2
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
        exact h2.symm
      have hd : x - v ⊗ₜ[Qp] (1 : B) ∈ Dcris PD ρ := (mem_Dcris_iff PD ρ).2 hcv
      have hιd : ιV PD (LL := LL) (V := V) (x - v ⊗ₜ[Qp] (1 : B)) - n.2 =
          y - v ⊗ₜ[Qp] (1 : BdR) := by
        rw [map_sub, ιV_tmul_one, ← e2]; abel
      have hmem : y - v ⊗ₜ[Qp] (1 : BdR) ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0 :=
        ⟨hιd ▸ Submodule.sub_mem _ (GlobalTheory.DRFil.ιV_mem_DdR PD ρ hd) n.2.2,
          Submodule.sub_mem _ hy (tmul_one_mem_FilV PD v)⟩
      refine ⟨(⟨_, hd⟩, ⟨_, hmem⟩), ?_⟩
      ext
      · change (x - v ⊗ₜ[Qp] (1 : B)) - φVB PD (LL := LL) (V := V) (x - v ⊗ₜ[Qp] (1 : B)) = _
        rw [map_sub, φVB_tmul_one, ← e1]; abel
      · change ιV PD (LL := LL) (V := V) (x - v ⊗ₜ[Qp] (1 : B)) - (y - v ⊗ₜ[Qp] (1 : BdR)) = _
        rw [← hιd]; abel
    · rintro ⟨⟨⟨d, hd⟩, ⟨e, he, hef⟩⟩, rfl⟩
      refine ⟨d, e, 0, hef, rfl, rfl, fun g => ?_, rfl⟩
      rw [(mem_Dcris_iff PD ρ).1 hd g]
      simp
  obtain ⟨-, hcount⟩ := GlobalTheory.T.linear_relation_exact_sequence_dim LL _ _ _ _ (aMap PD ρ) (bMap PD ρ) (relR PD ρ) hInj hRan hAll
    hOnto hZero hBack
  rw [Module.finrank_prod, Module.finrank_prod] at hcount
  omega

end Generic

theorem finite_periods {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V) :
    FiniteDimensional LL ↥(Dcris (P.PD K) ρ) ∧ FiniteDimensional LL ↥(DdR (P.PD K) ρ) := by
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  have h1 := (GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings l P AI T K L).2 V (GlobalTheory.BKRightExact.res ↥L.1 ρ)
  have h2 := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K L V (GlobalTheory.BKRightExact.res ↥L.1 ρ)).1
  rw [GlobalTheory.BKRightExact.Dcris_res] at h1
  rw [GlobalTheory.BKRightExact.DdR_res] at h2
  have h1' : Module.Finite ↥L.1 ↥(Dcris (P.PD K) ρ) := h1
  have h2' : Module.Finite ↥L.1 ↥(DdR (P.PD K) ρ) := h2
  exact ⟨Module.Finite.of_restrictScalars_finite ↥L.1 LL _,
    Module.Finite.of_restrictScalars_finite ↥L.1 LL _⟩

theorem bkADim_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, LocalSituation.bkADim (P.PD K) := by
  intro l _ P AI T K LL _ _ _ O _ _ hO A hdr
  haveI := hO.2.1
  obtain ⟨hD, hR⟩ := finite_periods T K LL A.ρ
  exact finrank_eq (P.PD K) A.ρ hD hR
    (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K LL A.V).2
    (fun d₁ h₁ d₂ h₂ => GlobalTheory.T.exists_blochKato_cocycle_of_crys_deRham_pair l P AI T K LL O hO A d₁ h₁ d₂ h₂)
    (fun c x hx => GlobalTheory.T.crystalline_coboundary_lift l P AI T K LL O hO A hdr c x hx)

end GlobalTheory.CompanionTheory.BKDim
