import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabfin
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

variable (F E) in

def adelstabT : E ⊗[F] FiniteAdeleRing (𝓞 F) F →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
  (TensorProduct.lid F _).toLinearMap ∘ₗ (Algebra.trace F E).rTensor _

theorem adelstabT_tmul (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    adelstabT F E (e ⊗ₜ a) = algebraMap F _ (Algebra.trace F E e) * a := by
  simp only [adelstabT, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, Algebra.smul_def]

theorem adelstab_trace_int (b : 𝓞 E) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = Algebra.trace F E (algebraMap (𝓞 E) E b) :=
  ⟨⟨_, Algebra.isIntegral_trace (R := ℤ) (RingOfIntegers.isIntegral_coe b)⟩, rfl⟩

theorem adelstabT_mem {s : 𝒜} (hs : s ∈ 𝒮) : adelstabT F E s ∈ intAd F := by
  obtain ⟨r, hr, rfl⟩ := levelaf_decomp (fun j => Module.finBasis ℤ (𝓞 E) j)
    (Module.Basis.span_eq _) hs
  rw [map_sum]
  refine sum_mem fun j _ => ?_
  rw [adelstabT_tmul]
  obtain ⟨t, ht⟩ := adelstab_trace_int (F := F) (Module.finBasis ℤ (𝓞 E) j)
  rw [← ht, ← IsScalarTower.algebraMap_apply]
  exact mul_mem (levelaf_int_mem t) (hr j)

theorem adelstab_F_int (k : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ intAd F) :
    k ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => ?_
  have hv : algebraMap F (v.adicCompletion F) k ∈ v.adicCompletionIntegers F := h v
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers, levelaf_valued_algebraMap] at hv

theorem adelstab_incl_int (b : 𝓞 E) :
    inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E b) ∈ 𝒮 :=
  levelaf_tmul_mem b (one_mem _)

theorem adelstab_tr_mem (e : E) (he : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e ∈ 𝒮) (b : 𝓞 E) :
    Algebra.trace F E (e * algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range := by
  apply adelstab_F_int
  have h1 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (e * algebraMap (𝓞 E) E b) ∈ 𝒮 := by
    rw [map_mul]; exact mul_mem he (adelstab_incl_int b)
  have := adelstabT_mem h1
  simpa [inclE, adelstabT_tmul] using this

theorem adelstab_dual {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E) (d : E)
    (hd : ∀ i, IsIntegral ℤ (d * β i)) (e : E)
    (he : ∀ b : 𝓞 E, Algebra.trace F E (e * algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range) :
    d * e ∈ Submodule.span (𝓞 F)
      (Set.range ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β)) := by
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  rw [← β'.sum_repr (d * e)]
  refine sum_mem fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  obtain ⟨t, ht⟩ := he ⟨d * β i, hd i⟩
  have : Algebra.trace F E (d * e * β i) = algebraMap (𝓞 F) F t := by
    rw [ht]; congr 1; show _ = e * (d * β i); ring
  rw [this, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Trace

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem adelstab_incl_C (d : 𝓞 F) : ι (algebraMap (𝓞 F) E d) = levelafC E d := by
  simp only [levelafC, inclE]
  first
  | (rw [Algebra.TensorProduct.includeLeftRingHom_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
      IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F),
      Algebra.algebraMap_eq_smul_one (A := E),
      Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F), TensorProduct.smul_tmul])
  | simp [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]

theorem adelstab_algebraMap_ne_zero (d : 𝓞 F) (hd : d ≠ 0) : algebraMap (𝓞 F) E d ≠ 0 := by
  intro h
  apply hd
  first
  | exact (FaithfulSMul.algebraMap_injective (𝓞 F) E) (h.trans (map_zero _).symm)
  | (rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_eq_zero_iff _ (algebraMap F E).injective] at h
     exact IsFractionRing.injective (𝓞 F) F (h.trans (map_zero _).symm))
  | simpa using h

variable (F E) in

def adelstabLam (G : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (L : Submodule 𝒮 (n → 𝒜)) :
    Submodule (𝓞 E) (n → E) where
  carrier := {x | ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈ L}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at *
    rw [show (fun i => ι (x i) + ι (y i)) = (fun i => ι (x i)) + (fun i => ι (y i)) from rfl,
      mulVec_add]
    exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
    rw [show (fun _ : n => (0 : 𝒜)) = 0 from rfl, mulVec_zero]
    exact zero_mem _
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply] at *
    have : (fun i => ι (a • x i)) = (ι (algebraMap (𝓞 E) E a)) • (fun i => ι (x i)) := by
      ext i; simp [Algebra.smul_def]
    rw [this, mulVec_smul]
    exact L.smul_mem ⟨_, adelstab_incl_int a⟩ hx

theorem adelstab_mem_iff (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (x : n → E) :
    x ∈ adelstabLam F E G L ↔ ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈ L := Iff.rfl

theorem adelstab_stab (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (γ₀ : GL n E)
    (hM : G⁻¹ * bc ι γ₀ * G ∈ stabGL L) : γ₀ ∈ stabGL (adelstabLam F E G L) := by
  intro x
  rw [adelstab_mem_iff, adelstab_mem_iff]
  have key : (fun i => ι (((γ₀ : Matrix n n E) *ᵥ x) i)) =
      ((bc ι γ₀ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) := by
    ext i; rw [RingHom.map_mulVec]; rfl
  rw [key, hM (((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i))), mulVec_mulVec, mulVec_mulVec]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Units.val_mul G G⁻¹, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem adelstab_span (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (c₁ d : 𝓞 F) (hc₁ : c₁ ≠ 0)
    (hd : d ≠ 0) (hL : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) → (fun i => levelafC E c₁ * v i) ∈ L)
    (hG : ∀ i j, levelafC E d * ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j ∈ 𝒮) :
    Submodule.span E (adelstabLam F E G L : Set (n → E)) = ⊤ := by
  set u : E := algebraMap (𝓞 F) E (c₁ * d)
  have hu : u ≠ 0 := adelstab_algebraMap_ne_zero _ (mul_ne_zero hc₁ hd)
  have hk : ∀ k, Pi.single k u ∈ adelstabLam F E G L := by
    intro k
    rw [adelstab_mem_iff]
    have : (fun i => ι ((Pi.single k u : n → E) i)) = Pi.single k (ι u) := by
      ext i; by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [this, mulVec_single]
    convert hL (fun i => levelafC E d * ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i k) (fun i => hG i k)
      using 1
    ext i
    simp only [u, adelstab_incl_C, levelafC_mul, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply]
    ring
  rw [eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  have : (Pi.basisFun E n) k = u⁻¹ • Pi.single k u := by
    rw [Pi.basisFun_apply, ← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hu]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hk k))

end Lattice

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem adelstab_finite (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (c₂ d : 𝓞 F) (hc₂ : c₂ ≠ 0)
    (hd : d ≠ 0) (hL : ∀ v ∈ L, ∀ i, levelafC E c₂ * v i ∈ 𝒮)
    (hG : ∀ i j, levelafC E d * (G : Matrix n n 𝒜) i j ∈ 𝒮) :
    Module.Finite (𝓞 E) (adelstabLam F E G L) := by
  classical
  set β := Module.finBasis F E
  obtain ⟨d₀, hd₀, -, hd₀i⟩ := sf_den (fun i => β i)
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  set u : E := algebraMap (𝓞 F) E (d * c₂)
  have hu : u ≠ 0 := adelstab_algebraMap_ne_zero _ (mul_ne_zero hd hc₂)
  set q : E := (d₀ * u)⁻¹
  set W : Submodule (𝓞 F) (n → E) := Submodule.span (𝓞 F)
    (Set.range fun p : n × Fin (Module.finrank F E) => (Pi.single p.1 (q * β' p.2) : n → E))
  have hle : (adelstabLam F E G L).restrictScalars (𝓞 F) ≤ W := by
    intro x hx
    have hw := hL _ hx
    set w := ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i))
    have hx' : (fun i => ι (x i)) = (G : Matrix n n 𝒜) *ᵥ w := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hj : ∀ j, ι (u * x j) ∈ 𝒮 := by
      intro j
      rw [map_mul, adelstab_incl_C, levelafC_mul, congrFun hx' j]
      simp only [mulVec, dotProduct, Finset.mul_sum]
      refine sum_mem fun k _ => ?_
      have : levelafC E d * levelafC E c₂ * ((G : Matrix n n 𝒜) j k * w k) =
          (levelafC E d * (G : Matrix n n 𝒜) j k) * (levelafC E c₂ * w k) := by ring
      rw [this]
      exact mul_mem (hG j k) (hw k)
    have hmem : ∀ j, d₀ * (u * x j) ∈ Submodule.span (𝓞 F) (Set.range β') :=
      fun j => adelstab_dual β d₀ hd₀i _ (adelstab_tr_mem _ (hj j))
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun j _ => ?_
    let Lj : E →ₗ[𝓞 F] (n → E) := (LinearMap.single (𝓞 F) (fun _ => E) j) ∘ₗ
      ((LinearMap.mulLeft F q).restrictScalars (𝓞 F))
    have h1 : Lj (d₀ * (u * x j)) = Pi.single j (x j) := by
      have hd0 : d₀ * u ≠ 0 := mul_ne_zero hd₀ hu
      simp only [Lj, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        LinearMap.mulLeft_apply, LinearMap.coe_single, q]
      congr 1
      rw [← mul_assoc, ← mul_assoc, mul_assoc _ d₀ u, inv_mul_cancel₀ hd0, one_mul]
    rw [← h1]
    have h2 := Submodule.mem_map_of_mem (f := Lj) (hmem j)
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨(j, i), by simp [Lj]⟩
  have : Module.Finite (𝓞 F) W := Module.Finite.span_of_finite _ (Set.finite_range _)
  have : IsNoetherian (𝓞 F) W := inferInstance
  have : IsNoetherian (𝓞 F) ((adelstabLam F E G L).restrictScalars (𝓞 F)) := isNoetherian_of_le hle
  have : Module.Finite (𝓞 F) (adelstabLam F E G L) := inferInstanceAs
    (Module.Finite (𝓞 F) ((adelstabLam F E G L).restrictScalars (𝓞 F)))
  exact Module.Finite.of_restrictScalars_finite (𝓞 F) (𝓞 E) _

end Fin

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem adelstab_entries (G : GL n 𝒜) (d : 𝓞 F) (c : 𝒮) (hc : (c : 𝒜) = levelafC E d)
    (h : (c : 𝒜) • (G : Matrix n n 𝒜) ∈ (RingHom.mapMatrix (m := n) (𝒮).subtype).range) :
    ∀ i j, levelafC E d * (G : Matrix n n 𝒜) i j ∈ 𝒮 := by
  intro i j
  obtain ⟨M, hM⟩ := h
  have h' := congrFun (congrFun hM i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h'
  rw [← hc, ← h']
  exact (M i j).2

theorem adelstab_core (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (L : Submodule 𝒮 (n → 𝒜)) (K : Subgroup (GL n 𝒜)) (hK : K ≤ stabGL L) (c₁ c₂ : 𝓞 F)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hL₁ : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) → (fun i => levelafC E c₁ * v i) ∈ L)
    (hL₂ : ∀ v ∈ L, ∀ i, levelafC E c₂ * v i ∈ 𝒮)
    (g : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    Finite (stabAt ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
      (UPts σ J (FiniteAdeleRing (𝓞 F) F))) (K.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g) := by
  classical
  set G : GL n 𝒜 := (g : GL n 𝒜)
  obtain ⟨d, hd, c, hc, hcg, hcgi⟩ := levelaf_exists_denom (E := E) G
  have hG := adelstab_entries G d c hc hcg
  have hGi := adelstab_entries G⁻¹ d c hc hcgi
  have hF : Finite (level (σ : E →+* E) J (adelstabLam F E G L)) :=
    UG_stabilizer_finite F E n σ J hτ hH hdet hdef _ (adelstab_finite G L c₂ d hc₂ hd hL₂ hG)
      (adelstab_span G L c₁ d hc₁ hd hL₁ hGi)
  have hrat : ∀ γ : stabAt ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
      (UPts σ J (FiniteAdeleRing (𝓞 F) F))) (K.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g,
      ∃ γ₀ : GL n E, γ₀ ∈ UJ (σ : E →+* E) J ∧ bc ι γ₀ = (((γ : _) : _) : GL n 𝒜) := by
    intro γ
    have h1 := Subgroup.mem_subgroupOf.1 γ.1.2
    obtain ⟨γ₀, h2, h3⟩ := Subgroup.mem_map.1 h1
    exact ⟨γ₀, h2, h3⟩
  choose f hfU hfeq using hrat
  have hmem : ∀ γ, f γ ∈ level (σ : E →+* E) J (adelstabLam F E G L) := by
    intro γ
    refine Subgroup.mem_inf.2 ⟨hfU γ, adelstab_stab G L (f γ) (hK ?_)⟩
    have h1 := Subgroup.mem_subgroupOf.1 γ.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hfeq γ]
    exact h1
  refine Finite.of_injective (fun γ => (⟨f γ, hmem γ⟩ : level (σ : E →+* E) J (adelstabLam F E G L))) ?_
  intro γ γ' h
  have h' : bc ι (f γ) = bc ι (f γ') := by
    have := congrArg (fun z : level (σ : E →+* E) J (adelstabLam F E G L) => bc ι (z : GL n E)) h
    simpa using this
  rw [hfeq, hfeq] at h'
  exact Subtype.ext (Subtype.ext (Subtype.ext h'))

theorem adelstab_levelafC_one : levelafC (F := F) E 1 = 1 := by
  simp [levelafC]
  first
  | rfl
  | exact Algebra.TensorProduct.one_def.symm

theorem adelstab_mem_stdLat (v : n → 𝒜) : v ∈ stdLat (n := n) (A := 𝒜) ↥𝒮 ↔ ∀ i, v i ∈ 𝒮 := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨v i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

end Main

theorem adelic_stabilizer_finite_holds : Formalism.UG.AdelicStabFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef g
  refine adelstab_core σ J hτ hH hdet hdef _ (levelAf σ J) inf_le_right 1 1 one_ne_zero one_ne_zero
    ?_ ?_ g
  · intro v hv
    rw [adelstab_mem_stdLat]
    intro i
    rw [adelstab_levelafC_one, one_mul]
    exact hv i
  · intro v hv i
    rw [adelstab_levelafC_one, one_mul]
    exact (adelstab_mem_stdLat v).1 hv i

end Formalism.UG.P
