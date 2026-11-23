import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMC.DdRLine

theorem exists_sep (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    ∃ e : E ⊗[F] E, (∀ a : E, (a ⊗ₜ[F] (1 : E)) * e = ((1 : E) ⊗ₜ[F] a) * e) ∧
      Algebra.TensorProduct.lmul' F e = 1 := by
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  obtain ⟨t, h1, h2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := F) (S := E)).1 this
  refine ⟨t, fun a => ?_, h2⟩
  have := h1 a
  rw [sub_mul, sub_eq_zero] at this
  exact this.symm

open Classical in

theorem pair_sep {F E Ω : Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω]
    (e : E ⊗[F] E) (h1 : ∀ a : E, (a ⊗ₜ[F] (1 : E)) * e = ((1 : E) ⊗ₜ[F] a) * e)
    (h2 : Algebra.TensorProduct.lmul' F e = 1) (ν ν' : E →ₐ[F] Ω) :
    Algebra.TensorProduct.productMap ν ν' e = if ν = ν' then 1 else 0 := by
  split_ifs with h
  · subst h
    have : Algebra.TensorProduct.productMap ν ν = ν.comp (Algebra.TensorProduct.lmul' F) := by
      ext a <;> simp
    rw [this, AlgHom.comp_apply, h2, map_one]
  · obtain ⟨a, ha⟩ : ∃ a, ν a ≠ ν' a := by
      by_contra hc
      exact h (AlgHom.ext fun a => by_contra fun h' => hc ⟨a, h'⟩)
    have := congrArg (Algebra.TensorProduct.productMap ν ν') (h1 a)
    simp only [map_mul, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul] at this
    have h3 : (ν a - ν' a) * Algebra.TensorProduct.productMap ν ν' e = 0 := by
      rw [sub_mul, this, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ha)

theorem exists_glue {G F K₀ K B D E Ω : Type} [Group G] [Field F] [CharZero F] [Field K₀] [Field K]
    [Algebra F K₀] [Algebra F K] [Algebra K₀ K] [IsScalarTower F K₀ K]
    [CommRing B] [CommRing D] [Algebra F B] [Algebra K₀ B] [IsScalarTower F K₀ B]
    [Algebra F D] [Algebra K₀ D] [Algebra K D] [IsScalarTower F K D]
    [IsScalarTower K₀ K D] [IsScalarTower F K₀ D] (PD : PeriodData G F K₀ K B D)
    [Field E] [Algebra F E] [FiniteDimensional F E] [Field Ω] [Algebra F Ω]
    (j : Ω →ₐ[F] D) (s : G → (Ω ≃ₐ[F] Ω)) (hs : ∀ g ω, PD.actdR g (j ω) = j (s g ω))
    (μ : G →* Eˣ) (ρ : Representation E G (Fin 1 → E)) (hρ : ∀ g v, ρ g v = (μ g : E) • v)
    (τ : K →ₐ[F] E) (y : (E →ₐ[F] Ω) → D) (hΩ : ∀ ω, j ω ∈ PD.Fil 0) (hy : ∀ ν, y ν ∈ PD.Fil 0)
    (hG : ∀ g (ν : E →ₐ[F] Ω), j (s g (ν (μ g : E))) * PD.actdR g (y ν) = y ((s g).toAlgHom.comp ν))
    (hK : ∀ (ν : E →ₐ[F] Ω) (c : K), j (ν (τ c)) * y ν = algebraMap K D c * y ν) :
    ∃ x ∈ DdRE PD ρ τ, x ∈ FilV PD (LL := E) (V := Fin 1 → E) 0 ∧
      ∀ (ν : E →ₐ[F] Ω) (f : (Fin 1 → E) ⊗[F] D →ₗ[F] D),
        (∀ v b, f (v ⊗ₜ b) = j (ν (v 0)) * b) → f x = y ν := by
  classical
  obtain ⟨e, h1, h2⟩ := exists_sep F E
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : E →ₗ[F] (Fin 1 → E), ∀ a, L₁ a = fun _ => a :=
    ⟨LinearMap.pi fun _ => LinearMap.id, fun _ => rfl⟩
  obtain ⟨L₂, hL₂⟩ : ∃ L₂ : E →ₗ[F] D, ∀ b, L₂ b = ∑ ν : E →ₐ[F] Ω, j (ν b) * y ν :=
    ⟨∑ ν : E →ₐ[F] Ω, LinearMap.mulRight F (y ν) ∘ₗ (j.comp ν).toLinearMap, fun b => by
      simp [LinearMap.sum_apply]⟩
  have hsm : ∀ c a : E, c • L₁ a = L₁ (c * a) := fun c a => by
    rw [hL₁, hL₁]; rfl
  have hact : ∀ g b, PD.actdR g (L₂ b) = L₂ ((((μ g)⁻¹ : Eˣ) : E) * b) := fun g b => by
    let q : (E →ₐ[F] Ω) ≃ (E →ₐ[F] Ω) :=
      { toFun := fun ν => (s g).toAlgHom.comp ν
        invFun := fun ν => (s g).symm.toAlgHom.comp ν
        left_inv := fun ν => by ext a; simp
        right_inv := fun ν => by ext a; simp }
    rw [hL₂, hL₂, map_sum]
    conv_rhs => rw [← q.sum_comp]
    refine Finset.sum_congr rfl fun ν _ => ?_
    change _ = j (s g (ν _)) * y ((s g).toAlgHom.comp ν)
    rw [← hG, ← mul_assoc, ← map_mul, ← map_mul, ← map_mul, mul_right_comm, Units.inv_mul, one_mul, map_mul, hs]
  have hmul : ∀ (c : K) b, algebraMap K D c * L₂ b = L₂ (τ c * b) := fun c b => by
    rw [hL₂, hL₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [mul_left_comm, ← hK, map_mul, map_mul]
    ring
  let Ψ : E ⊗[F] E →ₗ[F] (Fin 1 → E) ⊗[F] D := TensorProduct.map L₁ L₂
  have hΨ : ∀ a b, Ψ (a ⊗ₜ b) = L₁ a ⊗ₜ L₂ b := fun _ _ => rfl
  have hA : ∀ g t, actVdR PD ρ g (Ψ t) = Ψ (((μ g : E) ⊗ₜ[F] (((μ g)⁻¹ : Eˣ) : E)) * t) := fun g t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, hΨ, hΨ, ← hsm, ← hact, ← hρ]
      rfl
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
  have hM : ∀ (c : K) t, mulVdR (Qp := F) (K := K) (BdR := D) (V := Fin 1 → E) (LL := E) c (Ψ t) =
      Ψ (((1 : E) ⊗ₜ[F] τ c) * t) := fun c t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul a b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, hΨ, hΨ, ← hmul, one_mul]
      rfl
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
  have hS : ∀ (c : E) t, c • Ψ t = Ψ ((c ⊗ₜ[F] (1 : E)) * t) := fun c t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero, smul_zero]
    | tmul a b => rw [Algebra.TensorProduct.tmul_mul_tmul, hΨ, hΨ, ← hsm, one_mul, TensorProduct.smul_tmul']
    | add a b ha hb => simp only [map_add, mul_add, smul_add, ha, hb]
  refine ⟨Ψ e, ⟨?_, ?_⟩, ?_, fun ν f hf => ?_⟩
  · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    have h3 : ((μ g : E) ⊗ₜ[F] (((μ g)⁻¹ : Eˣ) : E)) =
        ((1 : E) ⊗ₜ[F] (((μ g)⁻¹ : Eˣ) : E)) * ((μ g : E) ⊗ₜ[F] (1 : E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [hA, h3, mul_assoc, h1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, one_mul,
      ← Algebra.TensorProduct.one_def, one_mul]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro c
    rw [hM, hS, h1]
  · generalize e = t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a b =>
      have hb : L₂ b ∈ PD.Fil 0 := by
        rw [hL₂]
        exact Submodule.sum_mem _ fun ν _ => by simpa using PD.Fil_mul 0 0 _ _ (hΩ (ν b)) (hy ν)
      exact ⟨L₁ a ⊗ₜ ⟨L₂ b, hb⟩, rfl⟩
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · have h4 : ∀ t, f (Ψ t) = ∑ ν' : E →ₐ[F] Ω, j (Algebra.TensorProduct.productMap ν ν' t) * y ν' := fun t => by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [hΨ, hf, hL₁, hL₂, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν' _ => ?_
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_mul, mul_assoc]
      | add a b ha hb => simp only [map_add, ha, hb, add_mul, Finset.sum_add_distrib]
    rw [h4, Finset.sum_eq_single ν]
    · rw [pair_sep e h1 h2, if_pos rfl, map_one, one_mul]
    · intro ν' _ hne
      rw [pair_sep e h1 h2, if_neg (Ne.symm hne), map_zero, zero_mul]
    · exact fun h => absurd (Finset.mem_univ ν) h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (y : (↥LL.1 →ₐ[ℚ_[l]] Om l) → P.R.BdR),
    (∀ ω : Om l, algebraMap (Om l) P.R.BdR ω ∈ (P.PD K).Fil 0) →
    (∀ ν, y ν ∈ (P.PD K).Fil 0) →
    (∀ (g : ↥(GK K)) (ν : ↥LL.1 →ₐ[ℚ_[l]] Om l),
      algebraMap (Om l) P.R.BdR ((g : GQ l) (ν (μ g : ↥LL.1))) * P.actQdR (g : GQ l) (y ν) =
        y ((g : GQ l).toAlgHom.comp ν)) →
    (∀ (ν : ↥LL.1 →ₐ[ℚ_[l]] Om l) (c : ↥K.1),
      algebraMap (Om l) P.R.BdR (ν (τ c)) * y ν = algebraMap ↥K.1 P.R.BdR c * y ν) →
    ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) μ) τ,
      x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 0 ∧
      ∀ (ν : ↥LL.1 →ₐ[ℚ_[l]] Om l) (f : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] P.R.BdR),
        (∀ v b, f (v ⊗ₜ b) = algebraMap (Om l) P.R.BdR (ν (v 0)) * b) → f x = y ν := by
  intro l _ P K LL μ τ y hΩ hy hG hK
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact exists_glue (P.PD K) (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR) (fun g => (g : GQ l))
    (fun g ω => by rw [P.PD_actdR]; exact P.actQdR_Om _ _) μ _ (fun _ _ => rfl) τ y hΩ hy
    (fun g ν => by rw [P.PD_actdR]; exact hG g ν) hK

end GlobalTheory.PMC.DdRLine
