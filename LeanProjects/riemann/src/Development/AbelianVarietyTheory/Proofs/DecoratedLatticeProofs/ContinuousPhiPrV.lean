import Mathlib
import Formalism.LocalToGlobal.HermitianForms.DefsGH
import Formalism.LocalToGlobal.Columns.RecLevelTop
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.LevelCharOpen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem redM_eq_one (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hX : ∀ i j, Valued.v (X i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) : redM F v X = 1 := by
  ext i j
  have h1 : (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hd : X i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := (hX i j).le
  have hx : X i j ∈ v.adicCompletionIntegers F := by
    have := add_mem hd h1
    rwa [sub_add_cancel] at this
  have h0 : IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hd⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact (hX i j).ne
  have e : (⟨X i j, hx⟩ : v.adicCompletionIntegers F) = ⟨_, hd⟩ + ⟨_, h1⟩ := Subtype.ext (sub_add_cancel _ _).symm
  simp only [redM, dif_pos hx]
  rw [e, map_add, h0, zero_add]
  by_cases hij : i = j
  · subst hij
    have : (⟨_, h1⟩ : v.adicCompletionIntegers F) = 1 := Subtype.ext (Matrix.one_apply_eq i)
    rw [this, map_one, Matrix.one_apply_eq]
  · have : (⟨_, h1⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (Matrix.one_apply_ne hij)
    rw [this, map_zero, Matrix.one_apply_ne hij]

theorem continuous_phi_prV (G : GLoc F E σ gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal) :
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous ((G.phi a v h).comp (prV (E := E) v)) := by
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := FiniteAdeleRing (𝓞 F) F) _ ?_
  have hv : Continuous (Formalism.UG.evalV F v) := RestrictedProduct.continuous_eval v
  refine hv.congr fun r => ?_
  show _ = (G.sp a v h ((1 : E) ⊗ₜ[F] Formalism.UG.evalV F v r)).1
  rw [G.sp_alg]

theorem isOpen_ker_chi {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp}
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (L : GLevH S G H lam) (hgp : ∀ a, gp a ≠ 0) :
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | ∃ hx : x.1 ∈ S.U, S.chi ⟨x.1, hx⟩ = 1} := by
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
  let K : Subgroup (UPts σ J (FiniteAdeleRing (𝓞 F) F)) := (S.chi.ker.map S.U.subtype).subgroupOf _
  have hK : {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | ∃ hx : x.1 ∈ S.U, S.chi ⟨x.1, hx⟩ = 1} = K := by
    ext x
    constructor
    · rintro ⟨hx, h1⟩
      exact ⟨⟨x.1, hx⟩, h1, rfl⟩
    · rintro ⟨y, hy, e⟩
      have e' : y.1 = x.1 := e
      refine ⟨e' ▸ y.2, ?_⟩
      have : (⟨x.1, e' ▸ y.2⟩ : S.U) = y := Subtype.ext e'.symm
      rw [this]
      exact hy
  rw [hK]
  refine Subgroup.isOpen_of_mem_nhds K (g := 1) ?_
  have hfin : ∀ a, {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal}.Finite := fun a => by
    have h0 : Ideal.span {(gp a : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (hgp a)
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have h1 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, x.1 ∈ S.U := S.U_open.mem_nhds S.U.one_mem
  have h2 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ a : Fin 2, ∀ v ∈ {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal},
      ∀ h : (gp a : 𝓞 F) ∈ v.asIdeal, redM F v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1)) = 1 := by
    refine Filter.eventually_all.2 fun a => (Filter.eventually_all_finite (hfin a)).2 fun v h => ?_
    have hc : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) := by
      have c0 : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => (x.1.val).map ((G.phi a v h).comp (prV (E := E) v)) :=
        (Units.continuous_val.comp continuous_subtype_val).matrix_map (continuous_phi_prV G a v h)
      exact ((continuous_const (y := ((L.fr a v h)⁻¹).val)).matrix_mul c0).matrix_mul (continuous_const (y := (L.fr a v h).val))
    have hone : G.mat a v h (L.fr a v h) (bc (prV (E := E) v) (1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)).1) = 1 := by
      simp [GLoc.mat]
    have h3 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ i j,
        Valued.v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1 := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      have c1 : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) =>
          G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j :=
        (hc.matrix_elem i j).sub continuous_const
      have ho : IsOpen {y : v.adicCompletion F | Valued.v y < 1} := by
        simpa using Valued.isOpen_ball (v.adicCompletion F) 1
      refine (ho.preimage c1).mem_nhds ?_
      rw [Set.mem_preimage, Set.mem_setOf_eq, hone, sub_self, map_zero]
      exact zero_lt_one
    exact h3.mono fun x hx _ => redM_eq_one v _ hx
  filter_upwards [h1, h2] with x hx hr
  refine ⟨⟨x.1, hx⟩, ?_, rfl⟩
  classical
  apply Units.ext
  rw [L.chi_eq, Units.val_one]
  refine Finset.prod_eq_one fun a _ => finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [finprod_eq_dif]
  split_ifs with h
  swap
  · rfl
  have : L.red a v h ⟨x.1, hx⟩ = 1 := Subtype.ext (Units.ext ((L.red_eq a v h ⟨x.1, hx⟩).trans (hr a v h h)))
  rw [this, map_one, Units.val_one, inv_one]

end GlobalTheory.LevelCharOpen
