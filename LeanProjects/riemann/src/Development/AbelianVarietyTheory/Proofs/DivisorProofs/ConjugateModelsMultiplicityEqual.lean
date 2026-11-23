import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

def conjMap (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) : MMap M' where
  toFun v' := star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩)
  map_update_add' v' i x y := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e, e, ← star_add, ← T.map_update_add]
    congr 3
    ext; simp
  map_update_smul' v' i a x := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e]
    have e2 : (⟨c i ((a • x : M'.sm i) : M'.H i), (h i _).1 (a • x).2⟩ : M.sm i) = star a • ⟨c i x, (h i _).1 x.2⟩ := by
      ext; exact (c i).map_smulₛₗ a x
    rw [e2, T.map_update_smul, star_smul, star_star]

theorem conjMap_apply (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (v' : M'.Vec) :
    conjMap M M' c h T v' = star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) := rfl

theorem conjMap_eq_zero (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (hT : conjMap M M' c h T = 0) : T = 0 := by
  refine MultilinearMap.ext fun v => ?_
  have h1 := congrArg (fun U : MMap M' => U fun τ => ⟨(c τ).symm (v τ), (h τ _).2 (by simpa using (v τ).2)⟩) hT
  simp only [conjMap_apply, LinearIsometryEquiv.apply_symm_apply, Subtype.coe_eta, MultilinearMap.zero_apply,
    star_eq_zero] at h1
  exact h1

theorem mult_congr (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {J : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = χ k) {T : MMap M} (hT : T ∈ Mult θ M J χ) : T ∈ Mult θ M J χ' := by
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k hk g, hT.equiv, hT.cont⟩

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type}
    (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg Sg' : Pl0 → ℂ[X])
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ))
    (hS : ∀ P k, (Sg' P).coeff k = star ((Sg P).coeff k)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
  obtain ⟨h, hM⟩ := GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · simp only [hPart, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at h3 ⊢
      intro P hP k hk α hα R hR
      have h4 := sub_eq_zero.1 (h3 P hP k hk α hα R hR)
      refine sub_eq_zero.2 (MultilinearMap.ext fun v' => funext fun g => ?_)
      have h5 : ∑ γ ∈ R, T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ) =
          ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g :=
        congrArg (fun U : MMap M => U (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g) h4
      show ∑ γ ∈ R, star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ)) =
          ((Sg' P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g)
      rw [← star_sum, h5, hS]
      simp
  let j : (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q (fun P => (Sg P).map (starRingEnd ℂ)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J χ χ' e e' J0 Pl0 ok pl q Sg hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' J0 ok pl q Sg _ hχ he fun P k => by simp) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e J0 ok pl q _ Sg ?_ ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P k
    simp

end GlobalTheory.ConjDim

end
