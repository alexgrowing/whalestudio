import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinearMapOfGram

open Matrix GlobalTheory.JointHarm
open scoped Classical

namespace GlobalTheory.JointHarm.OrbitMap

variable {ι : Type} {n : ℕ}

theorem one_mem_K (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by simp⟩

theorem one_mem_KC (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ GlobalTheory.Dec.KC ε :=
  ⟨isUnit_one, by simp⟩

theorem K_sub_KC {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ GlobalTheory.Dec.KC ε :=
  ⟨⟨Unitary.toUnits ⟨g, hg.1⟩, rfl⟩, hg.2⟩

theorem mul_mem_K {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε)
    (hh : h ∈ Formalism.REAL.Kset ε) : g * h ∈ Formalism.REAL.Kset ε :=
  ⟨mul_mem hg.1 hh.1, by rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]⟩

theorem star_mem_K {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    gᴴ ∈ Formalism.REAL.Kset ε := by
  have h1 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
  have h2 : g * gᴴ = 1 := Unitary.mul_star_self_of_mem hg.1
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  calc gᴴ * Formalism.REAL.Jm ε = gᴴ * (Formalism.REAL.Jm ε * g) * gᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
    _ = Formalism.REAL.Jm ε * gᴴ := by
        rw [← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem single_mem_KC {ε : ι → Fin n → Bool} {τ : ι} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.Dec.KC (ε τ)) (σ : ι) :
    (Pi.mulSingle τ g : ι → Matrix (Fin n) (Fin n) ℂ) σ ∈ GlobalTheory.Dec.KC (ε σ) := by
  by_cases h : σ = τ
  · subst h; simpa using hg
  · simpa [h] using one_mem_KC _

theorem single_comm {τ : ι} (g : Matrix (Fin n) (Fin n) ℂ) {v : ι → Matrix (Fin n) (Fin n) ℂ}
    (hv : v τ = 1) : Pi.mulSingle τ g * v = v * Pi.mulSingle τ g := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [hv]
  · simp [h]

theorem fam_induction [Fintype ι] {ε : ι → Fin n → Bool} (Q : (ι → Matrix (Fin n) (Fin n) ℂ) → Prop)
    (h1 : Q 1)
    (hs : ∀ τ k v, k ∈ Formalism.REAL.Kset (ε τ) → (∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) → v τ = 1 → Q v →
      Q (Pi.mulSingle τ k * v)) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) : Q u := by
  have key : ∀ s : Finset ι, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ,
      (∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) → (∀ σ ∉ s, u σ = 1) → Q u := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro u _ h
      have : u = 1 := funext fun σ => h σ (by simp)
      rw [this]; exact h1
    | insert τ s _ ih =>
      intro u hu h
      have hv : ∀ σ, Function.update u τ 1 σ ∈ Formalism.REAL.Kset (ε σ) := by
        intro σ
        by_cases e : σ = τ
        · subst e; simpa using one_mem_K _
        · simpa [e] using hu σ
      have e : u = Pi.mulSingle τ (u τ) * Function.update u τ 1 := by
        funext σ
        by_cases e : σ = τ
        · subst e; simp
        · simp [e]
      rw [e]
      refine hs τ _ _ (hu τ) hv (by simp) (ih _ hv fun σ hσ => ?_)
      by_cases e : σ = τ
      · subst e; simp
      · simpa [e] using h σ (by simp [e, hσ])
  exact key Finset.univ u hu (by simp)

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P} {ε : ι → Fin n → Bool} {μ : ι → Fin n → ℝ}

theorem adj_fam [Fintype ι] (h : IsHolFam ε B ϖ) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) :
    ∀ a b, B (ϖ u a) b = B a (ϖ (fun σ => (u σ)ᴴ) b) := by
  refine fam_induction (ε := ε) (fun u => ∀ a b, B (ϖ u a) b = B a (ϖ (fun σ => (u σ)ᴴ) b)) ?_ ?_ u hu
  · intro a b
    have : (fun σ => ((1 : ι → Matrix (Fin n) (Fin n) ℂ) σ)ᴴ) = 1 := by funext σ; simp
    rw [this, h.2.1]; rfl
  · intro τ k v hk hv _ ih a b
    have e : (fun σ => ((Pi.mulSingle τ k * v : ι → Matrix (Fin n) (Fin n) ℂ) σ)ᴴ) =
        (fun σ => (v σ)ᴴ) * Pi.mulSingle τ kᴴ := by
      funext σ
      by_cases e : σ = τ
      · subst e; simp
      · simp [e]
    rw [e, h.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      h.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hv σ))) (single_mem_KC (K_sub_KC (star_mem_K hk))),
      Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact (h.2.2.2 τ).2.2.2.1 k (K_sub_KC hk) _ _

theorem bottom_move (h : IsHolFam ε B ϖ) {x : P} (hx : IsBotFam ε ϖ μ x) {τ : ι}
    {v : ι → Matrix (Fin n) (Fin n) ℂ} (hv : ∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) (hτ : v τ = 1) :
    IsBottom (ε τ) (fun g => ϖ (Pi.mulSingle τ g)) (μ τ) (ϖ v x) := by
  have c : ∀ g ∈ GlobalTheory.Dec.KC (ε τ), ϖ (Pi.mulSingle τ g) (ϖ v x) = ϖ v (ϖ (Pi.mulSingle τ g) x) := by
    intro g hg
    rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      ← h.2.2.1 _ _ (single_mem_KC hg) (fun σ => K_sub_KC (hv σ)),
      ← h.2.2.1 _ _ (fun σ => K_sub_KC (hv σ)) (single_mem_KC hg), single_comm g hτ]
  refine ⟨fun g hg hl => ?_, fun θ => ?_⟩
  · show ϖ (Pi.mulSingle τ g) (ϖ v x) = _
    rw [c g hg]
    exact congrArg _ ((hx τ).1 g hg hl)
  · show ϖ (Pi.mulSingle τ _) (ϖ v x) = _
    rw [c, ← map_smul]
    · exact congrArg _ ((hx τ).2 θ)
    · refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.exp_ne_zero _

variable {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ}
  {ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P'}

theorem coef_fam [Fintype ι] (h : IsHolFam ε B ϖ) (h' : IsHolFam ε B' ϖ') {x : P} {x' : P'}
    (hx : IsBotFam ε ϖ μ x) (hx' : IsBotFam ε ϖ' μ x') (h0 : x' ≠ 0)
    (u : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) :
    B x (ϖ u x) * B' x' x' = B x x * B' x' (ϖ' u x') := by
  have hc : B' x' x' ≠ 0 := fun e => h0 (h'.1 _ e)
  refine fam_induction (ε := ε) (fun u => B x (ϖ u x) * B' x' x' = B x x * B' x' (ϖ' u x')) ?_ ?_ u hu
  · show B x (ϖ 1 x) * B' x' x' = B x x * B' x' (ϖ' 1 x')
    rw [h.2.1, h'.2.1]; rfl
  · intro τ k v hk hv hτ ih
    have e1 := GlobalTheory.JointHarm.Sph.coeff_eq n (ε τ) (μ τ) P B _ P' B' _ x (ϖ v x) x' x' (h.2.2.2 τ) (h'.2.2.2 τ)
      (hx τ) (bottom_move h hx hv hτ) (hx' τ) (hx' τ) k hk
    have e2 := GlobalTheory.JointHarm.Sph.coeff_eq n (ε τ) (μ τ) P' B' _ P' B' _ x' (ϖ' v x') x' x' (h'.2.2.2 τ) (h'.2.2.2 τ)
      (hx' τ) (bottom_move h' hx' hv hτ) (hx' τ) (hx' τ) k hk
    show B x (ϖ (Pi.mulSingle τ k * v) x) * B' x' x' = B x x * B' x' (ϖ' (Pi.mulSingle τ k * v) x')
    rw [h.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      h'.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      Module.End.mul_apply, Module.End.mul_apply]
    apply mul_right_cancel₀ hc
    linear_combination (B' x' x') * e1 - (B x x) * e2 + (B' x' (ϖ' (Pi.mulSingle τ k) x')) * ih

theorem gram_fam [Fintype ι] (h : IsHolFam ε B ϖ) (h' : IsHolFam ε B' ϖ') {x : P} {x' : P'}
    (hx : IsBotFam ε ϖ μ x) (hx' : IsBotFam ε ϖ' μ x') (h0 : x' ≠ 0)
    (u v : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ))
    (hv : ∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) :
    B (ϖ u x) (ϖ v x) * B' x' x' = B x x * B' (ϖ' u x') (ϖ' v x') := by
  rw [adj_fam h u hu, adj_fam h' u hu, ← Module.End.mul_apply, ← Module.End.mul_apply,
    ← h.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hu σ))) (fun σ => K_sub_KC (hv σ)),
    ← h'.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hu σ))) (fun σ => K_sub_KC (hv σ))]
  exact coef_fam h h' hx hx' h0 _ fun σ => mul_mem_K (star_mem_K (hu σ)) (hv σ)

theorem exists_map_of_gram {U : Type} (f : U → P) (f' : U → P') (hB : ∀ y, B y y = 0 → y = 0)
    {c d : ℂ} (hc : c ≠ 0) (hg : ∀ u v, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u, ψ (f' u) = f u := by
  first
  | exact @_root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram
  | exact _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram
  | (apply _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> assumption)
  | (intros; apply _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram ..)

theorem exists_orbit_map : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (μ : ι → Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P') (x : P) (x' : P'), IsHolFam ε B ϖ → IsHolFam ε B' ϖ' → IsBotFam ε ϖ μ x → IsBotFam ε ϖ' μ x' → x' ≠ 0 → ∃ ψ : P' →ₗ[ℂ] P, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)) → ψ (ϖ' u x') = ϖ u x := by
  intro ι _ n ε μ P _ _ B ϖ P' _ _ B' ϖ' x x' h h' hx hx' h0
  obtain ⟨ψ, hψ⟩ := exists_map_of_gram (B := B) (B' := B')
    (U := {u : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)})
    (fun u => ϖ u.1 x) (fun u => ϖ' u.1 x') h.1 (fun e => h0 (h'.1 _ e))
    (fun u v => gram_fam h h' hx hx' h0 u.1 v.1 u.2 v.2)
  exact ⟨ψ, fun u hu => hψ ⟨u, hu⟩⟩

end GlobalTheory.JointHarm.OrbitMap
