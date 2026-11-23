import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Adapt

namespace GlobalTheory.ThK.AdaptVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {κ₀ : Type} [Fintype κ₀]
  (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n₁ × Fin d₁)

theorem isVac_box {B : Base F E} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (Ma : Model σ X W) (M₁ : Model σ X₁ W₁)
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      Ma.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (p q : Matrix (Fin n) (Fin d) (AE F E) → κ₀ → AF F) (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hco : ∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)) (v : Pl F)
    (hlat : ∀ γ ∈ latAtV X W v, π γ ∈ latAtV X₁ W₁ v)
    (hpq : ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, B.ψ (p γ' ⬝ᵥ q γ) = 1)
    (hθ : ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * (p γ ⬝ᵥ q γ)) *
          B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W₁.J) (π γ) (π γ)))
    {φ : (Fin n₁ × Fin d₁ → Fv F v) → ℂ} (hφ : M₁.IsVac B.ψ v φ) (Λ₀ : Set (κ₀ → Fv F v))
    (hΛ₀ : ∀ a, a ∈ Λ₀ ↔ ∃ γ ∈ latAtV X W v, (fun k => evFin F v (p γ k)) = a) :
    Ma.IsVac B.ψ v (box ε Λ₀ φ) := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LatOpenCpt.main σ B X W r s r' s' hX hW Ma hrat v
  set K := (latAtV X W v).map (GlobalTheory.LatVac.locCo Ma.co v) with hK
  let pr : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) →+ (κ₀ → Fv F v) :=
    { toFun := fun w k => w.1 (ε.symm (.inl k)), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hΛc : IsCompact (K.map pr : Set (κ₀ → Fv F v)) :=
    hKc.image (show Continuous fun (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) k => w.1 (ε.symm (.inl k)) by
      fun_prop)
  have hΛo : IsOpen (K.map pr : Set (κ₀ → Fv F v)) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hc : Continuous fun a : κ₀ → Fv F v => ((glue ε a 0, 0) : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :=
      (continuous_glue ε continuous_id continuous_const).prodMk continuous_const
    refine Filter.mem_of_superset ((hKo.preimage hc).mem_nhds ?_) fun a ha => ⟨_, ha, funext fun k => glue_inl ε a 0 k⟩
    show (glue ε 0 0, 0) ∈ K
    rw [glue_zero]
    exact K.zero_mem
  have hmem : ∀ a, a ∈ K.map pr ↔ ∃ γ ∈ latAtV X W v, (fun k => evFin F v (p γ k)) = a := fun a => by
    have : ∀ γ, pr (GlobalTheory.LatVac.locCo Ma.co v γ) = fun k => evFin F v (p γ k) := fun γ => funext fun k => by
      show evFin F v ((Ma.co.e γ).1 _) = _
      simp only [hco, glue_inl]
    simp only [hK, AddSubgroup.map_map, AddSubgroup.mem_map, AddMonoidHom.comp_apply, this]
  have hΛe : Λ₀ = ((K.map pr : AddSubgroup (κ₀ → Fv F v)) : Set (κ₀ → Fv F v)) := by
    ext a
    rw [hΛ₀, SetLike.mem_coe, hmem]
  subst hΛe
  set Λ := K.map pr
  have h0 : ∀ b, box ε (Λ : Set _) φ (glue ε 0 b) = φ b := fun b => by
    rw [box_glue, Set.indicator_of_mem Λ.zero_mem, Pi.one_apply, one_mul]
  obtain ⟨hSB, hne, θ, hθ1, hA⟩ := hφ
  refine ⟨box_mem_SB ε hΛo hΛc hSB, fun h => hne (funext fun b => by rw [← h0, h]; rfl), θ, hθ1,
    fun γ hγ R hR => ?_⟩
  have hat : ∀ u, evFin F v u = 0 → u • p γ = 0 ∧ u • q γ = 0 := fun u hu => by
    have h1 := congrArg Ma.co.e ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ u hu)
    rw [map_smul, map_zero, hco] at h1
    exact ⟨funext fun k => by simpa using congrFun (congrArg Prod.fst h1) (ε.symm (.inl k)),
      funext fun k => by simpa using congrFun (congrArg Prod.snd h1) (ε.symm (.inl k))⟩
  funext x
  obtain ⟨a, b, rfl⟩ := exists_glue ε x
  have hp : (fun k => evFin F v (p γ k)) ∈ Λ := (hmem _).2 ⟨γ, hγ, rfl⟩
  simp only [Darboux.rho, schr, tens, hco, glue_dot, glue_add, glue_map ε (evFin F v), Pi.smul_apply, box_glue]
  by_cases ha : (fun k => evFin F v (a k)) ∈ Λ
  · have ha' : (fun k => evFin F v ((a + p γ) k)) ∈ Λ := by
      simp only [Pi.add_apply, map_add]
      exact Λ.add_mem ha hp
    have hR₁ : Rest (evFin F v) φ fun b => R (glue ε a b) := by
      refine ⟨fun x z hz => ?_, ?_⟩
      · have := hR.1 (glue ε a x) (glue ε 0 z) fun u hu => by rw [glue_smul, hz u hu, smul_zero, glue_zero]
        rwa [glue_add, add_zero] at this
      · have := slice_mem_schA ε a hR.2
        simp only [tens, glue_map ε (evFin F v), box_glue, Set.indicator_of_mem ha, Pi.one_apply, one_mul] at this
        exact this
    have key := congrFun (hA (π γ) (hlat γ hγ) _ hR₁) b
    simp only [Darboux.rho, schr, tens, Pi.smul_apply] at key
    have hs : ∀ c, R (glue ε (a + p γ) c) = R (glue ε a c) := fun c => by
      have := hR.1 (glue ε a c) (glue ε (p γ) 0) fun u hu => by rw [glue_smul, (hat u hu).1, smul_zero, glue_zero]
      rwa [glue_add, add_zero] at this
    have h1 : B.ψ (a ⬝ᵥ q γ) = 1 := by
      obtain ⟨γ', hγ', e⟩ := (hmem _).1 ha
      rw [← hpq γ hγ γ' hγ']
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have := congrFun (hat (a k - p γ' k) (by rw [map_sub, sub_eq_zero]; exact (congrFun e k).symm)).2 k
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      linear_combination this
    rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha', hs, hθ θ hθ1 γ hγ, mul_add, add_add_add_comm,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul B.ψ (a ⬝ᵥ q γ), h1]
    simp only [Pi.one_apply, one_mul, smul_eq_mul] at key ⊢
    rw [mul_assoc, key]
    ring
  · have ha' : (fun k => evFin F v ((a + p γ) k)) ∉ Λ := fun h => ha (by
      have := Λ.sub_mem h hp
      convert this using 1
      funext k
      simp)
    rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha']
    simp

end GlobalTheory.ThK.AdaptVac
