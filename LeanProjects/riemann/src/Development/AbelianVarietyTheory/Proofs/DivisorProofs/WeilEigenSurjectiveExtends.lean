import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchSurj

theorem exists_point_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hne : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y : κ → Af F, ∀ v, φ v (fun i => y i v) ≠ 0 := by
  have key : ∀ v : Pl F, ∃ z : κ → Fv F v, φ v z ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, z i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨z, hz⟩ := Function.ne_iff.mp (hne v)
    refine ⟨z, hz, fun h => ?_⟩
    rw [h] at hz
    exact Set.mem_of_indicator_ne_zero hz
  choose z hz hz' using key
  exact ⟨fun i => ⟨fun v => z v i, hstd.mono fun v hv => hz' v hv i⟩, hz⟩

theorem surjective_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.SurjOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Surjective ei := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM hM₁ e hsurj ei ev hev he h
  have h₁ : pure h M₁.vac ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA h M₁.vac (fun v => (hM₁.vac v).1) hM₁.std
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj h₁
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = M.vac v := by
    intro i
    filter_upwards [hM.std, T.eventually_cofinite_notMem] with v hv hT
    rw [hv, hstd i v hT]
  have hid : pure h M₁.vac = ∑ i, pure (ei (f i)) fun v => ev v (φ i v) := by
    rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨y, hy⟩ := exists_point_ne_zero M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  set c : ℂ := ∏ᶠ v, M₁.vac v (fun j => y j v) with hc
  have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
  set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
  refine ⟨∑ i, (cs i / c) • f i, ?_⟩
  refine DFunLike.ext _ _ fun x => ?_
  let a : Fin n × Fin d → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
  have hI : (fun j => evI F (a j)) = x := by
    funext j
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
  have hx : h x * c = ∑ i, ei (f i) x * cs i := by
    have := congrFun hid a
    rw [Finset.sum_apply] at this
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
    exact this
  rw [map_sum]
  have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
    rw [SchwartzMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]; rfl
  rw [hs]
  apply mul_right_cancel₀ hc0
  rw [hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end GlobalTheory.ArchSurj
