import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

theorem exists_finset_eval_eq_zero {X K W : Type} [Field K] [AddCommGroup W] [Module K W]
    (V : Submodule K (X → W)) [FiniteDimensional K V] :
    ∃ P : Finset X, ∀ f ∈ V, (∀ x ∈ P, f x = 0) → f = 0 := by
  classical
  let N : Finset X → Submodule K V := fun P =>
    ⨅ x ∈ P, LinearMap.ker ((LinearMap.proj (R := K) (φ := fun _ : X => W) x).comp V.subtype)
  have hN : ∀ P (f : V), f ∈ N P ↔ ∀ x ∈ P, (f : X → W) x = 0 := by
    intro P f; simp [N, Submodule.mem_iInf]
  obtain ⟨_, ⟨P, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min (Set.range N) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨P, fun f hf h0 => ?_⟩
  have key : ∀ x, N P ≤ N (insert x P) := by
    intro x
    have hle : N (insert x P) ≤ N P := fun g hg =>
      (hN _ _).2 fun y hy => (hN _ _).1 hg y (Finset.mem_insert_of_mem hy)
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle fun h => hne h.ge)
  funext x
  exact (hN _ _).1 (key x ((hN P ⟨f, hf⟩).2 h0)) x (Finset.mem_insert_self x P)

section Omega
variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
  [Fintype ι] [DecidableEq ι]

def coordCx (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') : W →ₛₗ[e] W' where
  toFun w := b'.equivFun.symm fun i => e (b.equivFun w i)
  map_add' x y := b'.equivFun.injective (by
    simp only [map_add, LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.add_apply, map_add])
  map_smul' a x := b'.equivFun.injective (by
    simp only [map_smul, LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply])

theorem coordCx_coord (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') (w : W) (i : ι) :
    b'.equivFun (coordCx e b b' w) i = e (b.equivFun w i) := by
  simp only [coordCx, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]

end Omega

theorem finrank_typeSp_cx : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (W W' : Type) [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') (J : Subgroup (GAf L n)) (χ : J →* Kˣ), WtMatch e ρ ρ' → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional K (NX.TypeSpF L n K ρ J χ) → Module.finrank ℂ (NG.TypeSp ρ' J (cx e χ)) = Module.finrank K (NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ e W W' _ _ _ _ ρ ρ' J χ hW hN hfin
  classical
  obtain ⟨ι, _, _, b, b', hM⟩ := hW
  letI : Algebra K ℂ := e.toAlgebra
  let β := Module.Basis.ofVectorSpace K ℂ
  let ω := coordCx e b b'
  have hωc : ∀ w i, b'.equivFun (ω w) i = e (b.equivFun w i) := fun w i => coordCx_coord e b b' w i
  have hρ : ∀ γ w i, b.equivFun (ρ γ w) i = ∑ k, LinearMap.toMatrix b b (ρ γ) i k * b.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b b (ρ γ) w) i
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hρ' : ∀ γ w i, b'.equivFun (ρ' γ w) i = ∑ k, e (LinearMap.toMatrix b b (ρ γ) i k) * b'.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b' b' (ρ' γ) w) i
    rw [hM γ] at this
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hωρ : ∀ γ w, ω (ρ γ w) = ρ' γ (ω w) := fun γ w =>
    b'.equivFun.injective (funext fun i => by rw [hωc, hρ, hρ', map_sum]; simp only [map_mul, hωc])
  have hβ1 : ∀ (y : K) (z : ℂ) α, β.repr (e y * z) α = y * β.repr z α := by
    intro y z α
    rw [show e y * z = y • z from rfl, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let V := NX.TypeSpF L n K ρ J χ
  let v := Module.finBasis K V
  have hωV : ∀ f ∈ V, (fun g => ω (f g)) ∈ NG.TypeSp ρ' J (cx e χ) := by
    rintro f ⟨h1, h2⟩
    obtain ⟨N, hN0, hNc⟩ := hN
    refine ⟨⟨fun γ g => by simp only [h1, hωρ], N, hN0, fun κ hκ g => ?_⟩, fun κ => ?_⟩
    · obtain ⟨h, h1'⟩ := hNc κ hκ
      show ω (f (g * κ)) = ω (f g)
      have := h2 ⟨κ, h⟩ g
      rw [this, h1', Units.val_one, one_smul]
    · funext g
      show ω (f (g * κ)) = ((cx e χ κ : ℂˣ) : ℂ) • ω (f g)
      rw [h2, map_smulₛₗ, cx_apply]

  have hlinK : LinearIndependent K (fun j => ((v j : V) : GAf L n → W)) :=
    v.linearIndependent.map' V.subtype V.ker_subtype
  have hli : LinearIndependent ℂ (fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    rw [Fintype.linearIndependent_iff] at hlinK ⊢
    intro c hc j
    have hcoord : ∀ g i, ∑ j, c j * e (b.equivFun (((v j : V) : GAf L n → W) g) i) = 0 := by
      intro g i
      have := congrArg (fun F => b'.equivFun (F g) i) hc
      simpa only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, hωc,
        Pi.zero_apply, map_zero] using this
    have hα : ∀ α, ∀ j, β.repr (c j) α = 0 := by
      intro α
      apply hlinK
      funext g
      apply b.equivFun.injective
      funext i
      have := congrArg (fun z => β.repr z α) (hcoord g i)
      simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, mul_comm (c _), hβ1, map_zero,
        Finsupp.coe_zero, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, map_zero, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact β.repr.injective (by ext α; simp [hα α j])

  have hspanV : ∀ a : Fin (Module.finrank K V) → K,
      (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) ∈
        Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    intro a
    have : (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) =
        ∑ j, e (a j) • fun g => ω (((v j : V) : GAf L n → W) g) := by
      funext g
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hspan : NG.TypeSp ρ' J (cx e χ) = Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    refine le_antisymm ?_ (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hωV _ (v j).2))
    rintro F ⟨⟨hF1, -⟩, hF2⟩
    have hFk : ∀ (κ : J) g, F (g * κ) = e (χ κ) • F g := fun κ g => congrFun (hF2 κ) g
    let fa : _ → GAf L n → W := fun α g => b.equivFun.symm fun i => β.repr (b'.equivFun (F g) i) α
    have hfa : ∀ α g i, b.equivFun (fa α g) i = β.repr (b'.equivFun (F g) i) α := by
      intro α g i; simp only [fa, LinearEquiv.apply_symm_apply]
    have hfaV : ∀ α, fa α ∈ V := by
      intro α
      refine ⟨fun γ g => b.equivFun.injective (funext fun i => ?_), fun κ g => b.equivFun.injective (funext fun i => ?_)⟩
      · rw [hfa, hF1, hρ', hρ, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
        simp only [hβ1, hfa]
      · rw [hfa, hFk, map_smul, Pi.smul_apply, smul_eq_mul, hβ1, map_smul, Pi.smul_apply, smul_eq_mul, hfa]
    obtain ⟨P, hP⟩ := exists_finset_eval_eq_zero V
    let S := P.biUnion fun g => Finset.univ.biUnion fun i => (β.repr (b'.equivFun (F g) i)).support
    have hzero : ∀ α ∉ S, fa α = 0 := by
      intro α hα
      refine hP _ (hfaV α) fun g hg => b.equivFun.injective (funext fun i => ?_)
      rw [hfa, map_zero, Pi.zero_apply]
      by_contra h
      exact hα (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 h⟩⟩)
    have hsub : ∀ g i, (β.repr (b'.equivFun (F g) i)).support ⊆ S := by
      intro g i α hα
      by_contra hS
      have := congrArg (fun f => b.equivFun (f g) i) (hzero α hS)
      simp only [hfa, Pi.zero_apply, map_zero] at this
      exact (Finsupp.mem_support_iff.1 hα) this
    have hFeq : F = ∑ α ∈ S, β α • fun g => ω (fa α g) := by
      funext g
      apply b'.equivFun.injective
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, hωc, hfa]
      conv_lhs => rw [← β.linearCombination_repr (b'.equivFun (F g) i)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hsub g i) (fun a c => c • β a) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun α _ => mul_comm _ _
    rw [hFeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    have hrep := congrArg Subtype.val (v.sum_repr ⟨fa α, hfaV α⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    rw [← hrep]
    exact hspanV _
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.LevCmp

end
