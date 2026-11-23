import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rT_adj (r : ℝ) (x : GL (Fin a) (Af E)) (X : Lie E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smAdj Ξ r X m) = smAdj Ξ r X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
  have h : lie E a X * act (.fin x) = act (.fin x) * lie E a X := lie_rt_fin X x
  have h1 : (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smA Ξ X m) = smA Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
    rw [smA_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, h]
  have h2 : (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smB Ξ X m) = smB Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
    rw [smB_apply]
    clear h1
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul φ v => simp
  rw [smAdj, adj_apply, adj_apply, map_sub, map_sub, h1, h2, LinearMap.map_smul_of_tower]

variable {π : CuspSub E a} {r : ℝ} {n : ℕ} {e : Fin n → GlobalTheory.GKCoh.Herm E a}

private theorem cocl_comb {q : ℕ} (s : ℂ) {ω η : Geo.Co Ξ q} (hω : Coclosed (smAdj Ξ r) e ω)
    (hη : Coclosed (smAdj Ξ r) e η) : Coclosed (smAdj Ξ r) e (s • ω + η) := by
  have ap : ∀ X, (s • ω + η) X = s • ω X + η X := fun X => rfl
  cases q with
  | zero => trivial
  | succ q =>
    refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω) X
    have h2 := DFunLike.congr_fun (show del _ e η = 0 from hη) X
    rw [del_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
    simp only [ap, map_add, map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]

private theorem cocl_zero {q : ℕ} : Coclosed (smAdj Ξ r) e (0 : Geo.Co Ξ q) := by
  cases q with
  | zero => trivial
  | succ q => exact AlternatingMap.ext fun X => by simp [del_apply]

private theorem cocl_trans {q : ℕ} (x : GL (Fin a) (Af E)) {ω : Geo.Co Ξ q} (hω : Coclosed (smAdj Ξ r) e ω) :
    Coclosed (smAdj Ξ r) e (Geo.trans x ω) := by
  have ap : ∀ X, Geo.trans x ω X = (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (ω X) := fun X => rfl
  cases q with
  | zero => trivial
  | succ q =>
    refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω) X
    rw [del_apply, AlternatingMap.zero_apply] at h1 ⊢
    simp only [ap, ← rT_adj, ← map_sum, h1, map_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.harmSub :
    UpperTheory.V.Cj.HarmSub := by
  intro E _ _ _ a π Ξ r n e q
  obtain ⟨L, L1, L2⟩ := (levSub E a Ξ q).2.2
  have comb : ∀ (s : ℂ) (α β : Geo.Co Ξ q), IsPiHarm π Ξ r e α → IsPiHarm π Ξ r e β → IsPiHarm π Ξ r e (s • α + β) :=
    fun s α β hα hβ => ⟨(L1 _).1 (L.add_mem (L.smul_mem s ((L1 _).2 hα.1)) ((L1 _).2 hβ.1)),
      by rw [dCo_comb, hα.2.1, hβ.2.1, smul_zero, add_zero], cocl_comb s hα.2.2.1 hβ.2.2.1,
      fun X => Submodule.add_mem _ (Submodule.smul_mem _ s (hα.2.2.2 X)) (hβ.2.2.2 X)⟩
  have zero : IsPiHarm π Ξ r e (0 : Geo.Co Ξ q) :=
    ⟨(L1 _).1 L.zero_mem, AlternatingMap.ext fun X => by simp [dCo_apply], cocl_zero, fun X => Submodule.zero_mem _⟩
  refine ⟨{ carrier := {ω | IsPiHarm π Ξ r e ω}, add_mem' := ?_, zero_mem' := zero, smul_mem' := ?_ },
    fun ω => Iff.rfl, ?_⟩
  · intro α β hα hβ
    have := comb 1 α β hα hβ
    rwa [one_smul] at this
  · intro s α hα
    have := comb s α 0 hα zero
    rwa [add_zero] at this
  · rintro x ω ⟨h1, h2, h3, h4⟩
    refine ⟨(L1 _).1 (L2 x ω ((L1 _).2 h1)), ?_, cocl_trans x h3, fun X => mem_tens.2 fun i => ?_⟩
    · obtain ⟨U, -, -, u3⟩ := h1
      rw [(perNat E a U ⊥ x (fun u hu => by rw [Subgroup.mem_bot.1 hu]; simp) Ξ q ω u3).2.1, h2,
        ← transRep_apply, map_zero]
    · rw [cmp_trans]
      exact π.stable (.fin x) _ (mem_tens.1 (h4 X) i)
