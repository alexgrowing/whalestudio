import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeUnif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem isDiff_mul (hA : IsAbelianScheme A) (u : HolUnif A L g) {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hv' : IsTangent v') (h : u.IsDiff w v) (h' : u.IsDiff w' v') :
    u.IsDiff (w + w') (v * v') := by
  have := GlobalTheory.isDiff_sum_smul_of_isLieComb A hA L g 2 u ![v, v'] ![w, w'] ![1, 1] (v * v')
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption)
    ⟨![v, v'], fun i => by
      fin_cases i <;> (rw [← GlobalTheory.GrpTangent.epsScale_left]; simp [GlobalTheory.GrpTangent.epsScale_one]),
      by simp [List.ofFn_succ]⟩
  simpa [Fin.sum_univ_two] using this

theorem isDiff_smul (hA : IsAbelianScheme A) (u : HolUnif A L g) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (h : u.IsDiff w v) (r : ℂ) :
    u.IsDiff (r • w) (GlobalTheory.GrpTangent.epsScale r ≫ v) := by
  have := GlobalTheory.isDiff_sum_smul_of_isLieComb A hA L g 1 u ![v] ![w] ![r] (GlobalTheory.GrpTangent.epsScale r ≫ v)
    (fun i => by fin_cases i; assumption) (fun i => by fin_cases i; assumption)
    ⟨![GlobalTheory.GrpTangent.epsScale r ≫ v], fun i => by
      fin_cases i; simp [Over.comp_left, GlobalTheory.GrpTangent.epsScale_left], by simp⟩
  simpa using this

theorem exists_isLieImage_isDiff (hA : IsAbelianScheme A) (u : HolUnif A L g) (P : u.Λ →+ HdR A)
    (hP : ∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) (c : u.Λ →₀ ℂ) :
    ∃ v, IsLieImage (c.sum fun x r ↦ r • P x) v ∧ u.IsDiff (c.sum fun x r ↦ r • (x : Fin g → ℂ)) v := by
  induction c using Finsupp.induction with
  | zero =>
    refine ⟨1, by simpa using isLieImage_one_iff.2 (zero_mem (Fil A)), ?_⟩
    simpa [Hom.one_def] using GlobalTheory.ArchMetricCompare.isDiff_zero u
  | single_add a b f _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    obtain ⟨v₀, hv₀, hd₀⟩ := hP a
    refine ⟨(GlobalTheory.GrpTangent.epsScale b ≫ v₀) * v, ?_, ?_⟩
    · rw [Finsupp.sum_add_index' (h := fun x r ↦ r • P x) (fun _ ↦ zero_smul ℂ _)
        (fun _ _ _ ↦ add_smul _ _ _), Finsupp.sum_single_index (h := fun x r ↦ r • P x) (zero_smul ℂ _)]
      exact (hv₀.smul b).add hv
    · rw [Finsupp.sum_add_index' (h := fun (x : u.Λ) (r : ℂ) ↦ r • (x : Fin g → ℂ)) (fun _ ↦ zero_smul ℂ _)
        (fun _ _ _ ↦ add_smul _ _ _),
        Finsupp.sum_single_index (h := fun (x : u.Λ) (r : ℂ) ↦ r • (x : Fin g → ℂ)) (zero_smul ℂ _)]
      exact isDiff_mul hA u (hv₀.smul b).1 hv.1 (isDiff_smul hA u hv₀.1 hd₀ b) hd

theorem sum_smul_mem_fil_iff :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (P : u.Λ →+ HdR A), LieExact A → (∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) →
    ∀ c : u.Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ Fil A ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0 := by
  intro A _ hA L g u P hE hP c
  obtain ⟨v, hv, hd⟩ := exists_isLieImage_isDiff hA u P hP c
  rw [← isLieImage_one_iff, GlobalTheory.ArchMetricCompare.isDiff_ne_iff u hv.1 hd, ← Hom.one_def]
  exact ⟨fun h ↦ (hE.1 _).unique hv h, fun e ↦ e ▸ hv⟩

end GlobalTheory.HodgeUnif
