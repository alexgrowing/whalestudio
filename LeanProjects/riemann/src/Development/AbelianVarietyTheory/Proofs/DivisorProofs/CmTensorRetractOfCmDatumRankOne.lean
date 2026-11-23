import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem smul_comm_of_finrank_one (D : Datum H) (h : Module.finrank (𝓞 E) D.La = 1)
    (l : D.La →ₗ[𝓞 E] 𝓞 E) (x y : D.La) : l x • y = l y • x := by
  have := D.fin
  have := D.proj
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul h hx y
  have hl : r * l y = s * l x := by rw [← smul_eq_mul, ← map_smul, e, map_smul, smul_eq_mul]
  have h0 : r • (l x • y - l y • x) = 0 := by
    rw [smul_sub, smul_comm r (l x) y, e, smul_smul, smul_smul, hl, mul_comm, sub_self]
  rw [smul_eq_zero] at h0
  exact sub_eq_zero.1 (h0.resolve_left hr)

theorem exists_dualBasis (D : Datum H) :
    ∃ (n : ℕ) (a : Fin n → D.La) (l : Fin n → (D.La →ₗ[𝓞 E] 𝓞 E)), ∀ x, ∑ k, l k x • a k = x := by
  have := D.fin
  have := D.proj
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) D.La
  refine ⟨n, fun k => f (fun j => if k = j then 1 else 0), fun k => LinearMap.proj k ∘ₗ g, fun x => ?_⟩
  have hx : f (g x) = x := LinearMap.congr_fun hfg x
  conv_rhs => rw [← hx, LinearMap.pi_apply_eq_sum_univ f (g x)]
  rfl

theorem exists_sum_comp_eq_id (DA DB : Datum H) (hA : DA.p + DA.q = 1) :
    ∃ (n : ℕ) (α : Fin n → (DA.La →ₗ[𝓞 E] DB.La)) (β : Fin n → (DB.La →ₗ[𝓞 E] DA.La)),
      ∑ i, α i ∘ₗ β i = LinearMap.id := by
  have := DA.fin
  have := DA.proj
  have hr : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hA]
  obtain ⟨n, a, l, decA⟩ := exists_dualBasis DA
  obtain ⟨m, b, mu, decB⟩ := exists_dualBasis DB
  have tr : ∑ k, l k (a k) = 1 := by
    have : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
    obtain ⟨x, hx⟩ := exists_ne (0 : DA.La)
    have e : (∑ k, l k (a k)) • x = (1 : 𝓞 E) • x := by
      rw [Finset.sum_smul, one_smul]
      conv_rhs => rw [← decA x]
      exact Finset.sum_congr rfl fun k _ => smul_comm_of_finrank_one DA hr (l k) (a k) x
    have h0 : ((∑ k, l k (a k)) - 1) • x = 0 := by rw [sub_smul, e, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx)
  refine ⟨n * m, fun i => (l (finProdFinEquiv.symm i).1).smulRight (b (finProdFinEquiv.symm i).2),
    fun i => (mu (finProdFinEquiv.symm i).2).smulRight (a (finProdFinEquiv.symm i).1), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  rw [finProdFinEquiv.symm.sum_comp (fun p : Fin n × Fin m =>
    ((l p.1).smulRight (b p.2) ∘ₗ (mu p.2).smulRight (a p.1)) y), Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [← decB y]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul, smul_smul]
  rw [← Finset.sum_smul, ← Finset.mul_sum, tr, _root_.mul_one]

end GlobalTheory.CM
end

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {ω : R}
  {C : Ell H R ω}

theorem IsTen.isLinearHom_mapLeft {A B : PAT H (Sp R)} {DA DB : Datum H} {hA : DA.La → DA.La → OK H}
    {hB : DB.La → DB.La → OK H} (tA : IsTen C DA hA A) (tB : IsTen C DB hB B) (φ : DA.La →ₗ[𝓞 E] DB.La) :
    Serre.IsLinearHom A.t.act B.t.act (tA.ten.mapLeft tB.ten (φ.restrictScalars (OK H))) := by
  refine ⟨inferInstance, fun s => ?_⟩
  have := A.t.act.hom s
  have := B.t.act.hom s
  refine tA.ten.hom_ext fun m => ?_
  rw [← Category.assoc, ← tA.lin, Serre.IsTensor.tmul_mapLeft, ← Category.assoc, Serre.IsTensor.tmul_mapLeft,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, map_smul, tB.lin]

theorem IsTen.prod_mapLeft {B : PAT H (Sp R)} {DB : Datum H} {hB : DB.La → DB.La → OK H}
    (tB : IsTen C DB hB B) {I : Type} (s : Finset I) (φ : I → (DB.La →ₗ[𝓞 E] DB.La)) :
    ∏ i ∈ s, tB.ten.mapLeft tB.ten ((φ i).restrictScalars (OK H)) =
      tB.ten.mapLeft tB.ten ((∑ i ∈ s, φ i).restrictScalars (OK H)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, LinearMap.restrictScalars_zero, Serre.IsTensor.mapLeft_zero]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, LinearMap.restrictScalars_add, Serre.IsTensor.mapLeft_add]

theorem isTen_retract_of_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (A B : PAT H (Sp R)) (DA DB : Datum H)
    (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H), DA.p + DA.q = 1 → IsTen C DA hA A → IsTen C DB hB B →
    ∃ (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G)) (g : Fin n → (B.t.G ⟶ A.t.G)),
      (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) ∧ (∀ i, Serre.IsLinearHom B.t.act A.t.act (g i)) ∧
      ∏ i, (g i ≫ f i) = 𝟙 B.t.G := by
  intro E _ _ _ H R _ ω C A B DA DB hA hB h tA tB
  obtain ⟨n, α, β, hαβ⟩ := exists_sum_comp_eq_id DA DB h
  refine ⟨n, fun i => tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H)),
    fun i => tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)),
    fun i => tA.isLinearHom_mapLeft tB (α i), fun i => tB.isLinearHom_mapLeft tA (β i), ?_⟩
  have e : ∀ i, tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)) ≫ tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H))
      = tB.ten.mapLeft tB.ten ((α i ∘ₗ β i).restrictScalars (OK H)) := fun i =>
    (Serre.IsTensor.mapLeft_comp _ _ _ _ _).symm
  simp only [e]
  rw [tB.prod_mapLeft, hαβ]
  exact Serre.IsTensor.mapLeft_id _

end GlobalTheory.CM
end
