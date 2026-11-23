import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def ipLin (R : RiemLat E g Λ) (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' y y' := by simp [RiemLat.ip, add_dotProduct]
  map_smul' c y := by simp [RiemLat.ip, smul_dotProduct]

theorem ip_eq_ipLin (R : RiemLat E g Λ) (x y : Fin g → ℂ) : R.ip x y = ipLin R x y := rfl

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def diagAct (s : Fin g → (𝓞 E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun x k => s k a * x k
      map_add' := fun x y => funext fun k => by simp [mul_add]
      map_smul' := fun r x => funext fun k => by simp [mul_left_comm] }
  map_one' := LinearMap.ext fun x => funext fun k => by simp
  map_mul' a b := LinearMap.ext fun x => funext fun k => by simp [mul_assoc]
  map_zero' := LinearMap.ext fun x => funext fun k => by simp
  map_add' a b := LinearMap.ext fun x => funext fun k => by simp [add_mul]

theorem diagAct_apply (s : Fin g → (𝓞 E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (k : Fin g) :
    diagAct s a x k = s k a * x k := rfl

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (R : RiemLat E g Λ) (e : ι ≃ Fin g) (c : ι → Fin g → ℂ)

include e

theorem sum_ip_smul (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (z : Fin g → ℂ) :
    ∑ i, R.ip (c i) z • c i = z := by
  have hli : LinearIndependent ℂ c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have h := congrArg (ipLin R (c k)) ha
    rw [map_zero, map_sum] at h
    simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul] at h
    simpa using h
  have hspan : Submodule.span ℂ (Set.range c) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [Fintype.card_congr e])
  have hz : z ∈ Submodule.span ℂ (Set.range c) := hspan ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [ip_eq_ipLin, map_sum]
  simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp

theorem sum_ip_mul_conj (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (u v : Fin g → ℂ) :
    ∑ i, R.ip (c i) u * starRingEnd ℂ (R.ip (c i) v) = R.ip v u := by
  conv_rhs => rw [← sum_ip_smul R e c hc u]
  rw [ip_eq_ipLin, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← ip_eq_ipLin, conj_ip, smul_eq_mul]

theorem ip_act (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (s : ι → (𝓞 E →+* ℂ))
    (hs : ∀ i, c i ∈ eigSp R.B (s i)) (a : 𝓞 E) (i : ι) (z : Fin g → ℂ) :
    R.ip (c i) (R.B a z) = s i a * R.ip (c i) z := by
  have hB : ∀ l, R.B a (c l) = s l a • c l := fun l => by
    have h := (Submodule.mem_iInf _).1 (hs l) a
    have h' := LinearMap.mem_ker.1 h
    simpa [sub_eq_zero] using h'
  conv_lhs => rw [← sum_ip_smul R e c hc z]
  rw [map_sum, ip_eq_ipLin, map_sum]
  simp only [map_smul, hB, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp [mul_comm]

end Frame

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' : ℕ}

theorem exists_riemLat_coord (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (c : Ix Ψ j j' → Fin g → ℂ) (hs : ∀ i, c i ∈ eigSp R₀.B (emb σ i))
    (hc : ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) :
    ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k := by
  let P : Λ →+ (Fin g → ℂ) :=
    { toFun := fun x k => R₀.ip (c (e.symm k)) (R₀.P x)
      map_zero' := funext fun k => by simp [ip_eq_ipLin]
      map_add' := fun x y => funext fun k => by simp [ip_eq_ipLin] }
  have hP : ∀ x k, P x k = R₀.ip (c (e.symm k)) (R₀.P x) := fun _ _ => rfl
  refine ⟨{ free := R₀.free, fin := R₀.fin, rank := R₀.rank, form := R₀.form, alt := R₀.alt, unimod := R₀.unimod,
            adj := R₀.adj, P := P, Hm := 1, herm := isHermitian_one, pos := ?_, im := ?_,
            B := diagAct fun k => emb σ (e.symm k), act := ?_ }, rfl, rfl, fun _ _ _ => rfl⟩
  · intro z hz
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
    have hk' : z k ≠ 0 := hk
    have : (z ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star z).re = ∑ l, Complex.normSq (z l) := by
      simp [dotProduct, Complex.mul_conj]
    rw [this]
    exact Finset.sum_pos' (fun l _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ _, Complex.normSq_pos.2 hk'⟩
  · intro x y
    have key : P x ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star (P y) = R₀.P x ⬝ᵥ R₀.Hm *ᵥ star (R₀.P y) := by
      have h := sum_ip_mul_conj R₀ e c hc (R₀.P x) (R₀.P y)
      rw [← e.symm.sum_comp] at h
      rw [one_mulVec]
      exact h
    rw [key]
    exact R₀.im x y
  · intro a x
    funext k
    rw [diagAct_apply, hP, hP, R₀.act]
    exact ip_act R₀ e c hc (emb σ) hs a (e.symm k) (R₀.P x)

theorem coord_lat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) → (∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) → ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k :=
  fun R₀ σ e c hs hc => exists_riemLat_coord R₀ σ e c hs hc

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat
