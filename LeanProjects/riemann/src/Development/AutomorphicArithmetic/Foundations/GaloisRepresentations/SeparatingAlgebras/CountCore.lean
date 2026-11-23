import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private theorem sq_sum_of_subsingleton {G : Type} (F : Finset G) (hF : ∀ g ∈ F, ∀ g' ∈ F, g = g') (t : G → ℂ) :
    ‖∑ g ∈ F, t g‖ ^ 2 = ∑ g ∈ F, ‖t g‖ ^ 2 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
  · simp
  · have e : F = {g} := Finset.eq_singleton_iff_unique_mem.2 ⟨hg, fun g' h' => hF _ h' _ hg⟩
    subst e
    simp

private theorem fibre_sum {G Y : Type} [Fintype Y] [DecidableEq Y] (S : Finset G) (π : G → Y)
    (hπ : ∀ g ∈ S, ∀ g' ∈ S, π g = π g' → g = g') (t : G → ℂ) :
    ∑ y, ‖∑ g ∈ S with π g = y, t g‖ ^ 2 = ∑ g ∈ S, ‖t g‖ ^ 2 := by
  refine Eq.trans ?_ (Finset.sum_fiberwise S π fun g => ‖t g‖ ^ 2)
  refine Finset.sum_congr rfl fun y _ => sq_sum_of_subsingleton _ (fun g hg g' hg' => ?_) t
  rw [Finset.mem_filter] at hg hg'
  exact hπ g hg.1 g' hg'.1 (hg.2.trans hg'.2.symm)

private noncomputable def mat {G X : Type} [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) : Matrix (X × Fin d) (X × Fin d) ℂ :=
  fun r s => ∑ g ∈ S with π r.1 g = s.1, t g * m r.1 g r.2 s.2

private theorem mat_mulVec {G X : Type} [Fintype X] [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) (u : X × Fin d → ℂ) (y : X) (i : Fin d) :
    (mat S π t m).mulVec u (y, i) = ∑ g ∈ S, t g * ∑ j, m y g i j * u (π y g, j) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mat, Finset.sum_mul]
  refine Eq.trans ?_ (Finset.sum_fiberwise S (π y) _)
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [(Finset.mem_filter.1 hg).2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

private theorem mat_hs {G X : Type} [Fintype X] [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) (M₀ : ℝ) (hm : ∀ y g i j, ‖m y g i j‖ ≤ M₀)
    (hπ : ∀ y, ∀ g ∈ S, ∀ g' ∈ S, π y g = π y g' → g = g') :
    ∑ r, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ ((d : ℝ) ^ 2 * M₀ ^ 2) * Fintype.card X * ∑ g ∈ S, ‖t g‖ ^ 2 := by
  have hrow : ∀ r : X × Fin d, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ (d : ℝ) * (M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2) := by
    intro r
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hj : ∀ j : Fin d, ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 ≤ M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2 := by
      intro j
      have e := fibre_sum S (π r.1) (hπ r.1) (fun g => t g * m r.1 g r.2 j)
      calc ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 = ∑ g ∈ S, ‖t g * m r.1 g r.2 j‖ ^ 2 := e
        _ ≤ ∑ g ∈ S, M₀ ^ 2 * ‖t g‖ ^ 2 := Finset.sum_le_sum fun g _ => by
            rw [norm_mul, mul_pow, mul_comm]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hm _ _ _ _) 2) (by positivity)
        _ = _ := (Finset.mul_sum _ _ _).symm
    calc ∑ j : Fin d, ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 ≤ ∑ j : Fin d, M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  calc ∑ r, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ ∑ r : X × Fin d, (d : ℝ) * (M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => hrow r
    _ = _ := by
      simp [Fintype.card_prod]
      ring

private theorem sep_eq {G : Type} [Group G] (R N C : Subgroup G) (hN : N.Normal) {z γ γ' x x' c c' : G}
    (hγ : γ ∈ R) (hγ' : γ' ∈ R) (hx : x ∈ N) (hx' : x' ∈ N) (hc : c ∈ C) (hc' : c' ∈ C) :
    ∃ Γ ∈ R, ∃ ξ ∈ N, ∃ k ∈ C, γ' * z * x' * c' = Γ * (γ * z * x * c) * ξ * k :=
  ⟨γ' * γ⁻¹, R.mul_mem hγ' (R.inv_mem hγ), c⁻¹ * (x⁻¹ * x') * c,
    hN.conj_mem' _ (N.mul_mem (N.inv_mem hx) hx') c, c⁻¹ * c', C.mul_mem (C.inv_mem hc) hc', by group⟩

private theorem form_val {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {W : Wt E a} {C : Subgroup (UA E a)}
    {f : algForms W} (hf : f ∈ fixedBy W C) {d : ℕ} (B : Module.Basis (Fin d) ℂ W.Sp) {γ q x c : UA E a}
    (hγ : γ ∈ ratU E a) (hx : x ∈ infU E a) (hc : c ∈ C) (v : W.Sp) :
    f.1 v (γ * q * x * c) = ∑ j, B.repr (W.rep ⟨x, hx⟩ v) j * f.1 (B j) q := by
  have h1 : f.1 v (γ * q * x * c) = f.1 (W.rep ⟨x, hx⟩ v) q := by
    rw [mem_fixedBy.1 hf c hc v, mul_assoc γ q x, (f.2.1 v).left γ hγ, f.2.2 ⟨x, hx⟩ v]
    rfl
  refine h1.trans ?_
  have h2 := congrFun (congrArg f.1 (B.sum_repr (W.rep ⟨x, hx⟩ v))) q
  refine h2.symm.trans ?_
  rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.countCore_pf :
    UpperTheory.Gal.Gen.HS → UpperTheory.Gal.Gen.WBound → UpperTheory.Gal.Gen.CountCore := by
  classical
  intro hHS hWB E _ _ _ a W
  let d := Module.finrank ℂ W.Sp
  let B : Module.Basis (Fin d) ℂ W.Sp := Module.finBasis ℂ W.Sp
  obtain ⟨M₀, hM₀⟩ := hWB E a W d B
  refine ⟨(d : ℝ) ^ 2 * M₀ ^ 2, by positivity, ?_⟩
  intro C X _ p hcov h hsep V hVC hV
  choose γ hγ π ξ hξ c hc hdec using fun (y : X) (g : UA E a) => hcov (p y * g)
  let η : X → UA E a → infU E a := fun y g => ⟨ξ y g, hξ y g⟩
  let m : X → UA E a → Fin d → Fin d → ℂ := fun y g i j => B.repr (W.rep (η y g) (B i)) j
  let ev : V →ₗ[ℂ] (X × Fin d → ℂ) :=
    { toFun := fun f q => f.1.1 (B q.2) (p q.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro f hf0
    have hz : ∀ j y, f.1.1 (B j) (p y) = 0 := fun j y => congrFun hf0 (y, j)
    refine Subtype.ext (Subtype.ext (LinearMap.ext fun v => funext fun g => ?_))
    obtain ⟨γ₀, hγ₀, y, x, hx, c₀, hc₀, rfl⟩ := hcov g
    rw [form_val (hVC f.2) B hγ₀ hx hc₀ v]
    exact Finset.sum_eq_zero fun j _ => by rw [hz, mul_zero]
  have hfix : ∀ f : V, (mat h.support π h m).mulVec (ev f) = ev f := by
    intro f
    funext ⟨y, i⟩
    rw [mat_mulVec]
    have hop := congrFun (hV f.1 f.2 (B i)) (p y)
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul] at hop
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) hop
    rw [hdec y g, form_val (hVC f.2) B (hγ y g) (hξ y g) (hc y g) (B i)]
    rfl
  have hπ : ∀ y, ∀ g ∈ h.support, ∀ g' ∈ h.support, π y g = π y g' → g = g' := by
    intro y g hg g' hg' e
    obtain ⟨Γ, hΓ, ξ', hξ', k, hk, e'⟩ := sep_eq (ratU E a) (infU E a) C inferInstance (z := p (π y g))
      (hγ y g) (hγ y g') (hξ y g) (hξ y g') (hc y g) (hc y g')
    refine hsep y g hg g' hg' Γ hΓ ξ' hξ' k hk ?_
    have e1 := hdec y g'
    rw [← e] at e1
    rw [e1, e', ← hdec y g]
  have hfd : FiniteDimensional ℂ V := FiniteDimensional.of_injective ev hinj
  refine ⟨hfd, ?_⟩
  have h1 := hHS (X × Fin d) (mat h.support π h m) (LinearMap.range ev) (by rintro _ ⟨f, rfl⟩; exact hfix f)
  rw [LinearMap.finrank_range_of_inj hinj] at h1
  exact h1.trans (mat_hs h.support π h m M₀ (fun y g i j => hM₀ (η y g) i j) hπ)
