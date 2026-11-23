import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenAction
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagField

open Matrix

theorem lowerUni_eq {Ω : Type} [Field Ω] {n : ℕ} (A C₁ C₂ : Matrix (Fin n) (Fin n) Ω)
    (h₁ : (A * C₁).IsLowerTriangular) (h₂ : (A * C₂).IsLowerTriangular)
    (d₁ : ∀ i, (A * C₁) i i = 1) (d₂ : ∀ i, (A * C₂) i i = 1)
    (hC₁ : C₁.IsUpperTriangular) (hC₂ : C₂.IsUpperTriangular) : A * C₁ = A * C₂ := by
  have det₂ : (A * C₂).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ h₂]; exact Finset.prod_eq_one fun i _ => d₂ i
  have uA : IsUnit A.det := isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one (by rw [← Matrix.det_mul, det₂]))
  have uC₂ : IsUnit C₂.det := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul_eq_one (by rw [← Matrix.det_mul, det₂]))
  have uG₂ : IsUnit (A * C₂).det := by rw [det₂]; exact isUnit_one
  haveI := Matrix.invertibleOfIsUnitDet (A * C₂) uG₂
  haveI := Matrix.invertibleOfIsUnitDet C₂ uC₂
  set N := (A * C₂)⁻¹ * (A * C₁) with hN
  have hNl : N.IsLowerTriangular := (Matrix.blockTriangular_inv_of_blockTriangular h₂).mul h₁
  have hN' : N = C₂⁻¹ * C₁ := by
    rw [hN, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹, Matrix.nonsing_inv_mul A uA,
      Matrix.one_mul]
  have hNu : N.IsUpperTriangular := by
    rw [hN']; exact (Matrix.blockTriangular_inv_of_blockTriangular hC₂).mul hC₁
  have hoff : ∀ l i, l ≠ i → N l i = 0 := fun l i hli => by
    rcases lt_or_gt_of_ne hli with h | h
    · exact hNl (show OrderDual.toDual i < OrderDual.toDual l from h)
    · exact hNu h
  have hG : A * C₁ = (A * C₂) * N := by rw [hN, Matrix.mul_nonsing_inv_cancel_left _ _ uG₂]
  have entry : ∀ j i, (A * C₁) j i = (A * C₂) j i * N i i := fun j i => by
    rw [hG, Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hoff l i hl, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
  have hdiag : ∀ i, N i i = 1 := fun i => by
    have := entry i i
    rw [d₁, d₂, one_mul] at this
    exact this.symm
  ext j i
  rw [entry, hdiag, mul_one]

theorem lowerUni_mem_range {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (C : Matrix (Fin n) (Fin n) Ω) (h : (M.map (algebraMap F Ω) * C).IsLowerTriangular)
    (d : ∀ i, (M.map (algebraMap F Ω) * C) i i = 1) (hC : C.IsUpperTriangular) (j i : Fin n) :
    (M.map (algebraMap F Ω) * C) j i ∈ Set.range (algebraMap F Ω) := by
  obtain ⟨π, hπ⟩ : ∃ π : Ω →ₗ[F] F, π ∘ₗ Algebra.linearMap F Ω = LinearMap.id :=
    LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap F Ω).injective)
  have hπa : ∀ a : F, π (algebraMap F Ω a) = a := fun a => LinearMap.congr_fun hπ a
  set A := M.map (algebraMap F Ω)
  set C' : Matrix (Fin n) (Fin n) Ω := fun a b => algebraMap F Ω (π (C a b))
  have key : A * C' = fun a b => algebraMap F Ω (π ((A * C) a b)) := by
    ext a b
    show ∑ l, algebraMap F Ω (M a l) * algebraMap F Ω (π (C l b)) =
      algebraMap F Ω (π (∑ l, algebraMap F Ω (M a l) * C l b))
    rw [map_sum π, map_sum (algebraMap F Ω)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Algebra.smul_def (M a l) (C l b), map_smul, smul_eq_mul, map_mul]
  have hC' : C'.IsUpperTriangular := fun a b hab => by
    show algebraMap F Ω (π (C a b)) = 0
    rw [hC hab, map_zero, map_zero]
  have h' : (A * C').IsLowerTriangular := fun a b hab => by
    rw [key]
    show algebraMap F Ω (π ((A * C) a b)) = 0
    rw [h hab, map_zero, map_zero]
  have d' : ∀ i, (A * C') i i = 1 := fun i => by
    rw [key]
    show algebraMap F Ω (π ((A * C) i i)) = 1
    rw [d i, ← map_one (algebraMap F Ω), hπa, map_one]
  have e := lowerUni_eq A C C' h h' d d' hC hC'
  rw [e, key]
  exact ⟨_, rfl⟩

end GlobalTheory.FlagField

namespace GlobalTheory.FlagField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X}

theorem coef_unique {l : Level H} {c : Coeff l} {R : Type} [CommRing R] {f : c.F →+* R} {x : Sp R ⟶ X}
    {u : Vecs Dw t R} (h : GlobalTheory.LocM.IsFrame t f x u) (τ : E →+* ℂ) {a b : Fin (Dw.mult τ) → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (ha : IsCombAtG t x (u τ) a w) (hb : IsCombAtG t x (u τ) b w) : a = b := by
  have hw : IsTanAtG t x w := GlobalTheory.FlagEmb.comb_tan t (fun i => (h.1 τ i).1) ha
  have he : ∀ a' : 𝓞 E, w ≫ (t.act.act a').left = spMap (epsMul (f (embK c τ a'))) ≫ w := fun a' =>
    GlobalTheory.FlagEmb.eig_of_comb t (u τ) a w a' _ (fun j => ⟨(h.1 τ j).1, (h.1 τ j).2 a'⟩) ha
  exact (h.2 τ w hw he).unique ha hb

end GlobalTheory.FlagField

open GlobalTheory.FlagField in

theorem GlobalTheory.FlagField.mem_closure : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) (ty : (E →+* ℂ) → Finset ℕ), (∀ τ k, k ≤ Dw.mult τ → k ∈ ty τ) →
    ∀ {k K Ω : Type} [Field k] [Field K] [Field Ω] (r : k →+* K) (yk : Sp k ⟶ X) (cu : c.F →+* K) (u : Vecs Dw t K),
    GlobalTheory.LocM.IsFrame t cu (spMap r ≫ yk) u →
    ∀ (σ ι : K →+* Ω), σ.comp r = ι.comp r → σ.comp cu = ι.comp cu →
    ∀ (s : ∀ τ, Low (Dw.mult τ) → Ω) (v : Vecs Dw t Ω),
    (∀ τ i, IsCombAtG t (spMap (ι.comp r) ≫ yk) ((u.bc ι) τ) (fun j => uni (s τ) j i) (v τ i)) →
    GlobalTheory.LocM.SameFlag ty t (spMap (ι.comp r) ≫ yk) (u.bc σ) v →
    ∀ τ q, s τ q ∈ Subfield.closure (Set.range ι ∪ Set.range σ) := by
  intro E _ _ _ H Dw l c X t ty hty k K Ω _ _ _ r yk cu u hu σ ι hr hc s v hv hsf τ q
  classical
  set L₀ := Subfield.closure (Set.range ι ∪ Set.range σ) with hL₀
  let σ₀ : K →+* L₀ := σ.codRestrict L₀ (fun z => Subfield.subset_closure (Or.inr ⟨z, rfl⟩))
  let ι₀ : K →+* L₀ := ι.codRestrict L₀ (fun z => Subfield.subset_closure (Or.inl ⟨z, rfl⟩))
  have hσ : L₀.subtype.comp σ₀ = σ := rfl
  have hι : L₀.subtype.comp ι₀ = ι := rfl
  have hr₀ : σ₀.comp r = ι₀.comp r := RingHom.ext fun z => Subtype.ext (RingHom.congr_fun hr z)
  have hc₀ : σ₀.comp cu = ι₀.comp cu := RingHom.ext fun z => Subtype.ext (RingHom.congr_fun hc z)
  have F₀ : GlobalTheory.LocM.IsFrame t (ι₀.comp cu) (spMap (ι₀.comp r) ≫ yk) (u.bc σ₀) := by
    have := isFrame_bc E H Dw l c X t K L₀ cu σ₀ (spMap r ≫ yk) u hu
    rwa [← Category.assoc, spMap_comp', hr₀, hc₀] at this
  have G₀ : GlobalTheory.LocM.IsFrame t (ι₀.comp cu) (spMap (ι₀.comp r) ≫ yk) (u.bc ι₀) := by
    have := isFrame_bc E H Dw l c X t K L₀ cu ι₀ (spMap r ≫ yk) u hu
    rwa [← Category.assoc, spMap_comp'] at this
  have U : GlobalTheory.LocM.IsFrame t (ι.comp cu) (spMap (ι.comp r) ≫ yk) (u.bc ι) := by
    have := isFrame_bc E H Dw l c X t K Ω cu ι (spMap r ≫ yk) u hu
    rwa [← Category.assoc, spMap_comp'] at this
  choose M₀ hM₀ using fun j => (GlobalTheory.LocM.IsFrame.exists_comb G₀ F₀ τ j).exists
  have hMΩ : ∀ j, IsCombAtG t (spMap (ι.comp r) ≫ yk) ((u.bc ι) τ) (fun l => L₀.subtype (M₀ j l))
      ((u.bc σ) τ j) := by
    intro j
    have h1 := GlobalTheory.LocM.comb_bc L₀.subtype (hM₀ j)
    have e1 : spMap L₀.subtype ≫ spMap (ι₀.comp r) ≫ yk = spMap (ι.comp r) ≫ yk := by
      rw [← Category.assoc, spMap_comp']; rfl
    have e2 : (fun i => spMap (dualMap L₀.subtype) ≫ (u.bc ι₀) τ i) = (u.bc ι) τ := by
      have := GlobalTheory.LocM.Vecs.bc_bc ι₀ L₀.subtype u
      rw [hι] at this
      exact funext fun i => congrFun (congrFun this τ) i
    have e3 : spMap (dualMap L₀.subtype) ≫ (u.bc σ₀) τ j = (u.bc σ) τ j := by
      have := GlobalTheory.LocM.Vecs.bc_bc σ₀ L₀.subtype u
      rw [hσ] at this
      exact congrFun (congrFun this τ) j
    rw [e1, e2, e3] at h1
    exact h1
  have hC : ∀ i : Fin (Dw.mult τ), ∃ cf : Fin (Dw.mult τ) → Ω, (∀ j : Fin (Dw.mult τ), i.1 + 1 ≤ j.1 → cf j = 0) ∧
      IsCombAtG t (spMap (ι.comp r) ≫ yk) ((u.bc σ) τ) cf (v τ i) := fun i =>
    hsf τ (i.1 + 1) (hty τ _ i.2) i (Nat.lt_succ_self _)
  choose C hC0 hCc using hC
  let M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L₀ := Matrix.of fun a j => M₀ j a
  let Cm : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω := Matrix.of fun j i => C i j
  have comb : ∀ i, IsCombAtG t (spMap (ι.comp r) ≫ yk) ((u.bc ι) τ) ((M.map (algebraMap L₀ Ω)).mulVec (C i))
      (v τ i) := fun i =>
    tanLinG _ (fun j => (U.1 τ j).1) _ (M.map (algebraMap L₀ Ω)) (C i) (v τ i) hMΩ (hCc i)
  have hG : M.map (algebraMap L₀ Ω) * Cm = Matrix.of fun j i => uni (s τ) j i := by
    ext j i
    have e := congrFun (coef_unique U τ (hv τ i) (comb i)) j
    rw [Matrix.of_apply, e]
    rfl
  have hlow : (M.map (algebraMap L₀ Ω) * Cm).IsLowerTriangular := by
    rw [hG]
    intro a b hab
    have hab' : a < b := hab
    simp only [Matrix.of_apply, uni, dif_neg (not_lt.2 hab'.le), if_neg hab'.ne]
  have hdiag : ∀ i, (M.map (algebraMap L₀ Ω) * Cm) i i = 1 := fun i => by
    rw [hG]
    simp [uni]
  have hup : Cm.IsUpperTriangular := fun a b hab => hC0 b a (Nat.succ_le_of_lt hab)
  obtain ⟨y, hy⟩ := lowerUni_mem_range M Cm hlow hdiag hup q.1.2 q.1.1
  have e : s τ q = uni (s τ) q.1.2 q.1.1 := by simp [uni, dif_pos q.2]
  rw [hG, Matrix.of_apply, ← e] at hy
  rw [← hy]
  exact y.2

end
