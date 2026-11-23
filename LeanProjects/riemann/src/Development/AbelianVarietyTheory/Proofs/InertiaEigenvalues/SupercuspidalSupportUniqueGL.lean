import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothDualNeZeroAtVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroIntertwiningMapFromUnitarySupercusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LocGL.SupportUnique

section Abstract

variable {G G' V W U : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem isSubquotient_comp {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (ψ : G' →* G) :
    IsSubquotient (σ.comp ψ : Representation ℂ G' W) (ρ.comp ψ : Representation ℂ G' V) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

theorem nonempty_equiv_of_isSubquotient {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible) (h : IsSubquotient σ ρ) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  have hS : S = ⊤ := by
    refine (eq_bot_or_eq_top S).resolve_left fun h => hw ?_
    have h1 : (v : V) ∈ (⊥ : Subrepresentation ρ).toSubmodule := h ▸ v.2
    have h2 : v = 0 := Subtype.ext h1
    rw [h2, map_zero]
  subst hS
  let q : ρ.IntertwiningMap σ :=
    ⟨f.toLinearMap ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id (fun _ => trivial),
      fun g => LinearMap.ext fun y => f.isIntertwining _ _ g ⟨y, trivial⟩⟩
  rcases Representation.IsIrreducible.bijective_or_eq_zero q with h | h
  · exact ⟨equivOfBijective q h⟩
  · exact absurd (congrArg (fun F : ρ.IntertwiningMap σ => F v) h) hw

theorem isSubquotient_of_span {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {μ : Representation ℂ G U}
    (hσ : σ.IsIrreducible) (h : IsSubquotient σ μ)
    (hspan : Submodule.span ℂ {u | ∃ (ι : ρ.IntertwiningMap μ) (v : V), ι v = u} = ⊤) : IsSubquotient σ ρ := by
  obtain ⟨S, f, hf⟩ := h
  by_contra hn
  let N : Subrepresentation μ → Prop := fun T => ∀ s : S.toSubmodule, (s : U) ∈ T.toSubmodule → f s = 0
  have step : ∀ T, N T → ∀ ι : ρ.IntertwiningMap μ, N (T ⊔ GlobalTheory.JHMult.subMap ι ⊤) := by
    intro T hT ι
    obtain ⟨l, hl⟩ := GlobalTheory.JHMult.exists_factor (S.toSubmodule.subtype.coprod T.toSubmodule.subtype)
      (f.toLinearMap ∘ₗ LinearMap.fst ℂ _ _) (by
        rintro ⟨s, t⟩ h0
        have h1 : (s : U) + t = 0 := h0
        exact hT s (by rw [eq_neg_of_add_eq_zero_left h1]; exact neg_mem t.2))
    have hl' : ∀ (s : S.toSubmodule) (t : U), t ∈ T.toSubmodule → l (s + t) = f s := fun s t ht => hl (s, ⟨t, ht⟩)
    let R := GlobalTheory.JHMult.subComap ι (S ⊔ T)
    let F : R.toRepresentation.IntertwiningMap σ := ⟨l ∘ₗ ι.toLinearMap ∘ₗ R.toSubmodule.subtype, fun g =>
      LinearMap.ext fun r => by
        obtain ⟨s, hs, t, ht, e⟩ := Submodule.mem_sup.1 (show ι r ∈ S.toSubmodule ⊔ T.toSubmodule from r.2)
        show l (ι (ρ g r)) = σ g (l (ι r))
        rw [ι.isIntertwining, ← e, map_add, hl' ⟨s, hs⟩ t ht, ← f.isIntertwining]
        exact hl' (S.toRepresentation g ⟨s, hs⟩) _ (T.apply_mem_toSubmodule g ht)⟩
    have hF : F = 0 := (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_left fun h => hn ⟨R, F, h⟩
    intro s hs
    obtain ⟨t, ht, _, ⟨v, -, rfl⟩, e⟩ := Submodule.mem_sup.1
      (show (s : U) ∈ T.toSubmodule ⊔ (GlobalTheory.JHMult.subMap ι ⊤).toSubmodule from hs)
    have e' : ι v = s + -t := by rw [← e]; simp
    have hv : v ∈ R.toSubmodule := by
      show ι v ∈ S.toSubmodule ⊔ T.toSubmodule
      rw [e']
      exact Submodule.add_mem_sup s.2 (neg_mem ht)
    have h2 : l (ι v) = 0 := congrArg (fun F : R.toRepresentation.IntertwiningMap σ => F ⟨v, hv⟩) hF
    rwa [e', hl' s _ (neg_mem ht)] at h2
  have key : ∀ u ∈ Submodule.span ℂ {u | ∃ (ι : ρ.IntertwiningMap μ) (v : V), ι v = u},
      ∀ T, N T → ∃ T', T ≤ T' ∧ N T' ∧ u ∈ T'.toSubmodule := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ι, v, rfl⟩ := hx
      exact fun T hT => ⟨_, le_sup_left, step T hT ι, Submodule.mem_sup_right ⟨v, trivial, rfl⟩⟩
    | zero => exact fun T hT => ⟨T, le_rfl, hT, zero_mem _⟩
    | add x y _ _ hx hy =>
      intro T hT
      obtain ⟨T₁, h1, h2, h3⟩ := hx T hT
      obtain ⟨T₂, h4, h5, h6⟩ := hy T₁ h2
      exact ⟨T₂, h1.trans h4, h5, add_mem (h4 h3) h6⟩
    | smul c x _ hx =>
      intro T hT
      obtain ⟨T₁, h1, h2, h3⟩ := hx T hT
      exact ⟨T₁, h1, h2, Submodule.smul_mem _ c h3⟩
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨s, rfl⟩ := hf w
  obtain ⟨T, -, h2, h3⟩ := key s (hspan ▸ Submodule.mem_top) ⊥ fun s hs => by
    rw [show s = 0 from Subtype.ext hs, map_zero]
  exact hw (h2 s h3)

theorem isSubquotient_factor {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (c : α)
    {σ : Representation ℂ (Γ c) W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ((piTensor ρ).comp (MonoidHom.mulSingle Γ c) : Representation ℂ (Γ c) (⨂[ℂ] a, X a))) :
    IsSubquotient σ (ρ c) := by
  refine isSubquotient_of_span hσ h (top_le_iff.1 fun y hy => ?_)
  clear hy
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | smul_tprod r x =>
    refine Submodule.smul_mem _ r (Submodule.subset_span
      ⟨⟨(PiTensorProduct.tprod ℂ (s := X)).toLinearMap x c, fun g => LinearMap.ext fun v => ?_⟩, x c, ?_⟩)
    · show PiTensorProduct.tprod ℂ (Function.update x c (ρ c g v)) =
        piTensor ρ (Pi.mulSingle c g) (PiTensorProduct.tprod ℂ (Function.update x c v))
      rw [piTensor_tprod]
      congr 1
      funext b
      by_cases hb : b = c
      · subst hb
        simp
      · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
    · show PiTensorProduct.tprod ℂ (Function.update x c (x c)) = _
      rw [Function.update_eq_self]

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSubquotient_jac_single {r : ℕ} {b : Fin r → ℕ} (a : Fin r) (ha : ∀ j, j ≠ a → b j = 0)
    (f : (Σ j, Fin (b j)) ≃ Fin (b a)) (σ : Representation ℂ (GL (Fin (b a)) k) V) :
    IsSubquotient ((jac f σ).comp (MonoidHom.mulSingle (fun j => GL (Fin (b j)) k) a) :
      Representation ℂ (GL (Fin (b a)) k) _) σ := by
  have hb : Function.Bijective (fun i : Fin (b a) => (⟨a, i⟩ : Σ j, Fin (b j))) := by
    refine ⟨sigma_mk_injective (β := fun j => Fin (b j)), fun ⟨j, i⟩ => ?_⟩
    obtain rfl : j = a := by_contra fun h => by have := i.2; have := ha j h; omega
    exact ⟨i, rfl⟩
  let f' := (Equiv.ofBijective _ hb).symm
  have hf' : ∀ i, f' ⟨a, i⟩ = i := fun i => (Equiv.ofBijective _ hb).symm_apply_apply i
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ f f' V).2 σ
  refine (isSubquotient_comp (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) _).trans ?_
  have h1 : ∀ g : GL (Fin (b a)) k, leviEmb k f' (Pi.mulSingle a g) = g := fun g => by
    ext i j
    conv_lhs => rw [← hf' i, ← hf' j]
    rw [leviEmb_apply_same]
    simp
  have h2 : modExp (fun j => Fin (b j)) a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro c hc
      simp [ha c (Finset.mem_filter.1 hc).2.ne]
    · intro c hc
      simp [ha c (Finset.mem_filter.1 hc).2.ne']
  have h3 : ∀ g : GL (Fin (b a)) k, deltaHalf k (fun j => Fin (b j)) (Pi.mulSingle a g) = 1 := fun g => by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun c _ => ?_
    by_cases hc : c = a
    · subst hc
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hc, map_one, map_one]
  refine .of_surjective ⟨Submodule.mkQ _, fun g => LinearMap.ext fun v => ?_⟩ (Submodule.mkQ_surjective _)
  show Submodule.Quotient.mk (σ g v) = jac f' σ (Pi.mulSingle a g) (Submodule.Quotient.mk v)
  rw [jac_mk, h1, h3, inv_one, Units.val_one, one_smul]

theorem exists_block_of_isCusp {x : IrrGL k} (hx : x.IsCusp) {r : ℕ} {b : Fin r → ℕ}
    (f : (Σ j, Fin (b j)) ≃ Fin x.1) (c : ∀ j, IrrRep (GL (Fin (b j)) k))
    (h : IsSubquotient (piTensor fun j => (c j).ρ) (jac f x.rep)) :
    ∃ a, (∀ j, j ≠ a → b j = 0) ∧ IrrGL.of (c a).ρ (c a).smooth (c a).irr = x := by
  have hn := GlobalTheory.ProdSupport.nontrivial_piTensor (fun j => (c j).V)
    fun j => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (c j).irr
  obtain ⟨⟨a, i⟩, -⟩ := f.surjective ⟨0, hx.1⟩
  have ha : ∀ j, j ≠ a → b j = 0 := by
    intro j hne
    by_contra hj
    have hU : unipRad k f ≠ ⊥ := by
      refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨f ⟨j, ⟨0, by omega⟩⟩, f ⟨a, i⟩, by rwa [blk_apply, blk_apply]⟩
      · exact ⟨f ⟨a, i⟩, f ⟨j, ⟨0, by omega⟩⟩, by rwa [blk_apply, blk_apply]⟩
    have hs := hx.2.2 r b f hU
    obtain ⟨S, g, hg⟩ := h
    exact not_subsingleton _ (Function.Surjective.subsingleton hg)
  refine ⟨a, ha, ?_⟩
  obtain ⟨d, y⟩ := x
  obtain rfl : b a = d := by
    have h1 : ∑ j, b j = d := by simpa using Fintype.card_congr f
    rwa [Finset.sum_eq_single a (fun j _ hj => ha j hj) (by simp)] at h1
  obtain ⟨Y, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
    ((piTensor fun j => (c j).ρ).comp (MonoidHom.mulSingle (fun j => GL (Fin (b j)) k) a)) hn
  obtain ⟨φ⟩ := nonempty_equiv_of_isSubquotient hυ (c a).irr (isSubquotient_factor _ a hυ hυs)
  obtain ⟨ψ⟩ := nonempty_equiv_of_isSubquotient hυ y.rep.irr
    (hυs.trans ((isSubquotient_comp h _).trans (isSubquotient_jac_single a ha f _)))
  exact (IrrGL.of_eq_of.2 ⟨φ.trans ψ.symm⟩).trans (IrrGL.of_rep ⟨_, y⟩)

theorem eq_zero_of_hasSupport {N : ℕ} (hN : N = 0) {π : Representation ℂ (GL (Fin N) k) V}
    {s : Multiset (IrrGL k)} (h : HasSupport π s) : s = 0 := by
  have h2 := h.sum_fst
  rw [Fintype.card_fin] at h2
  by_contra hne
  obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
  have h4 := (h.isCusp hy).1
  have h5 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hy)
  omega

theorem exists_sum_of_jac (hG : GeometricLemma) (hZ : ZelevinskyPolynomialRing) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL k)} (hs : HasSupport π s) {r : ℕ} {d : Fin r → ℕ}
    (e' : (Σ j, Fin (d j)) ≃ Fin N) {τ : Representation ℂ (Levi k fun j => Fin (d j)) W} (hτ : τ.IsIrreducible)
    (hτs : IsSubquotient τ (jac e' π)) (y : ∀ j, IrrRep (GL (Fin (d j)) k))
    (hy : ∀ j, IsSubquotient (y j).ρ (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W)) :
    ∃ t : Fin r → Multiset (IrrGL k), (∀ j, HasSupport (y j).ρ (t j)) ∧ s = ∑ j, t j := by
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  obtain ⟨h, x, rfl, hi, hc, e, hsub⟩ := hs
  have hx : ∀ i, (x i).IsCusp := fun i => ⟨(hc i).1, (hc i).2.2⟩
  obtain ⟨b, f, g, c, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e'
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength) hτ
    (hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e' (isSmooth_parInd _ _) hsub))
  choose J hJ0 hJ using fun i => exists_block_of_isCusp (hx i) (f i) (c i) (hrow i)
  let u : Fin h → Fin r → Multiset (IrrGL k) := fun i j => if j = J i then {x i} else 0
  have hu : ∀ i j, HasSupport (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr).rep (u i j) := by
    intro i j
    by_cases hj : j = J i
    · subst hj
      simp only [u, if_true]
      rw [hJ i]
      exact hasSupport_self (hx i)
    · obtain ⟨s', hs'⟩ := SupportRing.exists_hasSupport hZ (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr)
      simp only [u, if_neg hj]
      rwa [eq_zero_of_hasSupport (hJ0 i j hj) hs'] at hs'
  refine ⟨fun j => ∑ i, u i j, fun j => ?_, ?_⟩
  · have hd : ∑ i, b.1 i j = d j := by simpa using b.2.2 j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (c i j).ρ) j (y j).irr
      ((hy j).trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (c i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (c i j).ρ) (fun i => (c i j).smooth) fun i => (c i j).irr)
    exact SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ
      (y := fun i => IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr) (fun i => hu i j) (y j).irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  · rw [Finset.sum_comm]
    simp only [u, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Multiset.sum_map_singleton (Finset.univ.val.map x), Multiset.map_map]
    rfl

theorem exists_root_norm {ω : kˣ →* ℂˣ} (hω : IsSmoothChar ω) {b : ℕ} (hb : 0 < b) :
    ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ ∀ z, ‖((ω * ψ ^ b) z : ℂ)‖ = 1 := by
  let f : kˣ →* ℂ :=
    { toFun := fun z => ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ)
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, Units.val_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul] }
  refine ⟨f.toHomUnits, Subgroup.isOpen_mono (H₁ := ω.ker) (fun z hz => ?_) hω, fun z => ?_⟩
  · refine Units.ext ?_
    have hz' : ω z = 1 := hz
    show ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ) = 1
    rw [hz']; simp
  · have h0 : 0 < ‖(ω z : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have e : ((f.toHomUnits z : ℂˣ) : ℂ) = ((‖(ω z : ℂ)‖ ^ (-(b : ℝ)⁻¹) : ℝ) : ℂ) := rfl
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, e, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _), ← Real.rpow_natCast, ← Real.rpow_mul h0.le,
      neg_mul, inv_mul_cancel₀ (by positivity), Real.rpow_neg_one, mul_inv_cancel₀ h0.ne']

theorem exists_map_of_isCuspidal {b : ℕ} (hb : 0 < b) {ρ : Representation ℂ (GL (Fin b) k) V}
    (hρi : ρ.IsIrreducible) (hρc : IsCuspidal ρ) {τ : Representation ℂ (GL (Fin b) k) W} (hτ : IsSmooth τ)
    (hz : ∀ z : kˣ, ∃ c : ℂ, ∀ w, τ (GeneralLinearGroup.scalar _ z) w = c • w) (h : IsSubquotient ρ τ) :
    ∃ ι : ρ.IntertwiningMap τ, ι ≠ 0 := by
  obtain ⟨S, p, hp⟩ := h
  have hSs : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, Representation.IntertwiningMap.id _, Function.surjective_id⟩ hτ
  obtain ⟨ω, hω, hωc⟩ := exists_smooth_hasCentralChar hρc.1 hρi
  obtain ⟨ψ, hψ, hψ1⟩ := exists_root_norm hω hb
  have hc' : IsCuspidal (twist ρ (detChar (Fin b) ψ)) := isCuspidal_twist hρc hψ
  have hsc := GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k b V _ hc'
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρi
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  obtain ⟨l, hl, hly⟩ := GlobalTheory.SmoothForm.exists_smooth_form_ne_zero _ _ (twist ρ (detChar (Fin b) ψ)) (fun U hU => by
    obtain ⟨γ, hγ, h⟩ := GlobalTheory.CentralExponent.exists_cong_subset (n := Fin b) hU
    exact ⟨_, GlobalTheory.CentralExponent.isOpen_cong γ hγ, GlobalTheory.CentralExponent.isCompact_cong γ hγ, h⟩) hc'.1 y hy
  have hu := GlobalTheory.isUnitarisable_of_isSupercuspidal _ _ _ l hl (fun h => hly (by rw [h]; rfl))
    (isIrreducible_twist hρi _) hsc
    (fun z hz => by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨z, rfl⟩ := hz
      have h := hasCentralChar_twist hωc ψ z
      rw [Fintype.card_fin] at h
      exact ⟨_, hψ1 z, h⟩)
  obtain ⟨ι, hι⟩ := GlobalTheory.CuspBack.exists_back _ _ _ (twist S.toRepresentation (detChar (Fin b) ψ)) _ (twistMap p _)
    (isSmooth_twist hSs hψ.detChar) hsc hu
    (fun z hz' => by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
      obtain ⟨z, rfl⟩ := hz'
      obtain ⟨c, hc⟩ := hz z
      refine ⟨(detChar (Fin b) ψ (GeneralLinearGroup.scalar _ z) : ℂ) * c, fun w => ?_⟩
      rw [twist_apply, mul_smul]
      exact congrArg _ (Subtype.ext (hc w)))
    (fun h => by
      obtain ⟨w, hw⟩ := hp y
      have h1 : twistMap p (detChar (Fin b) ψ) w = y := hw
      rw [h] at h1
      exact hy h1.symm)
  refine ⟨⟨S.toSubmodule.subtype ∘ₗ ι.toLinearMap, fun g => LinearMap.ext fun v => ?_⟩, fun h => hι ?_⟩
  · have h1 := Representation.IntertwiningMap.isIntertwining _ _ ι g v
    rw [twist_apply, twist_apply, map_smul] at h1
    exact congrArg Subtype.val (smul_right_injective _ (Units.ne_zero _) h1)
  · ext v
    exact congrArg (fun F : ρ.IntertwiningMap τ => F v) h

theorem exists_scalar_multiProd {h N : ℕ} {d : Fin h → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) {X : Fin h → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (hs : ∀ a, IsSmooth (σ a)) (hi : ∀ a, (σ a).IsIrreducible) (z : kˣ) :
    ∃ c : ℂ, ∀ w, parInd e (piTensor σ) (GeneralLinearGroup.scalar _ z) w = c • w := by
  choose ω _ hω using fun a => exists_smooth_hasCentralChar (hs a) (hi a)
  let g : Levi k fun a => Fin (d a) := fun a => GeneralLinearGroup.scalar _ z
  have h1 : leviEmb k e g = GeneralLinearGroup.scalar _ z := by
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same]
      simp [g, GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne k e g hab]
      simp [GeneralLinearGroup.scalar, diagonal_apply, hab]
  have h2 : ∀ y, piTensor σ g y = (∏ a, (ω a z : ℂ)) • y := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | smul_tprod c y =>
      rw [map_smul, smul_comm, piTensor_tprod, ← MultilinearMap.map_smul_univ]
      congr 2
      funext a
      exact hω a z _
  refine ⟨(deltaHalf k _ g : ℂ) * ∏ a, (ω a z : ℂ), fun f => Subtype.ext (Subtype.ext (funext fun y => ?_))⟩
  have h4 := parInd_law e _ f ⟨_, leviEmb_mem_parab k e g⟩ y
  rw [leviProj_leviEmb, h2, smul_smul] at h4
  have hc : y * GeneralLinearGroup.scalar (Fin N) z = GeneralLinearGroup.scalar (Fin N) z * y := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (y * GeneralLinearGroup.scalar (Fin N) z) = ((deltaHalf k _ g : ℂ) * ∏ a, (ω a z : ℂ)) • f.1.1 y
  rw [hc, ← h1]
  exact h4

theorem eq_singleton_of_isCusp {x : IrrGL k} (hx : x.IsCusp) {s : Multiset (IrrGL k)} (hs : HasSupport x.rep s) :
    s = {x} := by
  obtain ⟨h, y, rfl, hi, hc, e, hsub⟩ := hs
  obtain ⟨ι, hι⟩ := exists_map_of_isCuspidal hx.1 hi hx.2 (isSmooth_parInd _ _)
    (exists_scalar_multiProd e (fun a => (y a).rep) (fun a => (y a).2.rep.smooth) fun a => (y a).2.rep.irr) hsub
  have hU : unipRad k e = ⊥ := by
    by_contra hU
    haveI := hx.2.2 h _ e hU
    refine hι ((GlobalTheory.SmGL.Model.evalOne_bijective e hx.2.1 _).1 ?_)
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
    rw [Subsingleton.elim v 0, map_zero, map_zero]
  obtain ⟨⟨a, i⟩, -⟩ := e.surjective ⟨0, hx.1⟩
  have ha : ∀ j, j = a := by
    intro j
    by_contra hne
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_ hU
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨e ⟨j, ⟨0, (hc j).1⟩⟩, e ⟨a, i⟩, by rwa [blk_apply, blk_apply]⟩
    · exact ⟨e ⟨a, i⟩, e ⟨j, ⟨0, (hc j).1⟩⟩, by rwa [blk_apply, blk_apply]⟩
  obtain rfl : h = 1 := by
    simpa using Fintype.card_eq_one_iff.2 ⟨a, ha⟩
  obtain ⟨y₀, rfl⟩ : ∃ y₀, y = fun _ => y₀ := ⟨y 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨d, x⟩ := x
  obtain rfl : y₀.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, y₀.1 = y₀.1 := by simp
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun _ : Fin 1 => y₀.1) hd) _).1
    (piTensor fun _ => y₀.rep)
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one y₀ hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := nonempty_equiv_of_isSubquotient hi y₀.2.rep.irr
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective))
  have : y₀ = ⟨_, x⟩ := (IrrGL.of_rep y₀).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, x⟩))
  exact congrArg (fun z => ({z} : Multiset (IrrGL k))) this

theorem eq_of_hasSupport (hG : GeometricLemma) (hZ : ZelevinskyPolynomialRing) (N : ℕ) :
    ∀ (x : IrrGL k), x.1 = N → ∀ s t : Multiset (IrrGL k), HasSupport x.rep s → HasSupport x.rep t → s = t := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x rfl s t hs ht
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · rw [eq_zero_of_hasSupport h0 hs, eq_zero_of_hasSupport h0 ht]
    by_cases hc : IsCuspidal x.rep
    · rw [eq_singleton_of_isCusp ⟨hpos, hc⟩ hs, eq_singleton_of_isCusp ⟨hpos, hc⟩ ht]
    obtain ⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧
        ¬ Subsingleton (Jacquet x.rep (unipRad k e)) := by
      by_contra! hn
      exact hc ⟨x.2.rep.smooth, hn⟩
    obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e x.rep)
      (not_subsingleton_iff_nontrivial.1 hJ)
    have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)
    have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
      intro j
      obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
        (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
      exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
        (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
    choose y hy using hy
    obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hZ hs e hτ hτs y hy
    obtain ⟨u', hu', rfl⟩ := exists_sum_of_jac hG hZ ht e hτ hτs y hy
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : d j < x.1 := by
      have hN : ∑ a, d a = x.1 := by simpa using Fintype.card_congr e
      obtain ⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by
        obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
        obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective p
        obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective q
        rw [blk_apply, blk_apply] at hpq
        by_cases haj : a = j
        · exact ⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩
        · exact ⟨a, haj, p.pos⟩
      have h1 := Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        (Finset.mem_univ j) ha
      omega
    exact ih (d j) hlt (IrrGL.of (y j).ρ (y j).smooth (y j).irr) rfl _ _
      ((hu j).of_equiv (IrrGL.equivOf _ _ _)) ((hu' j).of_equiv (IrrGL.equivOf _ _ _))

theorem hasSupport_unique : GeometricLemma → BernsteinZelevinskyFiniteness → ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (s t : Multiset (IrrGL k)), HasSupport x.rep s → HasSupport x.rep t → s = t :=
  fun hG _ hZ _ _ _ _ _ _ x s t hs ht => eq_of_hasSupport hG hZ _ x rfl s t hs ht

end GlobalTheory.LocGL.SupportUnique
