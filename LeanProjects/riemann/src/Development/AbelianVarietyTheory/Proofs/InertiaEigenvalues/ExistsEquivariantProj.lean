import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Petersson GlobalTheory.Published Formalism.L2.Host Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CuspOrth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {ω : HChar E}
  (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem cuspFormsBounded : CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay
    (GlobalTheory.cuspRapidDecaySiegelGL_of_finite GlobalTheory.automorphicFormsFiniteGL)

variable (ω) in

abbrev bddSm : Submodule ℂ (Sm E a) := (bddForms E a ω).comap (Sm E a).subtype

abbrev ip (φ ψ : Sm E a) : ℂ := pet (latticeGL E a) μ φ.1 ψ.1

theorem ip_add_right (hω : ω.IsUnitary) {φ ψ ψ' : Sm E a} (h : φ ∈ bddSm ω) (h1 : ψ ∈ bddSm ω) (h2 : ψ' ∈ bddSm ω) :
    ip μ φ (ψ + ψ') = ip μ φ ψ + ip μ φ ψ' := by
  unfold ip
  rw [← conj_pet μ (ψ + ψ').1, ← conj_pet μ ψ.1, ← conj_pet μ ψ'.1, ← map_add]
  exact congrArg conj (pet_add_left μ hω h1 h2 h)

theorem ip_smul_right (c : ℂ) (φ ψ : Sm E a) : ip μ φ (c • ψ) = conj c * ip μ φ ψ := by
  unfold ip
  rw [← conj_pet μ (c • ψ).1, ← conj_pet μ ψ.1, ← map_mul, ← pet_smul_left μ]
  rfl

theorem ip_sub_right (hω : ω.IsUnitary) {φ ψ ψ' : Sm E a} (h : φ ∈ bddSm ω) (h1 : ψ ∈ bddSm ω) (h2 : ψ' ∈ bddSm ω) :
    ip μ φ (ψ - ψ') = ip μ φ ψ - ip μ φ ψ' := by
  rw [eq_sub_iff_add_eq, ← ip_add_right μ hω h (sub_mem h1 h2) h2, sub_add_cancel]

theorem eq_zero_of_ip_self (hω : ω.IsUnitary) {φ : Sm E a} (h : φ ∈ bddSm ω) (h0 : ip μ φ φ = 0) : φ = 0 := by
  by_contra hne
  obtain ⟨r, hr, e⟩ := pet_self_pos μ hω h fun e => hne (Subtype.ext e)
  exact hr.ne' (by exact_mod_cast e.symm.trans h0)

theorem eq_of_ip_eq (hω : ω.IsUnitary) {D : Submodule ℂ (Sm E a)} (hD : D ≤ bddSm ω) {p p' : Sm E a} (h : p ∈ D)
    (h' : p' ∈ D) (e : ∀ x ∈ D, ip μ x p = ip μ x p') : p = p' :=
  sub_eq_zero.1 <| eq_zero_of_ip_self μ hω (hD (sub_mem h h')) <| by
    rw [ip_sub_right μ hω (hD (sub_mem h h')) (hD h) (hD h'), e _ (sub_mem h h'), sub_self]

def core (hω : ω.IsUnitary) : InnerProductSpace.Core ℂ (bddSm (a := a) ω) where
  inner x y := ip μ y.1 x.1
  conj_inner_symm x y := conj_pet μ _ _
  re_inner_nonneg x := by
    by_cases h : x.1.1 = 0
    · have : ip μ x.1 x.1 = 0 := by
        have := pet_smul_left μ 0 x.1.1 x.1.1
        rw [zero_smul, zero_mul] at this
        unfold ip
        conv_lhs => enter [3]; rw [h]
        exact this
      simp [this]
    · obtain ⟨r, hr, e⟩ := pet_self_pos μ hω x.2 h
      rw [show ip μ x.1 x.1 = r from e]
      simpa using hr.le
  add_left x y z := ip_add_right μ hω z.2 x.2 y.2
  smul_left x y r := ip_smul_right μ r _ _
  definite x h := Subtype.ext (eq_zero_of_ip_self μ hω x.2 h)

theorem exists_orth_of_core {H : Type} [AddCommGroup H] [Module ℂ H] (c : InnerProductSpace.Core ℂ H)
    (D : Submodule ℂ H) [FiniteDimensional ℂ D] (v : H) : ∃ p ∈ D, ∀ x ∈ D, c.inner (v - p) x = 0 := by
  letI : NormedAddCommGroup H := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ H := InnerProductSpace.ofCore _
  obtain ⟨p, hp, h⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := D) v
  exact ⟨p, hp, (Submodule.mem_orthogonal' _ _).1 h⟩

theorem exists_proj_of_finite (hω : ω.IsUnitary) {D : Submodule ℂ (Sm E a)} (hD : D ≤ bddSm ω) [FiniteDimensional ℂ D]
    {ψ : Sm E a} (hψ : ψ ∈ bddSm ω) : ∃ p ∈ D, ∀ x ∈ D, ip μ x ψ = ip μ x p := by
  let D' : Submodule ℂ (bddSm (a := a) ω) := D.comap (bddSm ω).subtype
  haveI : FiniteDimensional ℂ D' := (Submodule.comapSubtypeEquivOfLe hD).symm.finiteDimensional
  obtain ⟨p, hp, h⟩ := exists_orth_of_core (core μ hω) D' ⟨ψ, hψ⟩
  refine ⟨p.1, hp, fun x hx => ?_⟩
  have h1 : ip μ x (ψ - p.1) = 0 := h ⟨x, hD hx⟩ hx
  rwa [ip_sub_right μ hω (hD hx) hψ p.2, sub_eq_zero] at h1

theorem exists_linear_proj (hω : ω.IsUnitary) {D W : Submodule ℂ (Sm E a)} (hD : D ≤ bddSm ω) (hW : W ≤ bddSm ω)
    (h : ∀ ψ ∈ W, ∃ p ∈ D, ∀ x ∈ D, ip μ x ψ = ip μ x p) :
    ∃ P : W →ₗ[ℂ] D, ∀ ψ : W, ∀ x ∈ D, ip μ x ψ.1 = ip μ x (P ψ).1 := by
  choose f hf hf' using h
  refine ⟨⟨⟨fun ψ => ⟨f ψ.1 ψ.2, hf _ _⟩, fun ψ ψ' => Subtype.ext ?_⟩, fun c ψ => Subtype.ext ?_⟩, fun ψ => hf' _ _⟩
  · refine eq_of_ip_eq μ hω hD (hf _ _) (add_mem (hf _ _) (hf _ _)) fun x hx => ?_
    rw [← hf' _ _ x hx]
    exact (ip_add_right μ hω (hD hx) (hW ψ.2) (hW ψ'.2)).trans
      ((congrArg₂ (· + ·) (hf' _ _ x hx) (hf' _ _ x hx)).trans (ip_add_right μ hω (hD hx) (hD (hf _ _)) (hD (hf _ _))).symm)
  · refine eq_of_ip_eq μ hω hD (hf _ _) (D.smul_mem _ (hf _ _)) fun x hx => ?_
    rw [← hf' _ _ x hx]
    exact (ip_smul_right μ c _ _).trans ((congrArg (conj c * ·) (hf' _ _ x hx)).trans (ip_smul_right μ c _ _).symm)

theorem ip_rt (hω : ω.IsUnitary) {φ ψ : Sm E a} (h : φ ∈ bddSm ω) (h' : ψ ∈ bddSm ω) (g : GA E a) :
    ip μ φ (rt E a g ψ) = ip μ (rt E a g⁻¹ φ) ψ := by
  have := pet_mul_right_left μ hω h h' g⁻¹
  rw [inv_inv] at this
  exact this.symm

theorem ip_rt_proj (hω : ω.IsUnitary) {D : Submodule ℂ (Sm E a)} (hD : D ≤ bddSm ω) {g : GA E a}
    (hg : ∀ x ∈ D, rt E a g⁻¹ x ∈ D) {ψ p : Sm E a} (hψ : ψ ∈ bddSm ω) (hp : p ∈ D)
    (e : ∀ x ∈ D, ip μ x ψ = ip μ x p) : ∀ x ∈ D, ip μ x (rt E a g ψ) = ip μ x (rt E a g p) := fun x hx => by
  rw [ip_rt μ hω (hD hx) hψ, ip_rt μ hω (hD hx) (hD hp), e _ (hg x hx)]

theorem finRep_cptRep (k : GL (Fin a) (Af E)) (c : Kinf E a) (φ : Sm E a) :
    finRep E a k (cptRep E a c φ) = cptRep E a c (finRep E a k φ) := by
  change (rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c))) φ =
    (rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)) φ
  rw [← map_mul, ← map_mul, infGL_comm]

theorem finite_orbit {K : Subgroup (GL (Fin a) (Af E))} (hK : IsCompact (K : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (h : IsOpen {k | finRep E a k φ = φ}) : (Set.range fun k : K => finRep E a k.1 φ).Finite := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  refine IsLocallyConstant.range_finite ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
  have hc : Continuous fun y : K => x.1⁻¹ * y.1 := continuous_const.mul continuous_subtype_val
  filter_upwards [(h.preimage hc).mem_nhds (by simp)] with y hy
  have hy' : finRep E a (x.1⁻¹ * y.1) φ = φ := hy
  conv_rhs => rw [← hy', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem exists_hull (π : CuspSub E a) {K : Subgroup (GL (Fin a) (Af E))} (hK : IsCompact (K : Set (GL (Fin a) (Af E))))
    {F : Submodule ℂ (Sm E a)} (hF : F ≤ π.V) [FiniteDimensional ℂ F] :
    ∃ D : Submodule ℂ (Sm E a), F ≤ D ∧ D ≤ π.V ∧ FiniteDimensional ℂ D ∧ (∀ k ∈ K, ∀ x ∈ D, finRep E a k x ∈ D) ∧
      ∀ c, ∀ x ∈ D, cptRep E a c x ∈ D := by
  obtain ⟨t, rfl⟩ := (Submodule.fg_iff_finiteDimensional F).2 inferInstance
  let T : Set (Sm E a) := ⋃ φ ∈ t, Set.range fun k : K => finRep E a k.1 φ
  have htV : ∀ φ ∈ t, φ ∈ π.V := fun φ hφ => hF (Submodule.subset_span hφ)
  have hT : T.Finite := t.finite_toSet.biUnion fun φ hφ => finite_orbit hK (π.cusp φ (htV φ hφ)).1.level
  have hTV : ∀ χ ∈ T, χ ∈ π.V := fun χ hχ => by
    simp only [T, Set.mem_iUnion] at hχ
    obtain ⟨φ, hφ, k, rfl⟩ := hχ
    exact π.stable (.fin k.1) φ (htV φ hφ)
  have hTK : ∀ k ∈ K, ∀ χ ∈ T, finRep E a k χ ∈ T := fun k hk χ hχ => by
    simp only [T, Set.mem_iUnion] at hχ ⊢
    obtain ⟨φ, hφ, k', rfl⟩ := hχ
    exact ⟨φ, hφ, ⟨k * k'.1, mul_mem hk k'.2⟩, by simp only [map_mul, Module.End.mul_apply]⟩
  haveI := hT.to_subtype
  haveI : ∀ χ : T, FiniteDimensional ℂ (LocEx.orbSpan χ.1) := fun χ => (π.cusp _ (hTV _ χ.2)).1.kfin
  refine ⟨⨆ χ : T, LocEx.orbSpan χ.1, Submodule.span_le.2 fun φ hφ => ?_, iSup_le fun χ => Submodule.span_le.2 ?_,
    inferInstance, fun k hk => ?_, fun c => ?_⟩
  · refine Submodule.mem_iSup_of_mem ⟨φ, ?_⟩ (Submodule.subset_span ⟨1, by simp⟩)
    simp only [T, Set.mem_iUnion]
    exact ⟨φ, hφ, 1, by simp⟩
  · rintro _ ⟨c, rfl⟩
    exact π.stable (.cpt c) _ (hTV _ χ.2)
  · change (⨆ χ : T, LocEx.orbSpan χ.1) ≤ Submodule.comap (finRep E a k) (⨆ χ : T, LocEx.orbSpan χ.1)
    refine iSup_le fun χ => Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    exact Submodule.mem_comap.2
      (Submodule.mem_iSup_of_mem ⟨_, hTK k hk _ χ.2⟩ (Submodule.subset_span ⟨c, (finRep_cptRep k c _).symm⟩))
  · change (⨆ χ : T, LocEx.orbSpan χ.1) ≤ Submodule.comap (cptRep E a c) (⨆ χ : T, LocEx.orbSpan χ.1)
    exact iSup_le fun χ x hx => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem χ (LocEx.orbSpan_stable _ c x hx))

theorem le_bddSm (hω : ω.IsUnitary) {π : CuspSub E a} (h : π.HasCentral ω) : π.V ≤ bddSm ω := fun _ hφ =>
  mem_bddForms_of_cuspSub cuspFormsBounded hω (CuspSub.hasCentral_iff.1 h) hφ

theorem exists_cap_scalar (π : CuspSub E a) : ∃ c : (E →+* ℂ) → ℂ → ℂ, ∀ τ u, ∀ φ ∈ π.V, cap τ u φ = c τ u • φ := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ π.V, cap τ u φ = c • φ := fun τ u =>
    π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  exact ⟨c, hc⟩

theorem exists_proj (hω : ω.IsUnitary) {π : CuspSub E a} (hπ : π.HasCentral ω) {ψ : Sm E a} (hψ : ψ ∈ bddSm ω)
    (hA : IsAutForm ψ) : ∃ p ∈ π.V, ∀ x ∈ π.V, ip μ x ψ = ip μ x p := by
  have hV := le_bddSm hω hπ
  obtain ⟨c, hc⟩ := exists_cap_scalar π
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  let K : Subgroup (GL (Fin a) (Af E)) := U ⊓ LocEx.stab (finRep E a) ψ
  have hKo : IsOpen (K : Set (GL (Fin a) (Af E))) := hUo.inter hA.level
  have hKc : IsCompact (K : Set (GL (Fin a) (Af E))) :=
    hUc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_left
  let O := LocEx.orbSpan ψ
  haveI : FiniteDimensional ℂ O := hA.kfin
  have hO : O ≤ bddSm ω := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact mul_right_mem_bddForms hψ _)
  have hψO : ψ ∈ O := Submodule.subset_span ⟨1, by simp⟩
  let ρ₀ := GlobalTheory.PRep.sub (cptRep E a) O (LocEx.orbSpan_stable ψ)
  have hρc : AutFin.IsContRep ρ₀ := LocEx.isContRep_sub _ _
  have key : ∀ D : Submodule ℂ (Sm E a), D ≤ π.V → FiniteDimensional ℂ D → (∀ k ∈ K, ∀ x ∈ D, finRep E a k x ∈ D) →
      (∀ k, ∀ x ∈ D, cptRep E a k x ∈ D) →
      ∃ p ∈ D, p ∈ AutFinGL.forms K ρ₀ c ∧ ∀ x ∈ D, ip μ x ψ = ip μ x p := by
    intro D hD _ h1 h2
    have hDb := hD.trans hV
    obtain ⟨Q, hQ⟩ := exists_linear_proj μ hω hDb hO fun χ hχ => exists_proj_of_finite μ hω hDb (hO hχ)
    refine ⟨(Q ⟨ψ, hψO⟩).1, (Q _).2, ⟨(π.cusp _ (hD (Q _).2)).1, fun k hk => ?_, fun g => ?_,
      fun τ u => hc τ u _ (hD (Q _).2)⟩, hQ ⟨ψ, hψO⟩⟩
    · refine eq_of_ip_eq μ hω hDb (h1 k hk _ (Q _).2) (Q _).2 fun x hx => ?_
      have e := ip_rt_proj μ hω hDb (g := finGL E a k) (fun y hy => by
        rw [← map_inv]; exact h1 _ (inv_mem hk) y hy) hψ (Q ⟨ψ, hψO⟩).2 (hQ ⟨ψ, hψO⟩) x hx
      have e2 : rt E a (finGL E a k) ψ = ψ := hk.2
      rw [e2] at e
      exact e.symm.trans (hQ ⟨ψ, hψO⟩ x hx)
    · refine AutFinGL.type_of_map ρ₀ (D.subtype ∘ₗ Q) (fun k w => ?_) ⟨ψ, hψO⟩ g
      refine eq_of_ip_eq μ hω hDb (Q _).2 (h2 k _ (Q _).2) fun x hx => ?_
      exact (hQ _ x hx).symm.trans (ip_rt_proj μ hω hDb (g := infGL E a (Unitary.toUnits k)) (fun y hy => by
        rw [← map_inv, ← map_inv]; exact h2 _ y hy) (hO w.2) (Q w).2 (hQ w) x hx)
  let F : Submodule ℂ (Sm E a) := π.V ⊓ Submodule.span ℂ (AutFinGL.forms K ρ₀ c)
  haveI := GlobalTheory.automorphicFormsFiniteGL E a K hKo O ρ₀ hρc c
  haveI : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le inf_le_right
  have hFb : F ≤ bddSm ω := inf_le_left.trans hV
  obtain ⟨p, hp, hp'⟩ := exists_proj_of_finite μ hω hFb hψ
  refine ⟨p, hp.1, fun φ hφ => ?_⟩
  obtain ⟨D, h0, hD, hfin, h1, h2⟩ := exists_hull π hKc (F := F ⊔ ℂ ∙ φ)
    (sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).2 hφ))
  obtain ⟨q, hq, hq1, hq2⟩ := key D hD hfin h1 h2
  have e : p = q := eq_of_ip_eq μ hω hFb hp ⟨hD hq, Submodule.subset_span hq1⟩ fun x hx =>
    (hp' x hx).symm.trans (hq2 x (h0 (Submodule.mem_sup_left hx)))
  rw [e]
  exact hq2 φ (h0 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self φ)))

theorem exists_equivariant_proj (hω : ω.IsUnitary) {π π' : CuspSub E a} (hπ : π.HasCentral ω) (hπ' : π'.HasCentral ω) :
    ∃ P : π'.V →ₗ[ℂ] π.V, (∀ o ψ, P (π'.op o ψ) = π.op o (P ψ)) ∧
      ∀ ψ : π'.V, ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ.1.1 = pet (latticeGL E a) μ φ.1 (P ψ).1.1 := by
  have hV := le_bddSm hω hπ
  have hV' := le_bddSm hω hπ'
  obtain ⟨P, hP⟩ := exists_linear_proj μ hω hV hV' fun ψ hψ => exists_proj μ hω hπ (hV' hψ) (π'.cusp ψ hψ).1
  refine ⟨P, fun o ψ => Subtype.ext (eq_of_ip_eq μ hω hV (P _).2 (π.op o _).2 fun x hx => ?_), hP⟩
  refine (hP _ x hx).symm.trans ?_
  cases o with
  | fin k =>
    exact ip_rt_proj μ hω hV (g := finGL E a k) (fun y hy => by
      rw [← map_inv]; exact π.stable (.fin _) y hy) (hV' ψ.2) (P ψ).2 (hP ψ) x hx
  | cpt k =>
    exact ip_rt_proj μ hω hV (g := infGL E a (Unitary.toUnits k)) (fun y hy => by
      rw [← map_inv, ← map_inv]; exact π.stable (.cpt _) y hy) (hV' ψ.2) (P ψ).2 (hP ψ) x hx
  | lie X =>
    have hx' := π.stable (.lie X) x hx
    have e1 := pet_lie μ hω X (hV hx) (hV' ψ.2) (hV hx') (hV' (π'.stable (.lie X) _ ψ.2))
    have e2 := pet_lie μ hω X (hV hx) (hV (P ψ).2) (hV hx') (hV (π.stable (.lie X) _ (P ψ).2))
    exact neg_injective (e1.symm.trans ((hP ψ _ hx').trans e2))

theorem exists_cuspSub_range (π : CuspSub E a) (S : π.V →ₗ[ℂ] Sm E a) (hS : ∀ o φ, S (π.op o φ) = act o (S φ))
    (h0 : S ≠ 0) (hc : ∀ φ, IsCuspForm (S φ)) : ∃ σ : CuspSub E a, σ.V = LinearMap.range S ∧ π.Iso σ := by
  have sub : ∀ W : Submodule ℂ π.V, (∀ o, ∀ φ ∈ W, π.op o φ ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW => by
    have h := π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨φ, hφ, rfl⟩
      exact ⟨_, hW o φ hφ, rfl⟩)
    refine h.imp (fun h => ?_) fun h => ?_
    · exact Submodule.map_injective_of_injective π.V.injective_subtype (h.trans (Submodule.map_bot _).symm)
    · exact Submodule.map_injective_of_injective π.V.injective_subtype (h.trans (Submodule.map_subtype_top _).symm)
  have hinj : Function.Injective S := LinearMap.ker_eq_bot.1 <|
    (sub (LinearMap.ker S) fun o φ hφ => by
      rw [LinearMap.mem_ker] at hφ ⊢
      rw [hS, hφ, map_zero]).resolve_right fun h => h0 (LinearMap.ker_eq_top.1 h)
  refine ⟨⟨LinearMap.range S, ?_, ?_, fun h => h0 (LinearMap.range_eq_bot.1 h), fun W hW hs => ?_⟩, rfl,
    LinearEquiv.ofInjective S hinj, fun o φ => Subtype.ext (hS o φ)⟩
  · rintro _ ⟨φ, rfl⟩
    exact hc φ
  · rintro o _ ⟨φ, rfl⟩
    exact ⟨_, hS o φ⟩
  · have e : (W.comap S).map S = W := Submodule.map_comap_eq_self hW
    refine (sub (W.comap S) fun o φ hφ => ?_).imp (fun h => ?_) fun h => ?_
    · rw [Submodule.mem_comap, hS]
      exact hs o _ hφ
    · rw [← e, h, Submodule.map_bot]
    · rw [← e, h, Submodule.map_top]

theorem pet_eq_zero_of_mk_ne (hω : ω.IsUnitary) {π π' : CuspSub E a} (hπ : π.HasCentral ω) (hπ' : π'.HasCentral ω)
    (hne : CG.mk π ≠ CG.mk π') : ∀ φ ∈ π.V, ∀ φ' ∈ π'.V, pet (latticeGL E a) μ φ.1 φ'.1 = 0 := by
  obtain ⟨P, hP, hP'⟩ := exists_equivariant_proj μ hω hπ hπ'
  have h0 : π.V.subtype ∘ₗ P = 0 := by
    by_contra h0
    obtain ⟨σ, hσ, hi⟩ := exists_cuspSub_range π' (π.V.subtype ∘ₗ P)
      (fun o φ => congrArg Subtype.val (hP o φ)) h0 fun φ => π.cusp _ (P φ).2
    have hle : σ.V ≤ π.V := by
      rw [hσ]
      rintro _ ⟨φ, rfl⟩
      exact (P φ).2
    have e : σ = π := CuspSub.ext ((π.irred _ hle σ.stable).resolve_left σ.ne_bot)
    exact hne (Quotient.sound (e ▸ hi : π'.Iso π)).symm
  intro φ hφ φ' hφ'
  have e : (P ⟨φ', hφ'⟩).1 = (0 : ℂ) • φ := (LinearMap.congr_fun h0 ⟨φ', hφ'⟩).trans (zero_smul ℂ φ).symm
  refine (hP' ⟨φ', hφ'⟩ φ hφ).trans ?_
  rw [e]
  exact (ip_smul_right μ 0 φ φ).trans (by simp)

end GlobalTheory.CuspOrth

end
