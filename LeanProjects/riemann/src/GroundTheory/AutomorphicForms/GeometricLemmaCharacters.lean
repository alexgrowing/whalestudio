import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
import GroundTheory.AutomorphicForms.CuspidalAdmissible
import GroundTheory.AutomorphicForms.JacquetAdmissible
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Diagonal

variable {γ δ : Fin n → ℕ}

theorem diagPow_mem_levi_inf_blockUpper (μ : Fin n → ℤ) :
    Cartan.diagPow F n μ ∈ levi F n γ ⊓ blockUpper F n δ :=
  ⟨diagPow_mem_levi μ, levi_le_blockUpper (diagPow_mem_levi (β := δ) μ)⟩

theorem exists_diagPow_eq (h : ↥(levi F n γ ⊓ blockUpper F n δ)) :
    ∃ μ : Fin n → ℤ, ∀ {M : Type*} [CommMonoid M] (ψ : ↥(levi F n γ ⊓ blockUpper F n δ) →* M),
      (∀ k : ↥(levi F n γ ⊓ blockUpper F n δ), (k : GL (Fin n) F) ∈ integralGL F n → ψ k = 1) →
        ψ h = ψ ⟨Cartan.diagPow F n μ, diagPow_mem_levi_inf_blockUpper μ⟩ := by
  classical
  let H : Subgroup (GL (Fin n) F) := levi F n γ ⊓ blockUpper F n δ

  have hhδ : (h : GL (Fin n) F) ∈ blockUpper F n δ := h.2.2
  set ℓ : levi F n δ := leviProj F n δ ⟨h, hhδ⟩
  let ρ : Fin n → ℕ ×ₗ ℕ := fun i => toLex (γ i, δ i)
  have hℓρ : (ℓ : GL (Fin n) F) ∈ levi F n ρ := by
    rw [mem_levi]
    intro i j hij
    show ((leviProj F n δ ⟨h, hhδ⟩ : levi F n δ) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs with hδ
    · have hγ : γ i ≠ γ j := fun hγ => hij (by simp [ρ, hγ, hδ])
      exact (mem_levi.1 h.2.1) i j hγ
    · rfl
  have hρH : ∀ {g : GL (Fin n) F}, g ∈ levi F n ρ → g ∈ H := by
    intro g hg
    refine ⟨mem_levi.2 fun i j hij => (mem_levi.1 hg) i j fun e => hij ?_,
      levi_le_blockUpper (mem_levi.2 fun i j hij => (mem_levi.1 hg) i j fun e => hij ?_)⟩
    · have := congrArg (fun x : ℕ ×ₗ ℕ => (ofLex x).1) e
      simpa [ρ] using this
    · have := congrArg (fun x : ℕ ×ₗ ℕ => (ofLex x).2) e
      simpa [ρ] using this
  obtain ⟨μ, k₁, hk₁, k₂, hk₂, hℓ⟩ := exists_eq_mul_diagPow_mul_levi hℓρ
  refine ⟨μ, fun {M} _ ψ hψ => ?_⟩

  set u := (ℓ : GL (Fin n) F)⁻¹ * h
  have hℓH : (ℓ : GL (Fin n) F) ∈ H := hρH hℓρ
  have huH : u ∈ H := H.mul_mem (H.inv_mem hℓH) h.2
  have huN : u ∈ unipotentRadical F n δ := by
    rw [show u = ((leviIncl ℓ)⁻¹ * ⟨h, hhδ⟩ : blockUpper F n δ) from rfl]
    exact leviProj_inv_mul_mem _
  obtain ⟨e, he⟩ := exists_unipotentCompactG_of_isCompact (γ := δ)
    (isCompact_singleton (x := u)) (by simpa using huN)
  set t := rankTorus F n δ e
  have htH : t ∈ H := ⟨diagGL_mem_levi _, rankTorus_mem_blockUpper e⟩
  have hk : t * u * t⁻¹ ∈ integralGL F n := (mem_unipotentCompactG.1 (he rfl)).2
  have hψu : ψ ⟨u, huH⟩ = 1 := by
    have hkH : t * u * t⁻¹ ∈ H := H.mul_mem (H.mul_mem htH huH) (H.inv_mem htH)
    have h1 := hψ ⟨t * u * t⁻¹, hkH⟩ hk
    have : (⟨u, huH⟩ : H) = ⟨t, htH⟩⁻¹ * ⟨t * u * t⁻¹, hkH⟩ * ⟨t, htH⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [this, map_mul, map_mul, h1, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have hh : h = ⟨k₁, hρH hk₁.1⟩ * ⟨Cartan.diagPow F n μ, diagPow_mem_levi_inf_blockUpper μ⟩ *
      ⟨k₂, hρH hk₂.1⟩ * ⟨u, huH⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hℓ]
    simp [u]
  rw [hh, map_mul, map_mul, map_mul, hψu, hψ ⟨k₁, hρH hk₁.1⟩ hk₁.2, hψ ⟨k₂, hρH hk₂.1⟩ hk₂.2,
    one_mul, mul_one, mul_one]

end Diagonal

section PermConjUnipotent

variable {γ : Fin n → ℕ}

theorem permGL_conj_apply (w : Equiv.Perm (Fin n)) (g : GL (Fin n) F) (r c : Fin n) :
    ((permGL F w * g * (permGL F w)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
      (g : Matrix (Fin n) (Fin n) F) (w⁻¹ r) (w⁻¹ c) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, mul_permGL_apply, permGL_mul_apply]

theorem conj_permGL_mem_unipotentRadical_iff (w : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permGL F w * g * (permGL F w)⁻¹ ∈ unipotentRadical F n (γ ∘ ⇑w⁻¹) ↔
      g ∈ unipotentRadical F n γ := by
  have hγ : (γ ∘ ⇑w⁻¹) ∘ ⇑w = γ := by
    funext i
    simp
  rw [mem_unipotentRadical, mem_unipotentRadical, conj_permGL_mem_blockUpper_iff, hγ]
  refine and_congr_right fun _ => ⟨fun h i j hij => ?_, fun h r c hrc => ?_⟩
  · have := h (w i) (w j) (by simpa using hij)
    rw [permGL_conj_apply] at this
    simpa [Matrix.one_apply] using this
  · rw [permGL_conj_apply, h _ _ hrc]
    simp [Matrix.one_apply]

end PermConjUnipotent

section CellCoinv

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem leviProj_permConj_mem_unipotentRadical (a : cellUnipotent F β γ w) :
    ((leviProj F n β (permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper a)) :
      levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n (γ ∘ ⇑w⁻¹) := by
  have hx : permGL F w * (a : GL (Fin n) F) * (permGL F w)⁻¹ ∈ unipotentRadical F n (γ ∘ ⇑w⁻¹) :=
    (conj_permGL_mem_unipotentRadical_iff w).2 a.2.1
  obtain ⟨hxP, hx1⟩ := mem_unipotentRadical.1 hx
  refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · show ((leviProj F n β _ : levi F n β) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs
    · exact hxP hij
    · rfl
  · rw [leviProj_apply]
    split_ifs with hβ
    · exact hx1 i j hij
    · have hne : i ≠ j := fun e => hβ (e ▸ rfl)
      rw [Matrix.one_apply_ne hne]

theorem cellRepA_apply_eq (a : cellUnipotent F β γ w) (v : W) :
    cellRepA β γ w σ a v =
      σ (leviProj F n β (permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper a))) v := by
  rw [cellRepA, MonoidHom.coe_comp, Function.comp_apply, cellRep_apply, inflateTwist_apply]
  set p := permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper a)
  have h1 : sqrtModular F n β p = 1 := by
    rw [← sqrtModular_leviProj p]
    exact sqrtModular_leviIncl_of_mem _ (leviProj_permConj_mem_unipotentRadical a)
  rw [h1, one_smul]

variable (β γ w) in

abbrev innerJacquetSpace : Type _ :=
  Representation.Coinvariants (σ.comp (leviUnipotent F n β (γ ∘ ⇑w⁻¹)).subtype)

theorem exists_cellUnipotent_of_leviUnipotent (x : leviUnipotent F n β (γ ∘ ⇑w⁻¹)) :
    ∃ a : cellUnipotent F β γ w,
      leviProj F n β (permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper a)) = x := by
  have hxN : ((x : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n (γ ∘ ⇑w⁻¹) :=
    Subgroup.mem_subgroupOf.1 x.2
  set a := (permGL F w)⁻¹ * ((x : levi F n β) : GL (Fin n) F) * permGL F w
  have hconj : permGL F w * a * (permGL F w)⁻¹ = ((x : levi F n β) : GL (Fin n) F) := by
    simp only [a]
    group
  have haN : a ∈ unipotentRadical F n γ := by
    rw [← conj_permGL_mem_unipotentRadical_iff w, hconj]
    exact hxN
  have haP : a ∈ blockUpper F n (β ∘ w) := by
    rw [← conj_permGL_mem_blockUpper_iff w, hconj]
    exact levi_le_blockUpper (x : levi F n β).2
  refine ⟨⟨a, haN, haP⟩, ?_⟩
  apply Subtype.ext
  have : ((permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper ⟨a, haN, haP⟩) :
      blockUpper F n β) : GL (Fin n) F) = ((x : levi F n β) : GL (Fin n) F) := hconj
  have hp : permConj F β w (Subgroup.inclusion cellUnipotent_le_blockUpper ⟨a, haN, haP⟩) =
      ⟨((x : levi F n β) : GL (Fin n) F), levi_le_blockUpper (x : levi F n β).2⟩ :=
    Subtype.ext this
  rw [hp, leviProj_of_mem_levi (x : levi F n β).2]

variable (β γ w) in

def cellCoinvEquiv : Representation.Coinvariants (cellRepA β γ w σ) ≃ₗ[ℂ]
    innerJacquetSpace β γ w σ where
  toFun := Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _) fun a => by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [cellRepA_apply_eq]
    exact Representation.Coinvariants.mk_self_apply
      (σ.comp (leviUnipotent F n β (γ ∘ ⇑w⁻¹)).subtype)
      ⟨_, Subgroup.mem_subgroupOf.2 (leviProj_permConj_mem_unipotentRadical a)⟩ v
  invFun := Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _) fun x => by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
      Subgroup.coe_subtype]
    obtain ⟨a, ha⟩ := exists_cellUnipotent_of_leviUnipotent (β := β) (γ := γ) (w := w) x
    rw [← ha, ← cellRepA_apply_eq]
    exact Representation.Coinvariants.mk_self_apply _ a v
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    rfl
  right_inv x := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    rfl

theorem cellCoinvEquiv_mk (v : W) :
    cellCoinvEquiv β γ w σ (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ v := rfl

end CellCoinv

section InnerAction

variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

variable (β) in

def leviInfIncl (δ : Fin n → ℕ) : (levi F n β ⊓ blockUpper F n δ : Subgroup (GL (Fin n) F)) →* levi F n β where
  toFun x := ⟨x, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem leviInfIncl_conj_mem {δ : Fin n → ℕ} (x : (levi F n β ⊓ blockUpper F n δ : Subgroup (GL (Fin n) F)))
    (u : leviUnipotent F n β δ) :
    leviInfIncl β δ x * (u : levi F n β) * (leviInfIncl β δ x)⁻¹ ∈ leviUnipotent F n β δ := by
  refine Subgroup.mem_subgroupOf.2 ?_
  show (x : GL (Fin n) F) * (((u : levi F n β)) : GL (Fin n) F) * (x : GL (Fin n) F)⁻¹ ∈ _
  exact conj_mem_unipotentRadical x.2.2 (Subgroup.mem_subgroupOf.1 u.2)

variable (β) in

def levJacquetAction (δ : Fin n → ℕ) :
    Representation ℂ (levi F n β ⊓ blockUpper F n δ : Subgroup (GL (Fin n) F))
      (Representation.Coinvariants (σ.comp (leviUnipotent F n β δ).subtype)) where
  toFun x := Representation.Coinvariants.lift _
    ((Representation.Coinvariants.mk _) ∘ₗ σ (leviInfIncl β δ x)) fun u => by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp, Subgroup.coe_subtype]
      have h : σ (leviInfIncl β δ x) (σ (u : levi F n β) v) =
          σ (leviInfIncl β δ x * (u : levi F n β) * (leviInfIncl β δ x)⁻¹)
            (σ (leviInfIncl β δ x) v) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        group
      rw [h]
      exact Representation.Coinvariants.mk_self_apply
        (σ.comp (leviUnipotent F n β δ).subtype) ⟨_, leviInfIncl_conj_mem x u⟩ _
  map_one' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by simp)
  map_mul' x y := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
    simp [Module.End.mul_apply])

theorem levJacquetAction_mk {δ : Fin n → ℕ}
    (x : (levi F n β ⊓ blockUpper F n δ : Subgroup (GL (Fin n) F))) (v : W) :
    levJacquetAction β σ δ x (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (σ (leviInfIncl β δ x) v) := rfl

end InnerAction

section Compat

variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem leviProj_permConj_mem (b : cellLeviParabolic F β γ w) :
    ((leviProj F n β (permConj F β w (Subgroup.inclusion cellLeviParabolic_le_blockUpper b)) :
      levi F n β) : GL (Fin n) F) ∈ levi F n β ⊓ blockUpper F n (γ ∘ ⇑w⁻¹) := by
  refine ⟨(leviProj F n β _).2, fun i j hij => ?_⟩
  show ((leviProj F n β _ : levi F n β) : GL (Fin n) F) i j = 0
  rw [leviProj_apply]
  split_ifs
  · show ((permGL F w * (b : GL (Fin n) F) * (permGL F w)⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j = 0
    rw [permGL_conj_apply]
    exact (mem_levi.1 b.2.1) _ _ fun e => (ne_of_lt hij) (by simpa using e.symm)
  · rfl

variable (β γ w) in

def cellInnerHom : cellLeviParabolic F β γ w →*
    (levi F n β ⊓ blockUpper F n (γ ∘ ⇑w⁻¹) : Subgroup (GL (Fin n) F)) where
  toFun b := ⟨_, leviProj_permConj_mem b⟩
  map_one' := Subtype.ext (by simp)
  map_mul' b b' := Subtype.ext (by simp)

theorem cellCoinvEquiv_cellCoinvRep (b : cellLeviParabolic F β γ w)
    (x : Representation.Coinvariants (cellRepA β γ w σ)) :
    cellCoinvEquiv β γ w σ (cellCoinvRep σ b x) =
      sqrtModular F n β (permConj F β w (Subgroup.inclusion cellLeviParabolic_le_blockUpper b)) •
        levJacquetAction β σ (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w b) (cellCoinvEquiv β γ w σ x) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  rw [cellCoinvRep_mk, cellCoinvEquiv_mk, cellCoinvEquiv_mk, levJacquetAction_mk, ← map_smul]
  rfl

end Compat

section Induced

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {ρ₁ : Representation ℂ H V₁} {ρ₂ : Representation ℂ H V₂}

def indCongr (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ h v, e (ρ₁ h v) = ρ₂ h (e v)) :
    indSpace H ρ₁ ≃ₗ[ℂ] indSpace H ρ₂ where
  toFun φ := ⟨fun g => e ((φ : G → V₁) g), by
    obtain ⟨h1, K, hK, hKφ⟩ := (mem_indSpace).1 φ.2
    exact (mem_indSpace).2 ⟨fun h g => by rw [h1 h g, he], K, hK, fun k hk g => by rw [hKφ k hk g]⟩⟩
  invFun ψ := ⟨fun g => e.symm ((ψ : G → V₂) g), by
    obtain ⟨h1, K, hK, hKψ⟩ := (mem_indSpace).1 ψ.2
    refine (mem_indSpace).2 ⟨fun h g => ?_, K, hK, fun k hk g => by rw [hKψ k hk g]⟩
    rw [h1 h g]
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
  map_add' φ φ' := Subtype.ext (funext fun g => by simp)
  map_smul' c φ := Subtype.ext (funext fun g => by simp)
  left_inv φ := Subtype.ext (funext fun g => by simp)
  right_inv ψ := Subtype.ext (funext fun g => by simp)

theorem coe_indCongr_apply (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ h v, e (ρ₁ h v) = ρ₂ h (e v))
    (φ : indSpace H ρ₁) (g : G) : ((indCongr e he φ : indSpace H ρ₂) : G → V₂) g = e ((φ : G → V₁) g) :=
  rfl

theorem indCongr_indRep (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ h v, e (ρ₁ h v) = ρ₂ h (e v)) (g : G)
    (φ : indSpace H ρ₁) :
    indCongr e he (indRep H ρ₁ g φ) = indRep H ρ₂ g (indCongr e he φ) :=
  Subtype.ext (funext fun x => by rw [coe_indCongr_apply, coe_indRep_apply, coe_indRep_apply,
    coe_indCongr_apply])

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}

def indTwist (χ : G →* ℂ) (hχ : ∀ g, χ g ≠ 0)
    (hχo : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, χ u = 1) :
    indSpace H ρ ≃ₗ[ℂ] indSpace H (twist (χ.comp H.subtype) ρ) where
  toFun φ := ⟨fun g => χ g • (φ : G → V) g, by
    obtain ⟨h1, K, hK, hKφ⟩ := (mem_indSpace).1 φ.2
    obtain ⟨U, hU, hUχ⟩ := hχo
    refine (mem_indSpace).2 ⟨fun h g => ?_, K ⊓ U, ?_, fun k hk g => ?_⟩
    · rw [map_mul, h1 h g, twist_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, map_smul,
        smul_smul]
    · rw [Subgroup.coe_inf]
      exact hK.inter hU
    · rw [map_mul, hUχ k hk.2, mul_one, hKφ k hk.1 g]⟩
  invFun ψ := ⟨fun g => (χ g)⁻¹ • (ψ : G → V) g, by
    obtain ⟨h1, K, hK, hKψ⟩ := (mem_indSpace).1 ψ.2
    obtain ⟨U, hU, hUχ⟩ := hχo
    refine (mem_indSpace).2 ⟨fun h g => ?_, K ⊓ U, ?_, fun k hk g => ?_⟩
    · rw [h1 h g, twist_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, smul_smul,
        map_smul]
      congr 1
      have h₁ := hχ h
      have h₂ := hχ g
      field_simp
    · rw [Subgroup.coe_inf]
      exact hK.inter hU
    · rw [map_mul, hUχ k hk.2, mul_one, hKψ k hk.1 g]⟩
  map_add' φ φ' := Subtype.ext (funext fun g => by simp)
  map_smul' c φ := Subtype.ext (funext fun g => by simp [smul_comm (χ g) c])
  left_inv φ := Subtype.ext (funext fun g => by simp [smul_smul, inv_mul_cancel₀ (hχ g)])
  right_inv ψ := Subtype.ext (funext fun g => by simp [smul_smul, mul_inv_cancel₀ (hχ g)])

theorem coe_indTwist_apply (χ : G →* ℂ) (hχ : ∀ g, χ g ≠ 0)
    (hχo : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, χ u = 1) (φ : indSpace H ρ) (g : G) :
    ((indTwist χ hχ hχo φ : indSpace H (twist (χ.comp H.subtype) ρ)) : G → V) g =
      χ g • (φ : G → V) g := rfl

theorem indTwist_twist (χ : G →* ℂ) (hχ : ∀ g, χ g ≠ 0)
    (hχo : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, χ u = 1) (g : G) (φ : indSpace H ρ) :
    indTwist χ hχ hχo (twist χ (indRep H ρ) g φ) =
      indRep H (twist (χ.comp H.subtype) ρ) g (indTwist χ hχ hχo φ) :=
  Subtype.ext (funext fun x => by
    rw [coe_indTwist_apply, coe_indRep_apply, coe_indTwist_apply, twist_apply,
      Submodule.coe_smul, Pi.smul_apply, coe_indRep_apply, smul_smul, map_mul])

end Induced

end Parabolic

end GroundTheory.Automorphic
