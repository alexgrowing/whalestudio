import Mathlib
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

noncomputable section

open ReciprocityTheory.Gal

namespace UpperTheory.V.Base

section Eig

variable {R Q N : Type} [CommRing R] [Group Q] [AddCommGroup N] [Module R N]

def eig (π : Representation R Q N) (ψ : Q →* Rˣ) : Submodule R N :=
  ⨅ g, LinearMap.ker (π g - ((ψ g : Rˣ) : R) • LinearMap.id)

theorem mem_eig {π : Representation R Q N} {ψ : Q →* Rˣ} {x : N} :
    x ∈ eig π ψ ↔ ∀ g, π g x = ((ψ g : Rˣ) : R) • x := by
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem eig_one (π : Representation R Q N) : eig π 1 = π.invariants := by
  ext x
  rw [mem_eig, Representation.mem_invariants]
  simp

def coeig (π : Representation R Q N) (ψ : Q →* Rˣ) : Submodule R N :=
  ⨆ g, LinearMap.range (π g - ((ψ g : Rˣ) : R) • LinearMap.id)

end Eig

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

abbrev H1U (ρ : Representation R G M) (U : Subgroup G) : Type := H1 (ρ.comp U.subtype : Representation R U M)

abbrev Z1U (ρ : Representation R G M) (U : Subgroup G) : Submodule R (U → M) :=
  Z1 (ρ.comp U.subtype : Representation R U M)

abbrev H0U (ρ : Representation R G M) (U : Subgroup G) : Submodule R M :=
  H0 (ρ.comp U.subtype : Representation R U M)

def resU (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) : H1U ρ U →ₗ[R] H1U ρ U' :=
  pairH1DecompositionMap _ _ (Subgroup.inclusion h) (continuous_inclusion h) LinearMap.id continuous_id fun _ _ => rfl

theorem resU_mk (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ U', resU ρ h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U', z'.1 u = z.1 ⟨u.1, h u.2⟩ := ⟨_, rfl, fun _ => rfl⟩

theorem mk_eq_mk (ρ : Representation R G M) (U : Subgroup G) (z z' : Z1U ρ U) :
    (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk z' ↔
      ∃ m, ∀ u : U, z.1 u - z'.1 u = ρ u m - m := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  exact Iff.rfl

theorem resU_mk_eq_zero (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (z : Z1U ρ U) :
    resU ρ h (Submodule.Quotient.mk z) = 0 ↔ ∃ m, ∀ u : U', z.1 ⟨u.1, h u.2⟩ = ρ u m - m := by
  obtain ⟨z', e, f⟩ := resU_mk ρ h z
  rw [e, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  exact exists_congr fun m => forall_congr' fun u => by rw [f u]; rfl

theorem resU_resU (ρ : Representation R G M) {U'' U' U : Subgroup G} (h' : U'' ≤ U') (h : U' ≤ U) (x : H1U ρ U) :
    resU ρ h' (resU ρ h x) = resU ρ (h'.trans h) x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := resU_mk ρ h z
  obtain ⟨z₂, e₂, f₂⟩ := resU_mk ρ h' z₁
  obtain ⟨z₃, e₃, f₃⟩ := resU_mk ρ (h'.trans h) z
  rw [e₁, e₂, e₃]
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  rw [f₂, f₁, f₃]

def LocSel (ρ : Representation R G M) (U : Subgroup G) (𝒟 : Set (Subgroup G)) : Submodule R (H1U ρ U) :=
  ⨅ D ∈ 𝒟, LinearMap.ker (resU ρ (inf_le_left : U ⊓ D ≤ U))

theorem mem_locSel {ρ : Representation R G M} {U : Subgroup G} {𝒟 : Set (Subgroup G)} {x : H1U ρ U} :
    x ∈ LocSel ρ U 𝒟 ↔ ∀ D ∈ 𝒟, resU ρ (inf_le_left : U ⊓ D ≤ U) x = 0 := by
  simp only [LocSel, Submodule.mem_iInf, LinearMap.mem_ker]

theorem mk_mem_locSel {ρ : Representation R G M} {U : Subgroup G} {𝒟 : Set (Subgroup G)} {z : Z1U ρ U} :
    Submodule.Quotient.mk z ∈ LocSel ρ U 𝒟 ↔ ∀ D ∈ 𝒟, ∃ m, ∀ u : U, u.1 ∈ D → z.1 u = ρ u m - m := by
  rw [mem_locSel]
  refine forall₂_congr fun D _ => ?_
  rw [resU_mk_eq_zero]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, fun u hu => hm ⟨u.1, Subgroup.mem_inf.mpr ⟨u.2, hu⟩⟩⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, fun u => hm ⟨u.1, (Subgroup.mem_inf.mp u.2).1⟩ (Subgroup.mem_inf.mp u.2).2⟩

theorem resU_mem_locSel {ρ : Representation R G M} {U' U : Subgroup G} (h : U' ≤ U) {𝒟 : Set (Subgroup G)}
    {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) : resU ρ h x ∈ LocSel ρ U' 𝒟 := by
  rw [mem_locSel] at hx ⊢
  intro D hD
  have hle : U' ⊓ D ≤ U ⊓ D := inf_le_inf_right D h
  calc resU ρ (inf_le_left : U' ⊓ D ≤ U') (resU ρ h x)
      = resU ρ ((inf_le_left : U' ⊓ D ≤ U').trans h) x := resU_resU ρ _ h x
    _ = resU ρ hle (resU ρ (inf_le_left : U ⊓ D ≤ U) x) := (resU_resU ρ hle inf_le_left x).symm
    _ = 0 := by rw [hx D hD, map_zero]

def selRes (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (𝒟 : Set (Subgroup G)) :
    LocSel ρ U 𝒟 →ₗ[R] LocSel ρ U' 𝒟 :=
  (resU ρ h).restrict fun _ hx => resU_mem_locSel h hx

def ConjStable (𝒟 : Set (Subgroup G)) : Prop :=
  ∀ D ∈ 𝒟, ∀ g : G, ∃ D' ∈ 𝒟, ∀ x, x ∈ D ↔ g⁻¹ * x * g ∈ D'

abbrev quotRep (ρ : Representation R G M) (U U' : Subgroup G) [(U'.subgroupOf U).Normal] :=
  Representation.quotientToInvariants (ρ.comp U.subtype : Representation R U M) (U'.subgroupOf U)

section Conj

variable [IsTopologicalGroup G] [DiscreteTopology M]

def conjHom (U : Subgroup G) [hU : U.Normal] (g : G) : U →* U where
  toFun u := ⟨g⁻¹ * u * g, by simpa using hU.conj_mem u u.2 g⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem continuous_conjHom (U : Subgroup G) [U.Normal] (g : G) : Continuous (conjHom U g) := by
  refine continuous_induced_rng.2 ?_
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

def conjU (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) : H1U ρ U →ₗ[R] H1U ρ U :=
  pairH1DecompositionMap _ _ (conjHom U g) (continuous_conjHom U g) (ρ g) continuous_of_discreteTopology fun u m => by
    show ρ g (ρ (g⁻¹ * u * g) m) = ρ u (ρ g m)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]

theorem conjU_mk (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ U, conjU ρ U g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U, z'.1 u = ρ g (z.1 (conjHom U g u)) := ⟨_, rfl, fun _ => rfl⟩

def conjRep (ρ : Representation R G M) (U : Subgroup G) [U.Normal] : Representation R G (H1U ρ U) where
  toFun := conjU ρ U
  map_one' := LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z', e, f⟩ := conjU_mk ρ U 1 z
    rw [e, Module.End.one_apply]
    congr 1
    refine Subtype.ext (funext fun u => ?_)
    rw [f, map_one, Module.End.one_apply]
    exact congrArg z.1 (Subtype.ext (by simp [conjHom]))
  map_mul' g h := LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z₁, e₁, f₁⟩ := conjU_mk ρ U h z
    obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ U g z₁
    obtain ⟨z₃, e₃, f₃⟩ := conjU_mk ρ U (g * h) z
    rw [Module.End.mul_apply, e₁, e₂, e₃]
    congr 1
    refine Subtype.ext (funext fun u => ?_)
    rw [f₃, f₂, f₁, map_mul, Module.End.mul_apply]
    exact congrArg (fun t => ρ g (ρ h (z.1 t))) (Subtype.ext (by simp [conjHom, mul_assoc]))

theorem conjRep_apply (ρ : Representation R G M) (U : Subgroup G) [U.Normal] (g : G) :
    conjRep ρ U g = conjU ρ U g := rfl

private theorem cocycle_conj_identity (ρ : Representation R G M) (U : Subgroup G) (z : Z1U ρ U) (γ v : U) :
    ρ γ (z.1 (γ⁻¹ * (v * γ))) - z.1 v = ρ v (z.1 γ) - z.1 γ := by
  have hz : ∀ a b : U, z.1 (a * b) = z.1 a + ρ a (z.1 b) := ((mem_Z1_iff_cocycle _ _).mp z.2).2
  have h1 : z.1 1 = 0 := by simpa using hz 1 1
  have hinv : ρ γ (z.1 γ⁻¹) = - z.1 γ := by
    have := hz γ γ⁻¹
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hmul : ∀ w : M, ρ γ (ρ (γ⁻¹ : U) w) = w := by
    intro w
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  rw [hz, hz, map_add, hmul, hinv]
  abel

theorem conjRep_of_mem (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {g : G} (hg : g ∈ U) (x : H1U ρ U) :
    conjRep ρ U g x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := conjU_mk ρ U g z
  rw [conjRep_apply, e, mk_eq_mk]
  refine ⟨z.1 ⟨g, hg⟩, fun u => ?_⟩
  have hc : conjHom U g u = (⟨g, hg⟩ : U)⁻¹ * (u * ⟨g, hg⟩) :=
    Subtype.ext (by simp [conjHom, mul_assoc])
  rw [f u, hc]
  exact cocycle_conj_identity ρ U z ⟨g, hg⟩ u

theorem resU_conjRep (ρ : Representation R G M) {U' U : Subgroup G} [U.Normal] [U'.Normal] (h : U' ≤ U) (g : G)
    (x : H1U ρ U) : resU ρ h (conjRep ρ U g x) = conjRep ρ U' g (resU ρ h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := conjU_mk ρ U g z
  obtain ⟨z₂, e₂, f₂⟩ := resU_mk ρ h z₁
  obtain ⟨z₃, e₃, f₃⟩ := resU_mk ρ h z
  obtain ⟨z₄, e₄, f₄⟩ := conjU_mk ρ U' g z₃
  rw [conjRep_apply, conjRep_apply, e₁, e₂, e₃, e₄]
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  rw [f₂, f₁, f₄, f₃]
  exact congrArg (fun t => ρ g (z.1 t)) (Subtype.ext (by simp [conjHom]))

theorem conjRep_mem_locSel (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) (g : G) {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) : conjRep ρ U g x ∈ LocSel ρ U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := conjU_mk ρ U g z
  rw [conjRep_apply, e, mk_mem_locSel]
  rw [mk_mem_locSel] at hx
  intro D hD
  obtain ⟨D', hD', hiff⟩ := h𝒟 D hD g
  obtain ⟨m, hm⟩ := hx D' hD'
  refine ⟨ρ g m, fun u hu => ?_⟩
  rw [f u, hm (conjHom U g u) ((hiff u).mp hu), map_sub]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  simp [conjHom, mul_assoc]

def selRep (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟) :
    Representation R G (LocSel ρ U 𝒟) :=
  (conjRep ρ U).subrepresentation (LocSel ρ U 𝒟) fun g _ hx => conjRep_mem_locSel ρ U h𝒟 g hx

theorem coe_selRep (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟)
    (g : G) (x : LocSel ρ U 𝒟) : (selRep ρ U h𝒟 g x : H1U ρ U) = conjRep ρ U g x := rfl

theorem selRep_of_mem (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) {g : G} (hg : g ∈ U) (x : LocSel ρ U 𝒟) : selRep ρ U h𝒟 g x = x := by
  apply Subtype.ext
  rw [coe_selRep, conjRep_of_mem ρ U hg]

theorem selRes_selRep (ρ : Representation R G M) {U' U : Subgroup G} [U.Normal] [U'.Normal] (h : U' ≤ U)
    {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟) (g : G) (x : LocSel ρ U 𝒟) :
    selRes ρ h 𝒟 (selRep ρ U h𝒟 g x) = selRep ρ U' h𝒟 g (selRes ρ h 𝒟 x) := by
  apply Subtype.ext
  show resU ρ h (conjRep ρ U g x) = conjRep ρ U' g (resU ρ h x)
  exact resU_conjRep ρ h g x

abbrev invariantsUnderSubgroupH1 (ρ : Representation R G M) (U U' : Subgroup G) [U'.Normal] : Submodule R (H1U ρ U') :=
  Representation.invariants ((conjRep ρ U').comp U.subtype : Representation R U (H1U ρ U'))

abbrev selEig (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟)
    (W : Subgroup G) (ψ : W →* Rˣ) : Submodule R (LocSel ρ U 𝒟) :=
  eig ((selRep ρ U h𝒟).comp W.subtype : Representation R W (LocSel ρ U 𝒟)) ψ

abbrev resCoker (ρ : Representation R G M) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U) : Type :=
  invariantsUnderSubgroupH1 ρ U U' ⧸ (LinearMap.range (resU ρ h)).comap (invariantsUnderSubgroupH1 ρ U U').subtype

theorem restriction_mem_invariant_H1 (ρ : Representation R G M) {U' U : Subgroup G} [U'.Normal] (h : U' ≤ U) (x : H1U ρ U) :
    resU ρ h x ∈ invariantsUnderSubgroupH1 ρ U U' := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := resU_mk ρ h z
  rw [e₁, Representation.mem_invariants]
  intro u
  show conjRep ρ U' (u : G) (Submodule.Quotient.mk z₁) = Submodule.Quotient.mk z₁
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ U' (u : G) z₁
  rw [conjRep_apply, e₂, mk_eq_mk]
  refine ⟨z.1 u, fun v => ?_⟩
  have hc : (⟨(conjHom U' (u : G) v).1, h (conjHom U' (u : G) v).2⟩ : U) =
      u⁻¹ * (⟨v.1, h v.2⟩ * u) := Subtype.ext (by simp [conjHom, mul_assoc])
  have key := cocycle_conj_identity ρ U z u ⟨v.1, h v.2⟩
  rw [← hc] at key
  rw [f₂ v, f₁, f₁ v]
  exact key

end Conj

end UpperTheory.V.Base

end
