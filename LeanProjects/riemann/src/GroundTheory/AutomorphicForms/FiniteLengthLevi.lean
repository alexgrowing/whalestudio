import Mathlib
import GroundTheory.AutomorphicForms.FiniteLengthLeviBlock
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Inducing

theorem normLeviParSqrtModular_eq_one_of_mem_unipotentRadical {γ δ' : Fin n → ℕ}
    (u : leviPar F n γ δ') (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n δ') :
    normLeviParSqrtModular F γ δ' u = 1 := by
  obtain ⟨e, he⟩ := exists_unipotentCompactG_of_isCompact (γ := δ')
    (isCompact_singleton (x := (u : GL (Fin n) F))) (by simpa using hu)
  have ht : rankTorus F n δ' e ∈ leviPar F n γ δ' :=
    ⟨diagGL_mem_levi _, rankTorus_mem_blockUpper e⟩
  have hk : rankTorus F n δ' e * u * (rankTorus F n δ' e)⁻¹ ∈ integralGL F n :=
    (mem_unipotentCompactG.1 (he rfl)).2
  have hkL : rankTorus F n δ' e * u * (rankTorus F n δ' e)⁻¹ ∈ leviPar F n γ δ' :=
    (leviPar F n γ δ').mul_mem ((leviPar F n γ δ').mul_mem ht u.2) ((leviPar F n γ δ').inv_mem ht)
  have h1 := normLeviParSqrtModular_eq_one (l := ⟨_, hkL⟩) hk
  have : u = ⟨_, ht⟩⁻¹ * ⟨_, hkL⟩ * ⟨_, ht⟩ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group)
  rw [this, map_mul, map_mul, h1, mul_one, ← map_mul, inv_mul_cancel, map_one]

variable {β δ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W) {w : Equiv.Perm (Fin n)}

theorem conj_mem_unipotentRadical_of_mem {g : GL (Fin n) F}
    (hg : g ∈ unipotentRadical F n (β ∘ w)) :
    permGL F w * g * (permGL F w)⁻¹ ∈ unipotentRadical F n β := by
  have h := (conj_permGL_mem_unipotentRadical_iff (γ := β ∘ w) w).2 hg
  have e : (β ∘ w) ∘ ⇑w⁻¹ = β := by
    funext i
    simp
  rwa [e] at h

theorem normInducing_eq_one_of_mem_unipotentRadical (b : cellLeviSub F β δ w)
    (hb : ((b : levi F n δ) : GL (Fin n) F) ∈ unipotentRadical F n (β ∘ w)) :
    normInducing σ δ w b = 1 := by
  have hinner : cellInnerHom β δ w (cellLeviSubIncl F β δ w b) = 1 := by
    apply Subtype.ext
    show ((leviProj F n β (permConj F β w (Subgroup.inclusion cellLeviParabolic_le_blockUpper
      (cellLeviSubIncl F β δ w b))) : levi F n β) : GL (Fin n) F) = 1
    rw [(mem_unipotentRadical_iff_leviProj).1]
    · rfl
    · rw [coe_permConj]
      exact conj_mem_unipotentRadical_of_mem hb
  have hchar : normLeviParSqrtModular F δ (β ∘ w) (cellLeviSubIncl F β δ w b) = 1 :=
    normLeviParSqrtModular_eq_one_of_mem_unipotentRadical _ hb
  have hchar' : ((normLeviParSqrtModular F δ (β ∘ ⇑w)).comp (cellLeviSubIncl F β δ w)) b = 1 :=
    hchar
  refine LinearMap.ext fun v => ?_
  show ((normLeviParSqrtModular F δ (β ∘ ⇑w)).comp (cellLeviSubIncl F β δ w)) b •
    (innerJacquetRep β σ (δ ∘ ⇑w⁻¹)) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b)) v = v
  rw [hchar', hinner, map_one, one_smul]
  rfl

theorem mem_cellLeviSub_of_diagonal (x : levi F n δ) (d : Fin n → F)
    (hx : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d) :
    x ∈ cellLeviSub F β δ w := by
  refine Subgroup.mem_subgroupOf.2 ⟨x.2, ?_⟩
  show ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular (β ∘ w)
  rw [hx]
  exact blockTriangular_diagonal _

theorem exists_normInducing_blockEmb_center [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hinc : ∀ a b, β (w a) = β (w b) → δ a = δ b) {a : Set.range δ}
    {z : GL (Fin (blockSize δ a)) F} (hz : z ∈ Subgroup.center (GL (Fin (blockSize δ a)) F))
    (hmem : blockEmb F δ a z ∈ cellLeviSub F β δ w) :
    ∃ c : ℂ, ∀ v, normInducing σ δ w ⟨blockEmb F δ a z, hmem⟩ v = c • v := by
  classical
  obtain ⟨s, hs⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hz' := coe_blockEmb_apply_of_scalar (F := F) (a := a) (z := z) (s := s) hs.symm
  set d : Fin n → F := fun i => if blockOf δ i = a then s else 1 with hd_def
  set b : cellLeviSub F β δ w := ⟨blockEmb F δ a z, hmem⟩
  set x : levi F n β := leviInfIncl β (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b))
  have hx : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun r => d (w⁻¹ r) := by
    ext r c
    show ((leviProj F n β _ : levi F n β) : GL (Fin n) F) r c = _
    rw [leviProj_apply]
    split_ifs with hrc
    · show ((permGL F w * ((blockEmb F δ a z : levi F n δ) : GL (Fin n) F) * (permGL F w)⁻¹ :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c = _
      rw [permGL_conj_apply, hz', diagonal_apply, diagonal_apply]
      simp only [EmbeddingLike.apply_eq_iff_eq]
    · have hne : r ≠ c := fun h => hrc (h ▸ rfl)
      rw [diagonal_apply_ne _ hne]
  have hdc : ∀ r c, β r = β c → d (w⁻¹ r) = d (w⁻¹ c) := by
    intro r c hrc
    have h1 : δ (w⁻¹ r) = δ (w⁻¹ c) := hinc _ _ (by simpa using hrc)
    have h2 : blockOf δ (w⁻¹ r) = blockOf δ (w⁻¹ c) := Subtype.ext h1
    simp only [hd_def, h2]
  obtain ⟨cσ, hcσ⟩ := exists_central_character hσ (mem_center_levi_of_diagonal x _ hx hdc)
  refine ⟨normLeviParSqrtModular F δ (β ∘ w) (cellLeviSubIncl F β δ w b) *
    (normLeviParInvSqrtModular F β (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b)) *
      cσ), fun v => ?_⟩
  obtain ⟨u, rfl⟩ := Representation.Coinvariants.mk_surjective _ v
  simp only [normInducing, innerJacquetRep, twist_apply, MonoidHom.coe_comp, Function.comp_apply,
    levJacquetAction_mk]
  rw [show σ (leviInfIncl β (δ ∘ ⇑w⁻¹) (cellInnerHom β δ w (cellLeviSubIncl F β δ w b))) u =
    cσ • u from hcσ u, map_smul, smul_smul, smul_smul]
  simp only [mul_assoc]
  rfl

end Inducing

section Restrict

variable {β δ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W) {w : Equiv.Perm (Fin n)}

theorem blockEmb_mem_cellLeviSub {a : Set.range δ} {y : GL (Fin (blockSize δ a)) F}
    (hy : y ∈ unipotentRadical F (blockSize δ a) (restrictFun δ (β ∘ w) a)) :
    blockEmb F δ a y ∈ cellLeviSub F β δ w :=
  Subgroup.mem_subgroupOf.2 ⟨(blockEmb F δ a y).2,
    unipotentRadical_le_blockUpper (blockEmb_mem_unipotentRadical (β ∘ w) hy)⟩

set_option maxHeartbeats 400000 in

theorem intertwiningMap_blockEmb_eq_zero {a : Set.range δ} {V₀ : Type*} [AddCommGroup V₀]
    [Module ℂ V₀] {π₀ : Representation ℂ (GL (Fin (blockSize δ a)) F) V₀}
    (hsc : Subsingleton (JacquetModule F (blockSize δ a) (restrictFun δ (β ∘ w) a) π₀))
    (φ : Representation.IntertwiningMap π₀
      ((indRep (cellLeviSub F β δ w) (normInducing σ δ w)).comp (blockEmb F δ a))) :
    φ = 0 := by
  have hφ : ∀ y v, φ (π₀ y v) =
      indRep (cellLeviSub F β δ w) (normInducing σ δ w) (blockEmb F δ a y) (φ v) := fun y v =>
    Representation.IntertwiningMap.isIntertwining _ _ φ y v
  have hL : ∀ m' : levi F n δ, leviEquivPi F δ m' a = 1 → ∀ v, (φ v).1 m' = 0 := by
    intro m' hm' v
    let L : V₀ →ₗ[ℂ] innerJacquetSpace β δ w σ :=
      { toFun := fun v => (φ v).1 m'
        map_add' := fun x y => by
          show (φ (x + y)).1 m' = (φ x).1 m' + (φ y).1 m'
          rw [map_add]
          rfl
        map_smul' := fun c x => by
          show (φ (c • x)).1 m' = c • (φ x).1 m'
          rw [map_smul]
          rfl }
    have hLapp : ∀ v, L v = (φ v).1 m' := fun _ => rfl
    have hker : Representation.Coinvariants.ker
        (π₀.comp (unipotentRadical F (blockSize δ a) (restrictFun δ (β ∘ w) a)).subtype) ≤
          LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨y, x⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, hLapp, hLapp]
      have hy : (y : GL (Fin (blockSize δ a)) F) ∈
          unipotentRadical F (blockSize δ a) (restrictFun δ (β ∘ w) a) := y.2
      have hc : m' * blockEmb F δ a y = blockEmb F δ a y * m' :=
        (blockEmb_commute a (y : GL (Fin (blockSize δ a)) F) m' hm').symm
      have h1 : (φ (π₀ y x)).1 m' = (φ x).1 (m' * blockEmb F δ a y) :=
        congrArg (fun f => f.1 m') (hφ y x)
      have h2 : (φ x).1 (blockEmb F δ a y * m') =
          normInducing σ δ w ⟨blockEmb F δ a y, blockEmb_mem_cellLeviSub hy⟩ ((φ x).1 m') :=
        (φ x).2.1 ⟨blockEmb F δ a y, blockEmb_mem_cellLeviSub hy⟩ m'
      have h3 := normInducing_eq_one_of_mem_unipotentRadical σ
        ⟨blockEmb F δ a y, blockEmb_mem_cellLeviSub hy⟩ (blockEmb_mem_unipotentRadical (β ∘ w) hy)
      have h4 : normInducing σ δ w ⟨blockEmb F δ a y, blockEmb_mem_cellLeviSub hy⟩ ((φ x).1 m') =
          (1 : Module.End ℂ (innerJacquetSpace β δ w σ)) ((φ x).1 m') :=
        congrArg (fun T : Module.End ℂ (innerJacquetSpace β δ w σ) => T ((φ x).1 m')) h3
      exact h1.trans ((congrArg (φ x).1 hc).trans (h2.trans (h4.trans rfl)))
    have hv : v ∈ Representation.Coinvariants.ker
        (π₀.comp (unipotentRadical F (blockSize δ a) (restrictFun δ (β ∘ w) a)).subtype) :=
      (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact (hLapp v).symm.trans (LinearMap.mem_ker.1 (hker hv))
  have hall : ∀ v x, (φ v).1 x = 0 := by
    intro v x
    have h1 : blockEmb F δ a (leviEquivPi F δ x a) * blockRest F δ a x = x :=
      blockEmb_mul_blockRest a x
    have h2 : blockEmb F δ a (leviEquivPi F δ x a) * blockRest F δ a x =
        blockRest F δ a x * blockEmb F δ a (leviEquivPi F δ x a) :=
      blockEmb_commute a _ _ (leviEquivPi_blockRest_self a x)
    have h3 : (φ (π₀ (leviEquivPi F δ x a) v)).1 (blockRest F δ a x) =
        (φ v).1 (blockRest F δ a x * blockEmb F δ a (leviEquivPi F δ x a)) :=
      congrArg (fun f => f.1 (blockRest F δ a x)) (hφ _ v)
    exact (congrArg (φ v).1 (h1.symm.trans h2)).trans
      (h3.symm.trans (hL _ (leviEquivPi_blockRest_self a x) _))
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
  rw [Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
  exact (Submodule.coe_eq_zero).1 (funext fun x => hall v x)

end Restrict

section CuspidalBlock

variable {δ : Fin n → ℕ}

theorem subsingleton_jacquetModule_comp_blockEmb {U : Type*} [AddCommGroup U] [Module ℂ U]
    {τ : Representation ℂ (levi F n δ) U} (hτc : IsCuspidal τ) {a : Set.range δ}
    {ε : Fin (blockSize δ a) → ℕ} (hε : ∃ k l, ε k ≠ ε l) :
    Subsingleton (JacquetModule F (blockSize δ a) ε (τ.comp (blockEmb F δ a))) := by
  have h := hτc (blockExtend δ a ε) (exists_split_blockExtend hε)
  have hker : Representation.Coinvariants.ker
      (τ.comp (leviUnipotent F n δ (blockExtend δ a ε)).subtype) ≤
      Representation.Coinvariants.ker
        ((τ.comp (blockEmb F δ a)).comp (unipotentRadical F (blockSize δ a) ε).subtype) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, x⟩, rfl⟩
    obtain ⟨y, hy, hyu⟩ := exists_blockEmb_of_mem_unipotentRadical (u : levi F n δ)
      (Subgroup.mem_subgroupOf.1 u.2)
    have := Representation.Coinvariants.sub_mem_ker
      (ρ := (τ.comp (blockEmb F δ a)).comp (unipotentRadical F (blockSize δ a) ε).subtype)
      ⟨y, hy⟩ x
    simpa [hyu] using this
  have hzero : ∀ x : U, Representation.Coinvariants.mk
      ((τ.comp (blockEmb F δ a)).comp (unipotentRadical F (blockSize δ a) ε).subtype) x = 0 :=
    fun x => (Representation.Coinvariants.mk_eq_zero _).2
      (hker ((Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)))
  refine ⟨fun p q => ?_⟩
  obtain ⟨p, rfl⟩ := Representation.Coinvariants.mk_surjective _ p
  obtain ⟨q, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
  rw [hzero p, hzero q]

end CuspidalBlock

section Generic

theorem isSmooth_toRepresentation_of_isSmooth {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : IsSmooth ρ) (Y : Subrepresentation ρ) : IsSmooth Y.toRepresentation := by
  intro y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ (y : V))
  rw [mem_stabilizerOf] at hg ⊢
  exact Subtype.ext hg

variable {m : ℕ}

theorem exists_isSupercuspidal_quotient {U : Type*} [AddCommGroup U] [Module ℂ U]
    {τ : Representation ℂ (GL (Fin m) F) U} (hτ : IsSmooth τ)
    (hτc : ∀ ε : Fin m → ℕ, (∃ k l, ε k ≠ ε l) → Subsingleton (JacquetModule F m ε τ))
    {u₀ : U} (hu₀ : u₀ ≠ 0) :
    ∃ (A : Subrepresentation τ) (Y : Submodule ℂ A.toSubmodule)
      (hY : ∀ g, Y ≤ Y.comap (A.toRepresentation g)),
      (Representation.quotient A.toRepresentation Y hY).IsIrreducible ∧
      IsSmooth (Representation.quotient A.toRepresentation Y hY) ∧
      IsSupercuspidal (Representation.quotient A.toRepresentation Y hY) := by
  classical
  let A : Subrepresentation τ :=
    ⟨Submodule.span ℂ (Set.range fun g => τ g u₀), fun g x hx =>
      (Submodule.span_le.2 (by
        rintro _ ⟨h, rfl⟩
        exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩) :
        Submodule.span ℂ (Set.range fun g => τ g u₀) ≤
          (Submodule.span ℂ (Set.range fun g => τ g u₀)).comap (τ g)) hx⟩
  have hu₀A : u₀ ∈ A.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  let u₀' : A.toSubmodule := ⟨u₀, hu₀A⟩
  have : Nontrivial A.toSubmodule := ⟨⟨u₀', 0, fun h => hu₀ (congrArg Subtype.val h)⟩⟩
  have hspan : Submodule.span ℂ {x | ∃ g, ∃ s ∈ ({u₀'} : Finset A.toSubmodule),
      x = A.toRepresentation g s} = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact Submodule.subset_span ⟨g, u₀', Finset.mem_singleton_self _, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add y z hy hz ihy ihz => exact Submodule.add_mem _ ihy ihz
    | smul c y hy ih => exact Submodule.smul_mem _ c ih
  obtain ⟨Y, hY, hirr⟩ := exists_irreducible_quotient (τ := A.toRepresentation) {u₀'} hspan
  have hA : IsSmooth A.toRepresentation := isSmooth_toRepresentation hτ A
  refine ⟨A, Y, hY, hirr, isSmooth_quotient hA Y hY, fun ε hε => ?_⟩
  have h1 := hτc ε hε
  have hex := exact_jacquetMap (β := ε) hA hτ
    (0 : Representation.IntertwiningMap A.toRepresentation A.toRepresentation) (subrepIncl A)
    (fun y => ⟨fun hy => ⟨0, (Subtype.ext hy).symm⟩, by rintro ⟨y', rfl⟩; rfl⟩)
  have hz : ∀ y : JacquetModule F m ε A.toRepresentation, y = 0 := by
    intro y
    obtain ⟨y', hy'⟩ := (hex y).1 (Subsingleton.elim _ _)
    rw [← hy']
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y'
    rw [jacquetMap_mk]
    exact map_zero _
  exact subsingleton_coinvariants_of_surjective (quotientMk Y hY) (quotientMk_surjective Y hY)
    ⟨fun y y' => (hz y).trans (hz y').symm⟩

theorem exists_subrep_surjective {G : Type*} [Group G] {V₁ V₂ : Type*} [AddCommGroup V₁]
    [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] {ρ₁ : Representation ℂ G V₁}
    {ρ₂ : Representation ℂ G V₂} (p : Representation.IntertwiningMap ρ₁ ρ₂)
    (hp : Function.Surjective p) (A : Subrepresentation ρ₂) :
    ∃ (D : Subrepresentation ρ₁) (r : Representation.IntertwiningMap D.toRepresentation
      A.toRepresentation), Function.Surjective r := by
  let D : Subrepresentation ρ₁ :=
    ⟨A.toSubmodule.comap p.toLinearMap, fun g x hx => by
      show p (ρ₁ g x) ∈ A.toSubmodule
      rw [Representation.IntertwiningMap.isIntertwining _ _ p]
      exact A.apply_mem_toSubmodule g hx⟩
  refine ⟨D, ⟨p.toLinearMap.restrict (p := D.toSubmodule) (q := A.toSubmodule) (fun _ hx => hx),
    fun g => LinearMap.ext fun x =>
      Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ p g x)⟩, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨c, hc⟩ := hp x
  have hcA : p c ∈ A.toSubmodule := by
    rw [hc]
    exact hx
  exact ⟨⟨c, hcA⟩, Subtype.ext hc⟩

theorem not_surjective_of_forall_eq_zero {U V₀ : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V₀] [Module ℂ V₀] {ρ : Representation ℂ (GL (Fin m) F) U}
    {ω : GL (Fin m) F → ℂ} (hρ : IsSmooth ρ) (hωρ : HasCentralChar ρ ω)
    {π₀ : Representation ℂ (GL (Fin m) F) V₀} [π₀.IsIrreducible] (hπ₀ : IsSmooth π₀)
    (hsc : IsSupercuspidal π₀) (hzero : ∀ φ : Representation.IntertwiningMap π₀ ρ, φ = 0)
    (D : Subrepresentation ρ) (q : Representation.IntertwiningMap D.toRepresentation π₀) :
    ¬ Function.Surjective q := by
  intro hq
  have hωπ₀ : HasCentralChar π₀ ω := by
    intro z hz x
    obtain ⟨d, rfl⟩ := hq x
    rw [← Representation.IntertwiningMap.isIntertwining, (hωρ.toRepresentation D) z hz d,
      map_smul]
  have hpart : isotypicPart π₀ ρ = ⊥ := by
    rw [isotypicPart, eq_bot_iff]
    refine iSup_le fun φ => ?_
    rw [hzero φ, Representation.IntertwiningMap.zero_toLinearMap, LinearMap.range_zero]
  have hker_top : isotypicKernel π₀ ρ = ⊤ := by
    have h := (isCompl_isotypicPart_isotypicKernel hπ₀ hsc hωπ₀ hρ hωρ).sup_eq_top
    rwa [hpart, bot_sup_eq] at h
  exact not_surjective_of_le_isotypicKernel hπ₀ hsc hωπ₀ hρ hωρ D
    (by rw [hker_top]; exact le_top) q hq

end Generic

section Main

theorem indRep_eq_smul_of_central {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} {W' : Type*} [AddCommGroup W'] [Module ℂ W'] {ρ : Representation ℂ H W'}
    {z : G} (hz : ∀ x, x * z = z * x) (hzH : z ∈ H) {c : ℂ} (hc : ∀ v, ρ ⟨z, hzH⟩ v = c • v)
    (f : indSpace H ρ) : indRep H ρ z f = c • f := by
  apply Subtype.ext
  funext x
  show f.1 (x * z) = c • f.1 x
  rw [hz x, f.2.1 ⟨z, hzH⟩ x]
  exact hc _

universe u

theorem not_surjective_of_blockEmb {δ : Fin n → ℕ} {X : Type*} [AddCommGroup X] [Module ℂ X]
    {U : Type u} [AddCommGroup U] [Module ℂ U] {P : Representation ℂ (levi F n δ) X}
    (hP : IsSmooth P) {a : Set.range δ} {ε : Fin (blockSize δ a) → ℕ} (hε : ∃ k l, ε k ≠ ε l)
    (hcent : ∀ z ∈ Subgroup.center (GL (Fin (blockSize δ a)) F), ∃ c : ℂ, ∀ f,
      P (blockEmb F δ a z) f = c • f)
    (hzero : ∀ (V₀ : Type u) [AddCommGroup V₀] [Module ℂ V₀]
      (π₀ : Representation ℂ (GL (Fin (blockSize δ a)) F) V₀),
      Subsingleton (JacquetModule F (blockSize δ a) ε π₀) →
        ∀ φ : Representation.IntertwiningMap π₀ (P.comp (blockEmb F δ a)), φ = 0)
    {τ : Representation ℂ (levi F n δ) U} [τ.IsIrreducible] (hτ : IsSmooth τ)
    (hτc : IsCuspidal τ) (C : Subrepresentation P)
    (p : Representation.IntertwiningMap C.toRepresentation τ) : ¬ Function.Surjective p := by
  classical
  intro hp

  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
  obtain ⟨A, Y, hY, hirr, hπ₀, hsc⟩ := exists_isSupercuspidal_quotient
    (isSmooth_comp_of_continuous hτ _ (continuous_blockEmb a))
    (fun ε hε => subsingleton_jacquetModule_comp_blockEmb hτc hε) hu₀

  let ω : GL (Fin (blockSize δ a)) F → ℂ := fun z =>
    if hz : z ∈ Subgroup.center (GL (Fin (blockSize δ a)) F) then (hcent z hz).choose else 0
  have hωρ : HasCentralChar (C.toRepresentation.comp (blockEmb F δ a)) ω := by
    intro z hz f
    apply Subtype.ext
    show P (blockEmb F δ a z) f.1 = ω z • f.1
    rw [show ω z = (hcent z hz).choose from dif_pos hz]
    exact (hcent z hz).choose_spec f.1
  have hρ : IsSmooth (C.toRepresentation.comp (blockEmb F δ a)) :=
    isSmooth_comp_of_continuous (isSmooth_toRepresentation_of_isSmooth hP C) _
      (continuous_blockEmb a)

  have hzeroC : ∀ φ : Representation.IntertwiningMap (Representation.quotient A.toRepresentation Y hY)
      (C.toRepresentation.comp (blockEmb F δ a)), φ = 0 := by
    intro φ
    let incl : Representation.IntertwiningMap (C.toRepresentation.comp (blockEmb F δ a))
        (P.comp (blockEmb F δ a)) := ⟨C.toSubmodule.subtype, fun _ => rfl⟩
    have h := hzero _ _ (hsc ε hε) (incl.comp φ)
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
    rw [Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
    exact Subtype.ext (congrArg (fun ψ : Representation.IntertwiningMap
      (Representation.quotient A.toRepresentation Y hY) (P.comp (blockEmb F δ a)) => ψ v) h)

  obtain ⟨D, r, hr⟩ := exists_subrep_surjective
    (ρ₁ := C.toRepresentation.comp (blockEmb F δ a)) (ρ₂ := τ.comp (blockEmb F δ a))
    ⟨p.toLinearMap, fun g => p.isIntertwining' (blockEmb F δ a g)⟩ hp A
  exact not_surjective_of_forall_eq_zero hρ hωρ hπ₀ hsc hzeroC D
    ((quotientMk Y hY).comp r) ((quotientMk_surjective Y hY).comp hr)

variable {β δ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W} {w : Equiv.Perm (Fin n)}

theorem exists_indRep_blockEmb_center [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hinc : ∀ a b, β (w a) = β (w b) → δ a = δ b) {a : Set.range δ}
    {z : GL (Fin (blockSize δ a)) F} (hz : z ∈ Subgroup.center (GL (Fin (blockSize δ a)) F)) :
    ∃ c : ℂ, ∀ f, indRep (cellLeviSub F β δ w) (normInducing σ δ w) (blockEmb F δ a z) f = c • f := by
  obtain ⟨s, hs⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hmem : blockEmb F δ a z ∈ cellLeviSub F β δ w :=
    mem_cellLeviSub_of_diagonal _ _ (coe_blockEmb_apply_of_scalar hs.symm)
  obtain ⟨c, hc⟩ := exists_normInducing_blockEmb_center σ hσ hinc hz hmem
  exact ⟨c, indRep_eq_smul_of_central (fun x => Subgroup.mem_center_iff.1 (blockEmb_mem_center hz) x)
    hmem hc⟩

theorem not_surjective_of_isCuspidal_piece [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hinc : ∀ a b, β (w a) = β (w b) → δ a = δ b)
    (hprop : ∃ a b, δ a = δ b ∧ β (w a) ≠ β (w b))
    {U : Type*} [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ (levi F n δ) U}
    [τ.IsIrreducible] (hτ : IsSmooth τ) (hτc : IsCuspidal τ)
    (C : Subrepresentation (indRep (cellLeviSub F β δ w) (normInducing σ δ w)))
    (p : Representation.IntertwiningMap C.toRepresentation τ) : ¬ Function.Surjective p := by
  obtain ⟨i₀, j₀, hδij, hβij⟩ := hprop

  obtain ⟨a, hi₀⟩ : ∃ a : Set.range δ, blockOf δ i₀ = a := ⟨_, rfl⟩
  have hj₀ : blockOf δ j₀ = a := (Subtype.ext hδij.symm).trans hi₀
  have hε : ∃ k l, restrictFun δ (β ∘ w) a k ≠ restrictFun δ (β ∘ w) a l := by
    refine ⟨(fiberFin δ a).symm ⟨i₀, hi₀⟩, (fiberFin δ a).symm ⟨j₀, hj₀⟩, ?_⟩
    simp only [restrictFun, Equiv.apply_symm_apply, Function.comp_apply]
    exact hβij
  exact not_surjective_of_blockEmb (isSmooth_indRep _ _) hε
    (fun z hz => exists_indRep_blockEmb_center hσ hinc hz)
    (fun V₀ _ _ π₀ hsc φ => intertwiningMap_blockEmb_eq_zero σ hsc φ) hτ hτc C p

end Main

end Parabolic

end GroundTheory.Automorphic
