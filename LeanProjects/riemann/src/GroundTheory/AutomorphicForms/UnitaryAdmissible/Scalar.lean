import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.GKTensor
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian

namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open Module Set GKTensor

attribute [local instance 100] LieRing.ofAssociativeRing

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G}

section Scalar

variable [CompactSpace K] {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L] {V : Type*} [AddCommGroup V]
  [Module ℂ V]

theorem exists_eq_smul_one (Mx : GKLModule h K L V) (hirr : Mx.IsIrreducible)
    (T : Module.End ℂ V) (hρ : ∀ X, Mx.gk.ρ X * T = T * Mx.gk.ρ X)
    (hσ : ∀ k, Mx.gk.σ k * T = T * Mx.gk.σ k) (hτ : ∀ g, Mx.τ g * T = T * Mx.τ g)
    (hfin : ∀ v : V, ∃ F : Submodule ℂ V, FiniteDimensional ℂ F ∧ v ∈ F ∧ ∀ w ∈ F, T w ∈ F) :
    ∃ c : ℂ, T = c • 1 := by
  have : IsSimpleOrder (Subrepresentation Mx.fullRep) := hirr
  have hnt : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply (bot_ne_top : (⊥ : Subrepresentation Mx.fullRep) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    ext w
    simp [Subsingleton.elim w 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨F, hFd, hvF, hTF⟩ := hfin v
  set T' : Module.End ℂ F := T.restrict hTF
  have : Nontrivial F := ⟨⟨⟨v, hvF⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T'
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hcomm : ∀ p, Mx.fullRep p * T = T * Mx.fullRep p := by
    rintro ⟨a, g⟩
    show Mx.gk.rep a * Mx.τ g * T = T * (Mx.gk.rep a * Mx.τ g)
    rw [mul_assoc, hτ, ← mul_assoc, Mx.gk.rep_comm hρ hσ a, mul_assoc]
  let Y : Subrepresentation Mx.fullRep :=
    ⟨LinearMap.ker (T - c • 1), fun p x hx => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply] at hx ⊢
      have e := congrArg (fun f : Module.End ℂ V => f x) (hcomm p)
      simp only [Module.End.mul_apply] at e
      rw [← e, ← map_smul, ← map_sub, hx, map_zero]⟩
  have hwT : T (w : V) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
  rcases IsSimpleOrder.eq_bot_or_eq_top Y with hY | hY
  · exfalso
    have hmem : (w : V) ∈ Y.toSubmodule := by
      show (w : V) ∈ LinearMap.ker (T - c • 1)
      simp [hwT]
    rw [hY] at hmem
    exact hw0 hmem
  · refine ⟨c, LinearMap.ext fun x => ?_⟩
    have hmem : x ∈ Y.toSubmodule := by rw [hY]; trivial
    have hx : (T - c • 1) x = 0 := hmem
    simpa [sub_eq_zero] using hx

end Scalar

section Casimir

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι]

noncomputable def casimirOp (M : h.GKModule K V) (b : Module.Basis ι ℝ h.lieSubalgebra) (ε : ι → ℝ) :
    Module.End ℂ V :=
  ∑ i, ε i • (M.ρ (b i) * M.ρ (b i))

theorem σ_mul_ρ (M : h.GKModule K V) (k : K) (Y : h.lieSubalgebra) :
    M.σ k * M.ρ Y = M.ρ (h.AdLie (k : G) Y) * M.σ k :=
  LinearMap.ext fun v => M.map_ρ k (h.ofLie Y) v

theorem AdLie_AdLie_inv (g : G) (Y : h.lieSubalgebra) : h.AdLie g (h.AdLie g⁻¹ Y) = Y := by
  show h.toLie (h.Ad g (h.Ad g⁻¹ (h.ofLie Y))) = Y
  have e := h.Ad_inv_Ad g⁻¹ (h.ofLie Y)
  rw [inv_inv] at e
  rw [e]
  rfl

theorem σ_mul_casimirOp [DecidableEq ι] (M : h.GKModule K V)
    {B : LinearMap.BilinForm ℝ h.lieSubalgebra} {b : Module.Basis ι ℝ h.lieSubalgebra} {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y, B X Y = B Y X)
    (hAd : ∀ k : K, ∀ X Y, B (h.AdLie (k : G) X) (h.AdLie (k : G) Y) = B X Y) (k : K) :
    M.σ k * casimirOp M b ε = casimirOp M b ε * M.σ k := by
  set A := h.AdLie (k : G)
  set f : ι → h.lieSubalgebra := fun i => A (b i) with hf

  have hexp : ∀ Y, Y = ∑ i, (ε i * B Y (f i)) • f i := by
    intro Y
    have e := eq_sum_of_orthogonal hε horth (h.AdLie ((k : G)⁻¹) Y)
    have e2 := congrArg A e
    rw [AdLie_AdLie_inv] at e2
    conv_lhs => rw [e2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 2
    rw [← hAd k (b i) (h.AdLie ((k : G)⁻¹) Y), AdLie_AdLie_inv, hsymm]

  have hsum : ∀ j l, ∑ i, ε i * B (b j) (f i) * B (b l) (f i) = B (b j) (b l) := by
    intro j l
    conv_rhs => rw [hexp (b l)]
    rw [map_sum, Finset.sum_congr rfl]
    intro i _
    rw [map_smul, smul_eq_mul]
    ring

  have hρf : ∀ i, M.ρ (f i) = ∑ j, (ε j * B (b j) (f i)) • M.ρ (b j) := by
    intro i
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (f i)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
  have hcas : ∑ i, ε i • (M.ρ (f i) * M.ρ (f i)) = casimirOp M b ε := by
    simp_rw [hρf, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    unfold casimirOp
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have e : ∀ l, ∑ i, (ε i * (ε j * B (b j) (f i) * (ε l * B (b l) (f i)))) •
        (M.ρ (b j) * M.ρ (b l)) = (if j = l then ε j else 0) • (M.ρ (b j) * M.ρ (b l)) := by
      intro l
      rw [← Finset.sum_smul]
      congr 1
      have := hsum j l
      rw [horth] at this
      calc ∑ i, ε i * (ε j * B (b j) (f i) * (ε l * B (b l) (f i)))
          = ε l * ε j * ∑ i, ε i * B (b j) (f i) * B (b l) (f i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = if j = l then ε j else 0 := by
            rw [this]
            split_ifs with hjl
            · subst hjl
              have := hε j
              linear_combination (ε j) * this
            · ring
    rw [Finset.sum_congr rfl fun l _ => e l]
    simp
  conv_rhs => rw [← hcas]
  unfold casimirOp
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, σ_mul_ρ, mul_assoc, σ_mul_ρ, ← mul_assoc]

end Casimir

section KType

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem ρ_mem_of_stable (M : h.GKModule K V) {F : Submodule ℂ V}
    (hF : ∀ k, ∀ v ∈ F, M.σ k v ∈ F) {Z : h.lieSubalgebra}
    (hZ : ∀ t : ℝ, h.expG (t • h.ofLie Z) ∈ K) {v : V} (hv : v ∈ F) : M.ρ Z v ∈ F := by
  by_contra hnot
  obtain ⟨ψ, hψ, hψF⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hd := M.hasDerivAt_coeff (h.ofLie Z) hZ ψ v
  have h0 : (fun t : ℝ => ψ (M.σ ⟨h.expG (t • h.ofLie Z), hZ t⟩ v)) = fun _ => 0 := by
    funext t
    have hm : ψ (M.σ ⟨_, hZ t⟩ v) ∈ F.map ψ := ⟨_, hF _ v hv, rfl⟩
    rw [hψF] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  rw [h0] at hd
  exact hψ (hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))

theorem map_ρ_of_equivariant (M : h.GKModule K V) {F : Submodule ℂ V}
    (hF : ∀ k, ∀ v ∈ F, M.σ k v ∈ F) (f : F →ₗ[ℂ] V)
    (hf : ∀ k (v : F), f ⟨M.σ k v, hF k v v.2⟩ = M.σ k (f v)) {Z : h.lieSubalgebra}
    (hZ : ∀ t : ℝ, h.expG (t • h.ofLie Z) ∈ K) (v : F) (hv : M.ρ Z v ∈ F) :
    f ⟨M.ρ Z v, hv⟩ = M.ρ Z (f v) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ψ
  rw [map_sub, sub_eq_zero]
  obtain ⟨ψ', hψ'⟩ := LinearMap.exists_extend (ψ ∘ₗ f)
  have e : ∀ w : F, ψ' w = ψ (f w) := fun w => congrArg (fun g => g w) hψ'
  have h1 := M.hasDerivAt_coeff (h.ofLie Z) hZ ψ' v
  have h2 := M.hasDerivAt_coeff (h.ofLie Z) hZ ψ (f v)
  have e2 : (fun t : ℝ => ψ' (M.σ ⟨h.expG (t • h.ofLie Z), hZ t⟩ v)) =
      fun t => ψ (M.σ ⟨h.expG (t • h.ofLie Z), hZ t⟩ (f v)) := by
    funext t
    rw [← hf ⟨h.expG (t • h.ofLie Z), hZ t⟩ v]
    exact e ⟨_, _⟩
  rw [e2] at h1
  have := h1.unique h2
  rw [← e ⟨_, hv⟩]
  exact this

def toSub (M : h.GKModule K V) (m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule) :
    Submodule ℂ V where
  carrier := {v | M.σ.asModuleEquiv.symm v ∈ m}
  add_mem' {x y} hx hy := by
    show M.σ.asModuleEquiv.symm (x + y) ∈ m
    rw [map_add]
    exact m.add_mem hx hy
  zero_mem' := by
    show M.σ.asModuleEquiv.symm 0 ∈ m
    rw [map_zero]
    exact m.zero_mem
  smul_mem' c x hx := by
    show M.σ.asModuleEquiv.symm (c • x) ∈ m
    rw [Representation.asModuleEquiv_symm_map_smul]
    exact m.smul_mem _ hx

theorem mem_toSub (M : h.GKModule K V) {m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule} {v : V} :
    v ∈ toSub M m ↔ M.σ.asModuleEquiv.symm v ∈ m := Iff.rfl

theorem σ_mem_toSub (M : h.GKModule K V) (m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule) (k : K)
    {v : V} (hv : v ∈ toSub M m) : M.σ k v ∈ toSub M m := by
  rw [mem_toSub, Representation.asModuleEquiv_symm_map_rho]
  exact m.smul_mem _ hv

def ofStable (M : h.GKModule K V) (O : Submodule ℂ V) (hO : ∀ k, ∀ v ∈ O, M.σ k v ∈ O) :
    Submodule (MonoidAlgebra ℂ K) M.σ.asModule where
  carrier := {x | M.σ.asModuleEquiv x ∈ O}
  add_mem' {x y} hx hy := by
    show M.σ.asModuleEquiv (x + y) ∈ O
    rw [map_add]
    exact O.add_mem hx hy
  zero_mem' := by
    show M.σ.asModuleEquiv 0 ∈ O
    rw [map_zero]
    exact O.zero_mem
  smul_mem' a x hx := by
    induction a using MonoidAlgebra.induction_on with
    | of k =>
      show M.σ.asModuleEquiv (MonoidAlgebra.of ℂ K k • x) ∈ O
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
      exact hO k _ hx
    | add a b ha hb =>
      rw [add_smul]
      show M.σ.asModuleEquiv (a • x + b • x) ∈ O
      rw [map_add]
      exact O.add_mem ha hb
    | smul r a ha =>
      rw [smul_assoc]
      show M.σ.asModuleEquiv (r • (a • x)) ∈ O
      rw [map_smul]
      exact O.smul_mem r ha

theorem mem_ofStable (M : h.GKModule K V) (O : Submodule ℂ V) (hO : ∀ k, ∀ v ∈ O, M.σ k v ∈ O)
    {x : M.σ.asModule} : x ∈ ofStable M O hO ↔ M.σ.asModuleEquiv x ∈ O := Iff.rfl

theorem sumSq_mem_of_stable (M : h.GKModule K V) {ι : Type*} [Fintype ι]
    (Z : ι → h.lieSubalgebra) (hZ : ∀ i (t : ℝ), h.expG (t • h.ofLie (Z i)) ∈ K) {F : Submodule ℂ V}
    (hF : ∀ k, ∀ v ∈ F, M.σ k v ∈ F) {v : V} (hv : v ∈ F) :
    (∑ i, M.ρ (Z i) * M.ρ (Z i)) v ∈ F := by
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ =>
    ρ_mem_of_stable M hF (hZ i) (ρ_mem_of_stable M hF (hZ i) hv)

theorem aeval_eq_zero_of_equiv (M : h.GKModule K V) {ι : Type*} [Fintype ι]
    (Z : ι → h.lieSubalgebra) (hZ : ∀ i (t : ℝ), h.expG (t • h.ofLie (Z i)) ∈ K)
    {S m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule} (g : m ≃ₗ[MonoidAlgebra ℂ K] S)
    (q : Polynomial ℂ)
    (hq : ∀ v ∈ toSub M S, Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) q v = 0)
    {x : M.σ.asModule} (hx : x ∈ m) :
    Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) q (M.σ.asModuleEquiv x) = 0 := by
  have hFs : ∀ k, ∀ v ∈ toSub M S, M.σ k v ∈ toSub M S := fun k v hv => σ_mem_toSub M S k hv
  have hCF : ∀ v ∈ toSub M S, (∑ i, M.ρ (Z i) * M.ρ (Z i)) v ∈ toSub M S :=
    fun v hv => sumSq_mem_of_stable M Z hZ hFs hv
  let fm : toSub M S →ₗ[ℂ] V :=
    { toFun := fun w => M.σ.asModuleEquiv (g.symm ⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ : m)
      map_add' := fun w w' => by
        have e : (⟨M.σ.asModuleEquiv.symm ((w + w' : toSub M S) : V), (w + w').2⟩ : S) =
            ⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ + ⟨M.σ.asModuleEquiv.symm (w' : V), w'.2⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [e, map_add, Submodule.coe_add, map_add]
      map_smul' := fun a w => by
        have e : (⟨M.σ.asModuleEquiv.symm ((a • w : toSub M S) : V), (a • w).2⟩ : S) =
            a • (⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ : S) :=
          Subtype.ext (map_smul _ _ _)
        have e2 : g.symm (a • (⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ : S)) =
            a • g.symm ⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ := by
          rw [← algebraMap_smul (MonoidAlgebra ℂ K) a, map_smul, algebraMap_smul]
        rw [e, e2, Submodule.coe_smul_of_tower, map_smul]
        rfl }
  have hfm : ∀ k (v : toSub M S), fm ⟨M.σ k v, hFs k v v.2⟩ = M.σ k (fm v) := by
    intro k v
    have e : (⟨M.σ.asModuleEquiv.symm (M.σ k v), hFs k v v.2⟩ : S) =
        MonoidAlgebra.of ℂ K k • (⟨M.σ.asModuleEquiv.symm (v : V), v.2⟩ : S) :=
      Subtype.ext (by rw [Submodule.coe_smul]; exact Representation.asModuleEquiv_symm_map_rho _ _ _)
    show M.σ.asModuleEquiv (g.symm ⟨M.σ.asModuleEquiv.symm (M.σ k v), _⟩ : m) = _
    rw [e, map_smul, Submodule.coe_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
    rfl
  set A : Module.End ℂ (toSub M S) := LinearMap.restrict _ hCF with hA
  have hAC : ∀ w : toSub M S, fm (A w) = (∑ i, M.ρ (Z i) * M.ρ (Z i)) (fm w) := by
    intro w
    have e : A w = ∑ i, (⟨M.ρ (Z i) (M.ρ (Z i) w),
        ρ_mem_of_stable M hFs (hZ i) (ρ_mem_of_stable M hFs (hZ i) w.2)⟩ : toSub M S) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      show (∑ i, M.ρ (Z i) * M.ρ (Z i)) (w : V) = _
      rw [LinearMap.sum_apply]
      rfl
    rw [e, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.End.mul_apply]
    rw [map_ρ_of_equivariant M hFs fm hfm (hZ i) ⟨_, ρ_mem_of_stable M hFs (hZ i) w.2⟩,
      map_ρ_of_equivariant M hFs fm hfm (hZ i) w]
  have hAsub : ∀ w : toSub M S, ((Polynomial.aeval A q w : toSub M S) : V) =
      Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) q (w : V) :=
    AutomorphicForm.map_aeval_apply_of_intertwine (toSub M S).subtype (fun _ => rfl) q
  set y : S := g ⟨x, hx⟩ with hy
  have hyF : M.σ.asModuleEquiv (y : M.σ.asModule) ∈ toSub M S := by
    rw [mem_toSub, LinearEquiv.symm_apply_apply]
    exact y.2
  have hfy : fm ⟨_, hyF⟩ = M.σ.asModuleEquiv x := by
    show M.σ.asModuleEquiv (g.symm ⟨M.σ.asModuleEquiv.symm
      (M.σ.asModuleEquiv (y : M.σ.asModule)), _⟩ : m) = _
    have e : (⟨M.σ.asModuleEquiv.symm (M.σ.asModuleEquiv (y : M.σ.asModule)), hyF⟩ : S) = y :=
      Subtype.ext (LinearEquiv.symm_apply_apply _ _)
    rw [e, hy, LinearEquiv.symm_apply_apply]
  have h0 : Polynomial.aeval A q ⟨_, hyF⟩ = 0 :=
    Subtype.ext ((hAsub _).trans (hq _ hyF))
  have h3 := AutomorphicForm.map_aeval_apply_of_intertwine fm hAC q ⟨_, hyF⟩
  rw [h0, map_zero, hfy] at h3
  exact h3.symm

theorem finiteDimensional_toSub_of_isSimpleModule (M : h.GKModule K V)
    {S : Submodule (MonoidAlgebra ℂ K) M.σ.asModule} (hS : IsSimpleModule (MonoidAlgebra ℂ K) S) :
    FiniteDimensional ℂ (toSub M S) ∧ Nontrivial (toSub M S) := by
  have hSnt : Nontrivial S := IsSimpleModule.nontrivial (MonoidAlgebra ℂ K) S
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  set O := Submodule.span ℂ (range fun k : K => M.σ k (M.σ.asModuleEquiv (s₀ : M.σ.asModule)))
    with hOdef
  have hOfin : FiniteDimensional ℂ O := M.locallyFinite _
  have hOs : ∀ k, ∀ v ∈ O, M.σ k v ∈ O := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨k * k', rfl⟩
    | zero => rw [map_zero]; exact O.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact O.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact O.smul_mem a hx
  have hs₀O : M.σ.asModuleEquiv (s₀ : M.σ.asModule) ∈ O :=
    Submodule.subset_span ⟨1, show M.σ 1 _ = _ by rw [map_one, Module.End.one_apply]⟩
  have hatom : IsAtom S := (isSimpleModule_iff_isAtom).1 hS
  have hSN : S ≤ ofStable M O hOs := by
    rcases hatom.le_iff.1 (inf_le_right : ofStable M O hOs ⊓ S ≤ S) with h0 | h1
    · exfalso
      have hmem : (s₀ : M.σ.asModule) ∈ ofStable M O hOs ⊓ S := ⟨hs₀O, s₀.2⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hs₀ (Subtype.ext hmem)
    · rw [← h1]
      exact inf_le_left
  have hFO : toSub M S ≤ O := fun v hv => by
    exact (mem_ofStable M O hOs).1 (hSN hv)
  refine ⟨Submodule.finiteDimensional_of_le hFO, ?_⟩
  have hs₀F : M.σ.asModuleEquiv (s₀ : M.σ.asModule) ∈ toSub M S := by
    rw [mem_toSub, LinearEquiv.symm_apply_apply]
    exact s₀.2
  refine ⟨⟨⟨_, hs₀F⟩, 0, fun he => hs₀ ?_⟩⟩
  have h0 : M.σ.asModuleEquiv (s₀ : M.σ.asModule) = 0 := congrArg Subtype.val he
  apply Subtype.ext
  rw [Submodule.coe_zero]
  exact M.σ.asModuleEquiv.injective (h0.trans (map_zero _).symm)

theorem exists_aeval_eq_zero_of_mem_isotypic (M : h.GKModule K V) {ι : Type*} [Fintype ι]
    (Z : ι → h.lieSubalgebra) (hZ : ∀ i (t : ℝ), h.expG (t • h.ofLie (Z i)) ∈ K)
    {c : Submodule (MonoidAlgebra ℂ K) M.σ.asModule}
    (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) M.σ.asModule) :
    ∃ q : Polynomial ℂ, q.Monic ∧ 0 < q.natDegree ∧
      ∀ v : V, M.σ.asModuleEquiv.symm v ∈ c →
        Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) q v = 0 := by
  obtain ⟨S, hS, rfl⟩ := hc
  obtain ⟨hFfin, hFnt⟩ := finiteDimensional_toSub_of_isSimpleModule M hS
  have hFs : ∀ k, ∀ v ∈ toSub M S, M.σ k v ∈ toSub M S := fun k v hv => σ_mem_toSub M S k hv
  have hCF : ∀ v ∈ toSub M S, (∑ i, M.ρ (Z i) * M.ρ (Z i)) v ∈ toSub M S :=
    fun v hv => sumSq_mem_of_stable M Z hZ hFs hv
  let A : Module.End ℂ (toSub M S) := LinearMap.restrict _ hCF
  refine ⟨A.charpoly, LinearMap.charpoly_monic A, ?_, ?_⟩
  · rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_pos
  have hvanF : ∀ v ∈ toSub M S, Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) A.charpoly v = 0 := by
    intro v hv
    have := AutomorphicForm.map_aeval_apply_of_intertwine (toSub M S).subtype (A := A)
      (B := ∑ i, M.ρ (Z i) * M.ρ (Z i)) (fun _ => rfl) A.charpoly ⟨v, hv⟩
    rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at this
    exact this.symm
  intro v hv
  have hv' : M.σ.asModuleEquiv.symm v ∈ ⨆ m : {m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule |
      Nonempty (m ≃ₗ[MonoidAlgebra ℂ K] S)}, m.1 := by
    rw [← sSup_eq_iSup']
    exact hv
  have key := Submodule.iSup_induction _ (motive := fun x =>
    Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) A.charpoly (M.σ.asModuleEquiv x) = 0) hv'
    (fun m x hx => aeval_eq_zero_of_equiv M Z hZ m.2.some A.charpoly hvanF hx)
    (by rw [map_zero, map_zero])
    (fun x y hx hy => by rw [map_add, map_add, hx, hy, add_zero])
  rwa [LinearEquiv.apply_symm_apply] at key

end KType

end UnitaryAdmissible

end GroundTheory.Automorphic
