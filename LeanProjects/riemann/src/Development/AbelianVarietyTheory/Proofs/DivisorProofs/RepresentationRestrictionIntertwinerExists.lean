import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionSubmoduleFunctionalInjectiveStatement
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL GlobalTheory.LocTypeGood

namespace GlobalTheory.LocTypeExt

theorem map_prod_shift {α V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (a : α → Module.End ℂ V) (b : α → Module.End ℂ W) (h : ∀ i v, T (a i v) = b i (T v))
    (l : List (α × ℂ)) (v : V) :
    T ((l.map fun p => a p.1 - p.2 • (1 : Module.End ℂ V)).prod v) =
      (l.map fun p => b p.1 - p.2 • (1 : Module.End ℂ W)).prod (T v) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, h, ih]

theorem eigen_prod_shift {α V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (L : V →ₗ[ℂ] W) (a : α → Module.End ℂ V) (ξ : α → ℂ) (M : Submodule ℂ V) (hM : ∀ i, ∀ v ∈ M, a i v ∈ M)
    (h : ∀ v ∈ M, ∀ i, L (a i v) = ξ i • L v) (l : List (α × ℂ)) (v : V) (hv : v ∈ M) :
    (l.map fun p => a p.1 - p.2 • (1 : Module.End ℂ V)).prod v ∈ M ∧
      L ((l.map fun p => a p.1 - p.2 • (1 : Module.End ℂ V)).prod v) = (l.map fun p => ξ p.1 - p.2).prod • L v := by
  induction l with
  | nil => simp [hv]
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul]
    refine ⟨M.sub_mem (hM _ _ ih.1) (M.smul_mem _ ih.1), ?_⟩
    rw [h _ ih.1, ih.2, ← sub_smul, smul_smul]

theorem imgSpan_le {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ G V) (ρ : Representation ℂ G W) (S : Submodule ℂ W)
    (h : ∀ T : V →ₗ[ℂ] W, (∀ g v, T (π g v) = ρ g (T v)) → ∀ v, T v ∈ S) : imgSpan π ρ ≤ S := by
  refine iSup_le fun T => iSup_le fun hT => ?_
  rintro _ ⟨v, rfl⟩
  exact h T (fun g v => LinearMap.congr_fun (hT g) v) v

theorem mem_imgSpan {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ G V) (ρ : Representation ℂ G W) (T : V →ₗ[ℂ] W) (hT : ∀ g v, T (π g v) = ρ g (T v)) (v : V) :
    T v ∈ imgSpan π ρ :=
  Submodule.mem_iSup_of_mem T (Submodule.mem_iSup_of_mem (fun g => LinearMap.ext (hT g)) ⟨v, rfl⟩)

theorem imgSpan_stable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ G V) (ρ : Representation ℂ G W) (g : G) : ∀ φ ∈ imgSpan π ρ, ρ g φ ∈ imgSpan π ρ := by
  have : imgSpan π ρ ≤ (imgSpan π ρ).comap (ρ g) := imgSpan_le π ρ _ fun T hT v => by
    rw [Submodule.mem_comap, ← hT]
    exact mem_imgSpan π ρ T hT _
  exact fun φ hφ => this hφ

theorem imgSpan_smooth {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ G V) (ρ : Representation ℂ G W) (hπ : IsSmooth π) :
    ∀ φ ∈ imgSpan π ρ, IsOpen {g | ρ g φ = φ} := by
  have : imgSpan π ρ ≤ smoothPart ρ := imgSpan_le π ρ _ fun T hT v => by
    let S : Subgroup G :=
      { carrier := {g | ρ g (T v) = T v}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    refine S.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) ?_)
    intro g hg
    show ρ g (T v) = T v
    rw [← hT, show π g v = v from hg]
  exact fun φ hφ => this hφ

theorem eigenMap_mem_imgSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n)
    (V V₁ X G₁ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup X] [Module ℂ X] [Group G₁]
    (I : Representation ℂ (GL (Fin n) k) V) (I₁ : Representation ℂ (GL (Fin m) k) V₁) (π : Representation ℂ (GL (Fin n) k) X)
    (ι : GL (Fin m) k →* G₁), IsSmooth I → Function.Injective ι →
    ∀ (ξ : kˣ × kˣ → ℂ) (l : List ((kˣ × kˣ) × ℂ)), (∀ p ∈ l, ξ p.1 ≠ p.2) →
    ∀ A : V₁ →ₗ[ℂ] Jacquet I (unipRad k e),
      (∀ h w, A (I₁ h w) = jacU e I (midIncl k m h) (A w)) →
      (∀ w, (l.map fun p => jacU e I (torusPt k m p.1.1 p.1.2) - p.2 • (1 : Module.End ℂ (Jacquet I (unipRad k e)))).prod w ∈
        LinearMap.range A) →
    ∀ (M : Submodule ℂ X) (Λ : X →ₗ[ℂ] (G₁ → ℂ)), M ≤ imgSpan I π → (∀ g, ∀ φ ∈ M, π g φ ∈ M) →
      (∀ φ ∈ M, ∀ u ∈ unipRad k e, Λ (π u φ) = Λ φ) →
      (∀ φ ∈ M, ∀ h, Λ (π (leviEmb k e (midIncl k m h)) φ) = rightReg ℂ G₁ ℂ (ι h) (Λ φ)) →
      (∀ φ ∈ M, ∀ t₁ t₂, Λ (π (leviEmb k e (torusPt k m t₁ t₂)) φ) = ξ (t₁, t₂) • Λ φ) →
      ∀ φ ∈ M, Λ φ ∈ imgSpan I₁ ((rightReg ℂ G₁ ℂ).comp ι) := by
  intro k _ _ _ _ n m e V V₁ X G₁ _ _ _ _ _ _ _ I I₁ π ι hI hι ξ l hl A hA hP M Λ hMU hM hN hmid htor φ hφ
  obtain ⟨Λ', h1, h2, h3⟩ := GlobalTheory.T.restriction_submodule_functional_injective k n m e X G₁ π ι hι (imgSpan I π) M Λ hMU (imgSpan_stable I π) hM
    (imgSpan_smooth I π hI) hN hmid
  let aX : kˣ × kˣ → Module.End ℂ X := fun t => π (leviEmb k e (torusPt k m t.1 t.2))
  let P : Module.End ℂ X := (l.map fun p => aX p.1 - p.2 • (1 : Module.End ℂ X)).prod
  have ha := eigen_prod_shift Λ aX ξ M (fun t v hv => hM _ v hv) (fun v hv t => htor v hv t.1 t.2) l φ hφ
  have hc : (l.map fun p => ξ p.1 - p.2).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    intro h0
    obtain ⟨p, hp, hp0⟩ := List.mem_map.1 h0
    exact hl p hp (sub_eq_zero.1 hp0)
  have hb : imgSpan I π ≤ (imgSpan I₁ ((rightReg ℂ G₁ ℂ).comp ι)).comap (Λ' ∘ₗ P) := by
    refine imgSpan_le I π _ fun T hT v => ?_
    have hker : twKer I (unipRad k e) 1 ≤ LinearMap.ker (Λ' ∘ₗ T) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, y, rfl⟩
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, SetLike.mem_coe, LinearMap.mem_ker, map_sub,
        LinearMap.comp_apply, hT]
      rw [h2 _ (mem_imgSpan I π T hT y) _ u.2, sub_self]
    let B : Jacquet I (unipRad k e) →ₗ[ℂ] (G₁ → ℂ) := (twKer I (unipRad k e) 1).liftQ (Λ' ∘ₗ T) hker
    have hB : ∀ y : V, B (Submodule.Quotient.mk y) = Λ' (T y) := fun y => rfl
    have hBeq : ∀ h y, B (jacU e I (midIncl k m h) y) = rightReg ℂ G₁ ℂ (ι h) (B y) := by
      intro h y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change Λ' (T (I (leviEmb k e (midIncl k m h)) y)) = rightReg ℂ G₁ ℂ (ι h) (Λ' (T y))
      rw [hT, h3 _ (mem_imgSpan I π T hT y)]
    let aV : kˣ × kˣ → Module.End ℂ V := fun t => I (leviEmb k e (torusPt k m t.1 t.2))
    have e1 := map_prod_shift T aV aX (fun t y => hT _ y) l v
    have e2 := map_prod_shift (twKer I (unipRad k e) 1).mkQ aV (fun t => jacU e I (torusPt k m t.1 t.2))
      (fun t y => rfl) l v
    obtain ⟨w, hw⟩ := hP ((twKer I (unipRad k e) 1).mkQ v)
    have e3 : Λ' (P (T v)) = (B ∘ₗ A) w := by
      rw [LinearMap.comp_apply, hw, ← e2, Submodule.mkQ_apply, hB, e1]
    rw [Submodule.mem_comap, LinearMap.comp_apply, e3]
    refine mem_imgSpan _ _ _ (fun h y => ?_) w
    rw [LinearMap.comp_apply, hA, hBeq]
    rfl
  have h4 : Λ' (P φ) ∈ imgSpan I₁ ((rightReg ℂ G₁ ℂ).comp ι) := hb (hMU hφ)
  rw [h1 _ ha.1, ha.2] at h4
  exact (Submodule.smul_mem_iff _ hc).1 h4

end GlobalTheory.LocTypeExt
