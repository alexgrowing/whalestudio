import Mathlib

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KaehlerTower

theorem append_of_shortExact {A M₁ M₂ M₃ : Type*} [CommRing A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) {e m : ℕ} (u : Fin e → M₁) (w : Fin m → M₂)
    (hu : LinearIndependent A u) (hus : Submodule.span A (Set.range u) = ⊤)
    (hw : LinearIndependent A (fun i => g (w i)))
    (hws : Submodule.span A (Set.range fun i => g (w i)) = ⊤) :
    LinearIndependent A (Fin.append (fun i => f (u i)) w) ∧
      Submodule.span A (Set.range (Fin.append (fun i => f (u i)) w)) = ⊤ := by
  have happ : Fin.append (fun i => f (u i)) w =
      Sum.elim (fun i => f (u i)) w ∘ finSumFinEquiv.symm := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  have hfu : LinearIndependent A (fun i => f (u i)) :=
    hu.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hw' : LinearIndependent A w := LinearIndependent.of_comp g hw
  have hcomp : ∀ y, g (f y) = 0 := fun y => (hfg (f y)).mpr ⟨y, rfl⟩
  have hdisj : Disjoint (Submodule.span A (Set.range fun i => f (u i)))
      (Submodule.span A (Set.range w)) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hgx : g x = 0 := by
      have hle : Submodule.span A (Set.range fun i => f (u i)) ≤ LinearMap.ker g := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hcomp _
      exact hle hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hx'
    have h0 : ∑ i, c i • g (w i) = 0 := by simpa [map_sum] using hgx
    have hc := (Fintype.linearIndependent_iff.mp hw) c h0
    simp [hc]
  constructor
  · rw [happ]
    exact (hfu.sum_type hw' hdisj).comp _ finSumFinEquiv.symm.injective
  · rw [happ, Set.range_comp, finSumFinEquiv.symm.surjective.range_eq, Set.image_univ,
      Set.Sum.elim_range, Submodule.span_union, eq_top_iff]
    intro x _
    have hgx : g x ∈ Submodule.span A (Set.range fun i => g (w i)) := hws ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hgx
    have hker : g (x - ∑ i, c i • w i) = 0 := by
      simp [map_sum, hc]
    obtain ⟨y, hy⟩ := (hfg _).mp hker
    have hy' : y ∈ Submodule.span A (Set.range u) := hus ▸ Submodule.mem_top
    have hfy : f y ∈ Submodule.span A (Set.range fun i => f (u i)) := by
      have := Submodule.mem_map_of_mem (f := f) hy'
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hsum : ∑ i, c i • w i ∈ Submodule.span A (Set.range w) :=
      Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hx : x = f y + ∑ i, c i • w i := by rw [hy]; abel
    rw [hx]
    exact Submodule.add_mem_sup hfy hsum

theorem kaehler_basis_tower : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] (e m : ℕ) (z : Fin e → S) (w : Fin m → T),
    LinearIndependent S (fun i => KaehlerDifferential.D R S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D R S (z i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) ∧
    Submodule.span T (Set.range fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) = ⊤ := by
  intro R S T _ _ _ _ _ _ _ _ e m z w hz hzs hw hws
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
    have : Subsingleton (Algebra.H1Cotangent S T) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [Subsingleton.elim y 0, map_zero]
  have hex : Function.Exact (KaehlerDifferential.mapBaseChange R S T)
      (KaehlerDifferential.map R S T T) := KaehlerDifferential.exact_mapBaseChange_map R S T
  let b : Module.Basis (Fin e) S (Ω[S⁄R]) := Module.Basis.mk hz hzs.ge
  let bT := Algebra.TensorProduct.basis T b
  have hb : ∀ i, bT i = (1 : T) ⊗ₜ[S] KaehlerDifferential.D R S (z i) := by
    intro i
    simp [bT, b]
  have hmain := append_of_shortExact (KaehlerDifferential.mapBaseChange R S T)
    (KaehlerDifferential.map R S T T) hinj hex (fun i => bT i)
    (fun i => KaehlerDifferential.D R T (w i)) bT.linearIndependent bT.span_eq
    (by simpa [KaehlerDifferential.map_D] using hw)
    (by simpa [KaehlerDifferential.map_D] using hws)
  have hfun : (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) =
      Fin.append (fun i => KaehlerDifferential.mapBaseChange R S T (bT i))
        (fun i => KaehlerDifferential.D R T (w i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [hb, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
    · simp
  rw [hfun]
  exact hmain

end GlobalTheory.CompanionTheory.KaehlerTower
