import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeClosed

section Algebra

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem pairing_map (v : Fin 2 → Module.Dual R N) (g : M →ₗ[R] N) (t : ⋀[R]^2 M) :
    exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) (exteriorPower.map 2 g t) =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) t := by
  have e : exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) ∘ₗ exteriorPower.map 2 g =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) := by
    apply exteriorPower.linearMap_ext
    ext x
    simp [exteriorPower.pairingDual_ιMulti_ιMulti]
  exact LinearMap.congr_fun e t

theorem eq_zero_of_pairing [Module.Finite R M] [Module.Projective R M] (t : ⋀[R]^2 M)
    (h : ∀ v : Fin 2 → Module.Dual R M, exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 v) t = 0) :
    t = 0 := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hu : exteriorPower.map 2 g t = 0 := by
    let b := Pi.basisFun R (Fin n)
    refine (b.exteriorPower 2).repr.injective (Finsupp.ext fun s ↦ ?_)
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual, exteriorPower.ιMulti_family]
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact (pairing_map _ g t).trans (h _)
  exact exteriorPower.map_injective f hfg (hu.trans (map_zero _).symm)

theorem eq_zero_of_additive [Module.Finite R M] [Module.Projective R M] (A B : M →ₗ[R] N)
    (hb : Function.Bijective fun x : M × M ↦ A x.1 + B x.2) (t : ⋀[R]^2 M)
    (h : exteriorPower.map 2 (A + B) t = exteriorPower.map 2 A t + exteriorPower.map 2 B t) : t = 0 := by
  let e : (M × M) ≃ₗ[R] N := LinearEquiv.ofBijective (A.coprod B) ((funext fun x ↦ LinearMap.coprod_apply A B x : ⇑(A.coprod B) = _) ▸ hb)
  have eA : ∀ x, e.symm (A x) = (x, 0) := fun x ↦ e.symm_apply_eq.2 (by simp [e])
  have eB : ∀ x, e.symm (B x) = (0, x) := fun x ↦ e.symm_apply_eq.2 (by simp [e])
  refine eq_zero_of_pairing t fun v ↦ ?_
  let L : Module.Dual R N := v 0 ∘ₗ LinearMap.fst R M M ∘ₗ e.symm.toLinearMap
  let L' : Module.Dual R N := v 1 ∘ₗ LinearMap.snd R M M ∘ₗ e.symm.toLinearMap
  have key := congrArg (exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 ![L, L'])) h
  rw [map_add, pairing_map, pairing_map, pairing_map] at key
  have h0 : (fun i ↦ ![L, L'] i ∘ₗ (A + B)) = v := by
    funext i
    fin_cases i
    · ext x; simp [L, eA, eB]
    · ext x; simp [L', eA, eB]
  have hA : (fun i ↦ ![L, L'] i ∘ₗ A) 1 = 0 := by ext x; simp [L', eA]
  have hB : (fun i ↦ ![L, L'] i ∘ₗ B) 0 = 0 := by ext x; simp [L, eB]
  rw [h0, (exteriorPower.ιMulti R 2).map_coord_zero (m := fun i ↦ ![L, L'] i ∘ₗ A) 1 hA,
    (exteriorPower.ιMulti R 2).map_coord_zero (m := fun i ↦ ![L, L'] i ∘ₗ B) 0 hB] at key
  simpa using key

end Algebra

section Forms

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem nu_natural (c : CoefMap (RingHom.id R) F G) (ν : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (ν' : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hν : ∀ a b T, ν (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hν' : ∀ a b T, ν' (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (t : ⋀[R]^2 (Glob1 F)) (T : D) :
    qOm c 2 T (ν t (c.G.obj T)) = ν' (exteriorPower.map 2 (pullGlob1 c) t) T := by
  have e : (qOm c 2 T : _ →ₗ[R] _) ∘ₗ LinearMap.proj (c.G.obj T) ∘ₗ ν =
      LinearMap.proj T ∘ₗ ν' ∘ₗ exteriorPower.map 2 (pullGlob1 c) := by
    apply exteriorPower.linearMap_ext
    ext x
    obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] := ⟨x 0, x 1, by funext i; fin_cases i <;> rfl⟩
    have hy : (pullGlob1 c : Glob1 F →ₗ[R] Glob1 G) ∘ ![a, b] = ![pullGlob1 c a, pullGlob1 c b] := by
      funext i; fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      exteriorPower.map_apply_ιMulti]
    rw [hy, hν, hν']
    exact congrArg Subtype.val (qOm_wedge c (a.1 (c.G.obj T)) (b.1 (c.G.obj T)))
  exact LinearMap.congr_fun e t

end Forms

theorem closedSt_of_twoFormCohSt : TwoFormCohSt → ClosedSt := by
  intro h2 R _ C _ F hF hBi
  obtain ⟨D, _, G, m, p, q, hS, hP, -, hb, -, hm, -⟩ := hBi
  have hG : Framed G := by
    obtain ⟨-, -, h1, h3⟩ := hF
    let e : (Glob1 F × Glob1 F) ≃ₗ[R] Glob1 G := LinearEquiv.ofBijective ((pullGlob1 p).coprod (pullGlob1 q))
      ((funext fun x ↦ LinearMap.coprod_apply (pullGlob1 p) (pullGlob1 q) x :
        ⇑((pullGlob1 p).coprod (pullGlob1 q)) = _) ▸ hb)
    exact ⟨hS, hP, Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  obtain ⟨ν, hν, -, hsurj⟩ := h2 R C F hF
  obtain ⟨ν', hν', hinj, -⟩ := h2 R D G hG
  obtain ⟨-, -, hfin, hproj⟩ := hF
  refine eq_top_iff.2 fun ω₀ _ T ↦ ?_
  obtain ⟨t, ht⟩ := hsurj (fun T ↦ dOne R _ (ω₀.1 T)) fun T T' φ ↦ by
    rw [pOm_dOne, ω₀.2 φ]
  have step : ∀ (c : CoefMap (RingHom.id R) F G),
      ν' (exteriorPower.map 2 (pullGlob1 c) t) = fun T ↦ dOne R _ ((pullGlob1 c ω₀).1 T) := by
    intro c
    funext T
    rw [← nu_natural c ν ν' hν hν' t T, ht]
    exact qOm_dOne c (ω₀.1 (c.G.obj T))
  have hadd : exteriorPower.map 2 (pullGlob1 p + pullGlob1 q) t =
      exteriorPower.map 2 (pullGlob1 p) t + exteriorPower.map 2 (pullGlob1 q) t := by
    have h1 : pullGlob1 p + pullGlob1 q = pullGlob1 m := LinearMap.ext fun ω ↦ (hm ω).symm
    apply hinj
    rw [h1, step m, map_add, step p, step q]
    funext T'
    change dOne R _ ((pullGlob1 m ω₀).1 T') = dOne R _ ((pullGlob1 p ω₀).1 T') + dOne R _ ((pullGlob1 q ω₀).1 T')
    rw [hm, ← map_add]
    rfl
  have ht0 : t = 0 := eq_zero_of_additive _ _ hb t hadd
  have := congrFun ht T
  rw [ht0, map_zero] at this
  exact this.symm

end GlobalTheory.CompanionTheory.HodgeClosed
