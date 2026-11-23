import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanishCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section LocE

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)

def locConeE (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod S N M.coneSubE I →ₗ[Poly S N] ConeE S x E :=
  LocalizedModule.lift (monos I) M.coneSubE.subtype fun s => by
    rw [Module.End.isUnit_iff]
    obtain ⟨e, he⟩ := monos_isHomogeneous s.2
    exact bijective_smul_of_isHomogeneous he (aeval_ne_zero_of_mem_monos_support hI s.2)

theorem locConeE_mk (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) (m : M.coneSubE)
    (s : monos (S := S) I) :
    (s : Poly S N) • locConeE M I hI (LocalizedModule.mk m s) = m := by
  have h1 : (s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSubE) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel s m
  have h2 : locConeE M I hI ((s : Poly S N) • LocalizedModule.mk m s) = m := by
    change LocalizedModule.lift (monos I) M.coneSubE.subtype _
      ((s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSubE)) = m
    rw [h1]
    simp
  have h3 := (locConeE M I hI).map_smul (s : Poly S N) (LocalizedModule.mk m s : LocMod S N M.coneSubE I)
  exact h3.symm.trans h2

theorem locConeE_mk_eq {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {m : M.coneSubE}
    {s : monos (S := S) I} {w : ConeE S x E} (h : (s : Poly S N) • w = m) :
    locConeE M I hI (LocalizedModule.mk m s) = w := by
  obtain ⟨e, he⟩ := monos_isHomogeneous s.2
  exact (bijective_smul_of_isHomogeneous he (aeval_ne_zero_of_mem_monos_support hI s.2)).1
    ((locConeE_mk M I hI m s).trans h.symm)

theorem locConeE_injective (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locConeE M I hI) := by
  refine (injective_iff_map_eq_zero _).mpr fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSubE => locConeE M I hI z = 0 → z = 0)
    (fun m s hz => ?_) z
  have h := locConeE_mk M I hI m s
  rw [hz, smul_zero] at h
  have hm : m = 0 := Subtype.ext h.symm
  rw [hm, LocalizedModule.zero_mk]

theorem locConeE_locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSubE I) :
    locConeE M J hJ (locRes h z) = locConeE M I (h.trans hJ) z := by
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSubE =>
      locConeE M J hJ (locRes h z) = locConeE M I (h.trans hJ) z) (fun m s => ?_) z
  rw [locRes_mk]
  exact locConeE_mk_eq M hJ (locConeE_mk M I _ m s)

theorem locModE_subsingleton {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod S N M.coneSubE I) := by
  have hX : ∀ m : M.coneSubE, (X i : Poly S N) • m = 0 := fun m => by
    apply Subtype.ext
    refine coneE_ext fun d => ?_
    change coeffE S x E d ((X i : Poly S N) • (m : ConeE S x E)) = coeffE S x E d 0
    rw [coeffE_smul_of_isHomogeneous (isHomogeneous_X S i), aeval_X, hx, zero_smul, map_zero]
  refine subsingleton_of_forall_eq 0 fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSubE => z = 0) (fun m s => ?_) z
  rw [← LocalizedModule.mk_cancel_common_left ⟨X i, X_mem_monos hi⟩ s m]
  have h0 : (⟨X i, X_mem_monos hi⟩ : monos (S := S) I) • m = 0 := hX m
  rw [h0, LocalizedModule.zero_mk]

theorem locConeE_degLoc (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSubE I.1}
    (hz : z ∈ degLoc M.coneGradedE c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locConeE M I.1 hI z = singleE S x E c v := by
  refine Submodule.span_induction (p := fun z _ => ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩,
    locConeE M I.1 hI z = singleE S x E c v) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, s, a, e, hm, hse, hae, rfl⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI s.2
    refine ⟨(aeval x (s : Poly S N))⁻¹ • coeffE S x E a (m : ConeE S x E),
      Submodule.subset_span ⟨coeffE S x E a m, s, a, e, s.2, hse, m.2 a, hae, rfl⟩, locConeE_mk_eq M hI ?_⟩
    rw [smul_singleE hse, smul_smul, mul_inv_cancel₀ hs0, one_smul, show c + (e : ℤ) = a by omega]
    exact (M.eq_singleE_of_mem_conePieceE hm).symm
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨v, hv, hzv⟩ ⟨v', hv', hzv'⟩
    exact ⟨v + v', add_mem hv hv', by rw [map_add, map_add, hzv, hzv']⟩
  · rintro s _ _ ⟨v, hv, hzv⟩
    refine ⟨s • v, ?_, by rw [LinearMap.map_smul_of_tower, hzv, map_smul]⟩
    rw [← algebraMap_smul Ω s v]
    exact (M.tilde c _).smul_mem (algebraMap S (chartRing S x ⟨I.1, I.2.1, hI⟩) s) hv

def tildeGensE (c : ℤ) (I : Chart x) : Set E :=
  {y | ∃ (m : E) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧
    a - e = c ∧ y = (aeval x s)⁻¹ • m}

theorem tildeE_le_span (c : ℤ) (I : Chart x) :
    (M.tilde c I : Set E) ⊆ Submodule.span S (tildeGensE M c I) := by
  have hclosed : ∀ a : chartRing S x I, ∀ y ∈ Submodule.span S (tildeGensE M c I),
      a • y ∈ Submodule.span S (tildeGensE M c I) := by
    intro a y hy
    refine Submodule.span_induction (p := fun y _ => a • y ∈ Submodule.span S (tildeGensE M c I))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
      obtain ⟨f, s', e', hs', hf, hse', ha⟩ := a.2
      refine Submodule.subset_span ⟨aeval x f • m, s' * s, b + e', e' + e, mul_mem hs' hs, hse'.mul hse,
        M.smul_mem e' b f m hf hm, by push_cast; omega, ?_⟩
      change (a : Ω) • ((aeval x s)⁻¹ • m) = _
      rw [smul_smul, smul_smul, ha, map_mul, mul_inv, div_eq_mul_inv]
      congr 1
      ring
    · rw [smul_zero]; exact zero_mem _
    · intro y y' _ _ hy hy'; rw [smul_add]; exact add_mem hy hy'
    · intro t y _ hy
      have : a • (t • y) = t • (a • y) := by
        rw [← algebraMap_smul Ω t y, ← algebraMap_smul Ω t (a • y)]
        change (a : Ω) • (algebraMap S Ω t • y) = algebraMap S Ω t • ((a : Ω) • y)
        rw [smul_smul, smul_smul, mul_comm]
      rw [this]; exact Submodule.smul_mem _ t hy
  intro y hy
  exact Submodule.span_induction (p := fun y _ => y ∈ Submodule.span S (tildeGensE M c I))
    (fun y hy => Submodule.subset_span hy) (zero_mem _) (fun _ _ _ _ => add_mem)
    (fun a y _ hy => hclosed a y hy) hy

theorem exists_locConeE_eq (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : E}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGradedE c I, locConeE M I.1 hI z = singleE S x E c y := by
  refine Submodule.span_induction (p := fun y _ => ∃ z ∈ degLoc M.coneGradedE c I,
    locConeE M I.1 hI z = singleE S x E c y) ?_ ?_ ?_ ?_ (tildeE_le_span M c _ hy)
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine ⟨LocalizedModule.mk ⟨singleE S x E a m, M.singleE_mem_coneSubE hm⟩ ⟨s, hs⟩,
      Submodule.subset_span ⟨_, ⟨s, hs⟩, a, e, M.singleE_mem_conePieceE hm, hse, hae, rfl⟩,
      locConeE_mk_eq M hI ?_⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI hs
    change s • singleE S x E c ((aeval x s)⁻¹ • m) = singleE S x E a m
    rw [smul_singleE hse, smul_smul, mul_inv_cancel₀ hs0, one_smul, show c + (e : ℤ) = a by omega]
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨z, hz, hzy⟩ ⟨z', hz', hzy'⟩
    exact ⟨z + z', add_mem hz hz', by rw [map_add, map_add, hzy, hzy']⟩
  · rintro t _ _ ⟨z, hz, hzy⟩
    exact ⟨t • z, Submodule.smul_mem _ t hz, by rw [LinearMap.map_smul_of_tower, hzy, map_smul]⟩

end LocE

end

end GroundTheory.Heights₂.Heights.Kleiman
