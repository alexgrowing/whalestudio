import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.Induced

theorem isHopfOrder_indOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  classical
  intro R _ _ T _ _ H _ ι hι A hA
  obtain ⟨hfin, hproj, hfull, hcomul, hinv⟩ := hA
  unfold prodSpan at hcomul
  have hmemInd : ∀ f : T → R, f ∈ indOrder ι A ↔ ∀ t : T, (fun h => f (t * ι h)) ∈ A := by
    intro f
    unfold indOrder
    exact Iff.rfl
  have hTr : ∀ g ∈ A, ∀ h0 : H, (fun h => g (h * h0)) ∈ A := by
    intro g hg h0
    obtain ⟨E, hE⟩ : ∃ E : (H × H → R) →ₗ[R] (H → R), ∀ φ h, E φ h = φ (h, h0) :=
      ⟨{ toFun := fun φ h => φ (h, h0)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }, fun _ _ => rfl⟩
    have hle : Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z : H × H => a z.1 * b z.2} ≤
        (Subalgebra.toSubmodule A).comap E := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have hEab : E (fun z : H × H => a z.1 * b z.2) = b h0 • a := by
        funext h
        rw [hE]
        simp [mul_comm]
      show E _ ∈ Subalgebra.toSubmodule A
      rw [hEab]
      exact A.smul_mem ha _
    have h1 := hle (hcomul g hg)
    have h2 : E (fun z : H × H => g (z.1 * z.2)) = fun h => g (h * h0) := funext fun h => hE _ h
    rw [Submodule.mem_comap, h2] at h1
    simpa using h1
  have hs : Function.Surjective (QuotientGroup.mk : T → T ⧸ ι.range) := QuotientGroup.mk_surjective
  have hQfin : Finite (T ⧸ ι.range) := Finite.of_surjective _ hs
  let _ : Fintype (T ⧸ ι.range) := Fintype.ofFinite _
  obtain ⟨σ, hσ⟩ : ∃ σ : T ⧸ ι.range → T, ∀ c, (σ c : T ⧸ ι.range) = c :=
    ⟨Function.surjInv hs, Function.surjInv_eq hs⟩
  have hmem : ∀ t : T, (σ (t : T ⧸ ι.range))⁻¹ * t ∈ ι.range := fun t => QuotientGroup.eq.mp (hσ _)
  choose δ hδ using fun t : T => MonoidHom.mem_range.mp (hmem t)
  have hdec : ∀ t : T, σ (t : T ⧸ ι.range) * ι (δ t) = t := fun t => by
    rw [hδ, mul_inv_cancel_left]
  have hmk : ∀ (t : T) (h : H), ((t * ι h : T) : T ⧸ ι.range) = (t : T ⧸ ι.range) := by
    intro t h
    apply QuotientGroup.eq.mpr
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem (MonoidHom.mem_range.mpr ⟨h, rfl⟩)
  have hδmul : ∀ (t : T) (h : H), δ (t * ι h) = δ t * h := by
    intro t h
    apply hι
    rw [hδ, map_mul, hδ, hmk, mul_assoc]
  obtain ⟨e, he⟩ : ∃ e : T ⧸ ι.range → T → R,
      ∀ c t, e c t = if (t : T ⧸ ι.range) = c then 1 else 0 :=
    ⟨fun c t => if (t : T ⧸ ι.range) = c then 1 else 0, fun _ _ => rfl⟩
  have he_self : ∀ t : T, e (t : T ⧸ ι.range) t = 1 := fun t => by rw [he, if_pos rfl]
  have he_ne : ∀ (c : T ⧸ ι.range) (t : T), c ≠ (t : T ⧸ ι.range) → e c t = 0 :=
    fun c t hc => by rw [he, if_neg (fun h => hc h.symm)]
  have he_mk : ∀ (c : T ⧸ ι.range) (t : T) (h : H), e c (t * ι h) = e c t :=
    fun c t h => by rw [he, he, hmk]
  let i : (indOrder ι A) →ₗ[R] (T ⧸ ι.range → A) :=
    { toFun := fun f c => ⟨fun h => (f : T → R) (σ c * ι h), (hmemInd _).mp f.2 (σ c)⟩
      map_add' := fun f g => by
        funext c
        apply Subtype.ext
        rfl
      map_smul' := fun r f => by
        funext c
        apply Subtype.ext
        rfl }
  have hp : ∀ a : T ⧸ ι.range → A,
      (fun t : T => ((a (t : T ⧸ ι.range) : A) : H → R) (δ t)) ∈ indOrder ι A := by
    intro a
    rw [hmemInd]
    intro t
    have heq : (fun h => ((a ((t * ι h : T) : T ⧸ ι.range) : A) : H → R) (δ (t * ι h))) =
        fun h => ((a (t : T ⧸ ι.range) : A) : H → R) (h * δ t) := by
      funext h
      rw [hmk, hδmul, mul_comm (δ t) h]
    show (fun h => ((a ((t * ι h : T) : T ⧸ ι.range) : A) : H → R) (δ (t * ι h))) ∈ A
    rw [heq]
    exact hTr _ (a _).2 _
  let p : (T ⧸ ι.range → A) →ₗ[R] (indOrder ι A) :=
    { toFun := fun a => ⟨fun t : T => ((a (t : T ⧸ ι.range) : A) : H → R) (δ t), hp a⟩
      map_add' := fun a b => by
        apply Subtype.ext
        rfl
      map_smul' := fun r a => by
        apply Subtype.ext
        rfl }
  have hpi' : ∀ f, p (i f) = f := by
    intro f
    apply Subtype.ext
    funext t
    show (f : T → R) (σ (t : T ⧸ ι.range) * ι (δ t)) = (f : T → R) t
    rw [hdec]
  have hpi : p.comp i = LinearMap.id := LinearMap.ext hpi'
  have := hfin
  have := hproj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_surjective p (fun f => ⟨i f, hpi' f⟩)
  · have hQM : Module.Projective R (T ⧸ ι.range → A) := by
      obtain ⟨M, _, _, _, i0, s0, hs0⟩ := Module.Projective.iff_split.mp hproj
      refine Module.Projective.of_split
        ({ toFun := fun g c => i0 (g c)
           map_add' := fun g g' => by
             funext c
             simp
           map_smul' := fun r g => by
             funext c
             simp } : (T ⧸ ι.range → A) →ₗ[R] (T ⧸ ι.range → M))
        ({ toFun := fun g c => s0 (g c)
           map_add' := fun g g' => by
             funext c
             simp
           map_smul' := fun r g => by
             funext c
             simp } : (T ⧸ ι.range → M) →ₗ[R] (T ⧸ ι.range → A)) ?_
      apply LinearMap.ext
      intro g
      funext c
      show s0 (i0 (g c)) = g c
      exact LinearMap.congr_fun hs0 (g c)
    exact Module.Projective.of_split i p hpi
  · obtain ⟨d, hd0, hd⟩ := hfull
    exact ⟨d, hd0, fun f => (hmemInd _).mpr fun t => hd (fun h => f (t * ι h))⟩
  · intro f hf
    unfold prodSpan
    have hind : ∀ (c : T ⧸ ι.range), ∀ a ∈ A, (fun t => e c t * a (δ t)) ∈ indOrder ι A := by
      intro c a ha
      rw [hmemInd]
      intro t
      have heq : (fun h => e c (t * ι h) * a (δ (t * ι h))) = fun h => e c t * a (h * δ t) := by
        funext h
        rw [he_mk, hδmul, mul_comm (δ t) h]
      show (fun h => e c (t * ι h) * a (δ (t * ι h))) ∈ A
      rw [heq]
      exact A.smul_mem (hTr a ha (δ t)) (e c t)
    obtain ⟨L, hL⟩ : ∃ L : T ⧸ ι.range → T ⧸ ι.range → (H × H → R) →ₗ[R] (T × T → R),
        ∀ c1 c2 φ z, L c1 c2 φ z = e c1 z.1 * e c2 z.2 * φ (δ z.1, δ z.2) :=
      ⟨fun c1 c2 =>
        { toFun := fun φ z => e c1 z.1 * e c2 z.2 * φ (δ z.1, δ z.2)
          map_add' := fun φ ψ => by
            funext z
            simp only [Pi.add_apply]
            ring
          map_smul' := fun r φ => by
            funext z
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            ring },
        fun _ _ _ _ => rfl⟩
    have hsum : (fun z : T × T => f (z.1 * z.2)) =
        ∑ c1 : T ⧸ ι.range, ∑ c2 : T ⧸ ι.range,
          L c1 c2 (fun z : H × H => f (σ c1 * σ c2 * ι (z.1 * z.2))) := by
      funext z
      rw [Finset.sum_apply, Fintype.sum_eq_single (z.1 : T ⧸ ι.range)]
      · rw [Finset.sum_apply, Fintype.sum_eq_single (z.2 : T ⧸ ι.range)]
        · rw [hL]
          try dsimp only
          rw [he_self, he_self, one_mul, one_mul, map_mul, mul_mul_mul_comm, hdec, hdec]
        · intro c2 hc2
          rw [hL, he_ne _ _ hc2, mul_zero, zero_mul]
      · intro c1 hc1
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro c2 _
        rw [hL, he_ne _ _ hc1, zero_mul, zero_mul]
    rw [hsum]
    refine sum_mem fun c1 _ => sum_mem fun c2 _ => ?_
    have hle : Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z : H × H => a z.1 * b z.2} ≤
        (Submodule.span R {g | ∃ a ∈ indOrder ι A, ∃ b ∈ indOrder ι A,
          g = fun z : T × T => a z.1 * b z.2}).comap (L c1 c2) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      show L c1 c2 _ ∈ Submodule.span R _
      apply Submodule.subset_span
      refine ⟨_, hind c1 a ha, _, hind c2 b hb, ?_⟩
      funext z
      rw [hL]
      dsimp only
      ring
    exact hle (hcomul _ ((hmemInd f).mp hf (σ c1 * σ c2)))
  · intro f hf
    rw [hmemInd] at hf ⊢
    intro t
    have heq : (fun h => f ((t * ι h)⁻¹)) = fun h => f (t⁻¹ * ι h⁻¹) := by
      funext h
      rw [map_inv, mul_inv]
    show (fun h => f ((t * ι h)⁻¹)) ∈ A
    rw [heq]
    exact hinv _ (hf t⁻¹)

end GlobalTheory.CompanionTheory.Ar.BT.Induced
