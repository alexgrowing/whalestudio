import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi.ACA

section
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y]

private lemma lift_commute_of {X : Type} (u : X → Module.End ℂ Y) (z : Module.End ℂ Y)
    (h : ∀ x, Commute (u x) z) (p : FreeAlgebra ℂ X) : Commute (FreeAlgebra.lift ℂ u p) z := by
  induction p using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact Algebra.commutes r z
  | grade1 x => simpa using h x
  | mul p q hp hq => rw [map_mul]; exact hp.mul_left hq
  | add p q hp hq => rw [map_add]; exact hp.add_left hq

private lemma lift_commute {X X' : Type} (u : X → Module.End ℂ Y) (v : X' → Module.End ℂ Y)
    (h : ∀ x y, Commute (u x) (v y)) (p : FreeAlgebra ℂ X) (q : FreeAlgebra ℂ X') :
    Commute (FreeAlgebra.lift ℂ u p) (FreeAlgebra.lift ℂ v q) :=
  lift_commute_of u _ (fun x => (lift_commute_of v (u x) (fun y => (h x y).symm) q).symm) p

private lemma lift_intertwine {X : Type} (u v : X → Module.End ℂ Y) (A : Module.End ℂ Y)
    (h : ∀ x, A * u x = v x * A) (p : FreeAlgebra ℂ X) :
    A * FreeAlgebra.lift ℂ u p = FreeAlgebra.lift ℂ v p * A := by
  induction p using FreeAlgebra.induction with
  | grade0 r => simpa using (Algebra.commutes r A).symm
  | grade1 x => simpa using h x
  | mul p q hp hq => rw [map_mul, map_mul, ← mul_assoc, hp, mul_assoc, hq, mul_assoc]
  | add p q hp hq => rw [map_add, map_add, mul_add, add_mul, hp, hq]

private lemma lift_lift {X : Type} (u : X → Module.End ℂ Y) (p : FreeAlgebra ℂ (FreeAlgebra ℂ X)) :
    FreeAlgebra.lift ℂ (fun q => FreeAlgebra.lift ℂ u q) p =
      FreeAlgebra.lift ℂ u (FreeAlgebra.lift ℂ (fun q : FreeAlgebra ℂ X => q) p) := by
  have h : FreeAlgebra.lift ℂ (fun q => FreeAlgebra.lift ℂ u q) =
      (FreeAlgebra.lift ℂ u).comp (FreeAlgebra.lift ℂ (fun q : FreeAlgebra ℂ X => q)) :=
    FreeAlgebra.hom_ext (by funext q; simp)
  exact DFunLike.congr_fun h p

private lemma mem_adjoin_iff {X : Type} (u : X → Module.End ℂ Y) (x : Module.End ℂ Y) :
    x ∈ Algebra.adjoin ℂ (Set.range u) ↔ ∃ q, FreeAlgebra.lift ℂ u q = x := by
  constructor
  · intro hx
    have hle : Algebra.adjoin ℂ (Set.range u) ≤ (FreeAlgebra.lift ℂ u).range :=
      Algebra.adjoin_le (by
        rintro _ ⟨t, rfl⟩
        exact ⟨FreeAlgebra.ι ℂ t, by simp⟩)
    obtain ⟨q, hq⟩ := hle hx
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩
    induction q using FreeAlgebra.induction with
    | grade0 r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
    | grade1 t =>
      simpa using (Algebra.subset_adjoin (Set.mem_range_self t) : u t ∈ Algebra.adjoin ℂ (Set.range u))
    | mul p q hp hq => rw [map_mul]; exact Subalgebra.mul_mem _ hp hq
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq

private lemma conj_mul (A x y : Module.End ℂ Y) (hAA : A * A = 1) :
    A * x * A * (A * y * A) = A * (x * y) * A := by
  calc A * x * A * (A * y * A) = A * x * (A * A) * y * A := by simp only [mul_assoc]
    _ = A * (x * y) * A := by rw [hAA, mul_one]; simp only [mul_assoc]

end

end UpperTheory.V.Z.Mult.Pi.ACA

open UpperTheory.V.Z.Mult.Pi.ACA in
theorem UpperTheory.V.Z.Mult.Pi.absCoreA_pf :
    AbsCore → RankOne → Corner → MinIdem → AbsCoreA := by
  intro hC hR hK hI I _ J M _ _ _ Y _ _ _ _ α a b A hM hrel haa hab hAA hAb hY
  classical
  obtain ⟨d, hd0, hd⟩ := hC I (fun i => FreeAlgebra ℂ (J i)) M Y
    (fun i q => FreeAlgebra.lift ℂ (α i) q) (fun i q => FreeAlgebra.lift ℂ (a i) q)
    (fun i q => FreeAlgebra.lift ℂ (b i) q) A
    (fun i W hW => hM i W fun f x hx => by simpa using hW (FreeAlgebra.ι ℂ f) x hx)
    (fun i p h => by
      rw [lift_lift] at h ⊢
      exact hrel i _ h)
    (fun i k h f g => lift_commute _ _ (haa i k h) f g)
    (fun i k f g => lift_commute _ _ (hab i k) f g)
    hAA
    (fun i q => lift_intertwine _ _ A (hAb i) q)
    (fun W hW => hY W fun i f x hx => by simpa using hW i (FreeAlgebra.ι ℂ f) x hx)
  have hd' : ∀ x y : ∀ i, FreeAlgebra ℂ (J i),
      LinearMap.trace ℂ Y (((Finset.univ : Finset I).toList.map fun i =>
        FreeAlgebra.lift ℂ (a i) (x i) * FreeAlgebra.lift ℂ (b i) (y i)).prod * A) =
      d * ∏ i, LinearMap.trace ℂ (M i)
        (FreeAlgebra.lift ℂ (α i) (x i) * FreeAlgebra.lift ℂ (α i) (y i)) := hd
  have hnt : ∀ i, Nontrivial (M i) := by
    intro i
    by_contra hn
    have hs : Subsingleton (M i) := not_nontrivial_iff_subsingleton.1 hn
    have h0 : FreeAlgebra.lift ℂ (α i) (1 : FreeAlgebra ℂ (J i)) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have h1 := hrel i 1 h0
    rw [map_one] at h1
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    exact hy (by simpa using LinearMap.congr_fun h1 y)
  have hex : ∀ i, ∃ p : FreeAlgebra ℂ (J i),
      LinearMap.trace ℂ (M i) (FreeAlgebra.lift ℂ (α i) p * FreeAlgebra.lift ℂ (α i) p) = 1 ∧
      FreeAlgebra.lift ℂ (a i) p * FreeAlgebra.lift ℂ (a i) p = FreeAlgebra.lift ℂ (a i) p ∧
      ∀ q, ∃ c : ℂ, FreeAlgebra.lift ℂ (a i) p * FreeAlgebra.lift ℂ (a i) q *
        FreeAlgebra.lift ℂ (a i) p = c • FreeAlgebra.lift ℂ (a i) p := fun i => by
    haveI := hnt i
    exact hI (J i) (M i) Y (α i) (a i) (hM i) (hrel i)
  choose p hp1 hp2 hp3 using hex
  have hAq : ∀ i q, A * FreeAlgebra.lift ℂ (a i) q = FreeAlgebra.lift ℂ (b i) q * A :=
    fun i q => lift_intertwine _ _ A (hAb i) q
  have hbq : ∀ i q, FreeAlgebra.lift ℂ (b i) q = A * FreeAlgebra.lift ℂ (a i) q * A :=
    fun i q => by rw [hAq, mul_assoc, hAA, mul_one]
  have hbf : ∀ i f, b i f = A * a i f * A := fun i f => by rw [hAb, mul_assoc, hAA, mul_one]
  have hbb : ∀ i k, i ≠ k → ∀ f g, Commute (b i f) (b k g) := by
    intro i k h f g
    show b i f * b k g = b k g * b i f
    rw [hbf i f, hbf k g, conj_mul A _ _ hAA, conj_mul A _ _ hAA, (haa i k h f g).eq]
  obtain ⟨e, he⟩ : ∃ e : I → Module.End ℂ Y, ∀ i, e i = FreeAlgebra.lift ℂ (a i) (p i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : I → Module.End ℂ Y, ∀ i, e' i = FreeAlgebra.lift ℂ (b i) (p i) :=
    ⟨_, fun _ => rfl⟩
  have hee' : ∀ i, e' i = A * e i * A := fun i => by rw [he, he', hbq]
  have hidem : ∀ i, e i * e i = e i := fun i => by rw [he]; exact hp2 i
  have hcorner := hK I J Y a b e e' haa hab hbb hY
    (fun i => ⟨(mem_adjoin_iff _ _).2 ⟨p i, (he i).symm⟩, hidem i, fun x hx => by
      obtain ⟨q, rfl⟩ := (mem_adjoin_iff _ _).1 hx
      rw [he]
      exact hp3 i q⟩)
    (fun i => ⟨(mem_adjoin_iff _ _).2 ⟨p i, (he' i).symm⟩, by
        rw [hee', conj_mul A _ _ hAA, hidem], fun x hx => by
      obtain ⟨q, rfl⟩ := (mem_adjoin_iff _ _).1 hx
      obtain ⟨c, hc⟩ := hp3 i q
      refine ⟨c, ?_⟩
      rw [hee', hbq, conj_mul A _ _ hAA, conj_mul A _ _ hAA, he, hc, mul_smul_comm, smul_mul_assoc]⟩)
    _ rfl
  obtain ⟨hff, hsc⟩ := hcorner
  have hfac : ∀ i, Commute A (e i * e' i) := by
    intro i
    have hce : Commute (e i) (e' i) := by
      rw [he, he']
      exact lift_commute _ _ (hab i i) _ _
    have h1 : A * e i = e' i * A := by rw [he, he']; exact hAq i (p i)
    have h2 : A * e' i = e i * A := by
      rw [hee', ← mul_assoc, ← mul_assoc, hAA, one_mul]
    show A * (e i * e' i) = e i * e' i * A
    calc A * (e i * e' i) = A * e i * e' i := by rw [mul_assoc]
      _ = e' i * (A * e' i) := by rw [h1, mul_assoc]
      _ = e' i * e i * A := by rw [h2, mul_assoc]
      _ = e i * e' i * A := by rw [hce.eq]
  have hAF : Commute A ((Finset.univ : Finset I).toList.map fun i => e i * e' i).prod :=
    Commute.list_prod_right _ _ (by
      intro z hz
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hz
      exact hfac k)
  have htr : LinearMap.trace ℂ Y
      (((Finset.univ : Finset I).toList.map fun i => e i * e' i).prod * A) = d := by
    have h := hd' p p
    simp only [hp1, Finset.prod_const_one, mul_one] at h
    simpa only [he, he'] using h
  have hn : ‖d‖ = 1 := by
    rcases hR Y _ A hff hAA hAF.eq hsc with h | h
    · rw [htr] at h
      exact absurd h hd0
    · rwa [htr] at h
  refine ⟨d, hn, fun f g => ?_⟩
  simpa using hd' (fun i => FreeAlgebra.ι ℂ (f i)) (fun i => FreeAlgebra.ι ℂ (g i))
