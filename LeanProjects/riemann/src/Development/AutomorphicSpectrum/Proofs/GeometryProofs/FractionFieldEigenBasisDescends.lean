import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig

theorem exists_retraction {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {M : Type}
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (hN : ∀ (c : O) (x : M), c ≠ 0 → c • x ∈ N → x ∈ N) :
    ∃ r : M →ₗ[O] N, r ∘ₗ N.subtype = LinearMap.id := by
  haveI : NoZeroSMulDivisors O (M ⧸ N) := by
    refine ⟨fun {c y} h => ?_⟩
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      exact (Submodule.Quotient.mk_eq_zero N).2 (hN c x hc h)
  haveI : Module.Free O (M ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  refine ⟨LinearMap.codRestrict N (LinearMap.id - s ∘ₗ N.mkQ) ?_, ?_⟩
  · intro x
    have h1 : N.mkQ (s (N.mkQ x)) = N.mkQ x := LinearMap.congr_fun hs _
    refine (Submodule.Quotient.mk_eq_zero N).1 ?_
    change N.mkQ (x - s (N.mkQ x)) = 0
    rw [map_sub, h1, sub_self]
  · refine LinearMap.ext fun y => Subtype.ext ?_
    have h0 : N.mkQ (y : M) = 0 := (Submodule.Quotient.mk_eq_zero N).2 y.2
    change (y : M) - s (N.mkQ y) = y
    rw [h0, map_zero, sub_zero]

theorem exists_integral_leftInverse {V K : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] {g n : ℕ}
    (W : Submodule K (Fin g → K)) (b : Fin n → Fin g → K) (hb : LinearIndependent K b)
    (hsp : Submodule.span V (Set.range b) = stdLat V K g ⊓ W.restrictScalars V) :
    ∃ m : Fin n → Fin g → V, ∀ i i', ∑ k, algebraMap V K (m i k) * b i' k =
      if i = i' then 1 else 0 := by
  let φ : (Fin g → V) →ₗ[V] (Fin g → K) :=
    LinearMap.pi fun k => (Algebra.linearMap V K).comp (LinearMap.proj k)
  let N : Submodule V (Fin g → V) := (W.restrictScalars V).comap φ
  have hNsat : ∀ (c : V) (x : Fin g → V), c ≠ 0 → c • x ∈ N → x ∈ N := by
    intro c x hc hx
    have hc' : algebraMap V K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hc
    have h1 : φ (c • x) ∈ W := hx
    rw [map_smul, ← algebraMap_smul K c (φ x)] at h1
    have h2 := W.smul_mem (algebraMap V K c)⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ hc', one_smul] at h2
    exact h2
  obtain ⟨r, hr⟩ := exists_retraction N hNsat
  have hbmem : ∀ i', b i' ∈ stdLat V K g ⊓ W.restrictScalars V := by
    intro i'
    rw [← hsp]
    exact Submodule.subset_span ⟨i', rfl⟩
  have hβ : ∀ i' k, ∃ v : V, algebraMap V K v = b i' k := by
    intro i' k
    have h : ∀ k, b i' k ∈ (algebraMap V K).range := (Submodule.mem_inf.1 (hbmem i')).1
    exact RingHom.mem_range.1 (h k)
  choose β hβ using hβ
  have hφβ : ∀ i', φ (β i') = b i' := fun i' => funext fun k => hβ i' k
  have hβN : ∀ i', β i' ∈ N := by
    intro i'
    show φ (β i') ∈ W
    rw [hφβ]
    exact (Submodule.mem_inf.1 (hbmem i')).2
  have hinj : Function.Injective fun r : V => r • (1 : K) := by
    intro x y hxy
    exact IsFractionRing.injective V K (by simpa [Algebra.smul_def] using hxy)
  have hbV : LinearIndependent V b := hb.restrict_scalars hinj
  have hψ : ∀ y : N, (φ ∘ₗ N.subtype) y ∈ Submodule.span V (Set.range b) := by
    intro y
    rw [hsp]
    refine Submodule.mem_inf.2 ⟨?_, y.2⟩
    show ∀ k, φ y k ∈ (algebraMap V K).range
    intro k
    exact RingHom.mem_range.2 ⟨(y : Fin g → V) k, rfl⟩
  let ψ : N →ₗ[V] Submodule.span V (Set.range b) :=
    LinearMap.codRestrict _ (φ ∘ₗ N.subtype) hψ
  let F : Fin n → (Fin g → V) →ₗ[V] V := fun i =>
    Finsupp.lapply i ∘ₗ hbV.repr ∘ₗ ψ ∘ₗ r
  refine ⟨fun i k => F i (fun j => if k = j then 1 else 0), fun i i' => ?_⟩
  have hF : F i (β i') = if i = i' then 1 else 0 := by
    have hr' : r (β i') = ⟨β i', hβN i'⟩ := LinearMap.congr_fun hr ⟨β i', hβN i'⟩
    have hrep : hbV.repr (ψ ⟨β i', hβN i'⟩) = Finsupp.single i' 1 :=
      hbV.repr_eq_single i' _ (hφβ i')
    change hbV.repr (ψ (r (β i'))) i = _
    rw [hr', hrep, Finsupp.single_apply]
    by_cases h : i = i'
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hsum : F i (β i') = ∑ k, β i' k * F i (fun j => if k = j then 1 else 0) := by
    rw [LinearMap.pi_apply_eq_sum_univ (F i) (β i')]
    simp only [smul_eq_mul]
  calc ∑ k, algebraMap V K (F i (fun j => if k = j then 1 else 0)) * b i' k
      = algebraMap V K (∑ k, β i' k * F i (fun j => if k = j then 1 else 0)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul, hβ, mul_comm]
    _ = if i = i' then 1 else 0 := by
        rw [← hsum, hF]
        split_ifs <;> simp

theorem mem_span_of_mem {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] {g n : ℕ} (W : Submodule K (Fin g → K)) (b : Fin n → Fin g → K)
    (hsp : Submodule.span V (Set.range b) = stdLat V K g ⊓ W.restrictScalars V) {u : Fin g → K}
    (hu : u ∈ W) : u ∈ Submodule.span K (Set.range b) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors V)
    (Finset.univ : Finset (Fin g)) u
  have hd0 : algebraMap V K (d : V) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have hdu : algebraMap V K (d : V) • u ∈ Submodule.span V (Set.range b) := by
    rw [hsp]
    refine Submodule.mem_inf.2 ⟨?_, W.smul_mem _ hu⟩
    show ∀ k, (algebraMap V K (d : V) • u) k ∈ (algebraMap V K).range
    intro k
    obtain ⟨y, hy⟩ := hd k (Finset.mem_univ k)
    refine RingHom.mem_range.2 ⟨y, ?_⟩
    rw [hy, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
  have hK : algebraMap V K (d : V) • u ∈ Submodule.span K (Set.range b) :=
    Submodule.span_le_restrictScalars V K _ hdu
  have h2 := Submodule.smul_mem _ (algebraMap V K (d : V))⁻¹ hK
  rwa [smul_smul, inv_mul_cancel₀ hd0, one_smul] at h2

theorem eigSub_baseChange : ∀ (E : Type) [Field E] [NumberField E] (K C V A : Type) [Field K] [CharZero K] [Field C] [CharZero C] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra V K] [IsFractionRing V K] [CommRing A] [IsDomain A] [Algebra A C]
    (j : K →+* C) (g n : ℕ) (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (σ : E →+* K) (b : Fin n → Fin g → K),
    (∀ a : K, a ∈ (algebraMap V K).range → j a ∈ (algebraMap A C).range) →
    (∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i)) →
    LinearIndependent K b → Submodule.span V (Set.range b) = HT.eigSub ρK σ (stdLat V K g) →
    LinearIndependent C (fun i k => j (b i k)) ∧
      Submodule.span C (Set.range fun i k => j (b i k)) = HT.eigSp ρC (j.comp σ) ∧
      Submodule.span A (Set.range fun i k => j (b i k)) = HT.eigSub ρC (j.comp σ) (stdLat A C g) := by
  intro E _ _ K C V A _ _ _ _ _ _ _ _ _ _ _ _ j g n ρK ρC σ b hA hρ hb hsp
  have hsp' : Submodule.span V (Set.range b) =
      stdLat V K g ⊓ (HT.eigSp ρK σ).restrictScalars V := hsp
  obtain ⟨m, hm⟩ := exists_integral_leftInverse (HT.eigSp ρK σ) b hb hsp'
  have hbmem : ∀ i', b i' ∈ stdLat V K g ⊓ (HT.eigSp ρK σ).restrictScalars V := by
    intro i'
    rw [← hsp']
    exact Submodule.subset_span ⟨i', rfl⟩
  have hbE : ∀ (a : 𝓞 E) i', ρK a (b i') = σ (a : E) • b i' := by
    intro a i'
    have h : b i' ∈ ⨅ a : 𝓞 E, LinearMap.ker (ρK a - σ (a : E) • 1) :=
      (Submodule.mem_inf.1 (hbmem i')).2
    have h2 := (Submodule.mem_iInf _).1 h a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h2
    exact h2
  have hcoef : ∀ (c : Fin n → C) i,
      ∑ k, j (algebraMap V K (m i k)) * (∑ i', c i' • fun k => j (b i' k)) k = c i := by
    intro c i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∀ i', ∑ k, j (algebraMap V K (m i k)) * (c i' * j (b i' k)) =
        if i = i' then c i' else 0 := by
      intro i'
      have e3 : ∑ k, j (algebraMap V K (m i k)) * (c i' * j (b i' k)) =
          c i' * j (∑ k, algebraMap V K (m i k) * b i' k) := by
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul]
        ring
      rw [e3, hm i i']
      split_ifs <;> simp
    simp only [e2]
    simp
  have hli : LinearIndependent C (fun i k => j (b i k)) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have hc' : ∑ i, c i • (fun k => j (b i k)) = 0 := hc
    rw [← hcoef c i, hc']
    simp
  have hspanC : Submodule.span C (Set.range fun i k => j (b i k)) = HT.eigSp ρC (j.comp σ) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i', rfl⟩
      show (fun k => j (b i' k)) ∈ ⨅ a : 𝓞 E, LinearMap.ker (ρC a - (j.comp σ) (a : E) • 1)
      refine (Submodule.mem_iInf _).2 fun a => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hρ,
        hbE, sub_eq_zero]
      funext k
      simp [RingHom.comp_apply]
    · intro x hx
      have hxE : ∀ a : 𝓞 E, ρC a x = j (σ (a : E)) • x := by
        intro a
        have h : x ∈ ⨅ a : 𝓞 E, LinearMap.ker (ρC a - (j.comp σ) (a : E) • 1) := hx
        have h2 := (Submodule.mem_iInf _).1 h a
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          sub_eq_zero, RingHom.comp_apply] at h2
        exact h2
      letI : Algebra K C := j.toAlgebra
      let S : Submodule K C := Submodule.span K (Set.range x)
      haveI : Module.Finite K S := Module.Finite.span_of_finite K (Set.finite_range x)
      let bS := Module.finBasis K S
      let c : Fin (Module.finrank K S) → C := fun t => (bS t : C)
      have hc : LinearIndependent K c := bS.linearIndependent.map' S.subtype S.ker_subtype
      let y : Fin (Module.finrank K S) → Fin g → K := fun t k =>
        bS.repr ⟨x k, Submodule.subset_span ⟨k, rfl⟩⟩ t
      have hxk : ∀ k, x k = ∑ t, j (y t k) * c t := by
        intro k
        have h := congrArg (fun s : S => (s : C)) (bS.sum_repr ⟨x k, Submodule.subset_span ⟨k, rfl⟩⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_smul_of_tower,
          Algebra.smul_def] at h
        exact h.symm
      have hxsum : x = ∑ t, c t • (fun k => j (y t k)) := by
        funext k
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hxk k]
        exact Finset.sum_congr rfl fun t _ => mul_comm _ _
      have key : ∀ (a : 𝓞 E) k t, ρK a (y t) k - σ (a : E) * y t k = 0 := by
        intro a k
        refine Fintype.linearIndependent_iff.1 hc (fun t => ρK a (y t) k - σ (a : E) * y t k) ?_
        have h := congrFun (hxE a) k
        rw [hxsum, map_sum] at h
        simp only [map_smul, hρ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum] at h
        calc ∑ t, (ρK a (y t) k - σ (a : E) * y t k) • c t
            = ∑ t, c t * j (ρK a (y t) k) - ∑ t, j (σ (a : E)) * (c t * j (y t k)) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sub, map_mul]
              ring
          _ = 0 := by rw [h, sub_self]
      have hyE : ∀ t, y t ∈ HT.eigSp ρK σ := by
        intro t
        show y t ∈ ⨅ a : 𝓞 E, LinearMap.ker (ρK a - σ (a : E) • 1)
        refine (Submodule.mem_iInf _).2 fun a => ?_
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          sub_eq_zero]
        funext k
        rw [Pi.smul_apply, smul_eq_mul]
        exact sub_eq_zero.1 (key a k t)
      have hyC : ∀ t, (fun k => j (y t k)) ∈ Submodule.span C (Set.range fun i k => j (b i k)) := by
        intro t
        obtain ⟨coef, hcoef⟩ :=
          (Submodule.mem_span_range_iff_exists_fun K).1 (mem_span_of_mem _ b hsp' (hyE t))
        refine (Submodule.mem_span_range_iff_exists_fun C).2 ⟨fun i => j (coef i), ?_⟩
        funext k
        rw [← hcoef]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
      rw [hxsum]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ (c t) (hyC t)
  have hbA : ∀ i' k, j (b i' k) ∈ (algebraMap A C).range := by
    intro i' k
    have h : ∀ k, b i' k ∈ (algebraMap V K).range := (Submodule.mem_inf.1 (hbmem i')).1
    exact hA _ (h k)
  have hmA : ∀ i k, j (algebraMap V K (m i k)) ∈ (algebraMap A C).range := fun i k =>
    hA _ (RingHom.mem_range.2 ⟨m i k, rfl⟩)
  refine ⟨hli, hspanC, ?_⟩
  show Submodule.span A _ = stdLat A C g ⊓ (HT.eigSp ρC (j.comp σ)).restrictScalars A
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i', rfl⟩
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · show ∀ k, j (b i' k) ∈ (algebraMap A C).range
      exact hbA i'
    · show (fun k => j (b i' k)) ∈ HT.eigSp ρC (j.comp σ)
      rw [← hspanC]
      exact Submodule.subset_span ⟨i', rfl⟩
  · intro x hx
    have hx1 : ∀ k, x k ∈ (algebraMap A C).range := (Submodule.mem_inf.1 hx).1
    have hx2 : x ∈ HT.eigSp ρC (j.comp σ) := (Submodule.mem_inf.1 hx).2
    rw [← hspanC] at hx2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hx2
    have hc' : ∑ i', c i' • (fun k => j (b i' k)) = x := hc
    have hcA : ∀ i, c i ∈ (algebraMap A C).range := by
      intro i
      rw [← hcoef c i, hc']
      exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hmA i k) (hx1 k)
    choose α hα using fun i => RingHom.mem_range.1 (hcA i)
    rw [← hc']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hα i, algebraMap_smul]
    exact Submodule.smul_mem _ (α i) (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig
