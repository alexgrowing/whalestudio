import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.RealHerbrand
import GroundTheory.ProfiniteCohomology.EulerChar
import GroundTheory.ProfiniteCohomology.CupProducts.Projection
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

universe u

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃]

theorem eulerChar_mul_eq_mul_card_range_δ (hS : S.ShortExact)
    [Finite (cohomology S.X₁ 1)] [Finite (cohomology S.X₂ 1)] [Finite (cohomology S.X₃ 1)] :
    eulerChar S.X₁ * eulerChar S.X₃ =
      eulerChar S.X₂ * Nat.card (LinearMap.range (δ hS 2 3 rfl).hom) := by
  have hk := fun {X Y : ModuleCat k} (φ : X ⟶ Y) => card_eq_card_ker_mul_card_range φ.hom
  have e2 : ∀ i, Nat.card (LinearMap.range (cohomologyMap S.f i).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.g i).hom) := fun i =>
    card_range_eq_card_ker_of_exact (cohomology_exact₂ hS i)
  have e30 : Nat.card (LinearMap.range (cohomologyMap S.g 0).hom) =
      Nat.card (LinearMap.ker (δ hS 0 1 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 0 1 rfl)
  have e31 : Nat.card (LinearMap.range (cohomologyMap S.g 1).hom) =
      Nat.card (LinearMap.ker (δ hS 1 2 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 1 2 rfl)
  have e32 : Nat.card (LinearMap.range (cohomologyMap S.g 2).hom) =
      Nat.card (LinearMap.ker (δ hS 2 3 rfl).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₃ hS 2 3 rfl)
  have e10 : Nat.card (LinearMap.range (δ hS 0 1 rfl).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.f 1).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 0 1 rfl)
  have e11 : Nat.card (LinearMap.range (δ hS 1 2 rfl).hom) =
      Nat.card (LinearMap.ker (cohomologyMap S.f 2).hom) :=
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 1 2 rfl)
  have h0 : Nat.card (LinearMap.ker (cohomologyMap S.f 0).hom) = 1 := by
    have := hS.mono_f
    have hm : Mono (cohomologyMap S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (cochainsMap S.f) 0
        (fun i => by simp)
    rw [LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 hm)]
    simp
  have hA1 : Nat.card (cohomology S.X₁ 1) ≠ 0 := Nat.card_pos.ne'
  have hB1 : Nat.card (cohomology S.X₂ 1) ≠ 0 := Nat.card_pos.ne'
  have hC1 : Nat.card (cohomology S.X₃ 1) ≠ 0 := Nat.card_pos.ne'
  rw [hk (cohomologyMap S.f 1), ← e10] at hA1
  rw [hk (cohomologyMap S.g 1), ← e2 1] at hB1
  rw [hk (δ hS 1 2 rfl), ← e31] at hC1
  rw [eulerChar_eq, eulerChar_eq, eulerChar_eq,
    hk (cohomologyMap S.f 0), hk (cohomologyMap S.f 1), hk (cohomologyMap S.f 2),
    hk (cohomologyMap S.g 0), hk (cohomologyMap S.g 1), hk (cohomologyMap S.g 2),
    hk (δ hS 0 1 rfl), hk (δ hS 1 2 rfl), hk (δ hS 2 3 rfl),
    h0, ← e2 0, ← e2 1, ← e2 2, ← e30, ← e31, ← e32, ← e10, ← e11]
  simp only [mul_ne_zero_iff] at hA1 hB1 hC1
  obtain ⟨hz0, hx1⟩ := hA1
  obtain ⟨-, hy1⟩ := hB1
  obtain ⟨-, hz1⟩ := hC1
  push_cast
  field_simp

theorem eulerChar_mul_eq_mul_card_ker (hS : S.ShortExact)
    [Finite (cohomology S.X₁ 1)] [Finite (cohomology S.X₂ 1)] [Finite (cohomology S.X₃ 1)] :
    eulerChar S.X₁ * eulerChar S.X₃ =
      eulerChar S.X₂ * Nat.card (LinearMap.ker (cohomologyMap S.f 3).hom) := by
  rw [eulerChar_mul_eq_mul_card_range_δ hS,
    card_range_eq_card_ker_of_exact (cohomology_exact₁ hS 2 3 rfl)]

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] in

theorem card_X₂_eq_of_shortExact (hS : S.ShortExact) [Finite S.X₂] :
    Nat.card S.X₂ = Nat.card S.X₁ * Nat.card S.X₃ := by
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex := (hS.exact.map (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)))
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  rw [card_eq_card_ker_mul_card_range S.g.hom.toLinearMap, LinearMap.range_eq_top.2 hsurj]
  congr 1
  · have hex' : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap := hex
    rw [← hex']
    exact (Nat.card_congr (LinearEquiv.ofInjective S.f.hom.toLinearMap hinj).toEquiv).symm
  · exact Nat.card_congr (Submodule.topEquiv).toEquiv

end Generic

section Kernels

variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Fintype ι] {Mv Nv : ι → Type*} [∀ v, AddCommGroup (Mv v)] [∀ v, Module R (Mv v)]
  [∀ v, AddCommGroup (Nv v)] [∀ v, Module R (Nv v)]

theorem card_ker_eq_prod_card_ker (f : M →ₗ[R] N) (fv : ∀ v, Mv v →ₗ[R] Nv v)
    (rA : M →ₗ[R] (∀ v, Mv v)) (rB : N →ₗ[R] (∀ v, Nv v))
    (hcomm : ∀ x v, rB (f x) v = fv v (rA x v)) (hA : Function.Bijective rA)
    (hB : Function.Injective rB) :
    Nat.card (LinearMap.ker f) = ∏ v, Nat.card (LinearMap.ker (fv v)) := by
  let ψ : LinearMap.ker f → ∀ v, LinearMap.ker (fv v) := fun x v =>
    ⟨rA x.1 v, by
      rw [LinearMap.mem_ker, ← hcomm, LinearMap.mem_ker.1 x.2, map_zero, Pi.zero_apply]⟩
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y hxy => Subtype.ext (hA.1 (funext fun v => ?_)), fun y => ?_⟩
    · exact congrArg Subtype.val (congrFun hxy v)
    · obtain ⟨x, hx⟩ := hA.2 (fun v => (y v).1)
      have hfx : f x = 0 := hB (by
        funext v
        rw [hcomm, hx, map_zero, Pi.zero_apply]
        exact (y v).2)
      exact ⟨⟨x, hfx⟩, funext fun v => Subtype.ext (congrFun hx v)⟩
  rw [Nat.card_congr (Equiv.ofBijective ψ hψ), Nat.card_pi]

end Kernels

section GS

theorem ratio_mul_eq {a b c nA nB nC PA PB PC κ : ℚ} (r : ℕ) (hPA : PA ≠ 0) (hPB : PB ≠ 0)
    (hPC : PC ≠ 0) (hn : nB = nA * nC) (hχ : a * c = b * κ) (hP : PA * PC = PB * κ) :
    b * nB ^ r / PB = a * nA ^ r / PA * (c * nC ^ r / PC) := by
  rw [div_mul_div_comm, div_eq_div_iff hPB (mul_ne_zero hPA hPC), hP, hn, mul_pow]
  linear_combination (-(nA ^ r * nC ^ r * PB)) * hχ

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  {T : ShortComplex (Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))}
  [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃]

theorem gsReal_card_mul_eq (hT : T.ShortExact) [Finite T.X₁] [Finite T.X₂] [Finite T.X₃]
    (v : {v : InfinitePlace K.1 // v.IsReal}) :
    (gsRealH0Card S T.X₁ ιr v : ℚ) * gsRealH0Card S T.X₃ ιr v =
      gsRealH0Card S T.X₂ ιr v * Nat.card (LinearMap.ker
        (cohomologyMap ((Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom).map T.f) 3).hom) := by
  have hTv := (Rep.shortExact_res (gsRealFamily S ιr v).toMonoidHom).2 hT
  have : IsDiscreteRep (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₁ :=
    inferInstanceAs (IsDiscreteRep (Rep.res (gsRealFamily S ιr v).toMonoidHom T.X₁))
  have : IsDiscreteRep (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₂ :=
    inferInstanceAs (IsDiscreteRep (Rep.res (gsRealFamily S ιr v).toMonoidHom T.X₂))
  have : IsDiscreteRep (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₃ :=
    inferInstanceAs (IsDiscreteRep (Rep.res (gsRealFamily S ιr v).toMonoidHom T.X₃))
  have : Finite (cohomology (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₁ 1) :=
    gsReal_finite_cohomology S ιr T.X₁ v 1 (by norm_num)
  have : Finite (cohomology (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₂ 1) :=
    gsReal_finite_cohomology S ιr T.X₂ v 1 (by norm_num)
  have : Finite (cohomology (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₃ 1) :=
    gsReal_finite_cohomology S ιr T.X₃ v 1 (by norm_num)
  have h := eulerChar_mul_eq_mul_card_ker hTv
  have e1 : eulerChar (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₁ =
      (gsRealH0Card S T.X₁ ιr v : ℚ) := gsReal_eulerChar_eq_card_cohomology_zero S ιr T.X₁ v
  have e2 : eulerChar (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₂ =
      (gsRealH0Card S T.X₂ ιr v : ℚ) := gsReal_eulerChar_eq_card_cohomology_zero S ιr T.X₂ v
  have e3 : eulerChar (T.map (Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom)).X₃ =
      (gsRealH0Card S T.X₃ ιr v : ℚ) := gsReal_eulerChar_eq_card_cohomology_zero S ιr T.X₃ v
  exact ((congrArg₂ (· * ·) e1 e3).symm.trans h).trans (congrArg (· * _) e2)

omit [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] in

theorem gsRealRes_cohomologyMap {A B : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)}
    [IsDiscreteRep A] [IsDiscreteRep B] (f : A ⟶ B) (n : ℕ) (x : cohomology A n)
    (v : {v : InfinitePlace K.1 // v.IsReal}) :
    (gsRealRes S ιr B n).hom ((cohomologyMap f n).hom x) v =
      (cohomologyMap ((Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom).map f) n).hom
        ((gsRealRes S ιr A n).hom x v) := by
  have h1 := cohomologyMapAlong_cohomologyMap (gsRealFamily S ιr v).toMonoidHom
    (continuous_toMonoidHom _) f (𝟙 _) x
  have h2 := cohomologyMap_cohomologyMapAlong (gsRealFamily S ιr v).toMonoidHom
    (continuous_toMonoidHom _) (𝟙 _) ((Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom).map f) x
  have c1 := congrArg (fun g => (cohomologyMapAlong (gsRealFamily S ιr v).toMonoidHom
    (continuous_toMonoidHom _) g n).hom x)
    (Category.comp_id ((Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom).map f))
  have c2 := congrArg (fun g => (cohomologyMapAlong (gsRealFamily S ιr v).toMonoidHom
    (continuous_toMonoidHom _) g n).hom x)
    (Category.id_comp ((Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom).map f))
  exact (h1.trans c1).trans (h2.trans c2).symm

open scoped Classical in

theorem gsEulerRatio_shortExact [Finite S] (hT : T.ShortExact) [Finite T.X₂]
    (hn : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card T.X₂ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hA : Function.Bijective (gsRealRes S ιr T.X₁ 3).hom)
    (hB : Function.Injective (gsRealRes S ιr T.X₂ 3).hom) :
    gsEulerRatio S T.X₂ ιr = gsEulerRatio S T.X₁ ιr * gsEulerRatio S T.X₃ ιr := by
  have hinj : Function.Injective T.f.hom := (Rep.mono_iff_injective _).1 hT.mono_f
  have hsurj : Function.Surjective T.g.hom := (Rep.epi_iff_surjective _).1 hT.epi_g
  have : Finite T.X₁ := Finite.of_injective _ hinj
  have : Finite T.X₃ := Finite.of_surjective _ hsurj
  have hcard := card_X₂_eq_of_shortExact hT
  have hn1 : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card T.X₁ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S :=
    fun v hv => hn v (by rw [hcard, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hv)
  have hn3 : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card T.X₃ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S :=
    fun v hv => hn v (by rw [hcard, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hv)
  have : Finite (cohomology T.X₁ 1) := finite_cohomology_gs K S T.X₁ hn1 1 (by norm_num)
  have : Finite (cohomology T.X₂ 1) := finite_cohomology_gs K S T.X₂ hn 1 (by norm_num)
  have : Finite (cohomology T.X₃ 1) := finite_cohomology_gs K S T.X₃ hn3 1 (by norm_num)
  have hglob := eulerChar_mul_eq_mul_card_ker hT
  have hker := card_ker_eq_prod_card_ker (cohomologyMap T.f 3).hom
    (fun v => (cohomologyMap ((Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom).map T.f) 3).hom)
    (gsRealRes S ιr T.X₁ 3).hom (gsRealRes S ιr T.X₂ 3).hom
    (fun x v => gsRealRes_cohomologyMap S ιr T.f 3 x v) hA hB
  have hloc := fun v => gsReal_card_mul_eq S ιr hT v
  have hPA : (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S T.X₁ ιr v : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => by exact_mod_cast (gsRealH0Card_pos S T.X₁ ιr v).ne'
  have hPB : (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S T.X₂ ιr v : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => by exact_mod_cast (gsRealH0Card_pos S T.X₂ ιr v).ne'
  have hPC : (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S T.X₃ ιr v : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => by exact_mod_cast (gsRealH0Card_pos S T.X₃ ιr v).ne'
  have hprod : (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S T.X₁ ιr v : ℚ)) *
      ∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S T.X₃ ιr v : ℚ) =
      (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S T.X₂ ιr v : ℚ)) *
        (Nat.card (LinearMap.ker (cohomologyMap T.f 3).hom) : ℚ) := by
    refine Finset.prod_mul_distrib.symm.trans
      ((Finset.prod_congr rfl (fun v _ => hloc v)).trans (Finset.prod_mul_distrib.trans ?_))
    exact congrArg (_ * ·) ((Nat.cast_prod _ _).symm.trans (congrArg Nat.cast hker.symm))
  exact ratio_mul_eq (Fintype.card (InfinitePlace K.1)) hPA hPB hPC (by exact_mod_cast hcard)
    hglob hprod

open scoped Classical in

theorem gsEulerRatio_shortExact_of_bijective [Finite S] (hT : T.ShortExact) [Finite T.X₂]
    (hn : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card T.X₂ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hA : Function.Bijective (gsRealRes S ιr T.X₁ 3).hom)
    (hB : Function.Bijective (gsRealRes S ιr T.X₂ 3).hom) :
    gsEulerRatio S T.X₂ ιr = gsEulerRatio S T.X₁ ιr * gsEulerRatio S T.X₃ ιr :=
  gsEulerRatio_shortExact S ιr hT hn hA hB.1

end GS

end GroundTheory.ProfCoh
