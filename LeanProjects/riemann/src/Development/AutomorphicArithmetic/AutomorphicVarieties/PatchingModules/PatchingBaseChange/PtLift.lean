import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PsEv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaOverLift
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem root_const {O K : Type} [CommRing O] [Field K] [Algebra O K] (P : Polynomial O) (hm : P.Monic)
    (hs : (P.map (algebraMap O K)).Splits) (y : PowerSeries K)
    (hy : Polynomial.eval₂ (algebraMap O (PowerSeries K)) y P = 0) : ∃ c : K, y = PowerSeries.C c := by
  have h : algebraMap O (PowerSeries K) = (PowerSeries.C : K →+* PowerSeries K).comp (algebraMap O K) :=
    RingHom.ext fun a => PowerSeries.algebraMap_apply
  rw [h, ← Polynomial.eval₂_map, hs.eq_prod_roots_of_monic (hm.map _), Polynomial.eval₂_multiset_prod,
    Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map] at hy
  obtain ⟨c, -, hc⟩ := hy
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hc
  exact ⟨c, sub_eq_zero.1 hc⟩

private theorem surj_of_card {O' K : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field K]
    [Finite K] (φ : O' →+* K) (hc : Nat.card (ResidueField O') = Nat.card K) : Function.Surjective φ := by
  have hne : RingHom.ker φ ≠ ⊥ := by
    intro h
    have hi : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h
    haveI : Finite O' := Finite.of_injective φ hi
    exact IsDiscreteValuationRing.not_isField O' (Finite.isField_of_domain O')
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : RingHom.ker φ = maximalIdeal O' :=
    IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
  let g : ResidueField O' →+* K := Ideal.Quotient.lift (maximalIdeal O') φ (fun a ha => by
    rw [← hmax] at ha; exact ha)
  have hg : Function.Bijective g := by
    haveI : Finite (ResidueField O') := Finite.of_injective g g.injective
    exact (Nat.bijective_iff_injective_and_card g).2 ⟨g.injective, hc⟩
  intro k
  obtain ⟨a, ha⟩ := hg.2 k
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨b, ha⟩

private theorem exists_pt {O O' B K : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing B] [Algebra O B]
    [Field K] [Algebra O K] (α : O') (P : Polynomial O) (f : B →ₐ[O] PowerSeries K) (Q : Ideal (O' ⊗[O] B))
    (hα : Algebra.adjoin O {α} = ⊤) (hm : P.Monic) (h0 : Polynomial.aeval α P = 0)
    (hs : (P.map (algebraMap O K)).Splits) (hQ : Q.IsPrime)
    (hc : Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = RingHom.ker f) :
    ∃ x : O' ⊗[O] B →+* PowerSeries K, (∀ b, x (1 ⊗ₜ b) = f b) ∧ RingHom.ker x = Q := by
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  have hB : ∀ b : B, algebraMap B (O' ⊗[O] B) b = 1 ⊗ₜ b := fun b => rfl
  have hcomp : (algebraMap B (O' ⊗[O] B)).comp (algebraMap O B) =
      (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B).comp (algebraMap O O') :=
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
  obtain ⟨x, hx1, hx2⟩ := UpperTheory.V.AlgebraTools.exists_lift_ker_eq B (O' ⊗[O] B) (PowerSeries K) f.toRingHom Unit
    (fun _ => α ⊗ₜ 1) (fun _ => P.map (algebraMap O B)) (by
      have hl : ∀ o : O', o ⊗ₜ[O] (1 : B) ∈ Algebra.adjoin B (Set.range fun _ : Unit => α ⊗ₜ[O] (1 : B)) := by
        intro o
        have ho : o ∈ Algebra.adjoin O {α} := hα ▸ Algebra.mem_top
        induction ho using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff.1 hy]
          exact Algebra.subset_adjoin ⟨(), rfl⟩
        | algebraMap r =>
          have := RingHom.congr_fun hcomp r
          change algebraMap B (O' ⊗[O] B) (algebraMap O B r) = algebraMap O O' r ⊗ₜ 1 at this
          rw [← this]
          exact Subalgebra.algebraMap_mem _ _
        | add y z _ _ hy hz => rw [TensorProduct.add_tmul]; exact add_mem hy hz
        | mul y z _ _ hy hz =>
          have := mul_mem hy hz
          rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
      rw [eq_top_iff]
      rintro s -
      induction s using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | tmul o b =>
        have := mul_mem (hl o) (Subalgebra.algebraMap_mem _ b)
        rwa [hB, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
      | add y z hy hz => exact add_mem hy hz)
    (fun _ => ⟨hm.map _, by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
      have := Polynomial.hom_eval₂ P (algebraMap O O')
        (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B) α
      rw [← Polynomial.aeval_def, h0, map_zero] at this
      exact this.symm, by
      have h : f.toRingHom.comp (algebraMap O B) = (PowerSeries.C : K →+* PowerSeries K).comp (algebraMap O K) :=
        RingHom.ext fun a => (f.commutes a).trans PowerSeries.algebraMap_apply
      rw [Polynomial.map_map, h, ← Polynomial.map_map]
      exact hs.map _⟩) Q hQ hc
  exact ⟨x, fun b => RingHom.congr_fun hx1 b, hx2⟩

theorem UpperTheory.V.Pa.BC.pt_lift :
    ∀ (l : ℕ) [Fact l.Prime] (O O' : Type) [CommRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsCoef l O'] [Algebra O O'] (α : O') (P : Polynomial O) (B : Type) [CommRing B] [Algebra O B] (K : Type) [Field K] [Finite K] [Algebra O K] (f : B →ₐ[O] PowerSeries K) (Q : Ideal (O' ⊗[O] B)), Algebra.adjoin O {α} = ⊤ → P.Monic → Polynomial.aeval α P = 0 → (P.map (algebraMap O K)).Splits → Nat.card (ResidueField O') = Nat.card K → Q.IsPrime → Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = RingHom.ker f → ∃ (_ : Algebra O' K) (f' : Til O O' B →ₐ[O'] PowerSeries K), Function.Surjective (algebraMap O' K) ∧ (∀ b, f' (Til.ι O O' B b) = f b) ∧ f' (Til.s O O' B) = PowerSeries.X ∧ (RingHom.ker f').comap (Til.C O O' B) = Q := by
  intro l _ O O' _ _ _ _ _ _ α P B _ _ K _ _ _ f Q hα hm h0 hs hcard hQ hc
  obtain ⟨x, hx1, hx2⟩ := exists_pt α P f Q hα hm h0 hs hQ hc
  let y : O' →+* PowerSeries K := x.comp (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B)
  have hyO : y.comp (algebraMap O O') = algebraMap O (PowerSeries K) := by
    refine RingHom.ext fun r => ?_
    have := RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := O) (A := O') (B := B)) r
    change x ((Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap O O')) r) = _
    rw [this]
    exact (hx1 _).trans (f.commutes r)
  have hconst : ∀ o : O', ∃ c : K, y o = PowerSeries.C c := by
    intro o
    have ho : o ∈ Algebra.adjoin O {α} := hα ▸ Algebra.mem_top
    induction ho using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff.1 hz]
      refine root_const P hm hs _ ?_
      rw [← hyO, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, h0, map_zero]
    | algebraMap r => exact ⟨algebraMap O K r, (RingHom.congr_fun hyO r).trans PowerSeries.algebraMap_apply⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' + b', by rw [map_add, map_add, ha, hb]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' * b', by rw [map_mul, map_mul, ha, hb]⟩
  let φ : O' →+* K := (PowerSeries.constantCoeff : PowerSeries K →+* K).comp y
  have hφ : ∀ o, y o = PowerSeries.C (φ o) := by
    intro o
    obtain ⟨c, hc⟩ := hconst o
    change _ = PowerSeries.C (PowerSeries.constantCoeff (y o))
    rw [hc, PowerSeries.constantCoeff_C]
  obtain ⟨g, hg1, hg2⟩ := UpperTheory.V.Pa.BC.ps_ev (O' ⊗[O] B) K x
  letI : Algebra O' K := φ.toAlgebra
  let g' : Til O O' B →+* PowerSeries K := g
  have hg1' : ∀ a, g' (Til.C O O' B a) = x a := hg1
  refine ⟨this, { g' with commutes' := fun o => ?_ }, surj_of_card φ hcard, fun b => ?_, hg2, ?_⟩
  · have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
      PowerSeries.algebraMap_apply
    change g' (algebraMap O' (Til O O' B) o) = _
    rw [h, hg1', PowerSeries.algebraMap_apply]
    exact hφ o
  · exact (hg1' _).trans (hx1 b)
  · ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hx2, RingHom.mem_ker, ← hg1']
    rfl
