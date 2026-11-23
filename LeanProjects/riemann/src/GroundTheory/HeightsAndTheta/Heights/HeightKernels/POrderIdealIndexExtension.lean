import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PInvertibleIdealIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace OrderIdealIndexExtensionAlt

theorem index_ne_zero_of_zsmul_mem {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] (H : AddSubgroup M)
    {N : ℤ} (hN : N ≠ 0) (h : ∀ x : M, N • x ∈ H) : H.index ≠ 0 := by
  have htor : Module.IsTorsion ℤ (M ⧸ H.toIntSubmodule) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine ⟨⟨N, mem_nonZeroDivisors_of_ne_zero hN⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact h x
  have : Finite (M ⧸ H.toIntSubmodule) := Module.finite_of_fg_torsion _ htor
  have : Finite (M ⧸ H) := this
  exact AddSubgroup.index_ne_zero_of_finite

variable {L : Type} [Field L]

theorem exists_int_eq_mul [CharZero L] {B : Subring L} [Module.Finite ℤ B] {a : B} (ha : a ≠ 0) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ q : B, (c : B) = a * q := by
  have hi : IsIntegral ℤ a := IsIntegral.of_finite ℤ a
  have h0 : (minpoly ℤ a).coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hm := minpoly.monic hi
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X (hq ▸ hm)
    have hqa : Polynomial.aeval a q = 0 := by
      have h1 := minpoly.aeval ℤ a
      rw [hq, map_mul, Polynomial.aeval_X] at h1
      exact (mul_eq_zero.mp h1).resolve_left ha
    have h2 := minpoly.min ℤ a hqm hqa
    rw [hq, Polynomial.degree_mul, Polynomial.degree_X, Polynomial.degree_eq_natDegree hqm.ne_zero] at h2
    norm_cast at h2
    omega
  refine ⟨(minpoly ℤ a).coeff 0, h0, ?_⟩
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ a)
  refine ⟨-(Polynomial.aeval a q), ?_⟩
  have h := congrArg (Polynomial.aeval a) hq
  simp only [map_sub, minpoly.aeval, map_mul, Polynomial.aeval_X, eq_intCast, map_intCast] at h
  linear_combination -h

variable [NumberField L] {B : Subring L} [Module.Finite ℤ B]

theorem exists_family : ∃ S : Set (𝓞 L), S.Finite ∧ LinearIndepOn B (fun x : 𝓞 L => (x : L)) S ∧
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x : 𝓞 L,
      (N : L) * (x : L) ∈ Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_maximal_linearIndepOn B (fun x : 𝓞 L => (x : L))
  set F := Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) with hF
  have hfin : S.Finite := by
    have h1 : LinearIndependent ℤ (fun x : S => ((x : 𝓞 L) : L)) := hS.restrict_scalars' ℤ
    have h2 : LinearIndependent ℤ (fun x : S => (x : 𝓞 L)) :=
      LinearIndependent.of_comp (algebraMap (𝓞 L) L).toIntAlgHom.toLinearMap h1
    exact Set.finite_coe_iff.mp h2.finite
  refine ⟨S, hfin, hS, ?_⟩
  have hone : ∀ x : 𝓞 L, ∃ c : ℤ, c ≠ 0 ∧ (c : L) * (x : L) ∈ F := by
    intro x
    by_cases hx : x ∈ S
    · exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span (Set.mem_image_of_mem _ hx)⟩
    · obtain ⟨a, ha, hax⟩ := hmax x hx
      obtain ⟨c, hc, q, hcq⟩ := exists_int_eq_mul ha
      refine ⟨c, hc, ?_⟩
      have h1 : (c : L) * (x : L) = q • (a • (x : L)) := by
        have h2 : (c : L) = ((c : B) : L) := by push_cast; rfl
        rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, h2, hcq]
        push_cast
        ring
      rw [h1]
      exact F.smul_mem q hax
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 L)
  choose c hc0 hcF using hone
  set N := ∏ g ∈ T, c g with hN
  refine ⟨N, Finset.prod_ne_zero_iff.mpr fun g _ => hc0 g, ?_⟩
  have hgen : ∀ g ∈ T, (N : L) * (g : L) ∈ F := by
    intro g hg
    have h1 : (N : L) * (g : L) = (∏ h ∈ T.erase g, c h) • ((c g : L) * (g : L)) := by
      rw [hN, ← Finset.mul_prod_erase T c hg, zsmul_eq_mul]
      push_cast
      ring
    rw [h1]
    exact F.toAddSubgroup.zsmul_mem (hcF g) _
  intro x
  have hx : x ∈ Submodule.span ℤ (T : Set (𝓞 L)) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ hy hz =>
    have h1 : (N : L) * ((y + z : 𝓞 L) : L) = (N : L) * (y : L) + (N : L) * (z : L) := by
      push_cast
      ring
    rw [h1]
    exact F.add_mem hy hz
  | smul n y _ hy =>
    have h1 : (N : L) * ((n • y : 𝓞 L) : L) = n • ((N : L) * (y : L)) := by
      have h2 : ((n • y : 𝓞 L) : L) = n • (y : L) := map_zsmul (algebraMap (𝓞 L) L) n y
      rw [h2, mul_smul_comm]
    rw [h1]
    exact F.toAddSubgroup.zsmul_mem hy _

end OrderIdealIndexExtensionAlt

open OrderIdealIndexExtensionAlt InvertibleIdealIndexAlt in

theorem OrderIdealIndexExtension.proof : OrderIdealIndexExtension.Statement := by
  intro L _ _ B hB
  classical
  have := hB
  obtain ⟨S, hSfin, hS, N, hN, hNF⟩ := exists_family (L := L) (B := B)
  have : Fintype S := hSfin.fintype
  set v : S → L := fun x => ((x : 𝓞 L) : L) with hv
  set φ : (S → B) →ₗ[B] L := Fintype.linearCombination B v with hφ
  have hφinj : Function.Injective φ :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp hS
  set Fs := Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) with hFs
  have hrange : ∀ y, y ∈ Fs ↔ ∃ β, φ β = y := by
    intro y
    rw [← LinearMap.mem_range, hφ, Fintype.range_linearCombination, hFs, Set.image_eq_range]
  set O := (1 : Submodule (𝓞 L) L).toAddSubgroup with hO
  set F := Fs.toAddSubgroup with hF
  have hmemO : ∀ x : 𝓞 L, (x : L) ∈ O := fun x => Submodule.mem_one.mpr ⟨x, rfl⟩
  have hOmem : ∀ y ∈ O, ∃ x : 𝓞 L, (x : L) = y := fun y hy => Submodule.mem_one.mp hy
  have hBF : ∀ b : B, ∀ y ∈ F, (b : L) * y ∈ F := fun b y hy => by
    have h1 := Fs.smul_mem b hy
    rwa [Subring.smul_def, smul_eq_mul] at h1
  have hFO : F ≤ O := by
    intro y hy
    obtain ⟨β, rfl⟩ := (hrange y).1 hy
    rw [hφ, Fintype.linearCombination_apply]
    refine O.sum_mem fun j _ => ?_
    rw [Subring.smul_def, smul_eq_mul]
    exact mul_mem_of_mem (β j).2 (hmemO _)
  have hNO : ∀ y ∈ O, (N : L) * y ∈ F := by
    intro y hy
    obtain ⟨x, rfl⟩ := hOmem y hy
    exact hNF x

  let toO : 𝓞 L →+ O :=
    { toFun := fun x => ⟨(x : L), hmemO x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have htoO : Function.Surjective toO := by
    intro y
    obtain ⟨x, hx⟩ := hOmem y y.2
    exact ⟨x, Subtype.ext hx⟩
  have : Module.Finite ℤ O := Module.Finite.of_surjective toO.toIntLinearMap htoO
  have hFOidx : F.relIndex O ≠ 0 := by
    refine index_ne_zero_of_zsmul_mem (F.addSubgroupOf O) hN fun x => ?_
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_zsmul, zsmul_eq_mul]
    exact hNO x x.2

  have hint : ∀ β, IsIntegral ℤ (φ β) := fun β => by
    obtain ⟨x, hx⟩ := hOmem _ (hFO ((hrange _).2 ⟨β, rfl⟩))
    rw [← hx]
    exact x.isIntegral_coe
  let g1 : (S → B) →+ 𝓞 L :=
    { toFun := fun β => ⟨φ β, hint β⟩
      map_zero' := RingOfIntegers.ext (by
        show φ 0 = algebraMap (𝓞 L) L 0
        rw [map_zero, map_zero])
      map_add' := fun x y => RingOfIntegers.ext (by
        show φ (x + y) = algebraMap (𝓞 L) L (_ + _)
        rw [map_add]
        exact (map_add (algebraMap (𝓞 L) L) (⟨φ x, hint x⟩ : 𝓞 L) ⟨φ y, hint y⟩).symm) }
  have hg1 : Function.Injective g1 := fun a b h => hφinj (congrArg (fun x : 𝓞 L => (x : L)) h)
  have hsurj : ∀ x : 𝓞 L, ∃ β, φ β = (N : L) * (x : L) := fun x => (hrange _).1 (hNF x)
  choose g2 hg2 using hsurj
  have hg2add : ∀ x y, g2 (x + y) = g2 x + g2 y := fun x y => hφinj (by
    rw [map_add, hg2, hg2, hg2]; push_cast; ring)
  let g2' : 𝓞 L →+ (S → B) := AddMonoidHom.mk' g2 hg2add
  have hg2inj : Function.Injective g2' := fun x y h => by
    have h1 := congrArg φ h
    simp only [g2', AddMonoidHom.mk'_apply, hg2] at h1
    exact RingOfIntegers.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hN) h1)
  have hr1 := LinearMap.finrank_le_finrank_of_injective (f := g1.toIntLinearMap) hg1
  have hr2 := LinearMap.finrank_le_finrank_of_injective (f := g2'.toIntLinearMap) hg2inj
  have hrank : Module.finrank ℚ L = Fintype.card S * Module.finrank ℤ B := by
    rw [← RingOfIntegers.rank, le_antisymm hr2 hr1, Module.finrank_pi_fintype]
    simp
  refine ⟨Fintype.card S, (N : B), ?_, hrank, ?_, ?_⟩
  · intro h
    apply hN
    have h1 := congrArg (fun b : B => (b : L)) h
    simpa using h1
  · intro I hI
    obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, q, hcq⟩ := exists_int_eq_mul ht0
    refine index_ne_zero_of_zsmul_mem I.toAddSubgroup hc fun x => ?_
    rw [Submodule.mem_toAddSubgroup, zsmul_eq_mul, hcq, mul_assoc]
    exact I.mul_mem_right _ htI
  intro I hI hcase
  set J := (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup with hJ
  set IF := (AddSubgroup.pi Set.univ (fun _ : S => I.toAddSubgroup)).map φ.toAddMonoidHom with hIF
  have hmemIF : ∀ y, y ∈ IF ↔ ∃ β : S → B, (∀ j, β j ∈ I) ∧ φ β = y := by
    intro y
    simp [hIF, AddSubgroup.mem_pi]
  have hFtop : (⊤ : AddSubgroup (S → B)).map φ.toAddMonoidHom = F := by
    ext y
    simp [hF, hrange]
  have hIFidx : IF.relIndex F = I.toAddSubgroup.index ^ Fintype.card S := by
    rw [← hFtop, hIF, AddSubgroup.relIndex_map_map_of_injective _ _ hφinj,
      AddSubgroup.relIndex_top_right, AddSubgroup.index_pi]
    simp
  have hJO : J ≤ O := by
    intro y hy
    refine (Submodule.span_le.mpr ?_) hy
    rintro _ ⟨b, -, rfl⟩
    exact mem_one_of_mem b.2
  have hIF_I : ∀ i ∈ I, ∀ y ∈ F, (i : L) * y ∈ IF := by
    intro i hi y hy
    obtain ⟨β, rfl⟩ := (hrange y).1 hy
    refine (hmemIF _).2 ⟨i • β, fun j => ?_, ?_⟩
    · simpa using I.mul_mem_right (β j) hi
    · rw [map_smul, Subring.smul_def, smul_eq_mul]
  have hB_IF : ∀ b : B, ∀ y ∈ IF, (b : L) * y ∈ IF := by
    intro b y hy
    obtain ⟨β, hβ, rfl⟩ := (hmemIF y).1 hy
    refine (hmemIF _).2 ⟨b • β, fun j => ?_, ?_⟩
    · simpa using I.mul_mem_left b (hβ j)
    · rw [map_smul, Subring.smul_def, smul_eq_mul]
  have hIF_F : IF ≤ F := by
    intro y hy
    obtain ⟨β, -, rfl⟩ := (hmemIF y).1 hy
    exact (hrange _).2 ⟨β, rfl⟩
  have hIF_J : IF ≤ J := by
    intro y hy
    obtain ⟨β, hβ, rfl⟩ := (hmemIF y).1 hy
    rw [hφ, Fintype.linearCombination_apply]
    refine J.sum_mem fun j _ => ?_
    have h1 : β j • v j = (j : 𝓞 L) • ((β j : B) : L) := by
      rw [Subring.smul_def, smul_eq_mul, Algebra.smul_def, mul_comm]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨β j, hβ j, rfl⟩)
  rcases hcase with hP | hcop
  ·
    obtain ⟨t, hIt⟩ : ∃ t : B, I = Ideal.span {t} :=
      ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
    have ht0 : (t : L) ≠ 0 := by
      intro h
      apply hI
      rw [hIt, Ideal.span_singleton_eq_bot]
      exact Subtype.ext h
    have hJt : J = O.map (mulBy (t : L)) := by
      rw [hJ, hIt, ← map_mul_eq_span t]
    have hIFt : IF = F.map (mulBy (t : L)) := by
      ext y
      rw [hmemIF]
      constructor
      · rintro ⟨β, hβ, rfl⟩
        have h1 : ∀ j, ∃ a : B, a * t = β j := fun j => by
          have := hβ j
          rw [hIt] at this
          exact Ideal.mem_span_singleton'.mp this
        choose a ha using h1
        refine ⟨φ a, (hrange _).2 ⟨a, rfl⟩, ?_⟩
        have h2 : β = t • a := funext fun j => by simp [← ha j, mul_comm]
        rw [h2, mulBy_apply, map_smul, Subring.smul_def, smul_eq_mul]
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨a, rfl⟩ := (hrange z).1 hz
        refine ⟨t • a, fun j => ?_, ?_⟩
        · rw [hIt]
          simpa using Ideal.mul_mem_right (a j) _ (Ideal.mem_span_singleton_self t)
        · rw [mulBy_apply, map_smul, Subring.smul_def, smul_eq_mul]
    have hFt : F.map (mulBy (t : L)) ≤ F := by
      rintro _ ⟨z, hz, rfl⟩
      exact hBF t z hz
    have hOt : O.map (mulBy (t : L)) ≤ O := by
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem_of_mem t.2 hz
    have e1 : (F.map (mulBy (t : L))).relIndex (O.map (mulBy (t : L))) = F.relIndex O :=
      AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective ht0)
    have h1 := (AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hFO) hOt).trans
      (AddSubgroup.relIndex_mul_relIndex _ _ _ hFt hFO).symm
    rw [e1, mul_comm (AddSubgroup.relIndex _ F)] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hFOidx) h1
    rw [hJt, h2, ← hIFt, hIFidx]
  ·
    have h1 : (1 : B) ∈ I ⊔ Ideal.span {(N : B)} := hcop ▸ Submodule.mem_top
    obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hib : (i : L) + (b : L) * (N : L) = 1 := by
      have := congrArg (fun x : B => (x : L)) hiz
      simpa using this
    have key : ∀ y ∈ Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B)), ∀ o : 𝓞 L,
        (N : L) * ((o : L) * y) ∈ IF := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        intro o
        rw [show (N : L) * ((o : L) * (j : L)) = (j : L) * ((N : L) * (o : L)) by ring]
        exact hIF_I j hj _ (hNO _ (hmemO o))
      | zero =>
        intro o
        rw [mul_zero, mul_zero]
        exact IF.zero_mem
      | add y w _ _ hy hw =>
        intro o
        rw [mul_add, mul_add]
        exact IF.add_mem (hy o) (hw o)
      | smul a y _ hy =>
        intro o
        have h2 : (N : L) * ((o : L) * (a • y)) = (N : L) * (((o * a : 𝓞 L) : L) * y) := by
          rw [Algebra.smul_def]
          push_cast
          ring_nf
        rw [h2]
        exact hy (o * a)
    have hsup : J ⊔ F = O := by
      refine le_antisymm (sup_le hJO hFO) fun x hx => ?_
      obtain ⟨o, rfl⟩ := hOmem x hx
      have h2 : (o : L) = (i : L) * (o : L) + (b : L) * ((N : L) * (o : L)) := by
        linear_combination (-(o : L)) * hib
      rw [h2]
      refine AddSubgroup.add_mem_sup ?_ (hBF b _ (hNO _ hx))
      have h3 : (i : L) * (o : L) = o • (i : L) := by
        rw [Algebra.smul_def, mul_comm]
      rw [h3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    have hinf : J ⊓ F = IF := by
      refine le_antisymm (fun y hy => ?_) (le_inf hIF_J hIF_F)
      have h2 : y = (i : L) * y + (b : L) * ((N : L) * y) := by
        linear_combination (-y) * hib
      rw [h2]
      refine IF.add_mem (hIF_I i hi y hy.2) (hB_IF b _ ?_)
      simpa using key y hy.1 1
    calc J.relIndex O = J.relIndex (J ⊔ F) := by rw [hsup]
      _ = J.relIndex F := AddSubgroup.relIndex_sup_left _ _
      _ = (J ⊓ F).relIndex F := (AddSubgroup.inf_relIndex_right _ _).symm
      _ = IF.relIndex F := by rw [hinf]
      _ = _ := hIFidx

end

end GroundTheory.Heights₂.Heights
