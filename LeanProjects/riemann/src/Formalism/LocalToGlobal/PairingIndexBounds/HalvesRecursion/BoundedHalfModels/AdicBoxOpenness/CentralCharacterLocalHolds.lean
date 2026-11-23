import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfGen

noncomputable section
open scoped BigOperators nonZeroDivisors

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem phi_injective_holds : PhiInj := by
  intro D cc δ N N' hδ y z h
  have : Nonempty D.what₂.Tau := by
    apply Fintype.card_pos_iff.1
    rw [FL.card_tau D]; positivity
  obtain ⟨τ⟩ := (inferInstance : Nonempty D.what₂.Tau)
  funext i j
  have h1 := congrFun (congrFun (congrFun h τ) i) j
  simp only [Phi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, embV, tor0] at h1
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem good_duality_holds : GoodDual := by
  intro V _ _ H A B Λ hH hA hB hsum hsd
  have hanti : ∀ x y : V, altE H y x = -altE H x y := by
    intro x y
    simp only [altE]
    rw [hH x y]
    simp
  have hadd : ∀ w y₁ y₂ : V, altE H w (y₁ + y₂) = altE H w y₁ + altE H w y₂ := by
    intro w y₁ y₂; simp [altE, map_add]
  constructor
  · intro a ha h
    apply hsd
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := AddSubgroup.mem_sup.1 (hsum hy)
    obtain ⟨m₁, hm₁⟩ := hA a ha y₁ (AddSubgroup.mem_inf.1 hy₁).2
    obtain ⟨m₂, hm₂⟩ := h y₂ (AddSubgroup.mem_inf.1 hy₂).2 (AddSubgroup.mem_inf.1 hy₂).1
    exact ⟨m₁ + m₂, by rw [hadd, hm₁, hm₂, Int.cast_add]⟩
  · intro b hb h
    apply hsd
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := AddSubgroup.mem_sup.1 (hsum hy)
    obtain ⟨m₁, hm₁⟩ := h y₁ (AddSubgroup.mem_inf.1 hy₁).2 (AddSubgroup.mem_inf.1 hy₁).1
    obtain ⟨m₂, hm₂⟩ := hB b hb y₂ (AddSubgroup.mem_inf.1 hy₂).2
    refine ⟨-m₁ + m₂, ?_⟩
    rw [hadd, hanti y₁ b, hm₁, hm₂, Int.cast_add, Int.cast_neg]

theorem equality_off_boundary_holds : EqOffBound := by
  intro D P π hπ N L L₀ h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have h1 := hm (π ^ m) (cO D π ^ m) (by rw [← map_pow]; rfl) (Ideal.pow_mem_pow hπ m)
  simpa only [mul_pow] using h1

theorem oSmul (D : D7) {m n : Type} (x : 𝓞 D.host.E) (A : Matrix m n D.host.E) :
    x • A = (x : D.host.E) • A := by
  ext i j
  rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

def kE (D : D7) (c : 𝓞 D.host.K) : 𝓞 D.host.E := ⟨((c : D.host.K) : D.host.E), FL.intK D c⟩

theorem kE_mem (D : D7) (cc : Ideal (𝓞 D.host.K)) (c : 𝓞 D.host.K) (hc : c ∈ cc) : kE D c ∈ ccE D cc :=
  Ideal.subset_span ⟨c, hc, rfl⟩

theorem multiplicity_equality_holds : MMeq := by
  intro D cc N N' L L'
  apply le_antisymm
  · rw [MM, AddSubgroup.closure_le]
    rintro y ⟨c, hc, A, hA, rfl⟩
    have : ((c : D.host.K) : D.host.E) • A = kE D c • A := by
      rw [oSmul]; rfl
    rw [this]
    exact Submodule.smul_mem_smul (kE_mem D cc c hc) hA
  · intro y hy
    change y ∈ ccE D cc • YYl D L L' at hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro x hx A hA
      induction hx using Submodule.span_induction generalizing A with
      | mem x hx =>
        obtain ⟨c, hc, hxc⟩ := hx
        apply AddSubgroup.subset_closure
        refine ⟨c, hc, A, hA, ?_⟩
        rw [oSmul, hxc]
      | zero => rw [zero_smul]; exact AddSubgroup.zero_mem _
      | add x₁ x₂ _ _ h1 h2 => rw [add_smul]; exact AddSubgroup.add_mem _ (h1 A hA) (h2 A hA)
      | smul r x _ h1 =>
        rw [smul_eq_mul, mul_comm, mul_smul]
        exact h1 _ (Submodule.smul_mem _ r hA)
    · intro a b ha hb; exact AddSubgroup.add_mem _ ha hb

theorem lattice_equality_map_holds : LaEqMap := by
  intro D cc δ N N' L L'
  rw [MM, AddMonoidHom.map_closure]
  apply le_antisymm
  · refine (IO.La_le_gen cc δ L L').trans ?_
    rw [AddSubgroup.closure_le]
    rintro z ⟨c, hc, A, hA, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨((c : D.host.K) : D.host.E) • A, ⟨c, hc, A, hA, rfl⟩, ?_⟩
    funext τ i j
    simp only [Phi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, embV, tor0,
      Matrix.smul_apply]
    rw [map_mul, FL.embT_K D τ _ (((c : D.host.K)).2)]
    ring
  · rw [AddSubgroup.closure_le]
    rintro z ⟨y, ⟨c, hc, A, hA, rfl⟩, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨δ * D.host.φ₀ (((c : D.host.K) : D.host.E)), AddSubgroup.subset_closure ⟨c, hc, rfl⟩, A, hA, ?_⟩
    funext τ i j
    simp only [Phi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, embV, tor0,
      Matrix.smul_apply]
    rw [map_mul, FL.embT_K D τ _ (((c : D.host.K)).2)]
    ring

theorem uniformizer_element_holds : UnifElt := by
  intro D P hP
  classical
  have hP0 : P.asIdeal ≠ ⊥ := P.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 D.host.E))
  have hh : 0 < h := Fintype.card_pos
  have hm : P.asIdeal ^ h ∈ (Ideal (𝓞 D.host.E))⁰ := pow_mem (mem_nonZeroDivisors_of_ne_zero hP0) h
  have hprin : (P.asIdeal ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hm]
    have : ClassGroup.mk0 (⟨P.asIdeal ^ h, hm⟩ : (Ideal (𝓞 D.host.E))⁰) =
        ClassGroup.mk0 ⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero hP0⟩ ^ h := by
      rw [← map_pow, SubmonoidClass.mk_pow]
    rw [this, pow_card_eq_one]
  obtain ⟨π, hπ⟩ := hprin
  have hspan : Ideal.span {π} = P.asIdeal ^ h := hπ.symm
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hspan
    exact pow_ne_zero h hP0 hspan.symm
  have hπP : π ∈ P.asIdeal := by
    have : π ∈ P.asIdeal ^ h := by rw [← hspan]; exact Ideal.mem_span_singleton_self π
    exact Ideal.pow_le_self hh.ne' this
  have hprime : ∀ Q : Ideal (𝓞 D.host.E), Q.IsPrime → π ∈ Q → P.asIdeal = Q := by
    intro Q hQ hπQ
    have : P.asIdeal ^ h ≤ Q := by rw [← hspan, Ideal.span_le]; simpa using hπQ
    exact P.isMaximal.eq_of_le hQ.ne_top (hQ.le_of_pow_le this)
  refine ⟨π, hπ0, hπP, fun s hs => ?_, ?_⟩
  · rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : π ∈ Q := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self π))
    have h2 : s ∈ Q := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self s))
    rw [← hprime Q hQ.isPrime h1] at h2
    exact hs h2
  · intro hc
    obtain ⟨a, b, hab, haP, hbP⟩ := hP
    have hQ : (P.asIdeal.comap (cO D)).IsPrime := Ideal.IsPrime.comap _
    have heq := hprime _ hQ (Ideal.mem_comap.2 hc)
    have ha' : a ∈ P.asIdeal.comap (cO D) := heq ▸ haP
    rw [Ideal.mem_comap] at ha'
    apply hbP
    have hb : b = cO D a := Subtype.ext (hab.trans rfl)
    rw [hb]; exact ha'

theorem ccE_ne_bot (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) : ccE D cc ≠ ⊥ := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc.1
  intro h
  have := kE_mem D cc c hc
  rw [h, Ideal.mem_bot] at this
  apply hc0
  have h2 : ((c : D.host.K) : D.host.E) = 0 := congrArg Subtype.val this
  have h3 : (c : D.host.K) = 0 := by exact_mod_cast h2
  exact_mod_cast h3

theorem central_character_local_holds : CcLoc := by
  intro D cc hcc P
  classical
  have hI : ccE D cc ≠ ⊥ := ccE_ne_bot D cc hcc
  have hlt : ccE D cc * P.asIdeal < ccE D cc := by
    refine lt_of_le_of_ne Ideal.mul_le_left fun h => ?_
    have : ccE D cc * P.asIdeal = ccE D cc * ⊤ := by rw [h, Ideal.mul_top]
    exact P.isPrime.ne_top (mul_left_cancel₀ hI this)
  obtain ⟨γ, hγI, hγP⟩ := SetLike.exists_of_lt hlt
  have hγ0 : γ ≠ 0 := by rintro rfl; exact hγP (Submodule.zero_mem _)
  obtain ⟨J, hJ⟩ : ccE D cc ∣ Ideal.span {γ} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hγI)
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hJ'
    apply hγP
    have : Ideal.span {γ} ≤ ccE D cc * P.asIdeal := by rw [hJ]; exact Ideal.mul_mono_right hJ'
    exact this (Ideal.mem_span_singleton_self γ)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.1 hJP
  refine ⟨γ, hγ0, hγI, t, htP, fun c hc => ?_⟩
  have : t * c ∈ Ideal.span {γ} := by rw [hJ, mul_comm t c]; exact Ideal.mul_mem_mul hc htJ
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨o, by rw [← ho, mul_comm]⟩

theorem mem_homL (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E) :
    A ∈ homL D L L' ↔ ∀ x ∈ L, A.mulVec x ∈ L' := by
  constructor
  · intro hA
    induction hA using Submodule.span_induction with
    | mem A hA => exact hA
    | zero => intro x _; rw [Matrix.zero_mulVec]; exact L'.zero_mem
    | add A B _ _ h1 h2 => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (h1 x hx) (h2 x hx)
    | smul c A _ h1 => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem c (h1 x hx)
  · intro h; exact Submodule.subset_span h

theorem pairing_bound_holds : YYBound := by
  intro D w N N' L L₀ L' L₀' hL hL' y hy
  have hhom : ∀ A ∈ homL D L₀ L₀', (w * w) • A ∈ homL D L L' := by
    intro A hA
    rw [mem_homL] at hA ⊢
    intro x hx
    have : ((w * w) • A).mulVec x = w • (A.mulVec (w • x)) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, mul_smul]
    rw [this]; exact hL' _ (hA _ (hL x hx))
  induction hy using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    apply Submodule.subset_span
    exact ⟨a, ha, (w * w) • A, hhom A hA, smul_comm _ _ _⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
  | smul c B _ h1 => rw [smul_comm]; exact Submodule.smul_mem _ c h1

theorem mem_sLat (D : D7) {N : ℕ} (u : D.host.E) (hu : u ≠ 0) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (x : Fin N → D.host.E) : x ∈ sLat D u L ↔ u⁻¹ • x ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
    rwa [smul_smul, inv_mul_cancel₀ hu, one_smul]
  · intro h
    refine ⟨u⁻¹ • x, h, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
    rw [smul_smul, mul_inv_cancel₀ hu, one_smul]

theorem unipotent_pairing_holds : UYY := by
  intro D N N' L₀ L₀' u hu
  have hhom : ∀ A, A ∈ homL D L₀ (sLat D u L₀') ↔ u⁻¹ • A ∈ homL D L₀ L₀' := by
    intro A
    rw [mem_homL, mem_homL]
    refine forall₂_congr fun x _ => ?_
    rw [mem_sLat D u hu, Matrix.smul_mulVec]
  rw [sMod, YYl, YYl, Submodule.map_span]
  congr 1
  ext B
  simp only [Set.mem_ofPred_eq, Set.mem_image, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨a, ha, A, hA, rfl⟩
    refine ⟨a • (u⁻¹ • A), ⟨a, ha, u⁻¹ • A, (hhom A).1 hA, rfl⟩, ?_⟩
    rw [smul_comm u a, smul_smul u u⁻¹, mul_inv_cancel₀ hu, one_smul]
  · rintro ⟨_, ⟨a, ha, A, hA, rfl⟩, rfl⟩
    refine ⟨a, ha, u • A, (hhom _).2 (by rwa [smul_smul, inv_mul_cancel₀ hu, one_smul]), smul_comm _ _ _⟩

theorem admissible_unipotent_holds : UAdm := by
  intro D N N' L₀ L₀' u hu h
  let _ := D.host.cmStar
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hstar : star u = u⁻¹ := by
    rw [CU.star_conj D u]; exact eq_inv_of_mul_eq_one_right hu
  obtain ⟨h1, h2, h3, ⟨hfg, hspan, hsd⟩⟩ := h
  refine ⟨h1, h2, h3, hfg.map _, ?_, ?_⟩
  · have : ((sLat D u L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Set (Fin N' → D.host.E)) =
        (LinearMap.lsmul D.host.E (Fin N' → D.host.E) u) '' (L₀' : Set (Fin N' → D.host.E)) := by
      simp [sLat]
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨u⁻¹ • z, by simp [smul_smul, inv_mul_cancel₀ hu0]⟩
  · intro y
    rw [mem_sLat D u hu0, hsd]
    constructor
    · intro hy x' hx'
      rw [mem_sLat D u hu0] at hx'
      have := hy _ hx'
      convert this using 1
      simp only [Formalism.BasicNotions.stdH, Pi.smul_apply, smul_eq_mul, star_mul', star_inv₀, hstar, inv_inv]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    · intro hy x hx
      have := hy (u • x) ((mem_sLat D u hu0 L₀' _).2 (by rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul]))
      convert this using 1
      simp only [Formalism.BasicNotions.stdH, Pi.smul_apply, smul_eq_mul, star_mul', hstar]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp

end Formalism.L2.PairingIndexBounds.Rec
