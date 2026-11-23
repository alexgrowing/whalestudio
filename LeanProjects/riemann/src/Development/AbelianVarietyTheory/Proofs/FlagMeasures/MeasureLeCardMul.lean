import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology

open MeasureTheory Formalism.MainNotions.S NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongIndex

theorem measure_le_card_mul {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [Finite Q] (K H : Set G) (q : K → Q)
    (hq : ∀ x y : K, q x = q y → (y : G)⁻¹ * x ∈ H) : μ K ≤ (Nat.card Q : ENNReal) * μ H := by
  classical
  haveI := Fintype.ofFinite Q
  have h1 : K ⊆ ⋃ c : Q, Subtype.val '' (q ⁻¹' {c}) := fun x hx =>
    Set.mem_iUnion.2 ⟨q ⟨x, hx⟩, ⟨x, hx⟩, rfl, rfl⟩
  have h2 : ∀ c : Q, μ (Subtype.val '' (q ⁻¹' {c})) ≤ μ H := by
    intro c
    by_cases h : ∃ y, q y = c
    · obtain ⟨y, rfl⟩ := h
      rw [← measure_preimage_mul μ (y : G)⁻¹ H]
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hq x y hx
    · have : q ⁻¹' {c} = ∅ := Set.eq_empty_of_forall_notMem fun y hy => h ⟨y, hy⟩
      simp [this]
  calc μ K ≤ ∑ c : Q, μ (Subtype.val '' (q ⁻¹' {c})) :=
        (measure_mono h1).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _c : Q, μ H := Finset.sum_le_sum fun c _ => h2 c
    _ = _ := by simp [Nat.card_eq_fintype_card]

section Lift

variable {O A L n : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype n] [DecidableEq n]
  [AddCommGroup L] [Module O L] (S : Subring A) (ι : L →ₗ[O] (n → A)) (a : A)

theorem exists_approx (hO : ∀ o : O, algebraMap O A o ∈ S)
    (hS : ∀ s ∈ S, ∃ o : O, ∃ w ∈ S, s = algebraMap O A o + a * w) (ha : a ∈ S)
    {y : n → A} (hy : y ∈ Submodule.span S (Set.range ι)) :
    ∃ l : L, ∃ z ∈ Submodule.span S (Set.range ι), y = ι l + a • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    exact ⟨l, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, z, hz, rfl⟩ := hx
    obtain ⟨l', z', hz', rfl⟩ := hy
    exact ⟨l + l', z + z', add_mem hz hz', by rw [map_add, smul_add]; abel⟩
  | smul s x _ hx =>
    obtain ⟨l, z, hz, rfl⟩ := hx
    obtain ⟨o, w, hw, e⟩ := hS s s.2
    refine ⟨o • l, (⟨w, hw⟩ : S) • ι l + s • z,
      add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)) (Submodule.smul_mem _ _ hz), ?_⟩
    rw [map_smul, ← algebraMap_smul A o]
    simp only [Subring.smul_def, smul_add, smul_smul]
    rw [e, add_smul, mul_comm a (_ + _), add_assoc]

theorem exists_end [Module.Projective O L] (hO : ∀ o : O, algebraMap O A o ∈ S)
    (hS : ∀ s ∈ S, ∃ o : O, ∃ w ∈ S, s = algebraMap O A o + a * w) (ha : a ∈ S)
    (x : Matrix n n A) (hx : ∀ y ∈ Submodule.span S (Set.range ι), x *ᵥ y ∈ Submodule.span S (Set.range ι)) :
    ∃ φ : L →ₗ[O] L, ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), x *ᵥ ι l = ι (φ l) + a • z := by
  let N : Submodule O (n → A) :=
    { carrier := {w | ∃ z ∈ Submodule.span S (Set.range ι), w = a • z}
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
        exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro o _ ⟨z, hz, rfl⟩
        refine ⟨(⟨_, hO o⟩ : S) • z, Submodule.smul_mem _ _ hz, ?_⟩
        rw [Subring.smul_def, smul_comm a, algebraMap_smul] }
  let f : L →ₗ[O] ((n → A) ⧸ N) := N.mkQ ∘ₗ ι
  let h : L →ₗ[O] ((n → A) ⧸ N) := N.mkQ ∘ₗ (Matrix.mulVecLin x).restrictScalars O ∘ₗ ι
  have hh : ∀ l, h l ∈ LinearMap.range f := by
    intro l
    obtain ⟨l', z, hz, e⟩ := exists_approx S ι a hO hS ha (hx _ (Submodule.subset_span ⟨l, rfl⟩))
    refine ⟨l', ((Submodule.Quotient.eq N).2 ⟨z, hz, ?_⟩).symm⟩
    exact sub_eq_of_eq_add' e
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property f.rangeRestrict (h.codRestrict _ hh)
    f.surjective_rangeRestrict
  refine ⟨φ, fun l => ?_⟩
  have e : f (φ l) = h l := congrArg Subtype.val (LinearMap.congr_fun hφ l)
  obtain ⟨z, hz, e'⟩ := (Submodule.Quotient.eq N).1 e.symm
  exact ⟨z, hz, eq_add_of_sub_eq' e'⟩

theorem congr_of_end (g : ℕ) (x y : GL n A)
    (hx : x ∈ Formalism.UG.stabGL (Submodule.span S (Set.range ι)))
    (hy : y ∈ Formalism.UG.stabGL (Submodule.span S (Set.range ι))) (φ ψ θ : L →ₗ[O] L)
    (hφ : ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), (x : Matrix n n A) *ᵥ ι l = ι (φ l) + (g : A) • z)
    (hψ : ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), (y : Matrix n n A) *ᵥ ι l = ι (ψ l) + (g : A) • z)
    (hθ : φ = ψ + g • θ) :
    y⁻¹ * x ∈ GlobalTheory.CongTop.cong (Submodule.span S (Set.range ι)) (g : A) := by
  refine ⟨mul_mem (inv_mem hy) hx, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, rfl⟩ := hv
    obtain ⟨z, hz, e⟩ := hφ l
    obtain ⟨z', hz', e'⟩ := hψ l
    refine ⟨((y⁻¹ : GL n A) : Matrix n n A) *ᵥ (ι (θ l) + z - z'),
      (inv_mem hy _).1 (sub_mem (add_mem (Submodule.subset_span ⟨_, rfl⟩) hz) hz'), ?_⟩
    have e2 : (x : Matrix n n A) *ᵥ ι l - (y : Matrix n n A) *ᵥ ι l = (g : A) • (ι (θ l) + z - z') := by
      rw [e, e', hθ, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_nsmul,
        ← Nat.cast_smul_eq_nsmul A, smul_sub, smul_add]
      abel
    rw [← Matrix.mulVec_smul, ← e2, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Units.inv_mul, Units.val_mul, Matrix.sub_mulVec]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨z, hz, e⟩ := hv
    obtain ⟨z', hz', e'⟩ := hw
    exact ⟨z + z', add_mem hz hz', by rw [Matrix.mulVec_add, e, e', smul_add]⟩
  | smul s v _ hv =>
    obtain ⟨z, hz, e⟩ := hv
    refine ⟨s • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, Matrix.mulVec_smul, e, smul_comm]

end Lift

section Rank

variable {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

theorem exists_inj (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ m ≤ n, ∃ e : (L →ₗ[𝓞 E] L) →ₗ[ℤ] (Fin m → Fin n → E), Function.Injective e := by
  obtain ⟨b, hbL, hb, hli⟩ := exists_linearIndependent E (L : Set (Fin n → E))
  haveI : Finite b := hli.finite
  haveI := Fintype.ofFinite b
  have hc : Fintype.card b ≤ n := by simpa using hli.fintype_card_le_finrank
  let u := (Fintype.equivFin b).symm
  let e : (L →ₗ[𝓞 E] L) →+ (Fin (Fintype.card b) → Fin n → E) :=
    { toFun := fun φ i => (φ ⟨u i, hbL (u i).2⟩ : L)
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  refine ⟨_, hc, e.toIntLinearMap, (injective_iff_map_eq_zero e).2 fun φ hφ => ?_⟩
  ext1 l
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E b (l : Fin n → E)
    (by rw [hb, hL]; trivial)
  have hle : Submodule.span (𝓞 E) b ≤ (LinearMap.ker φ).map L.subtype := by
    refine Submodule.span_le.2 fun w hw => ⟨⟨w, hbL hw⟩, ?_, rfl⟩
    have := congrFun hφ (u.symm ⟨w, hw⟩)
    simpa [e] using this
  obtain ⟨l', hl', e'⟩ := hle ht
  have e2 : l' = (t : 𝓞 E) • l := Subtype.ext e'
  rw [e2, SetLike.mem_coe, LinearMap.mem_ker, map_smul, smul_eq_zero] at hl'
  exact hl'.resolve_left (nonZeroDivisors.ne_zero t.2)

theorem card_end_quot (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (g : ℕ) :
    ∃ r ≤ n ^ 2 * Module.finrank ℚ E,
      (nsmulAddMonoidHom (α := L →ₗ[𝓞 E] L) g).range.index = g ^ r := by
  obtain ⟨m, hm, e, he⟩ := exists_inj L hL
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  haveI : IsNoetherian (𝓞 E) L := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian (𝓞 E) (L →ₗ[𝓞 E] L) := isNoetherian_linearMap _ _ _
  haveI : Module.Finite (𝓞 E) (L →ₗ[𝓞 E] L) := Module.IsNoetherian.finite _ _
  haveI : Module.Finite ℤ (L →ₗ[𝓞 E] L) := Module.Finite.trans (𝓞 E) _
  haveI : Module.IsTorsionFree ℤ (L →ₗ[𝓞 E] L) := he.moduleIsTorsionFree e e.map_smul
  refine ⟨_, ?_, AddSubgroup.index_range_nsmul _ g⟩
  have h1 := e.rank_le_of_injective he
  rw [← IsFractionRing.rank_right_eq ℤ ℚ (Fin m → Fin n → E), ← Module.finrank_eq_rank,
    ← Module.finrank_eq_rank, Nat.cast_le] at h1
  refine h1.trans ?_
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, sq]
  gcongr

end Rank

theorem measure_Kset_le : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] (g : ℕ), 1 ≤ g → μf I.Kset ≤ (g : ENNReal) ^ (2 * (I.n ^ 2 * I.f)) * μf (I.Kg g) ∧ 0 < μf (I.Kg g) ∧ μf I.Kset < ⊤ := by
  intro I μf _ g hg
  obtain ⟨-, -, hsc, hc, -, -, h⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨ho, ⟨H, hH⟩, -⟩ := h g hg
  refine ⟨?_, ho.measure_pos μf ⟨1, hH ▸ H.one_mem⟩, hc.measure_lt_top⟩
  haveI : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.2 I.L_fg
  haveI : Module.FinitePresentation (𝓞 I.E) I.L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 I.E) I.L := Module.Flat.projective_of_finitePresentation
  let ι : I.L →ₗ[𝓞 I.E] (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    { toFun := fun x i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => rfl }
  have hL : I.Lf = Submodule.span (IntAf I.F I.E) (Set.range ι) := rfl
  have hO : ∀ o : 𝓞 I.E, algebraMap _ (I.E ⊗[I.F] Af I.F) o ∈ IntAf I.F I.E := fun o =>
    Formalism.UG.P.levelaf_tmul_mem o (one_mem _)
  have hS : ∀ s ∈ IntAf I.F I.E, ∃ o : 𝓞 I.E, ∃ w ∈ IntAf I.F I.E,
      s = algebraMap _ (I.E ⊗[I.F] Af I.F) o + (g : I.E ⊗[I.F] Af I.F) * w := by
    intro s hs
    obtain ⟨x, hx, w, hw, e⟩ := Formalism.UG.P.csSpan_approx Formalism.UG.P.csGlob_intAdApprox (g : 𝓞 I.F)
      (Nat.cast_ne_zero.2 (by omega)) hs
    refine ⟨⟨x, hx⟩, w, hw, ?_⟩
    rw [e, ← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]
    rfl
  have key := fun x : I.Kset => exists_end (IntAf I.F I.E) ι (g : I.E ⊗[I.F] Af I.F) hO hS
    (natCast_mem _ g) (I.fmat x) fun y hy => (x.2 y).1 hy
  choose φ hφ using key
  obtain ⟨r, hr, hi⟩ := card_end_quot I.L I.L_span I.L_fg g
  set N := (nsmulAddMonoidHom (α := I.L →ₗ[𝓞 I.E] I.L) g).range
  have hi' : Nat.card ((I.L →ₗ[𝓞 I.E] I.L) ⧸ N) = g ^ r := hi
  haveI : Finite ((I.L →ₗ[𝓞 I.E] I.L) ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hi']; positivity)
  have h1 := measure_le_card_mul μf I.Kset (I.Kg g) (fun x => (QuotientAddGroup.mk (φ x) : _ ⧸ N))
    fun x y hxy => by
      obtain ⟨θ, hθ⟩ := QuotientAddGroup.eq.1 hxy.symm
      exact congr_of_end (IntAf I.F I.E) ι g _ _ x.2 y.2 (φ x) (φ y) θ (hφ x) (hφ y)
        (by rw [show g • θ = -φ y + φ x from hθ]; abel)
  refine h1.trans ?_
  rw [hi', Nat.cast_pow]
  have h2 : Module.finrank ℚ I.E = I.f * 2 := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]; rfl
  gcongr
  · exact_mod_cast hg
  · rw [h2] at hr; linarith

end GlobalTheory.CongIndex
