import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct Topology

namespace GlobalTheory.Mem.Vol.StabGroup

theorem exists_compact_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG) :
    ∃ C : Set (Fin M → Af F ⊗[F] E), IsCompact C ∧ ∀ y ∈ latHat F E (L : Set (Fin M → E)), y ∈ C := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have hZ : (L.restrictScalars ℤ).FG := hL.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  let g : (Fin m → Af F) → Fin M → Af F ⊗[F] E := fun c i => ∑ k, c k ⊗ₜ[F] x k i
  have hg : Continuous g := by
    refine continuous_pi fun i => continuous_finset_sum _ fun k _ => ?_
    have : (fun c : Fin m → Af F => c k ⊗ₜ[F] x k i) = fun c => c k • ((1 : Af F) ⊗ₜ[F] x k i) := by
      funext c
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    have hk : Continuous fun c : Fin m → Af F => c k := continuous_apply k
    have ho : Continuous fun _ : Fin m → Af F => (1 : Af F) ⊗ₜ[F] x k i := continuous_const
    exact hk.smul ho
  have hI : IsCompact (intAf F) := GlobalTheory.AdeleCocompact.isCompact_integral F
  refine ⟨g '' Set.pi Set.univ fun _ => intAf F, (isCompact_univ_pi fun _ => hI).image hg, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    have hv' : v ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hv
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv'
    refine ⟨fun k => n k • a, fun k _ w => ?_, ?_⟩
    · rw [map_zsmul]
      exact zsmul_mem (ha w) _
    · funext i
      simp only [g, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero =>
    refine ⟨0, fun k _ w => ?_, ?_⟩
    · rw [Pi.zero_apply, map_zero]
      exact zero_mem _
    · funext i
      simp [g]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    refine ⟨c + d, fun k _ w => ?_, ?_⟩
    · rw [Pi.add_apply, map_add]
      exact add_mem (hc k trivial w) (hd k trivial w)
    · funext i
      simp only [g, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨-c, fun k _ w => ?_, ?_⟩
    · rw [Pi.neg_apply, map_neg]
      exact neg_mem (hc k trivial w)
    · funext i
      simp only [g, Pi.neg_apply, TensorProduct.neg_tmul, Finset.sum_neg_distrib]

theorem exists_compact_entries (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) :
    ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧ ∀ A : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (∀ y ∈ latHat F E (L : Set (Fin M → E)), A.mulVec y ∈ latHat F E (L : Set (Fin M → E))) →
      ∀ i j, A i j ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨C, hC, hLC⟩ := exists_compact_latHat F E L hL
  choose d hd hdL using fun j => GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  refine ⟨⋃ p : Fin M × Fin M, (fun y : Fin M → Af F ⊗[F] E =>
      y p.1 * ((1 : Af F) ⊗ₜ[F] ((d p.2 : E)⁻¹))) '' C,
    isCompact_iUnion fun p => hC.image ((continuous_apply p.1).mul continuous_const), fun A hA i j => ?_⟩
  have h1 : (1 : Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hy : (fun k => (1 : Af F) ⊗ₜ[F] (d j • (Pi.single j 1 : Fin M → E)) k) ∈
      latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL j, rfl⟩
  refine Set.mem_iUnion.2 ⟨(i, j), _, hLC _ (hA _ hy), ?_⟩
  have hd0 : (d j : E) ≠ 0 := Nat.cast_ne_zero.2 (hd j).ne'
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem congr_mem_nhds (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (N : ℕ) (hN : 0 < N) :
    {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) | ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho : IsOpen {z : Fin n → Af F ⊗[F] E | ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), z = N • y} :=
    (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E n L hL).1 N hN
  have hfz : (L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
    have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    exact (Module.Finite.iff_fg (N := L.restrictScalars ℤ)).mp (inferInstanceAs (Module.Finite ℤ L))
  obtain ⟨s, hs⟩ := hfz
  have hev : ∀ᶠ m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) in 𝓝 1, ∀ x ∈ s,
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    rw [Filter.eventually_all_finset]
    intro x _
    have hc : Continuous fun m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) =>
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x :=
      (continuous_id.matrix_mulVec continuous_const).sub continuous_const
    exact (ho.preimage hc).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hev fun m hm => ?_
  have hsm : ∀ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) →
      ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), a • y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
    intro a ha y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨a * b, fun v => mul_mem (ha v) (hb v), x, hx, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have hadd : ∀ z w : Fin n → Af F ⊗[F] E,
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y) →
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec w - w = N • y) →
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec (z + w) - (z + w) = N • y := by
    rintro z w ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', add_mem hy hy', by rw [smul_add, ← h, ← h', Matrix.mulVec_add]; abel⟩
  have hx : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hm x hx
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := funext fun i => TensorProduct.tmul_zero _ _
      exact ⟨0, zero_mem _, by simp [this]⟩
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y :=
        funext fun i => TensorProduct.tmul_add _ _ _
      rw [this]; exact hadd _ _ hx hy
    | smul c x _ hx =>
      obtain ⟨y, hy, h⟩ := hx
      have : GlobalTheory.AdLat.fv F (c • x) = c • GlobalTheory.AdLat.fv F x :=
        funext fun i => map_zsmul (TensorProduct.mk F (Af F) E 1) c (x i)
      refine ⟨c • y, zsmul_mem hy c, ?_⟩
      rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hxL, rfl⟩ := hz
    obtain ⟨y, hy, h⟩ := hx x (by rw [hs]; exact hxL)
    have : (fun i => a ⊗ₜ[F] x i) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp [GlobalTheory.AdLat.fv, TensorProduct.smul_tmul']
    refine ⟨a • y, hsm a ha y hy, ?_⟩
    rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add z w _ _ hz hw => exact hadd z w hz hw
  | neg z _ hz =>
    obtain ⟨y, hy, h⟩ := hz
    exact ⟨-y, neg_mem hy, by rw [smul_neg, ← h, Matrix.mulVec_neg]; abel⟩

noncomputable def stabGrp (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) :
    Subgroup (HA (Af F) σ J) where
  carrier := {h | StabHat F L (HA.mat (Af F) σ J h).1}
  one_mem' := fun y => by
    change _ ↔ (1 : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec y ∈ _
    rw [Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    change _ ↔ ((HA.mat (Af F) σ J a).1 * (HA.mat (Af F) σ J b).1).mulVec y ∈ _
    rw [← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    change _ ↔ ((HA.mat (Af F) σ J a)⁻¹).1.mulVec y ∈ _
    rw [ha (((HA.mat (Af F) σ J a)⁻¹).1.mulVec y), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]

theorem exists_compact_open_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∃ K : Subgroup (HA (Af F) σ J), (∀ h, h ∈ K ↔ StabHat F (L : Set (Fin M → E)) ((HA.mat (Af F) σ J h : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))) ∧ IsOpen (K : Set (HA (Af F) σ J)) ∧ IsCompact (K : Set (HA (Af F) σ J)) := by
  intro F E _ _ _ _ _ σ M J L hfg hsp
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : T2Space (Af F ⊗[F] E) := e.isEmbedding.t2Space
  haveI : IsTopologicalGroup (HA (Af F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))
  have hcl : IsClosed (HR (Af F) σ J : Set (GL (Fin M) (Af F ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (Af F ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  have hc : Continuous fun h : HA (Af F) σ J => (HA.mat (Af F) σ J h).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hopen : IsOpen (stabGrp F σ J (L : Set (Fin M → E)) : Set (HA (Af F) σ J)) := by
    have hn := congr_mem_nhds F E M L hfg hsp 1 one_pos
    have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds hn
    have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
      (by rw [Function.comp_apply, inv_one]; exact hn)
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro k ⟨hk1, hk2⟩ y
    constructor
    · intro hy
      obtain ⟨w, hw, h⟩ := hk1 y hy
      rw [eq_add_of_sub_eq h]
      exact add_mem (nsmul_mem hw 1) hy
    · intro hy
      obtain ⟨w, hw, h⟩ := hk2 _ hy
      have hk : (HA.mat (Af F) σ J k⁻¹).1 * (HA.mat (Af F) σ J k).1 = 1 :=
        (HA.mat (Af F) σ J k).inv_mul
      rw [Function.comp_apply, Matrix.mulVec_mulVec, hk, Matrix.one_mulVec] at h
      rw [eq_add_of_sub_eq h]
      exact add_mem (nsmul_mem hw 1) hy
  refine ⟨stabGrp F σ J (L : Set (Fin M → E)), fun h => Iff.rfl, hopen, ?_⟩
  obtain ⟨C, hC, hCe⟩ := exists_compact_entries F E L hfg hsp
  let S : Set (Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (Af F ⊗[F] E))).comp
    hcl.isClosedEmbedding_subtypeVal
  have hK : IsCompact (X := HA (Af F) σ J) _ :=
    hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) fun h hh => ?_
  have hi := (stabGrp F σ J (L : Set (Fin M → E))).inv_mem hh
  exact ⟨fun i _ j _ => hCe _ (fun y hy => (hh y).1 hy) i j,
    (HA.mat (Af F) σ J h⁻¹).1, fun i _ j _ => hCe _ (fun y hy => (hi y).1 hy) i j, rfl⟩

end GlobalTheory.Mem.Vol.StabGroup
