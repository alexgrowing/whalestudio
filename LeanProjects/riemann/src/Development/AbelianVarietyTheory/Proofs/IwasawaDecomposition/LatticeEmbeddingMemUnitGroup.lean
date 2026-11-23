import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordMapBasisFun

noncomputable section

open Formalism.BasicNotions NumberField Matrix
open scoped ComplexOrder

namespace GlobalTheory.Mem.DivInhab

section Semilinear

variable {K V M ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module ℂ M] [Fintype ι]
  {σ : K →+* ℂ} (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V)

theorem map_eq_sum (x : V) : e x = ∑ i, σ (b.repr x i) • e (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => LinearMap.map_smulₛₗ e _ _)

theorem exists_extension (h : LinearIndependent ℂ (fun i => e (b i))) {N : Type} [AddCommGroup N] [Module ℂ N]
    (g : V →ₛₗ[σ] N) : ∃ F : M →ₗ[ℂ] N, ∀ x, F (e x) = g x := by
  obtain ⟨F, hF⟩ := LinearMap.exists_extend ((Finsupp.linearCombination ℂ (fun i => g (b i))).comp h.repr)
  have hb : ∀ i, F (e (b i)) = g (b i) := by
    intro i
    have h1 := LinearMap.congr_fun hF ⟨e (b i), Submodule.subset_span ⟨i, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1, h.repr_eq_single i _ rfl]
    simp
  refine ⟨F, fun x => ?_⟩
  rw [map_eq_sum e b, map_eq_sum g b, map_sum]
  simp [hb]

theorem linearIndependent_map (h : LinearIndependent ℂ (fun i => e (b i))) {κ : Type} [Fintype κ] {z : κ → V}
    (hz : LinearIndependent K z) : LinearIndependent ℂ (fun j => e (z j)) := by
  classical
  obtain ⟨f, hf⟩ := LinearMap.exists_extend hz.repr
  have hfz : ∀ j, f (z j) = Finsupp.single j 1 := by
    intro j
    have h1 := LinearMap.congr_fun hf ⟨z j, Submodule.subset_span ⟨j, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1, hz.repr_eq_single j _ rfl]
  let g : V →ₛₗ[σ] (κ → ℂ) :=
    { toFun := fun x j => σ (f x j)
      map_add' := fun x y => by funext j; simp
      map_smul' := fun a x => by funext j; simp }
  obtain ⟨F, hF⟩ := exists_extension e b h g
  refine LinearIndependent.of_comp F ?_
  have : (F ∘ fun j => e (z j)) = Pi.basisFun ℂ κ := by
    funext j k
    simp only [Function.comp, hF, g, LinearMap.coe_mk, AddHom.coe_mk, hfz, Pi.basisFun_apply]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [Ne.symm hjk]
  rw [this]
  exact (Pi.basisFun ℂ κ).linearIndependent

theorem mem_span_ker (h : LinearIndependent ℂ (fun i => e (b i))) {S : Type} [Fintype S] (T : S → M →ₗ[ℂ] M)
    (hT : ∀ v x, ∃ y, e y = T v (e x)) {φ : M} (hφ : φ ∈ Submodule.span ℂ (Set.range fun i => e (b i)))
    (h0 : ∀ v, T v φ = 0) : φ ∈ Submodule.span ℂ (e '' {x | ∀ v, T v (e x) = 0}) := by
  classical
  have hinj := inj_of_li σ e b h
  let N : S → V →ₗ[K] V := fun v => descend e e hinj (T v) (hT v)
  have hN : ∀ v x, e (N v x) = T v (e x) := fun v x => descend_spec e e hinj (T v) (hT v) x
  let N' : V →ₗ[K] (S → V) := LinearMap.pi N
  obtain ⟨r, hr⟩ := N'.rangeRestrict.exists_rightInverse_of_surjective N'.range_rangeRestrict
  obtain ⟨s, hs⟩ := LinearMap.exists_extend r
  have hsN : ∀ x, N' (s (N' x)) = N' x := by
    intro x
    have h1 := LinearMap.congr_fun hs ⟨N' x, ⟨x, rfl⟩⟩
    have h2 := congrArg Subtype.val (LinearMap.congr_fun hr ⟨N' x, ⟨x, rfl⟩⟩)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    exact h2
  let p : V →ₗ[K] V := LinearMap.id - s ∘ₗ N'
  have hp : ∀ x v, T v (e (p x)) = 0 := by
    intro x v
    have h1 : N' (p x) = 0 := by simp [p, hsN]
    have h2 : N v (p x) = 0 := congrFun h1 v
    rw [← hN, h2, map_zero]
  obtain ⟨P, hP⟩ := exists_extension e b h (e.comp p)
  choose Sx hSx using fun v => exists_extension e b h (e.comp (s ∘ₗ LinearMap.single K (fun _ : S => V) v))
  have key : ∀ ψ ∈ Submodule.span ℂ (Set.range fun i => e (b i)),
      ψ = P ψ + ∑ v, Sx v (T v ψ) ∧ P ψ ∈ Submodule.span ℂ (e '' {x | ∀ v, T v (e x) = 0}) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨i, rfl⟩ := hψ
      refine ⟨?_, ?_⟩
      · simp only [← hN, hSx, hP, LinearMap.comp_apply]
        rw [← map_sum e, ← map_sum s, ← map_add]
        congr 1
        have : ∑ v, LinearMap.single K (fun _ : S => V) v (N v (b i)) = N' (b i) := by
          funext w; simp [N', Finset.sum_apply, Pi.single_apply]
        rw [this]; simp [p]
      · rw [hP]; exact Submodule.subset_span ⟨p (b i), hp _, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, by rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩
      simp only [map_add, Finset.sum_add_distrib]
      conv_lhs => rw [hx.1, hy.1]
      abel
    | smul a x _ hx =>
      refine ⟨?_, by rw [map_smul]; exact Submodule.smul_mem _ _ hx.2⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, ← smul_add, ← hx.1]
  obtain ⟨h1, h2⟩ := key φ hφ
  rw [h1]
  simpa [h0] using h2

end Semilinear

section Frames

open scoped MatrixOrder in
theorem exists_frame {κ : Type} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ) (hA : A.PosDef) :
    ∃ Y : Matrix κ κ ℂ, IsUnit Y.det ∧ (Y⁻¹)ᴴ * Y⁻¹ = A := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hB' : A = Bᴴ * B := by rw [hB, Matrix.star_eq_conjTranspose]
  have hdet : IsUnit B.det := by
    have h1 : A.det ≠ 0 := hA.det_pos.ne'
    rw [hB', Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hdet, hB']

theorem cnorm_mulVec {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) (y : κ → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M *ᵥ y) = Real.sqrt (star y ⬝ᵥ ((Mᴴ * M) *ᵥ y)).re := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

def vecMap (b : Module.Basis ι K V) (v : InfinitePlace K) : V →ₛₗ[v.embedding] (ι → ℂ) where
  toFun := Formalism.HermitianLatticesTheory.vecAt b v
  map_add' x y := by funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  map_smul' a x := by funext i; simp [Formalism.HermitianLatticesTheory.vecAt]

theorem exists_frames_restrict (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (U : Submodule K V) {κ : Type} [Fintype κ] [DecidableEq κ]
    (c : Module.Basis κ K U) : ∃ Y : InfinitePlace K → Matrix κ κ ℂ, (∀ v, IsUnit (Y v).det) ∧
      ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt c Y v x = Formalism.HermitianLatticesTheory.normAt b X v (x : V) := by
  let E : InfinitePlace K → Matrix ι κ ℂ := fun v => Matrix.of fun i j => vecMap b v (c j : V) i
  have hE : ∀ v, Function.Injective (E v).mulVec := by
    intro v
    rw [Matrix.mulVec_injective_iff]
    refine linearIndependent_map (vecMap b v) b ?_ (c.linearIndependent.map' U.subtype U.ker_subtype)
    have : (fun i => vecMap b v (b i)) = Pi.basisFun ℂ ι := by
      funext i k
      show v.embedding (b.repr (b i) k) = _
      by_cases hik : i = k
      · subst hik; simp
      · simp [Ne.symm hik]
    rw [this]
    exact (Pi.basisFun ℂ ι).linearIndependent
  have hM : ∀ v, Function.Injective ((X v)⁻¹ * E v).mulVec := by
    intro v y y' hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hy
    exact hE v (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ (hX v))) hy)
  choose Y hY1 hY2 using fun v => exists_frame _ (Matrix.PosDef.conjTranspose_mul_self _ (hM v))
  refine ⟨Y, hY1, fun v x => ?_⟩
  have hx : Formalism.HermitianLatticesTheory.vecAt b v (x : V) = E v *ᵥ Formalism.HermitianLatticesTheory.vecAt c v x := by
    have := map_eq_sum ((vecMap b v).comp U.subtype) c x
    funext i
    have h2 := congrFun this i
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    refine h2.trans (Finset.sum_congr rfl fun j _ => ?_)
    exact mul_comm _ _
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  rw [hx, Matrix.mulVec_mulVec, cnorm_mulVec, cnorm_mulVec, hY2]

end Frames

section Sub

variable {K : Type} [Field K] [NumberField K] [StarRing K]

@[reducible] def subHLat (A : HLat K) (U : Submodule K A.V) {d : ℕ} (c : Module.Basis (Fin d) K U)
    (Y : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) : HLat K where
  V := U
  ι := Fin d
  b := c
  X := Y
  L := A.L.comap (U.subtype.restrictScalars (𝓞 K))

theorem subHLat_map (A : HLat K) (U : Submodule K A.V) {d : ℕ} (c : Module.Basis (Fin d) K U)
    (Y : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) :
    (subHLat A U c Y).L.map (U.subtype.restrictScalars (𝓞 K)) = A.L ⊓ U.restrictScalars (𝓞 K) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h2⟩, h1, rfl⟩

theorem subHLat_good (A : HLat K) (hA : A.Good) (U : Submodule K A.V) {d : ℕ} (c : Module.Basis (Fin d) K U)
    (Y : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hY : ∀ v, IsUnit (Y v).det) : (subHLat A U c Y).Good := by
  refine ⟨hY, ?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    rw [subHLat_map]
    exact hA.2.1.of_le inf_le_left
  · rw [eq_top_iff]
    rintro x -
    have hx : (x : A.V) ∈ Submodule.span K (A.L : Set A.V) := by rw [hA.2.2]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx
    rw [Submodule.span_eq] at ht
    have ht0 : ((t : 𝓞 K) : K) ≠ 0 := by
      have := nonZeroDivisors.coe_ne_zero t
      exact_mod_cast this
    have h1 : ((t : 𝓞 K) : K) • x ∈ Submodule.span K ((subHLat A U c Y).L : Set U) := by
      refine Submodule.subset_span ?_
      show ((t : 𝓞 K) : K) • (x : A.V) ∈ A.L
      have : ((t : 𝓞 K) : K) • (x : A.V) = (t : 𝓞 K) • (x : A.V) := algebraMap_smul K (t : 𝓞 K) (x : A.V)
      rw [this]; exact ht
    exact (Submodule.smul_mem_iff _ ht0).1 h1

theorem stdHLat_good (n : ℕ) :
    (ProvRowSide.stdHLat K n (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))))).Good := by
  refine ⟨ProvRowSide.stdHLat_frames _ _ _, Submodule.fg_span (Set.finite_range _), ?_⟩
  show Submodule.span K (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) : Set (Fin n → K)) = ⊤
  rw [Submodule.span_span_of_tower, Module.Basis.span_eq]

end Sub

section Ram

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

theorem rhoT_rat (v : A.vT) (a : (A.Fv v)ˣ) (x : (M.lat 0).V) : ∃ y, M.emb 0 y = A.rhoT v a (M.emb 0 x) := by
  have hx : x ∈ Submodule.span LL ((M.lat 0).L : Set (M.lat 0).V) := by rw [(M.lat_good 0).2.2]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨y, -, hy⟩ := M.rhoT_lat v a x hx; exact ⟨y, hy⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by simp [hx', hy']⟩
  | smul c x _ hx =>
    obtain ⟨x', hx'⟩ := hx
    exact ⟨c • x', by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, hx']⟩

theorem Nm_rat (v : A.vT) (x : (M.lat 0).V) : ∃ y, M.emb 0 y = A.Nm v (M.emb 0 x) := by
  choose y hy using fun a => rhoT_rat M v a x
  exact ⟨∑ a, y a, by simp [ColumnsAtT.Nm, hy]⟩

theorem lattice_embedding_mem_unit_group (x : (M.lat 0).V) : M.emb 0 x ∈ A.Mu0 := by
  rw [← M.Fi_zero, ← (M.emb_basis 0).2, map_eq_sum (M.emb 0) (M.lat 0).b]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def ramEmb : M.ramSub →ₛₗ[embLL] A.Mram :=
  LinearMap.codRestrict A.Mram ((M.emb 0).comp M.ramSub.subtype) fun x => x.2

theorem ramEmb_basis {κ : Type} [Fintype κ] (c : Module.Basis κ LL M.ramSub) :
    LinearIndependent ℂ (fun i => ramEmb M (c i)) ∧ Submodule.span ℂ (Set.range fun i => ramEmb M (c i)) = ⊤ := by
  refine ⟨LinearIndependent.of_comp A.Mram.subtype ?_, ?_⟩
  · exact linearIndependent_map (M.emb 0) (M.lat 0).b (M.emb_basis 0).1
      (c.linearIndependent.map' M.ramSub.subtype M.ramSub.ker_subtype)
  · apply Submodule.map_injective_of_injective A.Mram.injective_subtype
    rw [Submodule.map_subtype_top]
    refine le_antisymm (Submodule.map_subtype_le _ _) fun φ hφ => ?_
    have h1 : φ ∈ Submodule.span ℂ (Set.range fun i => M.emb 0 ((M.lat 0).b i)) := by
      rw [(M.emb_basis 0).2, M.Fi_zero]; exact hφ.1
    have h2 := mem_span_ker (M.emb 0) (M.lat 0).b (M.emb_basis 0).1 A.Nm (Nm_rat M) h1
      (fun v => (Submodule.mem_iInf _).1 hφ.2 v)
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ M.ramSub := ⟨lattice_embedding_mem_unit_group M x, (Submodule.mem_iInf _).2 hx⟩
    refine ⟨ramEmb M ⟨x, hx'⟩, ?_, rfl⟩
    rw [map_eq_sum (ramEmb M) c]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Ram

theorem exists_divStage : ∀ (B : GlobalTheory.Mem.Base) (C : GlobalTheory.Mem.Cols B) (W : GlobalTheory.Mem.RowsRest B C),
    ∃ X : GlobalTheory.Mem.DivStage B C W, X.div.AllGood ∧
      ∀ u, (X.div.Nu u).L.map ((X.nuIn u).restrictScalars (𝓞 B.LL)) = (C.fm u).ramL := by
  intro B C W
  have hfin : ∀ u, Module.Finite B.LL (C.fm u).ramSub := fun u =>
    have := Module.Finite.of_basis ((C.fm u).lat 0).b
    inferInstance
  let c := fun u => Module.finBasis B.LL (C.fm u).ramSub
  choose Y hY1 hY2 using fun u => exists_frames_restrict ((C.fm u).lat 0).b ((C.fm u).lat 0).X
    ((C.fm u).lat_good 0).1 (C.fm u).ramSub (c u)
  let RR : HLat B.LL :=
    ProvRowSide.stdHLat B.LL W.Drows (Submodule.span (𝓞 B.LL) (Set.range (Pi.basisFun B.LL (Fin W.Drows))))
  let Nu : B.Word → HLat B.LL := fun u => subHLat ((C.fm u).lat 0) (C.fm u).ramSub (c u) (Y u)
  let D : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := fun _ => 0, h := fun _ => 0, HH := sFrame Nu (fun _ => 0) + RR.muMax
      HH_ge := le_rfl, etaF := 0, Dall := W.Dall, delP := W.delp, delP_le_one := W.delp_le_one }
  have hb : (fun i : Fin W.Drows => ProvRowSide.coordMap B.embLL W.onb (Pi.basisFun B.LL (Fin W.Drows) i)) =
      W.onb.toBasis := by
    funext i; rw [ProvRowSide.coordMap_basisFun]; simp
  refine ⟨{ div := D
            div_good := ⟨ProvRowSide.stdHLat_frames _ _ _, hY1⟩
            jEE := ProvRowSide.coordMap B.embLL W.onb
            jEE_basis := ⟨?_, ?_⟩
            jN := fun u => (W.eMu u).symm.toLinearMap.comp (ramEmb (C.fm u))
            jN_basis := fun u => ⟨?_, ?_⟩
            Dall_eq := rfl
            delP_eq := rfl
            nuIn := fun u => (C.fm u).ramSub.subtype
            nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
            nuIn_range := fun u => (C.fm u).ramSub.range_subtype
            nuIn_jN := fun u x => congrArg Subtype.val ((W.eMu u).apply_symm_apply (ramEmb (C.fm u) x))
            nuIn_norm := hY2
            jEE_norm := fun x => ProvRowSide.normAt_one B.embLL W.onb x },
    ⟨stdHLat_good _, fun u => subHLat_good _ ((C.fm u).lat_good 0) _ _ _ (hY1 u)⟩,
    fun u => subHLat_map _ _ _ _⟩
  · show LinearIndependent ℂ
      (fun i : Fin W.Drows => ProvRowSide.coordMap B.embLL W.onb (Pi.basisFun B.LL (Fin W.Drows) i))
    rw [hb]; exact W.onb.toBasis.linearIndependent
  · show Submodule.span ℂ (Set.range
      (fun i : Fin W.Drows => ProvRowSide.coordMap B.embLL W.onb (Pi.basisFun B.LL (Fin W.Drows) i))) = ⊤
    rw [hb]; exact W.onb.toBasis.span_eq
  · exact (ramEmb_basis (C.fm u) (c u)).1.map' (W.eMu u).symm.toLinearMap (W.eMu u).symm.ker
  · show Submodule.span ℂ (Set.range ((W.eMu u).symm.toLinearMap ∘ fun i => ramEmb (C.fm u) (c u i))) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (ramEmb_basis (C.fm u) (c u)).2, Submodule.map_top,
      LinearEquiv.range]

end GlobalTheory.Mem.DivInhab

end
