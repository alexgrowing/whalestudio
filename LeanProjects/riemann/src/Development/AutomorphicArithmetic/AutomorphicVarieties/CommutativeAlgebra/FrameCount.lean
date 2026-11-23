import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KrullDimQuotientComapEq

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

noncomputable section

namespace UpperTheory.V.Alg.FrameCount

open ReciprocityTheory.Gal

private theorem rank_range {k P A B : Type} [Field k] [AddCommGroup P] [Module k P] [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [Module.Finite k A] (π : P →ₗ[k] A) (hπ : Function.Surjective π)
    (δ : P →ₗ[k] B) (S : Submodule k A) (h : LinearMap.ker δ = S.comap π) :
    Module.Finite k (LinearMap.range δ) ∧
      Module.finrank k (LinearMap.range δ) + Module.finrank k S = Module.finrank k A := by
  have h' : LinearMap.ker δ = LinearMap.ker (S.mkQ.comp π) := by
    rw [h, LinearMap.ker_comp, Submodule.ker_mkQ]
  have e : LinearMap.range δ ≃ₗ[k] (A ⧸ S) :=
    (LinearMap.quotKerEquivRange δ).symm.trans ((Submodule.quotEquivOfEq _ _ h').trans
      (LinearMap.quotKerEquivOfSurjective _ (S.mkQ_surjective.comp hπ)))
  exact ⟨Module.Finite.equiv e.symm, by rw [e.finrank_eq, Submodule.finrank_quotient_add_finrank]⟩

private theorem finrank_prod_pi (k : Type) [Field k] {T Q : Type} [Fintype T] [Fintype Q] (A : T → Type) (B : Q → Type)
    [∀ v, AddCommGroup (A v)] [∀ v, Module k (A v)] [∀ v, Module.Finite k (A v)]
    [∀ q, AddCommGroup (B q)] [∀ q, Module k (B q)] [∀ q, Module.Finite k (B q)] :
    Module.finrank k ((∀ v, A v) × ∀ q, B q) = ∑ v, Module.finrank k (A v) + ∑ q, Module.finrank k (B q) := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]

variable {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M]
  (ρ : Representation k Γ M)

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M] in
private theorem dOne_eq (a : Γ → M) : dOne ρ a = d1 ρ a := by
  funext p
  obtain ⟨s, t⟩ := p
  show a s + ρ s (a t) - a (s * t) = ρ s (a t) - a (s * t) + a s
  abel

variable (F : Frame Γ)

omit [IsTopologicalGroup Γ] in
private theorem finite_compactly_supported_H1 [Module.Finite k M] [Module.Finite k (H1 ρ)] : Module.Finite k (F.H1c ρ) := by
  haveI : Module.Finite k (B1 ρ) := LinearMap.finiteDimensional_range _
  haveI : Module.Finite k ((B1 ρ).comap (Z1 ρ).subtype) :=
    Module.Finite.of_injective ((Z1 ρ).subtype.restrict (q := B1 ρ) (fun x hx => hx))
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : B1 ρ => z.1) h)))
  haveI : Module.Finite k (Z1 ρ) := Module.Finite.of_submodule_quotient ((B1 ρ).comap (Z1 ρ).subtype)
  let f : F.H1c ρ →ₗ[k] (Z1 ρ × (F.T → M)) :=
    { toFun := fun x => (⟨x.1.1, x.2.1.continuous, x.2.2.1⟩, x.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun x y h =>
    Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2) h))

omit [IsTopologicalGroup Γ] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M] in
private theorem mem_coboundaries_compact (x : F.C2 M) : x ∈ F.framedTwoCoboundaries ρ ↔
    ∃ (h : Γ → M) (y : F.T → M) (e : ∀ q, F.Gq q → M), IsLocallyConstant h ∧
    (∀ q, IsLocallyConstant (e q) ∧ (∀ s t, e q (s * t) = e q s + ρ (F.ψ q s) (e q t)) ∧ ∀ n ∈ F.N q, e q n = 0) ∧
    x.1 = dOne ρ h ∧ (∀ v s, x.2.1 v s = h (F.φ v s) - (ρ (F.φ v s) (y v) - y v)) ∧
    ∀ q s, x.2.2 q s = h (F.ψ q s) - e q s := by
  refine ⟨fun hx => ?_, fun hx => Submodule.subset_span hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 0, 0, IsLocallyConstant.const 0, fun q => ⟨IsLocallyConstant.const 0, by simp, by simp⟩,
      by funext p; simp [dOne], by simp, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨h, y, e, a1, a2, a3, a4, a5⟩ := hx
    obtain ⟨h', y', e', b1, b2, b3, b4, b5⟩ := hx'
    refine ⟨h + h', y + y', e + e', a1.add b1, fun q => ⟨(a2 q).1.add (b2 q).1, fun s t => ?_, fun n hn => ?_⟩, ?_,
      fun v s => ?_, fun q s => ?_⟩
    · simp only [Pi.add_apply, (a2 q).2.1, (b2 q).2.1, map_add]; abel
    · simp [(a2 q).2.2 n hn, (b2 q).2.2 n hn]
    · rw [Prod.fst_add, a3, b3, dOne_eq, dOne_eq, dOne_eq, map_add]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add]; abel
    · simp only [Prod.snd_add, Pi.add_apply, a5, b5]; abel
  | smul c x _ hx =>
    obtain ⟨h, y, e, a1, a2, a3, a4, a5⟩ := hx
    refine ⟨c • h, c • y, c • e, a1.comp (c • ·), fun q => ⟨(a2 q).1.comp (c • ·), fun s t => ?_, fun n hn => ?_⟩, ?_,
      fun v s => ?_, fun q s => ?_⟩
    · simp [(a2 q).2.1]
    · simp [(a2 q).2.2 n hn]
    · rw [Prod.smul_fst, a3, dOne_eq, dOne_eq, map_smul]
    · simp [a4, smul_sub]
    · simp [a5, smul_sub]

private abbrev PP : Type := (∀ v, Z1 (ρ.comp (F.φ v) : Representation k _ M)) × ∀ q, Z1 (ρ.comp (F.ψ q) : Representation k _ M)

private abbrev AA : Type := (∀ v, H1 (ρ.comp (F.φ v) : Representation k _ M)) ×
  ∀ q, H1 (ρ.comp (F.ψ q) : Representation k _ M) ⧸ H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)

private def piA : PP ρ F →ₗ[k] AA ρ F :=
  LinearMap.prodMap (LinearMap.pi fun v => (Submodule.mkQ _).comp (LinearMap.proj v))
    (LinearMap.pi fun q => (Submodule.mkQ _).comp ((Submodule.mkQ _).comp (LinearMap.proj q)))

private def res1 : H1 ρ →ₗ[k] AA ρ F :=
  (LinearMap.pi fun v => resH1 ρ (F.φ v) (F.hφ v)).prod
    (LinearMap.pi fun q => (Submodule.mkQ _).comp (resH1 ρ (F.ψ q) (F.hψ q)))

private def del0 : PP ρ F →ₗ[k] F.framedTwoCocycles ρ where
  toFun z := ⟨(0, fun v => (z.1 v).1, fun q => (z.2 q).1), IsLocallyConstant.const 0,
    fun v => (IsLocallyConstant.iff_continuous _).2 (z.1 v).2.1,
    fun q => (IsLocallyConstant.iff_continuous _).2 (z.2 q).2.1, by simp,
    fun v s t => by simp [dOne, (z.1 v).2.2 s t], fun q s t => by simp [dOne, (z.2 q).2.2 s t]⟩
  map_add' x y := Subtype.ext (Prod.ext (by simp) rfl)
  map_smul' c x := Subtype.ext (Prod.ext (by simp) rfl)

private def del : PP ρ F →ₗ[k] F.Ob ρ := (Submodule.mkQ _).comp (del0 ρ F)

private def fgt0 : F.framedTwoCocycles ρ →ₗ[k] Z2 ρ where
  toFun x := ⟨x.1.1, x.2.1.continuous, fun g h l => by
    have := x.2.2.2.2.1 g h l
    rw [← sub_eq_zero] at this
    rw [← this]; abel⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def fgt : F.Ob ρ →ₗ[k] H2 ρ :=
  Submodule.mapQ _ _ (fgt0 ρ F) fun x hx => by
    obtain ⟨h, y, e, a1, -, a3, -⟩ := (mem_coboundaries_compact ρ F _).1 hx
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨h, a1.continuous, by rw [← dOne_eq]; exact a3.symm⟩

omit [IsTopologicalGroup Γ] [DiscreteTopology M] in
private theorem piA_surj : Function.Surjective (piA ρ F) := by
  rintro ⟨a, b⟩
  choose a' ha using fun v => Submodule.mkQ_surjective _ (a v)
  choose b' hb using fun q => Submodule.mkQ_surjective _ (b q)
  choose b'' hb' using fun q => Submodule.mkQ_surjective _ (b' q)
  refine ⟨(a', b''), Prod.ext (funext ha) (funext fun q => ?_)⟩
  show _ = b q
  rw [← hb q, ← hb' q]; rfl

omit [IsTopologicalGroup Γ] [DiscreteTopology M] in
private theorem kernel_restriction_sha_selmer : LinearMap.ker (res1 ρ F) = Sha1 ρ F.φ F.hφ ⊓
    Sel ρ F.ψ F.hψ (fun q => H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) := by
  ext x
  rw [Submodule.mem_inf, mem_Sel, Sha1, Submodule.mem_iInf, LinearMap.mem_ker, Prod.ext_iff, funext_iff, funext_iff]
  refine and_congr Iff.rfl (forall_congr' fun q => ?_)
  exact Submodule.Quotient.mk_eq_zero _

omit [IsTopologicalGroup Γ] [DiscreteTopology M] in
private theorem mk_mem_ur (N : Subgroup Γ) (hN : ∀ n ∈ N, ρ n = 1) (z : Z1 ρ) :
    (Submodule.Quotient.mk z : H1 ρ) ∈ H1ur ρ N ↔ ∀ n ∈ N, z.1 n = 0 := by
  show Submodule.Quotient.mk (restrictCocycles1 ρ N.subtype continuous_subtype_val z) = (0 : H1 (ρ.comp N.subtype)) ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ n hn
    have e : z.1 n = ρ n m - m := hm ⟨n, hn⟩
    rw [e, hN n hn]; simp
  · intro h
    refine ⟨0, fun j => ?_⟩
    show z.1 j = _
    rw [h j j.2, map_zero, sub_zero]

omit [IsTopologicalGroup Γ] in
private theorem ker_del (hN : ∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) :
    LinearMap.ker (del ρ F) = (LinearMap.range (res1 ρ F)).comap (piA ρ F) := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_range]
  refine (Submodule.Quotient.mk_eq_zero _).trans ((mem_coboundaries_compact ρ F _).trans ?_)
  constructor
  · rintro ⟨h, y, e, a1, a2, a3, a4, a5⟩
    let c : Z1 ρ := ⟨h, a1.continuous, fun s t => by
      have : 0 = h s + ρ s (h t) - h (s * t) := congrFun a3 (s, t)
      exact (sub_eq_zero.1 this.symm).symm⟩
    refine ⟨Submodule.Quotient.mk c, Prod.ext (funext fun v => ?_) (funext fun q => ?_)⟩
    · refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨y v, fun s => ?_⟩)
      have : (z.1 v).1 s = _ := a4 v s
      show h (F.φ v s) - (z.1 v).1 s = ρ (F.φ v s) (y v) - y v
      rw [this]; abel
    · refine (Submodule.Quotient.eq _).2 ?_
      refine (mk_mem_ur _ _ (hN q) (restrictCocycles1 ρ (F.ψ q) (F.hψ q) c - z.2 q)).2 fun n hn => ?_
      have : (z.2 q).1 n = _ := a5 q n
      show h (F.ψ q n) - (z.2 q).1 n = 0
      rw [this, (a2 q).2.2 n hn]; abel
  · rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : ∀ v, ∃ m, ∀ s, c.1 (F.φ v s) - (z.1 v).1 s = ρ (F.φ v s) m - m := fun v =>
      (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 (congrFun (congrArg Prod.fst hx) v))
    have h2 : ∀ q, ∀ n ∈ F.N q, c.1 (F.ψ q n) - (z.2 q).1 n = 0 := fun q =>
      (mk_mem_ur _ _ (hN q) (restrictCocycles1 ρ (F.ψ q) (F.hψ q) c - z.2 q)).1
        ((Submodule.Quotient.eq _).1 (congrFun (congrArg Prod.snd hx) q))
    choose y hy using h1
    refine ⟨c.1, y, fun q => (restrictCocycles1 ρ (F.ψ q) (F.hψ q) c - z.2 q).1, (IsLocallyConstant.iff_continuous _).2 c.2.1,
      fun q => ⟨(IsLocallyConstant.iff_continuous _).2 (restrictCocycles1 ρ (F.ψ q) (F.hψ q) c - z.2 q).2.1,
        (restrictCocycles1 ρ (F.ψ q) (F.hψ q) c - z.2 q).2.2, h2 q⟩, ?_, fun v s => ?_, fun q s => ?_⟩
    · funext p
      show 0 = c.1 p.1 + ρ p.1 (c.1 p.2) - c.1 (p.1 * p.2)
      rw [c.2.2, sub_self]
    · show (z.1 v).1 s = _
      rw [← hy v s]; abel
    · show (z.2 q).1 s = c.1 (F.ψ q s) - (c.1 (F.ψ q s) - (z.2 q).1 s)
      abel

omit [IsTopologicalGroup Γ] in
private theorem ker_fgt : LinearMap.ker (fgt ρ F) = LinearMap.range (del ρ F) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨h, hh, e⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    have e' : x.1.1 = dOne ρ h := by rw [dOne_eq]; exact e.symm
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := x.2
    refine ⟨(fun v => ⟨fun s => x.1.2.1 v s - h (F.φ v s), (a2 v).continuous.sub (hh.comp (F.hφ v)), fun s t => ?_⟩,
      fun q => ⟨fun s => x.1.2.2 q s - h (F.ψ q s), (a3 q).continuous.sub (hh.comp (F.hψ q)), fun s t => ?_⟩), ?_⟩
    · have := a5 v s t
      rw [e'] at this
      simp only [dOne, MonoidHom.comp_apply] at this
      simp only [map_mul, map_sub, MonoidHom.comp_apply]
      rw [← sub_eq_zero] at this ⊢
      rw [← this]; abel
    · have := a6 q s t
      rw [e'] at this
      simp only [dOne, MonoidHom.comp_apply] at this
      simp only [map_mul, map_sub, MonoidHom.comp_apply]
      rw [← sub_eq_zero] at this ⊢
      rw [← this]; abel
    · symm
      refine (Submodule.Quotient.eq _).2 ((mem_coboundaries_compact ρ F _).2 ⟨h, 0, 0, (IsLocallyConstant.iff_continuous _).2 hh,
        fun q => ⟨IsLocallyConstant.const 0, by simp, by simp⟩, ?_, fun v s => ?_, fun q s => ?_⟩)
      · show x.1.1 - 0 = _
        rw [sub_zero, e']
      · show x.1.2.1 v s - (x.1.2.1 v s - h (F.φ v s)) = _
        simp
      · show x.1.2.2 q s - (x.1.2.2 q s - h (F.ψ q s)) = _
        simp
  · rintro _ ⟨z, rfl⟩
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact (B2 ρ).zero_mem

private def res2 : H2 ρ →ₗ[k] ((∀ v, H2 (ρ.comp (F.φ v) : Representation k _ M)) ×
    ∀ q, H2 (ρ.comp (F.ψ q) : Representation k _ M)) :=
  (LinearMap.pi fun v => resH2 ρ (F.φ v) (F.hφ v)).prod (LinearMap.pi fun q => resH2 ρ (F.ψ q) (F.hψ q))

omit [IsTopologicalGroup Γ] in
private theorem range_fgt : LinearMap.range (fgt ρ F) = LinearMap.ker (res2 ρ F) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := x.2
    refine Prod.ext (funext fun v => ?_) (funext fun q => ?_)
    · refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨x.1.2.1 v, (a2 v).continuous, ?_⟩)
      rw [← dOne_eq]
      exact funext fun p => (a5 v p.1 p.2).symm
    · refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨x.1.2.2 q, (a3 q).continuous, ?_⟩)
      rw [← dOne_eq]
      exact funext fun p => (a6 q p.1 p.2).symm
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    choose a ha ha' using fun v =>
      (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Prod.fst hx) v))
    choose b hb hb' using fun q =>
      (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Prod.snd hx) q))
    refine ⟨Submodule.Quotient.mk ⟨(c.1, a, b), (IsLocallyConstant.iff_continuous _).2 c.2.1,
      fun v => (IsLocallyConstant.iff_continuous _).2 (ha v), fun q => (IsLocallyConstant.iff_continuous _).2 (hb q),
      fun s t u => ?_, fun v s t => ?_, fun q s t => ?_⟩, rfl⟩
    · have := c.2.2 s t u
      rw [← sub_eq_zero, ← this]; abel
    · rw [dOne_eq]; exact (congrFun (ha' v) (s, t)).symm
    · rw [dOne_eq]; exact (congrFun (hb' q) (s, t)).symm

end UpperTheory.V.Alg.FrameCount

end

theorem UpperTheory.V.Alg.frame_count :
    ∀ (k Γ M : Type) [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M]
      (ρ : Representation k Γ M), IsOpen (ρ.ker : Set Γ) → ∀ (F : Frame Γ) [∀ v, IsTopologicalGroup (F.Gv v)] [∀ q, IsTopologicalGroup (F.Gq q)], (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) →
      Module.Finite k (ReciprocityTheory.Gal.H1 ρ) → Module.Finite k (ReciprocityTheory.Gal.H2 ρ) → (∀ v, Module.Finite k (ReciprocityTheory.Gal.H1 (ρ.comp (F.φ v) : Representation k _ M)) ∧ Module.Finite k (ReciprocityTheory.Gal.H2 (ρ.comp (F.φ v) : Representation k _ M))) →
      (∀ q, Module.Finite k (ReciprocityTheory.Gal.H1 (ρ.comp (F.ψ q) : Representation k _ M)) ∧ Module.Finite k (ReciprocityTheory.Gal.H2 (ρ.comp (F.ψ q) : Representation k _ M))) →
      Module.Finite k (F.H1c ρ) ∧ Module.Finite k (F.Ob ρ) ∧
      Module.finrank k (ReciprocityTheory.Gal.H0 ρ) + Module.finrank k (F.H1c ρ) + ∑ v, Module.finrank k (ReciprocityTheory.Gal.H1 (ρ.comp (F.φ v) : Representation k _ M)) + ∑ q, Module.finrank k (ReciprocityTheory.Gal.H1 (ρ.comp (F.ψ q) : Representation k _ M)) + Module.finrank k (ReciprocityTheory.Gal.H2 ρ)
        + Module.finrank k (((∀ v, ReciprocityTheory.Gal.H2 (ρ.comp (F.φ v) : Representation k _ M)) × ∀ q, ReciprocityTheory.Gal.H2 (ρ.comp (F.ψ q) : Representation k _ M)) ⧸
            LinearMap.range ((LinearMap.pi fun v => ReciprocityTheory.Gal.resH2 ρ (F.φ v) (F.hφ v)).prod (LinearMap.pi fun q => ReciprocityTheory.Gal.resH2 ρ (F.ψ q) (F.hψ q)))) =
      ∑ v, Module.finrank k (ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) + Module.finrank k (ReciprocityTheory.Gal.H1 ρ) + ∑ q, Module.finrank k (ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) + Module.finrank k (F.Ob ρ)
        + ∑ v, Module.finrank k (ReciprocityTheory.Gal.H2 (ρ.comp (F.φ v) : Representation k _ M)) + ∑ q, Module.finrank k (ReciprocityTheory.Gal.H2 (ρ.comp (F.ψ q) : Representation k _ M)) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ _ _ ρ hρ F _ _ hN h1 h2 hv hq
  haveI := fun v => (hv v).1
  haveI := fun v => (hv v).2
  haveI := fun q => (hq q).1
  haveI := fun q => (hq q).2
  have e0 := UpperTheory.V.Alg.finrank_compact_support_H1 k Γ M ρ hρ F hN h1
  rw [← FrameCount.kernel_restriction_sha_selmer] at e0
  have e1 := (FrameCount.res1 ρ F).finrank_range_add_finrank_ker
  obtain ⟨f2, e2⟩ := FrameCount.rank_range (FrameCount.piA ρ F) (FrameCount.piA_surj ρ F) (FrameCount.del ρ F) _
    (FrameCount.ker_del ρ F hN)
  rw [FrameCount.finrank_prod_pi] at e2
  have e3 : ∑ q, Module.finrank k (ReciprocityTheory.Gal.H1 (ρ.comp (F.ψ q) : Representation k _ M) ⧸
        ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) +
      ∑ q, Module.finrank k (ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) =
      ∑ q, Module.finrank k (ReciprocityTheory.Gal.H1 (ρ.comp (F.ψ q) : Representation k _ M)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => Submodule.finrank_quotient_add_finrank _
  rw [← FrameCount.ker_fgt] at f2 e2
  haveI fOb : Module.Finite k (F.Ob ρ) := by
    haveI := Module.Finite.equiv (FrameCount.fgt ρ F).quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker (FrameCount.fgt ρ F))
  have e4 := (FrameCount.fgt ρ F).finrank_range_add_finrank_ker
  rw [FrameCount.range_fgt] at e4
  have e5 := (FrameCount.res2 ρ F).finrank_range_add_finrank_ker
  have e6 := Submodule.finrank_quotient_add_finrank (LinearMap.range (FrameCount.res2 ρ F))
  rw [FrameCount.finrank_prod_pi] at e6
  refine ⟨FrameCount.finite_compactly_supported_H1 ρ F, fOb, ?_⟩
  change _ + Module.finrank k (_ ⧸ LinearMap.range (FrameCount.res2 ρ F)) = _
  omega
