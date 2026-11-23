import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

noncomputable section

namespace GlobalTheory.PrincInLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem exists_entries (S : Subring R) (β x : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (hx : ∀ z ∈ H, ∃ y ∈ H, x.1 *ᵥ z - z = N • y) :
    ∃ s : Matrix (Fin n) (Fin n) S, (β⁻¹ * x * β).1 = (1 + N • s).map S.subtype := by
  have h : ∀ j, ∃ c : Fin n → S, ∀ i, (β⁻¹ * x * β).1 i j = (1 : Matrix (Fin n) (Fin n) R) i j + N • (c i : R) := by
    intro j
    have e0 : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    obtain ⟨y, hy, e⟩ := hx (β.1 *ᵥ Pi.single j 1) ((hH _).2 fun i => by
      rw [e0, Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _])
    refine ⟨fun i => ⟨_, (hH y).1 hy i⟩, fun i => ?_⟩
    have e1 := congrArg (fun v => ((β⁻¹).1 *ᵥ v) i) e
    simp only [Matrix.mulVec_sub, e0, Matrix.mulVec_smul] at e1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Pi.sub_apply, sub_eq_iff_eq_add'] at e1
    rw [Units.val_mul, Units.val_mul, Matrix.one_apply]
    rw [Pi.single_apply] at e1
    exact e1
  choose c hc using h
  refine ⟨Matrix.of fun i j => c j i, Matrix.ext fun i j => ?_⟩
  rw [hc, Matrix.map_apply, Matrix.add_apply, map_add, Matrix.smul_apply, map_nsmul, Matrix.one_apply,
    Matrix.one_apply]
  congr 1
  split_ifs <;> simp

theorem exists_int (S : Subring R) (β x : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (hx : ∀ z ∈ H, ∃ y ∈ H, x.1 *ᵥ z - z = N • y) (hx' : ∀ z ∈ H, ∃ y ∈ H, (x⁻¹).1 *ᵥ z - z = N • y) :
    ∃ y : GL (Fin n) S, β * Formalism.UG.bc S.subtype y * β⁻¹ = x ∧
      ∀ (k : Type) [CommRing k] (φ : S →+* k), (N : k) = 0 → Formalism.UG.bc φ y = 1 := by
  obtain ⟨s, hs⟩ := exists_entries S β x H N hH hx
  obtain ⟨t, ht⟩ := exists_entries S β x⁻¹ H N hH hx'
  have inj : Function.Injective (fun m : Matrix (Fin n) (Fin n) S => m.map S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : (1 + N • s) * (1 + N • t) = 1 := inj <| by
    simp only [Matrix.map_mul, ← hs, ← ht, ← Units.val_mul]
    rw [show β⁻¹ * x * β * (β⁻¹ * x⁻¹ * β) = 1 by group, Matrix.map_one _ (map_zero _) (map_one _)]; rfl
  have h2 : (1 + N • t) * (1 + N • s) = 1 := inj <| by
    simp only [Matrix.map_mul, ← hs, ← ht, ← Units.val_mul]
    rw [show β⁻¹ * x⁻¹ * β * (β⁻¹ * x * β) = 1 by group, Matrix.map_one _ (map_zero _) (map_one _)]; rfl
  refine ⟨⟨_, _, h1, h2⟩, ?_, fun k _ φ hN => ?_⟩
  · have : Formalism.UG.bc S.subtype (⟨_, _, h1, h2⟩ : GL (Fin n) S) = β⁻¹ * x * β := Units.ext hs.symm
    rw [this]; group
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change φ ((1 + N • s) i j) = (1 : Matrix (Fin n) (Fin n) k) i j
    rw [Matrix.add_apply, map_add, Matrix.smul_apply, map_nsmul, nsmul_eq_mul, hN, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end Ring

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem swap_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) :
    (fun i => Algebra.TensorProduct.comm F _ E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    have hm : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have := Submodule.smul_mem (Formalism.L2.Herm.hatL (F := F) Λ) ⟨_, hm⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
    convert this using 1
    funext i
    change x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx

theorem smul_mem_hat (Λ : Submodule (𝓞 E) (Fin n → E)) (t : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (ht : t ∈ Formalism.L2.Herm.intAf F E) :
    ∀ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      (Algebra.TensorProduct.comm F _ E).symm t • y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have gen : ∀ t : FiniteAdeleRing (𝓞 F) F ⊗[F] E, (∀ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ,
      t • (fun i => a ⊗ₜ[F] x i) ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) →
      ∀ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), t • y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
    intro t ht y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz => obtain ⟨a, ha, x, hx, rfl⟩ := hz; exact ht a ha x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  induction ht using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩
    · refine gen _ fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, c • x, Λ.smul_mem c hx, ?_⟩
      funext i
      change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] algebraMap (𝓞 E) E c) * (a ⊗ₜ[F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
    · refine gen _ fun a ha x hx => AddSubgroup.subset_closure
        ⟨b * a, fun v => mul_mem (b.2 v) (ha v), x, hx, ?_⟩
      funext i
      change ((b : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E)) * (a ⊗ₜ[F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro y hy; rwa [map_one, one_smul]
  | add a b _ _ ha hb => intro y hy; rw [map_add, add_smul]; exact add_mem (ha y hy) (hb y hy)
  | neg a _ ha => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (ha y hy)
  | mul a b _ _ ha hb => intro y hy; rw [map_mul, mul_smul]; exact ha _ (hb y hy)

theorem swap_symm_mem_hat (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (fun i => (Algebra.TensorProduct.comm F _ E).symm (z i)) ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have := smul_mem_hat Λ c.1 c.2 _ hx
    convert this using 1
    funext i
    exact map_mul (Algebra.TensorProduct.comm F _ E).symm c.1 (x i)

theorem cong_swap (Λ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ)
    (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      M *ᵥ z - z = N • y) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      M.map (Algebra.TensorProduct.comm F _ E) *ᵥ z - z = N • y := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h _ (swap_symm_mem_hat Λ z hz)
  refine ⟨_, swap_mem_hatL Λ y hy, funext fun i => ?_⟩
  have := congrArg (Algebra.TensorProduct.comm F _ E) (congrFun e i)
  simpa only [Pi.sub_apply, Pi.smul_apply, map_sub, map_nsmul, Matrix.mulVec, dotProduct, map_sum, map_mul,
    AlgEquiv.apply_symm_apply, Matrix.map_apply] using this

theorem swap_mem_UPts (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (hg : g ∈ HR (FiniteAdeleRing (𝓞 F) F) σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom g ∈
      Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  refine Formalism.UG.Final.BCMem _ _ (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (Formalism.UG.sigR σ _)
    (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom (RingHom.ext fun x => ?_) (JR _ J) g hg
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x => rfl

end Swap

theorem eq_latC {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) : Λ = GlobalTheory.Member.latC V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  rw [one_pow, Nat.cast_one, ← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at h1 h2
  ext x
  exact ⟨fun hx => by simpa using h2 x hx, fun hx => by simpa using h1 x hx⟩

set_option maxHeartbeats 800000 in

theorem finCong_mem_levEnv : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (N : ℕ) (k : GA D V), IsSDFrame V β Λ 1 → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → GlobalTheory.Member.FinCong V N k → (finHom V).rangeRestrict k ∈ (levEnv V β L).J := by
  intro D V β Λ L N k hΛ hN hk
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V N a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V a).1 *ᵥ z - z = N • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact cong_swap Λ N _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, hred⟩ := exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Lev.finE V k)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) N hfr (hc k hk) hc'
  have hy' : Formalism.L2.DIV.frGL β y = Lev.finE V k := hy
  have hSt : Lev.finE V k ∈ Formalism.L2.DIV.St β := ⟨y, hy'⟩
  have hr : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
    intro PP hP
    rw [← hy', Formalism.L2.DIV.redFn_frGL]
    refine hred _ _ ?_
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hN PP hP)
  have hU : Lev.finE V k ∈ Formalism.L2.DIV.UA D.sp.cm V.gram :=
    swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V k)
  change Lev.finE V k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L)
  refine ⟨⟨⟨⟨hU, hSt⟩, ?_⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hr PP (Or.inl hP)]; exact one_mem _
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hr PP (Or.inr hP)]; exact one_mem _
  · have e : Formalism.L2.DIV.rTup β L (Lev.finE V k) = 1 := by
      funext PP
      show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn β PP.1 (Lev.finE V k)) = 1
      rw [hr PP.1 (Or.inl PP.2)]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    show Formalism.L2.DIV.rTup β L (Lev.finE V k) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r))
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.PrincInLevel
