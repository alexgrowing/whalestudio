import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective

noncomputable section

namespace GlobalTheory.JumpDescent

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

theorem descent {G M Ω : Type} [Group G] [AddCommGroup M] [Field Ω] (H : Subgroup G)
    [Finite (G ⧸ H)] (A : G → M →+ M) (hA1 : ∀ x, A 1 x = x)
    (hAm : ∀ g h x, A (g * h) x = A g (A h x))
    (m : Ω → M →+ M) (hm1 : ∀ x, m 1 x = x) (hmm : ∀ a b x, m (a * b) x = m a (m b x))
    (hma : ∀ a b x, m (a + b) x = m a x + m b x)
    (ε : G → (Ω →* Ω)) (hεm : ∀ g h a, ε (g * h) a = ε g (ε h a)) (hε1 : ∀ a, ε 1 a = a)
    (hε : ∀ g a x, A g (m a x) = m (ε g a) (A g x))
    (S : Submonoid Ω) (hH : ∀ g, g ∈ H ↔ ∀ a ∈ S, ε g a = a)
    (F F' : AddSubgroup M) (hFA : ∀ g, ∀ x ∈ F, A g x ∈ F) (hFm : ∀ a, ∀ x ∈ F, m a x ∈ F)
    (hF'A : ∀ g, ∀ x ∈ F', A g x ∈ F') (hF'm : ∀ a, ∀ x ∈ F', m a x ∈ F')
    (hfix : ∀ y ∈ F, (∀ g, A g y = y) → y ∈ F')
    (x : M) (hx : x ∈ F) (hxH : ∀ h ∈ H, A h x = x) : x ∈ F' := by
  classical
  haveI := Fintype.ofFinite (G ⧸ H)
  have hm0 : ∀ x, m 0 x = 0 := fun x => by
    have := hma 0 0 x
    rw [add_zero] at this
    exact left_eq_add.1 this
  let T : Submodule Ω (G ⧸ H → Ω) :=
    { carrier := {v | ∑ q, m (v q) (A q.out x) ∈ F'}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Pi.add_apply, hma, Finset.sum_add_distrib] at *
        exact F'.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, Pi.zero_apply, hm0, Finset.sum_const_zero]
        exact F'.zero_mem
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, hmm, ← map_sum] at *
        exact hF'm _ _ ha }
  let φ : G ⧸ H → (S →* Ω) := fun q => (ε q.out).comp S.subtype
  have hφ : Function.Injective φ := by
    intro q q' hq
    rw [← q.out_eq, ← q'.out_eq]
    apply QuotientGroup.eq.2
    rw [hH]
    intro a ha
    have h1 : ε q.out a = ε q'.out a := DFunLike.congr_fun hq ⟨a, ha⟩
    rw [hεm, ← h1, ← hεm, inv_mul_cancel, hε1]
  have hli : LinearIndependent Ω (fun q => (φ q : S → Ω)) :=
    (linearIndependent_monoidHom S Ω).comp φ hφ
  have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    change ∑ q : G ⧸ H, m (ε q.out a) (A q.out x) ∈ F'
    simp only [← hε]
    have hz : ∀ h ∈ H, A h (m a x) = m a x := fun h hh => by
      rw [hε, hxH h hh, (hH h).1 hh a a.2]
    apply hfix _ (F.sum_mem fun q _ => hFA _ _ (hFm _ _ hx))
    intro g
    rw [map_sum, ← Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => A q.out (m a x))]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g * q.out)
    have h2 : (MulAction.toPerm g q : G ⧸ H) = ((g * q.out : G) : G ⧸ H) :=
      (MulAction.Quotient.mk_smul_out H g q).symm
    rw [h2, hh, hAm, hAm, hz _ h.2]
  have h1 : (Pi.single ((1 : G) : G ⧸ H) 1 : G ⧸ H → Ω) ∈ T := hT ▸ Submodule.mem_top
  change ∑ q : G ⧸ H, m ((Pi.single ((1 : G) : G ⧸ H) 1 : G ⧸ H → Ω) q) (A q.out x) ∈ F' at h1
  rw [Finset.sum_eq_single ((1 : G) : G ⧸ H) (fun q _ hq => by rw [Pi.single_eq_of_ne hq, hm0])
    (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, hm1] at h1
  have h2 := hF'A (((1 : G) : G ⧸ H).out)⁻¹ _ h1
  rwa [← hAm, inv_mul_cancel, hA1] at h2

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

section
variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem map_mem_FilV (K K' : FinExt l) (a : ℤ) (f : V →ₗ[LL] V) (g : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)
    (hg : ∀ b ∈ (P.PD K).Fil a, g b ∈ (P.PD K').Fil a) (x : V ⊗[ℚ_[l]] P.R.BdR)
    (hx : x ∈ FilV (P.PD K) (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f g x ∈ FilV (P.PD K') (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨f v ⊗ₜ ⟨g b.1, hg _ b.2⟩, rfl⟩
  | add y z hy hz => simp only [map_add]; exact Submodule.add_mem _ hy hz

theorem FilV_eq (K K' : FinExt l) (a : ℤ) :
    FilV (P.PD K') (LL := LL) (V := V) a = FilV (P.PD K) (LL := LL) (V := V) a := by
  have key : ∀ K K' : FinExt l,
      FilV (P.PD K) (LL := LL) (V := V) a ≤ FilV (P.PD K') (LL := LL) (V := V) a := by
    intro K K' x hx
    have := map_mem_FilV P K K' a LinearMap.id LinearMap.id (fun b hb => by
      have h : b ∈ (((P.PD K).Fil a : Submodule ↥K.1 P.R.BdR) : Set P.R.BdR) := hb
      rw [P.PD_Fil K K' a] at h
      exact h) x hx
    rwa [AlgebraTensorModule.map_id] at this
  exact le_antisymm (key _ _) (key _ _)

theorem FilV_anti (K : FinExt l) (a : ℤ) :
    FilV (P.PD K) (LL := LL) (V := V) (a + 1) ≤ FilV (P.PD K) (LL := LL) (V := V) a := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, (P.PD K).Fil_anti a b.2⟩, rfl⟩
  | add y z hy hz => simp only [map_add]; exact Submodule.add_mem _ hy hz

theorem mul_mem_Fil (K : FinExt l) (a : ℤ) (c : Om l) (b : P.R.BdR) (hb : b ∈ (P.PD K).Fil a) :
    algebraMap (Om l) P.R.BdR c * b ∈ (P.PD K).Fil a := by
  obtain ⟨E, hc⟩ : ∃ E : FinExt l, c ∈ E.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {c},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c)⟩,
    IntermediateField.mem_adjoin_simple_self _ c⟩
  have h : b ∈ (((P.PD K).Fil a : Submodule ↥K.1 P.R.BdR) : Set P.R.BdR) := hb
  rw [P.PD_Fil K E a] at h
  have h2 : (⟨c, hc⟩ : ↥E.1) • b ∈
      (((P.PD E).Fil a : Submodule ↥E.1 P.R.BdR) : Set P.R.BdR) := Submodule.smul_mem _ _ h
  rw [P.PD_Fil E K a, Algebra.smul_def] at h2
  exact h2

theorem mem_DdR (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem actVdR_tmul (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K)) (v : V)
    (b : P.R.BdR) : actVdR (P.PD K) ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ P.actQdR g b := by
  rw [← P.PD_actdR K g b]
  rfl

theorem actVdR_comp {K K' : FinExt l} (h : K.1 ≤ K'.1) (ρ : Representation LL ↥(GK K) V)
    (g : ↥(GK K')) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    actVdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) g x =
      actVdR (P.PD K) ρ (Subgroup.inclusion (GK_le h) g) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVdR_tmul, actVdR_tmul]; rfl
  | add y z hy hz => simp only [map_add, hy, hz]

def mulOm (c : Om l) : V ⊗[ℚ_[l]] P.R.BdR →ₗ[LL] V ⊗[ℚ_[l]] P.R.BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft ℚ_[l] (algebraMap (Om l) P.R.BdR c))

theorem mulOm_tmul (c : Om l) (v : V) (b : P.R.BdR) :
    mulOm (LL := LL) P c (v ⊗ₜ b) = v ⊗ₜ (algebraMap (Om l) P.R.BdR c * b) := rfl

theorem mem_succ_of_fixed {K K' : FinExt l} (h : K.1 ≤ K'.1) (ρ : Representation LL ↥(GK K) V)
    (u : ℤ)
    (hfix : ∀ y ∈ FilV (P.PD K) (LL := LL) (V := V) u, y ∈ DdR (P.PD K) ρ →
      y ∈ FilV (P.PD K) (LL := LL) (V := V) (u + 1))
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ FilV (P.PD K) (LL := LL) (V := V) u)
    (hxH : x ∈ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :
    x ∈ FilV (P.PD K) (LL := LL) (V := V) (u + 1) := by
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  haveI : Finite (GQ l ⧸ GK K') :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K'.1)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hA : ∀ (a : ℤ) (g : ↥(GK K)), ∀ x ∈ FilV (P.PD K) (LL := LL) (V := V) a,
      actVdR (P.PD K) ρ g x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a g x hx =>
    map_mem_FilV P K K a _ _ (fun b hb => (P.PD K).Fil_G g a b hb) x hx
  have hM : ∀ (a : ℤ) (c : Om l), ∀ x ∈ FilV (P.PD K) (LL := LL) (V := V) a,
      mulOm (LL := LL) P c x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a c x hx =>
    map_mem_FilV P K K a _ _ (fun b hb => mul_mem_Fil P K a c b hb) x hx
  refine descent (Ω := Om l) ((GK K').subgroupOf (GK K))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom) ?_ ?_
    (fun c => (mulOm (LL := LL) P c).toAddMonoidHom) ?_ ?_ ?_
    (fun g => ((g : GQ l) : Om l →* Om l)) (fun _ _ _ => rfl) (fun _ => rfl) ?_
    K'.1.toSubalgebra.toSubsemiring.toSubmonoid ?_
    (FilV (P.PD K) (LL := LL) (V := V) u).toAddSubgroup
    (FilV (P.PD K) (LL := LL) (V := V) (u + 1)).toAddSubgroup (hA u) (hM u) (hA _) (hM _)
    (fun y hy hy' => hfix y hy ((mem_DdR P K ρ y).2 hy')) x hx ?_
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [actVdR_tmul]
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [actVdR_tmul]
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [mulOm_tmul]
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [mulOm_tmul, mul_assoc]
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul v b => simp [mulOm_tmul, add_mul, tmul_add]
    | add y z hy hz => simp only [map_add, hy, hz]; abel
  · intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [mulOm_tmul, actVdR_tmul, P.actQdR_Om]
    | add y z hy hz => simp only [map_add, hy, hz]
  · intro g
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hg a ha => hg ⟨a, ha⟩, fun hg a => hg a.1 a.2⟩
  · intro g hg
    have := (mem_DdR P K' _ x).1 hxH ⟨g.1, hg⟩
    rw [actVdR_comp P h] at this
    exact this

theorem de_rham_jump_iff_extension {K K' : FinExt l} (h : K.1 ≤ K'.1) (ρ : Representation LL ↥(GK K) V)
    (u : ℤ) :
    (DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
        FilV (P.PD K') (LL := LL) (V := V) (u + 1) ≠
      DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
        FilV (P.PD K') (LL := LL) (V := V) u) ↔
    (DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) (u + 1) ≠
      DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) u) := by
  rw [FilV_eq P K K', FilV_eq P K K', not_iff_not]
  constructor
  · intro he
    refine le_antisymm (inf_le_inf_left _ (FilV_anti P K u)) fun x hx => ⟨hx.1, ?_⟩
    have hx' : x ∈ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
      rw [mem_DdR]
      intro g
      rw [actVdR_comp P h]
      exact (mem_DdR P K _ x).1 hx.1 _
    exact (he.ge ⟨hx', hx.2⟩).2
  · intro he
    refine le_antisymm (inf_le_inf_left _ (FilV_anti P K u)) fun x hx => ⟨hx.1, ?_⟩
    exact mem_succ_of_fixed P h ρ u (fun y hy hy' => (he.ge ⟨hy', hy⟩).2) x hx.2 hx.1

end

theorem jump_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1)
    (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (u : ℤ),
    (DdR (P.PD K') (Y.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
        FilV (P.PD K') (LL := ↥LL.1) (V := Y.V) (u + 1) ≠
      DdR (P.PD K') (Y.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
        FilV (P.PD K') (LL := ↥LL.1) (V := Y.V) u) ↔
    (DdR (P.PD K) Y.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Y.V) (u + 1) ≠
      DdR (P.PD K) Y.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Y.V) u) :=
  fun _ _ P _ _ _ h Y u => de_rham_jump_iff_extension P h Y.ρ u

end GlobalTheory.JumpDescent
