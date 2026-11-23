import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.NsqEqRnSq
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightsCompactStabilizer

open scoped InnerProductSpace
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
open GlobalTheory.CompanionTheory.KLowSpan (kLowSpan KLower)
open PI.UpqRep (root)

noncomputable section

namespace UpperTheory.Lit.Bur.KShift

variable {n : ℕ} {ε : Fin n → Bool}

section Alg

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}

theorem kUnit_of (hU : IsUnitary ε E) : KUnit ε E := by
  intro a b hab y z
  have := hU a b y z
  simpa [Formalism.REAL.sgn, hab] using this

theorem comm_apply (hE : GlRel E) (i j a b : Fin n) (u : V) :
    E i j (E a b u) = E a b (E i j u) +
      ((if j = a then E i b u else 0) - (if b = i then E a j u else 0)) := by
  have h := congrArg (fun T : Module.End ℂ V => T u) (hE i j a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> simp_all [sub_eq_iff_eq_add, add_comm]

def annSub (E : Fin n → Fin n → Module.End ℂ V) (x : V) : Submodule ℂ V where
  carrier := {s | ⟪x, s⟫_ℂ = 0 ∧ ∀ a b, ⟪x, E a b s⟫_ℂ = 0}
  add_mem' := by
    rintro s t ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [inner_add_right, h1, h3, add_zero], fun a b => by
      rw [map_add, inner_add_right, h2, h4, add_zero]⟩
  zero_mem' := ⟨by simp, fun a b => by simp⟩
  smul_mem' := by
    rintro c s ⟨h1, h2⟩
    exact ⟨by rw [inner_smul_right, h1, mul_zero], fun a b => by
      rw [map_smul, inner_smul_right, h2, mul_zero]⟩

theorem inner_lower_eq_zero (hU : KUnit ε E) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε E μ x)
    {c d : Fin n} (hdc : d < c) (he : ε c = ε d) (y : V) : ⟪x, E c d y⟫_ℂ = 0 := by
  rw [← hU d c he.symm, hx.2 d c hdc he.symm, inner_zero_left]

theorem ann_lower (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε E μ x)
    {c d : Fin n} (hdc : d < c) (he : ε c = ε d) {s : V} (hs : s ∈ annSub E x) :
    E c d s ∈ annSub E x := by
  refine ⟨hs.2 c d, fun a b => ?_⟩
  rw [comm_apply hE a b c d s, inner_add_right, inner_lower_eq_zero hU hx hdc he, inner_sub_right]
  split_ifs <;> simp [hs.2]

theorem lowSpan_le_ann (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {x v : V}
    (hx : KHighest ε E μ x) (hv : v ∈ annSub E x) : kLowSpan ε E v ≤ annSub E x := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => simpa using hv
  | cons p l ih =>
    rw [word_cons, Module.End.mul_apply]
    exact ann_lower hE hU hx (hl p (by simp)).1 (hl p (by simp)).2
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

def nbr (E : Fin n → Fin n → Module.End ℂ V) (A : Submodule ℂ V) : Submodule ℂ V :=
  A ⊔ ⨆ p : Fin n × Fin n, A.map (E p.1 p.2)

theorem mem_nbr_of_mem {A : Submodule ℂ V} {s : V} (hs : s ∈ A) : s ∈ nbr E A :=
  Submodule.mem_sup_left hs

theorem apply_mem_nbr {A : Submodule ℂ V} {s : V} (hs : s ∈ A) (a b : Fin n) : E a b s ∈ nbr E A :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (a, b) ⟨s, hs, rfl⟩)

theorem nbr_finite (A : Submodule ℂ V) [FiniteDimensional ℂ A] : FiniteDimensional ℂ (nbr E A) := by
  unfold nbr
  infer_instance

theorem nbr_stab (hE : GlRel E) {A : Submodule ℂ V} (hA : KStab ε E A) : KStab ε E (nbr E A) := by
  intro c d he v hv
  have hle : nbr E A ≤ (nbr E A).comap (E c d) := by
    refine sup_le (fun s hs => mem_nbr_of_mem (hA c d he s hs)) (iSup_le fun p => ?_)
    rintro _ ⟨s, hs, rfl⟩
    show E c d (E p.1 p.2 s) ∈ nbr E A
    rw [comm_apply hE c d p.1 p.2 s]
    refine Submodule.add_mem _ (apply_mem_nbr (hA c d he s hs) _ _) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact apply_mem_nbr hs _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact apply_mem_nbr hs _ _
      · exact Submodule.zero_mem _
  exact hle hv

theorem weight_shift (hE : GlRel E) (hU : KUnit ε E) {μ μ' : Fin n → ℝ} {v x : V}
    (hv : IsWeight E μ v) (hx : KHighest ε E μ' x) (hx0 : x ≠ 0)
    (hxT : x ∈ nbr E (kLowSpan ε E v)) : μ' = μ ∨ ∃ a b, μ' = μ + root a b := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hv' : v ∈ annSub E x :=
    ⟨GlobalTheory.CompanionTheory.KLowSpan.inner_eq_zero_of_weight hU hx.1 hv h1, fun a b =>
      GlobalTheory.CompanionTheory.KLowSpan.inner_eq_zero_of_weight hU hx.1
        (GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply hE hv a b) (h2 a b)⟩
  have hann := lowSpan_le_ann hE hU hx hv'
  have hle : nbr E (kLowSpan ε E v) ≤ (ℂ ∙ x)ᗮ := by
    refine sup_le (fun s hs => ?_) (iSup_le fun p => ?_)
    · exact (Submodule.mem_orthogonal_singleton_iff_inner_right).2 (hann hs).1
    · rintro _ ⟨s, hs, rfl⟩
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right).2 ((hann hs).2 p.1 p.2)
  exact hx0 (inner_self_eq_zero.1 ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hxT)))

theorem nsq_root_le (a b : Fin n) : Formalism.REAL.nsq (root a b) ≤ 2 := by
  by_cases hab : a = b
  · subst hab
    simp [Formalism.REAL.nsq, Formalism.REAL.dot, root]
  · have h : ∀ c, root a b c * root a b c = (if c = a then (1 : ℝ) else 0) + (if c = b then 1 else 0) := by
      intro c
      simp only [root, Pi.sub_apply, Pi.single_apply]
      by_cases h1 : c = a <;> by_cases h2 : c = b
      · exact absurd (h1.symm.trans h2) hab
      · simp [h1, h2]; simp [← h1, h2]
      · subst h2; simp [h1]
      · simp [h1, h2]
    have : Formalism.REAL.nsq (root a b) = 2 := by
      unfold Formalism.REAL.nsq Formalism.REAL.dot
      simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      norm_num
    exact this.le

theorem diag_comm (hE : GlRel E) (a b : Fin n) (u : V) : E a a (E b b u) = E b b (E a a u) := by
  rw [comm_apply hE a a b b u]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem exists_weight (hE : GlRel E) (hU : KUnit ε E) {Q : Submodule ℂ V} [FiniteDimensional ℂ Q]
    (hQ : KStab ε E Q) (hQ0 : Q ≠ ⊥) : ∃ ν : Fin n → ℝ, ∃ x ∈ Q, x ≠ 0 ∧ IsWeight E ν x :=
  _root_.UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight hE hU hQ hQ0

theorem exists_highest (hE : GlRel E) (hU : KUnit ε E) {Q : Submodule ℂ V} [FiniteDimensional ℂ Q]
    (hQ : KStab ε E Q) (hQ0 : Q ≠ ⊥) : ∃ μ : Fin n → ℝ, ∃ x ∈ Q, x ≠ 0 ∧ KHighest ε E μ x := by
  classical
  let ht : (Fin n → ℝ) → ℝ := fun ν => ∑ c : Fin n, ((c : ℕ) : ℝ) * ν c
  let h : Module.End ℂ V := ∑ c : Fin n, (((c : ℕ) : ℝ) : ℂ) • E c c
  have hhQ : ∀ w ∈ Q, h w ∈ Q := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Q.sum_mem fun c _ => Q.smul_mem _ (hQ c c rfl w hw)
  have hh : ∀ (ν : Fin n → ℝ) (x : V), IsWeight E ν x → h x = ((ht ν : ℝ) : ℂ) • x := by
    intro ν x hx
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hx _, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℝ := {t | ∃ ν : Fin n → ℝ, ht ν = t ∧ ∃ x ∈ Q, x ≠ 0 ∧ IsWeight E ν x}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhQ)
    refine (hfin.preimage (f := fun t : ℝ => (t : ℂ)) Complex.ofReal_injective.injOn).subset ?_
    rintro t ⟨ν, rfl, x, hxQ, hx0, hx⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨x, hxQ⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh ν x hx)
    · exact fun h0 => hx0 (congrArg Subtype.val h0)
  obtain ⟨ν₀, x₀, hx₀Q, hx₀, hx₀w⟩ := exists_weight hE hU hQ hQ0
  have hSne : S.Nonempty := ⟨_, ν₀, rfl, x₀, hx₀Q, hx₀, hx₀w⟩
  obtain ⟨t, ⟨ν, rfl, x, hxQ, hx0, hx⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨ν, x, hxQ, hx0, hx, fun a b hab he => ?_⟩
  by_contra hne
  have hmem : ht (ν + root a b) ∈ S :=
    ⟨_, rfl, E a b x, hQ a b he x hxQ, hne, GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply hE hx a b⟩
  have h1 : ht (ν + root a b) = ht ν + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [GlobalTheory.CompanionTheory.DSHighestOfKType.height_root]
  have h2 := hmin _ hmem
  have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [id] at h2
  linarith

theorem le_of_highest (hE : GlRel E) (hU : KUnit ε E) {T M : Submodule ℂ V} [FiniteDimensional ℂ T]
    (hT : KStab ε E T) (hM : KStab ε E M)
    (h : ∀ Q : Submodule ℂ V, Q ≤ T → FiniteDimensional ℂ Q → KStab ε E Q →
      ∀ (μ : Fin n → ℝ), ∀ x ∈ Q, x ≠ 0 → KHighest ε E μ x → x ∈ M) : T ≤ M := by
  have hPfin : FiniteDimensional ℂ (T ⊓ M : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hP : KStab ε E (T ⊓ M) := fun a b he x hx => ⟨hT a b he x hx.1, hM a b he x hx.2⟩
  have hPo := GlobalTheory.CompanionTheory.KLowSpan.kstab_orthogonal hU hP
  have hQfin : FiniteDimensional ℂ (T ⊓ (T ⊓ M)ᗮ : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hQ : KStab ε E (T ⊓ (T ⊓ M)ᗮ) := fun a b he x hx => ⟨hT a b he x hx.1, hPo a b he x hx.2⟩
  have hbot : (T ⊓ (T ⊓ M)ᗮ : Submodule ℂ V) = ⊥ := by
    by_contra hne
    obtain ⟨μ, x, hxQ, hx0, hx⟩ := exists_highest hE hU hQ hne
    have hxM := h _ inf_le_left hQfin hQ μ x hxQ hx0 hx
    exact hx0 (inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hxQ.2 x ⟨hxQ.1, hxM⟩))
  intro t ht
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal (K := T ⊓ M) t
  have hzT : z ∈ T := by
    have : z = t - y := by rw [hyz]; abel
    rw [this]
    exact T.sub_mem ht hy.1
  have hz0 : z = 0 := by
    have : z ∈ (T ⊓ (T ⊓ M)ᗮ : Submodule ℂ V) := ⟨hzT, hz⟩
    rw [hbot] at this
    simpa using this
  rw [hyz, hz0, add_zero]
  exact hy.2

end Alg

section Rep

open CompanionTheory.D.DSIC (IsSmMod hStabLink hWtLink hLowSpan hHWofType hSmMod)
open PI.UpqRep (IsKTypeOf IsKStableOn IsURepOn UJset)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Sm : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ Sm}

theorem kType_of_highest (hσ : IsURepOn (UJset ε) σ) (hM : IsSmMod ε σ Sm E) {μ : Fin n → ℝ}
    {x : Sm} (hx0 : x ≠ 0) (hhw : KHighest ε E μ x) {Q : Submodule ℂ Sm}
    (hQf : FiniteDimensional ℂ Q) (hQ : KStab ε E Q) (hxQ : x ∈ Q) :
    ∃ L : Submodule ℂ Sm, x ∈ L ∧ IsKTypeOf ε σ μ (L.map Sm.subtype) := by
  have hinj : Function.Injective Sm.subtype := Sm.injective_subtype
  have hrel : KRel ε E := fun a b c d _ _ => hM.gl a b c d
  have hun : KUnit ε E := kUnit_of hM.unit
  obtain ⟨L, hLU, hxL, hLst, hirr, hdom, -⟩ := hLowSpan n ε Sm E μ x Q hrel hun hx0 hhw hQf hQ hxQ
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLU
  refine ⟨L, hxL, inferInstance, (hStabLink n ε H σ Sm E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩
  · intro S' hle hS'
    have hle' : S'.comap Sm.subtype ≤ L := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [← hinj hzy]
    have hmap : (S'.comap Sm.subtype).map Sm.subtype = S' := by
      apply Submodule.map_comap_eq_of_le
      exact hle.trans LinearMap.map_le_range
    have hst' : KStab ε E (S'.comap Sm.subtype) := by
      refine (hStabLink n ε H σ Sm E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_
      rwa [hmap]
    rcases hirr _ hle' hst' with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h]
  · exact ⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h),
      (hWtLink n ε H σ Sm E hσ hM μ x).1 hhw.1⟩
  · rintro ν _ ⟨v, hv, rfl⟩ hv0 hwt
    exact hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hWtLink n ε H σ Sm E hσ hM ν v).2 hwt)

theorem comap_kStab (hσ : IsURepOn (UJset ε) σ) (hM : IsSmMod ε σ Sm E) {S' : Submodule ℂ H}
    (hf : FiniteDimensional ℂ S') (hst : IsKStableOn ε σ S') (hle : S' ≤ Sm) :
    KStab ε E (S'.comap Sm.subtype) := by
  have hfinU : FiniteDimensional ℂ (S'.comap Sm.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hle).symm.finiteDimensional
  refine (hStabLink n ε H σ Sm E hσ hM _ hfinU).2 ?_
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hle]
  exact hst

end Rep

open CompanionTheory.D.DSIC (hHWofType hStabLink hSmMod) in
open PI.UpqRep (IsKTypeOf) in

theorem kTypeShift : Formalism.L2.S.S7.CasimirNormBounds.KTypeShift := by
  intro n ε lam H _ _ σ _ hds μ S hS a ha X hX
  obtain ⟨hc, -, hσ, hirr, -⟩ := hds
  haveI := hc
  obtain ⟨Sm, E, hM⟩ := hSmMod n ε H σ hσ
  have hgl := hM.gl
  have hun := kUnit_of hM.unit
  have hsm : ∀ (ν : Fin n → ℝ) (S' : Submodule ℂ H), IsKTypeOf ε σ ν S' → S' ≤ Sm :=
    fun ν S' h v hv =>
      (hM.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n ε H σ hσ hirr v ⟨S', h.1, hv, h.2.1⟩)
  have hSle := hsm μ S hS
  obtain ⟨v, hv0, hvS, hvh⟩ := hHWofType n ε H σ Sm E hσ hM μ S hS hSle
  have hAst : KStab ε E (kLowSpan ε E v) :=
    GlobalTheory.CompanionTheory.KLowSpan.kstab_kLowSpan (fun a b c d _ _ => hgl a b c d) hvh
  have hUst := comap_kStab hσ hM hS.1 hS.2.1 hSle
  have hAU : kLowSpan ε E v ≤ S.comap Sm.subtype := GlobalTheory.CompanionTheory.KLowSpan.kLowSpan_le hUst hvS
  have hUfin : FiniteDimensional ℂ (S.comap Sm.subtype) :=
    haveI := hS.1
    (Submodule.comapSubtypeEquivOfLe hSle).symm.finiteDimensional
  haveI hAfin : FiniteDimensional ℂ (kLowSpan ε E v) := Submodule.finiteDimensional_of_le hAU
  have hAmap : (kLowSpan ε E v).map Sm.subtype = S := by
    have hle : (kLowSpan ε E v).map Sm.subtype ≤ S := Submodule.map_le_iff_le_comap.2 hAU
    rcases hS.2.2.1 _ hle ((hStabLink n ε H σ Sm E hσ hM _ hAfin).1 hAst) with h | h
    · exfalso
      have hmem : (v : H) ∈ (kLowSpan ε E v).map Sm.subtype :=
        ⟨v, GlobalTheory.CompanionTheory.KLowSpan.kself_mem, rfl⟩
      rw [h] at hmem
      exact hv0 (Subtype.ext (by simpa using hmem))
    · exact h
  let M : Submodule ℂ Sm := sSup {L | ∃ (S' : Submodule ℂ H) (μ' : Fin n → ℝ),
    IsKTypeOf ε σ μ' S' ∧ Formalism.REAL.nsq (μ' - μ) ≤ 2 ∧ L = S'.comap Sm.subtype}
  have hMst : KStab ε E M := by
    intro c d he y hy
    have hle : M ≤ M.comap (E c d) := by
      refine sSup_le ?_
      rintro _ ⟨S', μ', h1, h2, rfl⟩ z hz
      exact (le_sSup ⟨S', μ', h1, h2, rfl⟩ : S'.comap Sm.subtype ≤ M)
        (comap_kStab hσ hM h1.1 h1.2.1 (hsm _ _ h1) c d he z hz)
    exact hle hy
  haveI : FiniteDimensional ℂ (nbr E (kLowSpan ε E v)) := nbr_finite _
  have hTM : nbr E (kLowSpan ε E v) ≤ M := by
    refine le_of_highest hgl hun (nbr_stab hgl hAst) hMst ?_
    intro Q hQT hQf hQ ν x hxQ hx0 hx
    obtain ⟨L, hxL, hL⟩ := kType_of_highest hσ hM hx0 hx hQf hQ hxQ
    have hnsq : Formalism.REAL.nsq (ν - μ) ≤ 2 := by
      rcases weight_shift hgl hun hvh.1 hx hx0 (hQT hxQ) with rfl | ⟨a, b, rfl⟩
      · simp [Formalism.REAL.nsq, Formalism.REAL.dot]
      · simpa using nsq_root_le a b
    exact (le_sSup ⟨_, ν, hL, hnsq, rfl⟩ : (L.map Sm.subtype).comap Sm.subtype ≤ M) ⟨x, hxL, rfl⟩
  have haA : (⟨a, hSle ha⟩ : Sm) ∈ kLowSpan ε E v := by
    have hmem : a ∈ (kLowSpan ε E v).map Sm.subtype := by rw [hAmap]; exact ha
    obtain ⟨y, hy, rfl⟩ := hmem
    exact hy
  refine ⟨_, hM.real X hX ⟨a, hSle ha⟩, ?_⟩
  have hMH : M.map Sm.subtype ≤ sSup {S' : Submodule ℂ H | ∃ μ', Formalism.MainNotions.S.IsKTypeOf ε σ μ' S' ∧
      Formalism.REAL.nsq (μ' - μ) ≤ 2} := by
    refine Submodule.map_le_iff_le_comap.2 (sSup_le ?_)
    rintro _ ⟨S', μ', h1, h2, rfl⟩ z hz
    have hmemS : S' ∈ {S' : Submodule ℂ H | ∃ μ', Formalism.MainNotions.S.IsKTypeOf ε σ μ' S' ∧
        Formalism.REAL.nsq (μ' - μ) ≤ 2} := ⟨μ', h1, h2⟩
    exact le_sSup hmemS hz
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (hMH ⟨_, hTM (apply_mem_nbr haA i j), rfl⟩)

end UpperTheory.Lit.Bur.KShift
