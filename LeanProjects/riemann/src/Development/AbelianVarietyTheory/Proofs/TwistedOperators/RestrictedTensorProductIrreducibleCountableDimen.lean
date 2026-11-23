import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIrreducibleOfCountableDimensionIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RestrTensIrr

open GlobalTheory.SmallThetaModules Formalism.MainNotions.KudlaSiegelWeil

variable {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

def fin (s ξ₀ : ∀ i, N i) (S : Finset ι) : Submodule ℂ (RTens s) :=
  Submodule.span ℂ {z | ∃ ξ, (∀ i ∉ S, ξ i = ξ₀ i) ∧ z = pureT s ξ}

theorem restr_of {s ξ₀ ξ : ∀ i, N i} (h0 : Restr s ξ₀) (S : Finset ι) (h : ∀ i ∉ S, ξ i = ξ₀ i) :
    Restr s ξ := by
  refine (h0.union S.finite_toSet).subset fun i hi => ?_
  by_cases hS : i ∈ S
  · exact Or.inr hS
  · left
    simp only [Set.mem_setOf_eq] at hi ⊢
    rwa [h i hS] at hi

theorem fin_mono (s ξ₀ : ∀ i, N i) {S T : Finset ι} (h : S ⊆ T) : fin s ξ₀ S ≤ fin s ξ₀ T := by
  refine Submodule.span_mono ?_
  rintro _ ⟨ξ, hξ, rfl⟩
  exact ⟨ξ, fun i hi => hξ i fun h' => hi (h h'), rfl⟩

theorem fin_stable {s ξ₀ : ∀ i, N i} (h0 : Restr s ξ₀) (S : Finset ι) {i : ι} (hi : i ∈ S)
    (T : Module.End ℂ (RTens s)) (a : Module.End ℂ (N i))
    (hT : ∀ ξ, Restr s ξ → T (pureT s ξ) = pureT s (Function.update ξ i (a (ξ i)))) :
    ∀ x ∈ fin s ξ₀ S, T x ∈ fin s ξ₀ S := by
  have : fin s ξ₀ S ≤ (fin s ξ₀ S).comap T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rw [hT ξ (restr_of h0 S hξ)]
    refine Submodule.subset_span ⟨_, fun k hk => ?_, rfl⟩
    rw [Function.update_of_ne (show k ≠ i by rintro rfl; exact hk hi)]
    exact hξ k hk
  exact fun x hx => this hx

theorem exists_ins (s : ∀ i, N i) (j : ι) (f : N j →ₗ[ℂ] ℂ) (n : N j) :
    ∃ T : Module.End ℂ (RTens s), ∀ ξ, Restr s ξ →
      T (pureT s ξ) = pureT s (Function.update ξ j (f (ξ j) • n)) := by
  obtain ⟨T, hT⟩ := GlobalTheory.TripleAssembly.exists_rtensOp s
    (Function.update (fun i => (LinearMap.id : Module.End ℂ (N i))) j (f.smulRight n))
  refine ⟨T, fun ξ hξ => ?_⟩
  rw [hT ξ hξ]
  congr 1
  funext i
  by_cases h : i = j
  · subst h
    simp
  · simp [Function.update_of_ne h]

def ins (s : ∀ i, N i) (j : ι) (f : N j →ₗ[ℂ] ℂ) (n : N j) : Module.End ℂ (RTens s) :=
  (exists_ins s j f n).choose

theorem ins_pure (s : ∀ i, N i) (j : ι) (f : N j →ₗ[ℂ] ℂ) (n : N j) (ξ : ∀ i, N i) (hξ : Restr s ξ) :
    ins s j f n (pureT s ξ) = pureT s (Function.update ξ j (f (ξ j) • n)) :=
  (exists_ins s j f n).choose_spec ξ hξ

theorem pureT_zero (s : ∀ i, N i) (ξ : ∀ i, N i) (hξ : Restr s ξ) (j : ι) :
    pureT s (Function.update ξ j 0) = 0 := by
  have h := pureT_mlin hξ j 1 0 0
  rw [one_smul, add_zero] at h
  simpa using h.symm

def insL (s : ∀ i, N i) (j : ι) (f : N j →ₗ[ℂ] ℂ) : N j →ₗ[ℂ] Module.End ℂ (RTens s) where
  toFun := ins s j f
  map_add' n m := by
    refine LinearMap.ext_on (pureT_span s) ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    simp only [LinearMap.add_apply, ins_pure s j f _ ξ hξ, smul_add]
    have h := pureT_mlin hξ j 1 (f (ξ j) • n) (f (ξ j) • m)
    rwa [one_smul, one_smul] at h
  map_smul' c n := by
    refine LinearMap.ext_on (pureT_span s) ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    simp only [LinearMap.smul_apply, RingHom.id_apply, ins_pure s j f _ ξ hξ]
    have h := pureT_mlin hξ j c (f (ξ j) • n) 0
    rw [add_zero, pureT_zero s ξ hξ, add_zero] at h
    rw [smul_comm, h]

def phi (s ξ₀ : ∀ i, N i) (S : Finset ι) (j : ι) (f : N j →ₗ[ℂ] ℂ) : N j ⊗[ℂ] fin s ξ₀ S →ₗ[ℂ] RTens s :=
  TensorProduct.lift ((insL s j f).compl₂ (fin s ξ₀ S).subtype)

theorem phi_tmul (s ξ₀ : ∀ i, N i) (S : Finset ι) (j : ι) (f : N j →ₗ[ℂ] ℂ) (n : N j) (y : fin s ξ₀ S) :
    phi s ξ₀ S j f (n ⊗ₜ y) = ins s j f n y := rfl

theorem claim {s ξ₀ : ∀ i, N i} (h0 : Restr s ξ₀) (hne : ∀ i, ξ₀ i ≠ 0)
    (hrank : ∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) (hnt : ∀ i, Nontrivial (N i))
    (Sv : ∀ i, Set (Module.End ℂ (N i)))
    (hirr : ∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (RTens s))
    (hOp : ∀ i, ∀ a ∈ Sv i, ∀ ξ, Restr s ξ →
      Op i a (pureT s ξ) = pureT s (Function.update ξ i (a (ξ i))))
    (S : Finset ι) : ∀ Q : Submodule ℂ (RTens s), (∀ i ∈ S, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) →
      ∀ x ∈ fin s ξ₀ S, x ∈ Q → x ≠ 0 → fin s ξ₀ S ≤ Q := by
  induction S using Finset.induction_on with
  | empty =>
    intro Q _ x hx hxQ hx0
    have hle : fin s ξ₀ ∅ ≤ ℂ ∙ pureT s ξ₀ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨ξ, hξ, rfl⟩
      have : ξ = ξ₀ := funext fun i => hξ i (Finset.notMem_empty i)
      subst this
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hle hx)
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx0 (zero_smul _ _)
    have hp : pureT s ξ₀ ∈ Q := by
      have := Q.smul_mem c⁻¹ hxQ
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    exact hle.trans ((Submodule.span_singleton_le_iff_mem _ _).mpr hp)
  | insert j S' hj IH =>
    intro Q hQ x hx hxQ hx0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ (hne j)
    have hrange : fin s ξ₀ (insert j S') ≤ LinearMap.range (phi s ξ₀ S' j f) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨ξ, hξ, rfl⟩
      have hη : ∀ i ∉ S', Function.update ξ j (ξ₀ j) i = ξ₀ i := by
        intro i hi
        by_cases e : i = j
        · subst e
          simp
        · rw [Function.update_of_ne e]
          exact hξ i (by simp [e, hi])
      refine ⟨ξ j ⊗ₜ ⟨pureT s (Function.update ξ j (ξ₀ j)), Submodule.subset_span ⟨_, hη, rfl⟩⟩, ?_⟩
      rw [phi_tmul]
      show ins s j f (ξ j) (pureT s (Function.update ξ j (ξ₀ j))) = pureT s ξ
      rw [ins_pure s j f _ _ (restr_of h0 S' hη), Function.update_self, hf, one_smul]
      simp
    have hΦj : ∀ a ∈ Sv j, (phi s ξ₀ S' j f).comp (LinearMap.rTensor (fin s ξ₀ S') a) =
        (Op j a).comp (phi s ξ₀ S' j f) := by
      intro a ha
      refine TensorProduct.ext' fun n y => ?_
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, phi_tmul]
      have key : Set.EqOn (ins s j f (a n)) ((Op j a).comp (ins s j f n))
          {z | ∃ ξ, (∀ i ∉ S', ξ i = ξ₀ i) ∧ z = pureT s ξ} := by
        rintro _ ⟨η, hη, rfl⟩
        have hr := restr_of h0 S' hη
        simp only [LinearMap.comp_apply]
        rw [ins_pure s j f _ η hr, ins_pure s j f _ η hr, hOp j a ha _ (restr_update hr j _)]
        simp [hη j hj, hf]
      exact LinearMap.eqOn_span' key y.2
    have hΦi : ∀ b ∈ {b : Module.End ℂ (fin s ξ₀ S') | ∃ i ∈ S', ∃ a ∈ Sv i,
        ∀ y : fin s ξ₀ S', (b y : RTens s) = Op i a y}, ∃ i ∈ insert j S', ∃ a ∈ Sv i,
        (phi s ξ₀ S' j f).comp (LinearMap.lTensor (N j) b) = (Op i a).comp (phi s ξ₀ S' j f) := by
      rintro b ⟨i, hi, a, ha, hb⟩
      refine ⟨i, Finset.mem_insert_of_mem hi, a, ha, TensorProduct.ext' fun n y => ?_⟩
      simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, phi_tmul, hb]
      have hij : i ≠ j := by
        rintro rfl
        exact hj hi
      have key : Set.EqOn ((ins s j f n).comp (Op i a)) ((Op i a).comp (ins s j f n))
          {z | ∃ ξ, (∀ i ∉ S', ξ i = ξ₀ i) ∧ z = pureT s ξ} := by
        rintro _ ⟨η, hη, rfl⟩
        have hr := restr_of h0 S' hη
        simp only [LinearMap.comp_apply]
        rw [hOp i a ha η hr, ins_pure s j f _ _ (restr_update hr i _), ins_pure s j f _ η hr,
          hOp i a ha _ (restr_update hr j _), Function.update_of_ne hij.symm, Function.update_of_ne hij,
          hη j hj, hf, one_smul, Function.update_comm hij]
      exact LinearMap.eqOn_span' key y.2
    have hU : ∀ M : Submodule ℂ (fin s ξ₀ S'), (∀ b ∈ {b : Module.End ℂ (fin s ξ₀ S') | ∃ i ∈ S', ∃ a ∈ Sv i,
        ∀ y : fin s ξ₀ S', (b y : RTens s) = Op i a y}, ∀ y ∈ M, b y ∈ M) → M = ⊥ ∨ M = ⊤ := by
      intro M hM
      by_cases hM0 : M = ⊥
      · exact Or.inl hM0
      right
      obtain ⟨y, hyM, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
      have hst : ∀ i ∈ S', ∀ a ∈ Sv i, ∀ z ∈ M.map (fin s ξ₀ S').subtype,
          Op i a z ∈ M.map (fin s ξ₀ S').subtype := by
        rintro i hi a ha _ ⟨w, hw, rfl⟩
        let b : Module.End ℂ (fin s ξ₀ S') :=
          (Op i a).restrict (fin_stable h0 S' hi (Op i a) a (hOp i a ha))
        exact ⟨b w, hM b ⟨i, hi, a, ha, fun _ => rfl⟩ w hw, rfl⟩
      have hle := IH (M.map (fin s ξ₀ S').subtype) hst y y.2 ⟨y, hyM, rfl⟩ (by simpa using hy0)
      rw [eq_top_iff]
      intro w _
      obtain ⟨w', hw', he⟩ := hle w.2
      have : w' = w := Subtype.ext he
      rwa [← this]
    have hN := GlobalTheory.T.tensor_irreducible_of_countable_dimension_irreducible (N j) (fin s ξ₀ S') (Sv j) _ (hrank j) (hnt j) (hirr j) hU
      (Q.comap (phi s ξ₀ S' j f))
      (fun a ha t ht => by
        rw [Submodule.mem_comap] at ht ⊢
        rw [← LinearMap.comp_apply, hΦj a ha, LinearMap.comp_apply]
        exact hQ j (Finset.mem_insert_self j S') a ha _ ht)
      (fun b hb t ht => by
        obtain ⟨i, hi, a, ha, e⟩ := hΦi b hb
        rw [Submodule.mem_comap] at ht ⊢
        rw [← LinearMap.comp_apply, e, LinearMap.comp_apply]
        exact hQ i hi a ha _ ht)
    obtain ⟨t, rfl⟩ := hrange hx
    rcases hN with hN | hN
    · exfalso
      have ht : t ∈ Q.comap (phi s ξ₀ S' j f) := hxQ
      rw [hN, Submodule.mem_bot] at ht
      exact hx0 (by rw [ht, map_zero])
    · refine hrange.trans ?_
      rintro _ ⟨t', rfl⟩
      have ht : t' ∈ Q.comap (phi s ξ₀ S' j f) := by
        rw [hN]
        trivial
      exact ht

end GlobalTheory.RestrTensIrr

theorem GlobalTheory.rtens_irreducible : ∀ {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i),
    {i | s i = 0}.Finite → (∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (N i)) →
    ∀ Sv : ∀ i, Set (Module.End ℂ (N i)),
    (∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤) →
    ∀ Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s),
    (∀ i, ∀ a ∈ Sv i, ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      Op i a (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (Function.update ξ i (a (ξ i)))) →
    ∀ Q : Submodule ℂ (GlobalTheory.SmallThetaModules.RTens s), (∀ i, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
  intro ι _ N _ _ s hs hrank hnt Sv hirr Op hOp Q hQ
  classical
  by_cases hQ0 : Q = ⊥
  · exact Or.inl hQ0
  right
  choose e he using fun i => exists_ne (0 : N i)
  let ξ₀ : ∀ i, N i := fun i => if s i = 0 then e i else s i
  have hne : ∀ i, ξ₀ i ≠ 0 := by
    intro i
    by_cases h : s i = 0
    · simp [ξ₀, h, he i]
    · simp [ξ₀, h]
  have h0 : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ₀ := hs.subset fun i hi => by
    by_contra h
    simp only [Set.mem_setOf_eq] at h hi
    exact hi (by simp [ξ₀, h])
  have hfinS : ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ → ∃ S : Finset ι, ∀ i ∉ S, ξ i = ξ₀ i := by
    intro ξ hξ
    refine ⟨(hξ.union h0).toFinset, fun i hi => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hi
    rw [hi.1, hi.2]
  have hall : ∀ x : GlobalTheory.SmallThetaModules.RTens s, ∃ S, x ∈ GlobalTheory.RestrTensIrr.fin s ξ₀ S := by
    intro x
    have hx : x ∈ Submodule.span ℂ {z | ∃ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ ∧ z = GlobalTheory.SmallThetaModules.pureT s ξ} := by
      rw [GlobalTheory.SmallThetaModules.pureT_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ξ, hξ, rfl⟩ := hz
      obtain ⟨S, hS⟩ := hfinS ξ hξ
      exact ⟨S, Submodule.subset_span ⟨ξ, hS, rfl⟩⟩
    | zero => exact ⟨∅, Submodule.zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨S, hS⟩ := ha
      obtain ⟨T, hT⟩ := hb
      exact ⟨S ∪ T, Submodule.add_mem _ (GlobalTheory.RestrTensIrr.fin_mono s ξ₀ Finset.subset_union_left hS)
        (GlobalTheory.RestrTensIrr.fin_mono s ξ₀ Finset.subset_union_right hT)⟩
    | smul c a _ ha =>
      obtain ⟨S, hS⟩ := ha
      exact ⟨S, Submodule.smul_mem _ c hS⟩
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  obtain ⟨S, hxS⟩ := hall x
  rw [eq_top_iff, ← GlobalTheory.SmallThetaModules.pureT_span s, Submodule.span_le]
  rintro _ ⟨ξ, hξ, rfl⟩
  obtain ⟨T, hT⟩ := hfinS ξ hξ
  have hle := GlobalTheory.RestrTensIrr.claim h0 hne hrank hnt Sv hirr Op hOp (S ∪ T) Q
    (fun i _ a ha y hy => hQ i a ha y hy) x
    (GlobalTheory.RestrTensIrr.fin_mono s ξ₀ Finset.subset_union_left hxS) hxQ hx0
  exact hle (GlobalTheory.RestrTensIrr.fin_mono s ξ₀ Finset.subset_union_right (Submodule.subset_span ⟨ξ, hT, rfl⟩))

end
