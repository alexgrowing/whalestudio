import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeeperCongruenceConjIntoCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorTranslateDeeperLevelEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivariantIsoOfTranslationStableGraphStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeRecon

section SlopeTestRemainingChoices
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem rt_rt {W : Type} [AddCommGroup W] [Module ℂ W] (h h' : GAf L n) (f : GAf L n → W) :
    NG.rt L n h' (NG.rt L n h f) = NG.rt L n (h' * h) f := by
  funext g
  change f (g * h' * h) = f (g * (h' * h))
  rw [mul_assoc]

theorem rt_one {W : Type} [AddCommGroup W] [Module ℂ W] (f : GAf L n → W) : NG.rt L n 1 f = f := by
  funext g
  change f (g * 1) = f g
  rw [mul_one]

theorem finite_cosets (N' : ℕ) (hN' : 0 < N') :
    {c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N' | ∃ x : GAf L n, x ∈ Umax L n ∧
      (x : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') = c}.Finite := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := GlobalTheory.IsotOrth.exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L) N' hN'
  haveI := hQ
  let cls : Umax L n → Fin n → Fin n → Q := fun κ i j => c ⟨(κ.1.1 : Matrix (Fin n) (Fin n) (AL L)) i j, κ.2 i j⟩
  have key : ∀ a b : Umax L n, cls a = cls b →
      ((a.1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') = (b.1 : GAf L n) := by
    intro a b hab
    rw [QuotientGroup.eq]
    exact GlobalTheory.IsotOrth.cong_inv_mul a.2 b.2 (fun i j => by
      obtain ⟨z, hz⟩ := hc _ _ (congrFun (congrFun hab i) j).symm
      refine ⟨z.1, z.2, ?_⟩
      simpa using congrArg Subtype.val hz)
  let F : (Fin n → Fin n → Q) → GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N' := fun q =>
    if h : ∃ a, cls a = q then ((h.choose.1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') else ((1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N')
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨cls ⟨x, hx⟩, ?_⟩
  have h : ∃ a, cls a = cls ⟨x, hx⟩ := ⟨_, rfl⟩
  simp only [F, dif_pos h]
  exact key _ _ h.choose_spec

open Classical in
theorem heckeD_eq_sum {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (f : GAf L n → W) (g : GAf L n) :
    NG.heckeD J D f g = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = c then f (g * hc.choose) else 0) := by
  unfold NG.heckeD
  rw [finsum_eq_sum_of_support_subset]
  intro c hc
  rw [Set.Finite.coe_toFinset]
  by_contra h
  exact hc (dif_neg h)

theorem heckeD_add {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (f f' : GAf L n → W) :
    NG.heckeD J D (f + f') = NG.heckeD J D f + NG.heckeD J D f' := by
  funext g
  rw [Pi.add_apply, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem heckeD_smul {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (a : ℂ) (f : GAf L n → W) :
    NG.heckeD J D (a • f) = a • NG.heckeD J D f := by
  funext g
  rw [Pi.smul_apply, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem heckeD_zero {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n)) :
    NG.heckeD J D (0 : GAf L n → W) = 0 := by
  funext g
  simp [NG.heckeD]

theorem heckeD_one {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (v : GAf L n → W)
    (hv : ∀ κ ∈ J, NG.rt L n κ v = v) :
    NG.heckeD J {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * 1 * u'} v = v := by
  funext g
  unfold NG.heckeD
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ J)]
  · have h : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * 1 * u'},
        (x : GAf L n ⧸ J) = ((1 : GAf L n) : GAf L n ⧸ J) :=
      ⟨1, ⟨1, J.one_mem, 1, J.one_mem, by simp⟩, rfl⟩
    rw [dif_pos h]
    obtain ⟨⟨u, hu, u', hu', e⟩, -⟩ := h.choose_spec
    rw [e]
    have : u * 1 * u' ∈ J := by simpa using J.mul_mem hu hu'
    exact congrFun (hv _ this) g
  · intro c hc
    rw [dif_neg]
    rintro ⟨x, ⟨u, hu, u', hu', rfl⟩, hx⟩
    apply hc
    rw [← hx, QuotientGroup.eq]
    have : u * 1 * u' ∈ J := by simpa using J.mul_mem hu hu'
    simpa using J.inv_mem this

end SlopeTestRemainingChoices

theorem recon : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a b : NG.AlgWt L n) (S₁ : Submodule ℂ (GAf L n → a.W)) (S₂ : Submodule ℂ (GAf L n → b.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep b.ρ S₂ → ∀ N : ℕ, 0 < N → ∀ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → b.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) → (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n a b S₁ S₂ hS₁ hS₂ N hN φ hφ hex hT
  obtain ⟨f₀, hf₀S, hf₀fix, hf₀ne⟩ := hex
  set J := GlobalTheory.IsotOrth.congSub L n N with hJ
  let gens : Set ((GAf L n → a.W) × (GAf L n → b.W)) :=
    {w | ∃ (h : GAf L n) (f : GAf L n → a.W), f ∈ S₁ ∧ (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧
      w = (NG.rt L n h f, NG.rt L n h (φ f))}
  let W := Submodule.span ℂ gens
  have hgen : ∀ (h : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) →
      (NG.rt L n h f, NG.rt L n h (φ f)) ∈ W := fun h f hf hfix => Submodule.subset_span ⟨h, f, hf, hfix, rfl⟩
  have hWS : ∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂ := by
    intro w hw
    have : W ≤ S₁.prod S₂ := by
      rw [Submodule.span_le]
      rintro _ ⟨h, f, hf, hfix, rfl⟩
      exact ⟨hS₁.1.stable h f hf, hS₂.1.stable h _ (hφ f hf hfix).1⟩
    exact this hw
  have hWst : ∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W := by
    intro h w hw
    have : W ≤ W.comap ((NG.rt L n h).prodMap (NG.rt L n h)) := by
      rw [Submodule.span_le]
      rintro _ ⟨h', f, hf, hfix, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.prodMap_apply, rt_rt, rt_rt]
      exact hgen _ f hf hfix
    exact this hw
  have hfinE : ∀ M', 0 < M' → {c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M') |
      ∃ x ∈ (J : Set (GAf L n)), (x : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M')) = c}.Finite := by
    intro M' hM'
    refine (finite_cosets (N * M') (Nat.mul_pos hN hM')).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (show NG.Cong L n N x from hx).1, rfl⟩
  let P : ((GAf L n → a.W) × (GAf L n → b.W)) → Prop := fun w => ∃ M : ℕ, 0 < M ∧ ∀ M', 0 < M' → M ∣ M' →
    NG.heckeD (GlobalTheory.IsotOrth.congSub L n (N * M')) (J : Set (GAf L n)) w.2 =
      φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n (N * M')) (J : Set (GAf L n)) w.1)
  let Good : Submodule ℂ ((GAf L n → a.W) × (GAf L n → b.W)) :=
    { carrier := {w | P w}
      zero_mem' := ⟨1, one_pos, fun M' _ _ => by simp [heckeD_zero]⟩
      add_mem' := by
        rintro w w' ⟨M, hM, hw⟩ ⟨M₁, hM₁, hw'⟩
        refine ⟨M * M₁, Nat.mul_pos hM hM₁, fun M' hM' hd => ?_⟩
        have h1 := hw M' hM' (dvd_trans (dvd_mul_right M M₁) hd)
        have h2 := hw' M' hM' (dvd_trans (dvd_mul_left M₁ M) hd)
        simp only [Prod.fst_add, Prod.snd_add]
        rw [heckeD_add _ _ (hfinE M' hM'), heckeD_add _ _ (hfinE M' hM'), h1, h2, map_add]
      smul_mem' := by
        rintro c w ⟨M, hM, hw⟩
        refine ⟨M, hM, fun M' hM' hd => ?_⟩
        simp only [Prod.smul_fst, Prod.smul_snd]
        rw [heckeD_smul _ _ (hfinE M' hM'), heckeD_smul _ _ (hfinE M' hM'), hw M' hM' hd, map_smul] }
  have hWG : W ≤ Good := by
    rw [Submodule.span_le]
    rintro _ ⟨h, f, hf, hfix, rfl⟩
    obtain ⟨M, hM, hMc⟩ := GlobalTheory.T.exists_deeper_congruence_conj_into_congruence L n N h hN
    refine ⟨M, hM, fun M' hM' hd => ?_⟩
    obtain ⟨k, rfl⟩ := hd
    have hconj : ∀ κ ∈ GlobalTheory.IsotOrth.congSub L n (N * (M * k)), h⁻¹ * κ * h ∈ J := by
      intro κ hκ
      rw [← mul_assoc] at hκ
      exact hMc κ (NG.Cong.of_mul_left L n hκ)
    have hle : GlobalTheory.IsotOrth.congSub L n (N * (M * k)) ≤ J := fun κ hκ => NG.Cong.of_mul_left L n hκ
    obtain ⟨m, -, hmE⟩ := GlobalTheory.T.doubleCosetOperator_translate_deeper_level_eq_smul L n J (GlobalTheory.IsotOrth.congSub L n (N * (M * k))) h hle hconj (hfinE _ hM')
    have hfixJ : ∀ κ ∈ J, NG.rt L n κ f = f := fun κ hκ => hfix κ hκ
    have hφfixJ : ∀ κ ∈ J, NG.rt L n κ (φ f) = φ f := fun κ hκ => (hφ f hf hfix).2 κ hκ
    show NG.heckeD _ _ (NG.rt L n h (φ f)) = φ (NG.heckeD _ _ (NG.rt L n h f))
    rw [hmE _ f hfixJ, hmE _ (φ f) hφfixJ, map_smul, hT h f hf hfix]
  have hWP : ∀ w ∈ W, P w := fun w hw => hWG hw
  have hK2 : ∀ u, ((0 : GAf L n → a.W), u) ∈ W → u = 0 := by
    let K : Submodule ℂ (GAf L n → b.W) := W.comap (LinearMap.inr ℂ _ _)
    have hKsub : NG.IsSubrep b.ρ K := ⟨fun u hu => hS₂.1.le (hWS _ hu).2, fun h u hu => by
      have := hWst h _ hu
      simpa [K] using this⟩
    have hKle : K ≤ S₂ := fun u hu => (hWS _ hu).2
    rcases hS₂.2.2 K hKsub hKle with hK | hK
    · intro u hu
      have : u ∈ K := hu
      rwa [hK, Submodule.mem_bot] at this
    · exfalso
      have hmem : φ f₀ ∈ K := hK ▸ (hφ f₀ hf₀S hf₀fix).1
      obtain ⟨M, hM, hMg⟩ := hWP _ (Submodule.mem_comap.1 hmem)
      have e := hMg M hM dvd_rfl
      obtain ⟨m, hm, hmE⟩ := GlobalTheory.T.doubleCosetOperator_translate_deeper_level_eq_smul L n J (GlobalTheory.IsotOrth.congSub L n (N * M)) 1
        (fun κ hκ => NG.Cong.of_mul_left L n hκ)
        (fun κ hκ => by rw [inv_one, one_mul, mul_one]; exact NG.Cong.of_mul_left L n hκ) (hfinE M hM)
      have hφfixJ : ∀ κ ∈ J, NG.rt L n κ (φ f₀) = φ f₀ := fun κ hκ => (hφ f₀ hf₀S hf₀fix).2 κ hκ
      have e2 := hmE _ (φ f₀) hφfixJ
      rw [rt_one, heckeD_one J _ hφfixJ] at e2
      simp only [LinearMap.inr_apply, heckeD_zero, map_zero] at e
      rw [e] at e2
      apply hf₀ne
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      exact (smul_eq_zero.1 e2.symm).resolve_left hm'
  have hK1 : ∀ u, (u, (0 : GAf L n → b.W)) ∈ W → u = 0 := by
    let K : Submodule ℂ (GAf L n → a.W) := W.comap (LinearMap.inl ℂ _ _)
    have hKsub : NG.IsSubrep a.ρ K := ⟨fun u hu => hS₁.1.le (hWS _ hu).1, fun h u hu => by
      have := hWst h _ hu
      simpa [K] using this⟩
    have hKle : K ≤ S₁ := fun u hu => (hWS _ hu).1
    rcases hS₁.2.2 K hKsub hKle with hK | hK
    · intro u hu
      have : u ∈ K := hu
      rwa [hK, Submodule.mem_bot] at this
    · exfalso
      have hmem : f₀ ∈ K := hK ▸ hf₀S
      have h1 : (f₀, (0 : GAf L n → b.W)) ∈ W := hmem
      have h2 := hgen 1 f₀ hf₀S hf₀fix
      rw [rt_one, rt_one] at h2
      have h3 := W.sub_mem h2 h1
      simp only [Prod.mk_sub_mk, sub_self, sub_zero] at h3
      exact hf₀ne (hK2 _ h3)
  refine GlobalTheory.T.equivariant_iso_of_translationStable_graph L n a.ρ b.ρ S₁ S₂ W hS₁ hS₂ hWS hWst hK2 hK1 ?_
  intro hbot
  have := hgen 1 f₀ hf₀S hf₀fix
  rw [hbot, Submodule.mem_bot, rt_one, rt_one] at this
  exact hf₀ne (congrArg Prod.snd this)

end GlobalTheory.HeckeRecon
