import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealIsMultiProjPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

noncomputable section

section Graded

variable (S : Type) [CommRing S] (N : ℕ)

theorem mem_polyPiece_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    f ∈ IndefiniteRowSideFullHecke.Kleiman.polyPiece S N e := by
  rw [IndefiniteRowSideFullHecke.Kleiman.polyPiece, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_int_of_isHomogeneous hf

theorem eq_zero_or_isHomogeneous_of_mem_polyPiece {f : Poly S N} {d : ℤ}
    (hf : f ∈ IndefiniteRowSideFullHecke.Kleiman.polyPiece S N d) :
    f = 0 ∨ ∃ e : ℕ, (e : ℤ) = d ∧ f.IsHomogeneous e := by
  classical
  rw [IndefiniteRowSideFullHecke.Kleiman.polyPiece, mem_weightedHomogeneousSubmodule] at hf
  have hw : ∀ s : Fin (N + 1) →₀ ℕ,
      Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) s = ((Finsupp.weight (1 : Fin (N + 1) → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp [Finsupp.weight_apply, Finsupp.sum]
  by_cases h0 : f = 0
  · exact Or.inl h0
  · right
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp h0
    refine ⟨Finsupp.weight (1 : Fin (N + 1) → ℕ) s, ?_, ?_⟩
    · rw [← hw]; exact hf hs
    · intro t ht
      have h1 := hf ht
      have h2 := hf hs
      rw [hw] at h1 h2
      exact_mod_cast h1.trans h2.symm

variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

def gradedEquiv : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M ≃ Kleiman.GradedPMod S N M where
  toFun G :=
    { piece := G.piece
      isInternal := G.internal
      smul_mem := fun d c p m hp hm => by
        rw [add_comm]
        exact G.smul_mem d c p (mem_polyPiece_of_isHomogeneous S N hp) m hm }
  invFun G :=
    { piece := G.piece
      internal := G.isInternal
      smul_mem := fun d c f hf m hm => by
        rcases eq_zero_or_isHomogeneous_of_mem_polyPiece S N hf with rfl | ⟨e, rfl, he⟩
        · rw [zero_smul]; exact zero_mem _
        · rw [add_comm]; exact G.smul_mem e c f m he hm }
  left_inv _ := rfl
  right_inv _ := rfl

theorem GradedMod.equiv (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) : (gradedEquiv S N M G).piece = G.piece :=
  rfl

theorem polyGraded.equiv :
    gradedEquiv S N (Poly S N) (IndefiniteRowSideFullHecke.Kleiman.polyGraded S N) = Kleiman.polyGraded S N :=
  rfl

theorem IsGradedHom.equiv {M' : Type} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
    [IsScalarTower S (Poly S N) M'] (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (G' : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M')
    (f : M →ₗ[Poly S N] M') :
    IndefiniteRowSideFullHecke.Kleiman.IsGradedHom S N G G' f ↔
      ∃ g : Kleiman.GradedHom (gradedEquiv S N M G) (gradedEquiv S N M' G'), g.toLin = f :=
  ⟨fun hf => ⟨⟨f, fun c m hm => hf c m hm⟩, rfl⟩, fun ⟨g, hg⟩ c m hm => hg ▸ g.map_piece c m hm⟩

end Graded

section Charts

variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem pow_div_mem_chartRingI (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) (i₀ : Fin (N + 1))
    {s : Poly S N} (hs : s ∈ Kleiman.monos I.1) :
    ∃ e : ℕ, s.IsHomogeneous e ∧ x i₀ ^ e / aeval x s ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨1, isHomogeneous_X S i, ?_⟩
    rw [pow_one, aeval_X]
    exact Algebra.subset_adjoin ⟨i, hi, i₀, rfl⟩
  | one => exact ⟨0, isHomogeneous_one _ _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨e, hae, hea⟩ := ha
    obtain ⟨e', hbe, heb⟩ := hb
    refine ⟨e + e', hae.mul hbe, ?_⟩
    have : x i₀ ^ (e + e') / aeval x (a * b) = (x i₀ ^ e / aeval x a) * (x i₀ ^ e' / aeval x b) := by
      rw [map_mul, pow_add, mul_div_mul_comm]
    rw [this]
    exact mul_mem hea heb

theorem chartRingI.equiv (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) :
    IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 = Kleiman.chartRing S x I := by
  apply le_antisymm
  · rw [IndefiniteRowSideFullHecke.Kleiman.chartRingI, Algebra.adjoin_le_iff]
    rintro _ ⟨i, hi, j, rfl⟩
    exact ⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩
  · rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨i₀, hi₀⟩ := I.2.1
    have hx₀ : x i₀ ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi₀)
    have hs0 : aeval x s ≠ 0 := Kleiman.eval_ne_zero_of_mem_monos I hs
    have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
    obtain ⟨e', hse', hmem⟩ := pow_div_mem_chartRingI S x I i₀ hs
    have hee : e = e' := hse.inj_right hse' hsne
    subst hee
    have hall : ∀ g : Poly S N, aeval (fun l => x l / x i₀) g ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul, aeval_X]
        exact mul_mem hp (Algebra.subset_adjoin ⟨i₀, hi₀, i, rfl⟩)
    have hf' : aeval x f / x i₀ ^ e ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
      rw [← Kleiman.aeval_div_of_isHomogeneous hf i₀]
      exact hall f
    have heq : aeval x f / aeval x s = (aeval x f / x i₀ ^ e) * (x i₀ ^ e / aeval x s) := by
      field_simp
    rw [heq]
    exact mul_mem hf' hmem

theorem chartRing.equiv (x : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart hi) := by
  rw [← IndefiniteRowSideFullHecke.Kleiman.chartRingI_singleton, ← chartRingI.equiv]
  rfl

theorem dimCl.equiv (k : Type) [Field k] [Algebra k Ω] (x : Fin (N + 1) → Ω) :
    IndefiniteRowSideFullHecke.Kleiman.dimCl k x = Kleiman.dimCl k x :=
  rfl

theorem lineX.equiv (k : Type) [Field k] : IndefiniteRowSideFullHecke.Kleiman.lineX k = Kleiman.lineX k :=
  rfl

end Charts

section Families

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

open Classical in

def toIndefiniteRowSideFullHecke (F : Kleiman.SubSystem S x E) (i : Fin (N + 1)) : Submodule S E :=
  if h : x i ≠ 0 then (F.sub (Kleiman.singleChart h)).restrictScalars S else ⊥

theorem chartModule_of_ne_zero (F : Kleiman.SubSystem S x E) {i : Fin (N + 1)} (h : x i ≠ 0) :
    toIndefiniteRowSideFullHecke F i = (F.sub (Kleiman.singleChart h)).restrictScalars S :=
  dif_pos h

theorem secs.equiv (F : Kleiman.SubSystem S x E) : IndefiniteRowSideFullHecke.Kleiman.secs S x (toIndefiniteRowSideFullHecke F) = F.secs := by
  apply le_antisymm
  · intro y hy
    simp only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf] at hy
    rw [Kleiman.SubSystem.secs, Submodule.mem_iInf]
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have h1 := hy i hxi
    rw [chartModule_of_ne_zero F hxi] at h1
    exact F.mono _ I (Finset.singleton_subset_iff.mpr hi) y h1
  · intro y hy
    rw [Kleiman.SubSystem.secs, Submodule.mem_iInf] at hy
    simp only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf]
    intro i hxi
    rw [chartModule_of_ne_zero F hxi]
    exact hy _

theorem mem_twistA_iff (F : Fin (N + 1) → Submodule S E) (c : ℤ) (i : Fin (N + 1)) (z : E) :
    z ∈ IndefiniteRowSideFullHecke.Kleiman.twistA S x F c i ↔ ∃ y ∈ F i, z = x i ^ c • y := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨y, hy, rfl⟩ := hz; exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨y', hy', rfl⟩ := hb
      exact ⟨y + y', add_mem hy hy', (smul_add _ _ _).symm⟩
    | smul s a _ ha =>
      obtain ⟨y, hy, rfl⟩ := ha
      exact ⟨s • y, Submodule.smul_mem _ s hy, smul_comm s (x i ^ c) y⟩
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

omit [Module S E] [IsScalarTower S Ω E] in

theorem mem_twist_twistSys_iff (F : Kleiman.SubSystem S x E) (c : ℤ) (I : Kleiman.Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (z : E) :
    z ∈ (F.twist (Kleiman.twistSys S x c)).sub I ↔ ∃ y ∈ F.sub I, z = x i ^ c • y := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, hq, y, hy, rfl⟩ := hz
      change q ∈ Kleiman.twistMod S x c I at hq
      rw [Kleiman.twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
      rw [Kleiman.chartRing_smul_def, mul_smul]
      exact smul_comm _ _ _
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨y', hy', rfl⟩ := hb
      exact ⟨y + y', add_mem hy hy', (smul_add _ _ _).symm⟩
    | smul a w _ hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_comm]
  · rintro ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨x i ^ c, ?_, y, hy, rfl⟩
    change x i ^ c ∈ Kleiman.twistMod S x c I
    rw [Kleiman.twistMod_eq_span c I hi]
    exact Submodule.mem_span_singleton_self _

theorem twist.equiv (F : Kleiman.SubSystem S x E) (c : ℤ) {i : Fin (N + 1)} (h : x i ≠ 0) :
    IndefiniteRowSideFullHecke.Kleiman.twistA S x (toIndefiniteRowSideFullHecke F) c i = toIndefiniteRowSideFullHecke (F.twist (Kleiman.twistSys S x c)) i := by
  ext z
  rw [mem_twistA_iff, chartModule_of_ne_zero F h, chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem,
    mem_twist_twistSys_iff F c (Kleiman.singleChart h) (Finset.mem_singleton_self i)]
  rfl

theorem span_image2_eq (A : Subalgebra S Ω) (T : Set E) :
    Submodule.span S (Set.image2 (· • ·) (A : Set Ω) T) = (Submodule.span A T).restrictScalars S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, y, hy, rfl⟩
    exact Submodule.smul_mem (Submodule.span A T) (⟨a, ha⟩ : A) (Submodule.subset_span hy)
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨1, one_mem A, y, hy, one_smul Ω y⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul a w hw0 hw =>
      clear hw0
      induction hw using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a', ha', y, hy, rfl⟩ := hz
        exact Submodule.subset_span ⟨(a : Ω) * a', mul_mem a.2 ha', y, hy, mul_smul _ _ _⟩
      | zero => rw [smul_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
      | smul s u _ hu =>
        show (a : Ω) • (s • u) ∈ _
        rw [smul_comm]
        exact Submodule.smul_mem _ s hu

theorem Generated.equiv (F : Kleiman.SubFamily S x E) :
    IndefiniteRowSideFullHecke.Kleiman.IsGenerated S x (toIndefiniteRowSideFullHecke F.toSubSystem) ↔ F.toSubSystem.Generated := by
  have key : ∀ {i : Fin (N + 1)} (h : x i ≠ 0),
      Submodule.span S (Set.image2 (· • ·) (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i : Set Ω)
        (IndefiniteRowSideFullHecke.Kleiman.secs S x (toIndefiniteRowSideFullHecke F.toSubSystem) : Set E)) =
      (Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart h)) (F.secs : Set E)).restrictScalars S := by
    intro i h
    rw [secs.equiv, chartRing.equiv S x h]
    exact span_image2_eq _ _
  constructor
  · intro hg I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have hsub : {i} ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
    have hi' : F.sub (Kleiman.singleChart hxi) =
        Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (F.secs : Set E) := by
      have := hg i hxi
      rw [key hxi, chartModule_of_ne_zero _ hxi] at this
      exact Submodule.restrictScalars_injective S _ _ this
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      rw [Kleiman.SubSystem.secs, SetLike.mem_coe, Submodule.mem_iInf] at hy
      exact hy I
    · intro y hy
      obtain ⟨a, ⟨u, hu⟩, hay⟩ := (F.mem_iff (Kleiman.singleChart hxi) I hsub y).mp hy
      rw [hi'] at hay
      have hmono : ∀ w ∈ Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hxi)) (F.secs : Set E),
          w ∈ Submodule.span (Kleiman.chartRing S x I) (F.secs : Set E) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem z hz => exact Submodule.subset_span hz
        | zero => exact zero_mem _
        | add u v _ _ hu hv => exact add_mem hu hv
        | smul b w _ hw =>
          have : b • w = (Kleiman.chartIncl hsub b) • w := rfl
          rw [this]
          exact Submodule.smul_mem _ _ hw
      have hay' := hmono _ hay
      have hinv : ((↑u⁻¹ : Kleiman.chartRing S x I) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy' : y = (↑u⁻¹ : Kleiman.chartRing S x I) • ((a : Ω) • y) := by
        rw [Subalgebra.smul_def, ← mul_smul, hinv, one_smul]
      rw [hy']
      exact Submodule.smul_mem _ _ hay'
  · intro hg i hxi
    rw [key hxi, chartModule_of_ne_zero _ hxi, hg]

theorem bundleA.equiv {i : Fin (N + 1)} (h : x i ≠ 0) :
    (IndefiniteRowSideFullHecke.Kleiman.bundleA S x).mods i = toIndefiniteRowSideFullHecke (Kleiman.twistSys S x 1) i := by
  ext z
  rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem]
  change z ∈ Submodule.span S (((Subalgebra.toSubmodule (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i)).map
      (LinearMap.mulRight S (x i ^ (1 : ℕ))) : Submodule S Ω) : Set Ω) ↔
    z ∈ Kleiman.twistMod S x 1 (Kleiman.singleChart h)
  rw [Submodule.span_eq, Kleiman.twistMod_eq_span 1 _ (Finset.mem_singleton_self i), zpow_one,
    Submodule.mem_span_singleton, Submodule.mem_map, chartRing.equiv S x h]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, by simp [Kleiman.chartRing_smul_def]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, by simp [Kleiman.chartRing_smul_def]⟩

theorem mul_eq_twist (P Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    (P.sub I).restrictScalars S * (Q.sub I).restrictScalars S = ((P.twist Q).sub I).restrictScalars S := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro p hp q hq
    exact Submodule.subset_span ⟨q, hq, p, hp, by rw [smul_eq_mul, mul_comm]⟩
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, hq, y, hy, rfl⟩ := hz
      rw [show q • y = y * q from mul_comm q y]
      exact Submodule.mul_mem_mul hy hq
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul a w hw0 hw =>
      clear hw0
      refine Submodule.mul_induction_on hw (fun p hp q hq => ?_) (fun u v hu hv => ?_)
      · have : a • (p * q) = (a • p) * q := by
          rw [Kleiman.chartRing_smul_def, Kleiman.chartRing_smul_def, mul_assoc]
        rw [this]
        exact Submodule.mul_mem_mul (Submodule.smul_mem _ a hp) hq
      · rw [smul_add]; exact add_mem hu hv

theorem lmul.equiv (P Q : Kleiman.SubSystem S x Ω) {i : Fin (N + 1)} (h : x i ≠ 0) :
    IndefiniteRowSideFullHecke.Kleiman.lmul S (toIndefiniteRowSideFullHecke P) (toIndefiniteRowSideFullHecke Q) i = toIndefiniteRowSideFullHecke (P.twist Q) i := by
  rw [IndefiniteRowSideFullHecke.Kleiman.lmul, chartModule_of_ne_zero _ h, chartModule_of_ne_zero _ h, chartModule_of_ne_zero _ h]
  exact mul_eq_twist P Q _

theorem lpow_zero (Q : Fin (N + 1) → Submodule S Ω) (i : Fin (N + 1)) : IndefiniteRowSideFullHecke.Kleiman.lpow S Q 0 i = 1 :=
  pow_zero _

theorem pow_zero_sub (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) (z : Ω) :
    z ∈ (Q.pow 0).sub I ↔ z ∈ Kleiman.chartRing S x I := by
  obtain ⟨i, hi⟩ := I.2.1
  change z ∈ Kleiman.twistMod S x 0 I ↔ _
  rw [Kleiman.twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Kleiman.chartRing_smul_def, mul_one]
    exact a.2
  · intro hz
    exact ⟨⟨z, hz⟩, by rw [Kleiman.chartRing_smul_def, mul_one]⟩

theorem lpow.equiv (Q : Kleiman.SubSystem S x Ω) {b : ℕ} (hb : 1 ≤ b) {i : Fin (N + 1)} (h : x i ≠ 0) :
    IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke Q) b i = toIndefiniteRowSideFullHecke (Q.pow b) i := by
  induction b, hb using Nat.le_induction with
  | base =>
    rw [IndefiniteRowSideFullHecke.Kleiman.lpow, pow_one]
    change toIndefiniteRowSideFullHecke Q i = toIndefiniteRowSideFullHecke ((Q.pow 0).twist Q) i
    rw [← lmul.equiv _ _ h, IndefiniteRowSideFullHecke.Kleiman.lmul]
    apply le_antisymm
    · intro q hq
      have h1 : (1 : Ω) ∈ toIndefiniteRowSideFullHecke (Q.pow 0) i := by
        rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem, pow_zero_sub]
        exact one_mem _
      simpa using Submodule.mul_mem_mul h1 hq
    · rw [Submodule.mul_le]
      intro a ha q hq
      rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem, pow_zero_sub] at ha
      rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem] at hq ⊢
      exact Submodule.smul_mem _ (⟨a, ha⟩ : Kleiman.chartRing S x _) hq
  | succ b hb ih =>
    rw [IndefiniteRowSideFullHecke.Kleiman.lpow, pow_succ]
    change IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke Q) b i * toIndefiniteRowSideFullHecke Q i = toIndefiniteRowSideFullHecke ((Q.pow b).twist Q) i
    rw [ih, ← lmul.equiv _ _ h]
    rfl

end Families

section Filtration

variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

theorem isGradedSub_span_singleton (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) {g : M} {d : ℤ}
    (hg : g ∈ G.piece d) : IndefiniteRowSideFullHecke.Kleiman.IsGradedSub S N G (Submodule.span (Poly S N) {g}) := by
  classical
  apply le_antisymm
  · intro z hz
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hz
    obtain ⟨f, rfl⟩ := hz
    rw [← sum_homogeneousComponent f, Finset.sum_smul]
    refine sum_mem fun e _ => ?_
    refine Submodule.mem_iSup_of_mem (d + e) ⟨?_, ?_⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
    · have := (gradedEquiv S N M G).smul_mem e d _ g (homogeneousComponent_isHomogeneous e f) hg
      exact this
  · exact iSup_le fun _ => inf_le_left

theorem isGradedSub_sup (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) {L L' : Submodule (Poly S N) M}
    (hL : IndefiniteRowSideFullHecke.Kleiman.IsGradedSub S N G L) (hL' : IndefiniteRowSideFullHecke.Kleiman.IsGradedSub S N G L') :
    IndefiniteRowSideFullHecke.Kleiman.IsGradedSub S N G (L ⊔ L') := by
  apply le_antisymm
  · rw [Submodule.restrictScalars_sup, sup_le_iff]
    constructor
    · exact hL.le.trans (iSup_mono fun c => inf_le_inf_right _ le_sup_left)
    · exact hL'.le.trans (iSup_mono fun c => inf_le_inf_right _ le_sup_right)
  · exact iSup_le fun _ => inf_le_left

def primeFiltEquiv (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) :
    IndefiniteRowSideFullHecke.Kleiman.PrimeFiltration S N G ≃ Kleiman.PrimeFilt (gradedEquiv S N M G) where
  toFun F :=
    { n := F.n, step := F.step, gen := F.gen, deg := F.deg, prime := F.prime
      step_zero := F.step_zero, step_last := F.step_last, step_succ := F.step_succ, gen_mem := F.gen_mem
      mem_prime := fun k p => (F.ann_gen k p).symm, isPrime := F.isPrime
      isHomogeneous := fun k p hp d => F.homog k p hp d, ann_le := F.ann_le }
  invFun F :=
    { n := F.n, step := F.step
      mono := Fin.monotone_iff_le_succ.mpr fun k => by rw [F.step_succ k]; exact le_sup_left
      step_zero := F.step_zero, step_last := F.step_last
      graded := by
        intro k
        induction k using Fin.induction with
        | zero =>
          rw [F.step_zero]
          exact le_antisymm (by simp) (iSup_le fun _ => inf_le_left)
        | succ k ih =>
          rw [F.step_succ k]
          exact isGradedSub_sup S N G ih (isGradedSub_span_singleton S N G (F.gen_mem k))
      prime := F.prime, isPrime := F.isPrime, homog := fun k p hp d => F.isHomogeneous k p hp d
      ann_le := F.ann_le, deg := F.deg, gen := F.gen, gen_mem := F.gen_mem, step_succ := F.step_succ
      ann_gen := fun k f => (F.mem_prime k f).symm }
  left_inv _ := rfl
  right_inv _ := rfl

theorem PrimeFiltration.equiv (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (F : IndefiniteRowSideFullHecke.Kleiman.PrimeFiltration S N G) :
    (primeFiltEquiv S N G F).n = F.n ∧ HEq (primeFiltEquiv S N G F).step F.step ∧
      HEq (primeFiltEquiv S N G F).gen F.gen ∧ HEq (primeFiltEquiv S N G F).deg F.deg ∧
      HEq (primeFiltEquiv S N G F).prime F.prime :=
  ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end Filtration

end

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
