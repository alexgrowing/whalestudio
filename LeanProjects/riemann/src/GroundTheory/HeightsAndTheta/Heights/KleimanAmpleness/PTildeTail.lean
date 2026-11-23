import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTailLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Cocycles

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

def FinGradedSub.cellCone (I : StdCell N) : LocMod S N M.coneSub I.1 →ₗ[Poly S N] ConeLaurent S x :=
  if h : I.1 ⊆ support x then locCone M I.1 h else 0

theorem FinGradedSub.cellCone_of_subset {I : StdCell N} (h : I.1 ⊆ support x) :
    M.cellCone I = locCone M I.1 h := dif_pos h

theorem Cech.sgn_mul_self {n : ℕ} (J : Finset (Fin n)) (j : Fin n) : Cech.sgn J j * Cech.sgn J j = 1 := by
  rw [Cech.sgn, ← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem FinGradedSub.cellCone_cocycle {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : Cech.d (locSys S N M.coneSub) locResS 0 z = 0)
    (K K' : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0)
    (hK : K.1.1 ⊆ support x) (hK' : K'.1.1 ⊆ support x) :
    M.cellCone K.1 (z K) = M.cellCone K'.1 (z K') := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · have : K = K' := Subtype.ext (Subtype.ext (ha.trans (hab ▸ hb.symm)))
    subst this; rfl
  let Kp : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, Finset.subset_univ _⟩, Finset.card_pair hab⟩
  have hKp : Kp.1.1 ⊆ support x := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hK (by rw [ha]; exact Finset.mem_singleton_self _)
    · exact hK' (by rw [hb]; exact hi)
  have hfa : ∀ j : Kp.1.1, (j : Fin (N + 1)) = a → Cech.face Kp j = K' := by
    intro j hj
    apply Subtype.ext; apply Subtype.ext
    change ({a, b} : Finset (Fin (N + 1))).erase j = K'.1.1
    rw [hj, hb, Finset.erase_insert (Finset.notMem_singleton.mpr hab)]
  have hfb : ∀ j : Kp.1.1, (j : Fin (N + 1)) = b → Cech.face Kp j = K := by
    intro j hj
    apply Subtype.ext; apply Subtype.ext
    change ({a, b} : Finset (Fin (N + 1))).erase j = K.1.1
    rw [hj, ha, Finset.pair_comm, Finset.erase_insert (Finset.notMem_singleton.mpr (Ne.symm hab))]
  have h0 := congrArg (M.cellCone Kp.1) (congrFun hz Kp)
  rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have hterm : ∀ j : Kp.1.1, M.cellCone Kp.1 (Cech.sgn Kp.1.1 j • locResS (Cech.face Kp j).1 Kp.1
      (Cech.face_subset Kp j) (z (Cech.face Kp j))) =
      Cech.sgn Kp.1.1 j • M.cellCone (Cech.face Kp j).1 (z (Cech.face Kp j)) := by
    intro j
    rw [map_zsmul, M.cellCone_of_subset hKp, M.cellCone_of_subset ((Cech.face_subset Kp j).trans hKp)]
    congr 1
    exact locCone_locRes M (Cech.face_subset Kp j) hKp _
  rw [Finset.sum_congr rfl fun j _ => hterm j] at h0
  rw [Fintype.sum_eq_add (⟨a, Finset.mem_insert_self a {b}⟩ : Kp.1.1)
    (⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩ : Kp.1.1)
    (fun h => hab (congrArg Subtype.val h)) (fun j hj => ?_)] at h0
  · rw [hfa ⟨a, Finset.mem_insert_self a {b}⟩ rfl,
      hfb ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩ rfl] at h0
    have hs : Cech.sgn Kp.1.1 b = -Cech.sgn Kp.1.1 a := by
      have := Cech.sum_sgn_of_card_two (J := Kp.1.1) Kp.2
      rw [show Kp.1.1 = {a, b} from rfl, Finset.sum_pair hab] at this
      linarith
    change Cech.sgn Kp.1.1 a • M.cellCone K'.1 (z K') + Cech.sgn Kp.1.1 b • M.cellCone K.1 (z K) = 0 at h0
    rw [hs, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h0
    have h1 := congrArg (Cech.sgn Kp.1.1 a • ·) h0
    simp only [smul_smul, Cech.sgn_mul_self, one_smul, smul_zero] at h1
    exact (sub_eq_zero.mp h1).symm
  · exfalso
    rcases Finset.mem_insert.mp j.2 with h | h
    · exact hj.1 (Subtype.ext h)
    · exact hj.2 (Subtype.ext (Finset.mem_singleton.mp h))

theorem FinGradedSub.cocycle_eq_coneSingle {c : ℤ} {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) (hK : K.1.1 ⊆ support x) :
    ∃ v ∈ (M.tildeSys c).secs, M.cellCone K.1 (z K) = coneSingle S x c v := by
  obtain ⟨v, -, hzv⟩ := locCone_degLoc M c K.1 hK (hz.2 K (Set.mem_univ _))
  rw [← M.cellCone_of_subset hK] at hzv
  refine ⟨v, ?_, hzv⟩
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro J
  obtain ⟨i, hi⟩ := J.2.1
  let Ki : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
    ⟨⟨{i}, Finset.singleton_nonempty i, Finset.subset_univ _⟩, Finset.card_singleton i⟩
  have hKi : Ki.1.1 ⊆ support x := Finset.singleton_subset_iff.mpr (J.2.2 hi)
  obtain ⟨v', hv', hzv'⟩ := locCone_degLoc M c Ki.1 hKi (hz.2 Ki (Set.mem_univ _))
  rw [← M.cellCone_of_subset hKi, ← M.cellCone_cocycle (LinearMap.mem_ker.mp hz.1) K Ki hK hKi, hzv] at hzv'
  have hvv : v = v' := by
    have := congrArg (coeffAt S x c) hzv'
    rwa [coeffAt_coneSingle_same, coeffAt_coneSingle_same] at this
  rw [hvv]
  exact (M.tildeSys c).mono _ J (Finset.singleton_subset_iff.mpr hi) v' hv'

theorem FinGradedSub.exists_cocycle_of_mem_secs {c : ℤ} {v : Ω} (hv : v ∈ (M.tildeSys c).secs) :
    ∃ z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0,
      ∀ K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0, K.1.1 ⊆ support x →
        M.cellCone K.1 (z K) = coneSingle S x c v := by
  classical
  rw [SubSystem.secs, Submodule.mem_iInf] at hv
  have hl : ∀ (I : StdCell N) (h : I.1 ⊆ support x), ∃ z ∈ degLoc M.coneGraded c I,
      locCone M I.1 h z = coneSingle S x c v :=
    fun I h => exists_locCone_eq M c I h (hv ⟨I.1, I.2.1, h⟩)
  choose w hw hwv using hl
  let u : ∀ I : StdCell N, LocMod S N M.coneSub I.1 := fun I =>
    if h : I.1 ⊆ support x then w I h else 0
  have hcompat : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (u I) = u J := by
    intro I J h
    by_cases hJ : J.1 ⊆ support x
    · apply locCone_injective M J.1 hJ
      have hI : I.1 ⊆ support x := h.trans hJ
      simp only [u, dif_pos hJ, dif_pos hI]
      rw [hwv J hJ]
      exact (locCone_locRes M h hJ (w I hI)).trans (hwv I hI)
    · obtain ⟨i, hiJ, hi⟩ : ∃ i ∈ J.1, x i = 0 := by
        by_contra hne
        push Not at hne
        exact hJ fun i hi => (mem_support x).mpr (hne i hi)
      have := locMod_subsingleton M hiJ hi
      exact Subsingleton.elim _ _
  refine ⟨fun K => u K.1, ⟨LinearMap.mem_ker.mpr (Cech.d_zero_of_compat u hcompat), fun K _ => ?_⟩,
    fun K hK => ?_⟩
  · change u K.1 ∈ degLoc M.coneGraded c K.1
    by_cases hK : K.1.1 ⊆ support x
    · simp only [u, dif_pos hK]; exact hw K.1 hK
    · simp only [u, dif_neg hK]; exact zero_mem _
  · change M.cellCone K.1 (u K.1) = _
    simp only [u, dif_pos hK, M.cellCone_of_subset hK]
    exact hwv K.1 hK

end Cocycles

theorem TildeTail.proof (h : SerreTail.Statement.{u, w}) : TildeTail.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x M hx c₁
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hx (funext hne)
  let K₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
    ⟨⟨{i₀}, Finset.singleton_nonempty i₀, Finset.subset_univ _⟩, Finset.card_singleton i₀⟩
  have hK₀ : K₀.1.1 ⊆ support x := Finset.singleton_subset_iff.mpr ((mem_support x).mpr hi₀)

  let Ψ : Cech.Cochain (locSys S N M.coneSub) 0 →ₗ[Poly S N] ConeLaurent S x :=
    (M.cellCone K₀.1).comp (LinearMap.proj (R := Poly S N)
      (φ := fun K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 => LocMod S N M.coneSub K.1.1) K₀)
  have hΨ : ∀ z, Ψ z = M.cellCone K₀.1 (z K₀) := fun z => rfl
  obtain ⟨t, ht, hspan⟩ := h S N M.coneSub M.coneGraded M.coneSub_finite c₁

  let G : Submodule S (Cech.Cochain (locSys S N M.coneSub) 0) :=
    { carrier := {z | ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧ (d < c₁ → coeffAt S x d (Ψ z) = 0)}
      add_mem' := fun {a b} ha hb d => by
        rw [map_add, map_add]
        exact ⟨add_mem (ha d).1 (hb d).1, fun hd => by rw [(ha d).2 hd, (hb d).2 hd, add_zero]⟩
      zero_mem' := fun d => by rw [map_zero, map_zero]; exact ⟨zero_mem _, fun _ => rfl⟩
      smul_mem' := fun s z hz d => by
        rw [LinearMap.map_smul_of_tower, map_smul]
        exact ⟨Submodule.smul_mem _ s (hz d).1, fun hd => by rw [(hz d).2 hd, smul_zero]⟩ }
  have hG : H0tail M.coneGraded c₁ ≤ G := by
    refine iSup₂_le fun c hc z hz => ?_
    show ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧ (d < c₁ → coeffAt S x d (Ψ z) = 0)
    intro d
    obtain ⟨v, hv, hzv⟩ := M.cocycle_eq_coneSingle hz K₀ hK₀
    rw [hΨ, hzv]
    by_cases hcd : c = d
    · subst hcd
      rw [coeffAt_coneSingle_same]
      exact ⟨hv, fun h => absurd hc (not_le.mpr h)⟩
    · rw [coeffAt_coneSingle_ne hcd]
      exact ⟨zero_mem _, fun _ => rfl⟩
  have hgood : ∀ z ∈ t, ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧
      (d < c₁ → coeffAt S x d (Ψ z) = 0) := fun z hz => hG (ht z hz)

  let D : Finset ℤ := (t.biUnion fun z => coneSupp (Ψ z)).filter (c₁ ≤ ·)
  let e := (t ×ˢ D).equivFin.symm
  refine ⟨(t ×ˢ D).card, fun j => (e j).1.2, fun j => coeffAt S x (e j).1.2 (Ψ (e j).1.1),
    fun j => ?_, fun c hc y hy => ?_⟩
  · have hm := Finset.mem_product.mp (e j).2
    exact ⟨(Finset.mem_filter.mp hm.2).2, (hgood _ hm.1 _).1⟩
  obtain ⟨z, hz, hzy⟩ := M.exists_cocycle_of_mem_secs hy
  have hzt : z ∈ H0tail M.coneGraded c₁ :=
    (le_iSup₂ (f := fun c (_ : c₁ ≤ c) =>
      Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0) c hc) hz
  let Sp : ℤ → Submodule S Ω := fun d => Submodule.span S {w | ∃ (j : Fin (t ×ˢ D).card) (f : Poly S N)
    (k : ℕ), f.IsHomogeneous k ∧ (k : ℤ) + (e j).1.2 = d ∧ w = aeval x f * coeffAt S x (e j).1.2 (Ψ (e j).1.1)}
  have hmulSp : ∀ (f : Poly S N) (k : ℕ), f.IsHomogeneous k → ∀ d, ∀ u ∈ Sp (d - k),
      aeval x f * u ∈ Sp d := by
    intro f k hf d u hu
    refine Submodule.span_induction (p := fun u _ => aeval x f * u ∈ Sp d) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, g, k', hg, hgk, rfl⟩
      exact Submodule.subset_span ⟨j, f * g, k + k', hf.mul hg, by push_cast; omega,
        by rw [map_mul, mul_assoc]⟩
    · rw [mul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact add_mem ha hb
    · intro s a _ ha; rw [mul_smul_comm]; exact Submodule.smul_mem _ s ha
  have key : ∀ w ∈ Submodule.span (Poly S N) (t : Set (Cech.Cochain (locSys S N M.coneSub) 0)),
      ∀ d, coeffAt S x d (Ψ w) ∈ Sp d := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∀ d, coeffAt S x d (Ψ w) ∈ Sp d) ?_ ?_ ?_ ?_ hw
    · intro z' hz' d
      by_cases h0 : coeffAt S x d (Ψ z') = 0
      · rw [h0]; exact zero_mem _
      · have hd : c₁ ≤ d := by
          by_contra hlt
          exact h0 ((hgood z' hz' d).2 (not_le.mp hlt))
        have hmem : (z', d) ∈ t ×ˢ D := Finset.mem_product.mpr ⟨hz', Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨z', hz', mem_coneSupp.mpr h0⟩, hd⟩⟩
        refine Submodule.subset_span ⟨e.symm ⟨(z', d), hmem⟩, 1, 0, isHomogeneous_one _ _, ?_, ?_⟩
        · simp
        · simp
    · intro d; rw [map_zero, map_zero]; exact zero_mem _
    · intro a b _ _ ha hb d; rw [map_add, map_add]; exact add_mem (ha d) (hb d)
    · intro p a _ ha d
      rw [map_smul, ← sum_homogeneousComponent p, Finset.sum_smul, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [coeffAt_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous k p)]
      exact hmulSp _ k (homogeneousComponent_isHomogeneous k p) d _ (ha (d - k))
  have hyc := key z (hspan hzt) c
  rwa [hΨ, hzy K₀ hK₀, coeffAt_coneSingle_same] at hyc

end

end GroundTheory.Heights₂.Heights.Kleiman
