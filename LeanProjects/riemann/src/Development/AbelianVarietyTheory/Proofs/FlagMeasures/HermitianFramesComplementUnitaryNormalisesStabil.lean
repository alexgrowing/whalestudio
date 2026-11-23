import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormAdditiveCharacterTypePrimeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnessesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameUnipotentExchangingDualIsotropicStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem inv_apply (h : S.GLV) (v : S.V) : h⁻¹ v = h.symm v := rfl

theorem fix {h : S.GLV} (hh : h ∈ S.H0) {v : S.V} (hv : v ∈ S.ME) : h v = v := by
  have := hh.2.2 v hv
  rw [Submodule.mem_bot, sub_eq_zero] at this
  exact this

theorem spanTo_le (g : Fin (r + 1) → S.V) (j : ℕ) : S.spanTo g j ≤ S.spanTo g (r + 1) :=
  Submodule.span_mono (Set.image_mono fun i _ => i.2)

theorem spanTo_le_ME (j : ℕ) : S.spanTo S.f j ≤ S.ME := (spanTo_le S S.f j).trans le_sup_left

theorem spanTo_le_ME' (j : ℕ) : S.spanTo S.f' j ≤ S.ME := (spanTo_le S S.f' j).trans le_sup_right

theorem f_mem (a : Fin (r + 1)) : S.f a ∈ S.ME :=
  spanTo_le_ME S (r + 1) (Submodule.subset_span ⟨a, a.2, rfl⟩)

theorem f'_mem (a : Fin (r + 1)) : S.f' a ∈ S.ME :=
  spanTo_le_ME' S (r + 1) (Submodule.subset_span ⟨a, a.2, rfl⟩)

theorem mem_iff {h : S.GLV} (hh : h ∈ S.H0) (A : Submodule E S.V) (hA : A ≤ S.ME) (v : S.V) :
    h v ∈ A ↔ v ∈ A := by
  constructor
  · intro H
    have : v ∈ S.ME := (hh.2.1 v).1 (hA H)
    rwa [fix S hh this] at H
  · intro H
    rwa [fix S hh (hA H)]

theorem perp_mem_iff {h : S.GLV} (hh : h ∈ S.H0) (A : Submodule E S.V) (hA : A ≤ S.ME) (v : S.V) :
    h v ∈ perp L S.Hm A ↔ v ∈ perp L S.Hm A := by
  constructor
  · intro H y hy
    rw [← hh.1 v y, fix S hh (hA hy)]
    exact H y hy
  · intro H y hy
    rw [← fix S hh (hA hy), hh.1 v y]
    exact H y hy

theorem conj_unipOn (h : S.GLV) (A B : Submodule E S.V) (hA : ∀ v, h v ∈ A ↔ v ∈ A)
    (hB : ∀ v, h v ∈ B ↔ v ∈ B) (s : S.GLV) (hs : s ∈ unipOn A B) : h * s * h⁻¹ ∈ unipOn A B := by
  have hA' : ∀ v, h⁻¹ v ∈ A ↔ v ∈ A := fun v => by
    rw [← hA (h⁻¹ v), inv_apply, LinearEquiv.apply_symm_apply]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · change h (s (h⁻¹ v)) ∈ A ↔ v ∈ A
    rw [hA, hs.1, hA']
  · change h (s (h⁻¹ v)) - v ∈ B
    have e : h (s (h⁻¹ v)) - v = h (s (h⁻¹ v) - h⁻¹ v) := by
      rw [map_sub, inv_apply, LinearEquiv.apply_symm_apply]
    rw [e, hB]
    exact hs.2 _ ((hA' v).2 hv)

theorem nof_conj (g : Fin (r + 1) → S.V) (hg : ∀ j, S.spanTo g j ≤ S.ME) {h : S.GLV} (hh : h ∈ S.H0)
    (s : S.GLV) (hs : s ∈ S.Nof g) : h * s * h⁻¹ ∈ S.Nof g := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hs ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  have hI : h ∈ isomG L S.Hm := hh.1
  refine ⟨⟨(isomG L S.Hm).mul_mem ((isomG L S.Hm).mul_mem hI h1) ((isomG L S.Hm).inv_mem hI),
    fun j => ?_⟩, ?_⟩
  · exact conj_unipOn S h _ _ (mem_iff S hh _ (hg _)) (mem_iff S hh _ (hg _)) s (h2 j)
  · exact conj_unipOn S h _ _ (perp_mem_iff S hh _ (hg _)) (mem_iff S hh _ (hg _)) s h3

theorem normalises {h : S.GLV} (hh : h ∈ S.H0) :
    (∀ s ∈ S.N, h * s * h⁻¹ ∈ S.N) ∧ (∀ s ∈ S.N', h * s * h⁻¹ ∈ S.N') ∧
      ∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St :=
  ⟨fun s hs => nof_conj S S.f (spanTo_le_ME S) hh s hs,
    fun s hs => nof_conj S S.f' (spanTo_le_ME' S) hh s hs,
    fun s hs => ⟨nof_conj S S.f (spanTo_le_ME S) hh s hs.1, nof_conj S S.f' (spanTo_le_ME' S) hh s hs.2⟩⟩

end GlobalTheory.HL.FixFrames

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

open GlobalTheory.FrameAct in
theorem graph_sub {h : S.GLV} (hh : h ∈ S.H0) (Λ : Submodule L.O S.V) (p : S.V × S.V)
    (hp : p ∈ S.graphOf Λ) : (h p.1, h p.2) ∈ S.graphOf (h • Λ) := by
  obtain ⟨y', hy', y, hy, a', a, b', b, c⟩ := hp
  refine ⟨h y', (mem_smul_iff S h Λ _).2 hy', h y, (mem_smul_iff S h Λ _).2 hy,
    (perp_mem_iff S hh S.X' (spanTo_le_ME' S r) _).2 a', (perp_mem_iff S hh S.X (spanTo_le_ME S r) _).2 a,
    ?_, ?_, ?_⟩
  · rw [← map_sub]; exact (mem_iff S hh S.X' (spanTo_le_ME' S r) _).2 b'
  · rw [← map_sub]; exact (mem_iff S hh S.X (spanTo_le_ME S r) _).2 b
  · rw [← map_sub, inTh_iff]; exact c

theorem graph_move {h : S.GLV} (hh : h ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.graphOf (h • Λ) = h • S.graphOf Λ := by
  have hh' : h⁻¹ ∈ S.H0 := S.H0.inv_mem hh
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro H
    have := graph_sub S hh' (h • Λ) p H
    rwa [inv_smul_smul] at this
  · intro H
    have := graph_sub S hh Λ _ H
    simpa [LinearEquiv.smul_def] using this

theorem conj_stab (h x : S.GLV) (P : Submodule L.O S.V) :
    h⁻¹ * x * h ∈ MulAction.stabilizer S.GLV P ↔ x ∈ MulAction.stabilizer S.GLV (h • P) := by
  simp only [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]

theorem conj_St {h : S.GLV} (hh : h ∈ S.H0) (x : S.GLV) : h⁻¹ * x * h ∈ S.St ↔ x ∈ S.St := by
  constructor
  · intro H
    have := (normalises S hh).2.2 _ H
    simpa [mul_assoc] using this
  · intro H
    have := (normalises S (S.H0.inv_mem hh)).2.2 _ H
    simpa using this

theorem mu_move {h : S.GLV} (hh : h ∈ S.H0) (Λ : Submodule L.O S.V) : S.mu (h • Λ) = S.mu Λ := by
  have hfixf : ∀ a, h (S.f a) = S.f a := fun a => fix S hh (f_mem S a)
  have hfixf' : ∀ a, h (S.f' a) = S.f' a := fun a => fix S hh (f'_mem S a)
  have sf : h • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) := by
    rw [GlobalTheory.FrameAct.smul_span, ← Set.range_comp]
    congr 2
    funext a
    exact hfixf a
  have sf' : h • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') := by
    rw [GlobalTheory.FrameAct.smul_span, ← Set.range_comp]
    congr 2
    funext a
    exact hfixf' a
  have e1 : (S.St ⊓ MulAction.stabilizer S.GLV Λ).map (MulAut.conj h).toMonoidHom =
      S.St ⊓ MulAction.stabilizer S.GLV (h • Λ) := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_inf, Subgroup.mem_inf, conj_St S hh,
      conj_stab]
  have e0 : S.K0.map (MulAut.conj h).toMonoidHom = S.K0 := by
    ext x
    unfold Frames.K0
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp only [Subgroup.mem_inf, conj_St S hh, conj_stab, sf, sf']
  have inj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  unfold Frames.mu invVol
  rw [← e1, ← e0, Subgroup.relIndex_map_map_of_injective _ _ inj,
    Subgroup.relIndex_map_map_of_injective _ _ inj, e0]

end GlobalTheory.HL.FixFrames

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

open GlobalTheory.FrameAct in
theorem mem_perp_span (s : Set S.V) (x : S.V) :
    x ∈ perp L S.Hm (Submodule.span E s) ↔ ∀ y ∈ s, hf L S.Hm x y = 0 :=
  ⟨fun H y hy => H y (Submodule.subset_span hy), fun H => GlobalTheory.FramePsi.hf_span_right L S.Hm x s H⟩

theorem fix_span (g : Fin (r + 1) → S.V) (h : S.GLV) (hfix : ∀ a, h (g a) = g a) (j : ℕ) (v : S.V)
    (hv : v ∈ S.spanTo g j) : h v = v := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨a, -, rfl⟩ := hx; exact hfix a
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem perp_spanTo_iff (g : Fin (r + 1) → S.V) (h : S.GLV) (hI : h ∈ isomG L S.Hm)
    (hfix : ∀ a, h (g a) = g a) (j : ℕ) (v : S.V) :
    h v ∈ perp L S.Hm (S.spanTo g j) ↔ v ∈ perp L S.Hm (S.spanTo g j) := by
  constructor
  · intro H y hy
    rw [← hI v y, fix_span S g h hfix j y hy]
    exact H y hy
  · intro H y hy
    rw [← fix_span S g h hfix j y hy, hI v y]
    exact H y hy

theorem perp_range_iff (gs : Fin r → S.V) (h : S.GLV) (hI : h ∈ isomG L S.Hm) (x : S.V) :
    h x ∈ perp L S.Hm (Submodule.span E (Set.range fun j => h (gs j))) ↔
      x ∈ perp L S.Hm (Submodule.span E (Set.range gs)) := by
  have hI' : ∀ a b, hf L S.Hm (h a) (h b) = hf L S.Hm a b := hI
  rw [mem_perp_span, mem_perp_span, Set.forall_mem_range, Set.forall_mem_range]
  simp only [hI']

theorem fg_smul (a : S.GLV) (N : Submodule L.O S.V) (hN : N.FG) : (a • N).FG := by
  rw [Submodule.pointwise_smul_def]
  exact hN.map _

end GlobalTheory.HL.FixFrames

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

open GlobalTheory.FrameAct in

theorem inner_transport (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hi : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (h : S.GLV) (hI : h ∈ isomG L S.Hm) (hfix : ∀ a, h (g a) = g a)
    (A : Submodule L.O S.V) (hA : S.IsInner g gs A) :
    S.IsInner g gs (h • A) ∧ ∃ m ∈ S.Nof g, (∀ a, m (g a) = g a) ∧
      m • S.stdLat g gs (h • A) = h • S.stdLat g gs A := by
  have hI' : ∀ a b, hf L S.Hm (h a) (h b) = hf L S.Hm a b := hI
  obtain ⟨a1, a2, a3, a4, a5, y, hy, a6⟩ := hA
  have hd2 : ∀ a j, hf L S.Hm (g a) (h (gs j)) = if a = j.castSucc then 1 else 0 := fun a j => by
    rw [← hfix a, hI', hd]
  have hi2 : ∀ i j, hf L S.Hm (h (gs i)) (h (gs j)) = 0 := fun i j => by rw [hI']; exact hi i j
  obtain ⟨m, hm, mfix, mgs, mA⟩ := GlobalTheory.T.exists_frameUnipotent_exchanging_dual_isotropic L r k S g t gs (fun j => h (gs j)) hg hd hd2 hi hi2
  have b1 : ∀ x ∈ S.spanTo g r, x ∈ h • A := fun x hx => by
    rw [← fix_span S g h hfix r x hx]
    exact (mem_smul_iff S h A x).2 (a1 x hx)
  have b2 : ∀ x ∈ h • A, x ∈ perp L S.Hm (S.spanTo g r) := fun x hx => by
    obtain ⟨x0, rfl⟩ := h.surjective x
    exact (perp_spanTo_iff S g h hI hfix r x0).2 (a2 x0 ((mem_smul_iff S h A x0).1 hx))
  have key := mA (h • A) b1 b2
  have eA : (h • A) ⊓ (perp L S.Hm (Submodule.span E (Set.range fun j => h (gs j)))).restrictScalars L.O =
      h • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O) := by
    refine eq_smul_of S h _ _ fun x => ?_
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff, perp_range_iff S gs h hI]
  have hfg : (h • A) ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O =
      m⁻¹ • (h • (A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O)) := by
    rw [← eA, ← key, inv_smul_smul]
  refine ⟨⟨b1, b2, ?_, fun z hz => ?_, ?_, h y, (mem_smul_iff S h A y).2 hy, ?_⟩, m, hm, mfix, ?_⟩
  · rw [hfg]
    exact fg_smul S _ _ (fg_smul S _ _ a3)
  · obtain ⟨z0, rfl⟩ := h.surjective z
    have hz0 := (perp_spanTo_iff S g h hI hfix r z0).1 hz
    rw [mem_smul_iff, ← a4 z0 hz0]
    constructor
    · intro H x hx
      have := H (h x) ((mem_smul_iff S h A x).2 hx)
      simpa only [Frames.h, hI'] using this
    · intro H x hx
      obtain ⟨x0, rfl⟩ := h.surjective x
      have := H x0 ((mem_smul_iff S h A x0).1 hx)
      simpa only [Frames.h, hI'] using this
  · rw [← hfix (Fin.last r)]
    exact (mem_smul_iff S h A _).2 a5
  · show hf L S.Hm (g (Fin.last r)) (h y) = 1
    rw [← hfix (Fin.last r), hI']
    exact a6
  · have s1 : h • Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) =
        Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact hfix _
    have s2 : m • Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) =
        Submodule.span L.O (Set.range fun j : Fin r => g j.castSucc) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact mfix _
    have s3 : h • Submodule.span L.O (Set.range gs) =
        Submodule.span L.O (Set.range fun j => h (gs j)) := by
      rw [smul_span, ← Set.range_comp]
      rfl
    have s4 : m • Submodule.span L.O (Set.range gs) =
        Submodule.span L.O (Set.range fun j => h (gs j)) := by
      rw [smul_span, ← Set.range_comp]
      congr 2
      funext j
      exact mgs _
    unfold Frames.stdLat
    rw [Submodule.smul_sup', Submodule.smul_sup', Submodule.smul_sup', Submodule.smul_sup', s1, s2, s3, s4,
      key, eA]

end GlobalTheory.HL.FixFrames

namespace GlobalTheory.HL.FixFrames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem psiOf_conj (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (h n : S.GLV)
    (H : ∀ b, (h * n * h⁻¹) (g b) = n (g b)) : S.psiOf g gs (h * n * h⁻¹) = S.psiOf g gs n := by
  unfold Frames.psiOf Frames.coef
  simp only [H]

theorem psiOf_fix (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (m : S.GLV) (mfix : ∀ a, m (g a) = g a) : S.psiOf g gs m = 1 := by
  have ne : ∀ j : Fin r, j.succ ≠ j.castSucc := fun j e => by
    have := congrArg Fin.val e
    simp at this
  unfold Frames.psiOf Frames.coef
  simp only [mfix, Frames.h, hd, ne, if_false, Finset.sum_const_zero, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.HL.FixFrames

open GlobalTheory.HL.FixFrames GlobalTheory.FrameAct in

theorem GlobalTheory.HL.FixFrames.unitary_complement_acts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, (∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St) ∧ ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh
  obtain ⟨nN, nN', nSt⟩ := normalises S hh
  refine ⟨nSt, fun d Λ H => ?_⟩
  have hh' : h⁻¹ ∈ S.H0 := S.H0.inv_mem hh
  have hfixf : ∀ a, h (S.f a) = S.f a := fun a => fix S hh (f_mem S a)
  have hfixf' : ∀ a, h (S.f' a) = S.f' a := fun a => fix S hh (f'_mem S a)
  have ifixf : ∀ a, h⁻¹ (S.f a) = S.f a := fun a => fix S hh' (f_mem S a)
  have ifixf' : ∀ a, h⁻¹ (S.f' a) = S.f' a := fun a => fix S hh' (f'_mem S a)
  have W0 := wit_spec S d Λ H
  obtain ⟨iA, iA', hn, hn', e1, e2, cg, gr⟩ := W0
  obtain ⟨jA, m, hm, mfix, em⟩ :=
    inner_transport S S.f S.es _ S.gram S.dual S.iso h hh.1 hfixf d.1 iA
  obtain ⟨jA', m', hm', mfix', em'⟩ :=
    inner_transport S S.f' S.es' _ S.gram' S.dual' S.iso' h hh.1 hfixf' d.2.1 iA'
  have W1 : S.IsTermW (h • d) (h • Λ) (h * (S.wit d Λ).1 * h⁻¹ * m) (h * (S.wit d Λ).2 * h⁻¹ * m') := by
    refine ⟨jA, jA', S.N.mul_mem (nN _ hn) hm, S.N'.mul_mem (nN' _ hn') hm', ?_, ?_, fun b => ?_, ?_⟩
    · show h • Λ = (h * (S.wit d Λ).1 * h⁻¹ * m) • S.stdLat S.f S.es (h • d.1)
      rw [mul_smul, em, mul_smul, inv_smul_smul, mul_smul, ← e1]
    · show h • Λ = (h * (S.wit d Λ).2 * h⁻¹ * m') • S.stdLat S.f' S.es' (h • d.2.1)
      rw [mul_smul, em', mul_smul, inv_smul_smul, mul_smul, ← e2]
    · have e : (h * (S.wit d Λ).2 * h⁻¹ * m') (S.f' b) - (h * (S.wit d Λ).1 * h⁻¹ * m) (S.f b) =
          h ((S.wit d Λ).2 (S.f' b) - (S.wit d Λ).1 (S.f b)) := by
        change h ((S.wit d Λ).2 (h⁻¹ (m' (S.f' b)))) - h ((S.wit d Λ).1 (h⁻¹ (m (S.f b)))) = _
        rw [mfix', mfix, ifixf', ifixf, map_sub]
      rw [e, inTh_iff]
      exact cg b
    · show h • d.2.2 = S.graphOf (h • Λ)
      rw [gr, graph_move S hh Λ]
  have hmemN : ∀ b, (h * (S.wit d Λ).1 * h⁻¹) (S.f b) = (S.wit d Λ).1 (S.f b) := fun b => by
    change h ((S.wit d Λ).1 (h⁻¹ (S.f b))) = _
    rw [ifixf]
    exact fix S hh (spanTo_le_ME S (r + 1)
      (spanTo_map S S.f _ S.gram _ hn (r + 1) _ (Submodule.subset_span ⟨b, b.2, rfl⟩)))
  have hmemN' : ∀ b, (h * (S.wit d Λ).2 * h⁻¹) (S.f' b) = (S.wit d Λ).2 (S.f' b) := fun b => by
    change h ((S.wit d Λ).2 (h⁻¹ (S.f' b))) = _
    rw [ifixf']
    exact fix S hh (spanTo_le_ME' S (r + 1)
      (spanTo_map S S.f' _ S.gram' _ hn' (r + 1) _ (Submodule.subset_span ⟨b, b.2, rfl⟩)))
  obtain ⟨o1, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S _ _ _ _ W1
  obtain ⟨o0, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S _ _ _ _ (wit_spec S d Λ H)
  obtain ⟨p1, p2, -⟩ := GlobalTheory.FramePsi.psi_unitary_character L r k S
  have q1 : S.psi (h * (S.wit d Λ).1 * h⁻¹ * m) = S.psi (S.wit d Λ).1 := by
    rw [p1 _ (nN _ hn) _ hm]
    unfold Frames.psi
    rw [psiOf_conj S _ _ _ _ hmemN, psiOf_fix S _ _ S.dual m mfix, mul_one]
  have q2 : S.psi' (h * (S.wit d Λ).2 * h⁻¹ * m') = S.psi' (S.wit d Λ).2 := by
    rw [p2 _ (nN' _ hn') _ hm']
    unfold Frames.psi'
    rw [psiOf_conj S _ _ _ _ hmemN', psiOf_fix S _ _ S.dual' m' mfix', mul_one]
  refine ⟨⟨(_, _), W1⟩, ?_, mu_move S hh Λ⟩
  rw [o1, o0, q1, q2]
