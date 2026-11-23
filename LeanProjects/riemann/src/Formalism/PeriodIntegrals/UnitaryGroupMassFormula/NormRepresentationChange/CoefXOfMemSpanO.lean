import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section IntP

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

def IntP (x : D.host.E) : Prop :=
  ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * x = o

theorem one_not_mem_P : (1 : 𝓞 D.host.E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem mul_not_mem_P {s t : 𝓞 D.host.E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht

theorem intP_O (o : 𝓞 D.host.E) : IntP P (o : D.host.E) := ⟨1, one_not_mem_P P, o, by simp⟩

theorem intP_add {x y : D.host.E} (hx : IntP P x) (hy : IntP P y) : IntP P (x + y) := by
  obtain ⟨s1, hs1, o1, h1⟩ := hx
  obtain ⟨s2, hs2, o2, h2⟩ := hy
  refine ⟨s1 * s2, mul_not_mem_P P hs1 hs2, o1 * s2 + o2 * s1, ?_⟩
  push_cast
  linear_combination (s2 : D.host.E) * h1 + (s1 : D.host.E) * h2

theorem valuation_coeff_mul_nonneg {x y : D.host.E} (hx : IntP P x) (hy : IntP P y) : IntP P (x * y) := by
  obtain ⟨s1, hs1, o1, h1⟩ := hx
  obtain ⟨s2, hs2, o2, h2⟩ := hy
  refine ⟨s1 * s2, mul_not_mem_P P hs1 hs2, o1 * o2, ?_⟩
  push_cast
  linear_combination ((s2 : D.host.E) * y) * h1 + (o1 : D.host.E) * h2

theorem isIntegralAt_neg {x : D.host.E} (hx : IntP P x) : IntP P (-x) := by
  have := valuation_coeff_mul_nonneg P (intP_O P (-1)) hx
  simpa using this

theorem intP_sum {ι : Type*} (s : Finset ι) (f : ι → D.host.E) (h : ∀ i ∈ s, IntP P (f i)) :
    IntP P (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using intP_O P 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact intP_add P (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem valuation_le_one_of_isIntegralAt {x : D.host.E} (hx : IntP P x) : P.valuation D.host.E x ≤ 1 := by
  obtain ⟨s, hs, o, h⟩ := hx
  have e1 : algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) := rfl
  have := congrArg (P.valuation D.host.E) h
  rw [map_mul, ← e1, ← e2, P.valuation_of_algebraMap, P.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, one_mul] at this
  rw [this]
  exact P.intValuation_le_one o

end IntP

section Loc

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

def LP (L : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V :=
  haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L

theorem mem_LP {L : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} :
    x ∈ LP P L ↔ ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x ∈ L := by
  unfold LP Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  rfl

theorem smul_eq_E (o : 𝓞 D.host.E) (v : (VS D).V) : o • v = (o : D.host.E) • v :=
  (algebraMap_smul D.host.E o v).symm

theorem mem_localization_of_mem₃ {L : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ L) : x ∈ LP P L :=
  (mem_LP P).mpr ⟨1, one_not_mem_P P, by rw [one_smul]; exact hx⟩

theorem localization_mono₃ {L L' : Submodule (𝓞 D.host.E) (VS D).V} (hle : L ≤ L') {x : (VS D).V} (hx : x ∈ LP P L) :
    x ∈ LP P L' := by
  obtain ⟨s, hs, h⟩ := (mem_LP P).mp hx
  exact (mem_LP P).mpr ⟨s, hs, hle h⟩

theorem add_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {x y : (VS D).V} (hx : x ∈ LP P L) (hy : y ∈ LP P L) :
    x + y ∈ LP P L := add_mem hx hy

theorem sub_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {x y : (VS D).V} (hx : x ∈ LP P L) (hy : y ∈ LP P L) :
    x - y ∈ LP P L := sub_mem hx hy

theorem smul_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {c : D.host.E} (hc : IntP P c) {x : (VS D).V}
    (hx : x ∈ LP P L) : c • x ∈ LP P L := by
  obtain ⟨s, hs, o, ho⟩ := hc
  obtain ⟨t, ht, h⟩ := (mem_LP P).mp hx
  refine (mem_LP P).mpr ⟨s * t, mul_not_mem_P P hs ht, ?_⟩
  have : (s * t) • (c • x) = o • (t • x) := by
    rw [smul_eq_E, smul_eq_E o, smul_eq_E t, smul_smul, smul_smul, ← ho]
    push_cast
    ring_nf
  rw [this]
  exact L.smul_mem o h

theorem LP_sum {L : Submodule (𝓞 D.host.E) (VS D).V} {ι : Type*} (s : Finset ι) (f : ι → (VS D).V)
    (h : ∀ i ∈ s, f i ∈ LP P L) : ∑ i ∈ s, f i ∈ LP P L := Submodule.sum_mem _ h

theorem LP_map {L L' : Submodule (𝓞 D.host.E) (VS D).V} (f : (VS D).V →ₗ[D.host.E] (VS D).V)
    (hf : ∀ v ∈ L, f v ∈ L') {x : (VS D).V} (hx : x ∈ LP P L) : f x ∈ LP P L' := by
  obtain ⟨s, hs, h⟩ := (mem_LP P).mp hx
  refine (mem_LP P).mpr ⟨s, hs, ?_⟩
  rw [smul_eq_E, ← f.map_smul, ← smul_eq_E]
  exact hf _ h

theorem mem_gLam {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : ℕ} {x : (VS D).V} :
    x ∈ Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ ↔ ∃ l ∈ Λ, ((g : ℕ) : D.host.E) • l = x := by
  have hc : (((g : ℕ) : 𝓞 D.host.E) : D.host.E) = ((g : ℕ) : D.host.E) :=
    map_natCast (algebraMap (𝓞 D.host.E) D.host.E) g
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩

theorem nlam_gLam {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ G) (g : ℕ) :
    ∀ v ∈ Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ, (n : (VS D).V →ₗ[D.host.E] (VS D).V) v ∈
      Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := mem_gLam.mp hv
  exact mem_gLam.mpr ⟨n l, nlam_mem hn hl, by simp⟩

end Loc

section Coef

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coefX_of_mem_spanO (F : FlagG S r T) {u : S.V} (hu : u ∈ Submodule.span (𝓞 E) (Set.range F.e)) :
    u ∈ F.X ∧ ∀ a, F.coefX u a ∈ (algebraMap (𝓞 E) E).range := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a', rfl⟩ := hy
    refine ⟨e_mem_X F a', fun a => ?_⟩
    rw [coefX_e]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  | zero => exact ⟨zero_mem _, fun a => by rw [coefX_zero]; exact Subring.zero_mem _⟩
  | add v w _ _ hv hw =>
    exact ⟨add_mem hv.1 hw.1, fun a => by rw [coefX_add _ hv.1 hw.1]; exact Subring.add_mem _ (hv.2 a) (hw.2 a)⟩
  | smul o v _ hv =>
    have e : o • v = (algebraMap (𝓞 E) E o) • v := (algebraMap_smul E o v).symm
    refine ⟨by rw [e]; exact Submodule.smul_mem _ _ hv.1, fun a => ?_⟩
    rw [e, coefX_smul _ hv.1]
    exact Subring.mul_mem _ ⟨o, rfl⟩ (hv.2 a)

end Coef

section FixedConv

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

theorem fixedConv_at {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    LP P (XLam Λ G) = LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e)) := by
  obtain ⟨c, _, hc1, hloc⟩ := hC.1 P
  have hc : (fun a => c a • G.fl.e a) = G.fl.e := funext fun a => by rw [hc1 hP a, one_smul]
  rw [hc] at hloc
  exact hloc

theorem e_mem_LP {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : Fin D.R.rS) :
    G.fl.e a ∈ LP P Λ := by
  have h : G.fl.e a ∈ LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e)) :=
    mem_localization_of_mem₃ P (Submodule.subset_span ⟨a, rfl⟩)
  rw [← fixedConv_at P hC hP] at h
  exact localization_mono₃ P (fun v hv => by rw [XLam, Submodule.mem_inf] at hv; exact hv.1) h

theorem coef_intP {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {w : (VS D).V}
    (hw : w ∈ LP P Λ) (hwX : w ∈ G.fl.X) (a : Fin D.R.rS) : IntP P (G.fl.coefX w a) := by
  obtain ⟨s, hs, hsw⟩ := (mem_LP P).mp hw
  have hsX : s • w ∈ G.fl.X := by rw [smul_eq_E]; exact Submodule.smul_mem _ _ hwX
  have h1 : s • w ∈ LP P (XLam Λ G) := mem_localization_of_mem₃ P (by rw [XLam, Submodule.mem_inf]; exact ⟨hsw, hsX⟩)
  rw [fixedConv_at P hC hP] at h1
  obtain ⟨t, ht, h2⟩ := (mem_LP P).mp h1
  obtain ⟨-, h3⟩ := coefX_of_mem_spanO G.fl h2
  obtain ⟨o, ho⟩ := h3 a
  refine ⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩
  rw [smul_eq_E, smul_eq_E, coefX_smul _ (Submodule.smul_mem _ _ hwX), coefX_smul _ hwX] at ho
  have e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) := rfl
  rw [← e2, ho]
  push_cast
  ring

theorem coef_intP_g {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) {Y : (VS D).V}
    (hY : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)) (hYX : Y ∈ G.fl.X) (a : Fin D.R.rS) :
    IntP P (G.fl.coefX Y a / (gS D : D.host.E)) := by
  obtain ⟨s, hs, hsY⟩ := (mem_LP P).mp hY
  obtain ⟨l, hl, hlY⟩ := mem_gLam.mp hsY
  have hl' : l = ((s : D.host.E) / (gS D : D.host.E)) • Y := by
    rw [smul_eq_E] at hlY
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hlY, smul_smul, inv_mul_cancel₀ hg, one_smul]
  have hlX : l ∈ G.fl.X := by rw [hl']; exact Submodule.smul_mem _ _ hYX
  obtain ⟨t, ht, o, ho⟩ := coef_intP P hC hP (mem_localization_of_mem₃ P hl) hlX a
  refine ⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩
  rw [hl', coefX_smul _ hYX] at ho
  rw [← ho]
  push_cast
  ring

end FixedConv

end PI.NRCW
