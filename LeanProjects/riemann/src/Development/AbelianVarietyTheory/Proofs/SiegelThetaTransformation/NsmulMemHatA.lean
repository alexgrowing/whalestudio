import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.VacBase

theorem exists_reps {G H : Type} [AddCommGroup G] [AddCommGroup H] (A B : AddSubgroup G) (A₀ : AddSubgroup H)
    (hfg : A₀.FG) (φ : H →+ G) (hφ : ∀ y ∈ A₀, φ y ∈ A) (hs : ∀ u ∈ A, ∃ y ∈ A₀, u - φ y ∈ B) (k : ℕ)
    (hN : ∀ u ∈ A, (2 * k + 1) • u ∈ B) :
    ∃ Ys : Finset G, (∀ y ∈ Ys, ∃ u ∈ A, y = 2 • u) ∧ ∀ u ∈ A, ∃! y, y ∈ Ys ∧ u - y ∈ B := by
  haveI : AddGroup.FG A₀ := (AddGroup.fg_iff_addSubgroup_fg A₀).2 hfg
  let φ' : A₀ →+ A := (φ.comp A₀.subtype).codRestrict A fun y => hφ y y.2
  have hq : ∀ a b : A, (a : A ⧸ B.addSubgroupOf A) = b ↔ (a : G) - b ∈ B := fun a b => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  have hsurj : Function.Surjective ((QuotientAddGroup.mk' (B.addSubgroupOf A)).comp φ') := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y, hy, h⟩ := hs u u.2
    exact ⟨⟨y, hy⟩, ((hq _ _).2 h).symm⟩
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective hsurj
  haveI : Finite (A ⧸ B.addSubgroupOf A) := by
    refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2 * k + 1, Nat.succ_pos _, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hN u u.2
  haveI := Fintype.ofFinite (A ⧸ B.addSubgroupOf A)
  let r : A ⧸ B.addSubgroupOf A → G := fun c => 2 • ((k + 1) • (c.out : G))
  have hr : ∀ (u : A) c, (u : G) - r c ∈ B ↔ (u : A ⧸ B.addSubgroupOf A) = c := fun u c => by
    have e : (u : G) - r c = ((u : G) - c.out) - (2 * k + 1) • (c.out : G) := by
      simp only [r]; module
    rw [e, sub_eq_add_neg, B.add_mem_cancel_right (B.neg_mem (hN _ c.out.2)), ← hq, QuotientAddGroup.out_eq']
  refine ⟨Finset.univ.image r, fun y hy => ?_, fun u hu => ?_⟩
  · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨_, A.nsmul_mem c.out.2 _, rfl⟩
  · refine ⟨r (⟨u, hu⟩ : A), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hr ⟨u, hu⟩ _).2 rfl⟩, ?_⟩
    rintro y ⟨hy, h⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(hr ⟨u, hu⟩ c).1 h]

theorem exists_odd_mem {R : Type} [CommRing R] (I : Ideal R) (h : IsCoprime I (Ideal.span {2})) (M : ℕ)
    (hM : 0 < M) (hm : (M : R) ∈ I) : ∃ k : ℕ, ((2 * k + 1 : ℕ) : R) ∈ I := by
  obtain ⟨a, m, ⟨k, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hM.ne'
  refine ⟨k, ?_⟩
  have h2 : IsCoprime I (Ideal.span {(2 : R) ^ a}) := by
    rw [← Ideal.span_singleton_pow]; exact h.pow_right
  obtain ⟨i, hi, j, hj, e⟩ := Ideal.isCoprime_iff_exists.1 h2
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hj
  have : ((2 * k + 1 : ℕ) : R) = i * ((2 * k + 1 : ℕ) : R) + c * ((2 ^ a * (2 * k + 1) : ℕ) : R) := by
    rw [Nat.cast_mul (2 ^ a), ← mul_assoc, ← add_mul, Nat.cast_pow, Nat.cast_ofNat, e, one_mul]
  rw [this]
  exact I.add_mem (I.mul_mem_right _ hi) (I.mul_mem_left _ hm)

theorem nsmul_mem_hatA {D : D7} (S T : HSp D) (Λ : Lt D.host.E S.rank) (L L' : Lt D.host.E T.rank) (N : ℕ)
    (h : ∀ v ∈ L, N • v ∈ L') : ∀ u ∈ hatA S T (tens Λ L), N • u ∈ hatA S T (tens Λ L') := by
  have h1 : tens Λ L ≤ (tens Λ L').comap (nsmulAddMonoidHom N) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨v, hv, u, hu, rfl⟩
    exact AddSubgroup.subset_closure ⟨v, hv, N • u, h u hu, (map_nsmul (LatTens.vmv v) N u).symm⟩
  have h2 : hatA S T (tens Λ L) ≤ (hatA S T (tens Λ L')).comap (nsmulAddMonoidHom N) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, y, hy, rfl⟩
    exact AddSubgroup.subset_closure ⟨α, hα, N • y, h1 hy, (map_nsmul (LatTens.gen S T α) N y).symm⟩
  exact fun u hu => h2 hu

theorem vac_base : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ LT : Lt D.host.E T.rank, IsAA C.X.Λ LT → ∀ f₀, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) ((stdL D.host.E S.rank) : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) f₀ → C.IsTh f₀ ∧ f₀ ≠ 0 ∧ C.IsFock B f₀ ∧ IsLatVac (heisO C.ψ S T) (hatA S T (tens (stdL D.host.E S.rank) C.X.Λ)) f₀ ∧ ∃ Ys : Finset (WO S T), (∀ y ∈ Ys, ∃ u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)), y = 2 • u) ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)), ∃! y, y ∈ Ys ∧ u - y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
  intro D S T C μ 𝓕 hμ Lv hn M _ hM hm B _ LT hLT f₀ hf
  obtain ⟨-, hv⟩ := hf
  have hstar : ∀ v : Fin S.rank → D.host.E, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank := by
    have : ∀ v : Fin S.rank → D.host.E, v ∈ stdL D.host.E S.rank → star v ∈ stdL D.host.E S.rank := fun v hv =>
      (SW.Base.mem_stdL _).2 fun a => SW.Base.isIntegral_cc ((SW.Base.mem_stdL _).1 hv a)
    exact fun v => ⟨this v, fun h => by simpa using this _ h⟩
  refine ⟨hv.theta, ?_, hv.fock, ?_, ?_⟩
  · rintro rfl
    have := hv.norm.2 (μ, 𝓕) hμ
    simp [nrm2] at this
  · rw [← LatTens.latO_eq_hatA D S T C _ _ LT _ hstar hLT]
    exact hv.lat
  obtain ⟨k, hk⟩ := exists_odd_mem _ Lv.odd M hM hm
  have hlev := SW.level_laws _ _ C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  have hsd : SelfD C.X (Lv.sh C.X.Λ) := (hlev.2.2.2.1 _ hlev.1).1
  have hfg := (SW.TensLat.tens_selfDual_semichar_index _ _ C.X C.g C.bas C.idx S.rank C.sympl C.even Lv.w
    Lv.w_int Lv.w_tr _ hsd M _ (SW.Base.stdL_mem_Vset S.rank M)).1
  have hN : ∀ v ∈ Lv.sh C.X.Λ, (2 * k + 1) • v ∈ C.X.Λ := fun v hv => by
    have hc : ((2 * k + 1 : ℕ) : 𝓞 D.host.E) ∈ conjI Lv.𝔪 :=
      Ideal.subset_span ⟨_, hk, by simp only [RingOfIntegers.coe_eq_algebraMap, map_natCast, cc]⟩
    have := Submodule.smul_le_right (hv _ hc)
    rwa [Nat.cast_smul_eq_nsmul] at this
  have hspan : Submodule.span D.host.E (Lv.sh C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← C.X.Λ_span, Submodule.span_le]
    intro v hv
    have h1 : (M : 𝓞 D.host.E) • v ∈ Lv.sh C.X.Λ := fun b _ => by
      rw [smul_comm]
      exact Submodule.smul_mem_smul hm (C.X.Λ.smul_mem b hv)
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E] at h1
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hM.ne')).1 (Submodule.subset_span h1)
  have hspanS : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, by simp⟩
  have hh := HatLat.hatA_tens D S T C _ _ ⟨(SW.Base.stdL_mem_Vset S.rank M).1, hspanS⟩ ⟨hsd.1, hspan⟩
  have hN' := nsmul_mem_hatA S T (stdL D.host.E S.rank) _ _ _ hN
  refine exists_reps _ _ _ hfg (LatTens.gen S T 1) (fun y hy => (hh.2.1 y).2 hy) (fun u hu => ?_) k hN'
  obtain ⟨y, hy, u', hu', e⟩ := (hh.2.2.1 u hu).2 (2 * k + 1) (Nat.succ_pos _)
  refine ⟨y, hy, ?_⟩
  have : u - LatTens.gen S T 1 y = (2 * k + 1) • u' := by
    rw [e]; exact add_sub_cancel_left _ _
  rw [this]
  exact hN' u' hu'

end GlobalTheory.Ker.VacBase
