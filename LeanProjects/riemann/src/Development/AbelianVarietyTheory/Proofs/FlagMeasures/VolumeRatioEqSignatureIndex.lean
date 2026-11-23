import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolRatioRows

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open GlobalTheory.RowLev GlobalTheory.RowLev.Inhab IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

namespace GlobalTheory.RowIndex

theorem exists_family {V : Type} {N k s : ℕ} (hN : N = s + k + 1 + s) (e : Fin s → V) (β : Fin k → V) (z : V)
    (f : Fin s → V) : ∃ b : Fin N → V, (∀ (j : Fin N) (a : Fin s), j.1 = a.1 → b j = e a) ∧
      (∀ (j : Fin N) (a : Fin k), j.1 = s + a.1 → b j = β a) ∧ (∀ j : Fin N, j.1 = s + k → b j = z) ∧
      ∀ (j : Fin N) (a : Fin s), j.1 + a.1 + 1 = N → b j = f a := by
  refine ⟨fun j => if h : j.1 < s then e ⟨j.1, h⟩ else if h' : j.1 < s + k then β ⟨j.1 - s, by omega⟩
    else if h'' : j.1 = s + k then z else f ⟨N - 1 - j.1, by have := j.2; omega⟩, fun j a h => ?_, fun j a h => ?_,
    fun j h => ?_, fun j a h => ?_⟩
  · have := a.2
    beta_reduce
    rw [dif_pos (by omega)]
    exact congrArg e (Fin.ext h)
  · have := a.2
    beta_reduce
    rw [dif_neg (by omega), dif_pos (by omega)]
    exact congrArg β (Fin.ext (by simp only; omega))
  · beta_reduce
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos h]
  · have := a.2
    beta_reduce
    rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
    exact congrArg f (Fin.ext (by simp only; omega))

theorem index_cases {N k s : ℕ} (hN : N = s + k + 1 + s) (j : Fin N) :
    (∃ a : Fin s, j.1 = a.1) ∨ (∃ a : Fin k, j.1 = s + a.1) ∨ j.1 = s + k ∨ ∃ a : Fin s, j.1 + a.1 + 1 = N := by
  have := j.2
  by_cases h : j.1 < s
  · exact Or.inl ⟨⟨_, h⟩, rfl⟩
  by_cases h' : j.1 < s + k
  · exact Or.inr (Or.inl ⟨⟨j.1 - s, by omega⟩, by simp only; omega⟩)
  by_cases h'' : j.1 = s + k
  · exact Or.inr (Or.inr (Or.inl h''))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨N - 1 - j.1, by omega⟩, by simp only; omega⟩))

theorem exists_dual_families {V R : Type} [CommRing R] {N k s : ℕ} (hN : N = s + k + 1 + s) (h : V → V → R)
    (e f : Fin s → V) (β β' : Fin k → V) (z z' : V) :
    ∃ b b' : Fin N → V, (∀ j : Fin N, j.1 < s → b j = b' j.rev) ∧ (∀ j : Fin N, j.1 = s + k → b j = z ∧ b' j = z') ∧
      (∀ (j : Fin N) (a : Fin s), j.1 = a.1 → b j = e a ∧ b '' {i | i < j} = e '' {c | c.1 < a.1}) ∧
      (∀ (j : Fin N) (a : Fin k), j.1 = s + a.1 →
        b j = β a ∧ b '' {i | i < j} = Set.range e ∪ β '' {c | c.1 < a.1}) ∧
      b '' {i | i.1 < s} = Set.range e ∧
      ∀ 𝔞 : R → Prop, (∀ a c, 𝔞 (h (f a) (e c) - if a = c then 1 else 0) ∧ 𝔞 (h (e a) (f c) - if a = c then 1 else 0) ∧
          𝔞 (h (e a) (e c)) ∧ 𝔞 (h (f a) (f c))) →
        (∀ a c, 𝔞 (h (f a) (β c)) ∧ 𝔞 (h (e a) (β c)) ∧ 𝔞 (h (β' c) (e a)) ∧ 𝔞 (h (β' c) (f a))) →
        (∀ a, 𝔞 (h (f a) z) ∧ 𝔞 (h (e a) z) ∧ 𝔞 (h z' (e a)) ∧ 𝔞 (h z' (f a))) →
        (∀ a c, 𝔞 (h (β' a) (β c) - if a = c then 1 else 0)) → (∀ c, 𝔞 (h (β' c) z) ∧ 𝔞 (h z' (β c))) →
        𝔞 (h z' z - 1) → ∀ i j, 𝔞 (h (b' i) (b j) - if i = j then 1 else 0) := by
  obtain ⟨b, b1, b2, b3, b4⟩ := exists_family hN e β z f
  obtain ⟨b', c1, c2, c3, c4⟩ := exists_family hN f β' z' e
  have seg : ∀ (t : ℕ), t ≤ s → b '' {i | i.1 < t} = e '' {c | c.1 < t} := fun t ht => by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.1, lt_of_lt_of_le hi ht⟩, hi, (b1 _ _ rfl).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c.1, by have := c.2; omega⟩, hc, b1 _ _ rfl⟩
  have seg' : b '' {i | i.1 < s} = Set.range e := by
    rw [seg s le_rfl, ← Set.image_univ]
    exact congrArg _ (Set.eq_univ_of_forall fun c => c.2)
  refine ⟨b, b', fun j hj => ?_, fun j hj => ⟨b3 j hj, c3 j hj⟩, fun j a hj => ⟨b1 j a hj, ?_⟩,
    fun j a hj => ⟨b2 j a hj, ?_⟩, seg', fun 𝔞 g1 g2 g3 g4 g5 g6 i j => ?_⟩
  · rw [b1 j ⟨j.1, hj⟩ rfl, c4 j.rev ⟨j.1, hj⟩ (by rw [Fin.val_rev]; simp only; omega)]
  · rw [← seg a.1 a.2.le, ← hj]
    rfl
  · rw [← seg']
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i.1 < j.1 := hi
      have := a.2
      by_cases h : i.1 < s
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr ⟨⟨i.1 - s, by omega⟩, by show i.1 - s < a.1; omega, (b2 _ _ (by simp only; omega)).symm⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨c, hc, rfl⟩)
      · have hi' : i.1 < s := hi
        exact ⟨i, by show i.1 < j.1; omega, rfl⟩
      · have hc' : c.1 < a.1 := hc
        have := j.2
        exact ⟨⟨s + c.1, by omega⟩, by show s + c.1 < j.1; omega, b2 _ _ rfl⟩
  · have off : i.1 ≠ j.1 → ∀ x : R, 𝔞 x → 𝔞 (x - if i = j then 1 else 0) := fun hne x hx => by
      rwa [if_neg (fun e => hne (congrArg Fin.val e)), sub_zero]
    have on : ∀ {t : ℕ} (a c : Fin t), (i.1 = j.1 ↔ a.1 = c.1) → ∀ x : R,
        𝔞 (x - if a = c then 1 else 0) → 𝔞 (x - if i = j then 1 else 0) := fun a c hh x hx => by
      rwa [if_congr (Fin.ext_iff.trans (hh.trans Fin.ext_iff.symm)) rfl rfl]
    rcases index_cases hN i with ⟨a, ha⟩ | ⟨a, ha⟩ | ha | ⟨a, ha⟩ <;>
      rcases index_cases hN j with ⟨c, hc⟩ | ⟨c, hc⟩ | hc | ⟨c, hc⟩
    · rw [c1 i a ha, b1 j c hc]; exact on a c (by omega) _ (g1 a c).1
    · rw [c1 i a ha, b2 j c hc]; exact off (by omega) _ (g2 a c).1
    · rw [c1 i a ha, b3 j hc]; exact off (by omega) _ (g3 a).1
    · rw [c1 i a ha, b4 j c hc]; exact off (by omega) _ (g1 a c).2.2.2
    · rw [c2 i a ha, b1 j c hc]; exact off (by omega) _ (g2 c a).2.2.1
    · rw [c2 i a ha, b2 j c hc]; exact on a c (by omega) _ (g4 a c)
    · rw [c2 i a ha, b3 j hc]; exact off (by omega) _ (g5 a).1
    · rw [c2 i a ha, b4 j c hc]; exact off (by omega) _ (g2 c a).2.2.2
    · rw [c3 i ha, b1 j c hc]; exact off (by omega) _ (g3 c).2.2.1
    · rw [c3 i ha, b2 j c hc]; exact off (by omega) _ (g5 c).2
    · rw [c3 i ha, b3 j hc, if_pos (Fin.ext (ha.trans hc.symm))]; exact g6
    · rw [c3 i ha, b4 j c hc]; exact off (by omega) _ (g3 c).2.2.2
    · rw [c4 i a ha, b1 j c hc]; exact off (by omega) _ (g1 a c).2.2.1
    · rw [c4 i a ha, b2 j c hc]; exact off (by omega) _ (g2 a c).2.1
    · rw [c4 i a ha, b3 j hc]; exact off (by omega) _ (g3 a).2.1
    · rw [c4 i a ha, b4 j c hc]; exact on a c (by omega) _ (g1 a c).2.1

variable {I : AutInst}

theorem mem_mL {m : ℕ} {x : VA I} : x ∈ mL I m ↔ ∃ z ∈ I.Lf, x = (m : I.E ⊗[I.F] Af I.F) • z := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
  | smul a x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨a • z, Submodule.smul_mem _ a hz, smul_comm (a : I.E ⊗[I.F] Af I.F) _ z⟩

theorem inMod_iff (m : ℕ) (S : Set I.Lf) (y : VA I) : InMod I m (Subtype.val '' S) y ↔
    ∃ t ∈ Submodule.span (IntAf I.F I.E) S, ∃ z ∈ I.Lf, y = t.1 + (m : I.E ⊗[I.F] Af I.F) • z := by
  unfold InMod
  rw [← Submodule.coe_subtype, ← Submodule.map_span, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, u, hu, rfl⟩
    obtain ⟨z, hz, rfl⟩ := mem_mL.1 hu
    exact ⟨t, ht, z, hz, rfl⟩
  · rintro ⟨t, ht, z, hz, rfl⟩
    exact ⟨_, ⟨t, ht, rfl⟩, _, mem_mL.2 ⟨z, hz, rfl⟩, rfl⟩

theorem mem_span_of_zmod {m : ℕ} {a : IntAf I.F I.E} (h : ZMod' I m a) : a ∈ Ideal.span {(m : IntAf I.F I.E)} := by
  obtain ⟨t, ht, e⟩ := h
  refine Ideal.mem_span_singleton.2 ⟨⟨t, ht⟩, Subtype.ext ?_⟩
  simpa using e

theorem sigI_mem {m : ℕ} {a : IntAf I.F I.E} (h : a ∈ Ideal.span {(m : IntAf I.F I.E)}) :
    sigI I a ∈ Ideal.span {(m : IntAf I.F I.E)} := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.1 h
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem hI_neg (x y : I.Lf) : hI (-x) y = -hI x y := by
  rw [← sigI_hI, ← neg_one_smul (IntAf I.F I.E) x, hI_smul, map_mul, sigI_hI, map_neg, map_one, neg_one_mul]

set_option maxHeartbeats 800000 in

theorem vol_ratio_frame {N f k s : ℕ} (hN : N = s + k + 1 + s) (hn : I.n = N) (g : Fin 2 → ℕ)
    (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (hrad : ∀ i, (Ideal.span {((g i : ℕ) : 𝓞 I.E)}).IsRadical)
    (hsp : ∀ i (v : HeightOneSpectrum (𝓞 I.E)), ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g i)
    (hf : 0 < f) (hcard : ∀ i, {v : HeightOneSpectrum (𝓞 I.E) | ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * f)
    (G : ℕ) (hG : G = g 0 * g 1) (𝔤 : Ideal (IntAf I.F I.E)) (h𝔤 : 𝔤 = Ideal.span {(G : IntAf I.F I.E)})
    (ε : IntAf I.F I.E) (e1 : ε * ε = ε) (e2 : ε * sigI I ε = 0) (e f' : Fin s → I.Lf) (z : I.Lf) (β β' : Fin k → I.Lf)
    (e3 : ∃ y : I.Lf, (1 - ε - sigI I ε) • z = (G : IntAf I.F I.E) • y)
    (g1 : ∀ a c, hI (e a) (e c) ∈ 𝔤 ∧ hI (f' a) (f' c) ∈ 𝔤 ∧ (hI (e a) (f' c) - if a = c then 1 else 0) ∈ 𝔤)
    (g2 : hI z z + 1 ∈ 𝔤) (g3 : ∀ a, hI (e a) z ∈ 𝔤 ∧ hI (f' a) z ∈ 𝔤)
    (g4 : ∀ i, hI z (β i) ∈ 𝔤 ∧ hI z (β' i) ∈ 𝔤 ∧
      ∀ a, hI (e a) (β i) ∈ 𝔤 ∧ hI (f' a) (β i) ∈ 𝔤 ∧ hI (e a) (β' i) ∈ 𝔤 ∧ hI (f' a) (β' i) ∈ 𝔤)
    (g5 : ∀ i j, (hI (β' i) (β j) - if i = j then ε else 0) ∈ 𝔤) (hβ : ∀ i, ε • β i = β i)
    (μf : Measure I.Gf) [μf.IsHaarMeasure] :
    (μf I.Kset).toReal / (μf (K2set I G (fun a => (e a).1) z.1 fun i => (β i).1)).toReal =
      Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 0)) N (Formalism.MainNotions.StandardLattice.IsRowLev k s) ^ f *
        Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 1)) N (Formalism.MainNotions.StandardLattice.IsRowLev k s) ^ f := by
  obtain ⟨b, b', b1, b2, b3, b4, b5, b6⟩ := exists_dual_families hN (hI (I := I)) e f' β β' z (-z)
  have hle : ∀ l (v : HeightOneSpectrum (𝓞 I.E)), ((g l : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 𝔤 ≤ extId I v.asIdeal := by
    intro l v hv
    rw [h𝔤, Ideal.span_singleton_le_iff_mem, extId_eq_map_psi, ← map_natCast (psi I.F I.E) G]
    refine Ideal.mem_map_of_mem _ ?_
    rw [hG, Nat.cast_mul]
    fin_cases l
    · exact Ideal.mul_mem_right _ _ hv
    · exact Ideal.mul_mem_left _ _ hv
  have sw : ∀ {x y : I.Lf}, hI x y ∈ 𝔤 → hI y x ∈ 𝔤 := fun {x y} h => by
    rw [← sigI_hI, h𝔤]
    exact sigI_mem (h𝔤 ▸ h)
  have sw' : ∀ a c, (hI (f' a) (e c) - if a = c then 1 else 0) ∈ 𝔤 := fun a c => by
    have h := sigI_mem (h𝔤 ▸ (g1 c a).2.2)
    rw [map_sub, sigI_hI, apply_ite (sigI I), map_one, map_zero, if_congr eq_comm rfl rfl] at h
    exact h𝔤 ▸ h
  have e4 : 1 - ε - sigI I ε ∈ 𝔤 := by
    obtain ⟨y, hy⟩ := e3
    have h := congrArg (hI z) hy
    rw [hI_smul, hI_smul] at h
    have h' : 1 - ε - sigI I ε = (1 - ε - sigI I ε) * (hI z z + 1) - G * hI z y := by rw [← h]; ring
    rw [h']
    exact sub_mem (Ideal.mul_mem_left _ _ g2) (Ideal.mul_mem_right _ _ (h𝔤 ▸ Ideal.mem_span_singleton_self _))
  refine vol_ratio_rows hN hn g hg hne hrad hsp hf hcard ε e1 e2 (fun l v hv => hle l v hv e4) b b'
    (fun l v hv hε => ?_) b1 (fun j hj => by rw [(b2 j hj).1, (b2 j hj).2, neg_neg]) (fun j hj hj' => ?_) μf _
    fun x => ?_
  · have L := hle l v hv
    refine b6 (· ∈ extId I v.asIdeal) (fun a c => ⟨L (sw' a c), L (g1 a c).2.2, L (g1 a c).1, L (g1 a c).2.1⟩)
      (fun a c => ⟨L ((g4 c).2.2 a).2.1, L ((g4 c).2.2 a).1, L (sw ((g4 c).2.2 a).2.2.1),
        L (sw ((g4 c).2.2 a).2.2.2)⟩)
      (fun a => ⟨L (g3 a).2, L (g3 a).1, ?_, ?_⟩) (fun a c => ?_) (fun c => ⟨L (sw (g4 c).2.1), ?_⟩) ?_
    · rw [hI_neg]; exact neg_mem (L (sw (g3 a).1))
    · rw [hI_neg]; exact neg_mem (L (sw (g3 a).2))
    · have h := L (g5 a c)
      split_ifs at h ⊢
      · have := sub_mem h hε
        rwa [sub_sub, add_sub_cancel] at this
      · exact h
    · rw [hI_neg]; exact neg_mem (L (g4 c).1)
    · rw [hI_neg, ← neg_add']; exact neg_mem (L g2)
  · rw [(b4 j ⟨j.1 - s, by omega⟩ (by simp only; omega)).1, hβ]
  · subst hG
    show x ∈ I.Kset ∧ _ ↔ _
    rw [← exists_prop]
    refine exists_congr fun hx => ?_
    have hc : ∀ y : I.Lf, (latEnd hx y - y).1 = (I.fmat x - 1) *ᵥ y.1 := fun y => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
    simp only [hc, ← inMod_iff]
    have i1 : ∀ S, (fun a => (e a).1) '' S = Subtype.val '' (e '' S) := fun S => (Set.image_image _ _ _).symm
    have i2 : ∀ S, (fun a => (β a).1) '' S = Subtype.val '' (β '' S) := fun S => (Set.image_image _ _ _).symm
    have i3 : (Set.range fun a => (e a).1) = Subtype.val '' Set.range e := Set.range_comp Subtype.val e
    unfold K2cong
    simp only [i1, i2, i3, ← Set.image_union]
    constructor
    · rintro ⟨H1, H2, H3⟩
      refine ⟨fun j hj => ?_, fun j hj => by rw [b5, (b2 j hj).1]; exact H2⟩
      by_cases h : j.1 < s
      · rw [(b3 j ⟨_, h⟩ rfl).1, (b3 j ⟨_, h⟩ rfl).2]; exact H1 _
      · have h' : j.1 = s + (⟨j.1 - s, by omega⟩ : Fin k).1 := by simp only; omega
        rw [(b4 j _ h').1, (b4 j _ h').2]; exact H3 _
    · rintro ⟨H1, H2⟩
      refine ⟨fun a => ?_, ?_, fun a => ?_⟩
      · have ha := a.2
        have h := H1 ⟨a.1, by omega⟩ (by simp only; omega)
        rwa [(b3 _ a rfl).1, (b3 _ a rfl).2] at h
      · have h := H2 ⟨s + k, by omega⟩ rfl
        rwa [b5, (b2 _ rfl).1] at h
      · have ha := a.2
        have h := H1 ⟨s + a.1, by omega⟩ (by simp only; omega)
        rwa [(b4 _ a rfl).1, (b4 _ a rfl).2] at h

theorem volume_ratio_eq_signature_index : ∀ (D : D7) (X : HidaSetting D),
    (X.B.μf X.B.I.Kset).toReal / X.volK2 = Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) := by
  intro D X
  have hm := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  have hN : D.R.r = D.R.rS + D.R.k + 1 + D.R.rS := by unfold Ranks.r Ranks.rS; omega
  have hE : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
    ring
  have hs := fun i => split_facts X.ιE (D.host.g_prime i) (D.nd.g_split i)
  obtain ⟨i1, i2, i3⟩ := X.vectorsInLattice
  obtain ⟨y, hy, ey⟩ := mem_mL.1 (X.ew_full _ i2)
  refine vol_ratio_frame hN X.n_eq D.host.g D.host.g_prime D.host.g_ne (fun i => (hs i).2.1) (fun i => (hs i).2.2)
    (by unfold Ranks.f Ranks.n; positivity) (fun i => (hs i).1.trans hE) X.B.g X.g_eq _ rfl ⟨X.ew, X.ew_int⟩ (Subtype.ext X.ew_idem)
    (Subtype.ext X.ew_orth) (fun a => ⟨X.e0 a, (i1 a).1⟩) (fun a => ⟨X.f0 a, (i1 a).2⟩) ⟨X.z0, i2⟩
    (fun i => ⟨X.bw i, (i3 i).1⟩) (fun i => ⟨X.bwd i, (i3 i).2⟩) ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    (fun a c => ⟨mem_span_of_zmod (X.gramIntegral a c).1, mem_span_of_zmod (X.gramIntegral a c).2.1, mem_span_of_zmod ?_⟩)
    (mem_span_of_zmod X.formsAtZero.1) (fun a => ⟨mem_span_of_zmod (X.formsAtZero.2 a).1, mem_span_of_zmod (X.formsAtZero.2 a).2⟩)
    (fun i => ⟨mem_span_of_zmod (X.weightVectorsIntegral i).1, mem_span_of_zmod (X.weightVectorsIntegral i).2.1, fun a =>
      ⟨mem_span_of_zmod ((X.weightVectorsIntegral i).2.2 a).1, mem_span_of_zmod ((X.weightVectorsIntegral i).2.2 a).2.1,
        mem_span_of_zmod ((X.weightVectorsIntegral i).2.2 a).2.2.1, mem_span_of_zmod ((X.weightVectorsIntegral i).2.2 a).2.2.2⟩⟩)
    (fun i j => mem_span_of_zmod ?_) (fun i => Subtype.ext (X.bw_w i).symm) X.B.μf
  · refine ey.trans ?_
    show _ = (((X.B.g : ℕ) : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y
    rw [Subring.coe_natCast]
  · have h := (X.gramIntegral a c).2.2
    split_ifs at h ⊢ <;> exact h
  · have h := X.bw_dual i j
    split_ifs at h ⊢ <;> exact h

end GlobalTheory.RowIndex
