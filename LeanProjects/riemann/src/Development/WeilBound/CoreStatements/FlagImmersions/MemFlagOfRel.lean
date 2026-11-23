import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

noncomputable section

namespace RootFieldNumerics.Rig

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.HodgeExt

theorem exists_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ : Type}
    {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)} (h : FibreLatVec t z R x v) {V : Type} [AddCommGroup V] [Module ℂ V]
    (Mz : LieModel t.G z V) : ∃ Rel : Submodule ℂ ((Fin g → ℂ) × V), (∀ a s, v a = Mz.pt s → (x a, s) ∈ Rel) ∧
      (∀ d, (d, 0) ∈ Rel → d = 0) ∧ ∀ s, (0, s) ∈ Rel → s = 0 := by
  obtain ⟨A, _, φ, u, χ, hp, -, -, -, -, hv⟩ := h
  have h1 : lft hp (1 : epsAt z ⟶ t.G) = 1 := by
    have := lft_mul hp (1 : epsAt z ⟶ t.G) 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have h0 : u.IsDiff 0 (lft hp (Mz.pt 0)) := by
    rw [Mz.pt_zero, h1, Hom.one_def]
    exact GlobalTheory.ArchMetricCompare.isDiff_zero u
  have hc : ∀ (c c' : ℂ) (p q : (Fin g → ℂ) × V), u.IsDiff p.1 (lft hp (Mz.pt p.2)) → u.IsDiff q.1 (lft hp (Mz.pt q.2)) →
      u.IsDiff (c • p.1 + c' • q.1) (lft hp (Mz.pt (c • p.2 + c' • q.2))) := fun c c' p q a b => by
    have := HodgePull.isDiff_comb Mz hp u ![p.2, q.2] ![p.1, q.1] (fun l => by fin_cases l; exacts [a, b]) 0 ![c, c']
    simpa [Fin.sum_univ_two] using this
  have ht : ∀ s, IsTangent (lft hp (Mz.pt s)) := fun s => isTangent_lft hp (Mz.tan s)
  refine ⟨{ carrier := {p | u.IsDiff p.1 (lft hp (Mz.pt p.2))}
            add_mem' := fun {p q} a b => by simpa using hc 1 1 p q a b
            zero_mem' := h0
            smul_mem' := fun c p a => by simpa using hc c 0 p p a a }, fun a s e => ?_, fun d hd => ?_, fun s hs => ?_⟩
  · obtain ⟨v', e', hd⟩ := hv a
    show u.IsDiff (x a) (lft hp (Mz.pt s))
    rw [← e, ← lft_unique hp e']
    exact hd
  · exact eq_of_isDiff u (ht 0) hd h0
  · have e := GlobalTheory.ArchMetricCompare.eq_of_isDiff u (ht s) (ht 0) hs h0
    apply Mz.inj
    apply Over.OverMorphism.ext
    rw [← lft_left hp (Mz.pt s), e, lft_left]

section Lin

variable {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] {Rel : Submodule ℂ (W × V)} {m : ℕ}

theorem indep_of_rel (h1 : ∀ d, (d, 0) ∈ Rel → d = 0) {x : Fin m → W} {ω : Fin m → V} (h : ∀ i, (x i, ω i) ∈ Rel)
    (hx : LinearIndependent ℂ x) : LinearIndependent ℂ ω := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro c hc
  refine hx c (h1 _ ?_)
  have := Rel.sum_mem (t := Finset.univ) fun i _ => Rel.smul_mem (c i) (h i)
  convert this using 1
  ext
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, hc]

theorem mem_flag_of_rel (h2 : ∀ s, (0, s) ∈ Rel → s = 0) {x : Fin m → W} {ω : Fin m → V} (h : ∀ i, (x i, ω i) ∈ Rel)
    {k : ℕ} {d : W} {s : V} (hd : (d, s) ∈ Rel) (hm : d ∈ flagStep ℂ x k) : s ∈ flagStep ℂ ω k := by
  have key : ∀ d ∈ flagStep ℂ x k, ∃ s ∈ flagStep ℂ ω k, (d, s) ∈ Rel := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact ⟨ω i, Submodule.subset_span ⟨i, hi, rfl⟩, h i⟩
    | zero => exact ⟨0, Submodule.zero_mem _, Rel.zero_mem⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨s', hs', hb⟩ := hb
      exact ⟨s + s', Submodule.add_mem _ hs hs', Rel.add_mem ha hb⟩
    | smul c a _ ha =>
      obtain ⟨s, hs, ha⟩ := ha
      exact ⟨c • s, Submodule.smul_mem _ c hs, Rel.smul_mem c ha⟩
  obtain ⟨s', hs', hr⟩ := key d hm
  have e : s - s' = 0 := h2 _ (by simpa using Rel.sub_mem hd hr)
  rwa [sub_eq_zero.1 e]

theorem flag_le_of_rel (h2 : ∀ s, (0, s) ∈ Rel → s = 0) {x x' : Fin m → W} {ω ω' : Fin m → V} (h : ∀ i, (x i, ω i) ∈ Rel)
    (h' : ∀ i, (x' i, ω' i) ∈ Rel) {k : ℕ} (e : flagStep ℂ x k = flagStep ℂ x' k) : flagStep ℂ ω' k ≤ flagStep ℂ ω k := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, hi, rfl⟩
  exact mem_flag_of_rel h2 h (h' i) (e ▸ Submodule.subset_span ⟨i, hi, rfl⟩)

theorem tri_unique {α ω : Fin m → V} (hα : LinearIndependent ℂ α) {u u' : Fin m → Fin m → ℂ} (h1 : ∀ k, u k k = 1)
    (h0 : ∀ l k, l < k → u l k = 0) (h1' : ∀ k, u' k k = 1) (h0' : ∀ l k, l < k → u' l k = 0)
    (hu : ∀ k : Fin m, ∑ l, u l k • α l ∈ flagStep ℂ ω (k + 1)) (hu' : ∀ k : Fin m, ∑ l, u' l k • α l ∈ flagStep ℂ ω (k + 1)) :
    u = u' := by
  classical
  let ε : Fin m → V := fun k => ∑ l, u l k • α l
  have hco : ∀ (t : Fin m → ℂ) (c : Fin m → ℂ), ∑ i, t i • ε i = ∑ l, c l • α l → ∀ l, ∑ i, t i * u l i = c l := by
    intro t c e
    have e2 : ∑ l, ((∑ i, t i * u l i) - c l) • α l = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← e, ε, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm, sub_self]
    exact fun l => sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hα _ e2 l)
  have hlow : ∀ (t : Fin m → ℂ) (l : Fin m), (∀ i, i < l → t i = 0) → ∑ i, t i * u l i = t l := by
    intro t l ht
    rw [Finset.sum_eq_single l, h1, _root_.mul_one]
    · intro i _ hi
      rcases lt_or_gt_of_ne hi with h | h
      · rw [ht i h, zero_mul]
      · rw [h0 l i h, mul_zero]
    · simp
  have hvan : ∀ (t c : Fin m → ℂ) (k : ℕ), (∀ l, ∑ i, t i * u l i = c l) → (∀ l : Fin m, (l : ℕ) < k → c l = 0) →
      ∀ l : Fin m, (l : ℕ) < k → t l = 0 := by
    intro t c k e hc l
    induction l using WellFoundedLT.induction with
    | ind l ih =>
      intro hl
      rw [← hlow t l fun i hi => ih i hi (lt_trans hi hl), e, hc l hl]
  have hε : LinearIndependent ℂ ε := by
    rw [Fintype.linearIndependent_iff]
    intro t ht l
    exact hvan t 0 m (hco t 0 (by simpa using ht)) (fun _ _ => rfl) l l.2
  have hfl : ∀ k : ℕ, flagStep ℂ ε k = flagStep ℂ ω k := fun k => by
    have hle : flagStep ℂ ε k ≤ flagStep ℂ ω k := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      refine Submodule.span_mono (Set.image_mono fun j hj => ?_) (hu i)
      exact lt_of_lt_of_le (show (j : ℕ) < i + 1 from hj) hi
    haveI : FiniteDimensional ℂ (flagStep ℂ ω k) := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    unfold flagStep
    rw [Set.image_eq_range, Set.image_eq_range]
    exact (finrank_range_le_card _).trans (finrank_span_eq_card (hε.comp _ Subtype.val_injective)).ge
  funext l k
  have hm := hu' k
  rw [← hfl] at hm
  obtain ⟨t, ht, e⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hm
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
  have e1 := hco t _ e
  have e2 := hvan t _ k e1 fun l hl => h0' l k hl
  have e3 : t k = 1 := by rw [← hlow t k fun i hi => e2 i hi, e1, h1']
  rw [← e1 l, Finset.sum_eq_single k, e3, _root_.one_mul]
  · intro i _ hi
    rcases lt_or_gt_of_ne hi with h | h
    · rw [e2 i h, zero_mul]
    · have : t i = 0 := by
        by_contra hne
        have h6 : (i : ℕ) < k + 1 := ht (Finsupp.mem_support_iff.2 hne)
        have h7 : (k : ℕ) < i := h
        omega
      rw [this, zero_mul]
  · simp

end Lin

end RootFieldNumerics.Rig
