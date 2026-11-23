import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SemiCharBasic
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.LineTransport

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

theorem InterClass_of (h : SemiHom) : InterClass := by
  intro V _ _ H hH Λ₁ Λ₂ α hα F hF x hx y hy hy1 z
  have hF' : ∀ w ∈ Λ₁, ∀ v, α w * opU H w F v = F v := hF
  have hfun : (fun v => α y * opU H y F v) = F := funext fun v => hF' y hy1 v
  have e := h V H hH Λ₂ α hα x hx y hy F z
  exact e.symm.trans (congrArg (fun G => α x * opU H x G z) hfun)

section Reps

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def repClass {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (x : S) :
    Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ :=
  QuotientAddGroup.mk (⟨x.1, hS.1 x.1 x.2⟩ : Λ₂)

private theorem quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem {Λ₁ Λ₂ : AddSubgroup V} (a b : Λ₂) :
    (QuotientAddGroup.mk a : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = QuotientAddGroup.mk b ↔
      ((b : V) - (a : V)) ∈ Λ₁ := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
    AddSubgroup.coe_neg, neg_add_eq_sub]

theorem repClass_bijective {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    Function.Bijective (repClass hS) := by
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h := (quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem (Λ₁ := Λ₁) (⟨a, hS.1 a ha⟩ : Λ₂) ⟨b, hS.1 b hb⟩).1 hab
    exact Subtype.ext (hS.2.1 b hb a ha h).symm
  · intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨x, hxS, hyx⟩ := hS.2.2 y hy
    exact ⟨⟨x, hxS⟩, (quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem (Λ₁ := Λ₁) (⟨x, hS.1 x hxS⟩ : Λ₂) ⟨y, hy⟩).2 hyx⟩

private theorem quotient_addSubgroupOf_mk_out {Λ₁ Λ₂ : AddSubgroup V} (c : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) :
    (QuotientAddGroup.mk (Quotient.out c) : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = c := by
  exact Quotient.out_eq c

private theorem sub_quotient_out_mem_of_mk_eq {Λ₁ Λ₂ : AddSubgroup V} (c : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) (y : Λ₂)
    (hc : (QuotientAddGroup.mk y : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = c) :
    (y : V) - ((Quotient.out c : Λ₂) : V) ∈ Λ₁ := by
  have h1 : (QuotientAddGroup.mk (Quotient.out c) : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) =
      QuotientAddGroup.mk y := by
    rw [hc]; exact quotient_addSubgroupOf_mk_out c
  exact (quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem (Λ₁ := Λ₁) (Quotient.out c) y).1 h1

theorem reps_translate {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} [DecidableEq V] (hS : IsReps Λ₁ Λ₂ S)
    {y : V} (hy : y ∈ Λ₂) : IsReps Λ₁ Λ₂ (S.image (fun x => y + x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    exact Λ₂.add_mem hy (hS.1 a ha)
  · intro x hx x' hx' hxx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx'
    have hab : a - b ∈ Λ₁ := by
      have e : (y + a) - (y + b) = a - b := by abel
      have hxx' : (y + a) - (y + b) ∈ Λ₁ := hxx
      rw [e] at hxx'
      exact hxx'
    exact congrArg (fun t => y + t) (hS.2.1 a ha b hb hab)
  · intro w hw
    obtain ⟨a, ha, hwa⟩ := hS.2.2 (w - y) (Λ₂.sub_mem hw hy)
    refine ⟨y + a, Finset.mem_image.2 ⟨a, ha, rfl⟩, ?_⟩
    have e : w - (y + a) = w - y - a := by abel
    rw [e]; exact hwa

end Reps

theorem cosetRepsExist : RepsExist := by
  intro V _ _ Λ₁ Λ₂ hne
  classical
  have hQ : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hne
  refine ⟨?_, fun S hS => ?_⟩
  · letI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _
    refine ⟨Finset.univ.image (fun c : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ => ((Quotient.out c : Λ₂) : V)),
      ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      exact (Quotient.out c).2
    · intro x hx y hy hxy
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
      have h1 := (quotient_addSubgroupOf_mk_eq_mk_iff_sub_mem (Λ₁ := Λ₁) (Quotient.out d) (Quotient.out c)).2 hxy
      rw [quotient_addSubgroupOf_mk_out, quotient_addSubgroupOf_mk_out] at h1
      rw [h1]
    · intro y hy
      refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨y, hy⟩ : Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) : Λ₂) : V),
        Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      exact sub_quotient_out_mem_of_mk_eq _ ⟨y, hy⟩ rfl
  · have h1 := Nat.card_eq_of_bijective _ (repClass_bijective hS)
    have h2 : Nat.card S = S.card := by
      exact Nat.card_eq_finsetCard S
    rw [h2] at h1
    exact h1

theorem InterReps_of (h : SemiHom) : InterReps := by
  intro V _ _ H hH Λ₁ Λ₂ α hα F hF S hS z
  classical
  have hcl := InterClass_of h V H hH Λ₁ Λ₂ α hα F hF
  letI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofBijective _ (repClass_bijective hS)
  unfold inter sumU
  congr 1
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort S]
  symm
  refine Fintype.sum_bijective (repClass hS) (repClass_bijective hS) _ _ ?_
  intro s
  show α (s : V) * opU H (s : V) F z = _
  have hmem := sub_quotient_out_mem_of_mk_eq (repClass hS s) ⟨s, hS.1 s s.2⟩ rfl
  have h2 := hcl ((Quotient.out (repClass hS s) : Λ₂) : V) (Quotient.out (repClass hS s)).2
    ((s : V) - ((Quotient.out (repClass hS s) : Λ₂) : V))
    (Λ₂.sub_mem (hS.1 s s.2) (Quotient.out (repClass hS s)).2) hmem z
  rw [show ∀ a b : V, a + (b - a) = b from fun a b => by abel] at h2
  exact h2

private theorem semiChar_mul_opU_const_mul_sumU {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ)
    (S : Finset V) (F : V → ℂ) (k : ℂ) (y z : V) :
    α y * opU H y (fun v => k * sumU H α S F v) z
      = k * ∑ x ∈ S, α y * opU H y (fun v => α x * opU H x F v) z := by
  simp only [opU, sumU, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem InterFixed_of (h : SemiHom) : InterFixed := by
  intro V _ _ H hH Λ₁ Λ₂ α hα hne F hF
  classical
  obtain ⟨S, hS⟩ := (cosetRepsExist V Λ₁ Λ₂ hne).1
  have hrep := InterReps_of h V H hH Λ₁ Λ₂ α hα F hF
  have hG : inter H α Λ₁ Λ₂ F
      = fun v => ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * sumU H α S F v :=
    funext (hrep S hS)
  show ∀ y ∈ Λ₂, ∀ z, α y * opU H y (inter H α Λ₁ Λ₂ F) z = inter H α Λ₁ Λ₂ F z
  intro y hy z
  calc α y * opU H y (inter H α Λ₁ Λ₂ F) z
      = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ *
          ∑ x ∈ S, α y * opU H y (fun v => α x * opU H x F v) z := by
        rw [hG]; exact semiChar_mul_opU_const_mul_sumU H α S F _ y z
    _ = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ *
          ∑ x ∈ S, α (y + x) * opU H (y + x) F z := by
        congr 1
        exact Finset.sum_congr rfl fun x hx => h V H hH Λ₂ α hα y hy x (hS.1 x hx) F z
    _ = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ *
          sumU H α (S.image (fun x => y + x)) F z := by
        congr 1
        unfold sumU
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact add_left_cancel hab
    _ = inter H α Λ₁ Λ₂ F z := (hrep _ (reps_translate hS hy) z).symm

theorem InterTh_of (h : SemiHom) (ha : OpUAnalytic) : InterTh := by
  intro V _ _ _ H hH Λ₁ Λ₂ α hα hne F hF
  classical
  have hF' : AnalyticOnNhd ℂ F Set.univ ∧ F ∈ fixedBy H α Λ₁ := hF
  obtain ⟨S, hS⟩ := (cosetRepsExist V Λ₁ Λ₂ hne).1
  have hsum : ∀ T : Finset V,
      AnalyticOnNhd ℂ (fun v => ∑ x ∈ T, α x * opU H x F v) Set.univ := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro w _
      simp only [Finset.sum_empty]
      exact analyticAt_const
    · intro a T haT ih w hw
      simp only [Finset.sum_insert haT]
      exact (analyticAt_const.mul (ha V H a F hF'.1 w hw)).add (ih w hw)
  have hrep := InterReps_of h V H hH Λ₁ Λ₂ α hα F hF'.2
  have hG : inter H α Λ₁ Λ₂ F
      = fun v => ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * sumU H α S F v :=
    funext (hrep S hS)
  show AnalyticOnNhd ℂ (inter H α Λ₁ Λ₂ F) Set.univ ∧
    inter H α Λ₁ Λ₂ F ∈ fixedBy H α Λ₂
  refine ⟨?_, InterFixed_of h V H hH Λ₁ Λ₂ α hα hne F hF'.2⟩
  rw [hG]
  intro w hw
  exact analyticAt_const.mul (hsum S w hw)

theorem ThIsom_of (h : OpUIsom) : ThIsom := by
  intro V W _ _ _ _ _ _ H H' g hiso Λ α' G
  have hgA : ∀ v : V, AnalyticAt ℂ (fun v => g v) v := by
    intro v
    have := (LinearMap.toContinuousLinearMap (g : V →ₗ[ℂ] W)).analyticAt v
    exact this
  have hgsA : ∀ w : W, AnalyticAt ℂ (fun w => g.symm w) w := by
    intro w
    have := (LinearMap.toContinuousLinearMap (g.symm : W →ₗ[ℂ] V)).analyticAt w
    exact this
  constructor
  · intro hG
    have hG' : AnalyticOnNhd ℂ G Set.univ ∧
        G ∈ fixedBy H' α' (imgLat (g : V →ₗ[ℂ] W) Λ) := hG
    have hinv : ∀ x ∈ imgLat (g : V →ₗ[ℂ] W) Λ, ∀ z, α' x * opU H' x G z = G z :=
      hG'.2
    show AnalyticOnNhd ℂ (fun v => G (g v)) Set.univ ∧
      (fun v => G (g v)) ∈ fixedBy H (fun v => α' (g v)) Λ
    refine ⟨fun v _ => (hG'.1 (g v) (Set.mem_univ _)).comp (hgA v), ?_⟩
    show ∀ x ∈ Λ, ∀ z, α' (g x) * opU H x (fun v => G (g v)) z = G (g z)
    intro x hx z
    have e := h V W H H' (g : V →ₗ[ℂ] W) hiso x G z
    have m : (g : V →ₗ[ℂ] W) x ∈ imgLat (g : V →ₗ[ℂ] W) Λ :=
      AddSubgroup.mem_map_of_mem (g : V →ₗ[ℂ] W).toAddMonoidHom hx
    have h3 := hinv _ m (g z)
    exact (congrArg (fun t => α' (g x) * t) e).trans h3
  · intro hG
    have hG' : AnalyticOnNhd ℂ (fun v => G (g v)) Set.univ ∧
        (fun v => G (g v)) ∈ fixedBy H (fun v => α' (g v)) Λ := hG
    have hinv : ∀ x ∈ Λ, ∀ z, α' (g x) * opU H x (fun v => G (g v)) z = G (g z) :=
      hG'.2
    show AnalyticOnNhd ℂ G Set.univ ∧ G ∈ fixedBy H' α' (imgLat (g : V →ₗ[ℂ] W) Λ)
    refine ⟨fun w _ => ?_, ?_⟩
    · have h3 := (hG'.1 (g.symm w) (Set.mem_univ _)).comp (hgsA w)
      have e : ((fun v => G (g v)) ∘ fun w => g.symm w) = G := funext fun w => by simp
      rw [e] at h3
      exact h3
    · show ∀ x ∈ imgLat (g : V →ₗ[ℂ] W) Λ, ∀ z, α' x * opU H' x G z = G z
      intro x hx z
      have hx' : x ∈ Λ.map (g : V →ₗ[ℂ] W).toAddMonoidHom := hx
      obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx'
      have e := h V W H H' (g : V →ₗ[ℂ] W) hiso y G (g.symm z)
      have hz : (g : V →ₗ[ℂ] W) (g.symm z) = z := g.apply_symm_apply z
      rw [hz] at e
      have h3 := hinv y hy (g.symm z)
      have h4 : G (g (g.symm z)) = G z := by rw [g.apply_symm_apply]
      exact (congrArg (fun t => α' (g y) * t) e).symm.trans (h3.trans h4)

end Formalism.L2.Th1.H
