import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertTypeEigenvaluesIffLabelEigensystemsRowsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftInertEigenvaluesIffThetaImageEigensystemStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrPass

theorem sep_extend {α κ K : Type} [Field K] [CharZero K] (S : Finset α) (C : α → Prop) (f : α → κ → K) (k0 : κ) :
    ∃ g : α → κ → K, (∀ a, C a → g a = f a) ∧
      ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → ¬ (C a ∧ C a') → g a k0 ≠ g a' k0 := by
  classical
  set Ex : Finset K := (S.filter C).image (fun a => f a k0)
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hinf : ((Ex : Set K)ᶜ).Infinite := Ex.finite_toSet.infinite_compl
  haveI := hinf.to_subtype
  let e : ℕ ↪ ((Ex : Set K)ᶜ : Set K) := Infinite.natEmbedding _
  set U := S.filter (fun a => ¬ C a)
  let idx : α → ℕ := fun a => if h : a ∈ U then ((U.equivFin ⟨a, h⟩ : Fin U.card) : ℕ) else 0
  refine ⟨fun a => if C a then f a else fun _ => (e (idx a) : K), fun a ha => by simp [ha], ?_⟩
  intro a ha a' ha' hne hC
  have hidx : ∀ b ∈ S, ¬ C b → ∀ b' ∈ S, ¬ C b' → idx b = idx b' → b = b' := by
    intro b hb hCb b' hb' hCb' h
    have hbU : b ∈ U := Finset.mem_filter.2 ⟨hb, hCb⟩
    have hbU' : b' ∈ U := Finset.mem_filter.2 ⟨hb', hCb'⟩
    simp only [idx, dif_pos hbU, dif_pos hbU'] at h
    have := U.equivFin.injective (Fin.ext h)
    exact congrArg Subtype.val this
  have hnot : ∀ n, (e n : K) ∉ Ex := fun n => (e n).2
  by_cases h1 : C a
  · have h2 : ¬ C a' := fun h2 => hC ⟨h1, h2⟩
    simp only [if_pos h1, if_neg h2]
    intro h
    have hm : f a k0 ∈ Ex := Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, h1⟩, rfl⟩
    rw [h] at hm
    exact hnot _ hm
  · by_cases h2 : C a'
    · simp only [if_neg h1, if_pos h2]
      intro h
      have hm : f a' k0 ∈ Ex := Finset.mem_image.2 ⟨a', Finset.mem_filter.2 ⟨ha', h2⟩, rfl⟩
      rw [← h] at hm
      exact hnot _ hm
    · simp only [if_neg h1, if_neg h2]
      intro h
      exact hne (hidx a ha h1 a' ha' h2 (e.injective (Subtype.ext h)))

end GlobalTheory.TrPass

namespace GlobalTheory.TrPass

theorem exists_inert_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hCW hEx hSch hJ hAbs hPB hPP
  classical
  have hlab : ∀ (j : Fin D.R.m) P d, IsLab (Yc D 0) P d ↔ IsLab (Wc D j) P d := by
    intro j P d
    rw [GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing, GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing]
    have h1 : (Yc D 0).rank = D.R.r := by
      rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
    have h2 : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
    rw [h1, h2]
  let Wit : ∀ j : Fin D.R.m, A3.fam3.base3.Ix → (Pl D.host.E → List ℤ → ℂ) →
      ((A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) → Prop :=
    fun j p c s => R.Carries p c ∧ ∃ x : (A3.A.fam.L j A3.A.μ0).S.Forms,
      x ∈ BlockGood.goodR (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) ∧
      (∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x) ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧
      R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0
  have key : ∀ j p c s p' c' s', Wit j p c s → Wit j p' c' s' → ∀ Q : A3.okI A3.A.μ0,
      ((∀ y, p.1.2 (Q.1, y) = p'.1.2 (Q.1, y)) ↔ ∀ y, s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y))) := by
    intro j p c s p' c' s' hw hw' Q
    obtain ⟨hc, x, -, hx, hxW, hx0⟩ := hw
    obtain ⟨hc', x', -, hx', hxW', hx0'⟩ := hw'
    rw [GlobalTheory.T.inertTypeEigenvalues_iff_labelEigensystems_rows hHowe R F hLI hCW hEx hSch hJ hPB hPP p p' c c' hc hc' Q,
      GlobalTheory.T.liftInertEigenvalues_iff_thetaImageEigensystem hHowe R F hLI hCW hEx hSch hJ hAbs j c c' s s' x x' hx hxW hx0 hx' hxW' hx0' Q]
    exact forall_congr' fun d => imp_congr_left (hlab j _ d)
  let Cons : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → Prop := fun j a => ∃ p c s, Wit j p c s ∧ p.1.2 = a
  let f : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL := fun j a k =>
    if h : Cons j a then
      (if hk : k.1 ∈ A3.okI A3.A.μ0 then h.choose_spec.choose_spec.choose (Sum.inr (⟨k.1, hk⟩, k.2)) else 0)
    else 0
  have hf : ∀ j a (h : Cons j a) (Q : A3.okI A3.A.μ0) y,
      f j a (Q.1, y) = h.choose_spec.choose_spec.choose (Sum.inr (Q, y)) := by
    intro j a h Q y
    simp only [f, dif_pos h, dif_pos Q.2]
  have hspec : ∀ j a (h : Cons j a),
      Wit j h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose ∧ h.choose.1.2 = a :=
    fun j a h => h.choose_spec.choose_spec.choose_spec
  let S : Finset (I0 × List ℕ → D.what₂.LL) := ((A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X).image Prod.snd
  have hg : ∀ j, ∃ g : (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL, (∀ a, Cons j a → g a = f j a) ∧
      ∀ _q : A3.okI A3.A.μ0, ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → ¬ (Cons j a ∧ Cons j a') →
        ∃ k : A3.okI A3.A.μ0 × List ℕ, g a (k.1.1, k.2) ≠ g a' (k.1.1, k.2) := by
    intro j
    by_cases hne : Nonempty (A3.okI A3.A.μ0)
    · obtain ⟨q⟩ := hne
      obtain ⟨g, hg1, hg2⟩ := sep_extend S (Cons j) (f j) (q.1, ([] : List ℕ))
      exact ⟨g, hg1, fun _ a ha a' ha' hne hC => ⟨(q, []), hg2 a ha a' ha' hne hC⟩⟩
    · exact ⟨f j, fun _ _ => rfl, fun q => (hne ⟨q⟩).elim⟩
  choose g hg1 hg2 using hg
  refine ⟨g, ?_, ?_⟩
  · intro j p c hc s hx k
    have hC : Cons j p.1.2 := ⟨p, c, s, ⟨hc, hx⟩, rfl⟩
    rw [hg1 j _ hC]
    change s (Sum.inr k) = f j p.1.2 (k.1.1, k.2)
    rw [hf j _ hC k.1 k.2]
    obtain ⟨hw, ha⟩ := hspec j _ hC
    exact (((key j _ _ _ p c s hw ⟨hc, hx⟩ k.1).1 (fun y => by rw [ha])) k.2).symm
  · intro j p hp p' hp' hk
    obtain ⟨k0, hk0⟩ := hk
    by_cases hC : Cons j p.2 ∧ Cons j p'.2
    · by_contra hcon
      push_neg at hcon
      obtain ⟨hw, ha⟩ := hspec j _ hC.1
      obtain ⟨hw', ha'⟩ := hspec j _ hC.2
      have := (key j _ _ _ _ _ _ hw hw' k0.1).2 (fun y => by
        have h1 := hcon (k0.1, y)
        rw [hg1 j _ hC.1, hg1 j _ hC.2, hf j _ hC.1, hf j _ hC.2] at h1
        exact h1) k0.2
      rw [ha, ha'] at this
      exact hk0 this
    · have hne : p.2 ≠ p'.2 := fun h => hk0 (by rw [h])
      exact hg2 j k0.1 p.2 (Finset.mem_image_of_mem _ hp) p'.2 (Finset.mem_image_of_mem _ hp') hne hC

end GlobalTheory.TrPass

end
