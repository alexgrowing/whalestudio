import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictPf

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.Act

open Formalism.L2.SG.Pf Formalism.L2.SG.Saturated

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  (Λ : Submodule (𝓞 E) S.V) (g : ℕ)

theorem e_mem_locP {F : LFlag S r T} (hF : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E))
    (hg : (g : 𝓞 E) ∈ P.asIdeal) (a : Fin r) :
    F.fl.e a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F)) := by
  haveI := P.isPrime
  obtain ⟨c, -, hc1, hloc⟩ := hF.1 P
  rw [hloc]
  refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
  rw [one_smul]
  refine Submodule.subset_span ⟨a, ?_⟩
  simp [hc1 hg a]

theorem xlam_le_locP {F : LFlag S r T} (hF : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E))
    (hg : (g : 𝓞 E) ∈ P.asIdeal) {N : Submodule (𝓞 E) S.V}
    (hN : ∀ a, F.fl.e a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N)) :
    XLam Λ F ≤ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) := by
  haveI := P.isPrime
  obtain ⟨c, -, hc1, hloc⟩ := hF.1 P

  have hspan : Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a) ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simpa [hc1 hg a] using hN a
  intro x hx
  have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
  rw [hloc] at hx'
  obtain ⟨s, hs, hsx⟩ := hx'
  obtain ⟨t, ht, htx⟩ := hspan hsx
  exact ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact htx⟩

private theorem le_of_forall_localization_le {M N : Submodule (𝓞 E) S.V}
    (h : ∀ P : HeightOneSpectrum (𝓞 E), M ≤ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N)) : M ≤ N := by
  intro x hx
  by_contra hxN

  have hI : N.colon {x} ≠ ⊤ := by
    intro htop
    apply hxN
    have h1 : (1 : 𝓞 E) ∈ N.colon {x} := htop ▸ Submodule.mem_top
    simpa using Submodule.mem_colon_singleton.1 h1
  obtain ⟨Mx, hMx, hIM⟩ := Ideal.exists_le_maximal _ hI
  have hne : Mx ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hMx (RingOfIntegers.not_isField E)
  let P : HeightOneSpectrum (𝓞 E) := ⟨Mx, hMx.isPrime, hne⟩
  obtain ⟨s, hs, hsx⟩ := h P hx
  exact hs (hIM (Submodule.mem_colon_singleton.2 hsx))

theorem xlam_le {F : LFlag S r T} {F' : LFlag S r T'} (hAdm : IsAdmissible Λ g F F') (hF : IsFixedConv Λ g F)
    (hF' : IsFixedConv Λ g F') : XLam Λ F' ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F := by
  obtain ⟨ξ, hlow, -, hmod⟩ := hAdm
  apply le_of_forall_localization_le
  intro P
  haveI := P.isPrime
  have hmono : ∀ {A B : Submodule (𝓞 E) S.V}, A ≤ B →
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B :=
    fun hAB _ ⟨s, hs, hx⟩ => ⟨s, hs, hAB hx⟩
  have hsm : ∀ (o : 𝓞 E) (v : S.V),
      v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F) →
      ((o : E)) • v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F) := by
    intro o v hv
    rw [show ((o : E)) • v = o • v from algebraMap_smul E o v]
    exact Submodule.smul_mem _ o hv
  have hframe : ∀ b : Fin r, frame F (Fin.castSucc b) = F.fl.e b := fun b => by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  have hframe' : ∀ b : Fin r, frame F' (Fin.castSucc b) = F'.fl.e b := fun b => by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
  · refine xlam_le_locP Λ g hF' P hg (fun a => ?_)
    have h1 := hmod (Fin.castSucc a) P hg
    rw [hframe'] at h1
    have hact : frameAct (frame F) ξ (Fin.castSucc a) ∈
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F) := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : Fin.castSucc a < b
      · rw [hlow b (Fin.castSucc a) hb]
        simp
      · push_neg at hb
        have hbr : (b : ℕ) < r := lt_of_le_of_lt (Fin.le_def.1 hb) (by simp)
        obtain ⟨b', rfl⟩ : ∃ b' : Fin r, b = Fin.castSucc b' :=
          ⟨b.castLT hbr, (Fin.castSucc_castLT b hbr).symm⟩
        rw [hframe]
        exact hsm _ _ (hmono le_sup_right (e_mem_locP Λ g hF P hg b'))
    have e : F'.fl.e a = (F'.fl.e a - frameAct (frame F) ξ (Fin.castSucc a)) +
        frameAct (frame F) ξ (Fin.castSucc a) := by abel
    rw [e]
    exact Submodule.add_mem _ (hmono le_sup_left h1) hact
  · intro x hx
    exact ⟨(g : 𝓞 E), hg, Submodule.mem_sup_left
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx.1)⟩

theorem xlam_le' {F : LFlag S r T} {F' : LFlag S r T'} (hAdm : IsAdmissible Λ g F F') (hF : IsFixedConv Λ g F)
    (hF' : IsFixedConv Λ g F') : XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  obtain ⟨ξ, hlow, hdiag, hmod⟩ := hAdm
  apply le_of_forall_localization_le
  intro P
  haveI := P.isPrime
  have hmono : ∀ {A B : Submodule (𝓞 E) S.V}, A ≤ B →
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B :=
    fun hAB _ ⟨s, hs, hx⟩ => ⟨s, hs, hAB hx⟩
  have hsm : ∀ (o : 𝓞 E) (v : S.V),
      v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') →
      ((o : E)) • v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := by
    intro o v hv
    rw [show ((o : E)) • v = o • v from algebraMap_smul E o v]
    exact Submodule.smul_mem _ o hv
  have hframe : ∀ b : Fin r, frame F (Fin.castSucc b) = F.fl.e b := fun b => by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  have hframe' : ∀ b : Fin r, frame F' (Fin.castSucc b) = F'.fl.e b := fun b => by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
  · refine xlam_le_locP Λ g hF P hg (fun a => ?_)

    have key : ∀ k : ℕ, ∀ b : Fin r, (b : ℕ) = k →
        F.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
      intro b hbk
      have hsplit : frameAct (frame F) ξ (Fin.castSucc b) = F.fl.e b +
          ∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 E) : E) • frame F a := by
        unfold frameAct
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.castSucc b)), hdiag, hframe]
        simp
      have hrest : ∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 E) : E) • frame F a ∈
          Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') := by
        refine Submodule.sum_mem _ fun a ha => ?_
        have hab : a ≠ Fin.castSucc b := Finset.ne_of_mem_erase ha
        rcases lt_or_gt_of_ne hab with hlt | hgt
        · have hlt' : (a : ℕ) < (b : ℕ) := by simpa [Fin.lt_def] using hlt
          have har : (a : ℕ) < r := lt_trans hlt' b.isLt
          obtain ⟨a', rfl⟩ : ∃ a' : Fin r, a = Fin.castSucc a' :=
            ⟨a.castLT har, (Fin.castSucc_castLT a har).symm⟩
          rw [hframe]
          exact hsm _ _ (ih a' (by rw [← hbk]; simpa using hlt') a' rfl)
        · rw [hlow a (Fin.castSucc b) hgt]
          simp
      have h1 := hmod (Fin.castSucc b) P hg
      rw [hframe'] at h1
      have e : F.fl.e b = F'.fl.e b - (F'.fl.e b - frameAct (frame F) ξ (Fin.castSucc b)) -
          ∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 E) : E) • frame F a := by
        rw [hsplit]
        abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (hmono le_sup_right (e_mem_locP Λ g hF' P hg b))
        (hmono le_sup_left h1)) hrest
    exact key a a rfl
  · intro x hx
    exact ⟨(g : 𝓞 E), hg, Submodule.mem_sup_left
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx.1)⟩

theorem rep_exists {F : LFlag S r T} {F' : LFlag S r T'} (hg0 : ((g : ℕ) : E) ≠ 0) {f : Fin r → S.V}
    {L : Submodule (𝓞 E) S.V} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hff : ∀ a b, S.hT (f a) (f b) = 0) (hef : ∀ a b, S.hT (F.fl.e a) (f b) = if a = b then 1 else 0)
    (hLp : ∀ x ∈ L, ∀ a, S.hT (F.fl.e a) x = 0 ∧ S.hT (f a) x = 0)
    (hΛ : Λ = latSpan aa F.fl.e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hC : XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') :
    ∀ x' ∈ Lrep Λ F', ∃ x ∈ Lrep Λ F, x' - x ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
  classical
  intro x' hx'
  obtain ⟨hx'Λ, hx'o⟩ := Submodule.mem_inf.1 hx'

  have hstar : ∀ o : 𝓞 E, ∃ o' : 𝓞 E, (o' : E) = star (o : E) := fun o =>
    ⟨⟨star (o : E), o.isIntegral_coe.map (starRingEnd E).toIntAlgHom⟩, rfl⟩
  have hsmulO : ∀ (o : 𝓞 E) (y z : S.V), S.hT (o • y) z = star (o : E) * S.hT y z := by
    intro o y z
    rw [← algebraMap_smul E o y, LinearMap.map_smulₛₗ₂]
    rfl
  have hsmulE : ∀ (c : E) (y z : S.V), S.hT (c • y) z = star c * S.hT y z := by
    intro c y z
    rw [LinearMap.map_smulₛₗ₂]
    rfl

  have horth : ∀ {U : Submodule E S.V} {v w : S.V}, v ∈ orth S U → w ∈ U → S.hT w v = 0 := by
    intro U v w hv hw
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv w) hw)

  have hint : ∀ y ∈ Λ, ∀ z ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT y z := by
    intro y hy z hz
    rw [← hU] at hz
    exact Submodule.mem_one.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz y) hy)

  have hgmul : ∀ u ∈ Ideal.span {(g : 𝓞 E)} • Λ, ∃ o : 𝓞 E, S.hT u x' = (g : E) * (o : E) := by
    intro u hu
    refine Submodule.smul_induction_on hu ?_ ?_
    · intro a ha y hy
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      obtain ⟨o, ho⟩ := hint y hy x' hx'Λ
      obtain ⟨k', hk'⟩ := hstar k
      refine ⟨k' * o, ?_⟩
      rw [hsmulO, ← ho]
      push_cast
      rw [star_mul, ← hk', star_natCast]
      ring
    · rintro u v ⟨o1, h1⟩ ⟨o2, h2⟩
      exact ⟨o1 + o2, by rw [map_add, LinearMap.add_apply, h1, h2]; push_cast; ring⟩

  set β : Fin r → E := fun b => S.hT (F.fl.e b) x' with hβ
  have hβf : ∀ b, β b • f b ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
    intro b
    set c : E := β b / (g : E) with hc

    have hkey : ∀ α ∈ aa b, ∃ o : 𝓞 E, (o : E) = c * star α := by
      intro α hα
      have hAΛ : α • F.fl.e b ∈ Λ := by
        rw [hΛ]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨b, α, hα, rfl⟩))
      have hXsp : α • F.fl.e b ∈ Xsp F :=
        Submodule.smul_mem _ α (Submodule.subset_span ⟨b, rfl⟩)
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hC (Submodule.mem_inf.2 ⟨hAΛ, hXsp⟩))
      obtain ⟨o, ho⟩ := hgmul u hu
      have hw0 : S.hT w x' = 0 := horth hx'o (Submodule.mem_inf.1 hw).2
      have e1 : star α * β b = (g : E) * (o : E) := by
        rw [hβ]
        dsimp only
        rw [← hsmulE, ← huw, map_add, LinearMap.add_apply, ho, hw0, add_zero]
      refine ⟨o, ?_⟩
      rw [hc, div_mul_eq_mul_div, eq_div_iff hg0, mul_comm (β b), e1, mul_comm]
    let W : Submodule (𝓞 E) S.V :=
      { carrier := {y | ∃ o : 𝓞 E, (o : E) = c * S.hT y (f b)}
        add_mem' := by
          rintro y z ⟨o1, h1⟩ ⟨o2, h2⟩
          exact ⟨o1 + o2, by rw [map_add, LinearMap.add_apply, mul_add, ← h1, ← h2]; simp⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro o y ⟨o1, h1⟩
          obtain ⟨o', h'⟩ := hstar o
          exact ⟨o' * o1, by rw [hsmulO, mul_left_comm, ← h1, ← h']; simp⟩ }
    have hΛW : Λ ≤ W := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [latSpan, Submodule.span_le]
        rintro _ ⟨a, α, hα, rfl⟩
        show ∃ o : 𝓞 E, (o : E) = c * S.hT (α • F.fl.e a) (f b)
        rw [hsmulE, hef]
        by_cases hab : a = b
        · subst hab
          obtain ⟨o, ho⟩ := hkey α hα
          exact ⟨o, by rw [ho]; simp⟩
        · exact ⟨0, by simp [hab]⟩
      · intro l hl
        have h0 : S.hT l (f b) = 0 := by
          rw [← S.herm.eq (f b) l, (hLp l hl b).2, map_zero]
        exact ⟨0, by rw [h0]; simp⟩
      · rw [latSpan, Submodule.span_le]
        rintro _ ⟨a, γ, hγ, rfl⟩
        show ∃ o : 𝓞 E, (o : E) = c * S.hT (γ • f a) (f b)
        exact ⟨0, by rw [hsmulE, hff]; simp⟩
    have hcf : c • f b ∈ Λ := by
      rw [← hU]
      refine (Submodule.mem_iInf _).2 fun y => (Submodule.mem_iInf _).2 fun hy => ?_
      obtain ⟨o, ho⟩ := hΛW hy
      refine Submodule.mem_one.2 ⟨o, ?_⟩
      show (o : E) = S.hT y (c • f b)
      rw [map_smul, smul_eq_mul, ho]
    have e : β b • f b = (g : 𝓞 E) • (c • f b) := by
      rw [← algebraMap_smul E (g : 𝓞 E), smul_smul, hc]
      congr 1
      push_cast
      field_simp
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hcf
  have hsum : ∑ b, β b • f b ∈ Ideal.span {(g : 𝓞 E)} • Λ := Submodule.sum_mem _ fun b _ => hβf b
  refine ⟨x' - ∑ b, β b • f b, Submodule.mem_inf.2 ⟨?_, ?_⟩, by rw [sub_sub_cancel]; exact hsum⟩
  · exact Λ.sub_mem hx'Λ (Submodule.smul_le_right hsum)
  · show x' - ∑ b, β b • f b ∈ orth S (Xsp F)
    refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun hw => ?_
    rw [LinearMap.mem_ker]
    have hw' : w ∈ Submodule.span E (Set.range F.fl.e) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem w0 hw0 =>
      obtain ⟨a, rfl⟩ := hw0
      simp [β, map_sub, map_sum, hef, Finset.sum_ite_eq]
    | zero => simp
    | add w1 w2 _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    | smul c w _ h => rw [LinearMap.map_smulₛₗ₂, h, smul_zero]

theorem gmap_gSmul {β : S.V ≃ₗ[E] S.V} (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) {x : S.V}
    (hx : x ∈ Ideal.span {(g : 𝓞 E)} • Λ) : β x ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha n hn
    rw [← algebraMap_smul E a n, map_smul, algebraMap_smul]
    refine Submodule.smul_mem_smul ha ?_
    rw [← hβΛ]
    exact Submodule.mem_map_of_mem hn
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

theorem iotaCompat_iff {F : LFlag S r T} {F1 F2 : LFlag S r T'} (β : S.V ≃ₗ[E] S.V)
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ)
    (hN1 : XLam Λ F1 ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F)
    (hN1' : XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F1)
    (hN2 : XLam Λ F2 ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F)
    (hβX : ∀ x ∈ XLam Λ F1, β x ∈ XLam Λ F2)
    (hrep : ∀ x' ∈ Lrep Λ F1, ∃ x ∈ Lrep Λ F, x' - x ∈ Ideal.span {(g : 𝓞 E)} • Λ)
    (hrep' : ∀ x ∈ Lrep Λ F, ∃ x' ∈ Lrep Λ F1, x - x' ∈ Ideal.span {(g : 𝓞 E)} • Λ) :
    IotaCompat Λ F F1 F2 β g ↔ ∀ x ∈ Lrep Λ F, β x - x ∈ NgX Λ g F F := by
  set N := Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F with hNdef
  have hgN : Ideal.span {(g : 𝓞 E)} • Λ ≤ N := le_sup_left
  have h1 : NgX Λ g F F1 = N := sup_eq_left.2 hN1
  have h2 : NgX Λ g F F2 = N := sup_eq_left.2 hN2
  have h0 : NgX Λ g F F = N := sup_eq_left.2 le_sup_right

  have hβN : ∀ y ∈ N, β y ∈ N := by
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 (hN1' hv)
    rw [map_add, map_add]
    refine N.add_mem (hgN (gmap_gSmul Λ g hβΛ hu)) (N.add_mem (hgN (gmap_gSmul Λ g hβΛ hw)) ?_)
    have := hN2 (hβX z hz)
    exact this
  unfold IotaCompat
  rw [h1, h2, h0]
  constructor
  · intro h x hx
    obtain ⟨x', hx', hxx'⟩ := hrep' x hx
    have e1 := (h x' hx' x hx).1 (hgN hxx')
    have e2 : β x - x = β (x - x') - (x - β x') := by rw [map_sub]; abel
    rw [e2]
    exact N.sub_mem (hβN _ (hgN hxx')) e1
  · intro h x' hx' l _
    obtain ⟨x, hx, hx'x⟩ := hrep x' hx'
    have hd : β x' - x' ∈ N := by
      have e : β x' - x' = β (x' - x) + (β x - x) - (x' - x) := by rw [map_sub]; abel
      rw [e]
      exact N.sub_mem (N.add_mem (hβN _ (hgN hx'x)) (h x hx)) (hgN hx'x)
    constructor
    · intro hl
      have e : l - β x' = (l - x') - (β x' - x') := by abel
      rw [e]
      exact N.sub_mem hl hd
    · intro hl
      have e : l - x' = (l - β x') + (β x' - x') := by abel
      rw [e]
      exact N.add_mem hl hd

theorem latSpan_gmap (β : S.V ≃ₗ[E] S.V) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (v : Fin r → S.V) : Formalism.HermitianLatticesTheory.gmap β (latSpan aa v) = latSpan aa (fun a => β (v a)) := by
  unfold Formalism.HermitianLatticesTheory.gmap latSpan
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨a, x, hx, rfl⟩, rfl⟩
    exact ⟨a, x, hx, by simp⟩
  · rintro ⟨a, x, hx, rfl⟩
    exact ⟨x • v a, ⟨a, x, hx, rfl⟩, by simp⟩

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.TermOp Formalism.L2.SG.Full

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem gS_ne : ((gS D : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem Xsp_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) :
    Xsp (mapLF γ (lf D F)) = (Xsp (lf D F)).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  rw [mapLF, dif_pos hγ]
  show Submodule.span _ (Set.range fun a => γ ((lf D F).fl.e a)) =
    (Submodule.span _ (Set.range (lf D F).fl.e)).map _
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem e_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : (mapLF γ (lf D F)).fl.e a = γ (F.e a) := by
  rw [mapLF, dif_pos hγ]
  rfl

theorem split_mapLF (Y : Full X) {u' : D.what₂.Word} {Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ' : Λ' ∈ Y.what₂ u')
    {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    ∃ (f : Fin D.R.rS → (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
      (∀ a b, (VS D).hT (f a) (f b) = 0) ∧
      (∀ a b, (VS D).hT ((mapLF γ (lf D (X.Fu u'))).fl.e a) (f b) = if a = b then 1 else 0) ∧
      (∀ x ∈ L, ∀ a, (VS D).hT ((mapLF γ (lf D (X.Fu u'))).fl.e a) x = 0 ∧ (VS D).hT (f a) x = 0) ∧
      Formalism.HermitianLatticesTheory.gmap γ Λ' = latSpan (aaS D) (mapLF γ (lf D (X.Fu u'))).fl.e ⊔ L ⊔
        latSpan (fun a => (aaS D a)⁻¹) f := by
  obtain ⟨f, L, hff, hef, hLp, -, hΛ⟩ := Y.split u' Λ' hΛ'
  have he : (mapLF γ (lf D (X.Fu u'))).fl.e = fun a => γ ((X.Fu u').e a) := funext (e_mapLF hγ _)
  refine ⟨fun a => γ (f a), Formalism.HermitianLatticesTheory.gmap γ L, fun a b => (hγ (f a) (f b)).trans (hff a b),
    fun a b => ?_, fun x hx a => ?_, ?_⟩
  · rw [he]
    exact (hγ _ _).trans (hef a b)
  · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    rw [he]
    exact ⟨(hγ _ _).trans (hLp y hy a).1, (hγ _ _).trans (hLp y hy a).2⟩
  · have hsup : ∀ A B : Submodule (𝓞 D.host.E) (VS D).V,
        Formalism.HermitianLatticesTheory.gmap γ (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap γ A ⊔ Formalism.HermitianLatticesTheory.gmap γ B :=
      fun A B => Submodule.map_sup _ _ _
    rw [he, hΛ, hsup, hsup, latSpan_gmap, latSpan_gmap]

theorem ratIotaC' (Y : Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam)
    (hl' : s₁.lam' = s₂.lam') :
    IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) ↔
      RatTriv u X s₁.lam (s₂.lin * s₁.lin⁻¹) := by
  rcases s₁ with ⟨l, m, l', m', c₁⟩
  rcases s₂ with ⟨k, mk, k', mk', c₂⟩
  simp only at hl hl'
  subst hl hl'
  set s₁ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := ⟨l, m, l', m', c₁⟩ with hs₁
  set s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := ⟨l, mk, l', mk', c₂⟩ with hs₂
  have hγ1 : s₁.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s₁.rep.2.2.1
  have hγ2 : s₂.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s₂.rep.2.2.1
  have hg1 : Formalism.HermitianLatticesTheory.gmap s₁.lin l' = l := s₁.rep.2.2.2.1
  have hg2 : Formalism.HermitianLatticesTheory.gmap s₂.lin l' = l := s₂.rep.2.2.2.1
  obtain ⟨-, hadm1, hok1⟩ := s₁.rep.2.2.2.2
  obtain ⟨-, hadm2, hok2⟩ := s₂.rep.2.2.2.2
  obtain ⟨-, ⟨-, hun, -, hconv⟩, -⟩ := (Y.rowsOK u).1 l m
  have hF1 : s₁.frame = mapLF s₁.lin (lf D (X.Fu u')) := rfl
  have hF2 : s₂.frame = mapLF s₂.lin (lf D (X.Fu u')) := rfl
  have hN1 := xlam_le l (gS D) hadm1 hconv hok1.1
  have hN1' := xlam_le' l (gS D) hadm1 hconv hok1.1
  have hN2 := xlam_le l (gS D) hadm2 hconv hok2.1
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (s₂.lin * s₁.lin⁻¹) l = l :=
    (gmap_mul_sat _ _ _).trans ((congrArg (fun M => Formalism.HermitianLatticesTheory.gmap s₂.lin (Formalism.HermitianLatticesTheory.gmap s₁.lin⁻¹ M)) hg1.symm).trans
      ((congrArg (Formalism.HermitianLatticesTheory.gmap s₂.lin) (gmap_inv_gmap _ _)).trans hg2))
  have hβX : ∀ x ∈ XLam l s₁.frame, (s₂.lin * s₁.lin⁻¹) x ∈ XLam l s₂.frame := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [← hβΛ]; exact (gmap_apply_mem _ l x).2 hx.1
    · have hx2 : x ∈ Xsp (mapLF s₁.lin (lf D (X.Fu u'))) := hx.2
      obtain ⟨w, hw, rfl⟩ := (Xsp_mapLF hγ1 (X.Fu u')).le hx2
      show (s₂.lin * s₁.lin⁻¹) (s₁.lin w) ∈ Xsp (mapLF s₂.lin (lf D (X.Fu u')))
      refine (Xsp_mapLF hγ2 (X.Fu u')).ge ⟨w, hw, ?_⟩
      show s₂.lin w = s₂.lin (s₁.lin.symm (s₁.lin w))
      rw [LinearEquiv.symm_apply_apply]
  obtain ⟨f, L, hff, hef, hLp, -, hsplit⟩ := Y.split u l m
  have hrep := rep_exists l (gS D) (F := lf D (X.Fu u)) (F' := s₁.frame) gS_ne (aaS D) hff hef hLp hsplit hun hN1'
  obtain ⟨f1, L1, hff1, hef1, hLp1, hsplit1⟩ := split_mapLF Y m' hγ1 (X := X)
  have hsplit1' : l = latSpan (aaS D) s₁.frame.fl.e ⊔ L1 ⊔ latSpan (fun a => (aaS D a)⁻¹) f1 := by
    rw [← hg1]; exact hsplit1
  have hrep' := rep_exists l (gS D) (F := s₁.frame) (F' := lf D (X.Fu u)) gS_ne (aaS D) hff1 hef1 hLp1 hsplit1'
    hun hN1
  exact iotaCompat_iff l (gS D) _ hβΛ hN1 hN1' hN2 hβX hrep hrep'

end D7

end Formalism.L2.SG.Pf.Act
