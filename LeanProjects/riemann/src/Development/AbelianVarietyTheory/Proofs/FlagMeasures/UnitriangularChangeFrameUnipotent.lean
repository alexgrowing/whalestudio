import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.UnipLevi

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
  (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))

lemma cjO {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

def Gen : Set V :=
  {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}

variable {Fr L}

lemma gen_mem {v : V} (hv : v ∈ Gen Fr L) : v ∈ Fr.LamStd L := Submodule.subset_span hv

lemma smulO {c : E} (hc : c ∈ M.L.O) {v : V} (hv : v ∈ Fr.LamStd L) : c • v ∈ Fr.LamStd L :=
  (Fr.LamStd L).smul_mem (⟨c, hc⟩ : M.L.O) hv

variable (Fr L)

lemma e_gen (a : Fin r) : Fr.e a ∈ Gen Fr L := by
  have h1 : ∀ b, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun b => Fr.h_es a b
  have h2 : ∀ b, H.h (Fr.e a) (Fr.e b) = 0 := fun b => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
  refine ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, ?_⟩⟩
  · rw [h1]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · rw [h2]; exact M.L.O.zero_mem
  · simp only [FrameD.prF, h1, h2, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.sum_const_zero, sub_self, sub_zero, ZeroMemClass.coe_zero]
  · rw [map_zero]; exact L.zero_mem

lemma es_gen (k : Fin r) : Fr.es k ∈ Gen Fr L := by
  have h1 : ∀ b, H.h (Fr.es k) (Fr.es b) = 0 := fun b => Fr.h_ss k b
  have h2 : ∀ b, H.h (Fr.es k) (Fr.e b) = if b = k then 1 else 0 := fun b => by
    rw [h_right H, show Fr.e b = Fr.f b.castSucc from rfl, Fr.h_es]
    split_ifs <;> simp
  refine ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, ?_⟩⟩
  · rw [h1]; exact M.L.O.zero_mem
  · rw [h2]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · simp only [FrameD.prF, h1, h2, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_const_zero, sub_self, sub_zero, ZeroMemClass.coe_zero]
  · rw [map_zero]; exact L.zero_mem

lemma comb_mem (β : Fin r → E) (hβ : ∀ a, β a ∈ M.L.O) :
    (∑ a, β a • Fr.e a) ∈ Fr.LamStd L ∧ ∀ v ∈ Gen Fr L, H.h v (∑ a, β a • Fr.e a) ∈ M.L.O := by
  refine ⟨Submodule.sum_mem _ fun a _ => smulO (hβ a) (gen_mem (e_gen Fr L a)), fun v hv => ?_⟩
  rw [h_right H]
  apply cjO
  have hl : H.h (∑ a, β a • Fr.e a) v = ∑ a, β a * H.h (Fr.e a) v := by
    show (lf H v) _ = _
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  rw [hl]
  exact M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hβ a) (by rw [h_right H]; exact cjO (hv.2.1 a))

variable {Fr L}

lemma pres_of_gen (g : V →ₗ[E] V) (h : ∀ v ∈ Gen Fr L, g v ∈ Fr.LamStd L) :
    ∀ v ∈ Fr.LamStd L, g v ∈ Fr.LamStd L := by
  have : Fr.LamStd L ≤ (Fr.LamStd L).comap (g.restrictScalars M.L.O) :=
    Submodule.span_le.2 fun v hv => h v hv
  exact fun v hv => this hv

lemma eich_gen {x : V} (hxl : x ∈ Fr.LamStd L) (hxh : ∀ v ∈ Gen Fr L, H.h v x ∈ M.L.O) (k : Fin r) :
    ∀ y ∈ Gen Fr L, eichL H x (Fr.es k) 0 y ∈ Fr.LamStd L := by
  intro y hy
  show eichF H x (Fr.es k) 0 y ∈ _
  unfold eichF
  rw [map_zero, zero_mul, zero_smul, add_zero]
  exact sub_mem (add_mem (gen_mem hy) (smulO (hy.1 k) hxl)) (smulO (hxh y hy) (gen_mem (es_gen Fr L k)))

end GlobalTheory.LocOver.UnipLevi

namespace GlobalTheory.LocOver.UnipLevi

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
  (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))

lemma levi_lam (u : Fin r → V) (hu : ∀ c, u c ∈ Fr.Fj c.val) (hul : ∀ c, u c ∈ Fr.LamStd L)
    (huh : ∀ c, ∀ v ∈ Gen Fr L, H.h v (u c) ∈ M.L.O) :
    ∀ k, k ≤ r → ∃ n ∈ NUg Fr, (∀ c : Fin r, n (Fr.f c.castSucc) =
      Fr.f c.castSucc + if c.val < k then u c else 0) ∧ n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) ∧
      ∀ v ∈ Fr.LamStd L, n v ∈ Fr.LamStd L ∧ n⁻¹ v ∈ Fr.LamStd L := by
  intro k
  induction k with
  | zero => intro _; exact ⟨1, (NUg Fr).one_mem, fun c => by simp, by simp, fun v hv => by simpa using hv⟩
  | succ k ih =>
    intro hk
    obtain ⟨n, hn, hne, hnz, hnl⟩ := ih (by omega)
    set kk : Fin r := ⟨k, by omega⟩ with hkk
    have hx : u kk ∈ H.X Fr.f := Fj_le_X Fr _ (hu kk)
    have hxv : H.h (u kk) (Fr.es kk) = 0 := Fj_es Fr kk.val kk le_rfl _ (hu kk)
    have hc : 2 * algebraMap F E (0 : F) + H.h (Fr.es kk) (Fr.es kk) = 0 := by
      rw [Fr.h_ss, map_zero]; ring
    have hM := eich_mem Fr hx hxv hc (fun a => by
      rw [Fr.h_es]
      by_cases hak : a = kk
      · subst hak; simpa using hu _
      · simp [hak])
    set g := eichE H (X_iso Fr (u kk) hx (u kk) hx) hxv hc with hg
    have hgl : ∀ v ∈ Fr.LamStd L, g v ∈ Fr.LamStd L ∧ g⁻¹ v ∈ Fr.LamStd L := by
      intro v hv
      refine ⟨pres_of_gen _ (eich_gen (hul kk) (huh kk) kk) v hv, ?_⟩
      have hxh' : ∀ y ∈ Gen Fr L, H.h y (-u kk) ∈ M.L.O := fun y hy => by
        rw [h_neg_right]; exact M.L.O.neg_mem (huh kk y hy)
      exact pres_of_gen _ (eich_gen (neg_mem (hul kk)) hxh' kk) v hv
    refine ⟨g * n, mul_mem hM hn, fun c => ?_, ?_, fun v hv => ?_⟩
    · rw [LinearEquiv.mul_apply, hne c, hg, eichE_apply]
      have hcx : H.h (Fr.f c.castSucc) (u kk) = 0 :=
        X_iso Fr _ (Fj_le_X Fr (c.val + 1) (e_mem Fr c)) _ hx
      by_cases hck : c.val < k
      · have hfix : eichF H (u kk) (Fr.es kk) 0 (u c) = u c :=
          eich_fix H _ _ _ _ (Fj_es Fr c.val kk (by simp [hkk]; omega) _ (hu c))
            (X_iso Fr _ (Fj_le_X Fr _ (hu c)) _ hx)
        have hne' : c ≠ kk := fun h => by subst h; simp [hkk] at hck
        have hadd : eichF H (u kk) (Fr.es kk) 0 (Fr.f c.castSucc + u c) =
            eichF H (u kk) (Fr.es kk) 0 (Fr.f c.castSucc) + eichF H (u kk) (Fr.es kk) 0 (u c) :=
          (eichL H (u kk) (Fr.es kk) 0).map_add _ _
        have hes : H.h (Fr.f c.castSucc) (Fr.es kk) = 0 := by rw [Fr.h_es, if_neg hne']
        rw [if_pos hck, if_pos (by omega), hadd, hfix]
        simp [eichF, hcx, hes]
      · rw [if_neg hck]
        by_cases hce : c = kk
        · subst hce
          have h1 : H.h (Fr.f kk.castSucc) (Fr.es kk) = 1 := by rw [Fr.h_es, if_pos rfl]
          have : kk.val < k + 1 := by simp [hkk]
          rw [if_pos this]
          simp [eichF, hcx, h1]
        · have : ¬ c.val < k + 1 := fun h => hce (Fin.ext (by simp [hkk]; omega))
          have hes : H.h (Fr.f c.castSucc) (Fr.es kk) = 0 := by rw [Fr.h_es, if_neg hce]
          rw [if_neg this]
          simp [eichF, hcx, hes]
    · rw [LinearEquiv.mul_apply, hnz, hg, eichE_apply]
      exact eich_fix H _ _ _ _ (z_es Fr kk) (z_X Fr _ hx)
    · refine ⟨?_, ?_⟩
      · rw [LinearEquiv.mul_apply]
        exact (hgl _ (hnl v hv).1).1
      · rw [mul_inv_rev, LinearEquiv.mul_apply]
        exact (hnl _ (hgl v hv).2).2

end GlobalTheory.LocOver.UnipLevi

namespace GlobalTheory.LocOver.UnipLevi

open GlobalTheory.LocOver.UnipOnto

theorem levi_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)), ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) E, Uni A →
    (∀ a b, A a b ∈ M.L.O) → ∃ n ∈ Fr.N, (∀ c : Fin r, n (Fr.f c.castSucc) = ∑ a, A a c.castSucc • Fr.f a) ∧
      n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) ∧ img n (Fr.LamStd L) = Fr.LamStd L := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r Fr L A hA hAO
  set u : Fin r → V := fun c => (∑ a, A a c.castSucc • Fr.f a) - Fr.f c.castSucc with hud
  have hm := mem_of_tri Fr.f (fun b => ∑ a, A a b • Fr.f a) ⟨A, hA, fun b => rfl⟩
  have hu : ∀ c : Fin r, u c ∈ Fr.Fj c.val := fun c =>
    spanf_le Fr c.val c.isLt.le (by simpa using hm c.castSucc)
  have hdec : ∀ c : Fin r, u c = (∑ a : Fin r, A a.castSucc c.castSucc • Fr.e a) - Fr.e c := by
    intro c
    simp only [hud]
    rw [Fin.sum_univ_castSucc, hA.1 _ _ (Fin.castSucc_lt_last c), zero_smul, add_zero]
    rfl
  have hul : ∀ c, u c ∈ Fr.LamStd L := fun c => by
    rw [hdec]
    exact sub_mem (comb_mem Fr L _ (fun a => hAO _ _)).1 (gen_mem (e_gen Fr L c))
  have huh : ∀ c, ∀ v ∈ Gen Fr L, H.h v (u c) ∈ M.L.O := fun c v hv => by
    rw [hdec, h_sub_right]
    exact M.L.O.sub_mem ((comb_mem Fr L _ (fun a => hAO _ _)).2 v hv) (hv.2.1 c)
  obtain ⟨n, hn, hne, hnz, hnl⟩ := levi_lam Fr L u hu hul huh r le_rfl
  refine ⟨n, by rw [N_eq]; exact hn, fun c => ?_, hnz, ?_⟩
  · rw [hne c, if_pos c.isLt]
    exact add_sub_cancel _ _
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (hnl v hv).1
    · intro v hv
      refine ⟨n⁻¹ v, (hnl v hv).2, ?_⟩
      show n (n⁻¹ v) = v
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl

end GlobalTheory.LocOver.UnipLevi
