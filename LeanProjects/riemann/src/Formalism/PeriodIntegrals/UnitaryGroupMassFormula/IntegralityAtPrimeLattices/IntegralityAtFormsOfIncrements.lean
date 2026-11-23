import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField Classical IsDedekindDomain

variable {D : D7} {u : D.what₂.Word}

def ValSc (T : Forms0 D u) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0) (h : (D.mem u).C.Y 0 → ℂ) : Prop :=
  ∀ B : GL (Fin (D.R.N 0)) D.host.E,
    IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B →
    ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ z, h z =
      fnOf _ (shiftOf (lamT u 0)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P (T.val0.eY z)

def ValBc (T : Forms0 D u) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (h : (D.mem u).C.Y 0 → ℂ) : Prop :=
  ∀ B B' : GL (Fin (D.R.N 0)) D.host.E,
    IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B →
    IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) B' →
    ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ z, h z =
      fnOf _ (shiftOf (lamT u 0))
        (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ
          else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ) P (T.val0.eY z)

def UpIncInt0 (T : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v c (x : (D.fm u).lv 0 v c), (D.fm u).fv 0 v c x = 1 →
    ∀ h, ValBc T w v ((D.fm u).up 0 v c x) h → ValSc T w c ((D.fm u).upT 0 v c x h)

def DnIncInt0 (T : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)),
    g ((D.fm u).te 0 v c) = 1 →
    ∀ h, ValSc T w ((D.fm u).dn 0 v c g) h → ValBc T w v c ((D.fm u).dnT 0 v c g h)

theorem valSc_sum (T : Forms0 D u) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0) {ι : Type} (s : Finset ι)
    (h : ι → (D.mem u).C.Y 0 → ℂ) (hh : ∀ i ∈ s, ValSc T w c (h i)) : ValSc T w c (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro B _
    refine ⟨0, (Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0)).zero_mem, fun z => ?_⟩
    simp
  | insert i s hi ih =>
    intro B hB
    rw [Finset.sum_insert hi]
    obtain ⟨P, hP, hPe⟩ := hh i (Finset.mem_insert_self _ _) B hB
    obtain ⟨Q, hQ, hQe⟩ := ih (fun j hj => hh j (Finset.mem_insert_of_mem hj)) B hB
    refine ⟨P + Q, AddSubgroup.add_mem _ hP hQ, fun z => ?_⟩
    rw [Pi.add_apply, hPe z, hQe z, map_add, Pi.add_apply]

theorem valBc_sum (T : Forms0 D u) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) {ι : Type}
    (s : Finset ι) (h : ι → (D.mem u).C.Y 0 → ℂ) (hh : ∀ i ∈ s, ValBc T w v c (h i)) :
    ValBc T w v c (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro B B' _ _
    refine ⟨0, (Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0)).zero_mem, fun z => ?_⟩
    simp
  | insert i s hi ih =>
    intro B B' hB hB'
    rw [Finset.sum_insert hi]
    obtain ⟨P, hP, hPe⟩ := hh i (Finset.mem_insert_self _ _) B B' hB hB'
    obtain ⟨Q, hQ, hQe⟩ := ih (fun j hj => hh j (Finset.mem_insert_of_mem hj)) B B' hB hB'
    refine ⟨P + Q, AddSubgroup.add_mem _ hP hQ, fun z => ?_⟩
    rw [Pi.add_apply, hPe z, hQe z, map_add, Pi.add_apply]

theorem uop_apply (v : (D.mem u).A.vT) (φ : Fn D u 0) (c : (D.mem u).C.cls 0) :
    Uop D u 0 v φ c = ∑ x ∈ Finset.univ.filter (fun x : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c x = 1),
      (D.fm u).upT 0 v c x (φ ((D.fm u).up 0 v c x)) := by
  simp only [Formalism.BasicNotions.LT.Uop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

theorem dop_apply (v : (D.mem u).A.vT) (φ : Fn D u 0) (c : (D.mem u).C.cls 0) :
    Dop D u 0 v φ c = ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g ((D.fm u).te 0 v c) = 1),
      (D.fm u).dnT 0 v c g (φ ((D.fm u).dn 0 v c g)) := by
  simp only [Dop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

theorem upValInt0_of (T : Forms0 D u) (hI : UpIncInt0 T) : UpValInt0 T := by
  intro w hw hs v x hx c B hB
  have hsum : ValSc T w c (∑ y ∈ Finset.univ.filter (fun y : (D.fm u).lv 0 v c => (D.fm u).fv 0 v c y = 1),
      (D.fm u).upT 0 v c y ((D.fm u).emb 0 x ((D.fm u).up 0 v c y))) := by
    refine valSc_sum T w c _ _ fun y hy => ?_
    have hy1 : (D.fm u).fv 0 v c y = 1 := (Finset.mem_filter.1 hy).2
    refine hI w hw hs v c y hy1 _ ?_
    intro B₁ B₁' hB₁ hB₁'
    exact hx _ B₁ B₁' hB₁ hB₁'
  obtain ⟨P, hP, hPe⟩ := hsum B hB
  refine ⟨P, hP, fun z => ?_⟩
  rw [uop_apply]
  exact hPe z

theorem dnValInt0_of (T : Forms0 D u) (hI : DnIncInt0 T) : DnValInt0 T := by
  intro w hw hs v x hx c B B' hB hB'
  have hsum : ValBc T w v c (∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g ((D.fm u).te 0 v c) = 1),
      (D.fm u).dnT 0 v c g ((D.fm u).emb 0 x ((D.fm u).dn 0 v c g))) := by
    refine valBc_sum T w v c _ _ fun g hg => ?_
    have hg1 : g ((D.fm u).te 0 v c) = 1 := (Finset.mem_filter.1 hg).2
    refine hI w hw hs v c g hg1 _ ?_
    intro B₁ hB₁
    exact hx _ B₁ hB₁
  obtain ⟨P, hP, hPe⟩ := hsum B B' hB hB'
  refine ⟨P, hP, fun z => ?_⟩
  rw [dop_apply]
  exact hPe z

theorem integrality_at_forms_of_increments
    (hR : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → HeckeRationalLevelZero D u)
    (hU : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → UpIncInt0 T)
    (hD : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), LocalLatticeBases.ChiFin0 T → admS D u → HidaSetting D u → DnIncInt0 T)
    (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.RT.IntegralityLevelZeroUnderForms D u := integrality_at_forms_of_values hR (fun D u T hC hA hS => upValInt0_of T (hU D u T hC hA hS))
    (fun D u T hC hA hS => dnValInt0_of T (hD D u T hC hA hS)) D u

end PI.UnitaryGroupMassFormula.IAT

end
