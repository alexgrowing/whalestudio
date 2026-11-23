import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

set_option genSizeOfSpec false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.VacScalar

open GlobalTheory.FinPl

theorem psi_ne {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [h, zero_mul, add_neg_cancel, AddChar.map_zero_eq_one] at this
  exact one_ne_zero this

theorem psi_neg {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ (-a) = (ψ a)⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one])

theorem iso_mem {V ι J : Type} [AddCommGroup V] [Module ℂ V] (A : ι → V →ₗ[ℂ] V) (U : Submodule ℂ V)
    (hU : ∀ i, ∀ x ∈ U, A i x ∈ U) (l : J → ι → ℂ) (s : Finset J) :
    ∀ z : J → V, (∀ j ∈ s, ∀ i, A i (z j) = l j i • z j) → (∀ j ∈ s, ∀ j' ∈ s, l j = l j' → j = j') →
      ∑ j ∈ s, z j ∈ U → ∀ j ∈ s, z j ∈ U := by
  classical
  induction s using Finset.induction_on with
  | empty => intro z _ _ _ j hj; simp at hj
  | insert a s ha ih =>
    intro z hz hl hsum
    rw [Finset.sum_insert ha] at hsum
    have hs : ∀ b ∈ s, z b ∈ U := by
      intro b hb
      have hne : l b ≠ l a := fun h => ha (by
        rw [← hl b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a s) h]; exact hb)
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
      have h1 : A i (z a + ∑ j ∈ s, z j) - l a i • (z a + ∑ j ∈ s, z j) ∈ U :=
        U.sub_mem (hU i _ hsum) (U.smul_mem _ hsum)
      have h2 : A i (z a + ∑ j ∈ s, z j) - l a i • (z a + ∑ j ∈ s, z j) = ∑ j ∈ s, (l j i - l a i) • z j := by
        rw [map_add, map_sum, hz a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum,
          Finset.sum_congr rfl (fun j hj => hz j (Finset.mem_insert_of_mem hj) i), add_sub_add_comm, sub_self, zero_add,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => (sub_smul _ _ _).symm
      rw [h2] at h1
      have h3 := ih (fun j => (l j i - l a i) • z j) (fun j hj i' => by
          simp only [map_smul, hz j (Finset.mem_insert_of_mem hj) i', smul_comm (l j i')])
        (fun j hj j' hj' h => hl j (Finset.mem_insert_of_mem hj) j' (Finset.mem_insert_of_mem hj') h) h1 b hb
      have hc : l b i - l a i ≠ 0 := sub_ne_zero.2 hi
      have h4 := U.smul_mem (l b i - l a i)⁻¹ h3
      simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h4
      exact h4
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have : z j = (z j + ∑ j ∈ s, z j) - ∑ j ∈ s, z j := by abel
      rw [this]; exact U.sub_mem hsum (U.sum_mem hs)
    · exact hs j hj

variable {D : D7}

theorem heisO_zero_fun (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u 0 = 0 := by
  funext w; simp [heisO]

def hL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T u
  map_add' f g := by funext w; simp [heisO, mul_add]
  map_smul' c f := by funext w; simp [heisO]; ring

theorem heisO_inv (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (m : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T (-m) (heisO ψ S T m f) = ψ (symplOH S T (-m) m) • f := by
  rw [GlobalTheory.SplitScalar.heisO_heisO, neg_add_cancel, GlobalTheory.LatVac.heisO_zero]

theorem eig_ne (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {m : WO S T} {f : WO S T → ℂ} {c : ℂ}
    (h : heisO ψ S T m f = c • f) (hf : f ≠ 0) : c ≠ 0 := fun hc => hf (by
  have h1 := heisO_inv ψ S T m f
  rw [h, hc, zero_smul, heisO_zero_fun] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left (psi_ne _ _))

theorem symplOH_eq (S T : HSp D) (m y : WO S T) :
    symplOH S T m y = symplO S T m y + symplOH S T y m := by
  unfold symplOH
  rw [GlobalTheory.SplitScalar.symplO_skew S T m y]
  have ha : (algebraMap D.host.F (AF D.host.F)) (1 / 2) + (algebraMap D.host.F (AF D.host.F)) (1 / 2) = 1 := by
    rw [← map_add]; norm_num
  linear_combination (symplO S T m y) * ha

theorem heisO_eig (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {m y : WO S T} {f : WO S T → ℂ} {c : ℂ}
    (h : heisO ψ S T m f = c • f) :
    heisO ψ S T m (heisO ψ S T y f) = (ψ (symplO S T m y) * c) • heisO ψ S T y f := by
  have h2 := GlobalTheory.SplitScalar.heisO_heisO ψ S T y m f
  rw [h, GlobalTheory.LatVac.heisO_smul, add_comm] at h2
  rw [GlobalTheory.SplitScalar.heisO_heisO, symplOH_eq, AddChar.map_add_eq_mul, mul_smul, ← h2, smul_smul]

end GlobalTheory.VacScalar

namespace GlobalTheory.VacScalar

open GlobalTheory.FinPl

variable {D : D7}

theorem vac_eigen (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S)
    (LT : GlobalTheory.FinPl.Lat T) (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) (Q : Finset (GlobalTheory.FinPl.Pl D)) :
    ∃ q : WO S T → ℂ, ∀ m ∈ latO S T (LS : Set _) (LT : Set _) (· ∈ Q), ∀ f,
      GlobalTheory.FinPl.Vac ψ S T LS LT (· ∈ Q) f → heisO ψ S T m f = q m • f := by
  classical
  let H : AddSubgroup (WO S T) :=
    { carrier := {m | ∃ c : ℂ, ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· ∈ Q) f → heisO ψ S T m f = c • f}
      zero_mem' := ⟨1, fun f _ => by rw [GlobalTheory.LatVac.heisO_zero, one_smul]⟩
      add_mem' := by
        rintro a b ⟨ca, ha⟩ ⟨cb, hb⟩
        refine ⟨(ψ (symplOH S T a b))⁻¹ * (ca * cb), fun f hf => ?_⟩
        have hk := psi_ne ψ (symplOH S T a b)
        calc heisO ψ S T (a + b) f = (ψ (symplOH S T a b))⁻¹ • (ψ (symplOH S T a b) • heisO ψ S T (a + b) f) := by
              rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
          _ = _ := by
              rw [← GlobalTheory.SplitScalar.heisO_heisO, hb f hf, GlobalTheory.LatVac.heisO_smul, ha f hf, smul_smul, smul_smul,
                mul_assoc, mul_comm cb ca]
      neg_mem' := by
        rintro a ⟨ca, ha⟩
        by_cases hc : ca = 0
        · refine ⟨0, fun f hf => ?_⟩
          have hf0 : f = 0 := by
            have h := heisO_inv ψ S T a f
            rw [ha f hf, hc, zero_smul, heisO_zero_fun] at h
            exact (smul_eq_zero.1 h.symm).resolve_left (psi_ne _ _)
          subst hf0
          rw [heisO_zero_fun, smul_zero]
        · refine ⟨ca⁻¹ * ψ (symplOH S T (-a) a), fun f hf => ?_⟩
          have h := heisO_inv ψ S T a f
          rw [ha f hf, GlobalTheory.LatVac.heisO_smul] at h
          calc heisO ψ S T (-a) f = ca⁻¹ • (ca • heisO ψ S T (-a) f) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
            _ = _ := by rw [h, smul_smul] }
  have hHmem : ∀ m, (∃ c : ℂ, ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· ∈ Q) f → heisO ψ S T m f = c • f) → m ∈ H :=
    fun m h => h
  have hHmem' : ∀ m, m ∈ H → (∃ c : ℂ, ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· ∈ Q) f → heisO ψ S T m f = c • f) :=
    fun m h => h
  have hmono : latO S T (LS : Set _) (LT : Set _) (fun _ => True) ≤
      latO S T (LS : Set _) (LT : Set _) (fun p => p ∈ Q ∨ p ∉ Q) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => (hv' (em _)).elim, rest⟩
  have hmono' : latO S T (LS : Set _) (LT : Set _) (· ∈ Q) ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => (hv' trivial).elim, rest⟩
  have hsplit : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True),
      GlobalTheory.DisjComb.idem (· ∈ Q) • u ∈ latO S T (LS : Set _) (LT : Set _) (· ∈ Q) := fun u hu =>
    (GlobalTheory.DisjComb.split_latO ψ hψ hLS hLT (P := (· ∈ Q)) (P' := (· ∉ Q)) (fun p h h' => h' h) (hmono hu)).2.2.1
  let G : AddSubgroup (WO S T) := H.comap (DistribMulAction.toAddMonoidHom (WO S T) (GlobalTheory.DisjComb.idem (· ∈ Q)))
  have hG : ∀ {u : WO S T}, u ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) → u ∈ G := by
    intro u hu
    refine GlobalTheory.LatVac.le_of_two_of_half G (fun u hu => ?_) (fun e he u hu hh => ?_) hu
    · refine AddSubgroup.mem_comap.2 ?_
      rw [DistribMulAction.toAddMonoidHom_apply, smul_comm]
      exact hHmem _ ⟨1, fun f hf => by rw [one_smul]; exact hf.2.1 _ (hsplit u hu)⟩
    · refine AddSubgroup.mem_comap.2 ?_
      rw [DistribMulAction.toAddMonoidHom_apply]
      exact hHmem _ ⟨1, fun f hf => by rw [one_smul]; exact hf.2.2 e he _ (hsplit u hu) (GlobalTheory.DisjComb.isHalf_parts hh).1⟩
  have hH : ∀ m ∈ latO S T (LS : Set _) (LT : Set _) (· ∈ Q), m ∈ H := by
    intro m hm
    have h1 : GlobalTheory.DisjComb.idem (· ∈ Q) • m ∈ H := hG (hmono' hm)
    have h2 : GlobalTheory.DisjComb.idem (· ∈ Q) • m = m := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul]
      exact GlobalTheory.DisjComb.idem_mul (GlobalTheory.FinPl.LatMem.latO_mxAt hm i j)
    rwa [h2] at h1
  refine ⟨fun m => if h : m ∈ H then (hHmem' m h).choose else 0, fun m hm f hf => ?_⟩
  have h := hH m hm
  simp only [dif_pos h]
  exact (hHmem' m h).choose_spec f hf

end GlobalTheory.VacScalar

namespace GlobalTheory.VacScalar

open GlobalTheory.FinPl

variable {D : D7}

theorem symplO_split (S T : HSp D) (m x x' : WO S T) :
    symplO S T m x = symplO S T m x' + symplO S T m (x - x') := by
  have e1 := GlobalTheory.SplitScalar.symplO_skew S T m (x' + (x - x'))
  have e2 := GlobalTheory.SplitScalar.symplO_skew S T m x'
  have e3 := GlobalTheory.SplitScalar.symplO_skew S T m (x - x')
  have e4 := GlobalTheory.LatVac.symplO_add_left S T x' (x - x') m
  have hx : x = x' + (x - x') := by abel
  conv_lhs => rw [hx]
  linear_combination e1 - e4 - e2 - e3

theorem class_mem (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (P : WO S T → Prop)
    (hself : ∀ m ∈ Λ, ∀ m' ∈ Λ, ψ (symplO S T m m') = 1)
    (hann : ∀ x, P x → (∀ m ∈ Λ, ψ (symplO S T m x) = 1) → x ∈ Λ)
    (hPΛ : ∀ m ∈ Λ, P m) (hPsub : ∀ x y, P x → P y → P (x - y))
    (f q : WO S T → ℂ) (hq : ∀ m ∈ Λ, heisO ψ S T m f = q m • f) (hq0 : ∀ m ∈ Λ, q m ≠ 0)
    (U : Submodule ℂ (WO S T → ℂ)) (hU : ∀ m ∈ Λ, ∀ x ∈ U, heisO ψ S T m x ∈ U)
    {ι : Type} (s : Finset ι) (y : ι → WO S T) (c : ι → ℂ) (hy : ∀ i ∈ s, P (y i))
    (hsum : ∑ i ∈ s, c i • heisO ψ S T (y i) f ∈ U) :
    ∀ i ∈ s, ∑ j ∈ s with (QuotientAddGroup.mk (y j) : WO S T ⧸ Λ) = QuotientAddGroup.mk (y i),
      c j • heisO ψ S T (y j) f ∈ U := by
  classical
  let mk : WO S T → WO S T ⧸ Λ := QuotientAddGroup.mk
  let z : (WO S T ⧸ Λ) → (WO S T → ℂ) := fun C => ∑ j ∈ s with mk (y j) = C, c j • heisO ψ S T (y j) f
  let l : (WO S T ⧸ Λ) → Λ → ℂ := fun C m => ψ (symplO S T m (Quotient.out C)) * q m
  have hout : ∀ x : WO S T, Quotient.out (mk x) - x ∈ Λ := by
    intro x
    have h : mk (Quotient.out (mk x)) = mk x := Quotient.out_eq _
    rw [QuotientAddGroup.eq] at h
    have := Λ.neg_mem h
    rw [neg_add, neg_neg] at this
    rwa [sub_eq_add_neg]
  have hsym : ∀ m ∈ Λ, ∀ x x', x - x' ∈ Λ → ψ (symplO S T m x) = ψ (symplO S T m x') := by
    intro m hm x x' hx
    rw [symplO_split S T m x x', AddChar.map_add_eq_mul, hself m hm _ hx, mul_one]
  have hPout : ∀ x, P x → P (Quotient.out (mk x)) := by
    intro x hx
    have h1 : P (x - Quotient.out (mk x)) := hPΛ _ (by rw [← neg_sub]; exact Λ.neg_mem (hout x))
    have := hPsub _ _ hx h1
    rwa [sub_sub_cancel] at this
  have hz : ∀ C, ∀ m : Λ, hL ψ S T m (z C) = l C m • z C := by
    intro C m
    simp only [z, map_sum, map_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjC : mk (y j) = C := (Finset.mem_filter.1 hj).2
    have e : hL ψ S T m (heisO ψ S T (y j) f) = (ψ (symplO S T m (y j)) * q m) • heisO ψ S T (y j) f :=
      heisO_eig ψ S T (hq m m.2)
    have hl' : ψ (symplO S T m (y j)) * q m = l C m := by
      simp only [l]; rw [← hjC, hsym m m.2 _ _ (hout (y j))]
    rw [e, smul_smul, smul_smul, hl', mul_comm (c j)]
  have hl : ∀ C ∈ s.image (fun i => mk (y i)), ∀ C' ∈ s.image (fun i => mk (y i)), l C = l C' → C = C' := by
    intro C hC C' hC' h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.1 hC'
    have hP : P (Quotient.out (mk (y i)) - Quotient.out (mk (y i'))) :=
      hPsub _ _ (hPout _ (hy i hi)) (hPout _ (hy i' hi'))
    have hd : ∀ m ∈ Λ, ψ (symplO S T m (Quotient.out (mk (y i)) - Quotient.out (mk (y i')))) = 1 := by
      intro m hm
      have h1 := congrFun h ⟨m, hm⟩
      simp only [l] at h1
      have h2 := mul_right_cancel₀ (hq0 m hm) h1
      rw [symplO_split S T m (Quotient.out (mk (y i))) (Quotient.out (mk (y i'))), AddChar.map_add_eq_mul] at h2
      exact mul_left_cancel₀ (psi_ne ψ _) (h2.trans (mul_one _).symm)
    have hmk : mk (Quotient.out (mk (y i))) = mk (Quotient.out (mk (y i'))) := by
      rw [QuotientAddGroup.eq]
      have := Λ.neg_mem (hann _ hP hd)
      rwa [neg_sub, sub_eq_neg_add] at this
    rw [show mk (Quotient.out (mk (y i))) = mk (y i) from Quotient.out_eq _,
      show mk (Quotient.out (mk (y i'))) = mk (y i') from Quotient.out_eq _] at hmk
    exact hmk
  have hsumJ : ∑ C ∈ s.image (fun i => mk (y i)), z C = ∑ i ∈ s, c i • heisO ψ S T (y i) f :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _
  have key := iso_mem (fun m : Λ => hL ψ S T m) U (fun m x hx => hU m m.2 x hx) l (s.image (fun i => mk (y i))) z
    (fun C _ m => hz C m) hl (hsumJ ▸ hsum)
  intro i hi
  exact key _ (Finset.mem_image_of_mem _ hi)

theorem class_line (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T))
    (f q : WO S T → ℂ) (hq : ∀ m ∈ Λ, heisO ψ S T m f = q m • f)
    {ι : Type} (s : Finset ι) (y : ι → WO S T) (c : ι → ℂ) (i : ι) :
    ∑ j ∈ s with (QuotientAddGroup.mk (y j) : WO S T ⧸ Λ) = QuotientAddGroup.mk (y i),
      c j • heisO ψ S T (y j) f ∈ ℂ ∙ heisO ψ S T (y i) f := by
  classical
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
  have hj' := (Finset.mem_filter.1 hj).2
  rw [QuotientAddGroup.eq] at hj'
  have hm : y j - y i ∈ Λ := by
    have := Λ.neg_mem hj'
    rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this
  have h := GlobalTheory.SplitScalar.heisO_heisO ψ S T (y i) (y j - y i) f
  rw [hq _ hm, GlobalTheory.LatVac.heisO_smul, add_sub_cancel] at h
  rw [Submodule.mem_span_singleton]
  refine ⟨(ψ (symplOH S T (y i) (y j - y i)))⁻¹ * q (y j - y i), ?_⟩
  rw [mul_smul, h, smul_smul, inv_mul_cancel₀ (psi_ne _ _), one_smul]

end GlobalTheory.VacScalar

namespace GlobalTheory.VacScalar

open GlobalTheory.FinPl

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)) (o o' : WO S T →₀ ℂ) (g₀ : WO S T → ℂ), IsStdChar D ψ (-1) → IsSelfDualC S M → IsSelfDualC T M' → IsSelfDualC S N → IsSelfDualC T N' → GlobalTheory.FinPl.CombAt (· ∈ Q) o → GlobalTheory.FinPl.CombAt (· ∈ Q) o' → GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ Q) g₀ → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o g₀) → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o' g₀) → comb ψ S T o' g₀ ≠ 0 → ∃ c : ℂ, comb ψ S T o g₀ = c • comb ψ S T o' g₀ := by
  intro D ψ S T M N M' N' Q o o' g₀ hψ hM hM' hN hN' ho ho' hg hF hF' hne
  classical
  let P : WO S T → Prop := GlobalTheory.FinPl.MxAt (· ∈ Q)
  have hPsub : ∀ x y, P x → P y → P (x - y) := fun x y hx hy i j => by
    rw [Matrix.sub_apply]; exact Submodule.sub_mem _ (hx i j) (hy i j)
  have hPadd : ∀ x y, P x → P y → P (x + y) := fun x y hx hy i j => by
    rw [Matrix.add_apply]; exact Submodule.add_mem _ (hx i j) (hy i j)
  have hPneg : ∀ x, P x → P (-x) := fun x hx i j => by
    rw [Matrix.neg_apply]; exact Submodule.neg_mem _ (hx i j)
  have hP0 : P 0 := fun i j => by rw [Matrix.zero_apply]; exact Submodule.zero_mem _
  have hann : ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
      (∀ m ∈ latO S T (LS : Set _) (LT : Set _) (· ∈ Q), ∀ m' ∈ latO S T (LS : Set _) (LT : Set _) (· ∈ Q),
        ψ (symplO S T m m') = 1) ∧
      (∀ x, P x → (∀ m ∈ latO S T (LS : Set _) (LT : Set _) (· ∈ Q), ψ (symplO S T m x) = 1) →
        x ∈ latO S T (LS : Set _) (LT : Set _) (· ∈ Q)) := by
    intro LS LT h1 h2
    have A := GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT h1 h2 (· ∈ Q)
    refine ⟨fun m hm m' hm' => (A m (GlobalTheory.FinPl.LatMem.latO_mxAt hm)).1 hm m' hm',
      fun x hx h => (A x hx).2 fun u' hu' => ?_⟩
    rw [GlobalTheory.SplitScalar.symplO_skew S T u' x, psi_neg, h u' hu', inv_one]
  obtain ⟨qM, hqM⟩ := vac_eigen ψ hψ S T M M' hM hM' Q
  obtain ⟨qN, hqN⟩ := vac_eigen ψ hψ S T N N' hN hN' Q
  have hcomb : ∀ (c : WO S T →₀ ℂ) f, comb ψ S T c f = ∑ u ∈ c.support, c u • heisO ψ S T u f := fun _ _ => rfl
  have hg0 : g₀ ≠ 0 := by
    rintro rfl; apply hne; rw [hcomb]
    exact Finset.sum_eq_zero fun u _ => by rw [heisO_zero_fun, smul_zero]
  set F' := comb ψ S T o' g₀ with hF'def
  have hqM0 : ∀ m ∈ latO S T (M : Set _) (M' : Set _) (· ∈ Q), qM m ≠ 0 := fun m hm =>
    eig_ne ψ S T (hqM m hm g₀ hg) hg0
  have hqN0 : ∀ m ∈ latO S T (N : Set _) (N' : Set _) (· ∈ Q), qN m ≠ 0 := fun m hm =>
    eig_ne ψ S T (hqN m hm F' hF') hne
  let U : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ {x | ∃ y, P y ∧ x = heisO ψ S T y F'}
  have hU : ∀ m, P m → ∀ x ∈ U, heisO ψ S T m x ∈ U := by
    intro m hm x hx
    have hle : U ≤ U.comap (hL ψ S T m) := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change heisO ψ S T m (heisO ψ S T y F') ∈ U
      rw [GlobalTheory.SplitScalar.heisO_heisO]
      exact U.smul_mem _ (Submodule.subset_span ⟨m + y, hPadd _ _ hm hy, rfl⟩))
    exact hle hx
  have hF'U0 : F' ∈ U := Submodule.subset_span ⟨0, hP0, (GlobalTheory.LatVac.heisO_zero ψ F').symm⟩
  have hF'U : ∑ u ∈ o'.support, o' u • heisO ψ S T (id u) g₀ ∈ U := by
    rw [hF'def, hcomb] at hF'U0; exact hF'U0

  have tM1 : ∀ m ∈ latO S T (M : Set _) (M' : Set _) (· ∈ Q), ∀ m' ∈ latO S T (M : Set _) (M' : Set _) (· ∈ Q),
      ψ (symplO S T m m') = 1 := (hann M M' hM hM').1
  have tM2 : ∀ x, P x → (∀ m ∈ latO S T (M : Set _) (M' : Set _) (· ∈ Q), ψ (symplO S T m x) = 1) →
      x ∈ latO S T (M : Set _) (M' : Set _) (· ∈ Q) := (hann M M' hM hM').2
  have tM3 : ∀ m ∈ latO S T (M : Set _) (M' : Set _) (· ∈ Q), P m := fun m hm => GlobalTheory.FinPl.LatMem.latO_mxAt hm
  have tMq : ∀ m ∈ latO S T (M : Set _) (M' : Set _) (· ∈ Q), heisO ψ S T m g₀ = qM m • g₀ :=
    fun m hm => hqM m hm g₀ hg
  have hA := class_mem ψ S T _ P tM1 tM2 tM3 hPsub g₀ qM tMq hqM0 U (fun m hm => hU m (tM3 m hm)) o'.support id o' ho' hF'U
  obtain ⟨i, hi, hne'⟩ : ∃ i ∈ o'.support, (∑ j ∈ o'.support with
      (QuotientAddGroup.mk (id j) : WO S T ⧸ latO S T (M : Set _) (M' : Set _) (· ∈ Q)) = QuotientAddGroup.mk (id i),
      o' j • heisO ψ S T (id j) g₀) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    show ∑ u ∈ o'.support, o' u • heisO ψ S T u g₀ = 0
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun j => (QuotientAddGroup.mk j : WO S T ⧸ latO S T (M : Set _) (M' : Set _) (· ∈ Q)))
      (t := o'.support.image (fun j => (QuotientAddGroup.mk j : WO S T ⧸ latO S T (M : Set _) (M' : Set _) (· ∈ Q))))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_eq_zero fun C hC => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hC
    exact hcon i hi
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.1
    (class_line ψ S T _ g₀ qM tMq o'.support id o' i)
  have hκ0 : κ ≠ 0 := by rintro rfl; rw [zero_smul] at hκ; exact hne' hκ.symm
  have hyU : heisO ψ S T i g₀ ∈ U := by
    have := U.smul_mem κ⁻¹ (hA i hi)
    rwa [← hκ, smul_smul, inv_mul_cancel₀ hκ0, one_smul] at this
  have hg0U : g₀ ∈ U := by
    have := U.smul_mem (ψ (symplOH S T (-i) i))⁻¹ (hU (-i) (hPneg _ (ho' i hi)) _ hyU)
    rwa [heisO_inv, smul_smul, inv_mul_cancel₀ (psi_ne _ _), one_smul] at this

  have hFU : comb ψ S T o g₀ ∈ U := by
    rw [hcomb]
    exact U.sum_mem fun u hu => U.smul_mem _ (hU u (ho u hu) g₀ hg0U)
  by_cases hF0 : comb ψ S T o g₀ = 0
  · exact ⟨0, by rw [hF0, zero_smul]⟩
  obtain ⟨n, cf, gf, hgf⟩ := (Submodule.mem_span_set').1 hFU
  have hgf' : ∀ i, ∃ y, P y ∧ (gf i : WO S T → ℂ) = heisO ψ S T y F' := fun i => (gf i).2
  choose y hyP hyeq using hgf'
  have hFsum : ∑ i ∈ Finset.univ, cf i • heisO ψ S T (y i) F' = comb ψ S T o g₀ := by
    rw [← hgf]; exact Finset.sum_congr rfl fun i _ => by rw [hyeq i]
  set F := comb ψ S T o g₀ with hFdef
  have tN1 : ∀ m ∈ latO S T (N : Set _) (N' : Set _) (· ∈ Q), ∀ m' ∈ latO S T (N : Set _) (N' : Set _) (· ∈ Q),
      ψ (symplO S T m m') = 1 := (hann N N' hN hN').1
  have tN2 : ∀ x, P x → (∀ m ∈ latO S T (N : Set _) (N' : Set _) (· ∈ Q), ψ (symplO S T m x) = 1) →
      x ∈ latO S T (N : Set _) (N' : Set _) (· ∈ Q) := (hann N N' hN hN').2
  have tN3 : ∀ m ∈ latO S T (N : Set _) (N' : Set _) (· ∈ Q), P m := fun m hm => GlobalTheory.FinPl.LatMem.latO_mxAt hm
  have tNq : ∀ m ∈ latO S T (N : Set _) (N' : Set _) (· ∈ Q), heisO ψ S T m F' = qN m • F' :=
    fun m hm => hqN m hm F' hF'
  have hB := class_mem ψ S T _ P tN1 tN2 tN3 hPsub F' qN tNq hqN0 (ℂ ∙ F)
    (fun m hm x hx => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [GlobalTheory.LatVac.heisO_smul, hqN m hm F hF, smul_smul]
      exact Submodule.mem_span_singleton.2 ⟨a * qN m, rfl⟩)
    Finset.univ y cf (fun i _ => hyP i) (by rw [hFsum]; exact Submodule.mem_span_singleton_self F)
  obtain ⟨i, -, hne2⟩ : ∃ i ∈ (Finset.univ : Finset (Fin n)), (∑ j ∈ Finset.univ with
      (QuotientAddGroup.mk (y j) : WO S T ⧸ latO S T (N : Set _) (N' : Set _) (· ∈ Q)) = QuotientAddGroup.mk (y i),
      cf j • heisO ψ S T (y j) F') ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hF0
    rw [← hFsum, ← Finset.sum_fiberwise_of_maps_to
      (g := fun j => (QuotientAddGroup.mk (y j) : WO S T ⧸ latO S T (N : Set _) (N' : Set _) (· ∈ Q)))
      (t := Finset.univ.image (fun j => (QuotientAddGroup.mk (y j) : WO S T ⧸ latO S T (N : Set _) (N' : Set _) (· ∈ Q))))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_eq_zero fun C hC => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hC
    exact hcon i hi
  obtain ⟨κ', hκ'⟩ := Submodule.mem_span_singleton.1
    (class_line ψ S T _ F' qN tNq Finset.univ y cf i)
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 (hB i (Finset.mem_univ _))
  have hκ'0 : κ' ≠ 0 := by rintro rfl; rw [zero_smul] at hκ'; exact hne2 hκ'.symm
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_smul] at hμ; exact hne2 hμ.symm
  have hX : heisO ψ S T (y i) F' = (κ'⁻¹ * μ) • F := by
    rw [mul_smul, hμ, ← hκ', smul_smul, inv_mul_cancel₀ hκ'0, one_smul]
  have hyN : y i ∈ latO S T (N : Set _) (N' : Set _) (· ∈ Q) := by
    refine tN2 _ (hyP i) fun m hm => ?_
    have e1 := heisO_eig ψ S T (y := y i) (hqN m hm F' hF')
    rw [hX, GlobalTheory.LatVac.heisO_smul, hqN m hm F hF, smul_smul, smul_smul] at e1
    have e2 := smul_left_injective ℂ hF0 e1
    have hk : κ'⁻¹ * μ ≠ 0 := mul_ne_zero (inv_ne_zero hκ'0) hμ0
    have e3 : (κ'⁻¹ * μ * qN m) * ψ (symplO S T m (y i)) = (κ'⁻¹ * μ * qN m) * 1 := by
      linear_combination -e2
    exact mul_left_cancel₀ (mul_ne_zero hk (hqN0 m hm)) e3
  refine ⟨μ⁻¹ * κ' * qN (y i), ?_⟩
  rw [mul_smul, ← hqN _ hyN F' hF', hX, smul_smul, show μ⁻¹ * κ' * (κ'⁻¹ * μ) = 1 by field_simp, one_smul]

end GlobalTheory.VacScalar
