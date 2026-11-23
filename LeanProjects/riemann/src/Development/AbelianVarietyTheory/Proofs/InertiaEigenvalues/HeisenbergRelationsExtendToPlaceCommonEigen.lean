import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointEigenvectorsEqZeroOfSumEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

variable {D : D7}

theorem psi_ne_zero' (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem heisO_injective (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) {f g : WO S T → ℂ}
    (h : heisO ψ S T w f = heisO ψ S T w g) : f = g := by
  funext x
  have := congrFun h (x - w)
  simp only [heisO, sub_add_cancel] at this
  exact mul_left_cancel₀ (psi_ne_zero' ψ _) this

theorem heisO_fun_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    heisO ψ S T w (0 : WO S T → ℂ) = 0 := by
  funext x
  simp [heisO]

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ)
    (X : WO S T → ℂ) : comb ψ S T c X = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u X) c := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem comb_sum_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ι : Type} (s : Finset ι) (r : ι → WO S T)
    (z : ι → ℂ) (X : WO S T → ℂ) :
    comb ψ S T (∑ i ∈ s, Finsupp.single (r i) (z i)) X = ∑ i ∈ s, z i • heisO ψ S T (r i) X := by
  rw [comb_eq_linearCombination, map_sum]
  simp only [Finsupp.linearCombination_single]

theorem comb_fun_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    comb ψ S T c (0 : WO S T → ℂ) = 0 := by
  unfold comb Finsupp.sum
  exact Finset.sum_eq_zero fun u _ => by
    show c u • heisO ψ S T u 0 = 0
    rw [heisO_fun_zero, smul_zero]

theorem relOff_factor {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Sb : Finset (FinPl D)} {p f : WO S T → ℂ}
    (hR : RelOff ψ S T Sb p f) (w : WO S T) (s : Finset (WO S T)) (a e : WO S T → ℂ) (r : WO S T → WO S T)
    (hr : ∀ u ∈ s, OffPl Sb (r u))
    (hp : ∀ u ∈ s, heisO ψ S T u p = e u • heisO ψ S T w (heisO ψ S T (r u) p))
    (hf : ∀ u ∈ s, heisO ψ S T u f = e u • heisO ψ S T w (heisO ψ S T (r u) f))
    (h0 : ∑ u ∈ s, a u • heisO ψ S T u p = 0) : ∑ u ∈ s, a u • heisO ψ S T u f = 0 := by
  classical
  set c' : WO S T →₀ ℂ := ∑ u ∈ s, Finsupp.single (r u) (a u * e u) with hc'
  have key : ∀ X : WO S T → ℂ, (∀ u ∈ s, heisO ψ S T u X = e u • heisO ψ S T w (heisO ψ S T (r u) X)) →
      ∑ u ∈ s, a u • heisO ψ S T u X = heisO ψ S T w (comb ψ S T c' X) := by
    intro X hX
    rw [hc', comb_sum_single, GlobalTheory.SplitScalar.heisO_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hX u hu, GlobalTheory.SplitScalar.heisO_smul, smul_smul]
  have hsupp : ∀ u ∈ c'.support, OffPl Sb u := by
    intro u hu
    obtain ⟨x, hx, hx'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hu)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx')]
    exact hr x hx
  have hp0 : comb ψ S T c' p = 0 := by
    apply heisO_injective ψ S T w
    rw [← key p hp, h0, heisO_fun_zero]
  rw [key f hf, hR c' hsupp hp0, heisO_fun_zero]

theorem offPl_zero (Sb : Finset (FinPl D)) (S T : HSp D) : OffPl Sb (0 : WO S T) :=
  ⟨by ext i j; simp, fun _ _ _ _ _ _ => by simp⟩

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (z : ℂ) (X : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u z) X = z • heisO ψ S T u X := by
  unfold comb
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem isHalf_one_sub {S T : HSp D} {b : AE D} (hb2 : b * b = b) (u : WO S T) : IsHalf (1 - b) (u - b • u) := by
  intro i j
  show (1 - b) * (u i j - b * u i j) = u i j - b * u i j
  rw [mul_sub, sub_mul, sub_mul, one_mul, one_mul, ← mul_assoc, hb2, sub_self, sub_zero]

theorem heisO_decomp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {b : AE D} (hb2 : b * b = b) (hcb : cA D b = b)
    (u u0 : WO S T) (X : WO S T → ℂ) (z : ℂ) (hX : heisO ψ S T (b • u - b • u0) X = z • X) :
    heisO ψ S T u X = ((ψ (symplOH S T (b • u0) (u - b • u0)))⁻¹ * z) •
      heisO ψ S T (b • u0) (heisO ψ S T (u - b • u) X) := by
  have hab : cA D (1 - b) * b = 0 := by rw [map_sub, map_one, hcb, sub_mul, one_mul, hb2, sub_self]
  have horth0 : symplO S T (u - b • u) (b • u - b • u0) = 0 :=
    GlobalTheory.SplitScalar.symplO_eq_zero S T hab (isHalf_one_sub hb2 u)
      (GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitScalar.isHalf_smul hb2 u) (GlobalTheory.SplitScalar.isHalf_smul hb2 u0))
  have h1 : heisO ψ S T (b • u0) (heisO ψ S T (u - b • u) (heisO ψ S T (b • u - b • u0) X)) =
      ψ (symplOH S T (b • u0) (u - b • u0)) • heisO ψ S T u X := by
    rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T horth0, GlobalTheory.SplitScalar.heisO_heisO, sub_add_sub_cancel,
      add_sub_cancel]
  rw [hX, GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_smul] at h1
  rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (psi_ne_zero' ψ _), one_smul]

theorem offPl_sub_idem {S T : HSp D} {Sb : Finset (FinPl D)} {v : FinPl D} {u : WO S T}
    (hu : OffPl (dropPl Sb v) u) : OffPl Sb (u - idem D (.inl v) • u) := by
  classical
  obtain ⟨hidem, horth, -, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  refine ⟨Matrix.ext fun i j => ?_, fun q hq ε hε i j => ?_⟩
  · have h : infPart D (u i j) = 0 := congrFun (congrFun hu.1 i) j
    show infPart D (u i j - idem D (.inl v) * u i j) = 0
    rw [map_sub, map_mul, (hfin v).1, h, zero_mul, sub_zero]
  · rw [placeIdem_eq hε]
    show idem D (.inl q) * (u i j - idem D (.inl v) * u i j) = 0
    by_cases hqv : q = v
    · rw [hqv, mul_sub, ← mul_assoc, hidem, sub_self]
    · have hq' : q ∈ dropPl Sb v := by unfold dropPl; exact Finset.mem_erase.2 ⟨hqv, hq⟩
      have h1 := hu.2 q hq' _ ((hfin q).2.2) i j
      rw [placeIdem_eq ((hfin q).2.2)] at h1
      rw [mul_sub, h1, ← mul_assoc, horth (.inl q) (.inl v) (fun h => hqv (Sum.inl.inj h)), zero_mul, sub_zero]

theorem relOff_dropPl_of_coEig : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D))
    (v : FinPl D), v ∈ Sb → ∀ (p f : WO S T → ℂ), (∀ u, IsHalf (idem D (.inl v)) u → CoEig ψ S T p f u ∨
      ∃ l, IsHalf (idem D (.inl v)) l ∧ CoEig ψ S T p f l ∧ ψ (symplO S T l u) ≠ 1) →
    RelOff ψ S T Sb p f → RelOff ψ S T (dropPl Sb v) p f := by
  classical
  intro D ψ S T Sb v _ p f hH hR c hc hcp
  have hrest : ∀ u : WO S T, OffPl (dropPl Sb v) u → OffPl Sb (u - idem D (.inl v) • u) :=
    fun u hu => offPl_sub_idem hu
  obtain ⟨hidem, -, hconj, -, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  obtain ⟨b, hb⟩ : ∃ b, b = idem D (.inl v) := ⟨_, rfl⟩
  rw [← hb] at hH hrest
  have hb2 : b * b = b := by rw [hb]; exact hidem _
  have hcb : cA D b = b := by rw [hb]; exact hconj _
  by_cases hp0 : p = 0
  · have hf0 : f = 0 := by
      have h1 := hR (Finsupp.single 0 1) (fun u hu => by
        rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]; exact offPl_zero Sb S T) (by
        rw [comb_single, GlobalTheory.SplitScalar.heisO_zero, one_smul, hp0])
      rwa [comb_single, GlobalTheory.SplitScalar.heisO_zero, one_smul] at h1
    rw [hf0, comb_fun_zero]

  have hcl : ∀ l : {l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l}, ∃ z : ℂ, z ≠ 0 ∧
      heisO ψ S T l.1 p = z • p ∧ heisO ψ S T l.1 f = z • f := by
    rintro ⟨l, -, z, h1, h2⟩
    refine ⟨z, fun hz => hp0 ?_, h1, h2⟩
    apply heisO_injective ψ S T l
    rw [h1, hz, zero_smul, heisO_fun_zero]
  choose cl hcl0 hclp _ using hcl
  obtain ⟨χ, hχ⟩ : ∃ χ : WO S T → {l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l} → ℂ,
      ∀ u l, χ u l = ψ (symplO S T l.1 u) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : (WO S T → ℂ) → ({l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l} → ℂ) → (WO S T → ℂ),
      ∀ X k, V X k = ∑ u ∈ c.support with χ u = k, c u • heisO ψ S T u X := ⟨_, fun _ _ => rfl⟩
  have hcomb : ∀ X, ∑ k ∈ c.support.image χ, V X k = comb ψ S T c X := by
    intro X
    simp only [hV]
    exact Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image_of_mem χ hu) _
  have heig : ∀ k ∈ c.support.image χ, ∀ l, GlobalTheory.SplitScalar.heisL ψ S T l.1 (V p k) = (k l * cl l) • V p k := by
    intro k _ l
    rw [GlobalTheory.SplitScalar.heisL_apply, hV, GlobalTheory.SplitScalar.heisO_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← (Finset.mem_filter.1 hu).2, hχ, GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_comm, hclp,
      GlobalTheory.SplitScalar.heisO_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hVp : ∀ k ∈ c.support.image χ, V p k = 0 :=
    GlobalTheory.joint_eigenvectors_eq_zero_of_sum_eq_zero _ _ _ (fun l => GlobalTheory.SplitScalar.heisL ψ S T l.1)
      (fun k l => k l * cl l) (V p) _ heig
      (fun k1 _ k2 _ h => funext fun l => mul_right_cancel₀ (hcl0 l) (congrFun h l)) (by rw [hcomb]; exact hcp)
  have hVf : ∀ k ∈ c.support.image χ, V f k = 0 := by
    intro k hk
    obtain ⟨u0, _, hu0k⟩ := Finset.mem_image.1 hk
    have hCo : ∀ u ∈ c.support.filter (fun u => χ u = k), ∃ z : ℂ,
        heisO ψ S T (b • u - b • u0) p = z • p ∧ heisO ψ S T (b • u - b • u0) f = z • f := by
      intro u hu
      have hχu := (Finset.mem_filter.1 hu).2
      rcases hH _ (GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitScalar.isHalf_smul hb2 u)
          (GlobalTheory.SplitScalar.isHalf_smul hb2 u0)) with h | ⟨l, hl, hlco, hne⟩
      · exact h
      · exfalso
        apply hne
        have e1 : ψ (symplO S T l u) = ψ (symplO S T l u0) := by
          have := congrFun (hχu.trans hu0k.symm) ⟨l, hl, hlco⟩
          rwa [hχ, hχ] at this
        have hbl : ∀ x, symplO S T l (b • x) = symplO S T l x := fun x => by
          conv_lhs => rw [← hcb]
          rw [← GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ l).1 hl]
        have e2 : symplO S T l (b • u - b • u0) + symplO S T l (b • u0) = symplO S T l (b • u) := by
          rw [← GlobalTheory.LatVac.symplO_add_right, sub_add_cancel]
        rw [hbl, hbl] at e2
        have e3 := congrArg ψ e2
        rw [AddChar.map_add_eq_mul, e1] at e3
        exact mul_right_cancel₀ (psi_ne_zero' ψ _) (e3.trans (one_mul _).symm)
    choose! eco hecp hecf using hCo
    have key := relOff_factor hR (b • u0) (c.support.filter fun u => χ u = k) c
      (fun u => (ψ (symplOH S T (b • u0) (u - b • u0)))⁻¹ * eco u) (fun u => u - b • u)
      (fun u hu => hrest u (hc u (Finset.mem_filter.1 hu).1))
      (fun u hu => heisO_decomp ψ S T hb2 hcb u u0 p _ (hecp u hu))
      (fun u hu => heisO_decomp ψ S T hb2 hcb u u0 f _ (hecf u hu))
      (by rw [← hV]; exact hVp k hk)
    rw [hV]
    exact key
  rw [← hcomb f]
  exact Finset.sum_eq_zero hVf

end GlobalTheory.DownLift.GenSplit

end
