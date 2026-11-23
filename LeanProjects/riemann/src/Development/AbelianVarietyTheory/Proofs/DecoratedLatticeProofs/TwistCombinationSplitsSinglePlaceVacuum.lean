import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommute
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedAtPlaceOfIsHalfSplitPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPlaceSplit

variable {D : D7}

theorem coeff_mul_eq {G : Type} [AddMonoid G] (x y : AddMonoidAlgebra ℂ G) :
    (x * y).coeff = x.coeff.sum fun g a => y.coeff.sum fun h b => Finsupp.single (g + h) (a * b) := by
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single]

theorem aconv_eq_prod {G : Type} [AddCommMonoid G] (l : List (G →₀ ℂ)) :
    AddMonoidAlgebra.ofCoeff (aconv l) = (l.map AddMonoidAlgebra.ofCoeff).prod := by
  induction l with
  | nil =>
    apply AddMonoidAlgebra.ext
    rw [List.map_nil, List.prod_nil, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_ofCoeff]
    rfl
  | cons e l ih =>
    apply AddMonoidAlgebra.ext
    rw [List.map_cons, List.prod_cons, ← ih, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff,
      AddMonoidAlgebra.coeff_ofCoeff, AddMonoidAlgebra.coeff_ofCoeff]
    rfl

theorem support_prod_mem {G ι : Type} [AddCommMonoid G] (M : AddSubmonoid G) (s : Finset ι) (g : ι → G →₀ ℂ)
    (h : ∀ i ∈ s, ∀ y ∈ (g i).support, y ∈ M) :
    ∀ y ∈ (∏ i ∈ s, AddMonoidAlgebra.ofCoeff (g i)).coeff.support, y ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy
    rw [Finset.prod_empty, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single] at hy
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]
    exact M.zero_mem
  | insert a s ha ih =>
    intro y hy
    rw [Finset.prod_insert ha, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff] at hy
    obtain ⟨x, hx, hy2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
    obtain ⟨z, hz, hy3⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy2)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy3)]
    exact M.add_mem (h a (Finset.mem_insert_self a s) x hx)
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) z hz)

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO hO
  simp

theorem comb_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AddMonoidAlgebra ℂ (WO S T))
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (a * b).coeff f = comb ψ S T a.coeff (comb ψ S T b.coeff f) := by
  have hz : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have ha : ∀ u (r r' : ℂ), (r + r') • heisO ψ S T u f = r • heisO ψ S T u f + r' • heisO ψ S T u f :=
    fun u r r' => add_smul _ _ _
  rw [GlobalTheory.HeisComb.comb_comb, coeff_mul_eq, GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha]
  simp only [Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha, Finsupp.sum_single_index, zero_smul]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.WeilVacMove.heisO_heisO, symplOH, h x hx y hy, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem heisO_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (b : WO S T →₀ ℂ)
    (h : ∀ y ∈ b.support, symplO S T u y = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (comb ψ S T b f) = comb ψ S T b (heisO ψ S T u f) := by
  unfold comb
  rw [GlobalTheory.HeisComb.heisO_finset_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T u y = 0 := by unfold symplOH; rw [h y hy, mul_zero]
  rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, add_comm y u, h0, GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]

theorem map_infPart_of_mxAt {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {y : Mx D m n} (hy : GlobalTheory.FinPl.MxAt P y) :
    y.map (infPart D) = 0 := by
  funext a b
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact (RingHom.mem_ker).1 (Submodule.mem_inf.1 (hy a b)).1

end GlobalTheory.TwistPlaceSplit

namespace GlobalTheory.TwistPlaceSplit

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ (i : Fin F.r) Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∃ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ ∧ comb c.ψ _ _ (w.eQ j) Ψ₁ = comb c.ψ _ _ ((F.Q i).eL j) f₁ := by
  intro D c v t w F hc hv hP j hj i Ψ₁ hΨ
  classical
  set v₀ := (F.Q i).q.v with hv₀def
  have hv₀ : v₀ ∈ w.Q := (hP.places v₀).2 ⟨i, rfl⟩

  have hat : ∀ i', ∀ u ∈ ((F.Q i').eL j).support, GlobalTheory.FinPl.MxAt (· = (F.Q i').q.v) u := by
    intro i' u hu
    have hs := (F.Q i').hs
    obtain ⟨d, hd⟩ : ∃ d, j + d = (F.Q i').s := ⟨(F.Q i').s - j, by omega⟩
    exact GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (F.Q i').q u (((F.Q i').eL_at j d hd).1 u hu)

  let M : AddSubmonoid (WO (c.V j) (c.V (j + 1))) :=
    { carrier := {y | (∀ x, GlobalTheory.FinPl.MxAt (· = v₀) x → symplO _ _ x y = 0) ∧ y.map (infPart D) = 0}
      add_mem' := fun {y y'} hy hy' => ⟨fun x hx => by rw [symplO_add_right, hy.1 x hx, hy'.1 x hx, add_zero], by
        rw [Matrix.map_add _ (map_add (infPart D)), hy.2, hy'.2, add_zero]⟩
      zero_mem' := ⟨fun x _ => symplO_zero_right _ _ x, by
        funext a b
        simp⟩ }
  have hM : ∀ i' ∈ Finset.univ.erase i, ∀ y ∈ ((F.Q i').eL j).support, y ∈ M := by
    intro i' hi' y hy
    have hne : v₀ ≠ (F.Q i').q.v := fun e => Finset.ne_of_mem_erase hi' (hP.inj e).symm
    exact ⟨fun x hx => GlobalTheory.FinPl.OverSwap.symplO_eq_zero_of_ne hne hx (hat i' y hy), map_infPart_of_mxAt (hat i' y hy)⟩
  set B := ∏ i' ∈ Finset.univ.erase i, AddMonoidAlgebra.ofCoeff ((F.Q i').eL j) with hB
  have hb : ∀ y ∈ B.coeff.support, y ∈ M := support_prod_mem M _ (fun i' => (F.Q i').eL j) hM
  have hprod : w.eQ j = (AddMonoidAlgebra.ofCoeff ((F.Q i).eL j) * B).coeff := by
    rw [hB, Finset.mul_prod_erase Finset.univ (fun i' => AddMonoidAlgebra.ofCoeff ((F.Q i').eL j)) (Finset.mem_univ i),
      ← Fin.prod_ofFn, hP.eQ j hj, ← AddMonoidAlgebra.coeff_ofCoeff (aconv _), aconv_eq_prod, List.map_ofFn]
    rfl

  have hmono : ∀ u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· = v₀),
      u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· ∈ w.Q) := by
    intro u hu
    refine AddSubgroup.closure_mono ?_ hu
    rintro x ⟨α, hα, hvα, rest⟩
    exact ⟨α, hα, fun v' hv' => hvα v' fun e => hv' (by rw [e]; exact hv₀), rest⟩
  refine ⟨comb c.ψ _ _ B.coeff Ψ₁, ⟨(GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 B.coeff Ψ₁ hΨ.1 (fun u hu => (hb u hu).2) hc.std,
    fun u hu => ?_, fun e he u hu hue => ?_⟩, ?_⟩
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt (AddSubgroup.nsmul_mem _ hu 2))),
      hΨ.2.1 u (hmono u hu)]
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)), hΨ.2.2 e he u (hmono u hu) hue]
  · rw [hprod, comb_mul _ _ _ _ _ (fun x hx y hy => (hb y hy).1 x (hat i x (by rwa [AddMonoidAlgebra.coeff_ofCoeff] at hx))),
      AddMonoidAlgebra.coeff_ofCoeff]

end GlobalTheory.TwistPlaceSplit
