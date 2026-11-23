import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleFrameExists
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

section SlopeTestRemainingChoices
open CategoryTheory.Limits TopologicalSpace
open GlobalTheory.Twist (resM resM_resM resM_smul resM_self app_resM)

variable {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {ι : Type}

private def UpperTheory.vanishingCoordinates (ch : ι → VB.Chart M r) (n : ℕ) : VB.Sub M where
  sec V :=
    { carrier := {s | ∀ (k : ι) (W : X.Opens) (h₁ : W ≤ V) (h₂ : W ≤ (ch k).U) (a : Fin r), n ≤ (a : ℕ) →
        ((ch k).isFrame.basis h₂).repr (resM M h₁ s) a = 0}
      add_mem' := fun hs ht k W h₁ h₂ a ha => by
        rw [map_add, map_add, Finsupp.add_apply, hs k W h₁ h₂ a ha, ht k W h₁ h₂ a ha, add_zero]
      zero_mem' := fun k W h₁ h₂ a ha => by rw [map_zero, map_zero, Finsupp.zero_apply]
      smul_mem' := fun c s hs k W h₁ h₂ a ha => by
        rw [resM_smul, map_smul, Finsupp.smul_apply, hs k W h₁ h₂ a ha, smul_zero] }
  res_mem h s hs k W h₁ h₂ a ha := by
    rw [resM_resM]; exact hs k W _ h₂ a ha
  mem_of_local {V s} H k W h₁ h₂ a ha := by
    choose T hT hx hs using fun x : W => H x (h₁ x.2)
    refine LB.fun_ext_of_cover (fun x : W => W ⊓ T x) (fun _ => inf_le_left)
      (fun x hxW => Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hxW, hx _⟩) fun x => ?_
    have := hs x k (W ⊓ T x) inf_le_right (inf_le_left.trans h₂) a ha
    rw [resM_resM] at this
    rw [← (ch k).isFrame.repr_resM, resM_resM, this, map_zero]

private theorem UpperTheory.mem_vanishing_coordinates (ch : ι → VB.Chart M r) (H : ∀ k k', IsTri (trS (ch k) (ch k'))) (n : ℕ) (k : ι)
    (V : X.Opens) (h : V ≤ (ch k).U) (s : Γ(M, V)) :
    s ∈ (UpperTheory.vanishingCoordinates ch n).sec V ↔ ∀ a : Fin r, n ≤ (a : ℕ) → ((ch k).isFrame.basis h).repr s a = 0 := by
  refine ⟨fun hs a ha => ?_, fun hs k' W h₁ h₂ a ha => ?_⟩
  · have := hs k V le_rfl h a ha
    rwa [resM_self] at this
  · rw [← ((ch k).isFrame.basis (h₁.trans h)).sum_repr (resM M h₁ s)]
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      IsFrame.basis_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : n ≤ (b : ℕ)
    · rw [(ch k).isFrame.repr_resM h h₁, hs b hb, map_zero, zero_mul]
    · have hW : W ≤ (ch k').U ⊓ (ch k).U := le_inf h₂ (h₁.trans h)
      have h0 : trS (ch k') (ch k) a b = 0 := H k' k a b (by rw [Fin.lt_def]; omega)
      have h1 := (ch k').isFrame.repr_resM inf_le_left hW (resM M inf_le_right ((ch k).e b)) a
      rw [resM_resM] at h1
      rw [trS, of_apply] at h0
      rw [h1, h0, map_zero, mul_zero]

private theorem UpperTheory.flag_charts_frames (N : VB.Sub M) (n : ℕ) (c : VB.Chart M r)
    (hN : ∀ (V : X.Opens) (h : V ≤ c.U) (s : Γ(M, V)),
      s ∈ N.sec V ↔ ∀ a : Fin r, n ≤ (a : ℕ) → (c.isFrame.basis h).repr s a = 0) :
    (∀ a : Fin r, (a : ℕ) < n → c.e a ∈ N.sec c.U) ∧
    (∃ f : {a : Fin r // (a : ℕ) < n} → Γ(N.toMod, c.U), VB.IsFrame f) ∧
    VB.IsFrame fun a : {a : Fin r // ¬ (a : ℕ) < n} => (cokernel.π N.incl).app c.U (c.e a) := by
  classical
  have hmem (V : X.Opens) (h : V ≤ c.U) (a : Fin r) (ha : (a : ℕ) < n) : resM M h (c.e a) ∈ N.sec V := by
    refine (hN V h _).2 fun b hb => ?_
    rw [← c.isFrame.basis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne]
    rintro rfl
    omega
  have hm (a : Fin r) (ha : (a : ℕ) < n) : c.e a ∈ N.sec c.U := by
    have := hmem _ le_rfl a ha
    rwa [resM_self] at this
  have hsplit (V : X.Opens) (h : V ≤ c.U) (s : Γ(M, V)) :
      s = ∑ a : {a : Fin r // (a : ℕ) < n}, (c.isFrame.basis h).repr s a • resM M h (c.e a) +
        ∑ a : {a : Fin r // ¬ (a : ℕ) < n}, (c.isFrame.basis h).repr s a • resM M h (c.e a) := by
    rw [Fintype.sum_subtype_add_sum_subtype (fun a : Fin r => (a : ℕ) < n)
      (fun a => (c.isFrame.basis h).repr s a • resM M h (c.e a))]
    simp only [← c.isFrame.basis_apply h]
    exact ((c.isFrame.basis h).sum_repr s).symm
  refine ⟨hm, ⟨fun a => N.mkSec (c.e a) (hm a a.2), fun V h => ⟨?_, fun t => ?_⟩⟩, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h0 := congrArg (N.incl.app V) ha
    simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul, app_resM,
      VB.Sub.incl_app_mkSec, map_zero] at h0
    have hli := ((VB.isFrame_iff.1 c.isFrame V h).1).comp (Subtype.val : {a : Fin r // (a : ℕ) < n} → _)
      Subtype.val_injective
    exact funext (Fintype.linearIndependent_iff.1 hli a h0)
  · refine ⟨fun a => (c.isFrame.basis h).repr (N.incl.app V t) a, N.incl_app_injective V ?_⟩
    simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul, app_resM,
      VB.Sub.incl_app_mkSec]
    refine Eq.symm ((hsplit V h _).trans ?_)
    rw [add_eq_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [(hN V h _).1 (N.incl_app_mem t) a (not_lt.1 a.2), zero_smul]
  · refine CokerFrame.isFrame_of_injective_of_local (fun V h => ?_) (fun V h s x hx => ?_)
    · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      simp only [Fintype.linearCombination_apply, ← app_resM, ← Scheme.Modules.Hom.app_smul,
        ← map_sum] at ha
      funext b
      have h1 := (hN V h _).1 (N.cokernel_π_app_eq_zero_iff.1 ha) b (not_lt.1 b.2)
      simp only [← c.isFrame.basis_apply h, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum,
        Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, Subtype.val_inj, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
      exact h1
    · obtain ⟨W, hWV, hxW, t, ht⟩ := VB.exists_app_eq_of_epi (cokernel.π N.incl) s hx
      refine ⟨W, hWV, hxW, fun a => (c.isFrame.basis (hWV.trans h)).repr t a, ?_⟩
      rw [← ht, Fintype.linearCombination_apply]
      conv_rhs => rw [hsplit W (hWV.trans h) t]
      rw [map_add, N.cokernel_π_app_eq_zero_iff.2
        (Submodule.sum_mem _ fun (a : {a : Fin r // (a : ℕ) < n}) _ =>
          Submodule.smul_mem _ _ (hmem W (hWV.trans h) a.1 a.2)), zero_add, map_sum]
      simp only [Scheme.Modules.Hom.app_smul, app_resM]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_flag_of_triangular_charts :
    ∀ (X : Scheme.{0}) (M : X.Modules) (r : ℕ) (ι : Type) (ch : ι → Chart M r), (∀ x : X, ∃ k, x ∈ (ch k).U) → (∀ k k', IsTri (trS (ch k) (ch k'))) → ∃ fl : Vert.Flag M r, ∀ k, IsAdapted fl (ch k) := by
  intro X M r ι ch hc H
  let N : Fin (r + 1) → VB.Sub M := fun i => UpperTheory.vanishingCoordinates ch i
  have hF (i : Fin (r + 1)) (k : ι) := UpperTheory.flag_charts_frames (N i) i (ch k) (UpperTheory.mem_vanishing_coordinates ch H i k)
  have hstep : ∀ (i : Fin r) V s, (N i.castSucc).incl.app V s ∈ (N i.succ).sec V :=
    fun i V s k W h₁ h₂ a ha => (N i.castSucc).incl_app_mem s k W h₁ h₂ a (by
      simp only [Fin.val_succ, Fin.val_castSucc] at ha ⊢; omega)
  refine ⟨{ F := fun i => (N i).toMod
            ι := fun i => (N i).incl
            isSubbundle := fun i => ⟨inferInstance, _,
              VB.isVB_of_frames (ι := {a : Fin r // ¬ (a : ℕ) < i}) rfl fun x => ?_⟩
            isVB := fun i => VB.isVB_of_frames (ι := {a : Fin r // (a : ℕ) < i}) ?_ fun x => ?_
            step := fun i => (N i.succ).lift _ (hstep i)
            step_ι := fun i => (N i.succ).lift_incl _ (hstep i)
            isIso_last := ?_ }, fun k i => ?_⟩
  · obtain ⟨k, hk⟩ := hc x
    exact ⟨_, _, hk, (hF i k).2.2⟩
  · exact Fintype.card_fin_lt_of_le i.is_le
  · obtain ⟨k, hk⟩ := hc x
    obtain ⟨f, hf⟩ := (hF i k).2.1
    exact ⟨_, f, hk, hf⟩
  · refine Twist.isIso_of_bijective _ fun V => ⟨(N _).incl_app_injective V, fun s => ?_⟩
    exact (N _).mem_sec_iff.1 fun k W h₁ h₂ a ha => absurd a.2 (not_lt.2 ha)
  · exact (N _).mem_sec_iff.1 ((hF i.succ k).1 i (Nat.lt_succ_self _))
