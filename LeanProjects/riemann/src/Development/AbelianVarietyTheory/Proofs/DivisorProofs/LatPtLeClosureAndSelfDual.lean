import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] {v : Pl D.host.F} {z : M}
    (h : At (evFin D.host.F v) z) : liftV v (1 : Fv D.host.F v) • z = z := by
  have h1 := h (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm

theorem at_smul {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] (v : Pl D.host.F) (z : M) :
    At (evFin D.host.F v) (liftV v (1 : Fv D.host.F v) • z) := fun u hu => by
  rw [smul_smul, ← smul_eq_mul u, at_liftV v 1 u hu, zero_smul]

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z :=
  map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c z

theorem symplO_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : symplO S T x (c • y) = symplO S T (c • x) y := by
  have h : hO S T x (c • y) = hO S T (c • x) y := by
    unfold hO
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  unfold symplO
  rw [h]

theorem infPart_smul (v : Pl D.host.F) (z : AE D) : infPart D (liftV v (1 : Fv D.host.F v) • z) = 0 := by
  rw [Algebra.smul_def, RingHom.map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (liftV v (1 : Fv D.host.F v))) = 0 := infPart_pair _ _
  rw [this, zero_mul]

theorem smul_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (v : Pl D.host.F)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h : liftV v (1 : Fv D.host.F v) • finTens α M = finTens (singleFin v 1 * α) M := by
      ext i j
      change (pairA D.host.F 0 (singleFin v 1) * pairA D.host.F 0 α) ⊗ₜ[D.host.F] M i j = _
      rw [pair_mul]
      rfl
    rw [h]
    refine finTens_mem_latO (mul_mem_intAf (fun w => ?_) hα) hM
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleFin_self]
      exact one_mem _
    · rw [evalV_singleFin_ne hw]
      exact zero_mem _
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem isHalf_smul {m n : ℕ} {ε : AE D} (c : AF D.host.F) {u : Mx D m n} (hu : IsHalf ε u) : IsHalf ε (c • u) :=
  fun i j => by rw [Matrix.smul_apply, mul_smul_comm, hu]

theorem isHalf_zero {m n : ℕ} (ε : AE D) : IsHalf ε (0 : Mx D m n) := fun _ _ => mul_zero _

section Pair

variable {S T S' T' : HSp D} {P : Type} [AddCommGroup P] [Module (AF D.host.F) P]
  (m : P ≃ₗ[AF D.host.F] WO S T × WO S' T') (v : Pl D.host.F) (Λ : AddSubgroup P)

theorem le_of_gen {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)}
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T LS LT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' LS' LT' fun _ => True) (H : AddSubgroup P) (h2 : ∀ u ∈ Λ, 2 • u ∈ H)
    (hh : ∀ ε, IsSplitIdem D ε → ∀ u ∈ Λ, IsHalf ε (m u).1 → IsHalf ε (m u).2 → u ∈ H) : Λ ≤ H := by
  let f : WO S T × WO S' T' →ₗ[AF D.host.F] P := liftV v (1 : Fv D.host.F v) • m.symm.toLinearMap
  have hf : ∀ x, f x = liftV v (1 : Fv D.host.F v) • m.symm x := fun _ => rfl
  have hm : ∀ x, m (f x) = liftV v (1 : Fv D.host.F v) • x := fun x => by rw [hf, map_smul, m.apply_symm_apply]
  have hin : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T LS LT (fun _ => True) →
      x.2 ∈ latO S' T' LS' LT' (fun _ => True) → f x ∈ Λ := fun x h1 h2 =>
    (hΛ _).2 ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩
  intro u hu
  obtain ⟨ha, h1, h1'⟩ := (hΛ u).1 hu
  have e : u = f ((m u).1, 0) + f (0, (m u).2) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, hf, Prod.mk.eta, m.symm_apply_apply, smul_eq_of_at ha]
  rw [e]
  refine add_mem ?_ ?_
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inl _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (x, 0) hx (zero_mem _))
    · exact hh ε hε (f (x, 0)) (hin (x, 0) hx (zero_mem _)) (by rw [hm]; exact isHalf_smul _ hx')
        (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inr _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1'
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (0, x) (zero_mem _) hx)
    · exact hh ε hε (f (0, x)) (hin (0, x) (zero_mem _) hx) (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
        (by rw [hm]; exact isHalf_smul _ hx')

theorem mem_iff_char {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T ΛS ΛT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' ΛS' ΛT' fun _ => True) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (B : P → P → AF D.host.F) (hB : ∀ x y, B x y = symplO S T (m x).1 (m y).1 + symplO S' T' (m x).2 (m y).2)
    {z : P} (hz : At (evFin D.host.F v) z) : z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1 := by
  constructor
  · intro h γ hγ
    obtain ⟨-, a, b⟩ := (hΛ z).1 h
    obtain ⟨-, a', b'⟩ := (hΛ γ).1 hγ
    rw [hB, AddChar.map_add_eq_mul, char_sympl_eq_one hψ hS hT a a', char_sympl_eq_one hψ hS' hT' b b', one_mul]
  · intro h
    have hm : ∀ x, m (liftV v (1 : Fv D.host.F v) • m.symm x) = liftV v (1 : Fv D.host.F v) • x := fun x => by
      rw [map_smul, m.apply_symm_apply]
    have hz' : liftV v (1 : Fv D.host.F v) • m z = m z := by rw [← map_smul, smul_eq_of_at hz]
    have hz1 : liftV v (1 : Fv D.host.F v) • (m z).1 = (m z).1 := congrArg Prod.fst hz'
    have hz2 : liftV v (1 : Fv D.host.F v) • (m z).2 = (m z).2 := congrArg Prod.snd hz'
    have key : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T ΛS ΛT (fun _ => True) →
        x.2 ∈ latO S' T' ΛS' ΛT' (fun _ => True) → ψ (symplO S T (m z).1 x.1 + symplO S' T' (m z).2 x.2) = 1 := fun x h1 h2 => by
      have := h _ ((hΛ (liftV v (1 : Fv D.host.F v) • m.symm x)).2
        ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩)
      rwa [hB, hm, Prod.smul_fst, Prod.smul_snd, symplO_swap, symplO_swap, hz1, hz2] at this
    refine (hΛ z).2 ⟨hz, mem_of_char hψ hS hT ?_ fun x hx => ?_, mem_of_char hψ hS' hT' ?_ fun x hx => ?_⟩
    · rw [← hz1]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S' T' (m z).2 0 = 0 := (symplHom S' T' (m z).2).map_zero
      have := key (x, 0) hx (zero_mem _)
      rwa [h0, add_zero] at this
    · rw [← hz2]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S T (m z).1 0 = 0 := (symplHom S T (m z).1).map_zero
      have := key (0, x) (zero_mem _) hx
      rwa [h0, zero_add] at this

end Pair

theorem latPt_le_closure_and_selfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ v : Pl D.host.F, latPt e v ≤ AddSubgroup.closure (genPt e v) ∧
      ∀ z : Pt G i j, At (evFin D.host.F v) z → (z ∈ latPt e v ↔ ∀ γ ∈ latPt e v, W.ψ (sympPt Γ z γ) = 1) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v
  have a := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨le_of_gen (maps e) v _ (fun _ => Iff.rfl) _ (fun u hu => AddSubgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩))
    fun ε hε u hu h1 h2 => AddSubgroup.subset_closure (Or.inr ⟨hu, ε, hε, h1, h2⟩), fun z hz => ?_⟩
  exact mem_iff_char (maps e) v _ (isSelfDualC_neg a) (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd a (fun _ => Iff.rfl) W.ψ_std (sympPt Γ) (symp_eq e Γ hW hWW) hz

end GlobalTheory.BigDatLat

end
