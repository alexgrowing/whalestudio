import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GrowthWeightBounds.WeightExtensions.WeightExtensionExistence.WeightExD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveInvTranspose
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.GlobFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B
open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.FrE PositivityTheory.Rg.BcB.F.FrE.FrameLocalData

namespace GlobalTheory.CompanionTheory.LFixDPf

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

open PositivityTheory.Rg.BcB.F.F5.Bo PositivityTheory.Rg.BcB.F.F5.Bo.GlobalFixedVectorsAlt in

theorem exists_fixAll_cusp (π : CuspSub E n) (Kf : ∀ w : Pl E, Subgroup (GLw n w))
    (hc : ∀ w, IsCompact (Kf w : Set (GLw n w)))
    (hv : ∀ w, ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep w) (Kf w)) (S : Finset (Pl E)) :
    ∀ ψ : π.V, ψ ≠ 0 → (∀ u ∉ S, FixAt Kf u ψ.1) → ∃ χ : π.V, χ ≠ 0 ∧ ∀ u, FixAt Kf u χ.1 := by
  induction S using Finset.induction_on with
  | empty => exact fun ψ h0 hF => ⟨ψ, h0, fun u => hF u (Finset.notMem_empty u)⟩
  | insert w S hwS ih =>
    intro ψ h0 hF
    let Y : Submodule ℂ π.V :=
      { carrier := {χ | ∀ u ∉ insert w S, FixAt Kf u χ.1}
        add_mem' := fun {a b} ha hb u hu k hk => by
          show finRep E n _ (a.1 + b.1) = a.1 + b.1
          rw [map_add, ha u hu k hk, hb u hu k hk]
        zero_mem' := fun u _ k _ => map_zero _
        smul_mem' := fun c a ha u hu k hk => by
          show finRep E n _ (c • a.1) = c • a.1
          rw [map_smul, ha u hu k hk] }
    have hY : ∀ g, ∀ y ∈ Y, π.locRep w g y ∈ Y := fun g y hy u hu =>
      fixAt_locGL (fun e => hu (by rw [e]; exact Finset.mem_insert_self w S)) (hy u hu) g
    obtain ⟨φ, hφ0, hφ⟩ := hv w
    have hne : Y ⊓ fixed (π.locRep w) (Kf w) ≠ ⊥ := fun h => h0 (by
      have h1 := GlobalTheory.CuspRep.LocEx.eq_bot_of_fixed π w (hc w) hφ0 hφ Y hY h
      have h2 : ψ ∈ Y := hF
      rw [h1] at h2
      exact (Submodule.mem_bot ℂ).1 h2)
    obtain ⟨y, ⟨hy1, hy2⟩, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
    refine ih y hy0 fun u hu => ?_
    by_cases e : u = w
    · subst e
      exact fun k hk => congrArg Subtype.val (GlobalTheory.CuspRep.LocEx.mem_fix.1 hy2 k hk)
    · exact hy1 u (by simp [e, hu])

open PositivityTheory.Rg.BcB.F.F5.Bo PositivityTheory.Rg.BcB.F.F5.Bo.GlobalFixedVectorsAlt in

theorem exists_global_fix (π : CuspSub E n) (Kf : ∀ w : Pl E, Subgroup (GLw n w))
    (hc : ∀ w, IsCompact (Kf w : Set (GLw n w)))
    (hv : ∀ w, ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep w) (Kf w))
    (hcof : ∀ᶠ w in Filter.cofinite, Kf w = GlobalTheory.LFun.KGL w n) :
    ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ v ∈ globL Kf, finRep E n v ψ = ψ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hev : ∀ᶠ w in Filter.cofinite, FixAt Kf w φ := by
    filter_upwards [hcof, GlobalTheory.CuspRep.LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w h1 h2
    intro k hk
    rw [h1] at hk
    obtain ⟨g, rfl⟩ := hk
    exact h2 g
  have hfin := Filter.eventually_cofinite.1 hev
  obtain ⟨χ, hχ0, hχ⟩ := exists_fixAll_cusp π Kf hc hv hfin.toFinset ⟨φ, hφ⟩
    (fun e => h0 (congrArg Subtype.val e)) fun u hu => by simpa using hu
  exact ⟨χ.1, χ.2, fun e => hχ0 (Subtype.ext e), fix_of_fixAll hcof (π.cusp χ.1 χ.2).1 hχ⟩

section Conj

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

def thAt (n : ℕ) (w u : Pl E) : GLw n w →* GLw n u :=
  (GeneralLinearGroup.map (pLoc E u)).comp ((thF E n).comp (locGL E n w))

theorem map_pLoc_thF (u : Pl E) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n k) = PhiU n _ * invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u)
      (GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) k)) * (PhiU n _)⁻¹ :=
  map_thetaGL (pLoc E u) _ (pLoc E _) (conjLoc (conjE E) u) (fun _ => rfl) k

theorem thAt_apply (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    thAt n (conjSrc (conjE E) u) u g =
      PhiU n _ * invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u) g) * (PhiU n _)⁻¹ := by
  show GeneralLinearGroup.map (pLoc E u) (thF E n (locGL E n _ g)) = _
  rw [map_pLoc_thF, pLoc_locGL]

theorem map_pLoc_thF_eq (u : Pl E) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n k) =
      thAt n (conjSrc (conjE E) u) u (GeneralLinearGroup.map (pLoc E _) k) := by
  rw [thAt_apply, map_pLoc_thF]

theorem exists_fixed_conj (π : CuspSub E n) (hd : GlobalTheory.ContraPair.DualIsConj π) {u : Pl E} {τ : SmIrr (GLw n u)}
    (hτ : π.IsLocComp u τ) (M : Subgroup (GLw n u)) {y : τ.V} (hy : y ∈ fixed τ.ρ M) (h0 : y ≠ 0) :
    ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep (conjSrc (conjE E) u)) (M.comap (thAt n (conjSrc (conjE E) u) u)) := by
  obtain ⟨f, hf0, hf⟩ := isLocComp_conjDual π hd hτ
  have hi := GlobalTheory.BcSpehCompare.injective_of_irred (conjDual τ).irred (τ := fun g => π.locRep _ g)
    (fun _ => map_zero _) hf0 hf
  set P : GLw n u := PhiU n _ with hP
  have hy' : τ.ρ P⁻¹ y ≠ 0 := fun e => h0 (by
    have h1 : τ.ρ P (τ.ρ P⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, e, map_zero])
  refine ⟨f (τ.ρ P⁻¹ y), (map_ne_zero_iff f hi).2 hy', GlobalTheory.CuspRep.LocEx.mem_fix.2 fun g hg => ?_⟩
  refine (hf g (τ.ρ P⁻¹ y)).symm.trans (congrArg f ?_)
  have h2 := GlobalTheory.CuspRep.LocEx.mem_fix.1 hy _ (Subgroup.mem_comap.1 hg)
  rw [thAt_apply] at h2
  have e : (conjDual τ).ρ g = τ.ρ (invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u) g)) := rfl
  show (conjDual τ).ρ g (τ.ρ P⁻¹ y) = τ.ρ P⁻¹ y
  rw [e]
  generalize invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u) g) = j at h2
  have key : j * P⁻¹ = P⁻¹ * (P * j * P⁻¹) := by group
  calc τ.ρ j (τ.ρ P⁻¹ y) = τ.ρ (j * P⁻¹) y := by rw [map_mul]; rfl
    _ = τ.ρ (P⁻¹ * (P * j * P⁻¹)) y := by rw [key]
    _ = τ.ρ P⁻¹ (τ.ρ (P * j * P⁻¹) y) := by rw [map_mul]; rfl
    _ = τ.ρ P⁻¹ y := by rw [h2]

end Conj

section Int

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

theorem mem_KGL_map_conj (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    GeneralLinearGroup.map (conjLoc (conjE E) u) g ∈ GlobalTheory.LFun.KGL u n ↔ g ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) n := by
  have hv : ∀ x : (conjSrc (conjE E) u).adicCompletion E,
      conjLoc (conjE E) u x ∈ u.adicCompletionIntegers E ↔ x ∈ (conjSrc (conjE E) u).adicCompletionIntegers E := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec (conjE E) u).2.2 x]
  rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
  refine and_congr (forall₂_congr fun a b => hv _) (forall₂_congr fun a b => ?_)
  rw [← map_inv]
  exact hv _

theorem mem_KGL_invT (u : Pl E) (x : GLw n u) : invT n _ x ∈ GlobalTheory.LFun.KGL u n ↔ x ∈ GlobalTheory.LFun.KGL u n := by
  rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
  have e1 : ∀ a b, (invT n _ x).val a b = (x⁻¹).val b a := fun _ _ => rfl
  have e2 : ∀ a b, ((invT n _ x)⁻¹).val a b = x.val b a := fun _ _ => rfl
  simp only [e1, e2]
  exact ⟨fun h => ⟨fun a b => h.2 b a, fun a b => h.1 b a⟩, fun h => ⟨fun a b => h.2 b a, fun a b => h.1 b a⟩⟩

end Int

section Int2

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws

theorem phiU_mem_KGL (u : Pl E) : PhiU n (u.adicCompletion E) ∈ GlobalTheory.LFun.KGL u n := by
  let p : u.adicCompletionIntegers E →+* u.adicCompletion E := (u.adicCompletionIntegers E).subtype
  have e : GeneralLinearGroup.map p (PhiU n (u.adicCompletionIntegers E)) = PhiU n (u.adicCompletion E) :=
    Units.ext (Matrix.ext fun i k => by
      change p (GlobalTheory.Tw.Phi n _ i k) = GlobalTheory.Tw.Phi n _ i k
      simp [GlobalTheory.Tw.Phi, apply_ite p])
  rw [GlobalTheory.AdelicU.mem_GLint_iff, ← e]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · exact ((PhiU n (u.adicCompletionIntegers E)).val a b).2
  · rw [← map_inv]
    exact (((PhiU n (u.adicCompletionIntegers E))⁻¹).val a b).2

theorem mem_KGL_thAt (u : Pl E) (g : GLw n (conjSrc (conjE E) u)) :
    thAt n (conjSrc (conjE E) u) u g ∈ GlobalTheory.LFun.KGL u n ↔ g ∈ GlobalTheory.LFun.KGL (conjSrc (conjE E) u) n := by
  have hP := phiU_mem_KGL (n := n) u
  rw [thAt_apply, Subgroup.mul_mem_cancel_right _ (inv_mem hP), Subgroup.mul_mem_cancel_left _ hP, mem_KGL_invT,
    mem_KGL_map_conj]

theorem continuous_thAt (u : Pl E) : Continuous (thAt n (conjSrc (conjE E) u) u) := by
  have e : (thAt n (conjSrc (conjE E) u) u : _ → _) = fun g =>
      PhiU n _ * invT n _ (GeneralLinearGroup.map (conjLoc (conjE E) u) g) * (PhiU n _)⁻¹ := funext (thAt_apply u)
  rw [e]
  have h1 : Continuous (invT n (u.adicCompletion E)) := GlobalTheory.GelfandKazhdan.continuous_invTranspose n _
  exact (continuous_const.mul (h1.comp (continuous_sLoc u))).mul continuous_const

theorem isCompact_comap_thAt (u : Pl E) (M : Subgroup (GLw n u)) (hM : IsCompact (M : Set (GLw n u)))
    (hK : M ≤ GlobalTheory.LFun.KGL u n) :
    IsCompact ((M.comap (thAt n (conjSrc (conjE E) u) u) : Subgroup _) : Set (GLw n (conjSrc (conjE E) u))) :=
  GlobalTheory.BcSpehCompare.isCompact_KGL.of_isClosed_subset (hM.isClosed.preimage (continuous_thAt u))
    fun g hg => (mem_KGL_thAt u g).1 (hK hg)

theorem blk_self (w : Pl E) (x : GLw n w) (z : GLw (n - n) w) (h : n + (n - n) = n) : blk h w (x, z) 0 = x := by
  have he : ∀ i : Fin n, (finSumFinEquiv.trans (finCongr h)).symm i = Sum.inl i := fun i =>
    (Equiv.symm_apply_eq _).2 (Fin.ext (by simp))
  have hM : ∀ X : Matrix (Fin n) (Fin (n - n)) (w.adicCompletion E),
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks x.val (x.val * X) 0 z.val) = x.val := fun X => by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, he, he]
    rfl
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks x.val (x.val * (0 : Matrix (Fin n) (Fin (n - n)) (w.adicCompletion E))) 0 z.val)) := by
    rw [hM]; exact x.isUnit
  exact (dif_pos hU).trans (Units.ext (hM 0))

end Int2

section Main

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

def Mlev (d : LocData E n) (w : Pl E) : Subgroup (GLw n w) :=
  if w ∈ d.S₀ then d.K' w else GlobalTheory.LFun.KGL w n

def Kfam (Sec : Set (Pl E)) (d : LocData E n) (w : Pl E) : Subgroup (GLw n w) :=
  if w ∈ Sec then Mlev d w else (Mlev d (conjSrc (conjE E) w)).comap (thAt n w (conjSrc (conjE E) w))

theorem Kfam_of_mem {Sec : Set (Pl E)} (d : LocData E n) {w : Pl E} (hw : w ∈ Sec) : Kfam Sec d w = Mlev d w := if_pos hw

theorem Kfam_of_notMem {Sec : Set (Pl E)} (d : LocData E n) {w u : Pl E} (hw : w ∉ Sec) (h : conjSrc (conjE E) w = u) :
    Kfam Sec d w = (Mlev d u).comap (thAt n w u) := by
  subst h
  exact if_neg hw

theorem exists_conj_of_notMem {Sec : Set (Pl E)} (hSec : IsSection Sec) {w : Pl E} (hw : w ∉ Sec) :
    ∃ u ∈ Sec, IsSplitAt u ∧ w = conjSrc (conjE E) u ∧ conjSrc (conjE E) w = u := by
  obtain ⟨u, ⟨hu, hun⟩, -⟩ := hSec w
  have hne : w ≠ u := fun e => hw (e ▸ hu)
  have hs : IsSplitAt u := ⟨w, hne, hun.symm⟩
  have h1 : w = conjSrc (conjE E) u := ((over_split hs).2.2 w hun.symm).resolve_left hne
  exact ⟨u, hu, hs, h1, by rw [h1, conjSrc_conjSrc_cm]⟩

variable {d : LocData E n}

theorem Mlev_compact (hd : d.Ok) (w : Pl E) : IsCompact (Mlev d w : Set (GLw n w)) ∧ Mlev d w ≤ GlobalTheory.LFun.KGL w n := by
  unfold Mlev
  split_ifs with h
  · obtain ⟨h1, h2, -⟩ := hd.K' w h
    exact ⟨GlobalTheory.BcSpehCompare.isCompact_KGL.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ h1) h2, h2⟩
  · exact ⟨GlobalTheory.BcSpehCompare.isCompact_KGL, le_rfl⟩

theorem fixed_of_comp {π : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : π.IsLocComp w σ) (M : Subgroup (GLw n w))
    {y : σ.V} (hy : y ∈ fixed σ.ρ M) (h0 : y ≠ 0) : ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep w) M := by
  obtain ⟨f, hf0, hf⟩ := h
  have hi := GlobalTheory.BcSpehCompare.injective_of_irred σ.irred (τ := fun g => π.locRep w g) (fun _ => map_zero _) hf0 hf
  refine ⟨f y, (map_ne_zero_iff f hi).2 h0, GlobalTheory.CuspRep.LocEx.mem_fix.2 fun g hg => ?_⟩
  rw [← hf, GlobalTheory.CuspRep.LocEx.mem_fix.1 hy g hg]

theorem Kfam_eq_of_notMem {Sec : Set (Pl E)} (hSec : IsSection Sec) {w : Pl E}
    (h1 : w ∉ d.S₀) (h2 : conjSrc (conjE E) w ∉ d.S₀) : Kfam Sec d w = GlobalTheory.LFun.KGL w n := by
  by_cases hw : w ∈ Sec
  · rw [Kfam_of_mem d hw, Mlev, if_neg h1]
  · obtain ⟨u, -, -, rfl, e⟩ := exists_conj_of_notMem hSec hw
    rw [Kfam_of_notMem d hw e]
    rw [e] at h2
    ext g
    rw [Subgroup.mem_comap, Mlev, if_neg h2]
    exact mem_KGL_thAt u g

theorem lev_mem {w : Pl E} (hd : d.Ok) (T₀ : d.T = ∅) (B₀ : d.Bad = ∅) {x : GLw n w} {z : GLw (n - n) w}
    (h : (x, z) ∈ d.lev n w) : x ∈ Mlev d w := by
  have hT : w ∉ d.T := by simp [T₀]
  rw [LocData.lev, if_neg hT] at h
  unfold Mlev
  by_cases hs : w ∈ d.S₀
  · rw [if_pos (Finset.mem_union_left _ hs)] at h
    have h1 := (hd.LS n le_rfl w hs _ h).1
    rw [if_pos hs]
    have h2 : blk (Nat.add_sub_of_le le_rfl) w (x, z) 0 ∈ d.K' w := h1
    rwa [blk_self] at h2
  · rw [if_neg (by simp [B₀, hs])] at h
    rw [if_neg hs]
    exact h.1

theorem lev₂_mem {w : Pl E} (hd : d.Ok) (B₀ : d.Bad = ∅) {x : GLw n w} {z : GLw (n - n) w}
    (h : (x, z) ∈ d.lev₂ n w) : x ∈ Mlev d w := by
  rw [LocData.lev₂] at h
  unfold Mlev
  by_cases hs : w ∈ d.S₀
  · rw [if_pos (Finset.mem_union_left _ hs)] at h
    have h1 := (hd.LS n le_rfl w hs _ h).1
    rw [if_pos hs]
    have h2 : blk (Nat.add_sub_of_le le_rfl) w (x, z) 0 ∈ d.K' w := h1
    rwa [blk_self] at h2
  · rw [if_neg (by simp [B₀, hs])] at h
    rw [if_neg hs]
    exact h.1

theorem lev₁_le {Sec : Set (Pl E)} (hSec : IsSection Sec) (hd : d.Ok) (T₀ : d.T = ∅) (B₀ : d.Bad = ∅) :
    lev₁ Sec d n ≤ globL (Kfam Sec d) := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  have hg' : (g, 1) ∈ levSet Sec d n := hg
  simp only [SetLike.mem_coe, globL, Subgroup.mem_iInf, Subgroup.mem_comap]
  intro w
  by_cases hw : w ∈ Sec
  · rw [Kfam_of_mem d hw]
    exact lev_mem hd T₀ B₀ (hg' w hw).1
  · obtain ⟨u, hu, hs, rfl, e⟩ := exists_conj_of_notMem hSec hw
    rw [Kfam_of_notMem d hw e, Subgroup.mem_comap, ← map_pLoc_thF_eq]
    exact lev₂_mem hd B₀ ((hg' u hu).2 hs)

end Main

section Core

open GlobalTheory.SplitPts GlobalTheory.CompanionTheory.CompConjPlace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.ConjPairLoc GlobalTheory.CuspRep.ParLaws
open PositivityTheory.Rg.BcB.F.F5.Bo

theorem exists_lev₁_fix (π : CuspSub E n) (hd : GlobalTheory.ContraPair.DualIsConj π) {Sec : Set (Pl E)} {d : LocData E n}
    {τ : ∀ w : Pl E, SmIrr (GLw n w)} (hSec : IsSection Sec) (ok₀ : d.Ok) (T₀ : d.T = ∅) (B₀ : d.Bad = ∅)
    (good : ∀ w ∈ Sec, w ∉ d.S₀ → ∃ B, (CG.mk π).HasSat w B) (hτ : ∀ w, π.IsLocComp w (τ w))
    (τ_fix : ∀ w ∈ d.S₀, ∃ y ∈ fixed (τ w).ρ (d.K' w), y ≠ 0) :
    ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ lev₁ Sec d n, finRep E n k ψ = ψ := by
  have hy : ∀ u ∈ Sec, ∃ y ∈ fixed (τ u).ρ (Mlev d u), y ≠ 0 := by
    intro u hu
    by_cases hs : u ∈ d.S₀
    · rw [Mlev, if_pos hs]
      exact τ_fix u hs
    · obtain ⟨B, hB⟩ := good u hu hs
      rw [Mlev, if_neg hs]
      exact (Submodule.ne_bot_iff _).1 ((GlobalTheory.BcSpehCompare.hasSat_iff (hτ u) B).1 hB).1
  have hc : ∀ w, IsCompact (Kfam Sec d w : Set (GLw n w)) := by
    intro w
    by_cases hw : w ∈ Sec
    · rw [Kfam_of_mem d hw]
      exact (Mlev_compact ok₀ w).1
    · obtain ⟨u, -, -, rfl, e⟩ := exists_conj_of_notMem hSec hw
      rw [Kfam_of_notMem d hw e]
      exact isCompact_comap_thAt u _ (Mlev_compact ok₀ u).1 (Mlev_compact ok₀ u).2
  have hv : ∀ w, ∃ φ : π.V, φ ≠ 0 ∧ φ ∈ fixed (π.locRep w) (Kfam Sec d w) := by
    intro w
    by_cases hw : w ∈ Sec
    · obtain ⟨y, h1, h2⟩ := hy w hw
      rw [Kfam_of_mem d hw]
      exact fixed_of_comp (hτ w) _ h1 h2
    · obtain ⟨u, hu, -, rfl, e⟩ := exists_conj_of_notMem hSec hw
      obtain ⟨y, h1, h2⟩ := hy u hu
      rw [Kfam_of_notMem d hw e]
      exact exists_fixed_conj π hd (hτ u) _ h1 h2
  have hfin : (↑(d.S₀ ∪ d.S₀.image (conjSrc (conjE E))) : Set (Pl E)).Finite := Finset.finite_toSet _
  have hcof : ∀ᶠ w in Filter.cofinite, Kfam Sec d w = GlobalTheory.LFun.KGL w n := by
    filter_upwards [hfin.compl_mem_cofinite] with w hw
    have hw' : w ∉ d.S₀ ∪ d.S₀.image (conjSrc (conjE E)) := fun h => hw (Finset.mem_coe.2 h)
    refine Kfam_eq_of_notMem hSec (fun h => hw' (Finset.mem_union_left _ h)) fun h => hw' (Finset.mem_union_right _ ?_)
    exact Finset.mem_image.2 ⟨_, h, conjSrc_conjSrc_cm w⟩
  obtain ⟨ψ, h1, h2, h3⟩ := exists_global_fix π _ hc hv hcof
  exact ⟨ψ, h1, h2, fun k hk => h3 k (lev₁_le hSec ok₀ T₀ B₀ hk)⟩

end Core

end GlobalTheory.CompanionTheory.LFixDPf

end
