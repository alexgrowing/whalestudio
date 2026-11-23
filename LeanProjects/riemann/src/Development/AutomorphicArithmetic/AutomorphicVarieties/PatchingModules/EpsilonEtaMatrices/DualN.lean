import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.TwistedCocycleApplyOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.ExistsNcardAnnihilatedCocyclesLeCoboundariesMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.CCount

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Pa.dualN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), l ≠ 2 → PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → Detects k (Set.range T.sg) → ∃ C : ℕ, ∀ m, ∀ᶠ N in atTop, ∀ rep' : Representation x.A (T.GN N).Γ (k.EpsilonEtaTensorDual (x.Am m)), IsAd (T.GN N).frame (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun g => epsD k (x.Am m) ((T.h N).p g)) (k.EpsilonEtaTensorDual (x.Am m)) rep' → Finite (Zl rep') → {y | y ∈ Zl rep' ∧ ∀ j, ∃ Y, y (T.ph N j) = rep' (T.ph N j) Y - Y ∧ y (T.ta N j) = rep' (T.ta N j) Y - Y}.ncard ≤ Nat.card (Bl rep') * Nat.card x.K ^ C := by
  intro l _ L G0 T n x k hl hphi hρ hdet
  obtain ⟨C, hC⟩ := exists_ncard_annihilated_cocycles_le_coboundaries_mul l L G0 n x k T.q T.sg hphi T.sg_mem hdet
  refine ⟨C, fun m => ?_⟩
  filter_upwards [phEq l L G0 T n x k m hphi hρ] with N hN
  intro rep' hAd hfin
  classical
  have hfinM := finAm l G0.frame n x m k.g
  haveI : Finite (DD (x.Am m) k.g) := hfinM.2.2.1
  haveI : Finite (Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) :=
    inferInstanceAs (Finite (Fin n → Fin n → DD (x.Am m) k.g))
  haveI : Finite ↥(k.EpsilonEtaTensorDual (x.Am m)) :=
    Finite.of_injective (fun Y : ↥(k.EpsilonEtaTensorDual (x.Am m)) => (Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)))
      Subtype.val_injective
  haveI := hfin
  have hrho1 := rho1 l G0.frame n x k (x.Am m)
  have hp0ta : ∀ j, (T.h N).p₀ (T.ta N j) = 1 := fun j =>
    Subtype.ext (by rw [Glob.Hom.coe_p₀, T.ta_ker]; rfl)
  have hta : ∀ j (Y : ↥(k.EpsilonEtaTensorDual (x.Am m))), rep' (T.ta N j) Y = Y := by
    intro j Y
    apply Subtype.ext
    rw [hAd.1]
    simp [map_inv, hp0ta, hrho1.1, T.ta_ker, epsD]
  have hZl : ∀ y, y ∈ Zl rep' ↔ IsLocallyConstant y ∧ ∀ g h, y (g * h) = y g + rep' g (y h) :=
    fun y => Iff.rfl
  let Z : AddSubgroup ((T.GN N).Γ → ↥(k.EpsilonEtaTensorDual (x.Am m))) :=
    { carrier := {y | y ∈ Zl rep' ∧ ∀ j, ∃ Y, y (T.ph N j) = rep' (T.ph N j) Y - Y ∧
        y (T.ta N j) = rep' (T.ta N j) Y - Y}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun j => ?_⟩
        obtain ⟨Y1, h1, h2⟩ := ha' j
        obtain ⟨Y2, h3, h4⟩ := hb' j
        refine ⟨Y1 + Y2, ?_, ?_⟩ <;> simp only [Pi.add_apply, h1, h2, h3, h4, map_add] <;> abel
      zero_mem' := ⟨zero_mem _, fun j => ⟨0, by simp, by simp⟩⟩
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨neg_mem ha, fun j => ?_⟩
        obtain ⟨Y, h1, h2⟩ := ha' j
        refine ⟨-Y, ?_, ?_⟩ <;> simp only [Pi.neg_apply, h1, h2, map_neg] <;> abel }
  haveI hZfin : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : Zl rep'))
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have hZlf : (Zl rep' : Set ((T.GN N).Γ → ↥(k.EpsilonEtaTensorDual (x.Am m)))).Finite := Set.toFinite _
  have hLC := lc1 l L (T.GN N) G0 (T.h N) n x k m
  have hLCr := hLC.2.2 _ _ rep' hLC.2.1 hAd
  have hBlZ : (Bl rep').toAddSubgroup ≤ Z := by
    intro y hy
    obtain ⟨Y, hY⟩ := (mem_Bl rep').1 hy
    refine ⟨(hZl y).2 ⟨?_, ?_⟩, fun j => ⟨Y, hY _, hY _⟩⟩
    · have hy' : y = fun g => rep' g Y - Y := funext hY
      rw [hy']
      exact (hLCr Y).sub (IsLocallyConstant.const _)
    · intro g h
      rw [hY, hY, hY, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hcoc : ∀ z ∈ Z, ∀ g h, z (g * h) = z g + rep' g (z h) := fun z hz => ((hZl z).1 hz.1).2
  obtain ⟨hA, hB, hCc⟩ := cCount x.A (T.GN N).Γ ↥(k.EpsilonEtaTensorDual (x.Am m)) rep' (T.GN N).c (T.GN N).c_sq
    (hfinM.2.2.2.2.2.2.2.1 hl)
  have hA' := hA Z hZfin hBlZ hcoc
  let s := Function.surjInv (T.h N).p₀_surj
  have hs : ∀ g0, (T.h N).p₀ (s g0) = g0 := Function.surjInv_eq _
  let Ψ : ((T.GN N).Γ → ↥(k.EpsilonEtaTensorDual (x.Am m))) → (G0.frame.G₀ → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) :=
    fun y g0 => ((y (s g0 : (T.GN N).Γ)) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))
  have hdesc : ∀ y ∈ Z, y (T.GN N).c = 0 → Ψ y ∈ TwZ k (x.Am m) ∧
      ∀ g : (T.GN N).G₀, ((y g : ↥(k.EpsilonEtaTensorDual (x.Am m))) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
        Ψ y ((T.h N).p₀ g) := by
    intro y hy hc
    obtain ⟨z, hz, hyz⟩ := descend l L G0 T n x k m N rep' hρ hAd y hy.1 hc (fun j => by
      obtain ⟨Y, -, h2⟩ := hy.2 j
      rw [h2, hta, sub_self])
    have hΨ : Ψ y = z := funext fun g0 => by
      simp only [Ψ]
      rw [hyz, hs]
    rw [hΨ]
    exact ⟨hz, hyz⟩
  have hmaps : ∀ y ∈ {z | z ∈ Z ∧ z (T.GN N).c = 0},
      Ψ y ∈ {z | z ∈ TwZ k (x.Am m) ∧ ∀ j, ell k (x.Am m) (T.sg j) z = 0} := by
    rintro y ⟨hy, hc⟩
    obtain ⟨hz, hyz⟩ := hdesc y hy hc
    refine ⟨hz, fun j => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hN j
    obtain ⟨Y, hY, -⟩ := hy.2 j
    have hval : Ψ y (T.sg j) = k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)) * (Y : Matrix (Fin n) (Fin n) _) *
        k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)⁻¹) - (Y : Matrix (Fin n) (Fin n) _) := by
      rw [← h3 _ hz, ← hyz, hY, Submodule.coe_sub, hAd.1]
      simp only [h2, one_smul]
    have hinv : k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)⁻¹) * k.ρ1 (x.Am m) (T.sg j) = 1 := by
      rw [← h1, ← hrho1.2.1, map_inv, inv_mul_cancel, hrho1.1]
    have key : (Ψ y (T.sg j) * k.ρ1 (x.Am m) (T.sg j)).trace = 0 := by
      rw [hval, Matrix.sub_mul, Matrix.mul_assoc (k.ρ1 (x.Am m) ((T.h N).p₀ (T.ph N j)) * _), hinv,
        Matrix.mul_one, ← h1, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    show (Ψ y (T.sg j) * k.ρ1 (x.Am m) (T.sg j)).trace.eta = 0
    rw [key]
    rfl
  have hinj : Set.InjOn Ψ {z | z ∈ Z ∧ z (T.GN N).c = 0} := by
    rintro y1 ⟨hy1, hc1⟩ y2 ⟨hy2, hc2⟩ heq
    obtain ⟨-, e1⟩ := hdesc y1 hy1 hc1
    obtain ⟨-, e2⟩ := hdesc y2 hy2 hc2
    have hpol := (polZ l (T.GN N).frame x.A (DD (x.Am m) k.g) n _ _ _ rep' hAd).2 (y1 - y2)
      (sub_mem hy1.1 hy2.1) (by
        show y1 (T.GN N).c - y2 (T.GN N).c = 0
        rw [hc1, hc2, sub_self])
    exact sub_eq_zero.1 (hpol.2 fun g => by
      rw [Pi.sub_apply, sub_eq_zero]
      exact Subtype.ext (by rw [e1, e2, heq]))
  have hSmf : {z | z ∈ TwZ k (x.Am m) ∧ ∀ j, ell k (x.Am m) (T.sg j) z = 0}.Finite :=
    (finTw l L G0 n x k m hphi).subset fun z hz => hz.1
  have hBcf : {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.Finite :=
    hZlf.subset fun z hz => (hBlZ ((Submodule.mem_toAddSubgroup _).2 hz.1)).1
  have h1 := Set.ncard_le_ncard_of_injOn Ψ hmaps hinj hSmf
  have h2 := hC m
  have h3 : (TwB k (x.Am m)).ncard ≤ {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard := by
    have hsub : TwB k (x.Am m) ⊆ Ψ '' {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0} := by
      rintro z ⟨Y, hYm, hYc, rfl⟩
      let Y' : ↥(k.EpsilonEtaTensorDual (x.Am m)) := ⟨Y, hYm⟩
      have hrepc : rep' (T.GN N).c Y' = Y' := Subtype.ext ((hAd.2 Y').trans (by
        show -(epsD k (x.Am m) ((T.h N).p (T.GN N).c) • Yᵀ) = Y
        rw [Glob.Hom.c]
        exact hYc))
      refine ⟨fun g => rep' g Y' - Y', ⟨(mem_Bl rep').2 ⟨Y', fun g => rfl⟩, by simp only [hrepc, sub_self]⟩, ?_⟩
      funext g0
      simp only [Ψ]
      rw [Submodule.coe_sub, hAd.1]
      simp only [map_inv, ← Glob.Hom.coe_p₀, hs]
      rfl
    calc (TwB k (x.Am m)).ncard ≤ (Ψ '' {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}).ncard :=
          Set.ncard_le_ncard hsub (hBcf.image _)
      _ ≤ _ := Set.ncard_image_le hBcf
  have hzc := h1.trans (h2.trans (Nat.mul_le_mul_right _ h3))
  have hi : 0 < Nat.card rep'.invariants := Nat.card_pos
  have hbc : 0 < {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard :=
    (Set.ncard_pos hBcf).2 ⟨0, Submodule.zero_mem _, rfl⟩
  have e : Nat.card Z * {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard =
      {z | z ∈ Z ∧ z (T.GN N).c = 0}.ncard * Nat.card (Bl rep') := by
    apply Nat.eq_of_mul_eq_mul_right hi
    rw [mul_assoc, hCc, hA', ← hB, mul_assoc]
  have hle : Nat.card Z * {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard ≤
      Nat.card (Bl rep') * Nat.card x.K ^ C * {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard := by
    rw [e]
    calc _ ≤ {z | z ∈ Bl rep' ∧ z (T.GN N).c = 0}.ncard * Nat.card x.K ^ C * Nat.card (Bl rep') :=
          Nat.mul_le_mul_right _ hzc
      _ = _ := by ring
  rw [← Nat.card_coe_set_eq]
  exact Nat.le_of_mul_le_mul_right hle hbc
