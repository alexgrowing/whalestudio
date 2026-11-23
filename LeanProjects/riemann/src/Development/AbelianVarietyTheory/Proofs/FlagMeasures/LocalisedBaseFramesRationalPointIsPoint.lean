import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualVectorsLocalHermitianFrame
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocalBlockEntries

open Formalism.L2.SG.Pf.AtPt

theorem ptEntryL_eq' {S : Type} [CommRing S] (L : List (Sˣ × ℕ+)) : ∀ i j : ℕ,
    Formalism.MainNotions.S.Loc.ptEntryL L i j = ptEntry (L.map fun b => ((b.1 : S), (b.2 : ℕ))) i j := by
  induction L with
  | nil => intro i j; rfl
  | cons b L ih =>
    intro i j
    obtain ⟨t, s⟩ := b
    simp only [Formalism.MainNotions.S.Loc.ptEntryL, List.map_cons, ptEntry]
    split_ifs <;> first | rfl | exact ih _ _

theorem modBlocks_map' {A S : Type} [CommRing S] (f : ℕ → ℕ → A → S) :
    ∀ (l : List (A × ℕ)) (a : ℕ) (L : List (Sˣ × ℕ+)),
    modBlocks f a l = some L → L.map (fun b => ((b.1 : S), (b.2 : ℕ))) = mapBlocks f a l
  | [], a, L, h => by
    simp only [modBlocks, Option.some.injEq] at h
    subst h; rfl
  | (t, s) :: l, a, L, h => by
    simp only [modBlocks] at h
    split_ifs at h with hu
    obtain ⟨L1, hL1, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [List.map_cons, mapBlocks, modBlocks_map' f l (a + s) L1 hL1]
    rfl

theorem mapBlocks_snd' {A B : Type} (f : ℕ → ℕ → A → B) : ∀ (l : List (A × ℕ)) (a : ℕ),
    (mapBlocks f a l).map Prod.snd = l.map Prod.snd
  | [], _ => rfl
  | (t, s) :: l, a => by simp [mapBlocks, mapBlocks_snd' f l (a + s)]

theorem modBlocks_some {A S : Type} [CommRing S] (f : ℕ → ℕ → A → S) :
    ∀ (l : List (A × ℕ)) (a : ℕ), (∀ b ∈ l, 0 < b.2) → (∀ b ∈ l, ∀ a' s, IsUnit (f a' s b.1)) →
      ∃ L, modBlocks f a l = some L
  | [], a, _, _ => ⟨[], rfl⟩
  | (t, s) :: l, a, h1, h2 => by
    obtain ⟨L1, hL1⟩ := modBlocks_some f l (a + s) (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
      (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
    have hu : IsUnit (f a s t) ∧ 0 < s := ⟨h2 (t, s) List.mem_cons_self a s, h1 (t, s) List.mem_cons_self⟩
    rw [modBlocks, dif_pos hu, hL1]
    exact ⟨_, rfl⟩

end GlobalTheory.LocalBlockEntries

end

open Formalism.L2.SG.Pf.AtPt in
theorem GlobalTheory.LocOver.isPoint_of_scaled : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS), ZhatOM (ZhatL F F') = ptMat w → P.A.f = scaled Z p (frame F) → P.B.f = scaled Z p (frame F') → P.IsPoint := by
  intro D Z p T T' F F' w P hZ hA hB
  let fB : ℕ → ℕ → D.host.E → (D.s.atP p).Ep := fun a s t =>
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((yP Z p)⁻¹ ^ nu D.R.rS a (a + s - 1)) * (D.s.atP p).ιE t
  have hunit : ∀ b ∈ w.1, ∀ a' s, IsUnit (fB a' s b.1) := fun b hb a' s =>
    (Formalism.L2.SG.Pf.BBTie.bt_alg_unit p (pow_ne_zero _ (inv_ne_zero (yP_ne Z p)))).mul
      (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p (w.2.1 b hb).1)
  obtain ⟨L, hL⟩ := GlobalTheory.LocalBlockEntries.modBlocks_some fB w.1 1 (fun b hb => (w.2.1 b hb).2) hunit
  have hLm := GlobalTheory.LocalBlockEntries.modBlocks_map' fB w.1 1 L hL
  have hsize : (L.map (fun b => (b.2 : ℕ))).sum = D.R.rS + 1 := by
    have := congrArg (List.map Prod.snd) hLm
    rw [List.map_map, GlobalTheory.LocalBlockEntries.mapBlocks_snd'] at this
    rw [← w.2.2, ← this]; rfl
  refine ⟨⟨L, hsize⟩, fun a b => ?_⟩
  have hR : (⟨L, hsize⟩ : Formalism.MainNotions.S.Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)).mat a b =
      if b = sgF w a then fB (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val) else 0 := by
    simp only [Formalism.MainNotions.S.Loc.Pt.mat]
    rw [GlobalTheory.LocalBlockEntries.ptEntryL_eq', hLm, ptEntry_eq, pSig_map, pTau_map _ _ _ _ (by rw [w.2.2]; exact a.2)]
    simp only [sgF, Fin.ext_iff]
  rw [hR]
  have hZab := congrFun (congrFun hZ a) b
  rw [zhatOM_eq, ptMat_apply'] at hZab
  simp only [Sg, Matrix.mul_diagonal] at hZab
  have hL1 : (locH Z p).Zhat P.A.f P.B.f a b =
      frFac Z.δ p b * (D.s.atP p).cj (frFac Z.δ p a) * (D.s.atP p).ιE (ZhatL F F' a b) := by
    simp only [Formalism.MainNotions.S.Loc.HermSp.Zhat, Matrix.of_apply, locH, locHerm, hA, hB, GlobalTheory.LocOver.scaled]
    rw [Formalism.L2.SG.Pf.BBTie.formP_bc, Z.hcj p]
    rfl
  rw [hL1, frFac_eq, frFac_eq, cj_alg]
  have key : ∀ (X Y : (D.s.atP p).Ep) (z : D.host.E), (-1 : (D.s.atP p).Ep) ^ (D.R.rS - b.val) * (X * Y * (D.s.atP p).ιE z) =
      X * Y * (D.s.atP p).ιE (z * (-1) ^ (D.R.rS - b.val)) := by
    intro X Y z; rw [map_mul, map_pow, map_neg, map_one]; ring
  rw [key, hZab]
  split_ifs with hb
  · subst hb
    simp only [fB]
    rw [nu_eq, pow_add, map_mul]
    ring
  · rw [map_zero, mul_zero]
