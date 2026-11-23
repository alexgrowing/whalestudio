import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.PushforwardCohomologyAffineStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.LogResVanish

theorem isSeparated_of_isProjOver {k : Type} [Field k] {Z : Scheme.{0}} {f : Z ⟶ Sp k}
    (h : IsProjOver f) : Z.IsSeparated := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str k N) := by unfold PSpace.str; infer_instance
  exact ⟨by rw [← terminal.comp_from (i ≫ PSpace.str k N)]; infer_instance⟩

end GlobalTheory.LogResVanish

open GlobalTheory.LogResVanish in

theorem GlobalTheory.vanishing_logRes_pushforward_and_local : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → (∀ i, 0 < i → Subsingleton (coh (twist ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB (-F)))) N) i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn (twist (twist (GlobalTheory.structureModule Y) (toLB (-F))) (N.pull s)) (s ⁻¹ᵁ U) j) := by
  intro k _ _ X _ p n hp η m G Y _ _ s _ K B F hη hm hres hF N M T hN hM r hT hr hcl hMnef a Fd A hA hAF
  letI := algebraΓOfHom p
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  have hHl : H.IsLB := hH.isLB
  have : CompactSpace X := hH.compactSpace
  have : CompactSpace Y := hA.compactSpace
  have : X.IsSeparated := isSeparated_of_isProjOver hp
  have : Y.IsSeparated := isSeparated_of_isProjOver hres.proj
  have hA0 : (toLB (-F)).IsLB := isLB_toLB _

  have key : ∀ (N' T' : LB X) (hN' : N'.IsLB) (hT' : IsNef k T'),
      cls T' hT'.isLB = (m * r) • cls N' hN' - r • toPic G - m • cls M hM →
      ∀ i, 0 < i → Subsingleton (coh (twist (twist (GlobalTheory.structureModule Y) (toLB (-F))) (N'.pull s)) i) := by
    intro N' T' hN' hT' e i hi
    obtain ⟨Q, hQ, eQ⟩ := cls_surj (CechPic.pull s (cls N' hN') - toPic F)
    have h := GlobalTheory.T.multiplier_vanishing_nef_twist k X p n hp η m G Y s K B F hη hm hres hF N' M T' hN' hM r hT' hr e hMnef
      a Fd A hA hAF Q hQ eQ i hi
    obtain ⟨iso⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule Y) hA0 (pull_isLB hN' s) hQ
      (by rw [eQ, cls_pull hN' s, ← toPic_apply, map_neg]; abel)
    exact (cohOn.mapIso Γ(Y, ⊤) ⊤ i iso).toEquiv.subsingleton_congr.2 h
  have hev : ∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist (twist (twist
      (GlobalTheory.structureModule Y) (toLB (-F))) (N.pull s)) (lbPow (H.pull s) c)) j) := by
    intro j hj
    refine Eventually.of_forall fun c => ?_
    have hNc : (tens N (lbPow H c)).IsLB := isLB_tens hN (isLB_lbPow hHl c)
    have hTc : IsNef k (tens T (lbPow H (m * r * c))) :=
      hT.tens ((IsAmpleLB.isNef (k := k) hH).pow hH _) hH
    have ec : cls _ hTc.isLB = (m * r) • cls _ hNc - r • toPic G - m • cls M hM := by
      rw [cls_tens hT.isLB (isLB_lbPow hHl _), cls_tens hN (isLB_lbPow hHl c), cls_lbPow hHl,
        cls_lbPow hHl, hcl, smul_add, smul_smul]
      abel
    obtain ⟨iso⟩ := nonempty_twist_twist_iso_of_cls_eq
      (twist (GlobalTheory.structureModule Y) (toLB (-F))) (pull_isLB hN s)
      (isLB_lbPow (pull_isLB hHl s) c) (pull_isLB hNc s)
      (by rw [cls_pull hNc s, cls_tens hN (isLB_lbPow hHl c), cls_lbPow hHl, cls_pull hN s,
        cls_lbPow (pull_isLB hHl s), cls_pull hHl s, map_add, map_nsmul])
    exact (cohOn.mapIso Γ(Y, ⊤) ⊤ j iso).toEquiv.subsingleton_congr.2 (key _ _ hNc hTc ec j hj)
  have : (GlobalTheory.structureModule Y).IsQuasicoherent := inferInstance
  have := Twist.isQuasicoherent_twist (F := GlobalTheory.structureModule Y) hA0
  have := Twist.isQuasicoherent_twist (F := twist (GlobalTheory.structureModule Y) (toLB (-F))) (pull_isLB hN s)
  have hdown := GlobalTheory.T.pushforward_cohomology_affine X Y s _ H hH hev
  refine ⟨fun i hi => ?_, hdown.2⟩
  obtain ⟨e⟩ := hdown.1 i
  have h0 := key N T hN hT hcl i hi
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ i (Twist.projIso N s _).symm).toEquiv.subsingleton_congr.2
    (e.toEquiv.subsingleton_congr.2 h0)
