import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftAgrees

open Formalism.IndefR Formalism.L2.DIV

theorem cong_mul {R : Type} [CommRing R] {n : ℕ} (K U : Matrix (Fin n) (Fin n) R) (M : ℕ) (x y w w' : Fin n → R)
    (e : y - K *ᵥ x = M • w) (e' : U *ᵥ x - x = M • w') : y - (K * U) *ᵥ x = M • (w - K *ᵥ w') := by
  rw [smul_sub, ← e, ← Matrix.mulVec_smul, ← e', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

variable {D : D7}

theorem isLift_inv_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g : Formalism.L2.DIV.G0 L.Pg L.r} {κ k : GA D V} (hκ : Lev.IsLevelLift V β L g κ) (hk : Lev.IsLevelLift V β L g k) :
    Lev.IsLevelLift V β L 1 (κ⁻¹ * k) := by
  have h1 : Lev.finE V (κ⁻¹ * k) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    rw [map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ.2.1) hk.2.1
  refine ⟨(GfC V).mul_mem ((GfC V).inv_mem hκ.1) hk.1, h1, ?_⟩
  have h2 := Formalism.L2.DIV.rTup_mul hκ.2.1 h1
  rw [← map_mul, mul_inv_cancel_left, hκ.2.2, hk.2.2] at h2
  exact (mul_eq_left.1 h2.symm)

theorem finCong_one_of_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : Formalism.IndefR.Links.IsSDFrame V β Λ 1) {κ : GA D V}
    (hκ : Lev.finE V κ ∈ St β) : GlobalTheory.Member.FinCong V 1 κ := by
  have hβ : IsFrame β Λ := h.choose_spec.1
  intro z hz
  have h1 := ((GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).1 hκ).1 _ ((GlobalTheory.LiftLevel.latHat_iff_frame h z).1 hz)
  refine ⟨(finHom V κ).1 *ᵥ z - z, sub_mem ?_ hz, (one_smul _ _).symm⟩
  refine (GlobalTheory.LiftLevel.latHat_iff_frame h _).2 ?_
  convert h1 using 1
  funext i
  exact RingHom.map_mulVec (Lev.swapAE D) _ z i

set_option maxHeartbeats 1000000 in

theorem finCong_of_red (P : Formalism.L2.Host.PiBar D.host) {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : Formalism.IndefR.Links.IsSDFrame V β Λ 1) {u : GA D V}
    (h1 : u ∈ GfC V) (h2 : Lev.finE V u ∈ St β)
    (h3 : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (∃ k, P.Div k PP) → redFn β PP (Lev.finE V u) = 1) :
    GlobalTheory.Member.FinCong V (D.host.g 0 * D.host.g 1) u := by
  obtain ⟨l, ⟨hM, -⟩, hMb⟩ := Formalism.L2.Pj.levelPb_exists D P.pb P.pb_over
  obtain ⟨Kf, hK⟩ := (GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D V l.M).1
  have hH := (GlobalTheory.Member.finCong_iff_half_and_kfHalf D _ l V).2 Kf hK
  have hN : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ l.Mb := by
    rw [hMb]; exact GlobalTheory.LiftLevel.natCast_mem_prod _
  have hsq : Squarefree l.Mb := (GlobalTheory.CoverHalf.squarefree_span_g D).squarefree_of_dvd
    (Ideal.dvd_span_singleton.2 hN)
  have hu : u ∈ Kf := (GlobalTheory.LiftLevel.mem_level_iff h hK hH hsq l.prod (by rw [hM]; exact hN) u).1
    ⟨h1, h2, fun PP hP => h3 PP (by rw [hMb, GlobalTheory.LiftLevel.prod_le_iff] at hP; exact hP)⟩
  rw [← hM]
  exact ((hK u).1 hu).2

theorem levAgrees_mul {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} {Mh : Ideal (𝓞 D.host.E)}
    {κ u : GA D V} {lev : La →ₗ[𝓞 D.host.E] La} (hκ : GlobalTheory.Member.FinCong V 1 κ) (hu : GlobalTheory.Member.FinCong V M u)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees V ι M Mh κ lev) : GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees V ι M Mh (κ * u) lev := by
  intro a ha
  obtain ⟨w, hw, e⟩ := h a ha
  have hm : ι a ∈ (⊤ : Ideal (𝓞 D.host.E)) • latG V 1 := by
    rw [Submodule.top_smul, ← hι.2]
    exact ⟨a, rfl⟩
  obtain ⟨w', hw', e'⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V u).2 M ⊤).1
    (fun b _ z hz => hu _ (GlobalTheory.Member.halfVec_mem_latHat V b z hz)) _ hm
  refine ⟨w - (finHom V κ).1 *ᵥ w', sub_mem hw ((GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ w' hw'), ?_⟩
  rw [map_mul, Units.val_mul]
  exact cong_mul _ _ M _ _ _ _ e e'

end GlobalTheory.LiftAgrees

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LiftAgrees.levAgrees_of_isLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Formalism.IndefR.Links.Wc D i).rank → D.host.E)) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La), LatEmb (Formalism.IndefR.Links.Wc D i) ι → Formalism.IndefR.FWT.LevIs R i ι (D.host.g 0 * D.host.g 1) Mh lev → ∀ (g : G) (k : GA D (Formalism.IndefR.Links.Wc D i)), Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.LevAgrees (Formalism.IndefR.Links.Wc D i) ι (D.host.g 0 * D.host.g 1) Mh k (lev g) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hIs La _ _ ι Mh lev hι hlev g k hk
  obtain ⟨κ, hκ, hag⟩ := hlev g
  have h1 := (GlobalTheory.LiftLevel.isLift_one_iff (R.βW i) (R.datWp i R.triv)
    (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le rfl _).1 (GlobalTheory.LiftAgrees.isLift_inv_mul hκ hk)
  have h2 := GlobalTheory.LiftAgrees.finCong_of_red R.C.P (hIs.βW i) h1.1 h1.2.1 fun PP hP => h1.2.2 PP ((hIs.Pg PP).2 hP)
  have h3 := GlobalTheory.LiftAgrees.finCong_one_of_St (hIs.βW i) (Formalism.L2.DIV.parLev_St hκ.2.1)
  have h4 := GlobalTheory.LiftAgrees.levAgrees_mul hι h3 h2 hag
  rwa [mul_inv_cancel_left] at h4
