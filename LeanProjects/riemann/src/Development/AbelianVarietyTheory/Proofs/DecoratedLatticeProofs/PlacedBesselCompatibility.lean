import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottomStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairIdentityStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

theorem GlobalTheory.MiTop.levFn_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {LL : Type} [CommRing LL] (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E LL n) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ Formalism.L2.DIV.lev hc J β L) (hy : y ∈ Formalism.L2.DIV.lev hc J β L) :
    Formalism.L2.DIV.levFn β L (x * y * x⁻¹) = Formalism.L2.DIV.levFn β L y := by
  have e := congrArg (Formalism.L2.DIV.levChar hc J β L)
    (show (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : Formalism.L2.DIV.lev hc J β L)⁻¹ : Formalism.L2.DIV.lev hc J β L) =
      ⟨x * y * x⁻¹, _⟩ from rfl)
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at e
  exact e.symm

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem mem_rJ_of_red (W : RealPack ex) (z : GA D (D.sp.Y 0)) (hz : z ∈ GfC (D.sp.Y 0))
    (hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0))
    (hR : ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg,
      Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1) :
    z ∈ rJ W := by
  refine ⟨hz, ?_⟩
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS ?_
  rintro PP (hP | hP)
  · exact hR PP hP
  · exact absurd hP (Finset.notMem_empty _)

theorem rChi_conj (W : RealPack ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ rJ W) (hκ : κ ∈ rJ W) :
    rChi W (k * κ * k⁻¹) = rChi W κ := by
  have h1 : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hk.2
  have h2 : Formalism.IndefR.Lev.finE (Yc D 0) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hκ.2
  have e := levFn_conj D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) h1 h2
  unfold rChi Formalism.IndefR.Lev.levChi
  erw [map_mul, map_mul, map_inv, e]

theorem mem_rJ_conj (W : RealPack ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ rJ W) : κ ∈ rJ W ↔ k * κ * k⁻¹ ∈ rJ W := by
  have := (Subgroup.mul_mem_cancel_right (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := k * κ) (Subgroup.inv_mem _ hk)).trans
    (Subgroup.mul_mem_cancel_left (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := κ) hk)
  exact this.symm

theorem matches_mul (W : RealPack ex) {z t k : GA D (D.sp.Y 0)} (hzf : z ∈ GfC (D.sp.Y 0))
    (hzc : z ∈ Subgroup.center (GA D (D.sp.Y 0))) (hk : k ∈ rJ W) (ht : Matches W.S.X W.Q.instEq (rJ W) (rChi W) t) :
    Matches W.S.X W.Q.instEq (rJ W) (rChi W) (z * t * k) := by
  have hkf : k ∈ GfC (D.sp.Y 0) := hk.1
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hzf ht.1) hkf, fun κ => ?_⟩
  have hz := Subgroup.mem_center_iff.mp hzc
  have hc : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹ := by
    have e : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = z * (t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹) * z⁻¹ := by group
    rw [e, ← hz, mul_inv_cancel_right]
  obtain ⟨h1, h2⟩ := ht.2 (k * κ * k⁻¹)
  rw [hc]
  refine ⟨(mem_rJ_conj W hk).trans h1, fun hκ => ?_⟩
  rw [h2 ((mem_rJ_conj W hk).1 hκ), rChi_conj W hk hκ]

theorem matching_coset : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → GlobalTheory.MiTop.Framed B → GlobalTheory.MiTop.Framed B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∃ a₁, IsAt f B a₀ a₁ ∧ ∃ k ∈ rJ W, tOf f B a₀ a₁ = tOf f' B' a₀' a' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' hF hF' a₀ a a₀' a' hA hA'
  obtain ⟨z, hzf, hzc, c, hcf, hcc, k, hk, he⟩ :=
    GlobalTheory.T.matching_translates_bottom W hW.bot hr u B (tOf f B a₀ a) hA.2.2.2.1 (tOf f' B' a₀' a') hA'.2.2.2.1 hA.2.2.2 hA'.2.2.2
  have hcc' := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hcc)
  have hX : tOf f B a₀ (a * c⁻¹) = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o c⁻¹ *
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * tOf f B a₀ a := by
    unfold tOf
    rw [show a₀ * (a * c⁻¹) = c⁻¹ * (a₀ * a) by rw [← hcc' (a₀ * a), mul_assoc], map_mul]
    have key : ∀ {G : Type} [Group G] (x e y b : G), x⁻¹ * (e * y) * b = x⁻¹ * e * x * (x⁻¹ * y * b) := by
      intros; group
    exact key (G := GA D (D.sp.Y 0)) _ _ _ _
  have e1 : tOf f B a₀ (a * c⁻¹) = z * tOf f' B' a₀' a' * k := by
    rw [hX, he, map_inv]
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  have hA₁ : IsAt f B a₀ (a * c⁻¹) := by
    refine ⟨hA.1, Subgroup.mul_mem _ hA.2.1 (Subgroup.inv_mem _ hcf),
      Subgroup.mul_mem _ hA.2.2.1 (Subgroup.inv_mem _ hcc), ?_⟩
    rw [e1]
    exact matches_mul W hzf hzc hk hA'.2.2.2
  have hz : z ∈ rJ W := mem_rJ_of_red W z hzf
    (by first
      | exact GlobalTheory.T.placed_bessel_pair_relation W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact GlobalTheory.T.placed_bessel_pair_relation W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
    (by first
      | exact GlobalTheory.T.placed_bessel_pair_identity W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact GlobalTheory.T.placed_bessel_pair_identity W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
  refine ⟨a * c⁻¹, hA₁, z * k, Subgroup.mul_mem _ hz hk, ?_⟩
  rw [e1, ← (Subgroup.mem_center_iff.mp hzc (tOf f' B' a₀' a')), mul_assoc]

end GlobalTheory.MiTop
