import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open scoped Classical

namespace GlobalTheory.FlagTan

open GlobalTheory.Frames GlobalTheory.AllWt
open TrivSqZeroExt hiding map lift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]

variable (Dw K) in

def horExt (Φ : Finset (E →+* ℂ)) : (HIx Dw Φ → K) →ₗ[K] (TIx Dw Φ → K) :=
  LinearMap.pi fun b => Sum.elim (fun k => LinearMap.proj k) (fun _ => 0) b

variable (c) in

def horMap (Φ : Finset (E →+* ℂ)) : TrivSqZeroExt K (HIx Dw Φ → K) →ₐ[c.F] TrivSqZeroExt K (TIx Dw Φ → K) :=
  (TrivSqZeroExt.map (horExt Dw K Φ)).restrictScalars c.F

theorem fst_horMap {Φ : Finset (E →+* ℂ)} (a : TrivSqZeroExt K (HIx Dw Φ → K)) : (horMap c Φ a).fst = a.fst :=
  fst_map _ a

theorem dir_horMap {Φ : Finset (E →+* ℂ)} (m : TIx Dw Φ → K) (a : TrivSqZeroExt K (HIx Dw Φ → K)) :
    dir c m (horMap c Φ a) = dir c (m ∘ Sum.inl) a := by
  ext
  · simp [fst_horMap]
  · simp [snd_dir, horMap, horExt, Fintype.sum_sum_type]

def vertDirs (Φ : Finset (E →+* ℂ)) : FIx Dw → TIx Dw Φ → K :=
  fun k b => Sum.elim (fun _ => 0) (fun w : VIx Dw => if k = w.toF then 1 else 0) b

end GlobalTheory.FlagTan

set_option maxHeartbeats 1000000 in
open GlobalTheory.FlagTan GlobalTheory.Frames GlobalTheory.AllWt in
open TrivSqZeroExt hiding map lift in

theorem GlobalTheory.FlagTan.KSIso.tanFrame_of_universal_injective : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (psiSet H) P → ∃ (W : FrPt Xo c (TrivSqZeroExt K (TIx Dw (psiSet H) → K))) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)), FrMap (TrivSqZeroExt.fstHom c.F K (TIx Dw (psiSet H) → K)) W P ∧ (∀ b, FrMap (GlobalTheory.FlagTan.dir c (Pi.single b (1 : K))) W (v b)) ∧ IsTanFrame (psiSet H) P v ∧ ∀ (m : TIx Dw (psiSet H) → K) (u P₀ : FrPt Xo c (DualNumber K)), FrMap (GlobalTheory.FlagTan.dir c m) W u → FrMap (GlobalTheory.FlagTan.cst c K) P P₀ → X.ptY u = X.ptY P₀ → m = 0 := by
  intro E _ _ _ H Dw l Xo c Y X K _ _ P hK
  obtain ⟨XH, h1, h2, hU⟩ := hK
  obtain ⟨WH, rfl, hWH⟩ := exists_lift P XH h1 h2
  obtain ⟨W₀, hW₀⟩ := exists_frMap (horMap c (K := K) (Dw := Dw) (psiSet H)) WH
  let n : FIx Dw → TIx Dw (psiSet H) → K := vertDirs (psiSet H)
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)
  have key : ∀ (m : TIx Dw (psiSet H) → K) (z₀ z : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      IsShift (fun k => ∑ b, n k b * m b) z₀ z → FrMap (dir c m) W z := fun m z₀ z k₀ k => by
    refine (frMap_iff_frChg hW k₀).2 ?_
    unfold IsShift at k
    convert k using 2 with τ
    · ext i j <;> simp [unip]
    · ext <;> simp [unip₀]
  have shift : ∀ (m : TIx Dw (psiSet H) → K) (u : FrPt Xo c (DualNumber K)), FrMap (dir c m) W u →
      ∃ z₀, FrMap (dir c m) W₀ z₀ ∧ IsShift (fun k => ∑ b, n k b * m b) z₀ u := fun m u hu => by
    obtain ⟨z₀, hz₀⟩ := exists_frMap (dir c m) W₀
    obtain ⟨z, hz, -⟩ := existsUnique_isShift (fun k => ∑ b, n k b * m b) z₀
    exact ⟨z₀, hz₀, frMap_unique (key m z₀ z hz₀ hz) hu ▸ hz⟩
  have hbase : ∀ (m : TIx Dw (psiSet H) → K) (z₀ : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      FrMap (dir c (m ∘ Sum.inl)) WH z₀ := fun m z₀ h => frMap_comp hW₀ h fun a => dir_horMap m a
  have hfst : FrMap (fstHom c.F K (TIx Dw (psiSet H) → K)) W P := by
    have h0 : FrMap (fstHom c.F K (TIx Dw (psiSet H) → K)) W₀ P :=
      frMap_of_comp hW₀ hWH fun a => fst_horMap (c := c) a
    refine (frMap_iff_frChg hW h0).2 ?_
    convert (frChg_calculus E H Dw l Xo c _).2.1 P using 2 with τ
    · ext i j; by_cases h : i = j <;> simp [unip, Matrix.one_apply, h]
    · simp [unip₀]
  have hdef : ∀ (m : TIx Dw (psiSet H) → K) (u : FrPt Xo c (DualNumber K)), FrMap (dir c m) W u → IsDef P u :=
    fun m u h => frMap_of_comp h hfst fun a => fst_dir (c := c) m a
  choose v hv using fun b : TIx Dw (psiSet H) => exists_frMap (dir c (Pi.single b (1 : K))) W
  refine ⟨W, v, hfst, hv, ⟨fun k => ?_, fun w => ?_⟩, fun m u P₀ hu hP₀ hpt => ?_⟩
  · obtain ⟨z₀, hz₀, hs⟩ := shift _ _ (hv (.inl k))
    have e0 : (fun k' => ∑ b, n k' b * (Pi.single (Sum.inl k) (1 : K) : TIx Dw (psiSet H) → K) b) = 0 := by
      funext k'; simp [n, vertDirs, Fintype.sum_sum_type, Pi.single_apply]
    rw [e0] at hs
    have ev : v (.inl k) = z₀ := (existsUnique_isShift 0 z₀).unique hs (isShift_zero z₀)
    have e1 : (Pi.single (Sum.inl k) (1 : K) : TIx Dw (psiSet H) → K) ∘ Sum.inl = Pi.single k 1 := by
      funext h; simp [Pi.single_apply]
    have hb := hbase _ _ hz₀
    rw [e1] at hb
    have hd := hdef _ _ (hv (.inl k))
    refine ⟨hd, ((hU _ hd.isTanX).2 _).2 ?_⟩
    rw [ev]; exact hb.1
  · obtain ⟨z₀, hz₀, hs⟩ := shift _ _ (hv (.inr w))
    have e0 : (fun k' => ∑ b, n k' b * (Pi.single (Sum.inr w) (1 : K) : TIx Dw (psiSet H) → K) b) =
        Pi.single w.toF 1 := by
      funext k'; simp [n, vertDirs, Fintype.sum_sum_type, Pi.single_apply]
    rw [e0] at hs
    have hc : FrMap (GlobalTheory.FlagTan.cst c K) P z₀ := by
      have hb := hbase _ _ hz₀
      refine frMap_of_comp (ψ := GlobalTheory.FlagTan.cst c K) hWH hb fun a => ?_
      ext <;> simp [snd_dir, Pi.single_apply]
    exact ⟨z₀, hc, hs⟩
  · obtain ⟨z₀, hz₀, hs⟩ := shift m u hu
    have hH := hbase m z₀ hz₀
    obtain ⟨t, hB⟩ : ∃ t, FrBor t P₀ u := by
      obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY P₀)
      obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd P₀) (X.lies_ptY P₀).1 k hz
      obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY P₀)
      obtain ⟨t', ht'⟩ := hQ.exists_frBor (hpt ▸ X.lies_ptY u)
      obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (DualNumber K)
      exact ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
    have hd := hdef m u hu
    have e0 : m ∘ Sum.inl = 0 := by
      refine (hU u.x hd.isTanX).1.unique (hs.1.trans hH.1) ?_
      have ed : dir c (0 : HIx Dw (psiSet H) → K) = (cst c K).comp (fstHom c.F K (HIx Dw (psiSet H) → K)) :=
        AlgHom.ext fun a => by ext <;> simp [snd_dir]
      rw [hB.1, hP₀.1, ed, GlobalTheory.FlagMod.spMap_algComp, h2]
    have e0' : ∀ h, m (Sum.inl h) = 0 := fun h => congrFun e0 h
    have hz : z₀ = P₀ := by
      refine frMap_unique (frMap_of_comp hWH hH fun a => ?_) hP₀
      ext <;> simp [snd_dir, e0']
    rw [hz] at hs
    obtain ⟨g, hup, -, hc⟩ := (frBor_iff_frChg _ _ _).1 hB
    obtain ⟨hg, -⟩ := (frChg_exists_unique E H Dw l Xo c _ P₀ u).2 _ _ _ _ hc hs
    have hsum : ∀ w₀ : VIx Dw, ∑ b, n w₀.toF b * m b = m (Sum.inr w₀) := fun w₀ => by
      simp [n, vertDirs, Fintype.sum_sum_type, VIx.toF_injective.eq_iff]
    have ev : ∀ w₀ : VIx Dw, m (Sum.inr w₀) = 0 := by
      rintro ⟨σ, ⟨i, j⟩, hij⟩
      have := congrArg (fun g => (g σ i j).snd) hg
      rw [← hsum]
      simp only [VIx.toF]
      simpa [hup σ i j hij, unip] using this.symm
    funext b
    rcases b with b | b
    · exact e0' b
    · exact ev b
