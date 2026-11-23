import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthBig

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem exists_modulBar_notMem (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0) :
    ∃ c : 𝓞 D.host.E, c ∈ G.pl.modulBar sc ∧ c ∉ (G.pl.w v).asIdeal := by
  classical
  have hne : ¬ G.pl.modul sc ≤ (GlobalTheory.IdemSupport.cP (G.pl.w v)).asIdeal := by
    intro h
    unfold Places.modul at h
    obtain ⟨v', hv', hle⟩ := (Ideal.IsPrime.prod_le (GlobalTheory.IdemSupport.cP (G.pl.w v)).isPrime).1 h
    have h1 := Ideal.IsPrime.le_of_pow_le (hP := (GlobalTheory.IdemSupport.cP (G.pl.w v)).isPrime) hle
    have h2 : G.pl.w v' = GlobalTheory.IdemSupport.cP (G.pl.w v) :=
      HeightOneSpectrum.ext ((G.pl.w v').isMaximal.eq_of_le (GlobalTheory.IdemSupport.cP (G.pl.w v)).isPrime.ne_top h1)
    have h3 : v' = v := by
      rw [← G.pl.under_w hv', h2, GlobalTheory.IdemSupport.under_cP, G.pl.under_w hv]
    subst h3
    obtain ⟨e, he⟩ := G.pl.w_split v' hv
    exact conjPrime_ne_of_isIdempotentAt he h2.symm
  obtain ⟨c₀, hc₀, hc₀'⟩ := Set.not_subset.1 hne
  refine ⟨D.host.conj • c₀, ?_, ?_⟩
  · unfold Places.modulBar
    exact Ideal.smul_mem_pointwise_smul _ _ _ hc₀
  · have e : D.host.conj • c₀ = GlobalTheory.IdemSupport.cO D c₀ := by
      apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
      rw [Formalism.L2.Pj.algebraMap_conj_smul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
        GlobalTheory.IdemSupport.cO_coe, bridge_star_holds D.R D.host]
    rw [e]
    exact hc₀'

theorem v_le_of_mem_shiftId (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0) {a : D.host.E}
    (ha : a ∈ shiftId G) :
    Valued.v (algebraMap D.host.E (Kw (G.pl.w v)) a) ≤ WithZero.exp (-(cosExp G (G.pl.w v) : ℤ)) := by
  obtain ⟨c, hc, hcw⟩ := exists_modulBar_notMem G hv
  have h0 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc
  have hm : algebraMap (𝓞 D.host.E) D.host.E c * a ∈
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨c, hc, rfl⟩) ha
    rwa [shiftId, mul_left_comm, mul_inv_cancel₀ h0, mul_one] at this
  obtain ⟨o, ho, hoe⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 hm
  have hle : G.pl.modul sc ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := by
    unfold Places.modul
    exact Ideal.prod_le_inf.trans (Finset.inf_le hv)
  have h1 : (G.pl.w v).valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E o) ≤
      WithZero.exp (-(G.pl.depth sc v : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (hle ho)
  have h2 : (G.pl.w v).valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E c) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm ((G.pl.w v).intValuation_le_one c)
      (not_lt.1 fun h => hcw (((G.pl.w v).intValuation_lt_one_iff_mem c).1 h))
  rw [hoe, map_mul, h2, one_mul] at h1
  rw [(depthAt_w G hv).1, Good.valued_alg]
  exact h1

end GlobalTheory.DepthBig

namespace GlobalTheory.DepthBig
open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames Formalism.L2.DIV

variable {D : D7} {S T : HSp D}

theorem genMap_add (s : Fin S.rank → D.host.E) (t t' : Fin T.rank → D.host.E) :
    GlobalTheory.LatVac.genMap S T 1 s (t + t') = GlobalTheory.LatVac.genMap S T 1 s t + GlobalTheory.LatVac.genMap S T 1 s t' := by
  ext i j
  simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  ring_nf

theorem genMap_smul (s : Fin S.rank → D.host.E) (r : D.host.E) (t : Fin T.rank → D.host.E) :
    GlobalTheory.LatVac.genMap S T 1 s (r • t) = r • GlobalTheory.LatVac.genMap S T 1 s t := by
  ext i j
  simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf

theorem genMap_zero (s : Fin S.rank → D.host.E) : GlobalTheory.LatVac.genMap S T 1 s 0 = 0 := by
  ext i j
  simp [GlobalTheory.LatVac.genMap]

end GlobalTheory.DepthBig

namespace GlobalTheory.DepthBig
open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RowLatChi

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

set_option maxHeartbeats 1000000 in

theorem v_le_of_mem_latO_idLat (hS : IsSelfDualC S ΛS) {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) (w : Pl D.host.E)
    (hw : ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1)
    {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {k : ℕ}
    (hI : ∀ a ∈ I, Valued.v (algebraMap D.host.E (Kw w) a) ≤ WithZero.exp (-(k : ℤ))) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (idLat I ΛT : Set _) fun _ => True) (a : Fin T.rank) (b : Fin S.rank) :
    Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ WithZero.exp (-(k : ℤ)) := by
  set B : WithZero (Multiplicative ℤ) := WithZero.exp (-(k : ℤ)) with hB
  let p : WO S T → Prop := fun u => ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ B
  have hadd : ∀ x y, p x → p y → p (x + y) := fun x y hx hy a b => by
    rw [Matrix.map_add _ (toEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]
    exact Valuation.map_add_le _ (hx a b) (hy a b)
  have hneg : ∀ x, p x → p (-x) := fun x hx a b => by
    rw [Matrix.map_neg _ (toEAf D).map_neg, fr_neg, Matrix.neg_apply, RingHom.map_neg, Valuation.map_neg]
    exact hx a b
  have hzero : p 0 := fun a b => by
    rw [Matrix.map_zero _ (toEAf D).map_zero, show Comparison₂.fr βT βS (0 : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) = 0 by
      rw [Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]
    simp

  have hY : ∀ s ∈ ΛS, ∀ t ∈ idLat I ΛT, ∀ a b,
      Valued.v (cpt (D := D) w (Comparison₂.fr βT βS ((GlobalTheory.LatVac.genMap S T 1 s t).map (eToEAf D)) a b)) ≤ B := by
    intro s hs t ht
    refine Submodule.span_induction (p := fun t _ => ∀ a b,
      Valued.v (cpt (D := D) w (Comparison₂.fr βT βS ((GlobalTheory.LatVac.genMap S T 1 s t).map (eToEAf D)) a b)) ≤ B) ?_ ?_ ?_ ?_ ht
    · rintro _ ⟨r, hr, y, hy, rfl⟩ a b
      have hY0 := genMap_one_mem_homLat hS hs hy
      obtain ⟨s', -, hs'⟩ := Comparison₂.fr_mem_idS hβS hβT (𝔪 := ⊤) (by rw [Submodule.top_smul]; exact hY0) a b
      have h4 := (mem_OA_iff _).1 s'.2 w
      rw [hs'] at h4
      rw [genMap_smul, show (r • GlobalTheory.LatVac.genMap S T 1 s y).map (eToEAf D) =
          eToEAf D r • (GlobalTheory.LatVac.genMap S T 1 s y).map (eToEAf D) from
          Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul],
        Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, Valuation.map_mul,
        show cpt (D := D) w (eToEAf D r) = algebraMap D.host.E (Kw w) r from Comparison₂.cpt_tmul w r]
      exact mul_le_of_le_of_le_one (hI r hr) h4
    · intro a b
      rw [genMap_zero, Matrix.map_zero _ (eToEAf D).map_zero, show Comparison₂.fr βT βS (0 : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) = 0 by
        rw [Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]
      simp
    · intro x y _ _ hx hy a b
      rw [genMap_add, Matrix.map_add _ (eToEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]
      exact Valuation.map_add_le _ (hx a b) (hy a b)
    · intro o x _ hx a b
      rw [show o • x = (algebraMap (𝓞 D.host.E) D.host.E o) • x from (algebraMap_smul _ _ _).symm, genMap_smul,
        show (algebraMap (𝓞 D.host.E) D.host.E o • GlobalTheory.LatVac.genMap S T 1 s x).map (eToEAf D) =
          eToEAf D (algebraMap (𝓞 D.host.E) D.host.E o) • (GlobalTheory.LatVac.genMap S T 1 s x).map (eToEAf D) from
          Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul],
        Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, Valuation.map_mul,
        show cpt (D := D) w (eToEAf D (algebraMap (𝓞 D.host.E) D.host.E o)) =
          algebraMap D.host.E (Kw w) (algebraMap (𝓞 D.host.E) D.host.E o) from Comparison₂.cpt_tmul w _, Good.valued_alg,
        HeightOneSpectrum.valuation_of_algebraMap]
      exact mul_le_of_le_one_of_le (w.intValuation_le_one o) (hx a b)
  refine GlobalTheory.LatVac.latO_induction (p := p) (fun α hα M hM => ?_) hzero hadd hneg hu a b
  induction hM using AddSubgroup.closure_induction with
  | mem M hM =>
    obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hM
    set Y := GlobalTheory.LatVac.genMap S T 1 s t
    have e1 : (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T c s t) : WO S T).map (toEAf D) =
        toEAf D ((pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c) • Y.map (eToEAf D) := by
      ext i j
      simp only [GlobalTheory.LatVac.finTens, Y, GlobalTheory.LatVac.genMap, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [show c * t i * ∑ k, star (s k) * HSpace.gram S k j = c * (1 * t i * ∑ k, star (s k) * HSpace.gram S k j) by ring,
        tmul_eq, RingHom.map_mul]
      rfl
    intro a b
    rw [e1, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      RingHom.map_mul, Valuation.map_mul]
    have h1 : Valued.v (cpt (D := D) w (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)))) ≤ 1 := by
      have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
      exact ((comp_toAd D).int (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E))).1 hi w
    have h2 : Valued.v (cpt (D := D) w (toEAf D (incA D c))) ≤ 1 := by
      rw [show cpt (D := D) w (toEAf D (incA D c)) = algebraMap D.host.E (Kw w) c from Comparison₂.cpt_tmul w c]
      exact hw c hc
    exact mul_le_of_le_one_of_le (mul_le_one' h1 h2) (hY s hs t ht a b)
  | zero => rw [GlobalTheory.LatVac.finTens_zero]; exact hzero
  | add x y _ _ hx hy => rw [GlobalTheory.LatVac.finTens_add]; exact hadd _ _ hx hy
  | neg x _ hx => rw [GlobalTheory.LatVac.finTens_neg]; exact hneg _ hx

end GlobalTheory.DepthBig

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.DepthBig in

theorem GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m →
    ∀ v : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)),
      v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _)
        (fun _ => True) → v ∈ latBig G i → ∀ e : AE D, IsIdemSum e G.pl.W0 →
      e • v ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  intro D hQ T L μ0 hL sc G W M _ i hi u _ hB e he
  have hV : ∀ X : Node, X.InRange D.R.m → IsSelfDualC (G.V X) (G.Λ X) := fun X hX => by
    by_cases h0 : ∀ j, X ≠ .grid 0 j
    · exact (G.isV hX h0).sd
    · push_neg at h0
      obtain ⟨j, rfl⟩ := h0
      exact (GlobalTheory.ChiGrid.colY_isV D T L μ0 hL j hX.2).sd
  have hS := hV (.grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩
  have hT := hV (.grid i 0) ⟨hi.le, Nat.zero_le _⟩
  obtain ⟨βS, hβS⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ _ hS.1
  obtain ⟨βT, hβT⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ _ hT.1
  obtain ⟨e0, e1, e2⟩ := Comparison₂.cpt_idemSum he
  rw [Comparison₂.mem_hatMx_iff hβS hβT]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, e0, zero_mul]
  · have hfr : Comparison₂.fr βT βS ((e • u).map (toEAf D)) a b = toEAf D e * Comparison₂.fr βT βS (u.map (toEAf D)) a b := by
      have hm : (e • u).map (toEAf D) = toEAf D e • u.map (toEAf D) := Matrix.ext fun i j => by
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      rw [hm, Comparison₂.fr_smul]
      rfl
    have hloc : ∀ w ∈ G.pl.W0, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤
        WithZero.exp (-(cosExp G w : ℤ)) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := (GlobalTheory.DepthFix.mem_orthogonal_frame_iff G).1 hw
      exact v_le_of_mem_latO_idLat hS hβS hβT _ (GlobalTheory.DepthFix.aa_int hL hQ G hw)
        (fun x hx => v_le_of_mem_shiftId G hv hx) hB a b
    have hint : Comparison₂.fr βT βS ((e • u).map (toEAf D)) a b ∈ OA D := by
      refine (mem_OA_iff _).2 fun Q => ?_
      rw [hfr, RingHom.map_mul]
      by_cases hQ : Q ∈ G.pl.W0
      · rw [e1 Q hQ, one_mul]
        exact (hloc Q hQ).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
      · rw [e2 Q hQ, zero_mul]
        exact zero_mem _
    refine ⟨⟨_, hint⟩, (Comparison₂.mem_idS_modul G _).2 fun w hw => ?_, rfl⟩
    show Valued.v (cpt (D := D) w (Comparison₂.fr βT βS ((e • u).map (toEAf D)) a b)) ≤ _
    rw [hfr, RingHom.map_mul, e1 w hw, one_mul]
    exact hloc w hw
