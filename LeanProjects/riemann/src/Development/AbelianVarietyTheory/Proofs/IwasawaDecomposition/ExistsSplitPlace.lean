import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeCharStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.ResidueEisenstein

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Host Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AntiChar

theorem exists_split_place (R : Ranks) (H : Formalism.BasicNotions.Host R) :
    ∃ w : HeightOneSpectrum (𝓞 H.E), ¬ GlobalTheory.Mem.Chr.ConjPl H.conj.toRingEquiv w w ∧
      ∃ p : ℕ, p.Prime ∧ Units.torsionOrder H.E + 1 < p ∧ (p : 𝓞 H.E) ∈ w.asIdeal := by
  obtain ⟨p, hp, hp2, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := H.QS * H.q * H.d) (Units.torsionOrder H.E + 1) H.condN_ne_zero
  have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p hp hmod
  have hne : {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hs]
    exact Module.finrank_pos.ne'
  obtain ⟨w, hw⟩ := hne
  obtain ⟨-, -, ⟨x, hx, hx'⟩, -⟩ := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs w hw
  refine ⟨w, fun h => ?_, p, hp, hp2, hw⟩
  · have h' := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w).2 h
    let y : 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv x
    exact hx' y rfl ((h' x y rfl).1 hx)

theorem exists_hchar (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (e : I ≃ R.Psi) (z : I → ℤ) :
    ∃ χ : HChar H.E, χ.IsUnitary ∧ χ.TrivOn H.F ∧ χ.HasInf (fun i => embPsi H (e i)) (fun i => -2 * z i) ∧
      ∃ T : Finset (HeightOneSpectrum (𝓞 H.E)), ∀ v, v ∉ T → χ.UnrAt v := by
  classical
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hcm' : GlobalTheory.Mem.Chr.CMData H.F c (fun i => embPsi H (e i)) :=
    ⟨hcm.real, hcm.cplx, hcm.rank, hcm.ne, hcm.bij.comp e.bijective⟩
  obtain ⟨w, hw, p, hp, hp2, hpw⟩ := exists_split_place R H
  rw [← hce] at hw
  obtain ⟨ω, -, hω⟩ := UpperTheory.Mu.tame_par w hp hp2 hpw (fun i => embPsi H (e i)) (fun i => -z i)
  obtain ⟨w', -, hw'⟩ := GlobalTheory.Mem.Chr.conjPl_main.1 H.E c.toRingEquiv w
  let θ0 : ∀ v : HeightOneSpectrum (𝓞 H.E), (𝓞 H.E ⧸ v.asIdeal)ˣ →* ℂˣ :=
    Function.update (fun _ => 1) w ω
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ := GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c I _ hcm' z {w} θ0
    (by
      intro v hv v' h hv'
      rw [Finset.mem_singleton] at hv hv'
      subst hv hv'
      exact hw h)
    (fun ζ hζ => by
      rw [Finset.prod_singleton]
      simp only [θ0, Function.update_self]
      exact hω ζ hζ)
  refine ⟨χ, hu, ht, hi, {w, w'}, fun v hv => hunr v ?_ ?_⟩
  · intro h
    exact hv (by rw [Finset.mem_singleton.1 h]; simp)
  · intro u hu' h
    rw [Finset.mem_singleton.1 hu'] at h
    exact hv (by rw [hw' v h]; simp)

theorem val_fin_principal (D : D7) (c : IdC D) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ v, v ∉ T → χ.UnrAt v) (k : D.host.Eˣ) (x : (AE D)ˣ)
    (h1 : infPart D (x : AE D) = 1) (h2 : finPart D (x : AE D) = finPart D (incA D k)) :
    ((χ.inf k : ℂˣ) : ℂ) * ((c x : Circle) : ℂ) = 1 := by
  classical
  obtain ⟨ι, i1, i2, i3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι i1 i2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι i1 i2 i3) c χ hc
  obtain ⟨S, -, -, hS⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)).toMonoidHom k)
  have hx : ∀ P, ι (finPart D (x : AE D)) P = algebraMap D.host.E (P.adicCompletion D.host.E) k := fun P => by
    rw [h2]
    exact congrArg (fun y : FiniteAdeleRing (𝓞 D.host.E) D.host.E => y P) (i1 k)
  have hS' : ∀ P, P ∉ S ∪ T → P.valuation D.host.E (k : D.host.E) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal := fun P hP => by
    have := hS P fun h => hP (Finset.mem_union_left _ h)
    exact ⟨(GlobalTheory.BaseIdeleTriv.val_algebraMap P (k : D.host.E)).symm.trans this.1, this.2⟩
  have h3 := hprod x h1 (S ∪ T) (fun _ => k)
    (fun P _ => ⟨by rw [hx, GlobalTheory.BaseIdeleTriv.val_algebraMap], by rw [hx, sub_self, map_zero]; exact zero_le⟩)
    (fun P hP => ⟨by rw [hx, GlobalTheory.BaseIdeleTriv.val_algebraMap]; exact (hS' P hP).1, (hS' P hP).2⟩)
  have h4 := GlobalTheory.HeckeProduct.hchar_productRule D.host.E χ (S ∪ T)
    (fun v hv => hT v fun h => hv (Finset.mem_union_right _ h)) k
  have h5 : (∏ᶠ (v : HeightOneSpectrum (𝓞 D.host.E)) (_ : v ∉ S ∪ T), χ.val v ^ ordF v k) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => (finprod_congr fun hv => by
      show χ.val v ^ ordF v k = 1
      rw [ordF, (hS' v hv).1]; simp).trans finprod_one
  rw [h5, mul_one] at h4
  rw [h3, ← Units.coe_prod, ← Units.val_mul, h4, Units.val_one]

set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare in

theorem val_inf (D : D7) [Fintype D.what₂.Tau] (c : IdC D) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ v, v ∉ T → χ.UnrAt v) (n : D.what₂.Tau → ℤ)
    (hn : χ.HasInf (tauE D) n) (θ : InfF D) (hθ : IsInfFam θ) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) :
    ((c x : Circle) : ℂ) = ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n τ := by
  obtain ⟨s, hs⟩ := GlobalTheory.FockCompare.exists_chart hθ
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let U : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Uc : Continuous U.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hU : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 →
      y = U.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom y := fun y hy =>
    Units.ext (ext _ _ (hy.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom y) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := GlobalTheory.HeckeFinTrivial.mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ, ((c (U.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / (‖(z τ : ℂ)‖ : ℂ)) ^ n τ := by
    intro z
    refine (GlobalTheory.HeckeFinTrivial.denseRange_units (tauE D) hd).induction_on z
      (isClosed_eq (continuous_subtype_val.comp (hc.1.1.comp Uc)) ?_) fun k => ?_
    · refine continuous_finsetProd _ fun τ _ => ?_
      have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h3 : ∀ z : D.what₂.Tau → ℂˣ, (‖(z τ : ℂ)‖ : ℂ) ≠ 0 := fun z => by
        exact_mod_cast norm_ne_zero_iff.2 (z τ).ne_zero
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _
        fun z => Or.inl (div_ne_zero (z τ).ne_zero (h3 z))
    · let y : (AE D)ˣ := Units.map (incA D).toMonoidHom k
      have e1 : a y = U.toHomUnits fun τ => Units.map (tauE D τ).toMonoidHom k := by
        rw [hU (a y) (ha y).2]
        congr 1
        funext τ
        exact Units.ext ((congrArg (θ τ) (ha y).1).trans ((hθ τ).1 k))
      have e2 := val_fin_principal D c χ hc T hT k (b y) (hb y).1 (hb y).2
      have e3 : c (a y) * c (b y) = 1 := by rw [← map_mul, ← hab y]; exact hc.1.2 k
      have e4 : ((c (a y) : Circle) : ℂ) * ((c (b y) : Circle) : ℂ) = 1 := by rw [← Circle.coe_mul, e3, Circle.coe_one]
      rw [← e1]
      exact (mul_right_cancel₀ (Circle.coe_ne_zero _) (e4.trans e2.symm)).trans (hn k)
  exact (congrArg (fun y => ((c y : Circle) : ℂ)) (hU x hx)).trans (key _)

theorem sign_zpow_even {w : ℂ} (hw : starRingEnd ℂ w = w) (h0 : w ≠ 0) (m : ℤ) : (w / (‖w‖ : ℂ)) ^ (-2 * m) = 1 := by
  have h1 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have h2 : (w / (‖w‖ : ℂ)) ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, div_pow, ← Complex.mul_conj', hw, sq]
    exact div_self (mul_ne_zero h0 h0)
  rw [show -2 * m = 2 * -m by ring, _root_.zpow_mul, h2, _root_.one_zpow]

set_option maxHeartbeats 1000000 in

theorem exists_char : ∀ (D : D7) (j : Fin D.R.m),
    ∃ χ : IdC D, IsHeckeChar D χ ∧ (∀ τ, HasInfExp D χ τ (-(D.hc τ).e j)) ∧ ResEta D χ 0 := by
  intro D j
  classical
  letI : Fintype D.what₂.Tau := Fintype.ofEquiv _ D.eTau.symm
  choose z hz using fun τ => (D.hc τ).e_int j
  obtain ⟨χ, hu, ht, hi, T, hT⟩ := exists_hchar D.R D.host D.what₂.Tau D.eTau z
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D χ hu
  have hv := val_inf D c χ hc T hT _ hi
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.Member.exists_isInfFam_family D
  refine ⟨c, hc.1, fun τ => ⟨-2 * z τ, by rw [hz]; push_cast; ring, ⟨θ₀, hθ₀⟩, fun θ hθ x h1 h2 => ?_⟩,
    GlobalTheory.VolHeckeCompare.exists_isEta D, fun η _ a => ?_⟩
  · rw [hv θ hθ x h1, Finset.prod_eq_single τ (fun τ' _ h => by rw [h2 τ' h]; simp) (by simp)]
  · let p : AF D.host.F →* AF D.host.F := (MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))
    let q : AF D.host.F →* AF D.host.F := (MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))
    have e : a = Units.map p a * Units.map q a := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have e1 : c (idF D (Units.map q a)) = 1 := GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ hc ht _ rfl
    have e2 : c (idF D (Units.map p a)) = 1 := by
      apply Circle.ext
      rw [hv θ₀ hθ₀ _ rfl, Circle.coe_one]
      refine Finset.prod_eq_one fun τ _ => sign_zpow_even (GlobalTheory.FockCompare.conj_tmul_one hθ₀ τ _) ?_ _
      exact (Units.map ((θ₀ τ).comp (infPart D)).toMonoidHom (idF D (Units.map p a))).ne_zero
    rw [pow_zero, e, map_mul, map_mul, e1, e2, one_mul]

end GlobalTheory.Mem.AntiChar
