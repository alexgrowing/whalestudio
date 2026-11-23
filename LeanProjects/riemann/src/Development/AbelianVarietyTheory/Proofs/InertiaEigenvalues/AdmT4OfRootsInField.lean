import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwInputs

variable {D : D7} {ρ : Setup D.ntw}

theorem de_mem_eO (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem e_mem_eO (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : ρ.e i b a ^ n = 1) : ρ.e i b a ∈ (ρ.eO i b).range := by
  have h1 : a ^ n = 1 := (ρ.e i b).injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral (D.ntw.O i) a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨y, rfl⟩

theorem typeCharacterExtension_value_mem_coefficientRing {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b}
    (T : CellTie hρ D.nexp rd) (g : G0 (ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (ρ.B i j b).G.P.H (⇑(ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  unfold ext1
  split_ifs with h
  · obtain ⟨g', rfl⟩ := (ρ.eG i j b).surjective g
    have e1 := T.psiU_eq ⟨g', (T.U_eq g').1 h⟩ h
    have hfin : ((ρ.B i j b).G.P.chi ⟨ρ.eG i j b g', h⟩) ^ Nat.card (ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [e1]
    refine e_mem_eO ρ i b (n := Nat.card (ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    rw [← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one]
  · exact one_mem _

theorem card_residueField_of_type {k : Fin 2} {PP : Pl D.host.E} (h : PP ∈ placesOver D.host.E (D.host.g k)) :
    Nat.card (kP PP) = D.host.g k :=
  GlobalTheory.SplitResidueCard.card_quotient_of_ncard (F := D.host.E) (D.host.g_prime k) (D.nd.g_split k) PP h

theorem muC_mem_eO (hρ : ρ.Good)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E} (hPP : PP ∈ (ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨k, hk⟩ := hρ.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hr k _ hz
  have h2 := (D.host.g_prime k).two_le
  have e : ρ.e i b (sideEmb D.ntw i b x) = (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) := (hρ.e_LL0 i b x).trans hx
  rw [← e] at hz ⊢
  exact e_mem_eO ρ i b (Nat.mul_ne_zero (by omega) (by omega)) hz

theorem locC_mem {t : Twist D Circle} (ht : t.Good) {O : Subring ℂ} (h : ∀ x, ((t.chi x : Circle) : ℂ) ∈ O)
    (PP : Pl D.host.E) (w : (kP PP)ˣ) : ((t.locC PP w : ℂˣ) : ℂ) ∈ O := by
  unfold Twist.locC
  split_ifs with hq
  · obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (ht.split.isIdemAt hq) w
    show ((t.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (ht.res PP hq)]
    exact h x
  · simp

theorem levLam_mem_eOk {hρ : ρ.Good}
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b} (T : CellTie hρ D.nexp rd) {k Q ψ} (hψ : TwOK i k Q ψ)
    (x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ)) :
    (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range := by
  obtain ⟨hg, -, hv⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ i j b k Q ψ hψ
  have hle := hρ.range_le i b k
  have e : (ρ.B i j b).levLam (ρ.tw i b k Q ψ) x =
      levFn (ρ.B i j b).F.βS ((ρ.B i j b).levS (ρ.tw i b k Q ψ)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hle (typeCharacterExtension_value_mem_coefficientRing T _)) (prod_mem fun PP hPP => prod_mem fun _ _ => hle (muC_mem_eO hρ hr i j b hPP _)))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (hle (locC_mem (hρ.base i j b).de (de_mem_eO hρ i j b) PP _))
    (locC_mem (O := (ρ.eOk i b k).range) hg (fun z => (hv z).elim fun u hu => ⟨u, hu.symm⟩) PP _)

theorem admT4_of_full_compatibility : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
    ∀ E : IntegralHeckeForms.XD D, IntegralHeckeForms.admT4 D.nexp E := by
  intro D ρ hρ rd hT hr E i _ j hj b k Q ψ hψ Sg _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have T := hT.tie i j' b
  rw [IntegralHeckeForms.ThPsi, Submodule.span_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨d, -, hx⟩ := hx
  have hg := (T.thPsi_iff k Q ψ hψ d x).1 hx
  obtain ⟨F, hF, e⟩ := GlobalTheory.T.twistedThetaGenerator_eq_classSum_integralForm D ρ hρ i j' b k Q ψ hψ (levLam_mem_eOk hr T hψ) _ _ _ (T.dat d) _ hg
  obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff k Q ψ hψ F).1 hF
  refine ⟨f, hf, T.injective_rdK k ?_⟩
  rw [T.thP_eq k Q ψ hψ f ⟨x, e⟩]
  exact e.symm

example (X : RealSide D) (hX : FieldOk X) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) : IntegralHeckeForms.admT4 D.nexp E :=
  admT4_of_full_compatibility D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hX.roots E

end GlobalTheory.TwInputs

end
