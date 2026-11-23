import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceRead.LevVal

variable {D : D7}

theorem mem_intLL_of_pow {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) (hz : ∃ y, D.what₂.embLL y = z) : z ∈ intLL D := by
  obtain ⟨y, rfl⟩ := hz
  have h1 : y ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral ℤ y := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  exact ⟨⟨y, hi⟩, rfl⟩

theorem mem_range_of_pow_of_fixed {K : Type} [Field K] [Countable K] [CharZero K] (f : K →+* ℂ) {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (h : z ^ n = 1) (hf : ∀ τ : ℂ ≃+* ℂ, (∀ x, τ (f x) = f x) → τ z = z) : ∃ y, f y = z := by
  letI : Algebra K ℂ := f.toAlgebra
  have hi : IsIntegral K z := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  let L := IntermediateField.adjoin K {z}
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hi
  haveI : Countable L := (Module.finBasis K L).equivFun.toEquiv.injective.countable
  let r : L := ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CompRat.FixedConst.mem_range_of_fixed (K := K) L.val (r := r) (IsIntegral.of_finite K r) hf
  exact ⟨y, congrArg Subtype.val hy⟩

theorem twistOf_good {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hψ : TwOK i k Q ψ) (f : D.ntw.Ok i k →+* ℂ) :
    (twistOf ρ.rc f (ρ.ch i) Q ψ).Good ∧
      ∀ x, ∃ σ, (((twistOf ρ.rc f (ρ.ch i) Q ψ).chi x : Circle) : ℂ) = f (ψ σ : (D.ntw.Ok i k)ˣ) ∧ ∃ n ≠ 0, ψ σ ^ n = 1 := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D D.nd D.ntw ρ hρ i j b Q hsplit hdisj
  let g : (D.ntw.Ok i k)ˣ →* Circle := unitPart.comp (Units.map f.toMonoidHom)
  have hkey : charOf ρ.rc f ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (D.ntw.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, ?_⟩
  · show (⟨half (ρ.ch i) Q, charOf ρ.rc f ψ, resOf (charOf ρ.rc f ψ)⟩ : Twist D Circle).Good
    rw [hkey]
    refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D D.nd D.ntw ρ.rc hρ.rc Circle (g.comp ψ) (D.ntw.l i) (D.ntw.lPrime i).out
      (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
    · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        rw [MonoidHom.comp_apply, hx, map_one]) hopen
    · intro x x' hx
      show g (ψ x') = (g (ψ x))⁻¹
      rw [hanti x x' hx, map_inv]
    · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
      exact h3.mono (Finset.subset_union_right.trans h2)
    · intro P hP hl
      exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (D.ntw.l i) from hl))
    · intro v hv hnc B hB σ hσ
      have hvQ : v ∉ Q := by
        intro hvQ
        by_cases hc : v ∈ ρ.ch i
        · exact hv (mem_half.2 ⟨hvQ, hc⟩)
        · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
          have hv'Q : v' ∈ Q := GlobalTheory.TwistGood.ramExactly_conj D.ntw ψ _ hanti hram v hvQ v' hv'
          have hne := ne_of_split (hsplit v hvQ) hv'
          have hv'c : v' ∈ ρ.ch i := by
            by_contra h
            exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
          exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
      have h1 : ψ σ = 1 := by
        by_contra h
        exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
      rw [MonoidHom.comp_apply, h1, map_one]
  · intro x
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
    exact ⟨σ, charOf_eq ρ.rc f hopen hσ (pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero) (hpow σ), _,
      pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero, hpow σ⟩

theorem de_chi_eq_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) ∧
      ∃ n ≠ 0, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ n = 1 := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_, _, Subgroup.FiniteIndex.index_ne_zero, hpow σ⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

variable {X : RealSide D} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀)

theorem de_mem_intLL (hX : FieldOk X) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    (((Z.ρ.B i j b).de.chi x : Circle) : ℂ) ∈ intLL D := by
  obtain ⟨σ, hσ, n, hn, hp⟩ := de_chi_eq_pow Z.good i j b x
  have hz : (((Z.ρ.B i j b).de.chi x : Circle) : ℂ) ^ n = 1 := by
    rw [hσ, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hp, Units.val_one, map_one, map_one]
  haveI : Countable D.what₂.LL := (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.injective.countable
  obtain ⟨y, hy⟩ := mem_range_of_pow_of_fixed (embLL0 D) hn hz fun τ hτ => by
    rw [hσ]
    refine GlobalTheory.DeltaFixed.aut_fixes_delta_values Z.ρ Z.good i j b (X.R.C.delAt (D.ntw.l i)) (Z.pin.delta i j b) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [hX.vals.del', hX.vals.del]
  exact mem_intLL_of_pow hn hz ⟨y, hy⟩

theorem muC_mem_intLL (hX : FieldOk X) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E}
    (hPP : PP ∈ (Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) : (((Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ intLL D := by
  obtain ⟨k, hk⟩ := Z.good.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hX.roots k _ hz
  have h2 := (D.host.g_prime k).two_le
  exact mem_intLL_of_pow (Nat.mul_ne_zero (by omega) (by omega)) hz ⟨x, hx⟩

theorem levLam_twVia_mem_intLL : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ k : (baseOf Z c w j).levJ (twVia Z.ρ ι), (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) ∈ intLL D := by
  intro D X X0 Y S YS Z c w j H ι hι x
  obtain ⟨hg, hv⟩ := twistOf_good Z.good (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) H.ok (viaOk ι)
  have htw : ∀ z, (((twVia Z.ρ ι).chi z : Circle) : ℂ) ∈ intLL D := fun z => by
    obtain ⟨σ, hσ, n, hn, hp⟩ := hv z
    obtain ⟨y, hy⟩ := H.val σ
    refine mem_intLL_of_pow hn ?_ ⟨y, ?_⟩
    · refine (congrArg (· ^ n) hσ).trans ?_
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hp, Units.val_one, map_one]
    · rw [← hι, hy]
      exact hσ.symm
  have hext : ∀ g : G0 (Z.ρ.B (c.twI w) j (c.sd w)).G.Pg (Wc D j).rank,
      ((ext1 (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H (⇑(Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi) g : ℂˣ) : ℂ) ∈ intLL D := fun g => by
    unfold ext1
    split_ifs with h
    · obtain ⟨g', rfl⟩ := (Z.ρ.eG (c.twI w) j (c.sd w)).surjective g
      obtain ⟨g₀, rfl⟩ := (X.R.eG.trans X.cG).surjective g'
      have hu : X.cG (X.R.eG g₀) ∈ D.nexp.U := ((Z.tie (c.twI w) j (c.sd w)).U_eq _).1 h
      have e1 := ((Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hu⟩ h).trans (H.psi_eq (c.twI w) (c.sd w) ⟨g₀, (H.U_eq g₀).1 hu⟩ hu)
      refine mem_intLL_of_pow (n := Nat.card (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H) Nat.card_pos.ne' ?_ ⟨_, (map_inv₀ _ _).trans e1.symm⟩
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
    · exact one_mem _
  have e : (baseOf Z c w j).levLam (twVia Z.ρ ι) x =
      levFn (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hext _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem_intLL Z H.field _ j _ hPP _))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (locC_mem (Z.good.base _ j _).de (de_mem_intLL Z H.field _ j _) PP _) (locC_mem (t := twVia Z.ρ ι) hg htw PP _)

end GlobalTheory.PlaceRead.LevVal

end
