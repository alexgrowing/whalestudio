import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeCharStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsResOfTameAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOneStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelChoices

open Formalism.L2.Host Formalism.L2.Herm

variable {D : D7}

theorem mem_crdLat (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ crdLat V V.L0 ↔ (crd V).symm x ∈ V.L0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (crd V).symm (crd V y) ∈ V.L0
    rwa [LinearEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, (crd V).apply_symm_apply x⟩

theorem coe_crdLat (V : HSp D) : (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  ext x
  rw [SetLike.mem_coe, mem_crdLat]
  show V.frame.equivFun.symm x ∈ V.L0 ↔ _
  rw [Module.Basis.equivFun_symm_apply]
  rfl

theorem dualL_crdLat (V : HSp D) : dualL D.sp.cm V (crdLat V V.L0) = crdLat V V.L0 := by
  unfold dualL
  conv_rhs => rw [← Submodule.span_eq (crdLat V V.L0)]
  congr 1
  ext x
  rw [SetLike.mem_coe, mem_crdLat]
  conv_rhs => rw [← V.baseLattice_isUnimodular]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one]
  constructor
  · intro h y hy
    have := h (crd V y) ⟨y, hy, rfl⟩
    rw [hT_crd D.sp.cm, LinearEquiv.apply_symm_apply]
    exact this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [hT_crd D.sp.cm, LinearEquiv.apply_symm_apply] at this
    exact this

theorem isSDFrame_of_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) (N : ℕ) : IsSDFrame V β Λ N := by
  obtain ⟨c, hc⟩ := h
  refine ⟨0, ?_⟩
  rw [one_pow] at hc
  rwa [pow_zero]

theorem isUnitary_of_orderDvd {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) :
    χ.IsUnitary := by
  intro x
  have h1 : (χ.1 x) ^ n = 1 := by
    have : (χ ^ n).1 x = 1 := by rw [h]; rfl
    rw [← this]; rfl
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem exists_levCh (D : D7) (C : CharFrame D) (T : Type) (μ0 : T) (ξ : T → HChar D.host.E)
    (Q : T → Finset (Pl D.host.E)) (hinj : Function.Injective ξ) (hbase : ξ μ0 = 1)
    (hfin : ∀ t, ∃ n : ℕ, 0 < n ∧ (ξ t).OrderDvd n) (htriv : ∀ t, (ξ t).TrivOn D.host.F)
    (htame : ∀ t v, (ξ t).TameAt v) (hpl : ∀ t, Lev.IsTwistPlaces D.host.g (Q t))
    (hoff : ∀ t, ∀ PP ∈ Q t, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
      ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hde : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
      ∀ t, ∀ PP ∈ Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭)
    (hram : ∀ t PP, ¬ (ξ t).UnrAt PP ↔ PP ∈ Q t ∨ ∃ PP' ∈ Q t, Lev.IsConjPl PP' PP) :
    ∃ L : LevCh D T, L.C = C ∧ L.xiH = ξ ∧ L.Q = Q ∧ (∀ j, L.ΛY j = crdLat _ (Yc D j).L0) ∧ L.Is μ0 := by
  classical
  choose m hm using fun j : Fin D.R.m => GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D (C.mu0 j) (C.isMu0 j).unitary
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D C.eta C.isEta.unitary
  choose x hx using fun t => GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D (ξ t) (by obtain ⟨n, hn, h⟩ := hfin t; exact isUnitary_of_orderDvd hn h)
  choose r hr using fun (j : Fin D.R.m) PP => GlobalTheory.exists_isRes_of_tameAt D (C.mu0 j) PP ((C.isMu0 j).tame PP)
  choose s hs using fun t PP => GlobalTheory.exists_isRes_of_tameAt D (ξ t) PP (htame t PP)
  choose β hβ using fun V : HSp D => GlobalTheory.T.exists_selfDual_adelic_frame_level_one D V (crdLat V V.L0) (coe_crdLat V) (dualL_crdLat V)
  refine ⟨{ C := C, xiH := ξ
            mu0 := fun j => if h : j - 1 < D.R.m then m ⟨j - 1, h⟩ else 1
            eta := η, xi := x
            Pg := Finset.univ.biUnion fun k => aboveF (L := D.host.E) D.host.K (C.P.pb k)
            Q := Q
            chi := fun j PP => if h : j - 1 < D.R.m then (r ⟨j - 1, h⟩ PP)⁻¹ else 1
            xiR := s
            ΛY := fun _ => crdLat _ (HSpace.L0 _), ΛX := crdLat _ (HSpace.L0 _)
            ΛV := fun _ => crdLat _ (HSpace.L0 _), ΛW := fun _ => crdLat _ (HSpace.L0 _)
            βY := fun _ => β _, βX := β _, βV := fun _ => β _, βW := fun _ => β _ }, rfl, rfl, rfl, fun _ => rfl, ?_⟩
  exact
    { mu0 := fun j => by
        have h : (j : ℕ) + 1 - 1 < D.R.m := j.2
        simp only [dif_pos h]
        exact hm j
      eta := hη, xi := hx, xi_inj := hinj, xi_base := hbase, xi_fin := hfin, xi_triv := htriv, xi_tame := htame
      Pg := fun PP => by
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, aboveF, Set.Finite.mem_toFinset]
        rfl
      Q_pl := hpl, Q_off := hoff, Q_de := hde, Q_ram := hram
      chi := fun j PP _ => by
        have h : (j : ℕ) + 1 - 1 < D.R.m := j.2
        simp only [dif_pos h, inv_inv]
        exact hr j PP
      xiR := fun t PP _ => hs t PP
      βY := fun j _ => isSDFrame_of_one (hβ _) _
      βX := hβ _, βV := fun _ => hβ _, βW := fun _ => hβ _ }

theorem exists_levCh_unit : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D), ∃ L : LevCh D Unit, L.C = C ∧ L.Is () := by
  intro D C
  obtain ⟨L, h1, -, -, -, h2⟩ := exists_levCh D C Unit () (fun _ => 1) (fun _ => ∅) (fun _ _ _ => rfl) rfl
    (fun _ => ⟨1, one_pos, one_pow 1⟩) (fun _ => (isPsi_one (H := D.host) 2).triv) (fun _ _ _ _ _ => rfl)
    (fun _ _ h => absurd h (Finset.notMem_empty _)) (fun _ _ h => absurd h (Finset.notMem_empty _))
    (fun _ _ => ⟨C.P.pb 0, fun _ _ h => absurd h (Finset.notMem_empty _)⟩)
    (fun _ _ => iff_of_false (fun h => h fun _ _ => rfl) (by simp))
  exact ⟨L, h1, h2⟩

end GlobalTheory.LevelChoices
