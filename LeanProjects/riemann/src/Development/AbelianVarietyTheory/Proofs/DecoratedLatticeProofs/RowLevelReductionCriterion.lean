import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryMatchingFramesAtNonconjugatePlaces

noncomputable section

namespace GlobalTheory.PrinFrame

section Alg

open Matrix

variable {A : Type} [CommRing A] {n : ℕ}

theorem conj_single_mem (S : Subring A) (p : S) (hp : p * p = p) (γ : GL (Fin n) A)
    (h : ∀ i j, i ≠ j → ∀ a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (i j a b : Fin n) :
    (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S := by
  by_cases hij : i = j
  · subst hij
    by_cases hl : ∃ l, l ≠ i
    · obtain ⟨l, hl⟩ := hl
      have hp' : (p : A) * p = p := congrArg Subtype.val hp
      have e1 : ∑ c, γ.1 l c * (γ⁻¹).1 c l = 1 := by
        have := congrFun (congrFun γ.mul_inv l) l
        rwa [Matrix.mul_apply, Matrix.one_apply_eq] at this
      have e2 : (p : A) * ((γ⁻¹).1 a i * γ.1 i b) =
          ∑ c, ((p : A) * ((γ⁻¹).1 a i * γ.1 l c)) * ((p : A) * ((γ⁻¹).1 c l * γ.1 i b)) := by
        rw [← mul_one ((p : A) * _), ← e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        linear_combination (-((γ⁻¹).1 a i * γ.1 i b * γ.1 l c * (γ⁻¹).1 c l)) * hp'
      rw [e2]
      exact S.sum_mem fun c _ => S.mul_mem (h i l hl.symm a c) (h l i hl c b)
    · push Not at hl
      have e1 : (γ⁻¹).1 i i * γ.1 i i = 1 := by
        have := congrFun (congrFun γ.inv_mul i) i
        rwa [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i (fun c _ hc => absurd (hl c) hc)
          (fun hc => absurd (Finset.mem_univ i) hc)] at this
      rw [hl a, hl b, e1, mul_one]
      exact p.2
  · exact h i j hij a b

theorem red_conj_eq_one (S : Subring A) {k : Type} [CommRing k] (ρ : S →+* k) (p : S) (hρ : ρ p = 1) (γ : GL (Fin n) A)
    (h : ∀ i j a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (y y₀ : Matrix (Fin n) (Fin n) S)
    (hy : y₀.map S.subtype = γ.1 * y.map S.subtype * (γ⁻¹).1) (h1 : y.map ρ = 1) : y₀.map ρ = 1 := by
  have e0 : ∀ {B : Type} [CommRing B] (f : S →+* B) (z : Matrix (Fin n) (Fin n) S), (z - 1).map f = z.map f - 1 := by
    intro B _ f z
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
  have e1 : (y₀ - 1).map S.subtype = γ.1 * (y - 1).map S.subtype * (γ⁻¹).1 := by
    rw [e0, e0, hy, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv]
  have e2 : ∀ b a, ρ ((y - 1) b a) = 0 := fun b a => by
    have := congrFun (congrFun (e0 ρ y) b) a
    rwa [h1, sub_self] at this
  rw [← sub_eq_zero, ← e0]
  ext j i
  have e3 : p * (y₀ - 1) j i = ∑ a, ∑ b, (⟨_, h i j a b⟩ : S) * (y - 1) b a := by
    apply Subtype.ext
    have := congrFun (congrFun e1 j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Subring.subtype_apply] at this
    rw [Subring.coe_mul, this]
    simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have e4 := congrArg ρ e3
  rw [map_mul, hρ, one_mul] at e4
  simp only [map_sum, map_mul, e2, mul_zero, Finset.sum_const_zero] at e4
  exact e4

theorem transv_entry (S : Subring A) (p : S) (β β₀ : GL (Fin n) A) (i j : Fin n) (z : Matrix (Fin n) (Fin n) S)
    (h : (p : A) • (β.1 * z.map S.subtype * (β⁻¹).1) =
      (p : A) • (β₀.1 * (Matrix.transvection i j (1 : S)).map S.subtype * (β₀⁻¹).1)) (a b : Fin n) :
    (p : A) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈ S := by
  have h2 := congrArg (fun M => (β⁻¹).1 * M * β.1) h
  have e0 : (Matrix.transvection i j (1 : S)).map S.subtype = 1 + Matrix.single i j (1 : A) := by
    rw [Matrix.transvection, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single,
      map_one]
  have e1 : (β⁻¹).1 * (β.1 * z.map S.subtype * (β⁻¹).1) * β.1 = z.map S.subtype := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have e2 : (β⁻¹).1 * (β₀.1 * (1 + Matrix.single i j (1 : A)) * (β₀⁻¹).1) * β.1 =
      1 + ((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Units.inv_mul, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_smul, Matrix.smul_mul] at h2
  rw [e0, e1, e2] at h2
  have h3 := congrFun (congrFun h2 a) b
  have e3 : (((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1) a b =
      ((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b := by
    generalize ((β₀⁻¹ * β)⁻¹).1 = M
    generalize (β₀⁻¹ * β).1 = N
    simp [Matrix.mul_apply, Matrix.single, ite_and]
  simp only [Matrix.smul_apply, Matrix.add_apply, e3, smul_eq_mul, Matrix.map_apply, Subring.subtype_apply, mul_add] at h3
  rw [← sub_eq_iff_eq_add'] at h3
  rw [← h3]
  refine S.sub_mem (S.mul_mem p.2 (z a b).2) (S.mul_mem p.2 ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

end Alg

end GlobalTheory.PrinFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrinFrame

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem redFn_eq_one_of_le (V : HSp D) (β β₀ : GL (Fin V.rank) (Lev.EAf D))
    (h₀ : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat V V.L0))
    (hle : ∀ κ ∈ GfC V, finE V κ ∈ Formalism.L2.DIV.St β₀ → finE V κ ∈ Formalism.L2.DIV.St β)
    (P : Formalism.L2.DIV.Pl D.host.E) (hP : ¬ Formalism.IndefR.Lev.IsConjPl P P) (x : GL (Fin V.rank) (Lev.EAf D))
    (hx : x ∈ Formalism.L2.DIV.St β) (hx₀ : x ∈ Formalism.L2.DIV.St β₀) (h1 : redFn β P x = 1) : redFn β₀ P x = 1 := by
  obtain ⟨β₁, h₁⟩ := GlobalTheory.StdFrames.exists_base V
  obtain ⟨c, hc⟩ := GlobalTheory.StdFrames.isSD_one h₁
  have hB : IsBaseFrame V β₀ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ c) := ⟨h₀, hc.2⟩
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hP
  obtain ⟨p, hp, hpp, hres⟩ := GlobalTheory.ParahoricLift.exists_idem_int he
  have hoff : ∀ i j, i ≠ j → ∀ a b, (p : Lev.EAf D) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j hij
    have hu' : p * (Matrix.transvection i j (1 : Formalism.L2.Herm.intAf D.host.F D.host.E)).det = p := by
      rw [Matrix.det_transvection_of_ne i j hij, mul_one]
    have hmm := GlobalTheory.ParahoricLift.conj_inv_part β₀ p p _ hu' hpp
    rw [hp] at hmm
    obtain ⟨κ, hs, hκ⟩ := GlobalTheory.ParahoricLift.split_lift_fin V he.1 _ _ hmm
    have hPI : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
    obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hsf := GlobalTheory.LevSplit.supp_fin V (f := e + cA D e) hs
    rw [← hp] at hκ
    have hf : GlobalTheory.LevSplit.finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
      rw [RingHom.map_add, GlobalTheory.LevSplit.finSw_cA, hp]
    have hSt : finE V κ ∈ Formalism.L2.DIV.St β₀ :=
      GlobalTheory.ParahoricLift.mem_St_of_part D.sp.cm.sig V.gram _ β₀ hB.1 (GlobalTheory.ParahoricLift.hatL_selfDual hB) p p hpp
        (GlobalTheory.LevSplit.sigR_int p.2) _ hu' (finE V κ) (GlobalTheory.LevSplit.finE_mem_UA V κ) _ hf hsf hκ
    obtain ⟨z, hz⟩ := hle κ ((T3 P e _ hPI).2.2.1 κ hs) hSt
    rw [← hz] at hκ
    exact transv_entry _ p β β₀ i j z.1 hκ
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y₀, hy₀⟩ := hx₀
  rw [redFn_frGL] at h1
  rw [← hy₀, redFn_frGL]
  have e1 : intGL D.host.F D.host.E V.rank y₀ = (β₀⁻¹ * β) * intGL D.host.F D.host.E V.rank y * (β₀⁻¹ * β)⁻¹ := by
    have e2 : β₀ * intGL D.host.F D.host.E V.rank y₀ * β₀⁻¹ = β * intGL D.host.F D.host.E V.rank y * β⁻¹ := hy₀
    rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq] at e2
    rw [e2]
    group
  exact Units.ext (red_conj_eq_one _ (resS D.host.F P) p hres (β₀⁻¹ * β) (conj_single_mem _ p hpp _ hoff) y.1 y₀.1
    (congrArg Units.val e1) (congrArg Units.val h1))

theorem kset_iff_finE (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h

theorem edgeSum_symEdge_one {k : Type} [CommRing k] {n : ℕ} (ρ l : ℕ) : edgeSum (symEdge ρ l) (1 : GL (Fin n) k) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    rintro rfl
    unfold symEdge at h
    omega
  · rfl

theorem rowChi_eq_one : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), GlobalTheory.Core.Mi.IdE X → ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St β) ↔ ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) → ∀ κ ∈ rowJ X h, (∀ PP ∈ Pg, redFn β PP (finE (D.sp.Y 0) κ) = 1) → rowChi X h κ = 1 := by
  intro D X h _ Pg hPg hIdem β hβ κ hκ hred
  have hnc := GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hPg hIdem
  have hψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI := PP.isPrime
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ0 hψ0 using hψ
  obtain ⟨β₀, h₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hPg hnc ψ0 fun PP _ => hψ0 PP
  have hle : ∀ κ ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β₀ → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β :=
    fun κ h1 h2 => ((hβ κ).2 ⟨(GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).2 h1, (kset_iff_finE X h β₀ h₀ κ).2 h2⟩).2
  have hS₀ := ((hK κ).1.1 hκ.2).1
  have hS := hle κ ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).1 hκ.1) hS₀
  refine ((hK κ).2 hκ.2).trans (Finset.prod_eq_one fun PP hPP => ?_)
  rw [redFn_eq_one_of_le (D.sp.Y 0) β β₀ h₀ hle PP (hnc PP hPP PP hPP) _ hS hS₀ (hred PP hPP), edgeSum_symEdge_one,
    AddChar.map_zero_eq_one]

end GlobalTheory.PrinFrame

end
