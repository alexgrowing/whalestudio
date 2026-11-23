import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootsBarEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInOfIsCharLab

noncomputable section

namespace GlobalTheory.SerSys.Bridge

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf
open scoped Classical

local instance factT (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem trace_alg {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ a) = tr a τ.character := by
  have e : Representation.asAlgebraHom τ.ρ a = ∑ x, a.coeff x • τ.ρ x :=
    LinearMap.ext fun w => by rw [alg_apply, LinearMap.sum_apply]; rfl
  rw [e, map_sum, tr]
  exact Finset.sum_congr rfl fun x _ => map_smul _ _ _

section Finite

variable {g : ℕ} [Fact g.Prime]

theorem tr_eSerC_eq (L : LabelDatum g) {n : ℕ} {χ : Gn g n → ℂ} {f : (ZMod g)[X]} (hχ : IsIrr χ)
    (hf : HasLabel L χ f) : tr (eSerC L n f) χ = χ 1 ∧ χ 1 ≠ 0 := by
  have hfin := (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1
  have hz : eSerC L n f * zOf χ = 1 * zOf χ := by
    rw [eSerC_eq_sum L n hfin, Finset.sum_mul, Finset.sum_eq_single_of_mem χ (by simp [hχ, hf]), one_mul]
    · simpa using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).1
    · intro b hb hne
      have hb' : IsIrr b := by simpa using (Finset.mem_filter.1 hb).1
      rw [(GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ b χ hb' hχ).1, if_neg hne]
  have h := congrArg (fun a : MonoidAlgebra ℂ (Gn g n) => a.coeff 1) hz
  simp only [(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ _ χ).2.2] at h
  obtain ⟨d, hd, e⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ 1 χ).2.1 hχ
  have h1 : χ 1 ≠ 0 := e ▸ Nat.cast_ne_zero.2 hd.ne'
  rw [MonoidAlgebra.one_def, Opp.tr_single, one_mul] at h
  exact ⟨mul_left_cancel₀ (div_ne_zero h1 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) h, h1⟩

theorem hasLabel_of_isCuspOf (L : LabelDatum g) {d : ℕ} {P : (ZMod g)[X]} {χ : Gn g d → ℂ} (h : IsCuspOf L P χ) :
    HasLabel L χ P := by
  have hχ : IsIrr χ := h.2.1.2.1
  refine ⟨[(P, ⟨d, χ⟩)], fun p hp => by rw [List.mem_singleton.1 hp]; exact h, by simp [degL], by simp, ?_⟩
  have hc : IsClass χ := fun x y => by
    obtain ⟨V, -, hV⟩ := hχ
    rw [← hV, ← hV, FDRep.char_conj]
  have e : hcL ([(P, (⟨d, χ⟩ : Pc g))].map Prod.snd) d = χ := GLq.Model.hc_full χ hc
  rw [e, (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).2.2, if_pos rfl]
  exact one_ne_zero

theorem labelsCusp (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) :
    TameGen.LabelsCusp (OfLabel.ofLabel L h5 hG) L := fun d τ P hP h0 => by
  obtain ⟨h1, h2⟩ := tr_eSerC_eq L hP.2.1.2.1 (hasLabel_of_isCuspOf L hP)
  rw [← trace_alg] at h1
  exact h2 (h1.symm.trans ((congrArg _ h0).trans (map_zero _)))

end Finite

theorem five_le (D : D7) (k : Fin 2) : 5 ≤ D.host.g k := by
  have hc := D.ntypes.g_cond k
  have h4 : D.host.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        ((((show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd).mul_right _).mul_right _)), hc]
  have := (D.host.g_prime k).two_le
  omega

theorem labParam_of (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameGen.TameParam (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) :
    LabParam D L rc := fun k v n π hπ f hf =>
  TameGen.ine_eq_of_has_green (OfLabel.ofLabel (L k) (five_le D k) hG) (L k) _ _ _ (h1 k v) (h2 k) hG (h3 k v)
    (labelsCusp _ _ _) ⟨n, π⟩ hπ.1 hπ.2 f hf

theorem serLoc_of (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : LocComp D rc) (hP : LabParam D L rc) : SerLoc D :=
  have hS : ∀ k, (OfLabel.ofLabel (L k) (five_le D k) hG).IsOf (L k) := fun _ _ _ => rfl
  GlobalTheory.SerLocal.serLoc D _ (hL.sysTie hS) hU (locType_of_ties hL hS hC hP)

theorem serLoc_of_ties (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : LocComp D rc)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameGen.TameParam (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) : SerLoc D :=
  serLoc_of D L rc hG hL hU hC (labParam_of D L rc hG h1 h2 h3)

end GlobalTheory.SerSys.Bridge
