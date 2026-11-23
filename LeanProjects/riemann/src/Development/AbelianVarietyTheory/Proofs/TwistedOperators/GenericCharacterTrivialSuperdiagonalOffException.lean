import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingSelfDualCompletionIntegralAtPlacStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryWittIsotropicCoordinateEqPairingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemSpanStaircaseIdealProductsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentMulIntegralOfUnitFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentSmulMemLatticeCompletionAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.UniOff

open GlobalTheory.FinPlLoc (idem idem_mem_idAt idem_mem_intAt idem_mul_self cA_idem mem_idAt_iff ePl ePl_int evalV_ePl)

theorem intAt_neg {D : D7} {v : GlobalTheory.FinPl.Pl D} {z : AE D} (h : z ∈ intAt D (· = v)) : -z ∈ intAt D (· = v) :=
  ⟨neg_mem h.1, by rw [map_neg]; exact neg_mem h.2⟩

theorem intAt_add {D : D7} {v : GlobalTheory.FinPl.Pl D} {z w : AE D} (h : z ∈ intAt D (· = v)) (h' : w ∈ intAt D (· = v)) :
    z + w ∈ intAt D (· = v) :=
  ⟨add_mem h.1 h'.1, by rw [map_add]; exact add_mem h.2 h'.2⟩

theorem idem_incA_mem {D : D7} (v : GlobalTheory.FinPl.Pl D) (o : 𝓞 D.host.E) :
    idem D (· = v) * incA D (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [map_mul, GlobalTheory.IdeleAA.finPart_incA]
  unfold idem
  rw [GlobalTheory.FinPlLoc.finPart_pair, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, o, rfl⟩

theorem idem_incA {D : D7} (P : GlobalTheory.FinPl.Pl D → Prop) (e : D.host.E) :
    idem D P * incA D e = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] e := by
  unfold idem
  show (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gen_mem {D : D7} (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D)
    (P : GlobalTheory.FinPl.Pl D → Prop) (hP : ∀ w, ¬ P w → w ≠ v) {a : D.host.E} (ha : a ∈ 𝔞) {x : Fin S.rank → D.host.E}
    (hx : x ∈ L) : (fun m => idem D (· = v) * incA D (a * x m)) ∈ GlobalTheory.FinPl.latMul S 𝔞 L P := by
  apply AddSubgroup.subset_closure
  refine ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg (hP w hw)], a, ha, x, hx, ?_⟩
  funext m
  exact idem_incA _ _

theorem col_mem {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (p : Fin c) {t : D.host.E} (ht : t ∈ 𝔟 p) : (fun m => t * d.a m p) ∈ d.lat Λ 𝔟 := by
  classical
  refine ⟨0, Λ.zero_mem, Pi.single p t, fun q => ?_, ?_⟩
  · by_cases hq : q = p
    · subst hq; simpa using ht
    · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
  · funext m
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem uni_off : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  intro D _ T L _ _ sc G W _ _ F hF ρ h M hM i j hij v hv o ho
  classical
  have h1 : 1 ≤ 2 * ρ + 2 := by omega
  have h1' : 1 ≤ 2 * ρ + 1 := by omega
  have h2' : 2 * ρ + 1 ≤ D.R.m := by omega
  obtain ⟨hleB, heB, -, -⟩ := hF.hB ρ h

  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D W.ψ W.ψ_std
  obtain ⟨hA, hψ⟩ := hα v

  have sdV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ fun j hj => by
      obtain ⟨h3, -⟩ := Node.grid.inj hj; omega).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1) 0) ⟨h2', Nat.zero_le _⟩ fun j hj => by
      obtain ⟨h3, -⟩ := Node.grid.inj hj; omega).sd
  have hMlat := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ (isSelfDualC_neg sdV) sdW (fun _ => True) M).1 hM.1

  set aB := (G.colDec (2 * ρ + 2) h1 h).a with haB
  set aJ := (G.colDec (2 * ρ + 1) h1' h2').a with haJ
  set p : Fin (2 * ρ + 2 - 1) := Fin.castLE (by omega) j with hp
  have hq : 2 * ρ - 1 - i.1 < 2 * ρ + 1 - 1 := by omega
  set q : Fin (2 * ρ + 1 - 1) := ⟨2 * ρ - 1 - i.1, hq⟩ with hqdef
  set colB : Fin (G.V (.grid (2 * ρ + 2) 0)).rank → AE D := fun l => incA D (aB l p) with hcolB
  set g : AE D := ∑ k, ∑ l, cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) * (M *ᵥ colB) l
    with hg

  have hcol : ∀ k, (M ⬝ (F.dB ρ h).jX) k j = incA D ((-D.host.xi0) ^ (j.1 + 1)) * (M *ᵥ colB) k := by
    intro k
    simp only [Matrix.mul_apply, GlobalTheory.MixModel.HypDec.jX, heB, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [GlobalTheory.MixModel.rat, Matrix.map_apply, colsOf, hcolB, map_mul, map_pow, hp]
    ring
  have hN : ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j = incA D (-D.host.xi0) * g := by
    have e1 : ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j = ((F.dJ ρ h).pX *ᵥ fun k => (M ⬝ (F.dB ρ h).jX) k j) i := rfl
    have e2 := GlobalTheory.T.auxiliaryWittIsotropicCoordinate_eq_pairing (G.colDec (2 * ρ + 1) h1' h2') (F.dJ ρ h) (by omega) (hF.hJ ρ h) i hq
      (fun k => (M ⬝ (F.dB ρ h).jX) k j)
    rw [← e1] at e2
    simp only [hcol] at e2
    have e3 : incA D ((-D.host.xi0) ^ (i.1 + 1)) * (incA D (-D.host.xi0) * g) =
        ∑ k, ∑ l, cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) *
          (incA D ((-D.host.xi0) ^ (j.1 + 1)) * (M *ᵥ colB) l) := by
      rw [hg, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hp1 : (-D.host.xi0) ^ (j.1 + 1) = (-D.host.xi0) ^ (i.1 + 1) * (-D.host.xi0) := by rw [hij, pow_succ]
      rw [hp1, map_mul]
      ring
    have hunit : incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * incA D ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)), map_one]
    calc ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j
        = (incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * incA D ((-D.host.xi0) ^ (i.1 + 1))) *
          ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j := by rw [hunit, one_mul]
      _ = incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * (incA D ((-D.host.xi0) ^ (i.1 + 1)) *
          (incA D (-D.host.xi0) * g)) := by rw [mul_assoc, e2, ← e3]
      _ = incA D (-D.host.xi0) * g := by rw [← mul_assoc, hunit, one_mul]

  set Φ : D.host.E → AE D := fun t => ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
    (idem D (· = v) * incA D t * g) with hΦ
  have hgen : ∀ t ∈ {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c}, Φ t ∈ intAt D (· = v) := by
    rintro t ⟨a, ha, c', hc', c, hc, rfl⟩
    have hxB : (fun m => c * aB m p) ∈ G.Λ (.grid (2 * ρ + 2) 0) := by
      have e := G.sp.colLat (2 * ρ + 2) h1 h
      show _ ∈ (vtxOf L G.sp.Vs (2 * ρ + 2) 0).lat
      rw [e]
      exact col_mem (G.colDec (2 * ρ + 2) h1 h) _ _ p hc
    have hxJ : (fun m => c' * aJ m q) ∈ G.Λ (.grid (2 * ρ + 1) 0) := by
      have e := G.sp.colLat (2 * ρ + 1) h1' h2'
      show _ ∈ (vtxOf L G.sp.Vs (2 * ρ + 1) 0).lat
      rw [e]
      exact col_mem (G.colDec (2 * ρ + 1) h1' h2') _ _ q hc'
    set y : Fin (G.V (.grid (2 * ρ + 2) 0)).rank → AE D := fun m => idem D (· = v) * incA D (1 * (c * aB m p)) with hy
    have hyT : y ∈ latV (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) :=
      gen_mem _ {1} _ v _ (fun w hw => absurd trivial hw) rfl hxB
    set w : Fin (G.V (.grid (2 * ρ + 1) 0)).rank → AE D := fun m => idem D (· = v) * incA D (a * (c' * aJ m q)) with hw
    have hwv : w ∈ latA (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) :=
      gen_mem _ {a | a ∈ D.host.AA} _ v _ (fun w hw => hw) ha hxJ
    have hMy : M *ᵥ y ∈ latA (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := hMlat.2 y hyT
    have hMy' := GlobalTheory.T.adeleIdempotent_smul_mem_latticeCompletionAtPlace D _ _ _ v _ hMy
    have hyy : idem D (· = v) • (M *ᵥ y) = M *ᵥ y := by
      rw [← Matrix.mulVec_smul]
      congr 1
      funext m
      simp only [hy, Pi.smul_apply, smul_eq_mul, ← mul_assoc, idem_mul_self]
    rw [hyy] at hMy'
    have z1 := (hA _ _ _).1 hMy'
    have z2 := (hA _ _ _).1 hwv
    have hP := GlobalTheory.T.hermitianPairing_selfDual_completion_integral_at_place D _ _ sdW v _ _ z1 z2
    have hw' : ∀ k, cA D ((((α⁻¹ : (AE D)ˣ) : AE D) • w) k) = cA D ((α⁻¹ : (AE D)ˣ) : AE D) * idem D (· = v) *
        incA D (D.host.conj (a * c')) * cA D (incA D (aJ k q)) := by
      intro k
      simp only [hw, Pi.smul_apply, smul_eq_mul, map_mul, cA_idem, GlobalTheory.IdeleAA.cA_incA]
      ring
    have hz' : ∀ l, (((α⁻¹ : (AE D)ˣ) : AE D) • (M *ᵥ y)) l = ((α⁻¹ : (AE D)ˣ) : AE D) * (idem D (· = v) * incA D c) *
        (M *ᵥ colB) l := by
      intro l
      rw [Pi.smul_apply, smul_eq_mul]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hy, hcolB]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [one_mul, map_mul]
      ring
    have hI := idem_mul_self (D := D) (· = v)
    convert hP using 1
    simp only [hw', hz', hΦ, hg, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    linear_combination (-(((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * incA D (D.host.conj a) * incA D (D.host.conj c') *
      incA D c * (cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) * (M *ᵥ colB) l))) * hI
  have hspan : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c}, Φ t ∈ intAt D (· = v) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact hgen t ht
    | zero =>
      have : Φ 0 = 0 := by simp only [hΦ, map_zero, mul_zero, zero_mul]
      rw [this]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      have : Φ (x + y) = Φ x + Φ y := by simp only [hΦ, map_add]; ring
      rw [this]; exact intAt_add hx hy
    | smul o x _ hx =>
      have hI := idem_mul_self (D := D) (· = v)
      have : Φ (o • x) = (idem D (· = v) * incA D (o : D.host.E)) * Φ x := by
        rw [Algebra.smul_def]
        simp only [hΦ, map_mul]
        linear_combination (-(((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
          incA D (algebraMap (𝓞 D.host.E) D.host.E o) * incA D x * g)) * hI
      rw [this]; exact GlobalTheory.IdeleAA.intAt_mul (idem_incA_mem v o) hx
  obtain ⟨u, hu, hus⟩ := GlobalTheory.T.exists_unit_mem_span_staircaseIdeal_products G ρ p q (by simp [hp, hqdef]; omega) v hv
  have hz : idem D (· = v) * (((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * g) ∈ intAt D (· = v) := by
    refine GlobalTheory.T.adeleIdempotent_mul_integral_of_unit_factor D v u hu _ ?_
    have := hspan _ hus
    simp only [hΦ] at this
    convert this using 1; ring

  have hs : idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : incA D D.host.xi0⁻¹ * ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
      (idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) ∈ intAt D (· = v) := by
    have hx0 : incA D D.host.xi0⁻¹ * incA D (-D.host.xi0) = -1 := by
      rw [← map_mul, mul_neg, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_neg, map_one]
    rw [hN]
    convert intAt_neg hz using 1
    linear_combination (((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * idem D (· = v) * g) * hx0
  have hoid : idem D (· = v) * o = o := (mem_idAt_iff _ o).1 ho.1
  have := (hψ _ hs).2 key o ho
  rw [← hoid]
  convert this using 2
  ring

end GlobalTheory.UniOff
