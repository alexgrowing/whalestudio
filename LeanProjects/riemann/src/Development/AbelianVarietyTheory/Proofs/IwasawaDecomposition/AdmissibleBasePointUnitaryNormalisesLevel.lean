import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
import Formalism.LocalToGlobal.Columns.RecLevelLocK
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLastRowDivisibleStabilizesLatticesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionEqBasePiMulIntegralStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

section Small
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem row_small_of_mul_eq_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (l : Fin n) (M N : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (hMN : M * N = 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) (hM : ∀ j, j ≠ l → Valued.v (M l j) < 1)
    (hl : Valued.v (M l l) = 1) (j : Fin n) (hj : j ≠ l) : Valued.v (N l j) < 1 := by
  have e := congrFun (congrFun hMN l) j
  rw [Matrix.mul_apply, Matrix.one_apply_ne (Ne.symm hj), ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at e
  have e2 : M l l * N l j = -∑ i ∈ Finset.univ.erase l, M l i * N i j := eq_neg_of_add_eq_zero_left e
  have h3 : Valued.v (∑ i ∈ Finset.univ.erase l, M l i * N i j) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun i hi => by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hN i j)) (hM i (Finset.ne_of_mem_erase hi))
  have h4 := congrArg Valued.v e2
  rw [Valuation.map_neg, map_mul, hl, one_mul] at h4
  rw [h4]
  exact h3

theorem val_eq_one_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c)
    (hc : c ≠ 0) : Valued.v z = 1 := by
  obtain ⟨r, rfl, hr⟩ := h
  have hr0 : r ∉ P.asIdeal := fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.2 h0)
  have ha : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) = 1 := by
    rw [valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hr0
  have e : z = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) +
      (z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) := by ring
  rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [ha]; exact hr), ha]

theorem prV_sigR_eq (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul a b => simp [prV, sigR]

variable [StarRing E]

theorem bc_prV_mem_UPts (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (AfE F E)}
    (hk : k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) v) k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := by
  have hg' : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (k : Matrix (Fin n) (Fin n) _) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hk
  change cT (sigR hc.sig (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F))
  have h1 : cT (sigR hc.sig (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
    ext i j
    simp [cT, prV_sigR_eq]
  have hJ : ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    simp [Matrix.one_apply]
  rw [h1, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end Small

theorem map_conj_levStab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E)) (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (E ⊗[F] v.adicCompletion F)), k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → k ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) → k ∈ stabGL (baseDualV hc n ST v) → k ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj k).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  intro F E _ _ _ _ _ _ hc n _ ST v k hU h1 h2 h3
  have key : ∀ g : GL (Fin n) (E ⊗[F] v.adicCompletion F), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) →
      g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) → g ∈ stabGL (baseDualV hc n ST v) →
      g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) →
      ∀ x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v),
      g * x * g⁻¹ ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
    intro g gU gL gD gK x hx
    have hgl : g ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) := Subgroup.mem_inf.2 ⟨gU, gL⟩
    obtain ⟨hxl, hxD, hxf⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgl hxl) (inv_mem hgl), ⟨mul_mem (mul_mem gD hxD) (inv_mem gD), fun y => ?_⟩⟩
    have hz : ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) ∈
        baseDualV hc n ST v := ((inv_mem gD : g⁻¹ ∈ stabGL (baseDualV hc n ST v)) _).1 y.2
    have h4 := hxf ⟨_, hz⟩
    simp only [fLoc, Submodule.mkQ_apply] at h4 ⊢
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at h4 ⊢
    simp only [Submodule.coe_subtype, Submodule.coe_sub] at h4 ⊢
    have e : ((g * x * g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) -
        (y : Fin n → E ⊗[F] v.adicCompletion F) =
        (g : Matrix (Fin n) (Fin n) _) *ᵥ ((x : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F)) -
          ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F)) := by
      have e1 : (g : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ
          (y : Fin n → E ⊗[F] v.adicCompletion F)) = (y : Fin n → E ⊗[F] v.adicCompletion F) := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : ((g * x * g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) =
          (g : Matrix (Fin n) (Fin n) _) *ᵥ ((x : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ
          (y : Fin n → E ⊗[F] v.adicCompletion F))) := by
        simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [Matrix.mulVec_sub, e2, e1]
    rw [e]
    exact (gK _).1 h4
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key k hU h1 h2 h3 x hx
  · intro x hx
    refine ⟨k⁻¹ * x * k, ?_, ?_⟩
    · have := key k⁻¹ (inv_mem hU) (inv_mem h1) (inv_mem h2) (inv_mem h3) x hx
      rwa [inv_inv] at this
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group

set_option maxHeartbeats 1000000 in

theorem basePt_facts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (k : GL (Fin n) (AfE F E)) (c : DiaG E ST), (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → k ∈ UAd hc n ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) ∧ (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, k.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) ∧ ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) k)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  intro F E _ _ _ _ _ _ hc n _ ST π hB k c ⟨p₀, hk, hk0⟩ hrow
  classical
  have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
  have hU : k ∈ UAd hc n := hk.uni
  have hkc := hk.lat
  rw [hk0] at hkc
  have hsingle : ∀ j, (Pi.single j 1 : Fin n → AfE F E) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := fun j => by
    refine (mem_latS_std _).2 fun i => ?_
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hInv : ∀ i j, ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E :=
    fun i j => by
      have := (mem_latS_std _).1 ((hkc _).1 (hsingle j)) i
      rw [Matrix.mulVec_single_one] at this; exact this
  have hK : ∀ i j, ((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E :=
    fun i j => by
      have h1 : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((k : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hsingle j
      have := (mem_latS_std _).1 ((hkc _).2 h1) i
      rw [Matrix.mulVec_single_one] at this; exact this
  have hvI : ∀ (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E), y ∈ Formalism.L2.Herm.intAf F E → Valued.v (adAt F P y) ≤ 1 :=
    fun P y hy => (mem_rInt_iff F E y).1 hy P
  have hsm : ∀ P ∈ ST, ∀ j, j ≠ lastIdx n →
      Valued.v (adAt F P ((k : Matrix (Fin n) (Fin n) (AfE F E)) (lastIdx n) j)) < 1 := by
    intro P hP j hj
    have hr := fun j' => hrow ⟨P, hP⟩ (lastIdx n) j' hl
    refine row_small_of_mul_eq_one (lastIdx n) (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P))
      ((k : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P)) ?_ (fun i j => hvI P _ (hK i j)) (fun j' hj' => ?_) ?_ j hj
    · rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have := hr j'
      rw [if_neg hj'] at this
      exact DilPt.hasRes_lt_one this
    · have h5 := hr (lastIdx n)
      rw [if_pos rfl] at h5
      have := P.isPrime
      exact val_eq_one_of_hasRes h5 (Units.ne_zero _)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) k ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧
      bc (prV (E := E) v) k ∈ stabGL (baseDualV hc n ST v) ∧
      bc (prV (E := E) v) k ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
    intro v
    refine GlobalTheory.T.unitary_lastRowDivisible_stabilizes_lattices hc n hB v _ (bc_prV_mem_UPts hc v hU)
      ⟨fun i j => Formalism.UG.P.afsplit_prV_int v _ (hK i j), fun j hj => GlobalTheory.T.placeProjection_eq_basePi_mul_integral hB v _ (hK _ j) (fun P hP => hsm P hP j hj)⟩ ?_
    rw [← map_inv]
    refine ⟨fun i j => Formalism.UG.P.afsplit_prV_int v _ (hInv i j), fun j hj => GlobalTheory.T.placeProjection_eq_basePi_mul_integral hB v _ (hInv _ j) (fun P hP => ?_)⟩
    have := hrow ⟨P, hP⟩ (lastIdx n) j hl
    rw [if_neg hj] at this
    exact DilPt.hasRes_lt_one this
  refine ⟨hU, fun v => ⟨bc_prV_mem_UPts hc v hU, (hloc v).1⟩, fun x => ?_,
    fun v _ => map_conj_levStab hc n ST v _ (bc_prV_mem_UPts hc v hU) (hloc v).1 (hloc v).2.1 (hloc v).2.2⟩
  rw [GlobalTheory.LatLocGlob.mem_latS_adele_iff _ (baseLb_fin n ST), GlobalTheory.LatLocGlob.mem_latS_adele_iff _ (baseLb_fin n ST)]
  refine forall_congr' fun v => ?_
  have e : (fun i => prV (E := E) v ((k.1 *ᵥ x) i)) =
      ((bc (prV (E := E) v) k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun i => prV (E := E) v (x i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [e]
  exact ((hloc v).1 _).symm

end GlobalTheory.Mem.Col2.ChEx
