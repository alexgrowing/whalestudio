import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.BotSmallTransl

open GlobalTheory.PlaceModel GlobalTheory.LocReduction Formalism.IndefR.Fin.LevelGroupLemmas.Lat
open scoped TensorProduct

variable {D : D7}

theorem mul_finOne {z : Formalism.L2.Theta.AE D} (hz : infPart D z = 0) :
    z * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = z := by
  have h : finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := rfl
  conv_lhs => rw [eq_lift_of_infPart z hz]
  rw [lift_mul, h, mul_one, ← eq_lift_of_infPart z hz]

theorem one_mem_AA (h : D.host.ccK = ⊤) : (1 : D.host.E) ∈ D.host.AA := by
  have h1 : (1 : D.host.E) ∈ D.host.AA0 := by
    refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  rwa [Host.AA, Host.ccE, h, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

theorem single_mem {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : IsStdLat L) (j : Fin n) :
    (Pi.single j 1 : Fin n → D.host.E) ∈ L :=
  (h _).2 fun i => by
    by_cases hi : i = j
    · exact ⟨1, by rw [hi, Pi.single_eq_same]; rfl⟩
    · exact ⟨0, by rw [Pi.single_eq_of_ne hi]; rfl⟩

variable {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem mem_latO_of_int (hc : D.host.ccK = ⊤) (hG : S.gram = 1) (hS : IsStdLat LS) (hT : IsStdLat LT) {t : WO S T}
    (h0 : ∀ i j, infPart D (t i j) = 0) (h1 : ∀ i j, finPart D (t i j) ∈ intAE D) :
    t ∈ latO S T LS LT fun _ => True := by
  have e : t = ∑ i, ∑ j, t i j • genL S T 1 1 (Pi.single j 1) (Pi.single i 1) := by
    ext k l
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, genL, Matrix.of_apply, hG]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
    · have : (1 : D.host.E) * (Pi.single k 1 : Fin T.rank → D.host.E) k *
          ∑ m, star ((Pi.single l 1 : Fin S.rank → D.host.E) m) * (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) m l = 1 := by
        simp [Matrix.one_apply]
      rw [this, mul_finOne (h0 k l)]
    · intro j _ hj
      have : (1 : D.host.E) * (Pi.single k 1 : Fin T.rank → D.host.E) k *
          ∑ m, star ((Pi.single j 1 : Fin S.rank → D.host.E) m) * (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) m l = 0 := by
        simp [Matrix.one_apply, Pi.single_eq_of_ne hj.symm]
      rw [this, TensorProduct.tmul_zero, mul_zero]
    · exact fun h => (h (Finset.mem_univ _)).elim
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Pi.single_eq_of_ne hi.symm, mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]
    · exact fun h => (h (Finset.mem_univ _)).elim
  rw [e]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => smul_mem_latAll (h1 i j) ?_
  exact genL_mem (fun v => by rw [map_one]; exact one_mem _) (one_mem_AA hc) (single_mem hS j) (single_mem hT i)

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem heis_off (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {vac : WO S T → ℂ} (hv : IsThetaFunO ψ S T vac)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm)
    (hfix : ∀ u ∈ latO S T LS LT fun _ => True, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u vac = vac)
    {u : WO S T} (h1 : ∀ x, IsHalf (cA D e) x → symplO S T u x = 0)
    (h2 : ∀ x, IsHalf (cA D (cA D e)) x → symplO S T u x = 0) {c : ℂ} (hc : c ≠ 0) (hu : heisO ψ S T u vac = c • vac)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf (cA D e) (latO S T LS LT fun _ => True) Φ) :
    heisO ψ S T u (Tm Φ) = c • Tm Φ := by
  obtain ⟨T0, -, huniq, -⟩ := Formalism.IndefR.Fin.placeModelAtF D ψ hψ S T LS LT hS hT P e he vac hv hfix (cA D e) (Or.inr rfl)
  have ap : ∀ Φ, (c⁻¹ • (heisL S T ψ u ∘ₗ Tm)) Φ = c⁻¹ • heisO ψ S T u (Tm Φ) := fun _ => rfl
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac
      (c⁻¹ • (heisL S T ψ u ∘ₗ Tm)) := by
    refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ x hx => ?_, ?_⟩
    · rw [ap, ap, hTm.trans Φ hΦ x hx, heis_comm, h1 x hx, AddChar.map_zero_eq_one, one_smul, heis_smul]
    · rw [ap, ap, hTm.modul Φ hΦ x hx, heis_comm, h2 x hx, AddChar.map_zero_eq_one, one_smul, heis_smul]
    · rw [ap, hTm.vac, hu, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h := (huniq _ hT' Φ hΦ).trans (huniq _ hTm Φ hΦ).symm
  rw [ap] at h
  rw [← h, smul_smul, mul_inv_cancel₀ hc, one_smul, h]

set_option maxHeartbeats 1600000 in

theorem heis_model (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {vac : WO S T → ℂ} (hv : IsThetaFunO ψ S T vac)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm)
    {w : WO S T} (hw : w ∈ latO S T LS LT fun _ => True) {c : ℂ} (hc : c ≠ 0) (hu : heisO ψ S T w vac = c • vac)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf (cA D e) (latO S T LS LT fun _ => True) Φ)
    (hsupp : ∀ t, Φ t ≠ 0 → t ∈ latO S T LS LT fun _ => True) :
    heisO ψ S T w (Tm Φ) = c • Tm fun t => Φ (t + cA D e • w) := by
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hec := he.2
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hLL := (lattice_facts (S := S) (T := T) hψ hS hT hcc hinf).1
  have hb : cA D (cA D e) = e := GlobalTheory.DualPairCheck.cA_cA e
  have hfix : ∀ u ∈ latO S T LS LT fun _ => True, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u vac = vac :=
    fun u hu h => h.elim (fun h => fix_conj hLL hTm hu (by rwa [hb])) fun h => fix_half hTm hu h
  have hA : IsHalf (cA D e) (cA D e • w) := isHalf_smul.2 (by rw [smul_smul, hcc])
  have hB : IsHalf e (e • w) := isHalf_smul.2 (by rw [smul_smul, hee])
  have hAL := GlobalTheory.PlaceModelSum.idem_smul_latO hcc hw
  have hBL := GlobalTheory.PlaceModelSum.idem_smul_latO hee hw
  have k : cA D (1 - cA D e - e) = 1 - e - cA D e := by rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, hb]
  have h1 : ∀ x : WO S T, IsHalf (cA D e) x → symplO S T ((1 - cA D e - e) • w) x = 0 := fun x hx => by
    have : (1 - e - cA D e) * cA D e = 0 := by linear_combination -hec - hcc
    rw [← isHalf_smul.1 hx, symplO_smul, k, smul_smul, this, zero_smul, symplO_zero_right]
  have h2 : ∀ x : WO S T, IsHalf e x → symplO S T ((1 - cA D e - e) • w) x = 0 := fun x hx => by
    have : (1 - e - cA D e) * e = 0 := by linear_combination -hec - hee
    rw [← isHalf_smul.1 hx, symplO_smul, k, smul_smul, this, zero_smul, symplO_zero_right]
  have hp : ψ (symplOH S T (cA D e • w) (e • w)) ≠ 0 := (AddChar.val_isUnit ψ _).ne_zero
  have dec : ∀ f, ψ (symplOH S T (cA D e • w) (e • w)) • heisO ψ S T w f =
      heisO ψ S T ((1 - cA D e - e) • w) (heisO ψ S T (cA D e • w) (heisO ψ S T (e • w) f)) := fun f => by
    have e1 : w = (1 - cA D e - e) • w + (cA D e • w + e • w) := by
      rw [← add_smul, ← add_smul, sub_sub, sub_add_cancel, one_smul]
    have e2 : heisO ψ S T (cA D e • w) (heisO ψ S T (e • w) f) =
        ψ (symplOH S T (cA D e • w) (e • w)) • heisO ψ S T (cA D e • w + e • w) f := heisL_heisL S T ψ _ _ f
    rw [e2, heis_smul, ← heis_add (by rw [symplO_add_right, h1 _ hA, h2 _ hB, add_zero]), ← e1]
  have hvu := dec vac
  rw [hfix _ hBL (Or.inl hB), hfix _ hAL (Or.inr hA), hu, smul_smul] at hvu
  have hoff := heis_off hψ hS hT he hv hTm hfix h1 (by rwa [hb]) (mul_ne_zero hp hc) hvu.symm hΦ
  have hm : heisO ψ S T (e • w) (Tm Φ) = Tm Φ := by
    rw [← hTm.modul Φ hΦ _ (by rwa [hb])]
    congr 1
    funext t
    by_cases ht : Φ t = 0
    · rw [ht, mul_zero]
    · rw [hLL t (hsupp t ht) (hΦ.1 t ht) _ hBL (by rwa [hb]), one_mul]
  have hF := dec (Tm Φ)
  rw [hm, heis_comm, h1 _ hA, AddChar.map_zero_eq_one, one_smul, hoff, heis_smul, ← hTm.trans Φ hΦ _ hA, mul_smul] at hF
  exact smul_right_injective _ hp hF

set_option maxHeartbeats 1600000 in

theorem reads_transl : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∀ (G : VC D a d → ℂ) (o : ℕ), Reads ψ θ hS hT ⊤ δ 1 G (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1 (ζ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) G)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o))) := by
  intro D ψ θ S T a d hS hT δ hcc hset LS LT hLS hLT hSd hTd e P c hge hSB κ e0 vac he0 hrd _ Tm hTm G o hG
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hge.1)
  set x := pt D (tor0 D ⊤ δ) δ (unitBlock D o a d) with hx
  have hph : wdPh D (tor0 D ⊤ δ) x ≠ 0 := Complex.exp_ne_zero _
  have hW : ∀ F, Wd D (tor0 D ⊤ δ) x F = wdPh D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x F := fun _ => rfl
  have hfix : Wd D (tor0 D ⊤ δ) x e0 = e0 :=
    GlobalTheory.NormSum.VacMove.wd_fix (GlobalTheory.InducedType.induced_type D).1 hset.crv
      (GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D _) (GlobalTheory.NormSum.VacMove.moves_one D _)) he0
      (pt_unitBlock_mem δ o a d)
  have hU : U D (tor0 D ⊤ δ) x (κ • e0) = (wdPh D (tor0 D ⊤ δ) x)⁻¹ • κ • e0 := by
    have e1 : U D (tor0 D ⊤ δ) x (κ • e0) = κ • U D (tor0 D ⊤ δ) x e0 := by
      funext z
      simp only [U, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [e1, smul_comm]
    conv_rhs => rw [← hfix, hW, smul_smul _ (wdPh D _ x), inv_mul_cancel₀ hph, one_smul]
  have hvac : heisO ψ S T (finPt hS hT 1 (unitBlock D o a d)) vac = (wdPh D (tor0 D ⊤ δ) x)⁻¹ • vac := by
    have h := heisO_finPt_reads ψ θ S T hS hT ⊤ δ 1 hset _ _ hrd (unitBlock D o a d)
    rw [← hx, hU] at h
    exact h.unique (hrd.smul _)
  have hent : ∀ i j, finPt hS hT 1 (unitBlock D o a d) i j =
      if i.1 = o + j.1 then -(pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) else 0 := fun i j => by
    show pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-((1 : D.host.E)⁻¹ * if i.1 = o + j.1 then 1 else 0)) = _
    split_ifs
    · rw [inv_one, mul_one, TensorProduct.tmul_neg]
    · rw [mul_zero, neg_zero, TensorProduct.tmul_zero]
  have hw : finPt hS hT 1 (unitBlock D o a d) ∈ latO S T LS LT fun _ => True := by
    refine mem_latO_of_int hcc hset.gS hLS hLT (fun i j => congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T _) i) j)
      fun i j => ?_
    rw [hent]
    split_ifs
    · have h : finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := rfl
      rw [RingHom.map_neg, h]
      exact neg_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (mul_one _))
    · rw [RingHom.map_zero]
      exact zero_mem _
  have hsupp : ∀ t : WO S T, cosetFn (cA D e) (D.host.conj • modul P c) 0 t ≠ 0 → t ∈ latO S T LS LT fun _ => True := by
    intro t ht
    have h : IsHalf (cA D e) t ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (t i j - (0 : WO S T) i j)) := by
      by_contra h
      exact ht (if_neg h)
    refine mem_latO_of_int hcc hset.gS hLS hLT (fun i j => ?_) fun i j => GlobalTheory.PlaceVec.finPart_mem_intAE ?_
    · rw [← h.1 i j, RingHom.map_mul, hinf, zero_mul]
    · obtain ⟨h1, -⟩ := h.2 i j
      rwa [Matrix.zero_apply, sub_zero] at h1
  have hmod := heis_model hset.std hSd hTd hge.1 hrd.1 hTm hw (inv_ne_zero hph) hvac hSB hsupp
  have hcc' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hge.1]
  have hA : ∀ i j, (cA D e • finPt hS hT 1 (unitBlock D o a d)) i j = -unitPt S T (cA D e) o i j := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, hent, unitPt]
    split_ifs
    · rw [mul_neg, mul_finOne hinf]
    · rw [mul_zero, neg_zero]
  have hΦ : (fun t => cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T) (t + cA D e • finPt hS hT 1 (unitBlock D o a d))) =
      cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) := by
    funext t
    refine if_congr (and_congr ?_ (forall_congr' fun i => forall_congr' fun j => ?_)) rfl rfl
    · rw [isHalf_smul, isHalf_smul, smul_add, smul_smul, hcc', add_left_inj]
    · rw [Matrix.add_apply, hA, Matrix.zero_apply, sub_zero, ← sub_eq_add_neg]
  have h := (heisO_finPt_reads ψ θ S T hS hT ⊤ δ 1 hset _ _ hG (unitBlock D o a d)).smul (wdPh D (tor0 D ⊤ δ) x)
  rw [hmod, hΦ, smul_smul, mul_inv_cancel₀ hph, one_smul] at h
  exact ⟨1, IsRootOne.one, by rw [one_smul]; exact h⟩

end GlobalTheory.BotSmallTransl

end
