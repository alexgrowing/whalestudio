import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeOfMemLatticeHomCosetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosDep

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem isHalf_smul {e : AE D} {u : WO S T} (hu : IsHalf e u) (z : AE D) : IsHalf e (z • u) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [mul_left_comm, hu i j]

theorem isHalf_add {e : AE D} {u v : WO S T} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_sub {e : AE D} {u v : WO S T} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u - v) := fun i j => by
  simp only [Matrix.sub_apply, mul_sub, hu i j, hv i j]

theorem isHalf_idem {e : AE D} (he : e * e = e) (u : WO S T) : IsHalf e (e • u) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem mxAt_of_isHalf {e : AE D} (hinf : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) : MxAt (fun _ => True) u :=
  fun i j => by
    refine Ideal.mem_inf.2 ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, ← hu i j, map_mul, hinf, zero_mul]
    · refine Submodule.mem_iInf _ |>.2 fun w => ?_
      exact absurd trivial w.2

theorem cosInd_add {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos ΛS ΛT 𝔪) {u : WO S T} (hu : IsHalf e u)
    (hm : u ∈ hatMx (𝔪 • homLat ΛS ΛT)) (t : WO S T) : cosInd e κ (t + u) = cosInd e κ t := by
  have key : ∀ (t v : WO S T), IsHalf e v → v ∈ hatMx (𝔪 • homLat ΛS ΛT) → t ∈ cosSet e κ → t + v ∈ cosSet e κ := by
    rintro t v hv hvm ⟨ht, x₀, hx₀, hd⟩
    refine ⟨isHalf_add ht hv, x₀, hx₀, ?_⟩
    rw [add_sub_right_comm]
    exact add_mem hd hvm
  unfold cosInd
  by_cases h : t ∈ cosSet e κ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key t u hu hm h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro h'
    apply h
    have hn : IsHalf e (-u) := fun i j => by simp only [Matrix.neg_apply, mul_neg, hu i j]
    simpa using key (t + u) (-u) hn (neg_mem hm) h'

variable {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}

theorem heisO_fix_trans (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (hΦ : IsSBHalf e Λ Φ) {u : WO S T}
    (hu : IsHalf e u) (hinv : ∀ t, Φ (t + u) = Φ t) : heisO ψ S T u f = f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  rw [hall Tm hT, ← hT.trans Φ hΦ u hu]
  congr 1
  funext t
  exact hinv t

theorem heisO_fix_modul (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (hΦ : IsSBHalf e Λ Φ) {y : WO S T}
    (hy : IsHalf (cA D e) y) (hinv : ∀ t, Φ t ≠ 0 → ψ (symplO S T t y) = 1) : heisO ψ S T y f = f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  rw [hall Tm hT, ← hT.modul Φ hΦ y hy]
  congr 1
  funext t
  by_cases h0 : Φ t = 0
  · rw [h0, mul_zero]
  · rw [hinv t h0, one_mul]

end GlobalTheory.CosDep

namespace GlobalTheory.CosDep

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ}

theorem isLatVac_of_cos (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (κ : Cos ΛS ΛT 𝔪) (hcos : ∀ t ∈ cosSet e κ, t ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
    {f₀ f : WO S T → ℂ} (hf₀ : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) f₀)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ (cosInd e κ) f)
    {Γ : AddSubgroup (WO S T)}
    (hΓ : ∀ u ∈ Γ, u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ∧ e • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) :
    IsLatVac (heisO ψ S T) Γ f := by
  have e1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have e2 : e * cA D e = 0 := he.2
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, e1]
  have c2 : cA D e * e = 0 := by rw [mul_comm, e2]
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd hS hT h𝔪 e1 hinf κ
  have ann : ∀ x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), MxAt (fun _ => True) x →
      ∀ y ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), ψ (symplO S T x y) = 1 := fun x hx hx' =>
    (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T ΛS ΛT hS hT (fun _ => True) x hx').1 hx

  have hA : ∀ v, IsHalf e v → v ∈ hatMx (𝔪 • homLat ΛS ΛT) → heisO ψ S T v f = f := fun v hv hm =>
    heisO_fix_trans h hSB hv (cosInd_add κ hv hm)

  have hB : ∀ v, IsHalf (cA D e) v → v ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → heisO ψ S T v f = f :=
    fun v hv hm => heisO_fix_modul h hSB hv fun t ht => by
      have htc : t ∈ cosSet e κ := Set.mem_of_indicator_ne_zero ht
      exact ann t (hcos t htc) (mxAt_of_isHalf hinf htc.1) v hm

  have hC : ∀ r : WO S T, (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) → heisO ψ S T r f₀ = f₀ → heisO ψ S T r f = f :=
    fun r hr h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ _ f h r hr h0
  have hoff : ∀ u : WO S T, ∀ i j, e * (u - e • u - cA D e • u) i j = 0 ∧ cA D e * (u - e • u - cA D e • u) i j = 0 :=
    fun u i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      constructor
      · linear_combination (-(u i j)) * e1 + (-(u i j)) * e2
      · linear_combination (-(u i j)) * c2 + (-(u i j)) * c1
  have hdec : ∀ u : WO S T, u = e • u + (cA D e • u + (u - e • u - cA D e • u)) := fun u => by abel

  have dbl : ∀ a b r : WO S T, IsHalf e a → a ∈ hatMx (𝔪 • homLat ΛS ΛT) →
      a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → IsHalf (cA D e) b →
      b ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → r ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) →
      (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) → heisO ψ S T (2 • (a + (b + r))) f = f := by
    intro a b r hae ham hal hbe hbl hrl hr0
    have h2 : 2 • (a + (b + r)) = (a + a) + (b + b + (r + r)) := by rw [two_nsmul]; abel
    have hph : ψ (symplOH S T (a + a) (b + b + (r + r))) = 1 := by
      rw [GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self]
      exact ann a hal (mxAt_of_isHalf hinf hae) _ (add_mem (add_mem hbl hbl) (add_mem hrl hrl))
    have hbr : symplO S T (b + b) (r + r) = 0 := GlobalTheory.Hk3.symplO_half_off S T (isHalf_add hbe hbe) fun i j => by
      rw [GlobalTheory.DualPairCheck.cA_cA, Matrix.add_apply, mul_add, (hr0 i j).1, add_zero]
    have hrr : heisO ψ S T (r + r) f = f := hC _ (fun i j => by
        simp only [Matrix.add_apply, mul_add, (hr0 i j).1, (hr0 i j).2, add_zero, and_self])
      (by rw [← two_nsmul]; exact hf₀.1 r hrl)
    have hbb : heisO ψ S T (b + b) f = f := hB _ (isHalf_add hbe hbe) (add_mem hbl hbl)
    have haa : heisO ψ S T (a + a) f = f := hA _ (isHalf_add hae hae) (add_mem ham ham)
    have key := GlobalTheory.SplitScalar.heisO_heisO ψ S T (a + a) (b + b + (r + r)) f
    rw [hph, one_smul, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T hbr, hrr, hbb, haa] at key
    rw [h2, ← key]

  have sng : ∀ e' : AE D, IsSplitIdem D e' → ∀ a b r : WO S T, IsHalf e a → a ∈ hatMx (𝔪 • homLat ΛS ΛT) →
      IsHalf (cA D e) b → b ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) →
      r ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → (∀ i j, e * r i j = 0 ∧ cA D e * r i j = 0) →
      IsHalf e' a → IsHalf e' b → IsHalf e' r → heisO ψ S T (a + (b + r)) f = f := by
    intro e' he' a b r hae ham hbe hbl hrl hr0 ha' hb' hr'
    have horth : ∀ x y : WO S T, IsHalf e' x → IsHalf e' y → symplO S T x y = 0 := fun x y hx hy =>
      GlobalTheory.Hk3.symplO_half_off S T hx fun i j => by
        rw [← hy i j, ← mul_assoc, mul_comm (cA D e'), he'.2.1, zero_mul]
    rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth _ _ ha' (isHalf_add hb' hr')),
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth _ _ hb' hr'), hC r hr0 (hf₀.2 e' he' r hrl hr'),
      hB b hbe hbl, hA a hae ham]
  refine ⟨fun u hu => ?_, fun e' he' u hu hu' => ?_⟩
  · obtain ⟨hu1, hu2⟩ := hΓ u hu
    have ha := GlobalTheory.PlaceModelSum.idem_smul_latO e1 hu1
    have hb := GlobalTheory.PlaceModelSum.idem_smul_latO c1 hu1
    rw [hdec u]
    exact dbl _ _ _ (isHalf_idem e1 u) hu2 ha (isHalf_idem c1 u) hb (sub_mem (sub_mem hu1 ha) hb) (hoff u)
  · obtain ⟨hu1, hu2⟩ := hΓ u hu
    have ha := GlobalTheory.PlaceModelSum.idem_smul_latO e1 hu1
    have hb := GlobalTheory.PlaceModelSum.idem_smul_latO c1 hu1
    have hae : IsHalf e' (e • u) := isHalf_smul hu' e
    have hbe : IsHalf e' (cA D e • u) := isHalf_smul hu' _
    rw [hdec u]
    exact sng e' he' _ _ _ (isHalf_idem e1 u) hu2 (isHalf_idem c1 u) hb (sub_mem (sub_mem hu1 ha) hb) (hoff u)
      hae hbe (isHalf_sub (isHalf_sub hu' hae) hbe)

end GlobalTheory.CosDep

namespace GlobalTheory.CosDep

theorem cosInd_ne_zero {D : D7} {m n : ℕ} {e : AE D} (he : e * e = e) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos Λ Λ' 𝔪) : cosInd e κ ≠ 0 := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  intro h0
  have hmem : e • (x₀.1 : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ cosSet e (Submodule.Quotient.mk x₀ : Cos Λ Λ' 𝔪) :=
    ⟨fun i j => by simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he], x₀, rfl, by rw [sub_self]; exact zero_mem _⟩
  have := congrFun h0 (e • (x₀.1 : Matrix (Fin m) (Fin n) D.host.E).map (incA D))
  unfold cosInd at this
  rw [Set.indicator_of_mem hmem] at this
  exact one_ne_zero this

end GlobalTheory.CosDep

theorem GlobalTheory.CosDep.cosVec_dep : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ Dep W (.chi i 0) (W.cosVec i κ) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ) := by
  intro D hoff T L μ₀ hL sc G W M _ i hi κ
  obtain ⟨e, he, hcos⟩ := W.cosVec_is
  have h := hcos i hi κ
  obtain ⟨hS, hT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hv := (W.vac_is i hi).2
  have e1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd hS hT (G.pl.modul_ne_bot sc) e1 hinf κ
  refine ⟨?_, ⟨GlobalTheory.RowTheta.isThetaFunO_cosVec W i hi κ, ?_⟩, fun τ => ?_⟩
  · obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
    rw [hall Tm hTm]
    have hne : W.vac i ≠ 0 := by
      rintro h0
      obtain ⟨⟨p, hp⟩, hall'⟩ := hv.norm
      have := hall' p hp
      rw [h0] at this
      simp [nrm2] at this
    exact GlobalTheory.PlaceModelInj.placeModel_ne_zero D W.ψ _ _ _ _ e _ _ Tm W.ψ_std hS hT e1 he.2 hinf hTm hne hSB
      (GlobalTheory.CosDep.cosInd_ne_zero e1 κ)
  · exact GlobalTheory.CosDep.isLatVac_of_cos W.ψ_std hS hT he (G.pl.modul_ne_bot sc) κ
      (fun t ht => GlobalTheory.T.mem_completedHomLattice_of_mem_latticeHomCoset hS he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hoff hL G) κ ht) hv.lat h fun u hu => ⟨hu.1, hu.2 e he⟩
  · exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is hinf
      (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj.infPart_eq h hv.theta
      (GlobalTheory.RowTheta.isThetaFunO_cosVec W i hi κ) (hv.fock τ)

end
