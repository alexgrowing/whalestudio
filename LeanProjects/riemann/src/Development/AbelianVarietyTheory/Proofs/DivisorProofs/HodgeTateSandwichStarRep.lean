import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichKernelRangeExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

noncomputable section

namespace GlobalTheory.DetInv

open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta (epsTate epsEquiv epsPairing toO pairingO bQuot Realizes)

theorem sum_integral_iff_dual {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    [IsFractionRing O C] {h n : ℕ} (F : Submodule O (Fin h → O))
    (hF : ∀ (d : O) (m : Fin h → O), d ≠ 0 → d • m ∈ F → m ∈ F) (f : Fin n → F) (w : Fin n → C) :
    (∀ k, ∑ i, w i * algebraMap O C ((f i : Fin h → O) k) ∈ (algebraMap O C).range) ↔
      ∀ y : Module.Dual O F, ∑ i, w i * algebraMap O C (y (f i)) ∈ (algebraMap O C).range := by
  refine ⟨fun H y => ?_, fun H k => H (LinearMap.proj k ∘ₗ F.subtype)⟩
  choose m hm using H
  obtain ⟨⟨d, hd⟩, hw⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose u hu using hw
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hi := IsFractionRing.injective O C
  have hu' : ∀ i, algebraMap O C (u i) = algebraMap O C d * w i := fun i => by
    rw [hu, Algebra.smul_def]
  have e : d • m = ((∑ i, u i • f i : F) : Fin h → O) := by
    funext k
    apply hi
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hm, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul, map_sum, hu', Finset.mul_sum, mul_assoc]
  have hmF : m ∈ F := hF d m hd0 (e ▸ Subtype.prop _)
  have e2 : d • (⟨m, hmF⟩ : F) = ∑ i, u i • f i := Subtype.ext e
  have e3 := congrArg (fun z => algebraMap O C (y z)) e2
  simp only [map_smul, map_sum, smul_eq_mul, map_mul, hu', mul_assoc, ← Finset.mul_sum] at e3
  exact ⟨_, mul_left_cancel₀ ((map_ne_zero_iff _ hi).2 hd0) e3⟩

section Group

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)

theorem pairing_dual_bidual (t : G.Tate) (u : G.dual.Tate) :
    pairing G.dual O u (tateMap G G.dual.dual O G.bidual.hom t) = pairing G O t u :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing]
    have h1 : charElem (G := G.dual) (tateMap G G.dual.dual O G.bidual.hom t) n =
        WithConv.toConv (t.pt n).toLinearMap :=
      (charHom_app_muT _ n).symm.trans (dualChar_app_muT t n)
    rw [h1]
    exact (apply_charElem u n _).symm

theorem omegaMap_hodgeTate (hinj : Function.Injective (pairing G O).flip) (f : G ⟶ G.dual)
    (halt : ∀ s t, pairing G O s (tateMap G G.dual O f t) = -pairing G O t (tateMap G G.dual O f s))
    (t : G.Tate) :
    omegaMap G G.dual f (hodgeTate G t) = -dlog G (tateMap G G.dual O f t) := by
  rw [hodgeTate_apply, ← dlog_tateMap, ← map_neg]
  congr 1
  refine hinj (LinearMap.ext fun s => ?_)
  rw [LinearMap.flip_apply, LinearMap.flip_apply, ← pairing_tateMap, pairing_dual_bidual, map_neg,
    halt t s]

def omegaIso {G H : PDivGroup p O} (e : G ≅ H) : H.omega ≃ₗ[O] G.omega :=
  LinearEquiv.ofLinearMap (omegaMap G H e.hom) (omegaMap H G e.inv)
    (by rw [← omegaMap_comp, e.hom_inv_id, omegaMap_id])
    (by rw [← omegaMap_comp, e.inv_hom_id, omegaMap_id])

end Group

section Coordinates

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
  [CommRing O] [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] [Algebra ℤ_[p] C]
  (P : Point p v O Λ) {h : ℕ} (ψ : P.T ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))

def coordV : P.V ≃ₗ[C] (Fin h → C) := ((Module.Basis.ofEquivFun ψ).baseChange C).equivFun

theorem coordV_tmul (c : C) (t : P.T) (i : Fin h) :
    coordV P ψ (c ⊗ₜ t) i = c * algebraMap ℤ_[p] C (ψ t i) := by
  rw [coordV, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
    Module.Basis.ofEquivFun_repr_apply, Algebra.smul_def, mul_comm]

theorem coordV_symm (w : Fin h → C) :
    (coordV P ψ).symm w = ∑ i, w i • ((1 : C) ⊗ₜ ψ.symm (Pi.single i 1) : P.V) := by
  rw [coordV, Module.Basis.equivFun_symm_apply]
  simp only [Module.Basis.baseChange_apply, Module.Basis.coe_ofEquivFun]

theorem eq_sum_coordV (x : P.V) :
    x = ∑ i, coordV P ψ x i • ((1 : C) ⊗ₜ ψ.symm (Pi.single i 1) : P.V) := by
  rw [← coordV_symm, LinearEquiv.symm_apply_apply]

theorem coordV_actV (a : Λ) (X : Matrix (Fin h) (Fin h) ℤ_[p])
    (hX : ∀ t, ψ (P.actT a t) = X *ᵥ ψ t) (x : P.V) :
    coordV P ψ (P.actV a x) = X.map (algebraMap ℤ_[p] C) *ᵥ coordV P ψ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul c t =>
    funext i
    change coordV P ψ (c ⊗ₜ P.actT a t) i = _
    simp only [coordV_tmul, hX, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
      Finset.mul_sum, mul_left_comm]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

theorem mem_latT_iff_coordV (x : P.V) :
    x ∈ P.latT ↔ ∀ i, coordV P ψ x i ∈ (algebraMap O C).range := by
  constructor
  · rintro ⟨y, rfl⟩ i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, Pi.add_apply] using Subring.add_mem _ hx hy
    | tmul c t =>
      rw [Point.inclT_tmul, coordV_tmul, IsScalarTower.algebraMap_apply ℤ_[p] O C, ← map_mul]
      exact ⟨_, rfl⟩
  · intro H
    rw [eq_sum_coordV P ψ x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := H i
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_mem _ _ (P.one_tmul_mem_latT _)

end Coordinates

theorem redC_incl {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] {h : ℕ}
    (X : Matrix (Fin h) (Fin h) (Ainf p O)) (m : Fin h → O) :
    redC C X (incl C h m) =
      incl C h (Matrix.toLin' (X.map (WittVector.fontaineTheta O p)) m) := by
  funext i
  simp [redC, incl, Matrix.mulVec, dotProduct]

theorem eq_sum_incl {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C] {h : ℕ}
    (w : Fin h → C) : w = ∑ i, w i • incl C h (Pi.single i (1 : O)) := by
  funext j
  simp [incl, Finset.sum_apply, Pi.single_apply, apply_ite]

theorem exists_isTie_of_selfDual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P → (∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.T) (ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G) (pol : G ≅ G.dual) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (tateMap G G.dual O pol.hom t) = pairT P.A P.eps (e s) (e t) • ζ) ∧ (∀ x t, l x (dlog (G := G) (tateMap G G.dual O pol.hom t)) = (P.al₀ (e t)).1 x) ∧ ∀ (a : Λ) t, e (ρ.onTate O (1 ⊗ₜ a) t) = P.actT a (e t)) → ∃ (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] Λ)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsTie P D (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[p] ⊗[ℤ] Λ).toRingHom φ := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ _ ε hε ⟨u₁, u₂, hS⟩ Λ _ _ P hK
    ⟨G, e, ρ, pol, l, ζ, hζ, hpair, hl, hact⟩
  obtain ⟨D, e', fil, lie, hR⟩ := hS G _ ρ
  have hv := P.integers
  have hi := hv.hom_inj
  have := hv.isFractionRing
  have := hv.isIntegrallyClosed
  have : IsIntegrallyClosedIn O C :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C).1 inferInstance
  have hpad : ∀ r, algebraMap O C (padicToO p O r) = algebraMap ℤ_[p] C r := fun r => by
    rw [← padicToO_unique p O (algebraMap ℤ_[p] O), ← IsScalarTower.algebraMap_apply]
  have hincl : Function.Injective (incl (O := O) C G.height) := fun x y hxy =>
    funext fun i => hi (congrFun hxy i)
  let ψ : P.T ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) := e.symm ≪≫ₗ e'
  let φ := coordV P ψ
  let t : Fin G.height → G.Tate := fun i => e'.symm (Pi.single i 1)
  have hφ : ∀ w, φ.symm w = ∑ i, w i • ((1 : C) ⊗ₜ e (t i) : P.V) := coordV_symm P ψ

  obtain ⟨c, hc⟩ : ∃ c : ℤ_[p], c • epsTate hε = ζ := (epsEquiv hε).surjective ζ
  have hcu : IsUnit c := by
    obtain ⟨c', hc'⟩ := hζ.2 (epsTate hε)
    refine IsUnit.of_mul_eq_one c' (hζ.1 ?_)
    change (c * c') • ζ = (1 : ℤ_[p]) • ζ
    rw [mul_smul, show c' • ζ = _ from hc', hc, one_smul]
  have heps : ∀ s s', epsPairing hε G s (tateMap G G.dual O pol.hom s') =
      pairT P.A P.eps (e s) (e s') * c := fun s s' => by
    rw [epsPairing, hpair, ← hc, smul_smul, LinearEquiv.symm_apply_eq]
    rfl
  let u : Oˣ := u₂⁻¹ * (hcu.map (padicToO p O)).unit
  have hu : algebraMap O C u₂ * algebraMap O C u = algebraMap ℤ_[p] C c := by
    rw [← map_mul, ← hpad, ← Units.val_mul, mul_inv_cancel_left, IsUnit.unit_spec]
  have hu₂ : algebraMap O C u₂ ≠ 0 := (u₂.isUnit.map _).ne_zero

  have hb : ∀ z, φ (P.bLie z) = incl C _ ((u : O) • bQuot D (lie.symm (l z))) := fun z => by
    rw [← LinearEquiv.eq_symm_apply]
    refine P.eq_of_pairV fun s => ?_
    obtain ⟨s, rfl⟩ := e.surjective s
    have h1 := congrArg (algebraMap O C) (hR.b_eq (l z) (tateMap G G.dual O pol.hom s))
    rw [← dlog_eq_omegaMap, hl, pairingO, map_mul, ← P.pairV_bLie] at h1
    refine mul_left_cancel₀ hu₂ (h1.symm.trans ?_)
    rw [hφ]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Point.pairV_tmul,
      Finset.mul_sum, map_mul, hpad, heps]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hu]
    simp only [incl, LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply,
      Pi.smul_apply, Algebra.smul_def, map_mul, t, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  have hbq : ∀ m, bQuot D (D.Fil.mkQ m) = D.bb m := fun _ => rfl
  have hbinj : Function.Injective (bQuot D) :=
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  have hlie : ∀ x, x ∈ P.latLie ↔ φ x ∈ D.Lie.map (incl C _) := fun x => by
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm (l z))
      rw [hb, ← hm, hbq]
      exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ ⟨m, rfl⟩)
    · rintro ⟨_, ⟨m, rfl⟩, hm⟩
      refine ⟨l.symm (lie (D.Fil.mkQ ((u⁻¹ : Oˣ) • m))), φ.injective ?_⟩
      rw [hb, Equiv.apply_symm_apply, LinearEquiv.symm_apply_apply, hbq, ← hm, Units.smul_def,
        D.bb.map_smul, smul_smul, Units.mul_inv, one_smul]
  have hex := (ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε
    (by simpa [GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta] using hε 1) _ _ D).2
  refine ⟨_, D, φ, mem_latT_iff_coordV P ψ, fun a x => ?_, hlie, fun z z' hz => ?_, fun x => ?_,
    fun x => ?_⟩
  · refine (coordV_actV P ψ a (D.ρT (1 ⊗ₜ a)) (fun s => ?_) x).trans ?_
    · obtain ⟨s, rfl⟩ := e.surjective s
      simp only [ψ, ← hact, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      exact hR.tate_act _ s
    · congr 1
      ext i j
      exact (hpad _).symm
  · have h1 := hb z
    rw [hz, hb] at h1
    exact (l.injective (lie.symm.injective (hbinj (MulAction.injective u (hincl h1))))).symm
  · rw [← LinearMap.mem_ker, hex, hK.2.2.2.2.2.2]
    constructor
    · intro hx
      refine (Submodule.span_le (p := (LinearMap.range (bC C D)).comap φ.toLinearMap)).2 ?_ hx
      rintro _ ⟨z, rfl⟩
      obtain ⟨_, ⟨m, rfl⟩, hm⟩ := (hlie _).1 ⟨z, rfl⟩
      exact ⟨incl C _ m, (redC_incl C D.G m).trans hm⟩
    · rintro ⟨w, hw⟩
      rw [eq_sum_incl (O := O) C w, ← LinearEquiv.symm_apply_eq] at hw
      rw [← hw]
      simp only [map_sum, map_smul]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine (hlie _).2 ⟨_, ⟨Pi.single i 1, rfl⟩, ?_⟩
      rw [LinearEquiv.apply_symm_apply]
      exact (redC_incl C D.G _).symm
  · obtain ⟨w, rfl⟩ := φ.symm.surjective x
    let f : Fin G.height → D.Fil := fun i => (u₁ : O) • fil (hodgeTate G (t i))
    have hf : ∀ i, D.al (Pi.single i 1) = f i := fun i => by
      have h1 := hR.al_eq (t i)
      rw [← hodgeTate_eq_omegaMap] at h1
      refine Eq.trans (congrArg _ (funext fun j => ?_)) h1
      simp [toO, t, Pi.single_apply, apply_ite]
    have h1 : ∀ k, alC C D w k = ∑ i, w i * algebraMap O C ((f i : _ → O) k) := fun k => by
      conv_lhs => rw [eq_sum_incl (O := O) C w]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hf]
      exact Finset.sum_congr rfl fun i _ => congrArg _ (congrFun (redC_incl C D.F _) k)
    have hsign := omegaMap_hodgeTate G (G.pairing_flip_bijective C).1 pol.hom fun s s' => by
      rw [hpair, hpair, ← neg_smul, (isAlt_pairT P.A P.eps).neg_eq]
    let Φ : D.Fil ≃ₗ[O] G.omega :=
      (LinearEquiv.smulOfUnit (-u₁⁻¹) ≪≫ₗ fil.symm) ≪≫ₗ omegaIso pol
    have hΦ : ∀ i, Φ (f i) = dlog G (tateMap G G.dual O pol.hom (t i)) := fun i => by
      have h2 : (LinearEquiv.smulOfUnit (-u₁⁻¹) : D.Fil ≃ₗ[O] D.Fil) (f i) =
          -fil (hodgeTate G (t i)) := by
        change ((-u₁⁻¹ : Oˣ) : O) • (u₁ : O) • fil (hodgeTate G (t i)) = _
        rw [smul_smul, Units.val_neg, neg_mul, Units.inv_mul, neg_smul, one_smul]
      simp only [Φ, LinearEquiv.trans_apply, h2, map_neg, LinearEquiv.symm_apply_apply]
      exact neg_eq_iff_eq_neg.2 (hsign _)
    have h3 : ∀ z, P.pairV (P.bLie z) (φ.symm w) =
        ∑ i, w i * algebraMap O C (Φ.dualMap (l z) (f i)) := fun z => by
      simp only [hφ, map_sum, map_smul, P.pairV_bLie, LinearEquiv.dualMap_apply, hΦ, hl,
        smul_eq_mul]
    simp only [LinearEquiv.apply_symm_apply, h1]
    rw [sum_integral_iff_dual D.Fil (fun d m hd hm => ?_) f w]
    · constructor
      · rintro H _ ⟨z, rfl⟩
        rw [h3]
        exact H _
      · intro H y
        obtain ⟨y, rfl⟩ := Φ.dualMap.surjective y
        obtain ⟨z, rfl⟩ := l.surjective y
        rw [← h3]
        exact H _ ⟨z, rfl⟩
    · have h4 : d • D.bb m = 0 := (map_smul D.bb d m).symm.trans hm
      exact (smul_eq_zero.1 h4).resolve_left hd

end GlobalTheory.DetInv
