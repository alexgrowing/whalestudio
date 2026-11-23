import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOfMulEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichStarRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DualDatumDot

def dotL {O : Type} [CommRing O] {h : ℕ} (u : Fin h → O) : (Fin h → O) →ₗ[O] O where
  toFun m := u ⬝ᵥ m
  map_add' a b := dotProduct_add u a b
  map_smul' c m := by simp

theorem dotL_apply {O : Type} [CommRing O] {h : ℕ} (u m : Fin h → O) : dotL u m = u ⬝ᵥ m := rfl

theorem dot_single {O : Type} [CommRing O] {h : ℕ} (g : (Fin h → O) →ₗ[O] O) (x : Fin h → O) :
    (fun i => g (Pi.single i 1)) ⬝ᵥ x = g x := by
  have hx : x = ∑ i, x i • Pi.single i (1 : O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp [map_sum, dotProduct, mul_comm]

theorem toLin'_transpose_dot {A O : Type} [CommRing A] [CommRing O] (θ : A →+* O) {h : ℕ}
    (X : Matrix (Fin h) (Fin h) A) (a b : Fin h → O) :
    Matrix.toLin' (Xᵀ.map θ) a ⬝ᵥ b = a ⬝ᵥ Matrix.toLin' (X.map θ) b := by
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.transpose_map, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]

end GlobalTheory.DualDatumDot

open GlobalTheory.DualDatumDot

namespace GlobalTheory.DualDatum

theorem hasDatum_dual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → HasDatum hε G.dual := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G ⟨D, e, fil, lie, hA, hB⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hζ
  have hν' : nu ε ≠ 0 := fun h0 => hν (by rw [h0, map_zero])
  have hμ : Sandwich.mu ε ≠ 0 := by rw [← xi_mul_nu]; exact mul_ne_zero hξ hν'
  obtain ⟨-, h1, -, h3, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have := hv.isFractionRing
  have := hv.isIntegrallyClosed
  have : IsIntegrallyClosedIn O C :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C).1 inferInstance
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G
  haveI := hfin
  haveI := hproj
  let θ := WittVector.fontaineTheta O p
  let D' := SelfDualFil.dualDatum hμ hξ D

  have perp : ∀ a, a ∈ D'.Fil ↔ ∀ f ∈ D.Fil, a ⬝ᵥ f = 0 := by
    intro a
    change Matrix.toLin' ((D.F)ᵀ.map θ) a = 0 ↔ _
    constructor
    · intro ha f hf
      obtain ⟨w, hw⟩ := h3 f hf
      have e1 : a ⬝ᵥ D.al w = 0 := by
        rw [show D.al w = Matrix.toLin' (D.F.map θ) w from rfl, ← toLin'_transpose_dot, ha,
          zero_dotProduct]
      rw [hw, dotProduct_smul, smul_eq_mul] at e1
      exact (mul_eq_zero.1 e1).resolve_left hν
    · intro ha
      funext i
      have h2 := ha _ (h1 ⟨Pi.single i 1, rfl⟩)
      rw [show D.al (Pi.single i 1) = Matrix.toLin' (D.F.map θ) (Pi.single i 1) from rfl,
        ← toLin'_transpose_dot] at h2
      simpa using h2

  let E : Fin G.height → G.Tate := fun i => e.symm (Pi.single i 1)
  have hexp : ∀ t, t = ∑ i, e t i • E i := by
    intro t
    apply e.injective
    rw [map_sum]
    ext j
    simp [E, Finset.sum_apply, Pi.single_apply]
  let L : G.dual.Tate →ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) :=
    LinearMap.pi fun i => (epsEquiv hε).symm.toLinearMap ∘ₗ pairing G O (E i)
  have hL : ∀ χ i, L χ i = epsPairing hε G (E i) χ := fun _ _ => rfl
  have hflip := G.pairing_flip_bijective C
  have hLb : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun χ hχ => hflip.1 ?_
      rw [map_zero]
      refine LinearMap.ext fun t => ?_
      rw [LinearMap.flip_apply, LinearMap.zero_apply, hexp t, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, LinearMap.smul_apply, ← epsPairing_smul hε, ← hL, hχ]
      simp
    · intro c
      let φ : G.Tate →ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
        (epsEquiv hε).toLinearMap ∘ₗ (∑ i, c i • LinearMap.proj i) ∘ₗ e.toLinearMap
      obtain ⟨χ, hχ⟩ := hflip.2 φ
      refine ⟨χ, funext fun j => ?_⟩
      have hj : pairing G O (E j) χ = φ (E j) := LinearMap.congr_fun hχ (E j)
      rw [hL, epsPairing, hj]
      simp [φ, E, Pi.single_apply]
  let e' : G.dual.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) := LinearEquiv.ofBijective L hLb
  have he' : ∀ χ i, e' χ i = epsPairing hε G (E i) χ := fun _ _ => rfl
  have hdualb : ∀ t i, epsPairing hε G t (e'.symm (Pi.single i 1)) = e t i := by
    intro t i
    have hj : ∀ j, epsPairing hε G (E j) (e'.symm (Pi.single i 1)) = (Pi.single i (1 : ℤ_[p]) : Fin G.height → ℤ_[p]) j := by
      intro j
      rw [← he', LinearEquiv.apply_symm_apply]
    have hs : ∀ s, epsPairing hε G s (e'.symm (Pi.single i 1)) =
        (epsEquiv hε).symm.toLinearMap ((pairing G O).flip (e'.symm (Pi.single i 1)) s) :=
      fun _ => rfl
    rw [hs]
    conv_lhs => rw [hexp t]
    rw [map_sum, map_sum]
    simp only [map_smul, ← hs, hj, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let Φ : G.omega →ₗ[O] (Fin G.height → O) :=
    LinearMap.pi fun i => lie (D.Fil.mkQ (Pi.single i 1))
  let g : G.omega → (Fin G.height → O) →ₗ[O] O := fun w =>
    Module.Dual.eval O G.omega w ∘ₗ lie.toLinearMap ∘ₗ D.Fil.mkQ
  have hΦdot : ∀ w m, Φ w ⬝ᵥ m = lie (D.Fil.mkQ m) w := fun w m => dot_single (g w) m
  have hΦmem : ∀ w, Φ w ∈ D'.Fil := fun w => (perp _).2 fun f hf => by
    rw [hΦdot, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hf, map_zero,
      LinearMap.zero_apply]
  have hΦinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun w hw => ?_
    apply (Module.evalEquiv O G.omega).injective
    rw [map_zero]
    refine LinearMap.ext fun x => ?_
    obtain ⟨q, rfl⟩ := lie.surjective x
    obtain ⟨m, rfl⟩ := D.Fil.mkQ_surjective q
    rw [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.zero_apply, ← hΦdot, hw,
      zero_dotProduct]
  have hΦsurj : ∀ u ∈ D'.Fil, ∃ w, Φ w = u := by
    intro u hu
    have hle : D.Fil ≤ LinearMap.ker (dotL u) := fun f hf => (perp u).1 hu f hf
    let ℓ : G.Lie →ₗ[O] O := D.Fil.liftQ (dotL u) hle ∘ₗ lie.symm.toLinearMap
    refine ⟨(Module.evalEquiv O G.omega).symm ℓ, funext fun i => ?_⟩
    have hw : ∀ x : G.Lie, x ((Module.evalEquiv O G.omega).symm ℓ) = ℓ x := fun x => by
      have h5 := LinearMap.congr_fun ((Module.evalEquiv O G.omega).apply_symm_apply ℓ) x
      rwa [Module.evalEquiv_apply, Module.Dual.eval_apply] at h5
    change lie (D.Fil.mkQ (Pi.single i 1)) _ = u i
    rw [hw]
    change D.Fil.liftQ (dotL u) hle (lie.symm (lie (D.Fil.mkQ (Pi.single i 1)))) = u i
    rw [LinearEquiv.symm_apply_apply]
    change u ⬝ᵥ Pi.single i 1 = u i
    simp
  let filE : G.omega ≃ₗ[O] D'.Fil := LinearEquiv.ofBijective (Φ.codRestrict D'.Fil hΦmem)
    ⟨fun a b hab => hΦinj (congrArg Subtype.val hab), fun u => by
      obtain ⟨w, hw⟩ := hΦsurj u.1 u.2
      exact ⟨w, Subtype.ext hw⟩⟩
  let fil' : G.dual.dual.omega ≃ₗ[O] D'.Fil := (DlogSpan.pDivGroupOmegaBidualEquiv G).symm ≪≫ₗ filE

  let Ψ : (Fin G.height → O) →ₗ[O] G.dual.Lie :=
    LinearMap.mk₂ O (fun m w => m ⬝ᵥ (fil w : Fin G.height → O))
      (fun _ _ _ => by simp [add_dotProduct]) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [dotProduct_add]) (fun _ _ _ => by simp)
  have hΨ : ∀ m w, Ψ m w = m ⬝ᵥ (fil w : Fin G.height → O) := fun _ _ => rfl
  have hΨker : LinearMap.ker Ψ = D'.Fil := by
    ext m
    rw [LinearMap.mem_ker, perp]
    constructor
    · intro hm f hf
      obtain ⟨w, hw⟩ := fil.surjective ⟨f, hf⟩
      have h5 := LinearMap.congr_fun hm w
      rwa [hΨ, hw] at h5
    · intro hm
      exact LinearMap.ext fun w => hm _ (fil w).2
  haveI : Module.Projective O ((Fin G.height → O) ⧸ D.Fil) := Module.Projective.of_equiv lie.symm
  obtain ⟨s, hs⟩ := Module.projective_lifting_property D.Fil.mkQ LinearMap.id D.Fil.mkQ_surjective
  let r : (Fin G.height → O) →ₗ[O] D.Fil :=
    (LinearMap.id - s ∘ₗ D.Fil.mkQ).codRestrict D.Fil fun x => by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
      have h5 := LinearMap.congr_fun hs (D.Fil.mkQ x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h5 ⊢
      rw [h5, sub_self]
  have hr : ∀ f : D.Fil, r f = f := fun f => by
    apply Subtype.ext
    have h0 : D.Fil.mkQ (f : Fin G.height → O) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 f.2
    simp [r, h0]
  have hΨsurj : Function.Surjective Ψ := by
    intro y
    let φ : (Fin G.height → O) →ₗ[O] O := y ∘ₗ fil.symm.toLinearMap ∘ₗ r
    refine ⟨fun i => φ (Pi.single i 1), LinearMap.ext fun w => ?_⟩
    rw [hΨ, dot_single]
    simp [φ, hr]
  let lie' : ((Fin G.height → O) ⧸ D'.Fil) ≃ₗ[O] G.dual.Lie :=
    Submodule.quotEquivOfEq _ _ hΨker.symm ≪≫ₗ Ψ.quotKerEquivOfSurjective hΨsurj
  have hlie' : ∀ m, lie' (D'.Fil.mkQ m) = Ψ m := fun _ => rfl
  refine ⟨D', e', fil', lie', fun χ => ?_, fun y ψ => ?_⟩
  · have hf : fil' (hodgeTate G.dual χ) = filE (dlog G χ) := by
      simp only [fil', LinearEquiv.trans_apply]
      congr 1
      rw [LinearEquiv.symm_apply_eq, DlogSpan.pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate]
    rw [hf]
    change _ = Φ (dlog G χ)
    funext i
    change _ = lie (D.Fil.mkQ (Pi.single i 1)) (dlog G χ)
    rw [← hB, LinearEquiv.symm_apply_apply]
    change Matrix.toLin' ((D.G)ᵀ.map θ) (toO e' χ) i =
      pairingO hε e (Matrix.toLin' (D.G.map θ) (Pi.single i 1)) χ
    simp [pairingO, toO, he', E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, θ,
      Pi.single_apply, mul_comm]
  · obtain ⟨m, rfl⟩ := hΨsurj y
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective ψ
    have hl : lie'.symm (Ψ m) = D'.Fil.mkQ m := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hlie' m).symm
    rw [hl]
    change pairingO hε e' (D'.bb m) (tateMap G G.dual.dual O G.bidual.hom t) =
      Ψ m (dlog G.dual (tateMap G G.dual.dual O G.bidual.hom t))
    rw [← hodgeTate_apply, hΨ, ← hA]
    have hp : ∀ i, epsPairing hε G.dual (e'.symm (Pi.single i 1))
        (tateMap G G.dual.dual O G.bidual.hom t) = e t i := fun i => by
      rw [epsPairing, DetInv.pairing_dual_bidual]
      exact hdualb t i
    simp only [pairingO, hp]
    change Matrix.toLin' ((D.F)ᵀ.map θ) m ⬝ᵥ toO e t = m ⬝ᵥ Matrix.toLin' (D.F.map θ) (toO e t)
    rw [toLin'_transpose_dot]

end GlobalTheory.DualDatum
