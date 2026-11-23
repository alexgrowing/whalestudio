import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LattIota

variable {A O M : Type} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M] {ι : Type}
  (θ : A →+* O) (hs : Function.Surjective θ) (R : (ι → A) →ₛₗ[θ] M)
  (hR : ∀ s : ι → A, (∀ i, θ (s i) = 0) → R s = 0)

include hR in
theorem eq_of_theta_eq {s s' : ι → A} (h : ∀ i, θ (s i) = θ (s' i)) : R s = R s' := by
  rw [← sub_eq_zero, ← map_sub]
  exact hR _ fun i => by rw [Pi.sub_apply, map_sub, h, sub_self]

def descend : (ι → O) →ₗ[O] M where
  toFun ρ := R (fun i => Function.surjInv hs (ρ i))
  map_add' ρ ρ' := by
    rw [← map_add]
    exact eq_of_theta_eq θ R hR fun i => by
      simp [Function.surjInv_eq hs]
  map_smul' c ρ := by
    have h1 : (c • R (fun i => Function.surjInv hs (ρ i)) : M) =
        θ (Function.surjInv hs c) • R (fun i => Function.surjInv hs (ρ i)) := by
      rw [Function.surjInv_eq hs]
    rw [RingHom.id_apply, h1, ← LinearMap.map_smulₛₗ]
    exact eq_of_theta_eq θ R hR fun i => by
      simp [Function.surjInv_eq hs]

theorem descend_comp (s : ι → A) : descend θ hs R hR (fun i => θ (s i)) = R s :=
  eq_of_theta_eq θ R hR fun i => Function.surjInv_eq hs _

variable [Fintype ι]

def dotL (ρ : ι → O) : (ι → O) →ₗ[O] O where
  toFun w := ρ ⬝ᵥ w
  map_add' := dotProduct_add ρ
  map_smul' c w := by rw [dotProduct_smul, RingHom.id_apply]

@[simp] theorem dotL_apply (ρ w : ι → O) : dotL ρ w = ρ ⬝ᵥ w := rfl

end GlobalTheory.LattIota

namespace GlobalTheory.LattIota

theorem iota_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O), HasDatum hε G → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (π : M →ₗ[O] G.dual.Lie), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ (y : latt G) t, π (r y) (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t)) → ∃ ι : G.omega →ₗ[O] M, Function.Injective ι ∧ Function.Exact ι π ∧ (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG M _ _ r π hrs hker hπ
  obtain ⟨D, e, fil, lie, hal, hb⟩ := hG
  obtain ⟨L, hL⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by
    simpa [zeta] using hε 1
  obtain ⟨hdom, -, hkerθ, hsθ, hν, hξ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε1
  obtain ⟨hFG, hrangeFil, -, hνFil, -, -⟩ :=
    GlobalTheory.Sandwich.HodgeTateBound.bound p C v O hv ε hε1 ℤ_[p] G.height D
  obtain ⟨hFin, hProj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G
  have hθξ : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hkerθ]; exact Ideal.mem_span_singleton_self _
  let R : (Fin G.height → Ainf p O) →ₛₗ[WittVector.fontaineTheta O p] M :=
    r.comp (L : (Fin G.height → Ainf p O) →ₗ[Ainf p O] latt G)
  have hR : ∀ s : Fin G.height → Ainf p O, (∀ i, WittVector.fontaineTheta O p (s i) = 0) →
      R s = 0 := by
    intro s hs0
    have hu : ∀ i, ∃ u, u * xi ε = s i := fun i => by
      rw [← Ideal.mem_span_singleton', ← hkerθ]; exact hs0 i
    choose u hu using hu
    have hsu : s = xi ε • u := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hu]
    change r (L s) = 0
    rw [hker, hsu, map_smul]
    exact ⟨_, rfl⟩
  let Φ := descend _ hsθ R hR
  have hΦ : ∀ s, Φ (fun i => WittVector.fontaineTheta O p (s i)) = r (L s) := fun s =>
    descend_comp _ hsθ R hR s
  have hlift : ∀ ρ : Fin G.height → O, ∃ s : Fin G.height → Ainf p O,
      (fun i => WittVector.fontaineTheta O p (s i)) = ρ := fun ρ =>
    ⟨fun i => Function.surjInv hsθ (ρ i), funext fun i => Function.surjInv_eq hsθ _⟩
  have hΦs : Function.Surjective Φ := by
    intro m
    obtain ⟨y, rfl⟩ := hrs m
    obtain ⟨s, rfl⟩ := L.surjective y
    exact ⟨_, hΦ s⟩
  have hΦi : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ρ hρ
    obtain ⟨s, rfl⟩ := hlift ρ
    rw [hΦ, hker] at hρ
    obtain ⟨n, hn⟩ := hρ
    have hs : s = xi ε • L.symm n := by
      apply L.injective; rw [map_smul, L.apply_symm_apply, hn]
    funext i
    rw [hs, Pi.smul_apply, smul_eq_mul, map_mul, hθξ, zero_mul, Pi.zero_apply]
  have hπHT : ∀ s t, π (r (L s)) (hodgeTate G t) =
      (fun i => WittVector.fontaineTheta O p (s i)) ⬝ᵥ (fil (hodgeTate G t) : Fin G.height → O) := by
    intro s t
    rw [hπ, hL, ← hal, RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    rfl
  have hsingle : ∀ i, toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
    intro i; funext j
    by_cases hij : j = i
    · subst hij; simp [toO]
    · simp [toO, Pi.single_apply, hij]
  have hext : ∀ f₁ f₂ : G.dual.omega →ₗ[O] O,
      (∀ t, f₁ (hodgeTate G t) = f₂ (hodgeTate G t)) → f₁ = f₂ := by
    intro f₁ f₂ hf
    let g : (G.dual.omega →ₗ[O] O) → (Fin G.height → O) →ₗ[O] O := fun f =>
      f ∘ₗ fil.symm.toLinearMap ∘ₗ (D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩))
    have key : ∀ f t, g f (toO e t) = f (hodgeTate G t) := by
      intro f t
      have h1 : D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩) (toO e t) =
          fil (hodgeTate G t) := Subtype.ext (hal t)
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, LinearEquiv.symm_apply_apply]
    have hg : g f₁ = g f₂ := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      change g f₁ (Pi.single i 1) = g f₂ (Pi.single i 1)
      rw [← hsingle, key, key, hf]
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, hw⟩ := hνFil _ (fil x).2
    have hgx : ∀ f, g f w = WittVector.fontaineTheta O p (nu ε) * f x := by
      intro f
      have h1 : D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩) w =
          WittVector.fontaineTheta O p (nu ε) • fil x := Subtype.ext hw
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, map_smul,
        LinearEquiv.symm_apply_apply, smul_eq_mul]
    exact mul_left_cancel₀ hν (by rw [← hgx, ← hgx, hg])
  have hπΦ : ∀ ρ x, π (Φ ρ) x = ρ ⬝ᵥ (fil x : Fin G.height → O) := by
    intro ρ
    obtain ⟨s, rfl⟩ := hlift ρ
    have := hext (π (Φ (fun i => WittVector.fontaineTheta O p (s i))))
      (dotL (fun i => WittVector.fontaineTheta O p (s i)) ∘ₗ D.Fil.subtype ∘ₗ fil.toLinearMap)
      (fun t => by rw [hΦ, hπHT]; rfl)
    intro x
    exact LinearMap.congr_fun this x
  let κ : G.omega →ₗ[O] (Fin G.height → O) :=
    LinearMap.pi fun i => lie (D.Fil.mkQ (Pi.single i 1))
  have hκ : ∀ w i, κ w i = lie (D.Fil.mkQ (Pi.single i 1)) w := fun w i => rfl
  have hk : ∀ w m, κ w ⬝ᵥ m = lie (D.Fil.mkQ m) w := by
    intro w
    have : dotL (κ w) = (LinearMap.applyₗ w : Module.Dual O G.omega →ₗ[O] O) ∘ₗ
        lie.toLinearMap ∘ₗ D.Fil.mkQ := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      simp [hκ]
    intro m
    exact LinearMap.congr_fun this m
  have hκi : Function.Injective κ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine (Module.forall_dual_apply_eq_zero_iff O w).1 fun φ => ?_
    obtain ⟨q, rfl⟩ := lie.surjective φ
    obtain ⟨m, rfl⟩ := D.Fil.mkQ_surjective q
    rw [← hk, hw, zero_dotProduct]
  refine ⟨Φ ∘ₗ κ, hΦi.comp hκi, fun m => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨ρ, rfl⟩ := hΦs m
    have hρ : D.Fil ≤ LinearMap.ker (dotL ρ) := fun f hf => by
      obtain ⟨x, hx⟩ := fil.surjective ⟨f, hf⟩
      have := LinearMap.congr_fun h0 x
      rw [hπΦ, hx] at this
      exact this
    let ψ : ((Fin G.height → O) ⧸ D.Fil) →ₗ[O] O := D.Fil.liftQ (dotL ρ) hρ
    let w := (Module.evalEquiv O G.omega).symm (ψ ∘ₗ lie.symm.toLinearMap)
    have hw : ∀ φ : G.Lie, φ w = ψ (lie.symm φ) := fun φ => by
      change (Module.evalEquiv O G.omega w) φ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    refine ⟨w, ?_⟩
    change Φ (κ w) = Φ ρ
    congr 1
    funext i
    rw [hκ, hw, LinearEquiv.symm_apply_apply]
    simp [ψ]
  · rintro ⟨w, rfl⟩
    refine LinearMap.ext fun x => ?_
    change π (Φ (κ w)) x = 0
    rw [hπΦ, hk, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (fil x).2, map_zero]
    rfl
  · intro χ y hy
    let sχ : Fin G.height → Ainf p O := fun i =>
      ofPadic p O (epsPairing hε G (e.symm (Pi.single i 1)) χ)
    have hpair : ∀ t, sχ ⬝ᵥ (fun i => ofPadic p O (e t i)) = ofPadic p O (epsPairing hε G t χ) := by
      intro t
      have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
        apply e.injective
        rw [map_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      have hlin : epsPairing hε G t χ =
          ∑ i, e t i * epsPairing hε G (e.symm (Pi.single i 1)) χ := by
        conv_lhs => rw [ht]
        simp only [epsPairing, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
          smul_eq_mul]
      rw [hlin, map_sum]
      simp only [dotProduct, sχ, map_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hyL : y = L (sχ ᵥ* D.G) := by
      apply Subtype.ext
      refine LinearMap.ext fun t => ?_
      rw [hL, hy, ← dotProduct_mulVec, mulVec_mulVec, D.G_mul_F, smul_mulVec, one_mulVec,
        dotProduct_smul, hpair, smul_eq_mul]
    rw [hyL, ← hΦ]
    change Φ (κ (dlog G χ)) = _
    congr 1
    funext i
    rw [hκ, ← hb, LinearEquiv.symm_apply_apply, RingHom.map_vecMul]
    simp [bQuot, pairingO, Datum.bb, Matrix.toLin'_apply, vecMul, dotProduct, padicToO, sχ,
      mul_comm]

end GlobalTheory.LattIota
