import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PhiTTmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TLTensor

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def cA (r : Res l K) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) : AW r →+* C₀ := c

theorem hkA (r : Res l K) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) :
    ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = cA r c (algebraMap (WittVector l r.k) (AW r) w) := hk

def vinv {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (hl : IsUnit (c l)) : C₀ := ↑(hl.unit⁻¹)

theorem vinv_mul {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (hl : IsUnit (c l)) : vinv c hl * c l = 1 := hl.val_inv_mul

theorem map_vinv {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (hl : IsUnit (c l)) (g : C₀ →+* C₀) (hg : g (c l) = c l) :
    g (vinv c hl) = vinv c hl := by
  have h1 : c l * g (vinv c hl) = 1 := by rw [← hg, ← map_mul, mul_comm, vinv_mul, map_one]
  calc g (vinv c hl) = (vinv c hl * c l) * g (vinv c hl) := by rw [vinv_mul, one_mul]
    _ = vinv c hl := by rw [mul_assoc, h1, mul_one]

def psiF (r : Res l K) {N : ℕ} (F : Fac r N) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l)) (M : Model l K) (j : ℕ) :
    HL M j →+ (Module.Dual (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j) →+ C₀) :=
  Psi.psi (cA r c) k (hkA r c k hk) (vinv c hl ^ F.e M j) (F.α M j)

theorem psiF_apply (r : Res l K) {N : ℕ} (F : Fac r N) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l)) (M : Model l K) (j : ℕ)
    (x : HL M j) (f : Module.Dual (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j)) :
    psiF r F c k hk hl M j x f = vinv c hl ^ F.e M j * Psi.T (cA r c) k (hkA r c k hk) f (F.α M j x) := rfl

theorem alg_cancel {R : Type} [CommRing R] {v L X Y : R} (h : v * L = 1) (m a b : ℕ)
    (e : L ^ m * (L ^ a * X - L ^ b * Y) = 0) : v ^ b * X = v ^ a * Y := by
  have hv : ∀ n, v ^ n * L ^ n = 1 := fun n => by rw [← mul_pow, h, one_pow]
  have e1 : L ^ a * X = L ^ b * Y := by
    have := congrArg (v ^ m * ·) e
    simp only [mul_zero] at this
    rw [← mul_assoc, hv, one_mul] at this
    exact sub_eq_zero.1 this
  calc v ^ b * X = v ^ b * ((v ^ a * L ^ a) * X) := by rw [hv, one_mul]
    _ = v ^ a * v ^ b * (L ^ a * X) := by ring
    _ = v ^ a * v ^ b * (L ^ b * Y) := by rw [e1]
    _ = v ^ a * ((v ^ b * L ^ b) * Y) := by ring
    _ = v ^ a * Y := by rw [hv, one_mul]

theorem psiF_lin (r : Res l K) {N : ℕ} (F : Fac r N) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l)) (M : Model l K) (hM : M.Sm) (j : ℕ) (a : (per l K).A) (x : HL M j)
    (f : Module.Dual (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j)) :
    psiF r F c k hk hl M j (a • x) f = c ((per l K).φ^[N] a) * psiF r F c k hk hl M j x f := by
  rw [psiF_apply, psiF_apply, F.lin M hM j a x]
  have e : ((per l K).φ^[N] a • F.α M j x : AL r M j) = ((show AW r from (per l K).φ^[N] a) • F.α M j x) := rfl
  rw [e, Psi.T_smul, show cA r c ((⇑(per l K).φ)^[N] a) = c ((⇑(per l K).φ)^[N] a) from rfl]
  ring

theorem psiF_lin' (r : Res l K) {N : ℕ} (F : Fac r N) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l)) (M : Model l K) (j : ℕ) (z : Wc.K₀ l r.k) (x : HL M j)
    (f : Module.Dual (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j)) :
    psiF r F c k hk hl M j x (z • f) = k z * psiF r F c k hk hl M j x f := by
  rw [psiF_apply, psiF_apply]
  rw [show Psi.T (cA r c) k (hkA r c k hk) (z • f) (F.α M j x) = k z * Psi.T (cA r c) k (hkA r c k hk) f (F.α M j x) from
    Psi.T_ksmul (cA r c) k (hkA r c k hk) z f (F.α M j x)]
  ring

theorem psiF_act (r : Res l K) {N : ℕ} (F : Fac r N) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l)) (σC : K.fixingSubgroup → C₀ →+* C₀)
    (hσc : ∀ g a, σC g (c a) = c ((per l K).σA g a)) (hσk : ∀ g x, σC g (k x) = k x)
    (M : Model l K) (hM : M.Sm) (j : ℕ) (g : K.fixingSubgroup) (x : HL M j)
    (f : Module.Dual (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j)) :
    psiF r F c k hk hl M j (galL M j g x) f = σC g (psiF r F c k hk hl M j x f) := by
  rw [psiF_apply, psiF_apply, F.gal M hM j g x,
    Psi.T_gal (cA r c) k (hkA r c k hk) ((per l K).σA g : AW r →+* AW r) (σC g) (F.galT M j g)
      (fun a y => F.galT_tmul M hM j g a y) (fun a => hσc g a) (hσk g),
    map_mul, map_pow, map_vinv c hl (σC g) (by rw [hσc, map_natCast])]

theorem psiF_phi (r : Res l K) {N : ℕ} (F : Fac r N) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l)) (φC : C₀ →+* C₀) (hφc : ∀ a, φC (c a) = c ((per l K).φ a))
    (hφk : ∀ x, φC (k x) = k (Wc.frob₀ l r.k x))
    (M : Model l K) (hM : M.Sm) (j : ℕ) {m : ℕ} (b : Module.Basis (Fin m) (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j))
    (x : HL M j) (f : Module.Dual (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j)) :
    psiF r F c k hk hl M j (phiL M j x) f =
      ∑ s, φC (psiF r F c k hk hl M j x (b.coord s)) * k (f (Wc.phiD l (B.schFn M.p) r.ρ j (b s))) := by
  rw [psiF_apply, F.phi M hM j x,
    Psi.T_phi (cA r c) k (hkA r c k hk) ((per l K).φ : AW r →+* AW r) φC (Wc.phiS l (B.schFn M.p) r.ρ j).lim
      (WittVector.FractionRing.frobeniusRingHom l r.k) (Wc.phiD l (B.schFn M.p) r.ρ j)
      (fun x y => TensorProduct.map_tmul _ _ x y) (F.phiT M j) (fun a y => F.phiT_tmul M hM j a y) hφc hφk b f,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [psiF_apply, map_mul, map_pow, map_vinv c hl φC (by rw [hφc, map_natCast])]
  exact (mul_assoc _ _ _).symm

theorem psiF_nat (r : Res l K) {N : ℕ} (F : Fac r N) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l)) (M M' : Model l K) (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (hM : M.Sm) (hM' : M'.Sm) (j : ℕ)
    (x : HL M' j) (f : Module.Dual (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j)) :
    psiF r F c k hk hl M j (pullL u hu j x) f = psiF r F c k hk hl M' j x (f ∘ₗ r.iso.pull u hu j) := by
  obtain ⟨m, hm⟩ := F.nat M M' u hu hM hM' j x
  have h0 := congrArg (Psi.T (cA r c) k (hkA r c k hk) f) hm
  rw [map_zero] at h0
  have e1 : ∀ (a : (per l K).A) (z : AL r M j), (a • z : AL r M j) = ((show AW r from a) • z) := fun _ _ => rfl
  rw [e1, Psi.T_smul, map_sub, e1, e1, Psi.T_smul, Psi.T_smul, Psi.T_lTensor] at h0
  have hc : ∀ n : ℕ, cA r c (show AW r from ((l : (per l K).A) ^ n)) = c l ^ n := fun n => by
    change c ((l : Acris l) ^ n) = _
    rw [map_pow]
  rw [hc, hc, hc] at h0
  rw [psiF_apply, psiF_apply]
  exact alg_cancel (vinv_mul c hl) m (F.e M' j) (F.e M j) h0

def hF (r : Res l K) {N : ℕ} (F : Fac r N) (M : Model l K) (j : ℕ) (f : HL M j →+ (per l K).B) : LW r M j →+ (per l K).B where
  toFun y := f (F.β M j ((1 : AW r) ⊗ₜ y))
  map_zero' := by rw [tmul_zero, map_zero, map_zero]
  map_add' y y' := by rw [tmul_add, map_add, map_add]

theorem one_tmul_smul (r : Res l K) (M : Model l K) (j : ℕ) (w : WittVector l r.k) (y : LW r M j) :
    ((1 : AW r) ⊗ₜ[WittVector l r.k] (w • y) : AL r M j) = ((show (per l K).A from r.w w) • ((1 : AW r) ⊗ₜ[WittVector l r.k] y) : AL r M j) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  rfl

theorem tmul_eq_smul (r : Res l K) (M : Model l K) (j : ℕ) (a : AW r) (y : LW r M j) :
    (a ⊗ₜ[WittVector l r.k] y : AL r M j) = ((show (per l K).A from a) • ((1 : AW r) ⊗ₜ[WittVector l r.k] y) : AL r M j) := by
  rw [TensorProduct.smul_tmul']
  exact congrArg (· ⊗ₜ[WittVector l r.k] y) (mul_one (show Acris l from a)).symm

theorem inv_aux {R : Type} [CommRing R] {v L X Y : R} (hv : v * L = 1) (e : ℕ) (h1 : Y = L ^ e * X) : X = v ^ e * Y := by
  rw [h1, ← mul_assoc, ← mul_pow, hv, one_pow, one_mul]

set_option maxHeartbeats 4000000 in
theorem psiF_fac (r : Res l K) {N : ℕ} (F : Fac r N) {C₀ : Type} [CommRing C₀] (c : Acris l →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l)) (ι : C₀ →+* (per l K).B) (hιc : ∀ a, ι (c a) = (per l K).i a) (hR : (per l K).Facts)
    (hσw : ∀ g w, (per l K).σA g (r.w w) = r.w w) (M : Model l K) (hM : M.Sm) (j : ℕ) {m : ℕ}
    (b : Module.Basis (Fin m) (Wc.K₀ l r.k) (Wc.D l (B.schFn M.p) r.ρ j)) :
    ∃ w : Fin m → (HL M j →+ (per l K).B) → (per l K).B,
      (∀ f, GMod.Fn (per l K) (M.HA true).toGMod j f → ∀ s (σ : K.fixingSubgroup), (per l K).σ σ (w s f) = w s f) ∧
      ∀ x f, GMod.Fn (per l K) (M.HA true).toGMod j f →
        f ((phiL M j)^[N] x) = ∑ s, ι (psiF r F c k hk hl M j x (b.coord s)) * w s f := by
  classical
  have hh : ∀ f, GMod.Fn (per l K) (M.HA true).toGMod j f → ∀ (w : WittVector l r.k) (y : LW r M j),
      hF r F M j f (w • y) = ((per l K).i : AW r →+* (per l K).B) (algebraMap (WittVector l r.k) (AW r) w) * hF r F M j f y := by
    intro f hf w y
    change f (F.β M j ((1 : AW r) ⊗ₜ (w • y))) = _ * f (F.β M j ((1 : AW r) ⊗ₜ y))
    rw [one_tmul_smul, LinearMap.map_smul, hf.1]
    rfl
  have hE : ∀ f (hf : GMod.Fn (per l K) (M.HA true).toGMod j f), ∃ E : Wc.K₀ l r.k ⊗[WittVector l r.k] LW r M j →+ (per l K).B,
      (∀ x y, E (x ⊗ₜ y) = ι (k x) * hF r F M j f y) ∧
      ∀ G : AL r M j →+ (per l K).B, (∀ a y, G (a ⊗ₜ y) = ((per l K).i : AW r →+* (per l K).B) a * hF r F M j f y) →
        ∀ z, G z = ∑ s, ι (Psi.T (cA r c) k (hkA r c k hk) (b.coord s) z) * E (b s) := fun f hf =>
    Psi.T_fac (cA r c) k (hkA r c k hk) ι ((per l K).i : AW r →+* (per l K).B) hιc (hF r F M j f) (hh f hf) b
  refine ⟨fun s f => if hf : GMod.Fn (per l K) (M.HA true).toGMod j f then (hE f hf).choose (b s) else 0, ?_, ?_⟩
  · intro f hf s σ
    dsimp only
    rw [dif_pos hf]
    refine Psi.E_fix k ι ((per l K).σ σ) (hF r F M j f) _ (hE f hf).choose_spec.1 (fun w => ?_) (fun y => ?_) (b s)
    · rw [hk, hιc, ← hR.i_σ, hσw]
    · change (per l K).σ σ (f (F.β M j ((1 : AW r) ⊗ₜ y))) = f (F.β M j ((1 : AW r) ⊗ₜ y))
      rw [← hf.2]
      exact congrArg f (F.galβ M hM j σ y)
  · intro x f hf
    dsimp only
    let G : AL r M j →+ (per l K).B :=
      { toFun := fun z => f (F.β M j z)
        map_zero' := by rw [map_zero, map_zero]
        map_add' := fun z z' => by rw [map_add, map_add] }
    have hG := (hE f hf).choose_spec.2 G (fun a y => by
      change f (F.β M j (a ⊗ₜ y)) = _
      rw [tmul_eq_smul, LinearMap.map_smul, hf.1]
      rfl) (F.α M j x)
    have h1 : f (F.β M j (F.α M j x)) = (per l K).i ((l : (per l K).A) ^ F.e M j) * f ((phiL M j)^[N] x) := by
      rw [F.fac M hM j x, hf.1]
    have hv : ι (vinv c hl) * (per l K).i (l : (per l K).A) = 1 := by
      rw [← hιc, ← map_mul, vinv_mul, map_one]
    have h2 : f ((phiL M j)^[N] x) = ι (vinv c hl) ^ F.e M j * f (F.β M j (F.α M j x)) :=
      inv_aux hv (F.e M j) (h1.trans (congrArg (· * f ((phiL M j)^[N] x)) (map_pow _ _ _)))
    have hG' : f (F.β M j (F.α M j x)) = _ := hG
    rw [h2, hG', Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [dif_pos hf, psiF_apply, map_mul, map_pow]
    exact (mul_assoc _ _ _).symm

theorem fmap_of (r : Res l K) (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (N : ℕ) (F : Fac r N)
    (C₀ : Type) [CommRing C₀] (c : Acris l →+* C₀) (ι : C₀ →+* (per l K).B) (φ : C₀ →+* C₀)
    (σ : K.fixingSubgroup → C₀ →+* C₀) (q : ℚ_[l] →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hC : (perCOf r C₀ c ι φ σ q k).Facts) (hR : (per l K).Facts)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l))
    (hφk : ∀ x, φ (k x) = k (Wc.frob₀ l r.k x)) (hσk : ∀ g x, σ g (k x) = k x)
    (hσw : ∀ g w, (per l K).σA g (r.w w) = r.w w)
    (hfin : ∀ M : Model l K, M.Sm → ∀ j, Module.Finite (WittVector l r.k) (LW r M j))
    (hid : ∀ M : Model l K, M.Sm → ∀ j (x : r.iso.D M j), r.iso.pull (𝟙 M.X) (Category.id_comp _) j x = x) :
    Nonempty (FMap Model.Sm (perCOf r C₀ c ι φ σ q k) r.iso (dat Amp) (fun {M N u hu a b} _ j =>
      (Model.pullH (M := M) (N := N) u hu true j).lim.toAddMonoidHom)) := by
  refine ⟨{ k := N
            ψ := fun {M} _ j => psiF r F c k hk hl M j
            fin := fun M hM j => by
              have := hfin M hM j
              exact (inferInstance : Module.Finite (Wc.K₀ l r.k) (Wc.K₀ l r.k ⊗[WittVector l r.k] LW r M j))
            pull_id := hid
            lin := fun {M} _ hM j a x f => psiF_lin r F c k hk hl M hM j a x f
            lin' := fun {M} _ _ j z x f => psiF_lin' r F c k hk hl M j z x f
            act := fun {M} _ hM j g x f => psiF_act r F c k hk hl σ hC.σ_c hσk M hM j g x f
            phi := fun {M} _ hM j _ b x f => psiF_phi r F c k hk hl φ hC.φ_c hφk M hM j b x f
            nat := fun {M M'} {u hu} {_ _} _ hM hM' j x f => psiF_nat r F c k hk hl M M' u hu hM hM' j x f
            fac := fun {M} _ hM j _ b => psiF_fac r F c k hk hl ι hC.ι_c hR hσw M hM j b }⟩

def fmapS (r : Res l K) (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (N : ℕ) (F : Fac r N)
    (C₀ : Type) [CommRing C₀] (c : Acris l →+* C₀) (ι : C₀ →+* (per l K).B) (φ : C₀ →+* C₀)
    (σ : K.fixingSubgroup → C₀ →+* C₀) (q : ℚ_[l] →+* C₀) (k : Wc.K₀ l r.k →+* C₀)
    (hC : (perCOf r C₀ c ι φ σ q k).Facts) (hR : (per l K).Facts)
    (hk : ∀ w, k (algebraMap (WittVector l r.k) (Wc.K₀ l r.k) w) = c (r.w w)) (hl : IsUnit (c l))
    (hφk : ∀ x, φ (k x) = k (Wc.frob₀ l r.k x)) (hσk : ∀ g x, σ g (k x) = k x)
    (hσw : ∀ g w, (per l K).σA g (r.w w) = r.w w)
    (hfin : ∀ M : Model l K, M.Sm → ∀ j, Module.Finite (WittVector l r.k) (LW r M j))
    (hid : ∀ M : Model l K, M.Sm → ∀ j (x : r.iso.D M j), r.iso.pull (𝟙 M.X) (Category.id_comp _) j x = x) :
    FMap Model.Sm (perCOf r C₀ c ι φ σ q k) r.iso (dat Amp) (fun {M N u hu a b} _ j =>
      (Model.pullH (M := M) (N := N) u hu true j).lim.toAddMonoidHom) :=
  { k := N
    ψ := fun {M} _ j => psiF r F c k hk hl M j
    fin := fun M hM j => by
      have := hfin M hM j
      exact (inferInstance : Module.Finite (Wc.K₀ l r.k) (Wc.K₀ l r.k ⊗[WittVector l r.k] LW r M j))
    pull_id := hid
    lin := fun {M} _ hM j a x f => psiF_lin r F c k hk hl M hM j a x f
    lin' := fun {M} _ _ j z x f => psiF_lin' r F c k hk hl M j z x f
    act := fun {M} _ hM j g x f => psiF_act r F c k hk hl σ hC.σ_c hσk M hM j g x f
    phi := fun {M} _ hM j _ b x f => psiF_phi r F c k hk hl φ hC.φ_c hφk M hM j b x f
    nat := fun {M M'} {u hu} {_ _} _ hM hM' j x f => psiF_nat r F c k hk hl M M' u hu hM hM' j x f
    fac := fun {M} _ hM j _ b => psiF_fac r F c k hk hl ι hC.ι_c hR hσw M hM j b }

end CrystallineSemistableComparison.Pb
