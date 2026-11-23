import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PrepairingEtaleValue
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PhiAbs

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {G : Model l K → Prop}
  {D : Dat R} {C : PerC R} {I : Iso l K C.K₀}

def iP (C : PerC R) (k : ℕ) : R.A →+* C.C := C.c.comp (R.φ ^ k)

theorem iP_apply (C : PerC R) (k : ℕ) (c : R.A) : iP C k c = C.c (R.φ^[k] c) := by
  rw [iP, RingHom.comp_apply, RingHom.coe_pow]

theorem phiA_iterate_tA_of_prime (hF : R.Facts) (m n : ℕ) : R.φ^[m] (R.t ^ n) = ((l : R.A) ^ m * R.t) ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_pow, map_mul, map_pow, map_natCast, hF.frobenius_period]
    ring

theorem l_unit (C : PerC R) : IsUnit ((l : C.C)) := by
  rw [← map_natCast C.q]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)).map C.q

theorem c_unit (hF : R.Facts) (hC : C.Facts) (m n : ℕ) : IsUnit (C.c (R.φ^[m] (R.t ^ n))) := by
  rw [phiA_iterate_tA_of_prime hF, map_pow, map_mul, map_pow, map_natCast]
  exact (((l_unit C).pow m).mul hC.t_unit).pow n

def dN (β : BMap G D) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) : ℕ := (β.surj' a hM j).choose

def dX (β : BMap G D) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) (y : (D.A a).N j) : (D.H' a).N j :=
  ((β.surj' a hM j).choose_spec y).choose

theorem dX_spec (β : BMap G D) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) (y : (D.A a).N j) :
    β.β' a j (dX β a hM j y) = R.t ^ dN β a hM j • y := ((β.surj' a hM j).choose_spec y).choose_spec

variable {β : BMap G D} {β₁ : BPhi β}

theorem psi_lin (Fm : FMap G C I D β₁.pull) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) (c : R.A)
    (x : (D.H' a).N j) (f : Module.Dual C.K₀ (I.D M j)) : Fm.ψ a j (c • x) f = iP C Fm.k c * Fm.ψ a j x f := by
  rw [Fm.lin a hM, iP_apply]

open Classical in

def delta (hF : R.Facts) (hC : C.Facts) (Fm : FMap G C I D β₁.pull) {M : Model l K} (a : D.Ch M) (j : ℕ) :
    (D.A a).N j →+ (Module.Dual C.K₀ (I.D M j) →+ C.C) :=
  if hM : G M then
    GamU.hom (psi_lin Fm a hM j) (by rw [iP_apply, ← pow_one R.t]; exact c_unit hF hC _ 1) (β₁.inj a hM j)
      (dN β a hM j) (dX β a hM j) (dX_spec β a hM j)
  else 0

theorem iP_unit (hF : R.Facts) (hC : C.Facts) (m n : ℕ) : IsUnit (iP C m (R.t ^ n)) := by
  rw [iP_apply]; exact c_unit hF hC m n

theorem periodMap_z_eq_cast (hF : R.Facts) (hC : C.Facts) (k : ℕ) (r : ℤ_[l]) : iP C k (R.z r) = C.q (algebraMap ℤ_[l] ℚ_[l] r) := by
  rw [iP_apply, Function.iterate_fixed (hC.frobenius_fixes_z r)]
  apply hC.ι_inj
  rw [hC.ι_c, hC.ι_q, hF.thetaSetup_structureMap_comp, PadicInt.algebraMap_apply]

variable (hF : R.Facts) (hC : C.Facts) (Fm : FMap G C I D β₁.pull)

theorem delta_key {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} {c : R.A} {x : (D.H' a).N j} {y : (D.A a).N j}
    (h : β.β' a j x = c • y) (f : Module.Dual C.K₀ (I.D M j)) :
    Fm.ψ a j x f = iP C Fm.k c * delta hF hC Fm a j y f := by
  rw [delta, dif_pos hM]
  exact GamU.hom_key _ _ _ _ _ _ h f

theorem delta_key' {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (y : (D.A a).N j) (f : Module.Dual C.K₀ (I.D M j)) :
    Fm.ψ a j (dX β a hM j y) f = iP C Fm.k (R.t ^ dN β a hM j) * delta hF hC Fm a j y f :=
  delta_key hF hC Fm hM (dX_spec β a hM j y) f

theorem delta_smul {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (c : R.A) (y : (D.A a).N j)
    (f : Module.Dual C.K₀ (I.D M j)) : delta hF hC Fm a j (c • y) f = iP C Fm.k c * delta hF hC Fm a j y f := by
  have h1 := delta_key hF hC Fm hM (x := c • dX β a hM j y) (c := R.t ^ dN β a hM j) (y := c • y)
    (by rw [map_smul, dX_spec, smul_comm]) f
  rw [psi_lin Fm a hM, delta_key' hF hC Fm hM] at h1
  apply (iP_unit hF hC Fm.k (dN β a hM j)).mul_left_cancel
  linear_combination -h1

theorem delta_lin' {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (y : (D.A a).N j) (k : C.K₀)
    (f : Module.Dual C.K₀ (I.D M j)) : delta hF hC Fm a j y (k • f) = C.k k * delta hF hC Fm a j y f := by
  have h1 := delta_key' hF hC Fm hM y (k • f)
  rw [Fm.lin' a hM, delta_key' hF hC Fm hM] at h1
  apply (iP_unit hF hC Fm.k (dN β a hM j)).mul_left_cancel
  linear_combination -h1

theorem delta_act (hL : D.Laws G) {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (σ : K.fixingSubgroup)
    (y : (D.A a).N j) (f : Module.Dual C.K₀ (I.D M j)) :
    delta hF hC Fm a j ((D.A a).act j σ y) f = C.σ σ (delta hF hC Fm a j y f) := by
  have h1 := delta_key hF hC Fm hM (x := (D.H' a).act j σ (dX β a hM j y)) (c := R.σA σ (R.t ^ dN β a hM j))
    (y := (D.A a).act j σ y) (by rw [β.act' a hM, dX_spec, hL.act_smul]) f
  rw [Fm.act a hM, delta_key' hF hC Fm hM, map_mul] at h1
  have e : iP C Fm.k (R.σA σ (R.t ^ dN β a hM j)) = C.σ σ (iP C Fm.k (R.t ^ dN β a hM j)) := by
    rw [iP_apply, iP_apply, hC.σ_c, Function.Commute.iterate_left (hC.φ_σ σ) Fm.k]
  rw [e] at h1
  exact ((iP_unit hF hC Fm.k (dN β a hM j)).map (C.σ σ)).mul_left_cancel h1.symm

theorem delta_nat {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}
    (m : D.Mo u hu a b) (hM : G M) (hN : G N) (j : ℕ) (y : (D.A b).N j) (f : Module.Dual C.K₀ (I.D M j)) :
    delta hF hC Fm a j (D.pullA m j y) f = delta hF hC Fm b j y (f ∘ₗ I.pull u hu j) := by
  have h1 := delta_key hF hC Fm hM (x := β₁.pull m j (dX β b hN j y)) (c := R.t ^ dN β b hN j) (y := D.pullA m j y)
    (by rw [β₁.nat m hM hN, dX_spec, map_smul]) f
  rw [Fm.nat m hM hN, delta_key' hF hC Fm hN] at h1
  exact ((iP_unit hF hC Fm.k _).mul_left_cancel h1).symm

theorem delta_phi (hL : D.Laws G) {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (y : (D.A a).N j)
    (hy : D.phiA a j y = y) {m : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M j)) (f : Module.Dual C.K₀ (I.D M j)) :
    delta hF hC Fm a j y f = ∑ s, C.φ (delta hF hC Fm a j y (b.coord s)) * C.k (f (I.φ M j (b s))) := by
  have h1 := delta_key hF hC Fm hM (x := D.phi' a j (dX β a hM j y)) (c := R.φ (R.t ^ dN β a hM j)) (y := y)
    (by rw [β.phi' a hM, dX_spec, hL.phi_smul, hy]) f
  rw [Fm.phi a hM j b] at h1
  simp only [delta_key' hF hC Fm hM, map_mul] at h1
  have e : C.φ (iP C Fm.k (R.t ^ dN β a hM j)) = iP C Fm.k (R.φ (R.t ^ dN β a hM j)) := by
    rw [iP_apply, iP_apply, hC.φ_c, Function.Commute.self_iterate R.φ Fm.k]
  have hu : IsUnit (iP C Fm.k (R.φ (R.t ^ dN β a hM j))) := by
    rw [iP_apply, ← Function.iterate_succ_apply]; exact c_unit hF hC _ _
  simp only [e] at h1
  apply hu.mul_left_cancel
  rw [← h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

variable (hL : D.Laws G) (E : EMap G D)

theorem deltaE_nat {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}
    (m : D.Mo u hu a b) (hM : G M) (hN : G N) (n : ℕ) (w : N.T n) (f : Module.Dual C.K₀ (I.D M n)) :
    delta hF hC Fm a n (E.e a n (Model.pullT u hu n w)) f = delta hF hC Fm b n (E.e b n w) (f ∘ₗ I.pull u hu n) := by
  rw [E.nat m hM hN, delta_nat hF hC Fm m hM hN]

theorem deltaE_id {M : Model l K} {a a' : D.Ch M} (m : D.Mo (𝟙 M.X) (Category.id_comp _) a' a) (hM : G M) (n : ℕ)
    (u : M.T n) (f : Module.Dual C.K₀ (I.D M n)) :
    delta hF hC Fm a' n (E.e a' n u) f = delta hF hC Fm a n (E.e a n u) f := by
  have := deltaE_nat hF hC Fm E m hM hM n u f
  rw [pullT_id, LinearMap.id_apply] at this
  rw [this]
  exact congrArg _ (LinearMap.ext fun x => by rw [LinearMap.comp_apply, Fm.pull_id M hM n x])

include hL in

theorem deltaE_indep {M : Model l K} (hM : G M) (a a' : D.Ch M) (n : ℕ) (u : M.T n) (f : Module.Dual C.K₀ (I.D M n)) :
    delta hF hC Fm a n (E.e a n u) f = delta hF hC Fm a' n (E.e a' n u) f := by
  obtain ⟨b, ⟨m₁⟩, ⟨m₂⟩⟩ := hL.refine M M (𝟙 M.X) (Category.id_comp _) hM hM a a'
  rw [← deltaE_id hF hC Fm E m₁ hM, deltaE_id hF hC Fm E m₂ hM]

def cD {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) : M.V n →+ (Module.Dual C.K₀ (I.D M n) →+ C.C) :=
  (ExtV.ext C.q ((delta hF hC Fm a n).comp (E.e a n))
    (fun r u f => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, E.lin a hM n r u, delta_smul hF hC Fm hM, periodMap_z_eq_cast hF hC]) :
    ℚ_[l] ⊗[ℤ_[l]] M.T n →+ (Module.Dual C.K₀ (I.D M n) →+ C.C))

theorem cD_tmV {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) (z : ℚ_[l]) (u : M.T n)
    (f : Module.Dual C.K₀ (I.D M n)) : cD hF hC Fm E hM a n (tmV M n z u) f = C.q z * delta hF hC Fm a n (E.e a n u) f := by
  unfold cD tmV
  exact ExtV.ext_tmul _ z u f

open Classical in

def cC (M : Model l K) (n : ℕ) : M.V n →+ (Module.Dual C.K₀ (I.D M n) →+ C.C) :=
  if hM : G M then cD hF hC Fm E hM (a0 hL M hM) n else 0

theorem cC_tmV {M : Model l K} (hM : G M) (n : ℕ) (z : ℚ_[l]) (u : M.T n) (f : Module.Dual C.K₀ (I.D M n)) :
    cC hF hC Fm hL E M n (tmV M n z u) f = C.q z * delta hF hC Fm (a0 hL M hM) n (E.e _ n u) f := by
  rw [cC, dif_pos hM, cD_tmV]

theorem cC_toV {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) (u : M.T n) (f : Module.Dual C.K₀ (I.D M n)) :
    cC hF hC Fm hL E M n (M.toV n u) f = delta hF hC Fm a n (E.e a n u) f := by
  rw [toV_eq, cC_tmV hF hC Fm hL E hM, map_one, one_mul, deltaE_indep hF hC Fm hL E hM]

theorem cC_not {M : Model l K} (hM : ¬ G M) (n : ℕ) (v : M.V n) (f : Module.Dual C.K₀ (I.D M n)) :
    cC hF hC Fm hL E M n v f = 0 := by
  rw [cC, dif_neg hM]; rfl

def crys (hE : EtSide G) (hinj : ∀ (M : Model l K) (n : ℕ), G M → ∀ {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n))
    (z : Fin a → C.C), (∀ f, ∑ i, z i * cC hF hC Fm hL E M n (b i) f = 0) → z = 0) : CrysCmp G C I where
  c := cC hF hC Fm hL E
  lin M n z v f := by
    by_cases hM : G M
    · refine V_induction (p := fun v => cC hF hC Fm hL E M n (z • v) f = C.q z * cC hF hC Fm hL E M n v f) v ?_ ?_ ?_
      · simp only [smul_zero, map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        rw [smul_tmV, cC_tmV hF hC Fm hL E hM, cC_tmV hF hC Fm hL E hM, map_mul, mul_assoc]
      · intro x y hx hy
        simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hy, mul_add]
    · rw [cC_not hF hC Fm hL E hM, cC_not hF hC Fm hL E hM, mul_zero]
  lin' M n k v f := by
    by_cases hM : G M
    · refine V_induction (p := fun v => cC hF hC Fm hL E M n v (k • f) = C.k k * cC hF hC Fm hL E M n v f) v ?_ ?_ ?_
      · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z u
        rw [cC_tmV hF hC Fm hL E hM, cC_tmV hF hC Fm hL E hM, delta_lin' hF hC Fm hM]
        ring
      · intro x y hx hy
        simp only [map_add, AddMonoidHom.add_apply, hx, hy, mul_add]
    · rw [cC_not hF hC Fm hL E hM, cC_not hF hC Fm hL E hM, mul_zero]
  fin M n hM := ⟨hE.fin M hM n, Fm.fin M hM n⟩
  equi M n hM σ v f := by
    refine V_induction (p := fun v => cC hF hC Fm hL E M n (M.act n σ v) f = C.σ σ (cC hF hC Fm hL E M n v f)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply]
    · intro z u
      rw [act_tmV, cC_tmV hF hC Fm hL E hM, cC_tmV hF hC Fm hL E hM, E.act _ hM, delta_act hF hC Fm hL hM, map_mul,
        hC.σ_q]
    · intro x y hx hy
      simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  inj M n hM := hinj M n hM
  phi M n hM m b v f := by
    refine V_induction (p := fun v => cC hF hC Fm hL E M n v f =
      ∑ s, C.φ (cC hF hC Fm hL E M n v (b.coord s)) * C.k (f (I.φ M n (b s)))) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply, zero_mul, Finset.sum_const_zero]
    · intro z u
      simp only [cC_tmV hF hC Fm hL E hM, map_mul, hC.φ_q]
      rw [delta_phi hF hC Fm hL hM _ (E.phi _ hM n u) b f, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    · intro x y hx hy
      simp only [map_add, AddMonoidHom.add_apply, add_mul, Finset.sum_add_distrib]
      rw [hx, hy]
  nat M N u hu n hM hN v f := by
    refine V_induction (p := fun v => cC hF hC Fm hL E M n (Model.pullV u hu n v) f =
      cC hF hC Fm hL E N n v (f ∘ₗ I.pull u hu n)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply]
    · intro z w
      rw [pullV_tmV, cC_tmV hF hC Fm hL E hM, cC_tmV hF hC Fm hL E hN]
      congr 1
      obtain ⟨a', -, ⟨m⟩⟩ := hL.refine M N u hu hM hN (a0 hL M hM) (a0 hL N hN)
      rw [deltaE_indep hF hC Fm hL E hM (a0 hL M hM) a', deltaE_nat hF hC Fm E m hM hN]
    · intro x y hx hy
      simp only [map_add, AddMonoidHom.add_apply, hx, hy]

theorem cC_inj (hE : EtSide G) (κ : PMap G D) (hInj : ComparisonInjectiveStrict) (P : Pre G R)
    (hP : ∀ M, G M → ∀ (a : D.Ch M) (n : ℕ) (v : M.T n) (φ : Module.Dual K (HdR M.q n)),
      P.c M n (M.toV n v) φ = gamma hF β κ a n (E.e a n v) φ)
    (M : Model l K) (n : ℕ) (hM : G M) {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (z : Fin a → C.C)
    (hz : ∀ f, ∑ i, z i * cC hF hC Fm hL E M n (b i) f = 0) : z = 0 := by
  have := Fm.fin M hM n
  obtain ⟨w, hw, hfac⟩ := Fm.fac (a0 hL M hM) hM n (Module.finBasis C.K₀ (I.D M n))
  let f : Module.Dual K (HdR M.q n) → ((D.H' (a0 hL M hM)).N n →+ R.B) := fun φ =>
    (AddMonoidHom.eval φ).comp ((gamma hF β κ (a0 hL M hM) n).comp (β.β' (a0 hL M hM) n).toAddMonoidHom)
  have hf : ∀ φ y, f φ y = gamma hF β κ (a0 hL M hM) n (β.β' (a0 hL M hM) n y) φ := fun _ _ => rfl
  have hFn : ∀ φ, GMod.Fn R (D.H' (a0 hL M hM)) n (f φ) := fun φ =>
    ⟨fun c y => by rw [hf, hf, map_smul, gamma_smul hF β κ hM],
     fun σ y => by rw [hf, hf, β.act' _ hM, gamma_act hF β κ hL hM]⟩
  have hc : ∀ (j n' : ℕ) (x : (D.H' (a0 hL M hM)).N n) (u : M.T n),
      β.β' (a0 hL M hM) n x = R.t ^ n' • E.e (a0 hL M hM) n u →
      β.β' (a0 hL M hM) n ((D.phi' (a0 hL M hM) n)^[j] x) = R.φ^[j] (R.t ^ n') • E.e (a0 hL M hM) n u := by
    intro j n' x u h
    induction j with
    | zero => simpa using h
    | succ j ih =>
      rw [Function.iterate_succ_apply', β.phi' _ hM, ih, hL.phi_smul, E.phi _ hM, Function.iterate_succ_apply']
  have relT : ∀ (u : M.T n) (φ : Module.Dual K (HdR M.q n)), P.c M n (M.toV n u) φ =
      ∑ s, C.ι (cC hF hC Fm hL E M n (M.toV n u) ((Module.finBasis C.K₀ (I.D M n)).coord s)) * w s (f φ) := by
    intro u φ
    obtain ⟨n', hn'⟩ := β.surj' (a0 hL M hM) hM n
    obtain ⟨x, hx⟩ := hn' (E.e (a0 hL M hM) n u)
    have h1 := hfac x (f φ) (hFn φ)
    rw [hf, hc Fm.k n' x u hx, gamma_smul hF β κ hM, ← hP M hM (a0 hL M hM)] at h1
    simp only [delta_key hF hC Fm hM hx, cC_toV hF hC Fm hL E hM (a0 hL M hM), map_mul, hC.ι_c, iP_apply] at h1 ⊢
    have hne : R.i (R.φ^[Fm.k] (R.t ^ n')) ≠ 0 := by
      rw [← hC.ι_c]; exact ((c_unit hF hC _ _).map C.ι).ne_zero
    apply mul_left_cancel₀ hne
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have relV : ∀ (v : M.V n) (φ : Module.Dual K (HdR M.q n)), P.c M n v φ =
      ∑ s, C.ι (cC hF hC Fm hL E M n v ((Module.finBasis C.K₀ (I.D M n)).coord s)) * w s (f φ) := by
    intro v φ
    refine V_induction (p := fun v => P.c M n v φ =
      ∑ s, C.ι (cC hF hC Fm hL E M n v ((Module.finBasis C.K₀ (I.D M n)).coord s)) * w s (f φ)) v ?_ ?_ ?_
    · simp
    · intro z u
      have e1 : tmV M n z u = z • M.toV n u := by rw [toV_eq, smul_tmV, mul_one]
      rw [e1, P.lin, relT u φ, Finset.mul_sum, ← e1]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [cC_tmV hF hC Fm hL E hM, cC_toV hF hC Fm hL E hM (a0 hL M hM), map_mul, hC.ι_q]
      ring
    · intro x y hx hy
      rw [map_add, AddMonoidHom.add_apply, hx, hy, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [map_add, AddMonoidHom.add_apply, map_add, add_mul]
  have hz' := (hInj l K R G P hF hE M hM n).1 b (fun i => C.ι (z i)) (fun φ => by
    simp only [relV, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    have h := hz ((Module.finBasis C.K₀ (I.D M n)).coord s)
    calc ∑ i, C.ι (z i) * (C.ι (cC hF hC Fm hL E M n (b i) ((Module.finBasis C.K₀ (I.D M n)).coord s)) * w s (f φ))
        = C.ι (∑ i, z i * cC hF hC Fm hL E M n (b i) ((Module.finBasis C.K₀ (I.D M n)).coord s)) * w s (f φ) := by
          rw [map_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
      _ = 0 := by rw [h, map_zero, zero_mul])
  funext i
  have h := congrFun hz' i
  exact hC.ι_inj (by simpa using h)

theorem phi_of (hInj : ComparisonInjectiveStrict) : FrobeniusComparison := by
  intro l _ K R G C I D hF hC hE hL E β β₁ κ Fm
  obtain ⟨P, -, hP⟩ := pre' l K R G D hF hE hL E β κ
  exact ⟨crys hF hC Fm hL E hE (fun M n hM => cC_inj hF hC Fm hL E hE κ hInj P hP M n hM)⟩

end CrystallineSemistableComparison
