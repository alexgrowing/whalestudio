import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.GammaKey
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PullRId
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PullTId

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def tmV (M : Model l K) (n : ℕ) (z : ℚ_[l]) (u : M.T n) : M.V n := (z ⊗ₜ[ℤ_[l]] u : ℚ_[l] ⊗[ℤ_[l]] M.T n)

theorem toV_eq (M : Model l K) (n : ℕ) (u : M.T n) : M.toV n u = tmV M n 1 u := rfl

theorem V_induction {M : Model l K} {n : ℕ} {p : M.V n → Prop} (v : M.V n) (h0 : p 0)
    (ht : ∀ z u, p (tmV M n z u)) (ha : ∀ x y, p x → p y → p (x + y)) : p v :=
  TensorProduct.induction_on (R := ℤ_[l]) (M := ℚ_[l]) (N := M.T n) (motive := p) v h0 ht ha

theorem act_tmV (M : Model l K) (n : ℕ) (σ : K.fixingSubgroup) (z : ℚ_[l]) (u : M.T n) :
    M.act n σ (tmV M n z u) = tmV M n z (M.actT n σ u) := rfl

theorem pullV_tmV {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (z : ℚ_[l]) (w : N.T n) :
    Model.pullV u hu n (tmV N n z w) = tmV M n z (Model.pullT u hu n w) := rfl

theorem smul_tmV (M : Model l K) (n : ℕ) (c z : ℚ_[l]) (u : M.T n) : c • tmV M n z u = tmV M n (c * z) u :=
  TensorProduct.smul_tmul' c z _

variable {R : Per l K} {G : Model l K → Prop} {D : Dat R} (hF : R.Facts) (hL : D.Laws G) (E : EMap G D)
  (β : BMap G D) (κ : PMap G D)

theorem gammaE_nat {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}
    (m : D.Mo u hu a b) (hM : G M) (hN : G N) (n : ℕ) (w : N.T n) (φ : Module.Dual K (HdR M.q n)) :
    gamma hF β κ a n (E.e a n (Model.pullT u hu n w)) φ =
      gamma hF β κ b n (E.e b n w) (φ ∘ₗ pullR n (Model.genMap u hu) (Model.genMap_q u hu)) := by
  rw [E.nat m hM hN, gamma_nat hF β κ m hM hN]

theorem gammaE_id {M : Model l K} {a a' : D.Ch M} (m : D.Mo (𝟙 M.X) (Category.id_comp _) a' a) (hM : G M) (n : ℕ)
    (u : M.T n) (φ : Module.Dual K (HdR M.q n)) :
    gamma hF β κ a' n (E.e a' n u) φ = gamma hF β κ a n (E.e a n u) φ := by
  have := gammaE_nat hF E β κ m hM hM n u φ
  rw [pullT_id, LinearMap.id_apply, pullR_genMap_id, LinearMap.comp_id] at this
  exact this

include hL in

theorem gammaE_indep {M : Model l K} (hM : G M) (a a' : D.Ch M) (n : ℕ) (u : M.T n) (φ : Module.Dual K (HdR M.q n)) :
    gamma hF β κ a n (E.e a n u) φ = gamma hF β κ a' n (E.e a' n u) φ := by
  obtain ⟨b, ⟨m₁⟩, ⟨m₂⟩⟩ := hL.refine M M (𝟙 M.X) (Category.id_comp _) hM hM a a'
  rw [← gammaE_id hF E β κ m₁ hM, gammaE_id hF E β κ m₂ hM]

def cV {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) : M.V n →+ (Module.Dual K (HdR M.q n) →+ R.B) :=
  (TensorProduct.liftAddHom (R := ℤ_[l]) (M := ℚ_[l]) (N := M.T n)
    (AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (fun u =>
      AddMonoidHom.mk' (fun φ => R.q z * gamma hF β κ a n (E.e a n u) φ) (by intros; simp [mul_add]))
        (by intros; ext; simp [mul_add])) (by intros; ext; simp [add_mul]))
    (by
      intro r z u
      ext φ
      simp only [AddMonoidHom.mk'_apply]
      rw [E.lin a hM n r u, gamma_smul hF β κ hM, hF.thetaSetup_structureMap_comp, Algebra.smul_def, map_mul]
      simp only [PadicInt.algebraMap_apply]
      ring) :
    ℚ_[l] ⊗[ℤ_[l]] M.T n →+ (Module.Dual K (HdR M.q n) →+ R.B))

theorem cV_tmV {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) (z : ℚ_[l]) (u : M.T n) (φ : Module.Dual K (HdR M.q n)) :
    cV hF E β κ hM a n (tmV M n z u) φ = R.q z * gamma hF β κ a n (E.e a n u) φ := by
  unfold cV tmV
  erw [TensorProduct.liftAddHom_tmul]
  rfl

def a0 (M : Model l K) (hM : G M) : D.Ch M := Classical.choice (hL.ch M hM)

open Classical in

def cP (M : Model l K) (n : ℕ) : M.V n →+ (Module.Dual K (HdR M.q n) →+ R.B) :=
  if hM : G M then cV hF E β κ hM (a0 hL M hM) n else 0

theorem cP_tmV {M : Model l K} (hM : G M) (n : ℕ) (z : ℚ_[l]) (u : M.T n) (φ : Module.Dual K (HdR M.q n)) :
    cP hF hL E β κ M n (tmV M n z u) φ = R.q z * gamma hF β κ (a0 hL M hM) n (E.e _ n u) φ := by
  rw [cP, dif_pos hM, cV_tmV]

theorem cP_toV {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) (u : M.T n) (φ : Module.Dual K (HdR M.q n)) :
    cP hF hL E β κ M n (M.toV n u) φ = gamma hF β κ a n (E.e a n u) φ := by
  rw [toV_eq, cP_tmV hF hL E β κ hM, map_one, one_mul, gammaE_indep hF hL E β κ hM]

theorem cP_not {M : Model l K} (hM : ¬ G M) (n : ℕ) (v : M.V n) (φ : Module.Dual K (HdR M.q n)) :
    cP hF hL E β κ M n v φ = 0 := by
  rw [cP, dif_neg hM]; rfl

include hL in

theorem isPow_beta (hE : EtSide G) {M : Model l K} (hM : G M) (a : D.Ch M) (x : (D.H a).N 2) (hx : D.c1H a x) :
    ∀ (k : ℕ) (z : (D.H a).N (2 * k)), IsPow (N := (D.H a).N) (D.H a).one (D.H a).cup x k z →
      ∃ v : M.T (2 * k), β.β a (2 * k) z = R.t ^ k • E.e a (2 * k) v := by
  intro k
  induction k with
  | zero =>
    intro z h
    obtain ⟨v₀, hv₀⟩ := E.one a hM
    exact ⟨v₀, by rw [pow_zero, one_smul]; exact hL.one_uniq a _ _ (β.one a hM z h) hv₀⟩
  | succ k ih =>
    intro z h
    obtain ⟨y, hy, hc⟩ := h
    obtain ⟨v, hv⟩ := ih y hy
    obtain ⟨v₁, hv₁⟩ := E.c1 a hM
    have e₁ := hL.first_chern_class_unique a _ _ (β.c1 a hM x hx) hv₁
    obtain ⟨w, hw⟩ := hE.cup_ex M v v₁
    have hA := hL.cup_smul a (R.t ^ k) R.t _ _ _ (E.cup a hM v v₁ w hw)
    have hB := β.cup a hM y x z hc
    rw [hv, e₁] at hB
    exact ⟨w, (hL.cup_uniq a _ _ _ _ hB hA).trans (by rw [pow_succ]; exact rfl)⟩

def preP (hE : EtSide G) : Pre G R where
  c := cP hF hL E β κ
  cupR := κ.cupR
  lin M n z v φ := by
    by_cases hM : G M
    · refine V_induction (p := fun v => cP hF hL E β κ M n (z • v) φ = R.q z * cP hF hL E β κ M n v φ) v ?_ ?_ ?_
      · simp only [smul_zero, map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        rw [smul_tmV, cP_tmV hF hL E β κ hM, cP_tmV hF hL E β κ hM, map_mul, mul_assoc]
      · intro x y hx hy
        simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hy, mul_add]
    · rw [cP_not hF hL E β κ hM, cP_not hF hL E β κ hM, mul_zero]
  lin' M n k v φ := by
    by_cases hM : G M
    · refine V_induction (p := fun v => cP hF hL E β κ M n v (k • φ) = R.o k * cP hF hL E β κ M n v φ) v ?_ ?_ ?_
      · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z u
        rw [cP_tmV hF hL E β κ hM, cP_tmV hF hL E β κ hM, gamma_lin' hF β κ hM]
        ring
      · intro x y hx hy
        simp only [map_add, AddMonoidHom.add_apply, hx, hy, mul_add]
    · rw [cP_not hF hL E β κ hM, cP_not hF hL E β κ hM, mul_zero]
  fin := κ.fin
  top := κ.top
  cupR_fil := κ.cupR_fil
  equi M n hM σ v φ := by
    refine V_induction (p := fun v => cP hF hL E β κ M n (M.act n σ v) φ = R.σ σ (cP hF hL E β κ M n v φ)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply]
    · intro z u
      rw [act_tmV, cP_tmV hF hL E β κ hM, cP_tmV hF hL E β κ hM, E.act _ hM, gamma_act hF β κ hL hM, map_mul, hF.σ_q]
    · intro x y hx hy
      simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  fil M n hM r v φ hφ := by
    refine V_induction (p := fun v => R.tB ^ r * cP hF hL E β κ M n v φ ∈ R.P) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
      exact R.P.zero_mem
    · intro z u
      rw [cP_tmV hF hL E β κ hM, mul_left_comm]
      exact R.P.mul_mem (hF.q_mem z) (gamma_fil hF β κ hM n r _ φ hφ)
    · intro x y hx hy
      rw [map_add, AddMonoidHom.add_apply, mul_add]
      exact R.P.add_mem hx hy
  nat M N u hu n hM hN v φ := by
    refine V_induction (p := fun v => cP hF hL E β κ M n (Model.pullV u hu n v) φ =
      cP hF hL E β κ N n v (φ ∘ₗ pullR n (Model.genMap u hu) (Model.genMap_q u hu))) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply]
    · intro z w
      rw [pullV_tmV, cP_tmV hF hL E β κ hM, cP_tmV hF hL E β κ hN]
      congr 1
      obtain ⟨a', -, ⟨m⟩⟩ := hL.refine M N u hu hM hN (a0 hL M hM) (a0 hL N hN)
      rw [gammaE_indep hF hL E β κ hM (a0 hL M hM) a', gammaE_nat hF E β κ m hM hN]
    · intro x y hx hy
      simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  cup M hM := by
    intro i j x y z hxyz m m' b b' φ
    simp only [cP_toV hF hL E β κ hM (a0 hL M hM)]
    exact gamma_cup hF β κ hL hM _ _ _ (E.cup _ hM x y z hxyz) b b' φ
  c1 M hM d hd := by
    obtain ⟨x, z, φ, hx, hz, hu⟩ := κ.c1 (a0 hL M hM) hM d hd
    obtain ⟨v, hv⟩ := isPow_beta hL E β hE hM _ x hx d z hz
    refine ⟨M.toV (2 * d) v, φ, ?_⟩
    rw [cP_toV hF hL E β κ hM (a0 hL M hM)]
    rw [gamma_key hF β κ hM hv, map_pow] at hu
    exact hu

theorem cP_span {M : Model l K} (hM : G M) (G' : Model l K → Prop) (S : Subring R.B) (ht : (R.tB)⁻¹ ∈ S)
    (hq : ∀ z, R.q z ∈ S) (hS : D.Span G' S) (hM' : G' M) (n : ℕ) :
    ∃ (r : ℕ) (w : Fin r → Module.Dual K (HdR M.q n) → R.B), (∀ i φ (σ : K.fixingSubgroup), R.σ σ (w i φ) = w i φ) ∧
      ∀ v, ∃ b : Fin r → R.B, (∀ i, b i ∈ S) ∧ ∀ φ, cP hF hL E β κ M n v φ = ∑ i, b i * w i φ := by
  obtain ⟨k, r, w', hw', hsp⟩ := hS M hM' (a0 hL M hM) n
  obtain ⟨n', hn'⟩ := β.surj' (a0 hL M hM) hM n
  let f : Module.Dual K (HdR M.q n) → ((D.H' (a0 hL M hM)).N n →+ R.B) := fun φ =>
    (AddMonoidHom.eval φ).comp ((gamma hF β κ (a0 hL M hM) n).comp (β.β' (a0 hL M hM) n).toAddMonoidHom)
  have hf : ∀ φ y, f φ y = gamma hF β κ (a0 hL M hM) n (β.β' (a0 hL M hM) n y) φ := fun _ _ => rfl
  have hFn : ∀ φ, GMod.Fn R (D.H' (a0 hL M hM)) n (f φ) := fun φ =>
    ⟨fun c y => by rw [hf, hf, map_smul, gamma_smul hF β κ hM],
     fun σ y => by rw [hf, hf, β.act' _ hM, gamma_act hF β κ hL hM]⟩
  have hc : ∀ (j : ℕ) (x : (D.H' (a0 hL M hM)).N n) (u : M.T n),
      β.β' (a0 hL M hM) n x = R.t ^ n' • E.e (a0 hL M hM) n u →
      β.β' (a0 hL M hM) n ((D.phi' (a0 hL M hM) n)^[j] x) = (((l : R.A) ^ j * R.t) ^ n') • E.e (a0 hL M hM) n u := by
    intro j x u h
    induction j with
    | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]; exact h
    | succ j ih =>
      rw [Function.iterate_succ_apply', β.phi' _ hM, ih, hL.phi_smul, E.phi _ hM]
      congr 1
      rw [map_pow, map_mul, map_pow, map_natCast, hF.frobenius_period]
      ring
  have hl : (l : R.B) ≠ 0 := by
    rw [← map_natCast R.q]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hic : R.i (((l : R.A) ^ k * R.t) ^ n') = ((l : R.B) ^ k * R.tB) ^ n' := by
    simp only [map_pow, map_mul, map_natCast]; rfl
  have hi : R.i (((l : R.A) ^ k * R.t) ^ n') ≠ 0 := by
    rw [hic]; exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hl) hF.t_ne)
  have hiS : (R.i (((l : R.A) ^ k * R.t) ^ n'))⁻¹ ∈ S := by
    rw [hic, ← inv_pow, mul_inv, ← inv_pow]
    refine S.pow_mem (S.mul_mem (S.pow_mem ?_ _) ht) _
    rw [← map_natCast R.q, ← map_inv₀]
    exact hq _
  have hu : ∀ u : M.T n, ∃ b : Fin r → R.B, (∀ i, b i ∈ S) ∧
      ∀ φ, gamma hF β κ (a0 hL M hM) n (E.e (a0 hL M hM) n u) φ = ∑ i, b i * w' i (f φ) := by
    intro u
    obtain ⟨x, hx⟩ := hn' (E.e (a0 hL M hM) n u)
    obtain ⟨b, hbS, hb⟩ := hsp x
    refine ⟨fun i => (R.i (((l : R.A) ^ k * R.t) ^ n'))⁻¹ * b i, fun i => S.mul_mem hiS (hbS i), fun φ => ?_⟩
    have h1 := hb (f φ) (hFn φ)
    rw [hf, hc k x u hx, gamma_smul hF β κ hM] at h1
    simp only [mul_assoc]
    rw [← Finset.mul_sum, ← h1, ← mul_assoc, inv_mul_cancel₀ hi, one_mul]
  refine ⟨r, fun i φ => w' i (f φ), fun i φ σ => hw' (f φ) (hFn φ) i σ, fun v => ?_⟩
  refine V_induction (p := fun v => ∃ b : Fin r → R.B, (∀ i, b i ∈ S) ∧
    ∀ φ, cP hF hL E β κ M n v φ = ∑ i, b i * w' i (f φ)) v ?_ ?_ ?_
  · exact ⟨0, fun _ => S.zero_mem, fun φ => by simp⟩
  · intro z u
    obtain ⟨b, hbS, hb⟩ := hu u
    refine ⟨fun i => R.q z * b i, fun i => S.mul_mem (hq z) (hbS i), fun φ => ?_⟩
    rw [cP_tmV hF hL E β κ hM, hb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rintro x y ⟨b, hbS, hb⟩ ⟨b', hbS', hb'⟩
    refine ⟨b + b', fun i => S.add_mem (hbS i) (hbS' i), fun φ => ?_⟩
    rw [map_add, AddMonoidHom.add_apply, hb, hb', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_mul]

def PrepairingEtaleValue : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (R : Per l K)
  (G : Model l K → Prop) (D : Dat R) (hF : R.Facts), EtSide G → D.Laws G → ∀ (E : EMap G D) (β : BMap G D) (κ : PMap G D),
    ∃ P : Pre G R, (∀ (G' : Model l K → Prop) (S : Subring R.B), (R.tB)⁻¹ ∈ S → (∀ z, R.q z ∈ S) → D.Span G' S →
      ∀ M, G M → G' M → ∀ n, P.Span M n S) ∧
      ∀ M, G M → ∀ (a : D.Ch M) (n : ℕ) (v : M.T n) (φ : Module.Dual K (HdR M.q n)),
        P.c M n (M.toV n v) φ = gamma hF β κ a n (E.e a n v) φ

theorem pre' : PrepairingEtaleValue := by
  intro l _ K R G D hF hE hL E β κ
  exact ⟨preP hF hL E β κ hE, fun G' S ht hq hS M hM hM' n => cP_span hF hL E β κ hM G' S ht hq hS hM' n,
    fun M hM a n v φ => cP_toV hF hL E β κ hM a n v φ⟩

theorem pre : ComparisonPairing := by
  intro l _ K R G D hF hE hL E β κ
  exact (pre' l K R G D hF hE hL E β κ).imp fun _ h => h.1

end CrystallineSemistableComparison
