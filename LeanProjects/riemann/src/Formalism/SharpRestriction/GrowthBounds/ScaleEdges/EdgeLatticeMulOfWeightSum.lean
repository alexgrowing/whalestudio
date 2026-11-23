import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleNegMono
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

theorem lamAt_add {n' m : ℕ} (lam mu : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (lam + mu) s = lamAt lam s + lamAt mu s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply, neg_add]

theorem Ar_add {n' m : ℕ} (r : ℕ) (lam mu : Fin n' → Fin (m + 1) → ℤ) :
    Ar r (lam + mu) = Ar r lam + Ar r mu := by
  unfold Ar
  simp only [lamAt_add, Pi.add_apply, Finset.sum_add_distrib]

theorem isDominant_add {n' m : ℕ} {lam mu : Fin n' → Fin (m + 1) → ℤ} (h1 : IsDominant lam) (h2 : IsDominant mu) :
    IsDominant (lam + mu) := by
  intro s
  exact (h1 s).add (h2 s)

theorem nuOf_add {m : ℕ} {a b : Fin (m + 1) → ℤ} (ha : Antitone a) (hb : Antitone b) :
    nuOf (a + b) = nuOf a + nuOf b := by
  funext t
  have h1 : 0 ≤ a t - a (Fin.last m) := sub_nonneg.2 (ha (Fin.le_last t))
  have h2 : 0 ≤ b t - b (Fin.last m) := sub_nonneg.2 (hb (Fin.le_last t))
  simp only [nuOf, Pi.add_apply]
  rw [show a t + b t - (a (Fin.last m) + b (Fin.last m)) =
      (a t - a (Fin.last m)) + (b t - b (Fin.last m)) by ring]
  exact Int.toNat_add h1 h2

theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ)
    {F G : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) (hG : G ∈ dualWeyl R r n ν') :
    F * G ∈ dualWeyl R r n (ν + ν') := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hF hG ⊢
  refine ⟨hF.1.mul hG.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hF.2 l j hlj, hG.2 l j hlj]

theorem tensorLat_mul (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M M' M'' : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ M s, ∀ G ∈ M' s, F * G ∈ M'' s)
    {x y : MvPolynomial (S × (Fin k × Fin n)) K} (hx : x ∈ tensorLat R K M) (hy : y ∈ tensorLat R K M') :
    x * y ∈ tensorLat R K M'' := by
  have key : tensorLat R K M * tensorLat R K M' ≤ tensorLat R K M'' := by
    unfold tensorLat
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
    refine ⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), ?_⟩
    simp only [map_mul, Finset.prod_mul_distrib]
  exact key (Submodule.mul_mem_mul hx hy)

theorem V_mul (Kf : Type*) [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu)
    {x y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf} (hx : x ∈ Vsp Kf lam) (hy : y ∈ Vsp Kf mu) :
    x * y ∈ Vsp Kf nu := by
  subst hnu
  unfold Vsp at hx hy ⊢
  refine tensorLat_mul Kf Kf _ _ _ ?_ hx hy
  intro s F hF G hG
  have hs := lamAt_add lam mu s
  by_cases ha : Antitone (lamAt lam s)
  · by_cases hb : Antitone (lamAt mu s)
    · have hab : Antitone (lamAt (lam + mu) s) := by
        rw [hs]
        exact ha.add hb
      rw [if_pos ha] at hF
      rw [if_pos hb] at hG
      rw [if_pos hab, hs, nuOf_add ha hb]
      exact dualWeyl_mul Kf (m + 1) (m + 1) _ _ hF hG
    · rw [if_neg hb, Submodule.mem_bot] at hG
      rw [hG, mul_zero]
      exact Submodule.zero_mem _
  · rw [if_neg ha, Submodule.mem_bot] at hF
    rw [hF, zero_mul]
    exact Submodule.zero_mem _

def mulV {Kf : Type*} [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (x : Vsp Kf lam) (y : Vsp Kf mu) : Vsp Kf nu :=
  ⟨(x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y, V_mul Kf hnu h1 h2 x.2 y.2⟩

@[simp] theorem mulV_coe {Kf : Type*} [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ}
    (hnu : nu = lam + mu) (h1 : IsDominant lam) (h2 : IsDominant mu) (x : Vsp Kf lam) (y : Vsp Kf mu) :
    ((mulV hnu h1 h2 x y : Vsp Kf nu) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y := rfl

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_scale (a b : Kf) (M : Submodule O X) : scale a (scale b M) = scale (a * b) M := by
  unfold scale
  rw [← Submodule.map_comp]
  congr 1
  ext x
  show a • (b • x) = (a * b) • x
  rw [mul_smul]

end Scale

section Lat

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}

theorem toV_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) (α β : Kf)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale α (toV lam (Hten O lam Λ))) (hy : y ∈ scale β (toV mu (Hten O mu Λ))) :
    z ∈ scale (α * β) (toV nu (Hten O nu Λ)) := by
  subst hnu
  obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.1 hy
  have hmem : ((x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y0) ∈ Hten O (lam + mu) Λ :=
    hM O Kf n' m lam mu Λ h1 h2 _ (Submodule.mem_comap.1 hx0) _ (Submodule.mem_comap.1 hy0)
  refine Submodule.mem_map.2 ⟨⟨(x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y0,
    V_mul Kf rfl h1 h2 x0.2 y0.2⟩, hmem, ?_⟩
  apply Subtype.ext
  rw [hz]
  show (α * β) • ((x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
      (y0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) =
    (α • (x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) * (β • (y0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
  rw [smul_mul_smul_comm]

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem HL_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (L : Submodule W (Fin (m + 1) → Qq)) (c : Kf) (hc : c ≠ 0) (a b : ℤ)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale (c ^ a) (HL (O := O) ι σ lam L)) (hy : y ∈ scale (c ^ b) (HL (O := O) ι σ mu L)) :
    z ∈ scale (c ^ (a + b)) (HL (O := O) ι σ nu L) := by
  rw [zpow_add₀ hc]
  exact toV_mul D hM hnu h1 h2 _ _ _ hz hx hy

theorem Re_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O)
    (hw : algebraMap O Kf w ≠ 0) (r : ℕ)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (e : Edge W Qq (m + 1)) (a b : ℤ)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale (algebraMap O Kf w ^ a) (Re p ι σ w r lam e))
    (hy : y ∈ scale (algebraMap O Kf w ^ b) (Re p ι σ w r mu e)) :
    z ∈ scale (algebraMap O Kf w ^ (a + b)) (Re p ι σ w r nu e) := by
  subst hnu
  unfold Re HLe at hx hy ⊢
  rw [scale_scale] at hx hy ⊢
  have hz' := toV_mul D hM rfl h1 h2 _ _ _ hz hx hy
  convert hz' using 2
  rw [Ar_add, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw]
  congr 1
  ring

theorem edge_lattice_mul_of_weight_sum (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O)
    (hw : algebraMap O Kf w ≠ 0) (r : ℕ)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (e : Edge W Qq (m + 1))
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ Re p ι σ w r lam e) (hy : y ∈ Re p ι σ w r mu e) : z ∈ Re p ι σ w r nu e := by
  have h1s : ∀ {lam0 : Fin n' → Fin (m + 1) → ℤ} (M : Submodule O (Vsp Kf lam0)), scale (1 : Kf) M = M := by
    intro lam0 M
    unfold scale
    have hid : (LinearMap.lsmul Kf (Vsp Kf lam0) (1 : Kf)).restrictScalars O = LinearMap.id :=
      LinearMap.ext fun v => by simp
    rw [hid, Submodule.map_id]
  have := Re_mul D hM p ι σ w hw r hnu h1 h2 e 0 0 hz (by rw [zpow_zero, h1s]; exact hx)
    (by rw [zpow_zero, h1s]; exact hy)
  rwa [add_zero, zpow_zero, h1s] at this

end Lat

end Formalism.MainNotions.Pf14
