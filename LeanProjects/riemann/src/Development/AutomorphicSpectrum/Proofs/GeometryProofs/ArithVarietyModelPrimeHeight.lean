import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPairingTorsionFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeFinalStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat_iff (R : Subalgebra o Ω) {Ix : Type} (x : Ix → Ω) : x ∈ stdLat R Ix ↔ ∀ i, x i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dotDual_iff (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (x : Fin m → Ω) :
    x ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ x ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem exists_uniform {Ix : Type} [Fintype Ix] (Rt : Subalgebra o Ω) {f : Ω} (hf : f ∈ Rt) (z : Ix → Ω)
    (h : ∀ j, ∃ m : ℕ, f ^ m * z j ∈ Rt) : ∃ m : ℕ, ∀ j, f ^ m * z j ∈ Rt := by
  classical
  choose m hm using h
  refine ⟨∑ j, m j, fun j => ?_⟩
  have hle : m j ≤ ∑ j, m j := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, add_comm, pow_add, _root_.mul_assoc]
  exact Rt.mul_mem (Rt.pow_mem hf k) (hm j)

theorem gam_key {V : Type} [AddCommGroup V] [Module Ω V] {r N : ℕ} (Rs Rt : Subalgebra o Ω)
    {w f P Q : Ω} (hw : w ≠ 0) (hf : f ∈ Rt) (hstd : ∀ a ∈ Rs, ∃ m : ℕ, f ^ m * a ∈ Rt)
    (Ws Wt : AddSubgroup (Fin r → Ω)) (hW : ∀ v ∈ Ws, ∃ m : ℕ, f ^ m • v ∈ Wt)
    (v : Fin r → V) (G C : Matrix (Fin N) (Fin N) Ω) (hGC : G * C = 1) (hC : ∀ i j, C i j ∈ Rt)
    (is it : (Fin r → Ω) →ₗ[Ω] (Fin N → Ω)) (Hs Ht : Fin N → Module.Dual Ω V)
    (om : Set (Module.Dual Ω V))
    (hs : ∀ a ∈ Ws, ∀ j, ∃ z ∈ Rs, ∑ l, is a l * G l j = Hs j (∑ k, a k • v k) + w * P * z)
    (ht : ∀ a ∈ Wt, ∀ j, ∃ z ∈ Rt, ∑ l, it a l * G l j = Ht j (∑ k, a k • v k) + w * P * z)
    (hP : P ∈ Rt) (hQ : Q ∈ Rt)
    (hΔ : ∃ m : ℕ, ∀ j, ∃ u ∈ om, f ^ m • (Hs j - Ht j) = (w * w * Q) • u)
    (hpair : ∀ u ∈ om, ∀ l ∈ Wt, w * u (∑ k, l k • v k) ∈ Rt)
    (a : Fin r → Ω) (ha : w • a ∈ Ws) : ∃ m : ℕ, f ^ m • (is a - it a) ∈ stdLat Rt (Fin N) := by
  obtain ⟨m₁, h₁⟩ := hW _ ha
  obtain ⟨m', hΔ'⟩ := hΔ
  choose u hu huE using hΔ'
  choose zs hzs hzsE using hs _ ha
  choose zt hzt hztE using ht _ h₁
  obtain ⟨m₄, hm₄⟩ := exists_uniform Rt hf zs (fun j => hstd _ (hzs j))
  refine ⟨m₁ + m' + m₄, ?_⟩
  set F : Ω := f ^ (m₁ + m' + m₄) with hF
  set A : V := ∑ k, (w • a) k • v k with hA
  have hA2 : ∑ k, (f ^ m₁ • w • a) k • v k = f ^ m₁ • A := by
    simp only [hA, Finset.smul_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_assoc]

  let y : Fin N → Ω := fun j => f ^ m₄ * Q * (w * (u j) (f ^ m₁ • A)) +
    P * (f ^ (m' + m₁) * (f ^ m₄ * zs j) - f ^ (m' + m₄) * zt j)
  have hy : ∀ j, y j ∈ Rt := fun j => by
    have h3 := hpair (u j) (hu j) _ h₁
    rw [hA2] at h3
    refine Rt.add_mem (Rt.mul_mem (Rt.mul_mem (Rt.pow_mem hf _) hQ) h3)
      (Rt.mul_mem hP (Rt.sub_mem (Rt.mul_mem (Rt.pow_mem hf _) (hm₄ j))
        (Rt.mul_mem (Rt.pow_mem hf _) (hzt j))))
  have key : ∀ j, ∑ l, (F • (is a - it a)) l * G l j = y j := fun j => by
    apply mul_left_cancel₀ hw
    have e1 := hzsE j
    have e2 := hztE j
    have e3 : f ^ m' * (Hs j A - Ht j A) = w * w * Q * (u j) A := by
      have := congrArg (fun g : Module.Dual Ω V => g A) (huE j)
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using this
    rw [hA2] at e2
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have e1' : w * ∑ l, is a l * G l j = Hs j A + w * P * zs j := by
      rw [← e1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have e2' : f ^ m₁ * (w * ∑ l, it a l * G l j) = f ^ m₁ * Ht j A + w * P * zt j := by
      have : ∑ l, f ^ m₁ * (w * it a l) * G l j = f ^ m₁ * (w * ∑ l, it a l * G l j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [← this, e2]
    have e4 : ∑ l, (F • (is a - it a)) l * G l j =
        F * (∑ l, is a l * G l j - ∑ l, it a l * G l j) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [e4]
    simp only [y, map_smul, smul_eq_mul]
    have hFe : F = f ^ m₄ * f ^ m' * f ^ m₁ := by rw [hF, pow_add, pow_add]; ring
    calc w * (F * (∑ l, is a l * G l j - ∑ l, it a l * G l j))
        = f ^ m₄ * f ^ m' * (f ^ m₁ * (w * ∑ l, is a l * G l j)
            - f ^ m₁ * (w * ∑ l, it a l * G l j)) := by rw [hFe]; ring
      _ = f ^ m₄ * f ^ m' * (f ^ m₁ * (Hs j A + w * P * zs j) - (f ^ m₁ * Ht j A + w * P * zt j)) := by
            rw [e1', e2']
      _ = f ^ m₄ * f ^ m₁ * (f ^ m' * (Hs j A - Ht j A))
            + w * (P * (f ^ (m' + m₁) * (f ^ m₄ * zs j) - f ^ (m' + m₄) * zt j)) := by
            rw [pow_add, pow_add]; ring
      _ = _ := by rw [e3]; ring
  rw [mem_stdLat_iff]
  intro l
  have hv : Matrix.vecMul (F • (is a - it a)) G = y := by
    funext j
    simp only [Matrix.vecMul, dotProduct]
    exact key j
  have hv2 : F • (is a - it a) = Matrix.vecMul y C := by
    rw [← hv, Matrix.vecMul_vecMul, hGC, Matrix.vecMul_one]
  rw [hv2]
  simp only [Matrix.vecMul, dotProduct]
  exact Rt.sum_mem fun j _ => Rt.mul_mem (hy j) (hC j l)

theorem del_key {V : Type} [AddCommGroup V] [Module Ω V] {s N : ℕ} (Rs Rt : Subalgebra o Ω)
    {w f Q : Ω} (hf : f ∈ Rt) (hstd : ∀ a ∈ Rs, ∃ m : ℕ, f ^ m * a ∈ Rt)
    (v : Fin s → V) (Wd : AddSubgroup (Fin s → Ω)) (Hs Ht : Fin N → Module.Dual Ω V)
    (om : Set (Module.Dual Ω V)) (hQ : Q ∈ Rt)
    (hΔ : ∃ m : ℕ, ∀ j, ∃ u ∈ om, f ^ m • (Hs j - Ht j) = (w * w * Q) • u)
    (hpair : ∀ u ∈ om, ∀ l ∈ Wd, w * u (∑ k, l k • v k) ∈ Rt)
    (a : Fin N → Ω) (ha : w • a ∈ stdLat Rs (Fin N)) :
    ∃ m : ℕ, f ^ m • (Fintype.linearCombination Ω (fun (i : Fin N) (k : Fin s) => Hs i (v k)) a -
      Fintype.linearCombination Ω (fun (i : Fin N) (k : Fin s) => Ht i (v k)) a) ∈ dotDual Rt Wd := by
  rw [mem_stdLat_iff] at ha
  obtain ⟨m₁, hm₁⟩ := exists_uniform Rt hf (fun i => (w • a) i) (fun i => hstd _ (ha i))
  obtain ⟨m', hΔ'⟩ := hΔ
  choose u hu huE using hΔ'
  refine ⟨m₁ + m', ?_⟩
  rw [mem_dotDual_iff]
  intro l hl
  have e : l ⬝ᵥ (f ^ (m₁ + m') • (Fintype.linearCombination Ω (fun (i : Fin N) (k : Fin s) => Hs i (v k)) a -
      Fintype.linearCombination Ω (fun (i : Fin N) (k : Fin s) => Ht i (v k)) a)) =
      ∑ i, (f ^ m₁ * (w • a) i) * Q * (w * u i (∑ k, l k • v k)) := by
    have e3 : ∀ i, f ^ m' * (Hs i (∑ k, l k • v k) - Ht i (∑ k, l k • v k)) =
        w * w * Q * (u i) (∑ k, l k • v k) := fun i => by
      have := congrArg (fun g : Module.Dual Ω V => g (∑ k, l k • v k)) (huE i)
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using this
    have e5 : ∀ i, (f ^ m₁ * (w • a) i) * Q * (w * u i (∑ k, l k • v k)) =
        f ^ m₁ * a i * (f ^ m' * (Hs i (∑ k, l k • v k) - Ht i (∑ k, l k • v k))) := fun i => by
      rw [e3]; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hl2 : l ⬝ᵥ (f ^ (m₁ + m') • (Fintype.linearCombination Ω (fun (i : Fin N) (k : Fin s) => Hs i (v k)) a -
        Fintype.linearCombination Ω (fun (i : Fin N) (k : Fin s) => Ht i (v k)) a)) =
        ∑ i, f ^ m₁ * a i * (f ^ m' * (Hs i (∑ k, l k • v k) - Ht i (∑ k, l k • v k))) := by
      simp only [map_sum, map_smul, smul_eq_mul, dotProduct, Pi.smul_apply, Pi.sub_apply,
        Fintype.linearCombination_apply, Finset.sum_apply]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]; ring
    rw [hl2]
    exact Finset.sum_congr rfl fun i _ => (e5 i).symm
  rw [e]
  exact Rt.sum_mem fun i _ => Rt.mul_mem (Rt.mul_mem (hm₁ i) hQ) (hpair _ (hu i) l hl)

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem std_smul (R : Subalgebra o Ω) {Ix : Type} {a : Ω} (ha : a ∈ R) {x : Ix → Ω} (hx : x ∈ stdLat R Ix) :
    a • x ∈ stdLat R Ix := by
  rw [mem_stdLat_iff] at hx ⊢
  exact fun i => R.mul_mem ha (hx i)

theorem pow_smul_mem {V : Type} [AddCommGroup V] [Module Ω V] (R : Subalgebra o Ω) {L : AddSubgroup V}
    (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) {f : Ω} (hf : f ∈ R) (k : ℕ) {v : V} (hv : v ∈ L) : f ^ k • v ∈ L :=
  hL _ (R.pow_mem hf k) _ hv

theorem graph_step {r n : ℕ} (R : Subalgebra o Ω) {w f : Ω} (hf : f ∈ R) (A A' : AddSubgroup (Fin r → Ω))
    (B B' : AddSubgroup (Fin n → Ω)) (hA' : ∀ a ∈ R, ∀ v ∈ A', a • v ∈ A') (hB' : ∀ a ∈ R, ∀ v ∈ B', a • v ∈ B')
    (hA : ∀ v ∈ A, ∃ m : ℕ, f ^ m • v ∈ A') (hB : ∀ v ∈ B, ∃ m : ℕ, f ^ m • v ∈ B')
    (qs qt : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω))
    (key : ∀ a, w • a ∈ A → ∃ m : ℕ, f ^ m • (qs a - qt a) ∈ B')
    (a : Fin r → Ω) (b : Fin n → Ω) (h1 : w • a ∈ A) (h2 : b - qs a ∈ B) :
    ∃ m : ℕ, w • f ^ m • a ∈ A' ∧ f ^ m • b - qt (f ^ m • a) ∈ B' := by
  obtain ⟨m₁, e₁⟩ := hA _ h1
  obtain ⟨m₂, e₂⟩ := hB _ h2
  obtain ⟨m₃, e₃⟩ := key a h1
  refine ⟨m₁ + m₂ + m₃, ?_, ?_⟩
  · have := pow_smul_mem R hA' hf (m₂ + m₃) e₁
    convert this using 1
    simp only [smul_smul]
    congr 1
    rw [pow_add, pow_add, pow_add]; ring
  · have h3 := pow_smul_mem R hB' hf (m₁ + m₃) e₂
    have h4 := pow_smul_mem R hB' hf (m₁ + m₂) e₃
    have := B'.add_mem h3 h4
    convert this using 1
    simp only [map_smul, smul_sub, smul_smul, ← pow_add]
    rw [show m₁ + m₃ + m₂ = m₁ + m₂ + m₃ by ring]
    abel

theorem chart_pow {Kx : Type} (x : Kx → Ω) (s t : Kx) (hs : x s ≠ 0) (ht : x t ≠ 0) :
    ∀ a ∈ chartRing o x s, ∃ m : ℕ, (x s / x t) ^ m * a ∈ chartRing o x t := by
  intro a ha
  have hf : x s / x t ∈ chartRing o x t := Algebra.subset_adjoin ⟨s, rfl⟩
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    refine ⟨1, ?_⟩
    have : (x s / x t) ^ 1 * (x j / x s) = x j / x t := by
      field_simp
    rw [this]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    exact ⟨0, by simpa using (chartRing o x t).algebraMap_mem r⟩
  | add a b _ _ h1 h2 =>
    obtain ⟨m₁, e₁⟩ := h1
    obtain ⟨m₂, e₂⟩ := h2
    refine ⟨m₁ + m₂, ?_⟩
    have := (chartRing o x t).add_mem ((chartRing o x t).mul_mem ((chartRing o x t).pow_mem hf m₂) e₁)
      ((chartRing o x t).mul_mem ((chartRing o x t).pow_mem hf m₁) e₂)
    convert this using 1
    rw [pow_add]; ring
  | mul a b _ _ h1 h2 =>
    obtain ⟨m₁, e₁⟩ := h1
    obtain ⟨m₂, e₂⟩ := h2
    refine ⟨m₁ + m₂, ?_⟩
    have := (chartRing o x t).mul_mem e₁ e₂
    convert this using 1
    rw [pow_add]; ring

theorem chart_pow_std {Kx : Type} (x : Kx → Ω) (s t : Kx) (hs : x s ≠ 0) (ht : x t ≠ 0) {n : ℕ} :
    ∀ v ∈ stdLat (chartRing o x s) (Fin n), ∃ m : ℕ, (x s / x t) ^ m • v ∈ stdLat (chartRing o x t) (Fin n) := by
  intro v hv
  rw [mem_stdLat_iff] at hv
  obtain ⟨m, hm⟩ := exists_uniform (chartRing o x t) (f := x s / x t) (Algebra.subset_adjoin ⟨s, rfl⟩) v
    (fun i => chart_pow x s t hs ht _ (hv i))
  exact ⟨m, (mem_stdLat_iff _ _).2 hm⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam

theorem emb_injective {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] [CharZero Ω] (g : 𝓞 E →+* Ω) :
    Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hk : RingHom.ker g = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    have h1 : g (algebraMap ℤ (𝓞 E) n) = 0 := hn
    simp only [eq_intCast, map_intCast, Int.cast_eq_zero] at h1
    simpa using h1
  have : a ∈ RingHom.ker g := ha
  rw [hk] at this
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam

theorem seqfam_holds : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c') (i : ∀ (c' : ∀ k, J k) (τ), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ (c' : ∀ k, J k) (h : mseg y c' ≠ 0) (τ : Sg), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i c' τ) (qMap (P c' h) (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq (P c' h) σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i c' τ)) → ∀ τ : Sg, IsLatFamily O y (fun c' => (famD e b pq sc w P i c').Gam τ) ∧ IsLatFamily O y (fun c' => (famD e b pq sc w P i c').Del τ) := by
  intro hFH E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hvar hpq p _ hpS hfree hp2 hdisc b hb φ hφ
    A _ _ _ m _ hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σ hOrb hSec G P i hseq τ
  have hp : p.Prime := Fact.out
  have hR : 4 ≤ 𝔐.R p := 𝔐.R_ge p hpS
  obtain ⟨-, -, -, -, hemb, -, ⟨hp0, ⟨u0, hu0, hwu⟩, hpnu⟩, hCp⟩ := hOrb
  have hlat := fun t => GlobalTheory.T.arith_variety_model_prime_bound hFH E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar hpq p hpS hfree hp2 hdisc b hb A m hpm O w hCp t

  have hw0 : algebraMap O Ω w ≠ 0 := by
    have h := hCp
    simp only [HT.IsCp, if_neg hp2] at h
    obtain ⟨ζ, hζ, he⟩ := h
    rw [he]
    exact sub_ne_zero.2 (hζ.ne_one hp.one_lt)
  have hp3 : 2 ≤ p - 1 := by
    have := hp.two_le
    omega
  obtain ⟨tO, htp⟩ : ∃ tO : O, (p : O) = w * tO := by
    obtain ⟨uu, rfl⟩ := hu0
    refine ⟨(↑uu⁻¹ : O) * w ^ (p - 2), ?_⟩
    have h2 : w ^ (p - 1) = w * w ^ (p - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : (p : O) = (↑uu⁻¹ : O) * w ^ (p - 1) := by
      rw [hwu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [h3, h2]
    ring
  set wΩ : Ω := algebraMap O Ω w with hwΩ
  set tΩ : Ω := algebraMap O Ω tO with htΩ
  have hpΩ : (p : Ω) = wΩ * tΩ := by
    rw [hwΩ, htΩ, ← map_mul, ← htp, map_natCast]

  have hOinj : Function.Injective (algebraMap O Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl x
    have h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap O Ω (algebraMap A O s) =
        algebraMap O Ω (algebraMap A O a) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [hx, MulZeroClass.zero_mul, ← IsScalarTower.algebraMap_apply A O Ω] at h1
    have h2 : a = 0 := IsIntegralClosure.algebraMap_injective A ℤ Ω
      (by rw [← h1, map_zero])
    rw [h2, IsLocalization.mk'_zero]
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective

  have hinj := emb_injective (𝔐.emb (e τ))
  let σE : E →+* Ω := IsFractionRing.lift (A := 𝓞 E) hinj
  have hσ : ∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a := fun a => IsFractionRing.lift_algebraMap hinj a
  let Gm : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Ω := Matrix.of fun i j =>
    ∑ k, σE (HT.dualInt E k) * ((G.e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)
  have hgram : ∀ (c' : ∀ k, J k) (Pc : ChartPack G O c') (l j), Pc.Dh.gram σE 1 l j = Gm l j := by
    intro c' Pc l j
    simp only [HT.HTChart.gram, map_one, _root_.one_mul, Pc.Dh_e]
    rfl
  have hGC : ∀ (c' : ∀ k, J k) (Pc : ChartPack G O c'), ∃ C : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Ω,
      (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ Gm * C = 1 := by
    intro c' Pc
    refine GlobalTheory.T.hermitian_pairing_torsion_free E (HT.cmConj E) p (𝔐.R p) (D.p + D.q) (by omega) hdisc G.e
      (fun a x y' => by rw [← Pc.Dh_e]; exact Pc.Dh.adj a x y')
      (fun x hx => Pc.Dh.e_inj x (by rw [Pc.Dh_e]; exact hx)) O Ω hOinj hpnu σE ?_
    intro a
    obtain ⟨o', ho, -⟩ := hemb τ a
    exact ⟨o', by rw [ho, hσ]⟩

  set Q : Ω := tΩ * tΩ * (p : Ω) ^ (𝔐.R p - 2) with hQ
  set Pw : Ω := tΩ * (p : Ω) ^ (𝔐.R p - 3) with hPw
  have gen2 : ∀ (x a c : Ω) (k : ℕ), x = a * c → x ^ (k + 2) = a * a * (c * c * x ^ k) := by
    intro x a c k h
    calc x ^ (k + 2) = x ^ k * (x * x) := by ring
      _ = x ^ k * ((a * c) * (a * c)) := by rw [← h]
      _ = _ := by ring
  have gen1 : ∀ (x a c : Ω) (k : ℕ), x = a * c → x ^ (k + 1) = a * (c * x ^ k) := by
    intro x a c k h
    calc x ^ (k + 1) = x ^ k * x := by ring
      _ = x ^ k * (a * c) := by rw [← h]
      _ = _ := by ring
  have hpR : (p : Ω) ^ 𝔐.R p = wΩ * wΩ * Q := by
    have := gen2 _ _ _ (𝔐.R p - 2) hpΩ
    rwa [show 𝔐.R p - 2 + 2 = 𝔐.R p by omega] at this
  have hpM : (p : Ω) ^ (𝔐.R p - 2) = wΩ * Pw := by
    have := gen1 _ _ _ (𝔐.R p - 3) hpΩ
    rwa [show 𝔐.R p - 3 + 1 = 𝔐.R p - 2 by omega] at this
  have hQO : ∀ c' : ∀ k, J k, Q ∈ CR O y c' := fun c' =>
    (CR O y c').mul_mem ((CR O y c').mul_mem ((CR O y c').algebraMap_mem tO) ((CR O y c').algebraMap_mem tO))
      ((CR O y c').pow_mem (natCast_mem _ p) _)
  have hPO : ∀ c' : ∀ k, J k, Pw ∈ CR O y c' := fun c' =>
    (CR O y c').mul_mem ((CR O y c').algebraMap_mem tO) ((CR O y c').pow_mem (natCast_mem _ p) _)

  have hpair : ∀ (c' : ∀ k, J k) (hc : mseg y c' ≠ 0) (Pc : ChartPack G O c') (u : Module.Dual Ω 𝔐.Li)
      (_ : u ∈ (Pc.Dh.om : Set (Module.Dual Ω 𝔐.Li))) (t' : CMType H ⊕ CMType H) (a : Fin (labelRk D t') → Ω)
      (_ : a ∈ coordLat O y (𝔐.HT p t') (b t') c'), wΩ * u (∑ k, a k • b t' k) ∈ CR O y c' := by
    intro c' hc Pc u hu t' a ha
    have h1 : wΩ • a ∈ coordLat O y (𝔐.dR t') (b t') c' := ((hlat t').2.2.2.2 c' hc).2.2.2.2.2.1 ha
    have e1 : ∑ k, (wΩ • a) k • b t' k = wΩ • ∑ k, a k • b t' k := by
      simp only [Pi.smul_apply, Finset.smul_sum, smul_assoc]
    have h2 := GlobalTheory.T.arith_variety_prime_hodge_final E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar hpq p hpS A m hpm O G c' hc Pc u hu
      (∑ k, (wΩ • a) k • b t' k) (fun q hq ho => by
        simp only [coordLat, AddSubgroup.mem_iInf] at h1
        have h4 : Fintype.linearCombination Ω (b t') (wΩ • a) ∈ 𝔐.dR t' q := h1 q hq ho
        have h5 := (Submodule.mem_inf.1 h4).1
        rwa [Fintype.linearCombination_apply] at h5)
    rwa [e1, map_smul, smul_eq_mul] at h2

  have hΔ : ∀ (s t : ∀ k, J k) (hs : mseg y s ≠ 0) (ht : mseg y t ≠ 0), ∃ n : ℕ, ∀ j : Fin (D.p + D.q),
      ∃ u ∈ ((P t ht).Dh.om : Set (Module.Dual Ω 𝔐.Li)), (mseg y s / mseg y t) ^ n •
        ((P s hs).Dh.h (Pi.single j 1) - (P t ht).Dh.h (Pi.single j 1)) = (wΩ * wΩ * Q) • u := by
    intro s t hs ht
    have h := fun j : Fin (D.p + D.q) => GlobalTheory.T.arith_variety_prime_hodge_bound E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar hpq p hpS A m hpm O G s t hs ht
      (P s hs) (P t ht) (Pi.single j 1)
    choose n₀ u hu hE using h
    have hf : mseg y s / mseg y t ∈ CR O y t := Algebra.subset_adjoin ⟨s, rfl⟩
    refine ⟨∑ j, n₀ j, fun j => ?_⟩
    have hle : n₀ j ≤ ∑ j, n₀ j :=
      Finset.single_le_sum (f := n₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨(mseg y s / mseg y t) ^ k • u j, ?_, ?_⟩
    · exact (P t ht).Dh.om.smul_mem (⟨_, (CR O y t).pow_mem hf k⟩ : CR O y t) (hu j)
    · rw [hk, add_comm, pow_add, mul_smul, hE j, ← Nat.cast_smul_eq_nsmul Ω, Nat.cast_pow, hpR, smul_comm]
  have hdual : ∀ (c' : ∀ k, J k) (hc : mseg y c' ≠ 0), ∀ a ∈ coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c',
      ∀ j, ∃ z ∈ CR O y c', ∑ l', i c' τ a l' * Gm l' j =
        (P c' hc).Dh.h (Pi.single j 1) (∑ k, a k • b (e τ) k) + wΩ * Pw * z := by
    intro c' hc a ha j
    obtain ⟨z, hz, heq⟩ := (hseq c' hc τ).2 σE hσ a ha j
    refine ⟨z, hz, ?_⟩
    simp only [hgram] at heq
    rw [heq, hpM]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro s hs a ha v hv
    change v ∈ (famD e b pq sc w P i s).Gam τ at hv
    change a • v ∈ (famD e b pq sc w P i s).Gam τ
    rw [famD_pos e b pq sc w P i s hs] at hv ⊢
    obtain ⟨h1, h2⟩ := hv
    refine ⟨?_, ?_⟩
    · change wΩ • a • v.1 ∈ coordLat O y (𝔐.HT p (e τ)) (b (e τ)) s
      rw [smul_comm]
      exact (hlat (e τ)).2.1.1 s hs a ha _ h1
    · change a • v.2 - i s τ (a • v.1) ∈ stdLat (CR O y s) (Fin (D.p + D.q))
      rw [map_smul, ← smul_sub]
      exact std_smul _ ha h2
  · intro s t hs ht v hv
    change v ∈ (famD e b pq sc w P i s).Gam τ at hv
    change ∃ n : ℕ, (mseg y s / mseg y t) ^ n • v ∈ (famD e b pq sc w P i t).Gam τ
    rw [famD_pos e b pq sc w P i s hs] at hv
    rw [famD_pos e b pq sc w P i t ht]
    obtain ⟨h1, h2⟩ := hv
    have hf : mseg y s / mseg y t ∈ CR O y t := Algebra.subset_adjoin ⟨s, rfl⟩
    obtain ⟨C, hC, hGCe⟩ := hGC t (P t ht)
    have key := gam_key (CR O y s) (CR O y t) hw0 hf (chart_pow (mseg y) s t hs ht) _ _
      ((hlat (e τ)).2.1.2 s t hs ht) (b (e τ)) Gm C hGCe
      (fun a c' => by obtain ⟨o', ho⟩ := hC a c'; rw [← ho]; exact (CR O y t).algebraMap_mem o')
      (i s τ) (i t τ) (fun j => (P s hs).Dh.h (Pi.single j 1)) (fun j => (P t ht).Dh.h (Pi.single j 1))
      ((P t ht).Dh.om : Set (Module.Dual Ω 𝔐.Li)) (hdual s hs) (hdual t ht) (hPO t) (hQO t) (hΔ s t hs ht)
      (fun u hu a ha => hpair t ht (P t ht) u hu (e τ) a ha)
    obtain ⟨n, e1, e2⟩ := graph_step (CR O y t) hf _ _ _ _ ((hlat (e τ)).2.1.1 t ht)
      (fun a ha v hv => std_smul _ ha hv) ((hlat (e τ)).2.1.2 s t hs ht)
      (chart_pow_std (mseg y) s t hs ht) (i s τ) (i t τ) key v.1 v.2 h1 h2
    exact ⟨n, e1, e2⟩
  · intro s hs a ha v hv
    change v ∈ (famD e b pq sc w P i s).Del τ at hv
    change a • v ∈ (famD e b pq sc w P i s).Del τ
    rw [famD_pos e b pq sc w P i s hs] at hv ⊢
    obtain ⟨h1, h2⟩ := hv
    refine ⟨?_, ?_⟩
    · change wΩ • a • v.1 ∈ stdLat (CR O y s) (Fin (D.p + D.q))
      rw [smul_comm]
      exact std_smul _ ha h1
    · change a • v.2 - qMap (P s hs) (b (e τ).swap) (a • v.1) ∈
        dotDual (CR O y s) (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) s)
      rw [map_smul, ← smul_sub]
      exact (hlat (e τ).swap).2.2.2.1.1 s hs a ha _ h2
  · intro s t hs ht v hv
    change v ∈ (famD e b pq sc w P i s).Del τ at hv
    change ∃ n : ℕ, (mseg y s / mseg y t) ^ n • v ∈ (famD e b pq sc w P i t).Del τ
    rw [famD_pos e b pq sc w P i s hs] at hv
    rw [famD_pos e b pq sc w P i t ht]
    obtain ⟨h1, h2⟩ := hv
    have hf : mseg y s / mseg y t ∈ CR O y t := Algebra.subset_adjoin ⟨s, rfl⟩
    have key := fun a ha => del_key (CR O y s) (CR O y t) (w := wΩ) hf (chart_pow (mseg y) s t hs ht)
      (b (e τ).swap) (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) t)
      (fun j => (P s hs).Dh.h (Pi.single j 1)) (fun j => (P t ht).Dh.h (Pi.single j 1))
      ((P t ht).Dh.om : Set (Module.Dual Ω 𝔐.Li)) (hQO t) (hΔ s t hs ht)
      (fun u hu a ha => hpair t ht (P t ht) u hu (e τ).swap a ha) a ha
    obtain ⟨n, e1, e2⟩ := graph_step (CR O y t) hf _ _ _ _ (fun a ha v hv => std_smul _ ha hv)
      ((hlat (e τ).swap).2.2.2.1.1 t ht) (chart_pow_std (mseg y) s t hs ht)
      ((hlat (e τ).swap).2.2.2.1.2 s t hs ht) (qMap (P s hs) (b (e τ).swap)) (qMap (P t ht) (b (e τ).swap))
      key v.1 v.2 h1 h2
    exact ⟨n, e1, e2⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqFam
