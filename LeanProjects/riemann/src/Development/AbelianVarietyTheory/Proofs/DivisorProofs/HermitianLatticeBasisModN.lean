import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEquationModN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentModRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftBasisModN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalOfFinite

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.OrthoFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem represent (N : ℕ) (hN : 0 < N) (T : 𝓞 E →+ ℤ)
    (hT : ∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T (c * d)) → ∃ b : 𝓞 E, c = N • b)
    (f : 𝓞 E →+ ℤ) : ∃ x : 𝓞 E, ∀ c : 𝓞 E, (N : ℤ) ∣ f c - T (c * x) :=
  GlobalTheory.exists_represent_mod_ringOfIntegers N hN T hT f

theorem freeModN (H : Host E) (D : Datum H) (N : ℕ) (hN : 0 < N) :
    ∃ e : Fin (D.p + D.q) → D.La, (∀ a : D.La, ∃ c : Fin (D.p + D.q) → 𝓞 E, D.ModN N (a - ∑ i, c i • e i)) ∧
      ∀ c : Fin (D.p + D.q) → 𝓞 E, D.ModN N (∑ i, c i • e i) → ∀ i, ∃ b : 𝓞 E, c i = N • b :=
  GlobalTheory.exists_lift_basis_modN H D N hN

theorem orthoFinite (R : Type) [CommRing R] [Finite R] (s : R →+* R) (hs : ∀ x, s (s x) = x)
    (hτ : ∃ τ : R, τ + s τ = 1) (hn : ∀ u : R, IsUnit u → s u = u → ∃ x : R, s x * x = u)
    (n : ℕ) (Q : Matrix (Fin n) (Fin n) R) (hQ : (Q.map s).transpose = Q) (hu : IsUnit Q) :
    ∃ a : GL (Fin n) R, (a.1.map s).transpose * Q * a.1 = 1 :=
  GlobalTheory.FiniteHermitian.exists_orthonormal_of_finite R s hs hτ hn n Q hQ hu

abbrev idealN (E : Type) [Field E] [NumberField E] (N : ℕ) : Ideal (𝓞 E) := Ideal.span {((N : ℕ) : 𝓞 E)}

theorem mk_eq_zero_iff (N : ℕ) (x : 𝓞 E) :
    Ideal.Quotient.mk (idealN E N) x = 0 ↔ ∃ b : 𝓞 E, x = N • b := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by rw [nsmul_eq_mul, mul_comm]⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, by rw [nsmul_eq_mul, mul_comm]⟩

section ModN
variable {H : Host E} {D : Datum H} {N : ℕ}

theorem modN_add {x y : D.La} (hx : D.ModN N x) (hy : D.ModN N y) : D.ModN N (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by rw [smul_add]⟩

theorem modN_smul_of (c : 𝓞 E) (x : D.La) (hc : ∃ b : 𝓞 E, c = N • b) : D.ModN N (c • x) := by
  obtain ⟨b, rfl⟩ := hc; exact ⟨b • x, by rw [smul_assoc]⟩

theorem modN_sum {ι : Type} (s : Finset ι) (f : ι → D.La) (h : ∀ i ∈ s, D.ModN N (f i)) :
    D.ModN N (∑ i ∈ s, f i) :=
  Finset.sum_induction f (D.ModN N) (fun _ _ => modN_add) ⟨0, by simp⟩ h

end ModN

theorem modN_of_dvd {H : Host E} (D : Datum H) (N : ℕ) (a : D.La)
    (h : ∀ b, (N : ℤ) ∣ D.EF a b) : D.ModN N a := by
  let φ : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun b => D.EF a b / N
      map_add' := fun x y => by simp only [map_add]; rw [Int.add_ediv_of_dvd_left (h x)]
      map_smul' := fun k x => by
        simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]; rw [Int.mul_ediv_assoc _ (h x)] }
  obtain ⟨a', ha'⟩ := D.unimod.2 φ
  refine ⟨a', D.unimod.1 ?_⟩
  ext b
  have hb : D.EF a' b = D.EF a b / N := by rw [ha']; rfl
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, hb, Int.mul_ediv_cancel' (h b)]

theorem calc_gram {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (a G : Matrix (Fin n) (Fin n) R) (k l : Fin n) :
    ∑ i, a i k * ∑ j, s (a j l) * G i j = (a.transpose * G * a.map s) k l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem calc_inv {R : Type} [CommRing R] {n : ℕ} (x : Fin n → R) (a b : Matrix (Fin n) (Fin n) R)
    (hab : a * b = 1) (i : Fin n) : x i - ∑ k, (∑ j, x j * b k j) * a i k = 0 := by
  have : ∑ k, (∑ j, x j * b k j) * a i k = ∑ j, x j * (a * b) i j := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this, hab]
  simp [Matrix.one_apply]

theorem calc_one {R : Type} [CommRing R] {n : ℕ} (x y : Fin n → R) :
    ∑ i, x i * ∑ j, y j * (1 : Matrix (Fin n) (Fin n) R) i j = ∑ i, x i * y i := by
  simp [Matrix.one_apply]

theorem frame (H : Host E) (D : Datum H) (N : ℕ) (hN : 0 < N) (T : 𝓞 E →+ ℤ)
    (hskew : ∀ c, T (H.bar c) = - T c)
    (hperf : ∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T (c * d)) → ∃ b : 𝓞 E, c = N • b) :
    ∃ e : Fin (D.p + D.q) → D.La, (∀ a : D.La, ∃ c : Fin (D.p + D.q) → 𝓞 E, D.ModN N (a - ∑ i, c i • e i)) ∧
      ∀ c d : Fin (D.p + D.q) → 𝓞 E,
        (N : ℤ) ∣ D.EF (∑ i, c i • e i) (∑ i, d i • e i) - ∑ i, T (c i * H.bar (d i)) := by
  classical
  set r := D.p + D.q
  set I := idealN E N
  set π := Ideal.Quotient.mk I
  have hπ : ∀ x, π x = 0 ↔ ∃ b : 𝓞 E, x = N • b := mk_eq_zero_iff N
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN.ne')
  have hIb : I ≤ I.comap (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show (H.bar : 𝓞 E →+* 𝓞 E) (N : 𝓞 E) ∈ I
    rw [map_natCast]; exact Ideal.mem_span_singleton_self _
  set s : (𝓞 E ⧸ I) →+* (𝓞 E ⧸ I) := Ideal.quotientMap I (H.bar : 𝓞 E →+* 𝓞 E) hIb
  have hs : ∀ x, s (π x) = π (H.bar x) := fun x => Ideal.quotientMap_mk
  have hss : ∀ y, s (s y) = y := by
    intro y; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hs, hs, GlobalTheory.HostModel.bar_bar]
  have perf : ∀ x : 𝓞 E, (∀ c, (N : ℤ) ∣ T (c * x)) → π x = 0 := by
    intro x hx; rw [hπ]; exact hperf x (fun d => by rw [mul_comm]; exact hx d)
  have hskEF : ∀ x y, D.EF x y = - D.EF y x := by
    intro x y; have := D.alt (x + y)
    simp only [map_add, LinearMap.add_apply, D.alt] at this; linarith
  have hrep := fun (a b : D.La) => represent N hN T hperf
      (AddMonoidHom.mk' (fun c : 𝓞 E => D.EF (c • a) b) (fun c c' => by simp [add_smul]))
  choose h hh using hrep
  have hh' : ∀ a b c, (N : ℤ) ∣ D.EF (c • a) b - T (c * h a b) := fun a b c => by
    have := hh a b c; rwa [AddMonoidHom.mk'_apply] at this
  have Hadd : ∀ a a' b, π (h (a + a') b) = π (h a b) + π (h a' b) := by
    intro a a' b
    rw [← map_add, ← sub_eq_zero, ← map_sub]
    apply perf
    intro c
    have e1 := hh' (a + a') b c; have e2 := hh' a b c; have e3 := hh' a' b c
    have : T (c * (h (a + a') b - (h a b + h a' b))) =
        -((D.EF (c • (a + a')) b - T (c * h (a + a') b)) - (D.EF (c • a) b - T (c * h a b)) -
          (D.EF (c • a') b - T (c * h a' b))) := by
      rw [smul_add, map_add, LinearMap.add_apply, mul_sub, mul_add, map_sub, map_add]; ring
    rw [this]; exact ((e1.sub e2).sub e3).neg_right
  have Hsmul : ∀ (x : 𝓞 E) a b, π (h (x • a) b) = π x * π (h a b) := by
    intro x a b
    rw [← map_mul, ← sub_eq_zero, ← map_sub]
    apply perf; intro c
    have e1 := hh' (x • a) b c; have e2 := hh' a b (c * x)
    have : T (c * (h (x • a) b - x * h a b)) =
        (D.EF (c • x • a) b - T (c * h (x • a) b)) * (-1) + (D.EF ((c * x) • a) b - T (c * x * h a b)) := by
      rw [smul_smul, mul_sub, map_sub, ← mul_assoc]; ring
    rw [this]; exact (dvd_mul_of_dvd_left e1 _).add e2
  have Hherm : ∀ a b, π (h b a) = s (π (h a b)) := by
    intro a b
    rw [hs, ← sub_eq_zero, ← map_sub]
    apply perf; intro c
    have e1 := hh' b a c; have e2 := hh' a b (H.bar c)
    have hEF : D.EF (c • b) a = - D.EF (H.bar c • a) b := by
      rw [hskEF (c • b) a, D.adj (H.bar c) a b, GlobalTheory.HostModel.bar_bar]
    have hT : T (c * H.bar (h a b)) = - T (H.bar c * h a b) := by
      rw [← hskew (H.bar c * h a b)]; congr 1; rw [map_mul, GlobalTheory.HostModel.bar_bar]
    have : T (c * (h b a - H.bar (h a b))) =
        (D.EF (c • b) a - T (c * h b a)) * (-1) + (-(D.EF (H.bar c • a) b - T (H.bar c * h a b))) := by
      rw [mul_sub, map_sub, hT, hEF]; ring
    rw [this]; exact (dvd_mul_of_dvd_left e1 _).add e2.neg_right
  have Hzero : ∀ a b, D.ModN N a → π (h a b) = 0 := by
    rintro a b ⟨a', rfl⟩
    apply perf; intro c
    have e1 := hh' (N • a') b c
    have : T (c * h (N • a') b) = (N : ℤ) * D.EF (c • a') b - (D.EF (c • N • a') b - T (c * h (N • a') b)) := by
      rw [smul_comm, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]; ring
    rw [this]; exact (dvd_mul_right _ _).sub e1
  have Hzero_right : ∀ a b, D.ModN N b → π (h a b) = 0 := by
    intro a b hb; rw [Hherm b a, Hzero b a hb, map_zero]
  have Hadd_right : ∀ a b b', π (h a (b + b')) = π (h a b) + π (h a b') := by
    intro a b b'
    rw [Hherm (b + b') a, Hadd, map_add, ← Hherm b a, ← Hherm b' a]
  have Hsum_left : ∀ (c : Fin r → 𝓞 E) (v : Fin r → D.La) b,
      π (h (∑ i, c i • v i) b) = ∑ i, π (c i) * π (h (v i) b) := by
    intro c v b
    let F : D.La →+ (𝓞 E ⧸ I) := AddMonoidHom.mk' (fun a => π (h a b)) (fun a a' => Hadd a a' b)
    have := map_sum F (fun i => c i • v i) Finset.univ
    simp only [F, AddMonoidHom.mk'_apply] at this
    rw [this]; exact Finset.sum_congr rfl fun i _ => Hsmul _ _ _
  have Hsum_right : ∀ (a : D.La) (d : Fin r → 𝓞 E) (v : Fin r → D.La),
      π (h a (∑ j, d j • v j)) = ∑ j, s (π (d j)) * π (h a (v j)) := by
    intro a d v
    rw [Hherm (∑ j, d j • v j) a, Hsum_left, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Hherm a (v j), hss]
  obtain ⟨e₀, hspan, hind⟩ := freeModN H D N hN
  set G : Matrix (Fin r) (Fin r) (𝓞 E ⧸ I) := Matrix.of fun i j => π (h (e₀ i) (e₀ j)) with hG
  have hGu : IsUnit G := by
    have key : ∀ x : Fin r → (𝓞 E ⧸ I), Matrix.vecMul x G = 0 → x = 0 := by
      intro x hx
      choose xl hxl using fun i => Ideal.Quotient.mk_surjective (I := I) (x i)
      have h1 : ∀ j, π (h (∑ i, xl i • e₀ i) (e₀ j)) = 0 := by
        intro j
        rw [Hsum_left]
        have := congrFun hx j
        simp only [Matrix.vecMul, dotProduct, G, Matrix.of_apply, Pi.zero_apply] at this
        rw [← this]; simp only [π, hxl]
      have h2 : ∀ b, π (h (∑ i, xl i • e₀ i) b) = 0 := by
        intro b
        obtain ⟨c, hc⟩ := hspan b
        have : π (h (∑ i, xl i • e₀ i) b) = π (h (∑ i, xl i • e₀ i) (∑ j, c j • e₀ j)) +
            π (h (∑ i, xl i • e₀ i) (b - ∑ j, c j • e₀ j)) := by
          rw [← Hadd_right, add_sub_cancel]
        rw [this, Hsum_right, Hzero_right _ _ hc]
        simp [h1]
      have h3 : D.ModN N (∑ i, xl i • e₀ i) := modN_of_dvd D N _ (fun b => by
        obtain ⟨z, hz⟩ := (hπ _).1 (h2 b)
        have := hh' (∑ i, xl i • e₀ i) b 1
        rw [one_smul, one_mul, hz, map_nsmul, nsmul_eq_mul] at this
        have := this.add (dvd_mul_right (N : ℤ) (T z))
        simpa using this)
      funext i
      obtain ⟨b, hb⟩ := hind xl h3 i
      rw [← hxl i, hb, Pi.zero_apply, hπ]; exact ⟨b, rfl⟩
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    apply Finite.surjective_of_injective
    intro x y hxy
    have hxy' : Matrix.vecMul x G = Matrix.vecMul y G := hxy
    have := key (x - y) (by rw [Matrix.sub_vecMul, hxy', sub_self])
    exact sub_eq_zero.mp this
  have hτ : ∃ τ, τ + s τ = 1 := ⟨π H.w0, by
    rw [hs, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, ← map_add, add_sub_cancel, map_one]⟩
  have hnorm : ∀ u, IsUnit u → s u = u → ∃ x, s x * x = u := by
    intro u hu hsu
    obtain ⟨ul, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) u
    obtain ⟨w, hw⟩ := hu
    obtain ⟨vl, hvl⟩ := Ideal.Quotient.mk_surjective (I := I) (↑w⁻¹ : 𝓞 E ⧸ I)
    have h1 : ∃ b : 𝓞 E, H.bar ul - ul = N • b := by
      rw [← hπ, map_sub, ← hs]; exact sub_eq_zero.mpr hsu
    have h2 : ∃ v b : 𝓞 E, ul * v - 1 = N • b := ⟨vl, by
      rw [← hπ, map_sub, map_mul, hvl, map_one, ← hw, Units.mul_inv, sub_self]⟩
    obtain ⟨x, b, hx⟩ := GlobalTheory.NormSurjMod.exists_mul_bar_sub_eq_nsmul H N hN ul h1 h2
    refine ⟨π x, ?_⟩
    rw [hs, ← map_mul, ← sub_eq_zero, ← map_sub, mul_comm, hπ]; exact ⟨b, hx⟩
  have hGh : Matrix.transpose (G.transpose.map s) = G.transpose := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, G, Matrix.of_apply]
    exact (Hherm (e₀ i) (e₀ j)).symm
  obtain ⟨a, ha⟩ := orthoFinite (𝓞 E ⧸ I) s hss hτ hnorm r G.transpose hGh ((Matrix.isUnit_transpose _).2 hGu)
  have ha' : a.1.transpose * G * (a.1.map s) = 1 := by
    have := congrArg Matrix.transpose ha
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      Matrix.transpose_one, ← Matrix.mul_assoc] at this
  choose A hA using fun i k => Ideal.Quotient.mk_surjective (I := I) (a.1 i k)
  choose B hB using fun k j => Ideal.Quotient.mk_surjective (I := I) ((a⁻¹ : GL (Fin r) (𝓞 E ⧸ I)).1 k j)
  replace hA : ∀ i k, π (A i k) = a.1 i k := hA
  replace hB : ∀ k j, π (B k j) = (a⁻¹ : GL (Fin r) (𝓞 E ⧸ I)).1 k j := hB
  obtain ⟨e, he⟩ : ∃ e : Fin r → D.La, ∀ k, e k = ∑ i, A i k • e₀ i := ⟨_, fun _ => rfl⟩
  have hON : ∀ k l, π (h (e k) (e l)) = (1 : Matrix (Fin r) (Fin r) (𝓞 E ⧸ I)) k l := by
    intro k l
    rw [← ha', he, he, Hsum_left]
    simp only [Hsum_right, hA]
    exact calc_gram s a.1 G k l
  refine ⟨e, ?_, ?_⟩
  · intro b
    obtain ⟨c0, hc0⟩ := hspan b
    refine ⟨fun k => ∑ j, c0 j * B k j, ?_⟩
    have hre : ∑ k, (∑ j, c0 j * B k j) • e k = ∑ i, (∑ k, (∑ j, c0 j * B k j) * A i k) • e₀ i := by
      simp only [he, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    have : b - ∑ k, (∑ j, c0 j * B k j) • e k = (b - ∑ j, c0 j • e₀ j) +
        ∑ i, (c0 i - ∑ k, (∑ j, c0 j * B k j) * A i k) • e₀ i := by
      rw [hre, ← sub_add_sub_cancel b (∑ j, c0 j • e₀ j), ← Finset.sum_sub_distrib]
      simp only [sub_smul]
    rw [this]
    refine modN_add hc0 (modN_sum _ _ fun i _ => modN_smul_of _ _ ?_)
    rw [← hπ]
    simp only [map_sub, map_sum, map_mul, hA, hB]
    exact calc_inv (fun j => π (c0 j)) a.1 (a⁻¹ : GL (Fin r) (𝓞 E ⧸ I)).1 (Units.mul_inv a) i
  · intro c d
    have h1 := hh' (∑ i, c i • e i) (∑ i, d i • e i) 1
    rw [one_smul, one_mul] at h1
    have h2 : π (h (∑ i, c i • e i) (∑ i, d i • e i)) = π (∑ i, c i * H.bar (d i)) := by
      rw [Hsum_left, map_sum]
      simp only [Hsum_right, hON]
      rw [calc_one]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hs]
    obtain ⟨z, hz⟩ := (hπ (h (∑ i, c i • e i) (∑ i, d i • e i) - ∑ i, c i * H.bar (d i))).1 (by rw [map_sub, h2, sub_self])
    have hT' : T (h (∑ i, c i • e i) (∑ i, d i • e i)) = T (N • z) + T (∑ i, c i * H.bar (d i)) := by
      rw [← map_add, ← hz, sub_add_cancel]
    rw [map_sum, map_nsmul, nsmul_eq_mul] at hT'
    rw [hT'] at h1
    have e3 : D.EF (∑ i, c i • e i) (∑ i, d i • e i) - ∑ i, T (c i * H.bar (d i)) =
        D.EF (∑ i, c i • e i) (∑ i, d i • e i) - ((N : ℤ) * T z + ∑ i, T (c i * H.bar (d i))) + (N : ℤ) * T z := by
      ring
    rw [e3]; exact h1.add (dvd_mul_right _ _)

end GlobalTheory.OrthoFrame
