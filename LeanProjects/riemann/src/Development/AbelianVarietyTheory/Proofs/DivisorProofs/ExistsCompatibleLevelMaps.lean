import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleSystemOfLatticeMapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormDivisibilityCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBasisModNStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEquationModNStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimultaneousUnitsModNStatement

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TwistIsom

theorem sum_twist_coord {ι κ R M : Type} [Fintype ι] [Fintype κ] [CommRing R] [AddCommGroup M] [Module R M]
    (σ : R ≃+* R) (x : R) (α : κ → ℤ) (ck : κ → ι → R) (e : ι → M) :
    ∑ k, α k • ∑ i, (x * σ (ck k i)) • e i = ∑ i, (x * σ (∑ k, (α k : R) * ck k i)) • e i := by
  simp only [map_sum, map_mul, map_intCast, Finset.mul_sum, Finset.sum_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← Int.cast_smul_eq_zsmul R, smul_smul]
  congr 1; ring

theorem sum_coord_sub {ι κ R M : Type} [Fintype ι] [Fintype κ] [CommRing R] [AddCommGroup M] [Module R M]
    (α : κ → ℤ) (b : κ → M) (ck : κ → ι → R) (e : ι → M) :
    ∑ k, α k • b k - ∑ i, (∑ k, (α k : R) * ck k i) • e i = ∑ k, (α k : R) • (b k - ∑ i, ck k i • e i) := by
  simp only [smul_sub, Finset.smul_sum, smul_smul, Finset.sum_sub_distrib, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun i k => ((α k : R) * ck k i) • e i)]
  simp only [Int.cast_smul_eq_zsmul]

end GlobalTheory.TwistIsom

namespace GlobalTheory.TwistIsom

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_comm (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

section ModN

variable {H : Host E} (D : Datum H)

def multSub (n : ℕ) : Submodule (𝓞 E) D.La := LinearMap.range (n • LinearMap.id : D.La →ₗ[𝓞 E] D.La)

theorem modN_iff {n : ℕ} {x : D.La} : D.ModN n x ↔ x ∈ multSub D n := by
  simp only [Datum.ModN, multSub, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]
  exact ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩

theorem EF_left {n : ℕ} {x : D.La} (hx : D.ModN n x) (y : D.La) : (n : ℤ) ∣ D.EF x y := by
  obtain ⟨b, rfl⟩ := hx
  exact ⟨D.EF b y, by rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]⟩

theorem EF_right (x : D.La) {n : ℕ} {y : D.La} (hy : D.ModN n y) : (n : ℤ) ∣ D.EF x y := by
  obtain ⟨b, rfl⟩ := hy
  exact ⟨D.EF x b, by rw [map_nsmul, nsmul_eq_mul]⟩

theorem EF_congr {n : ℕ} {x x' y y' : D.La} (hx : D.ModN n (x' - x)) (hy : D.ModN n (y' - y)) :
    (n : ℤ) ∣ D.EF x' y' - D.EF x y := by
  have : D.EF x' y' - D.EF x y = D.EF (x' - x) y' + D.EF x (y' - y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [this]; exact dvd_add (EF_left D hx _) (EF_right D _ hy)

end ModN

theorem exists_modN (H : Host E) (D : Datum H) (σ : 𝓞 E ≃+* 𝓞 E) (N : ℕ) (hN : 0 < N) :
    ∃ g : D.La →+ D.La,
      (∀ (c : 𝓞 E) (a : D.La), D.ModN N (g (c • a) - σ c • g a)) ∧
      (∀ a : D.La, ∃ b : D.La, D.ModN N (g b - a)) ∧
      (∀ a b : D.La, (N : ℤ) ∣ D.EF (g a) (g b) - D.EF a b) := by
  obtain ⟨T, hTs, hTp⟩ := GlobalTheory.T.trace_form_divisibility_criterion H N hN
  obtain ⟨e, hsp, hEF⟩ := GlobalTheory.T.hermitian_lattice_basis_mod_n H D N hN T hTs hTp
  let T₂ : 𝓞 E →+ ℤ := T.comp σ.symm.toRingHom.toAddMonoidHom
  have hT₂ : ∀ c, T₂ c = T (σ.symm c) := fun c => rfl
  have hT₂s : ∀ c, T₂ (H.bar c) = - T₂ c := by
    intro c; rw [hT₂, hT₂, bar_comm H σ.symm, hTs]
  have hT₂p : ∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T₂ (c * d)) → ∃ b : 𝓞 E, c = N • b := by
    intro c hc
    obtain ⟨b, hb⟩ := hTp (σ.symm c) (fun d => by simpa [hT₂] using hc (σ d))
    exact ⟨σ b, by rw [← map_nsmul, ← hb, RingEquiv.apply_symm_apply]⟩
  obtain ⟨μ, ν, ⟨b₁, hμν⟩, hμbar, hμT⟩ := GlobalTheory.T.simultaneous_units_mod_n H N hN T T₂ hTs hT₂s hTp hT₂p
  obtain ⟨x, b₂, hx⟩ := GlobalTheory.T.norm_equation_mod_n H N hN μ hμbar ⟨ν, b₁, hμν⟩

  have hxT : ∀ z : 𝓞 E, (N : ℤ) ∣ T (x * H.bar x * z) - T₂ z := by
    intro z
    have h1 : x * H.bar x * z = μ * z + N • (b₂ * z) := by
      rw [nsmul_eq_mul] at hx ⊢; linear_combination z * hx
    rw [h1, map_add, map_nsmul, nsmul_eq_mul]
    have := hμT z
    have h2 : T (μ * z) + (N : ℤ) * T (b₂ * z) - T₂ z = (T (μ * z) - T₂ z) + (N : ℤ) * T (b₂ * z) := by ring
    rw [h2]; exact dvd_add this (dvd_mul_right _ _)
  set y := H.bar x * ν with hy
  have hxy : ∃ b : 𝓞 E, x * y - 1 = N • b := ⟨b₂ * ν + b₁, by
    rw [nsmul_eq_mul] at hx hμν ⊢; rw [hy]; linear_combination ν * hx + hμν⟩

  have huq : ∀ δ : Fin (D.p + D.q) → 𝓞 E, D.ModN N (∑ i, δ i • e i) → ∀ i, ∃ b : 𝓞 E, δ i = N • b := by
    intro δ hδ i
    apply hTp
    intro d
    set s : Fin (D.p + D.q) → 𝓞 E := Pi.single i (H.bar.symm d) with hs
    have h1 := hEF δ s
    have h2 : ∑ j, T (δ j * H.bar (s j)) = T (δ i * d) := by
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [hs, Pi.single_eq_of_ne hj, map_zero, mul_zero, map_zero])
        (fun h => absurd (Finset.mem_univ i) h), hs, Pi.single_eq_same, RingEquiv.apply_symm_apply]
    rw [h2] at h1
    have h3 := EF_left D hδ (∑ j, s j • e j)
    have : T (δ i * d) = D.EF (∑ j, δ j • e j) (∑ j, s j • e j) -
      (D.EF (∑ j, δ j • e j) (∑ j, s j • e j) - T (δ i * d)) := by ring
    rw [this]; exact dvd_sub h3 h1

  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let bs := Module.Free.chooseBasis ℤ D.La
  choose ck hck using fun k => hsp (bs k)
  let v : Module.Free.ChooseBasisIndex ℤ D.La → D.La := fun k => ∑ i, (x * σ (ck k i)) • e i
  let g : D.La →+ D.La := (bs.constr ℤ v).toAddMonoidHom
  have hg : ∀ a, g a = ∑ k, bs.equivFun a k • v k := fun a => bs.constr_apply_fintype ℤ v a
  have key : ∀ (a : D.La) (c : Fin (D.p + D.q) → 𝓞 E), D.ModN N (a - ∑ i, c i • e i) →
      D.ModN N (g a - ∑ i, (x * σ (c i)) • e i) := by
    intro a c hc
    let α := bs.equivFun a
    let c' : Fin (D.p + D.q) → 𝓞 E := fun i => ∑ k, (α k : 𝓞 E) * ck k i
    have ha : a = ∑ k, α k • bs k := (bs.sum_equivFun a).symm
    have h1 : a - ∑ i, c' i • e i = ∑ k, (α k : 𝓞 E) • (bs k - ∑ i, ck k i • e i) := by
      conv_lhs => rw [ha]
      exact sum_coord_sub α bs ck e
    have hc' : D.ModN N (a - ∑ i, c' i • e i) := by
      rw [h1, modN_iff]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ((modN_iff D).1 (hck k))
    have hδ : D.ModN N (∑ i, (c' i - c i) • e i) := by
      have : ∑ i, (c' i - c i) • e i = (a - ∑ i, c i • e i) - (a - ∑ i, c' i • e i) := by
        simp only [sub_smul, Finset.sum_sub_distrib]; abel
      rw [this, modN_iff]
      exact Submodule.sub_mem _ ((modN_iff D).1 hc) ((modN_iff D).1 hc')
    choose β hβ using huq _ hδ
    have h2 : g a = ∑ i, (x * σ (c' i)) • e i := by
      rw [hg]
      exact sum_twist_coord σ x α ck e
    have h3 : g a - ∑ i, (x * σ (c i)) • e i = ∑ i, N • ((x * σ (β i)) • e i) := by
      rw [h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hci : c' i = c i + N • β i := by rw [← hβ i]; abel
      rw [hci, map_add, map_nsmul, ← sub_smul, mul_add, add_sub_cancel_left, mul_smul_comm, smul_assoc]
    rw [h3, modN_iff]
    exact Submodule.sum_mem _ fun i _ => (modN_iff D).1 ⟨_, rfl⟩
  obtain ⟨bxy, hbxy⟩ := hxy
  refine ⟨g, ?_, ?_, ?_⟩
  · intro c a
    obtain ⟨ca, hca⟩ := hsp a
    have h1 := key a ca hca
    have h2 := key (c • a) (fun i => c * ca i) (by
      have : c • a - ∑ i, (c * ca i) • e i = c • (a - ∑ i, ca i • e i) := by
        rw [smul_sub, Finset.smul_sum]; simp only [smul_smul]
      rw [this, modN_iff]; exact Submodule.smul_mem _ _ ((modN_iff D).1 hca))
    have h3 : ∑ i, (x * σ (c * ca i)) • e i = σ c • ∑ i, (x * σ (ca i)) • e i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, map_mul]; congr 1; ring
    have : g (c • a) - σ c • g a = (g (c • a) - ∑ i, (x * σ (c * ca i)) • e i) -
        σ c • (g a - ∑ i, (x * σ (ca i)) • e i) := by rw [smul_sub, h3]; abel
    rw [this, modN_iff]
    exact Submodule.sub_mem _ ((modN_iff D).1 h2) (Submodule.smul_mem _ _ ((modN_iff D).1 h1))
  · intro a
    obtain ⟨ca, hca⟩ := hsp a
    refine ⟨∑ i, (σ.symm (y * ca i)) • e i, ?_⟩
    have h1 := key (∑ i, (σ.symm (y * ca i)) • e i) (fun i => σ.symm (y * ca i)) ⟨0, by simp⟩
    have h4 : ∀ i, (x * σ (σ.symm (y * ca i))) • e i = ca i • e i + N • ((bxy * ca i) • e i) := by
      intro i
      have hxy' : x * y = 1 + N • bxy := by rw [← hbxy]; abel
      rw [RingEquiv.apply_symm_apply, ← mul_assoc, hxy', add_mul, one_mul, add_smul, smul_mul_assoc, smul_assoc]
    have : g (∑ i, (σ.symm (y * ca i)) • e i) - a =
        (g (∑ i, (σ.symm (y * ca i)) • e i) - ∑ i, (x * σ (σ.symm (y * ca i))) • e i) +
          ∑ i, N • ((bxy * ca i) • e i) - (a - ∑ i, ca i • e i) := by
      rw [Finset.sum_congr rfl (fun i _ => h4 i), Finset.sum_add_distrib]; abel
    rw [this, modN_iff]
    exact Submodule.sub_mem _ (Submodule.add_mem _ ((modN_iff D).1 h1)
      (Submodule.sum_mem _ fun i _ => (modN_iff D).1 ⟨_, rfl⟩)) ((modN_iff D).1 hca)
  · intro a b
    obtain ⟨ca, hca⟩ := hsp a
    obtain ⟨cb, hcb⟩ := hsp b
    have e1 := EF_congr D (key a ca hca) (key b cb hcb)
    have e2 := hEF (fun i => x * σ (ca i)) (fun i => x * σ (cb i))
    beta_reduce at e2
    have e3 : (N : ℤ) ∣ ∑ i, T (x * σ (ca i) * H.bar (x * σ (cb i))) - ∑ i, T (ca i * H.bar (cb i)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun i _ => ?_
      have : x * σ (ca i) * H.bar (x * σ (cb i)) = x * H.bar x * σ (ca i * H.bar (cb i)) := by
        simp only [map_mul, ← bar_comm H σ]; ring
      rw [this]
      have h := hxT (σ (ca i * H.bar (cb i)))
      rwa [hT₂, RingEquiv.symm_apply_apply] at h
    have e4 := hEF ca cb
    have e5 := EF_congr D hca hcb
    have := dvd_sub (dvd_sub (dvd_add (dvd_add e1 e2) e3) e4) e5
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by linear_combination hk⟩

end GlobalTheory.TwistIsom

namespace GlobalTheory.TwistIsom

theorem exists_semilinear_isometry : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (σ : 𝓞 E ≃+* 𝓞 E), σ H.w0 = H.w0 →
  ∃ f : ℕ → D.La →+ D.La,
    (∀ n : ℕ, 0 < n → ∀ (c : 𝓞 E) (a : D.La), D.ModN n (f n (c • a) - σ c • f n a)) ∧
    (∀ n m : ℕ, 0 < n → 0 < m → ∀ a : D.La, D.ModN n (f (n * m) a - f n a)) ∧
    (∀ n : ℕ, 0 < n → ∀ a : D.La, ∃ b : D.La, D.ModN n (f n b - a)) ∧
    (∀ n : ℕ, 0 < n → ∀ a : D.La, D.ModN n (f n a) → D.ModN n a) ∧
    (∀ n : ℕ, 0 < n → ∀ a b : D.La, (n : ℤ) ∣ D.EF (f n a) (f n b) - D.EF a b) := by
  intro E _ _ _ H D σ _
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let P : ℕ → (D.La →+ D.La) → Prop := fun n g =>
    (∀ (c : 𝓞 E) (a : D.La), D.ModN n (g (c • a) - σ c • g a)) ∧
    (∀ a : D.La, ∃ b : D.La, D.ModN n (g b - a)) ∧
    (∀ a b : D.La, (n : ℤ) ∣ D.EF (g a) (g b) - D.EF a b)
  have hmod : ∀ (n : ℕ) (g g' : D.La →+ D.La), 0 < n → P n g → (∀ a, ∃ b, g' a - g a = n • b) → P n g' := by
    intro n g g' _ ⟨h1, h2, h3⟩ hgg
    refine ⟨fun c a => ?_, fun a => ?_, fun a b => ?_⟩
    · have : g' (c • a) - σ c • g' a = (g (c • a) - σ c • g a) + (g' (c • a) - g (c • a)) -
          σ c • (g' a - g a) := by rw [smul_sub]; abel
      rw [this, modN_iff]
      exact Submodule.sub_mem _ (Submodule.add_mem _ ((modN_iff D).1 (h1 c a)) ((modN_iff D).1 (hgg _)))
        (Submodule.smul_mem _ _ ((modN_iff D).1 (hgg a)))
    · obtain ⟨b, hb⟩ := h2 a
      refine ⟨b, ?_⟩
      have : g' b - a = (g b - a) + (g' b - g b) := by abel
      rw [this, modN_iff]
      exact Submodule.add_mem _ ((modN_iff D).1 hb) ((modN_iff D).1 (hgg b))
    · rw [← sub_add_sub_cancel _ (D.EF (g a) (g b))]
      exact dvd_add (EF_congr D (hgg a) (hgg b)) (h3 a b)
  have hdiv : ∀ (n m : ℕ) (g : D.La →+ D.La), 0 < n → 0 < m → P (n * m) g → P n g := by
    intro n m g _ _ ⟨h1, h2, h3⟩
    have hr : ∀ x : D.La, D.ModN (n * m) x → D.ModN n x := fun x ⟨b, hb⟩ => ⟨m • b, by rw [hb, mul_smul]⟩
    refine ⟨fun c a => hr _ (h1 c a), fun a => ?_, fun a b => ?_⟩
    · obtain ⟨b, hb⟩ := h2 a; exact ⟨b, hr _ hb⟩
    · exact dvd_trans ⟨(m : ℤ), by push_cast; ring⟩ (h3 a b)
  obtain ⟨f, hfP, hft⟩ := GlobalTheory.T.compatible_system_of_lattice_maps D.La P hmod hdiv (fun n hn => exists_modN H D σ n hn)
  refine ⟨f, fun n hn => (hfP n hn).1, hft, fun n hn => (hfP n hn).2.1, ?_, fun n hn => (hfP n hn).2.2⟩
  intro n hn a ha
  have hall : ∀ b, (n : ℤ) ∣ D.EF a b := by
    intro b
    have h := (hfP n hn).2.2 a b
    have h' := EF_left D ha (f n b)
    have : D.EF a b = D.EF (f n a) (f n b) - (D.EF (f n a) (f n b) - D.EF a b) := by ring
    rw [this]; exact dvd_sub h' h
  let bs := Module.Free.chooseBasis ℤ D.La
  let ψ : D.La →ₗ[ℤ] ℤ := bs.constr ℤ (fun k => D.EF a (bs k) / n)
  have hψ : n • ψ = D.EF a := by
    refine bs.ext fun k => ?_
    rw [LinearMap.smul_apply, Module.Basis.constr_basis, nsmul_eq_mul]
    exact Int.mul_ediv_cancel' (hall (bs k))
  obtain ⟨a', ha'⟩ := D.unimod.2 ψ
  have h0 : D.EF (a - n • a') = D.EF 0 := by
    rw [map_sub, map_nsmul, ha', hψ, sub_self, map_zero]
  exact ⟨a', sub_eq_zero.mp (D.unimod.1 h0)⟩

end GlobalTheory.TwistIsom
