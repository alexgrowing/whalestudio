import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeOfXRegularQuotientTorsionFreeScalarTower

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per PowerSeries

namespace GlobalTheory.BKReal.OfCrystal

theorem isDVR (l : ℕ) [hl : Fact l.Prime] (O K : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] :
    IsDiscreteValuationRing O := by
  have hN : IsNoetherianRing O := IsNoetherianRing.of_finite ℤ_[l] O
  have key : ∀ x y : O, ‖algebraMap O K y‖ ≤ ‖algebraMap O K x‖ → x ∣ y := fun x y h => by
    rcases eq_or_ne (algebraMap O K x) 0 with h0 | h0
    · rw [h0, norm_zero, norm_le_zero_iff, ← map_zero (algebraMap O K)] at h
      rw [IsUnitBall.inj h]
      exact dvd_zero _
    · obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) (algebraMap O K y / algebraMap O K x)).2
        (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _))
      exact ⟨c, IsUnitBall.inj (K := K) (by rw [map_mul, hc, mul_div_cancel₀ _ h0])⟩
  have hV : ValuationRing O := ValuationRing.iff_dvd_total.2 ⟨fun x y =>
    (le_total ‖algebraMap O K y‖ ‖algebraMap O K x‖).imp (key x y) (key y x)⟩
  have hl1 : ‖(l : K)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hF : ¬ IsField O := fun h => by
    have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
    obtain ⟨y, hy⟩ := h.mul_inv_cancel (a := (l : O)) fun h0 => by
      have := congrArg (algebraMap O K) h0
      rw [map_natCast, map_zero] at this
      exact Nat.cast_ne_zero.2 hl.out.ne_zero this
    have h1 := congrArg (fun z => ‖algebraMap O K z‖) hy
    simp only [map_mul, map_natCast, map_one, norm_mul, norm_one] at h1
    have h2 := norm_algebraMap_le (K := K) y
    nlinarith [norm_nonneg (l : K), norm_nonneg (algebraMap O K y)]
  exact ((IsDiscreteValuationRing.TFAE O hF).out 0 1).2 hV

theorem exists_dual_pair {A S W R V ι : Type} [CommRing A] [CommRing S] [CommRing W] [CommRing R]
    [AddCommGroup V] [Module R V] [Module W V] [Module A V] [Fintype ι] (ω : W →+* R) (g : A →+* R)
    (hW : ∀ (w : W) (v : V), w • v = ω w • v) (hA : ∀ (f : A) (v : V), f • v = g f • v) (ψ : S →+* W)
    (c : Module.Basis ι W V) (ε : R) (hε : ε * ε = ε) (N : AddSubgroup V)
    (hN : ∀ x, x ∈ N ↔ ∃ s : ι → S, x = ∑ i, ψ (s i) • c i) (hεN : ∀ x ∈ N, ε • x ∈ N)
    (hψ : ∀ s, ∃ f, ε * ω (ψ s) = ε * g f)
    (hgen : ∀ p : R → Prop, p 0 → (∀ w f, p (ω w * g f)) → (∀ r r', p r → p r' → p (r + r')) → ∀ r, p r)
    (hg : ∀ f, ∀ x ∈ N, g f • x ∈ N)
    (M : Submodule A V) (hM : ∀ x, x ∈ M ↔ x ∈ N ∧ ε • x = x) {m : ℕ} (β : Module.Basis (Fin m) A M) :
    ∃ (b : Fin m → V) (μ : Fin m → V →ₗ[R] R), (∀ k, b k ∈ N) ∧
      (∀ j k, μ j (b k) = if j = k then ε else 0) ∧ (∀ x, ∑ j, μ j x • b j = ε • x) ∧
      ∀ x ∈ N, ∀ j, ∃ f, μ j x = ε * g f := by
  classical
  letI : Algebra W R := ω.toAlgebra
  have hm : ∀ x ∈ N, ε • x ∈ M := fun x hx => (hM _).2 ⟨hεN x hx, by rw [smul_smul, hε]⟩
  have hc : ∀ i, c i ∈ N := fun i => (hN _).2 ⟨Pi.single i 1, by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]; simp⟩
  let ν : Fin m → V →ₗ[W] R := fun j => c.constr W fun i => ε * g (β.repr ⟨_, hm _ (hc i)⟩ j)
  have hν : ∀ j x (hx : x ∈ N), ν j x = ε * g (β.repr ⟨_, hm x hx⟩ j) := fun j x hx => by
    obtain ⟨s, hs⟩ := (hN x).1 hx
    choose f hf using fun i => hψ (s i)
    have h1 : (⟨_, hm x hx⟩ : M) = ∑ i, f i • (⟨_, hm _ (hc i)⟩ : M) := Subtype.ext (by
      rw [AddSubmonoidClass.coe_finsetSum]
      change ε • x = _
      rw [hs, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ = f i • ε • c i
      rw [hW, hA, smul_smul, smul_smul, hf, mul_comm])
    rw [h1, hs, map_sum, map_sum, Finset.sum_apply', map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ← mul_assoc, ← hf]
    simp only [ν, Module.Basis.constr_basis]
    change ω _ * _ = _
    ring
  have hνW : ∀ j w x, ν j (ω w • x) = ω w * ν j x := fun j w x => by rw [← hW, map_smul]; rfl
  have hνA : ∀ j f x, ν j (g f • x) = g f * ν j x := fun j f x => by
    rw [← c.sum_repr x, Finset.smul_sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, smul_comm, hνW, hνW, hν _ _ (hg f _ (hc i)), hν _ _ (hc i)]
    have h1 : (⟨_, hm _ (hg f _ (hc i))⟩ : M) = f • (⟨_, hm _ (hc i)⟩ : M) := Subtype.ext (by
      change ε • g f • c i = f • ε • c i
      rw [hA, smul_comm])
    rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
    ring
  let μ : Fin m → V →ₗ[R] R := fun j =>
    { toFun := ν j
      map_add' := map_add _
      map_smul' := fun r x => by
        refine hgen (fun r => ν j (r • x) = r * ν j x) (by simp) (fun w f => ?_) (fun r r' h h' => ?_) r
        · simp only [mul_smul, hνW, hνA, mul_assoc]
        · simp only [add_smul, map_add, add_mul, h, h'] }
  have hμ : ∀ j x, μ j x = ν j x := fun _ _ => rfl
  refine ⟨fun k => β k, μ, fun k => ((hM _).1 (β k).2).1, fun j k => ?_, fun x => ?_,
    fun x hx j => ⟨_, hν j x hx⟩⟩
  · rw [hμ, hν _ _ ((hM _).1 (β k).2).1]
    have h1 : (⟨_, hm _ ((hM _).1 (β k).2).1⟩ : M) = β k := Subtype.ext ((hM _).1 (β k).2).2
    rw [h1, β.repr_self, Finsupp.single_apply]
    by_cases h : j = k
    · simp [h]
    · simp [h, Ne.symm h]
  · have h0 : ∀ i, ∑ j, μ j (c i) • (β j : V) = ε • c i := fun i => by
      have h1 := congrArg (fun y : M => ε • (y : V)) (β.sum_repr ⟨_, hm _ (hc i)⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, Finset.smul_sum, smul_smul, hε] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hμ, hν _ _ (hc i), mul_smul, ← hA]
      rfl
    rw [← c.sum_repr x]
    simp only [hW, map_sum, map_smul, Finset.sum_smul, Finset.smul_sum, smul_eq_mul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.smul_sum, h0, smul_comm]

theorem exists_basis_of_dual_pairs {A R V I : Type} [CommRing R] [AddCommGroup V] [Module R V] [Fintype I]
    (g : A → R) (ε : I → R) (h1 : ∀ τ, ε τ * ε τ = ε τ) (h2 : ∀ τ σ, τ ≠ σ → ε τ * ε σ = 0)
    (h3 : ∑ τ, ε τ = 1) (hch : ∀ τ (m m' : ℕ), m • ε τ = m' • ε τ → m = m') {n : ℕ}
    (v : Module.Basis (Fin n) R V) (N : AddSubgroup V) (hεN : ∀ τ, ∀ x ∈ N, ε τ • x ∈ N)
    (h : ∀ τ, ∃ (m : ℕ) (b : Fin m → V) (μ : Fin m → V →ₗ[R] R), (∀ k, b k ∈ N) ∧
      (∀ j k, μ j (b k) = if j = k then ε τ else 0) ∧ (∀ x, ∑ j, μ j x • b j = ε τ • x) ∧
      ∀ x ∈ N, ∀ j, ∃ f, μ j x = ε τ * g f) :
    ∃ b : Module.Basis (Fin n) R V, (∀ k, b k ∈ N) ∧
      ∀ x ∈ N, ∀ j, ∃ f : I → A, b.repr x j = ∑ τ, ε τ * g (f τ) := by
  classical
  have h' : ∀ τ, ∃ (b : Fin n → V) (μ : Fin n → V →ₗ[R] R), (∀ k, b k ∈ N) ∧
      (∀ j k, μ j (b k) = if j = k then ε τ else 0) ∧ (∀ x, ∑ j, μ j x • b j = ε τ • x) ∧
      ∀ x ∈ N, ∀ j, ∃ f, μ j x = ε τ * g f := fun τ => by
    obtain ⟨m, b, μ, hb, hd, hs, hf⟩ := h τ
    obtain rfl : m = n := by
      refine hch τ _ _ ?_
      have e1 : ∑ j, μ j (b j) = m • ε τ := by simp [hd]
      have e2 : ∑ i, v.repr (∑ j, μ j (v i) • b j) i = n • ε τ := by simp [hs]
      rw [← e1, ← e2]
      simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← v.sum_repr (b j)]
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    exact ⟨b, μ, hb, hd, hs, hf⟩
  choose b μ hb hd hs hf using h'
  have key : ∀ {Y : Type} [AddCommGroup Y] [Module R Y] (y : I → Y) (τ : I),
      ε τ • ∑ σ, ε σ • y σ = ε τ • y τ := fun y τ => by
    rw [Finset.smul_sum, Finset.sum_eq_single τ (fun σ _ hσ => by
      rw [smul_smul, h2 _ _ hσ.symm, zero_smul]) (by simp), smul_smul, h1]
  let B : Fin n → V := fun k => ∑ τ, ε τ • b τ k
  let F : V →ₗ[R] (Fin n → R) := LinearMap.pi fun j => ∑ τ, ε τ • μ τ j
  have hF : ∀ x j, F x j = ∑ τ, ε τ • μ τ j x := fun x j => by simp [F]
  have hFB : ∀ k j, F (B k) j = if j = k then 1 else 0 := fun k j => by
    rw [hF]
    simp only [← map_smul, B, key]
    simp only [map_smul, hd, smul_eq_mul, mul_ite, h1, mul_zero]
    split_ifs
    · exact h3
    · simp
  have hBF : ∀ x, ∑ j, F x j • B j = x := fun x => by
    simp only [hF, Finset.sum_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [← one_smul R x, ← h3, Finset.sum_smul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [show ε τ • x = ε τ • ε τ • x by rw [smul_smul, h1], ← hs τ x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, mul_smul, key, smul_comm]
  let G : V ≃ₗ[R] (Fin n → R) := LinearEquiv.ofLinear F (Fintype.linearCombination R B)
    ((Pi.basisFun R (Fin n)).ext fun k => funext fun j => by
      simp [hFB, Pi.single_apply])
    (LinearMap.ext fun x => by simpa [Fintype.linearCombination_apply] using hBF x)
  refine ⟨Module.Basis.ofEquivFun G, fun k => ?_, fun x hx j => ?_⟩
  · have : Module.Basis.ofEquivFun G k = B k := by
      simp [G]
    rw [this]
    exact sum_mem fun τ _ => hεN τ _ (hb τ k)
  · choose f hf using fun τ => hf τ x hx j
    refine ⟨f, ?_⟩
    rw [Module.Basis.ofEquivFun_repr_apply]
    change F x j = _
    simp only [hF, hf, smul_eq_mul, ← mul_assoc, h1]

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O : Type} (K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)

def iR : (ZMod a → A O K) →ₐ[O] OW l O := (inclO l O).comp (ϖ.iTot t K)

omit [NeZero e] [NormedAlgebra ℚ_[l] K] in

theorem iR_toAc (s : (Wq l a)⟦X⟧) : iR K t ϖ (toAc t K s) = 1 ⊗ₜ inclW l (ϖ.ev a s) :=
  congrArg (inclO l O) (ϖ.iTot_toAc t K s)

omit [NeZero e] [NormedAlgebra ℚ_[l] K] in

theorem iR_E : iR K t ϖ (fun _ => EIn l e _) = 1 ⊗ₜ inclW l (ϖ.ev a (eis l a e)) :=
  congrArg (inclO l O) (ϖ.iTot_E t K)

theorem iR_injective : Function.Injective (iR K t ϖ) := inclO_injective.comp (ϖ.iTot_injective t K)

omit [NeZero e] [NormedAlgebra ℚ_[l] K] in

theorem iR_apply (f : ZMod a → A O K) :
    iR K t ϖ f = ∑ τ, idem (constW t) τ * inclO l O (ϖ.iA O K (f τ)) := by
  change inclO l O (∑ τ, _) = _
  simp only [map_sum, map_mul, inclO_idem]

theorem exists_iW_eq {k : ℕ} {r : OW l O} {f : ZMod a → A O K}
    (h : iR K t ϖ (fun _ => EIn l e _) ^ k * r = iR K t ϖ f) : ∃ y, ϖ.iW t K y = r := by
  let u := Eunit O K l e
  have h1 : ϖ.iW t K (fun _ => (u : invE l e (A O K))) = iR K t ϖ (fun _ => EIn l e _) :=
    ϖ.iW_of_mem t K fun _ => EIn l e _
  have h2 : ϖ.iW t K (fun _ => ((u⁻¹ : (invE l e (A O K))ˣ) : invE l e (A O K))) *
      iR K t ϖ (fun _ => EIn l e _) = 1 := by
    rw [← h1, ← map_mul, ← map_one (ϖ.iW t K)]
    exact congrArg _ (funext fun _ => u.inv_mul)
  refine ⟨(fun _ => ((u⁻¹ : (invE l e (A O K))ˣ) : invE l e (A O K))) ^ k *
    fun τ => ⟨f τ, le_away _ _ (f τ).2⟩, ?_⟩
  rw [map_mul, map_pow, ϖ.iW_of_mem t K f]
  change _ * iR K t ϖ f = _
  rw [← h, ← mul_assoc, ← mul_pow, h2, one_pow, one_mul]

variable {K}

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem TWmap_smul {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (r : OW l O)
    (x : TW (OW l O) T) : TWmap (frobOW l O) T (r • x) = frobOW l O r • TWmap (frobOW l O) T x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x =>
    simp only [TWmap, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem exists_frobMat_eq {n : ℕ} (X Y : Fin n → Fin n → ZMod a → invE l e (A O K))
    (h : ∀ i j, ∑ m, ϖ.iW t K (X i m) * ϖ.iW t K (Y m j) = if i = j then 1 else 0) :
    ∃ P : PhiMod O K l e a (Fin n), ∀ i j, frobMat t ϖ P i j = ϖ.iW t K (X i j) := by
  have hτ : ∀ τ, (Matrix.of fun i j => X i j τ) * (Matrix.of fun i j => Y i j τ) = 1 := fun τ => by
    ext1 i j
    have h1 : ∑ m, X i m * Y m j = if i = j then 1 else 0 := ϖ.iW_injective t K (by
      rw [map_sum, apply_ite (ϖ.iW t K), map_one, map_zero, ← h]
      simp only [map_mul])
    have h2 := congrFun h1 τ
    rw [Finset.sum_apply, ite_apply] at h2
    exact h2
  exact ⟨⟨fun τ => ⟨_, _, hτ τ, mul_eq_one_comm.1 (hτ τ)⟩⟩, fun _ _ => rfl⟩

theorem exists_ident {V : Type} [AddCommGroup V] [Module (OW l O) V] (F : V →+ V)
    (hF : ∀ (r : OW l O) (x : V), F (r • x) = frobOW l O r • F x) {n q : ℕ}
    (b : Module.Basis (Fin n) (OW l O) V) (N : AddSubgroup V)
    (hb : ∀ j, b j ∈ N) (hN : ∀ x ∈ N, ∀ j, ∃ f, b.repr x j = iR K t ϖ f)
    (hs : ∀ f, ∀ x ∈ N, iR K t ϖ f • x ∈ N)
    (h1 : ∀ x ∈ N, ∃ k : ℕ, iR K t ϖ (fun _ => EIn l e _) ^ k • F x ∈ N)
    (c : Fin q → V) (hc : ∀ i, c i ∈ N)
    (h2 : ∀ x ∈ N, ∃ (k : ℕ) (s : Fin q → ZMod a → A O K),
      iR K t ϖ (fun _ => EIn l e _) ^ k • x = ∑ i, iR K t ϖ (s i) • F (c i)) :
    ∃ P : PhiMod O K l e a (Fin n),
      (∀ v, b.equivFun.symm (phiW t ϖ P v) = F (b.equivFun.symm v)) ∧ ∀ y, y ∈ N ↔
      ∃ (m : Vec K a (Fin n)) (hm : m ∈ P.M), y = b.equivFun.symm (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := by
  have hX : ∀ i j, ∃ y, ϖ.iW t K y = b.repr (F (b j)) i := fun i j => by
    obtain ⟨k, hk⟩ := h1 _ (hb j)
    obtain ⟨f, hf⟩ := hN _ hk i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at hf
    exact exists_iW_eq K t ϖ hf
  choose X hX using hX
  have hY : ∀ j, ∃ y : Fin n → ZMod a → invE l e (A O K),
      b j = ∑ m, ϖ.iW t K (y m) • F (b m) := fun j => by
    obtain ⟨k, s, hk⟩ := h2 _ (hb j)
    choose f hf using fun i m => hN _ (hc i) m
    have hu : IsUnit (iR K t ϖ (fun _ => EIn l e _) ^ k) := by
      rw [iR_E]
      exact ((ϖ.isUnit_inclW_ev_eis a).map
        (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O)).pow k
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h3 : ∀ m, ∃ y, ϖ.iW t K y = v * iR K t ϖ (∑ i, s i * frobAc l (f i m)) := fun m =>
      exists_iW_eq K t ϖ (k := k) (by rw [← mul_assoc, hv, one_mul])
    choose y hy using h3
    refine ⟨y, ?_⟩
    have h4 : ∀ i, F (c i) =
        ∑ m, iR K t ϖ (frobAc l (f i m)) • F (b m) := fun i => by
      conv_lhs => rw [← b.sum_repr (c i), map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hF, hf]
      congr 1
      exact (frobOW_inclO _).trans (congrArg (inclO l O) (ϖ.iTot_frob t K _).symm)
    rw [← one_smul (OW l O) (b j), ← hv, mul_comm, mul_smul, hk]
    simp only [hy, h4, map_sum, map_mul, mul_smul, Finset.sum_smul, ← Finset.smul_sum]
    simp only [Finset.smul_sum]
    exact Finset.sum_comm
  choose Y hY using hY
  obtain ⟨P, hP⟩ := exists_frobMat_eq t ϖ X (fun m j => Y j m) fun i j => by
    have h3 := congrArg (b.repr · i) (hY j)
    simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, ← hX, b.repr_self,
      Finsupp.single_apply] at h3
    simpa only [mul_comm, eq_comm (a := j)] using h3.symm
  simp only [hX] at hP
  have hj : ∀ v, b.equivFun.symm (phiW t ϖ P v) = F (b.equivFun.symm v) := fun v => by
    rw [b.equivFun_symm_apply, b.equivFun_symm_apply, map_sum]
    have h0 : ∀ i, phiW t ϖ P v i = ∑ j, frobMat t ϖ P i j * frobOW l O (v j) := fun _ => rfl
    simp only [h0, hP, Finset.sum_smul, hF]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← b.sum_repr (F (b j)), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
  have hW : ∀ (m : Vec K a (Fin n)) (hm : m ∈ P.M) i, toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i =
      iR K t ϖ fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩ := fun m hm i =>
    ϖ.iW_of_mem t K fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩
  refine ⟨P, hj, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · choose f hf using hN y hy
    refine ⟨fun τ i => f i τ, mem_tot.2 fun τ i => (f i τ).2, ?_⟩
    rw [b.equivFun_symm_apply]
    conv_lhs => rw [← b.sum_repr y]
    exact Finset.sum_congr rfl fun i _ => by rw [hW _ (mem_tot.2 fun τ i => (f i τ).2), hf]
  · rintro ⟨m, hm, rfl⟩
    rw [b.equivFun_symm_apply]
    exact sum_mem fun i _ => by rw [hW m hm]; exact hs _ _ (hb i)

theorem ev_injective (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] : Function.Injective ((inclW l).comp (ϖ.ev a)) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine (injective_iff_map_eq_zero _).2 fun s hs => PowerSeries.ext fun n => ?_
  have h1 : toAc t K s = 0 := iR_injective K t ϖ (by
    rw [iR_toAc, map_zero, show inclW l (ϖ.ev a s) = 0 from hs, tmul_zero])
  have h2 := coeff_toAc t K s 0 n
  rw [h1, emb_zero] at h2
  by_contra h0
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' _ h0
  rw [hu, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast] at h2
  exact mul_ne_zero (pow_ne_zero m (Nat.cast_ne_zero.2 hl.out.ne_zero))
    ((u.isUnit.map t).map (algebraMap O K)).ne_zero h2.symm

theorem exists_basis {V : Type} [AddCommGroup V] [Module (OW l O) V] [Module (WCb l) V]
    (hW : ∀ (w : WCb l) (x : V), w • x = ((1 : O) ⊗ₜ[ℤ_[l]] w) • x) {n q : ℕ}
    (v : Module.Basis (Fin n) (OW l O) V) (c : Module.Basis (Fin q) (WCb l) V) (N : AddSubgroup V)
    (hN : ∀ x, x ∈ N ↔ ∃ s : Fin q → (Wq l a)⟦X⟧, x = ∑ i, inclW l (ϖ.ev a (s i)) • c i)
    (hs : ∀ f, ∀ x ∈ N, iR K t ϖ f • x ∈ N) :
    ∃ b : Module.Basis (Fin n) (OW l O) V, (∀ j, b j ∈ N) ∧
      ∀ x ∈ N, ∀ j, ∃ f, b.repr x j = iR K t ϖ f := by
  classical
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have : IsDomain O := Function.Injective.isDomain (algebraMap O K) IsUnitBall.inj
  have := isDVR l O K
  let g : O⟦X⟧ →+* OW l O := ((inclO l O).comp (ϖ.evO O)).toRingHom
  have hg : ∀ f, g f = iR K t ϖ fun _ => equivA O K f := fun f =>
    congrArg (inclO l O) ((glue_const _ _ _).trans (ϖ.iA_equivA O K f)).symm
  have hg' : ∀ f, g f = inclO l O (ϖ.iA O K (equivA O K f)) := fun f =>
    congrArg (inclO l O) (ϖ.iA_equivA O K f).symm
  let ε := idem (constW t)
  have hε : ∀ τ, ε τ = iR K t ϖ (Pi.single τ 1) := fun τ => by
    rw [iR_apply, Finset.sum_eq_single τ (fun σ _ h => by simp [h]) (by simp)]
    simp [ε]
  have hεi : ∀ τ f, ε τ * iR K t ϖ f = ε τ * g ((equivA O K).symm (f τ)) := fun τ f => by
    rw [iR_apply, idem_mul_sum, hg', AlgEquiv.apply_symm_apply]
  have hεN : ∀ τ, ∀ x ∈ N, ε τ • x ∈ N := fun τ x hx => hε τ ▸ hs _ x hx
  have hgN : ∀ f, ∀ x ∈ N, g f • x ∈ N := fun f x hx => hg f ▸ hs _ x hx
  have hX : g X = (1 : O) ⊗ₜ[ℤ_[l]] inclW l (ϖ.ev a X) := by
    rw [PiSys.ev_X]
    exact congrArg (inclO l O) (ϖ.evO_X O)
  have hXu : IsUnit (g X) := by
    rw [hX, PiSys.ev_X]
    exact ϖ.isUnit_inclO_teichR O
  have hψ : ∀ τ s, ∃ f, ε τ * ((1 : O) ⊗ₜ[ℤ_[l]] inclW l (ϖ.ev a s)) = ε τ * g f := fun τ s =>
    ⟨_, by rw [← iR_toAc K t, hεi]⟩
  have htf : ∀ (k : ℕ), ∀ x ∈ N, ∀ y ∈ N, (l : OW l O) ^ k • x = g X • y → ∃ z ∈ N, x = g X • z := by
    intro k x hx y hy h
    obtain ⟨s, rfl⟩ := (hN x).1 hx
    obtain ⟨s', rfl⟩ := (hN y).1 hy
    have h0 : (l : OW l O) ^ k = (1 : O) ⊗ₜ[ℤ_[l]] inclW l (ϖ.ev a (l ^ k)) := by
      rw [← iR_toAc K t, map_pow, map_pow, map_natCast, map_natCast]
    rw [hX, h0, ← hW, ← hW] at h
    simp only [Finset.smul_sum, smul_smul, ← map_mul] at h
    have h1 : ∀ i, ∃ r, s i = X * r := fun i => by
      have h2 := congrArg (c.repr · i) h
      simp only [c.repr_sum_self] at h2
      have h3 := congrArg constantCoeff (ev_injective ϖ t K h2)
      rw [map_mul, map_mul, constantCoeff_X, zero_mul, map_pow, map_natCast] at h3
      exact X_dvd_iff.2 ((mul_eq_zero.1 h3).resolve_left (pow_ne_zero _ (WittVector.p_nonzero l _)))
    choose r hr using h1
    refine ⟨_, (hN _).2 ⟨r, rfl⟩, ?_⟩
    rw [hX, ← hW]
    simp only [Finset.smul_sum, smul_smul, ← map_mul, hr]
  obtain ⟨b, hb, hb'⟩ := exists_basis_of_dual_pairs g ε (idem_mul_self (constW t))
    (fun _ _ => idem_mul_of_ne (constW t)) (sum_idem (constW t)) (fun τ m m' h => by
      rw [hε, ← map_nsmul, ← map_nsmul] at h
      have h1 := congrArg (fun f : ZMod a → A O K => constantCoeff (f τ : K⟦X⟧)) (iR_injective K t ϖ h)
      simpa using h1) v N hεN fun τ => by
    letI : Module O⟦X⟧ V := Module.compHom V g
    let M : Submodule O⟦X⟧ V :=
      { carrier := {x | x ∈ N ∧ ε τ • x = x}
        add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, by rw [smul_add, hx.2, hy.2]⟩
        zero_mem' := ⟨zero_mem _, smul_zero _⟩
        smul_mem' := fun f x hx => ⟨hgN f x hx.1, by
          change ε τ • g f • x = g f • x
          rw [smul_comm, hx.2]⟩ }
    have hm : ∀ x ∈ N, ε τ • x ∈ M := fun x hx => ⟨hεN τ x hx, by rw [smul_smul, idem_mul_self]⟩
    have hc : ∀ i, c i ∈ N := fun i => (hN _).2 ⟨Pi.single i 1, by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]; simp⟩
    have : Module.Finite O⟦X⟧ M := by
      refine Module.Finite.iff_fg.2 ⟨Finset.univ.image fun i => ε τ • c i, le_antisymm ?_ fun x hx => ?_⟩
      · rw [Submodule.span_le, Finset.coe_image]
        rintro _ ⟨i, -, rfl⟩
        exact hm _ (hc i)
      · obtain ⟨s, hs⟩ := (hN x).1 hx.1
        rw [← hx.2, hs, Finset.smul_sum]
        refine sum_mem fun i _ => ?_
        obtain ⟨f, hf⟩ := hψ τ (s i)
        rw [hW, smul_smul, hf, mul_comm, mul_smul]
        exact Submodule.smul_mem _ f (Submodule.subset_span (by simp))
    have : Module.Free O⟦X⟧ M := free_of_X_regular_of_quotient_torsionFree O M
      (fun x hx => Subtype.ext (hXu.smul_eq_zero.1 (congrArg Subtype.val hx))) fun o x ho hy => by
        obtain ⟨y, hy⟩ := hy
        obtain ⟨k, o', h⟩ := exists_pow_mul_mem (O := O) l (algebraMap O K o)⁻¹
        have h1 : (l : O) ^ k = o' * o := IsUnitBall.inj (K := K) (by
          rw [map_mul, ← h, map_pow, map_natCast, inv_mul_cancel_right₀
            fun h0 => ho (IsUnitBall.inj (K := K) (h0.trans (map_zero _).symm))])
        have h2 : g (C o) • (x : V) = g X • (y : V) := congrArg Subtype.val hy
        obtain ⟨z, hz, h3⟩ := htf k x x.2.1 _ (hgN (C o') _ y.2.1) (by
          rw [smul_comm, ← h2, smul_smul, ← map_mul, ← map_mul, ← h1, map_pow, map_pow, map_natCast,
            map_natCast])
        refine ⟨⟨_, hm z hz⟩, Subtype.ext ?_⟩
        change (x : V) = g X • ε τ • z
        rw [smul_comm, ← h3, x.2.2]
    refine ⟨_, exists_dual_pair (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O).toRingHom g hW
      (fun _ _ => rfl) ((inclW l).comp (ϖ.ev a)) c (ε τ) (idem_mul_self (constW t) τ) N hN (hεN τ) (hψ τ)
      (fun p h0 h1 h2 r => ?_) hgN M (fun _ => Iff.rfl) (Module.finBasis O⟦X⟧ M)⟩
    induction r using TensorProduct.induction_on with
    | zero => exact h0
    | tmul o w =>
      convert h1 w (C o)
      rw [show g (C o) = o ⊗ₜ 1 from ((inclO l O).comp (ϖ.evO O)).commutes o]
      simp
    | add x y hx hy => exact h2 _ _ hx hy
  refine ⟨b, hb, fun x hx j => ?_⟩
  obtain ⟨f, hf⟩ := hb' x hx j
  exact ⟨fun τ => equivA O K (f τ), by simp only [hf, iR_apply, hg', ε]⟩

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem kappa_smul {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w' x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem kappa_frob {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      TWmap (frobOW l O) T (kappa T y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w' x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def mulZ {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (c : O) :
    letI := zlLat T
    ↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T :=
  letI := zlLat T
  { toFun := fun x => c • x
    map_add' := smul_add c
    map_smul' := fun z x => smul_comm c (algebraMap ℤ_[l] O z) x }

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem kappa_mulZ {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (c : O) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T ((mulZ T c).lTensor (WCb l) y) = c • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w' x => exact tmul_smul c _ x
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem exists_ident_of_basis {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) {M : Type}
    [AddCommGroup M] [Module (Wq l a)⟦X⟧ M] {q : ℕ} (β : Module.Basis (Fin q) (Wq l a)⟦X⟧ M) :
    letI := zlLat T
    ∀ (J₀ : M →+ WCb l ⊗[ℤ_[l]] ↥T.L.T) (c₀ : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
      (∀ (s : (Wq l a)⟦X⟧) x, J₀ (s • x) = inclW l (ϖ.ev a s) • J₀ x) → (∀ i, c₀ i = J₀ (β i)) →
      (∀ x, ∃ (k : ℕ) (m : M), inclW l (ϖ.ev a (eis l a e)) ^ k •
        TensorProduct.map (frobW l).toLinearMap LinearMap.id (J₀ x) = J₀ m) →
      (∀ x, ∃ (k : ℕ) (s : Fin q → (Wq l a)⟦X⟧), inclW l (ϖ.ev a (eis l a e)) ^ k • J₀ x =
        ∑ i, inclW l (ϖ.ev a (s i)) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c₀ i)) →
      (∀ o x, ∃ y, J₀ y = (mulZ T o).lTensor (WCb l) (J₀ x)) →
      ∃ (n : ℕ) (P : PhiMod O K l e a (Fin n)) (I : Ident t ϖ P T), ∀ y, (∃ x, y = kappa T (J₀ x)) ↔
        ∃ (m : Vec K a (Fin n)) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := by
  letI := zlLat T
  intro J₀ c₀ hJ₀ hc₀ hφ hφ' hO₀
  letI : Module (WCb l) (TW (OW l O) T) := Module.compHom _
    (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] OW l O).toRingHom
  have hW : ∀ (w : WCb l) (x : TW (OW l O) T), w • x = ((1 : O) ⊗ₜ[ℤ_[l]] w) • x := fun _ _ => rfl
  obtain ⟨c, hc⟩ : ∃ c : Module.Basis (Fin q) (WCb l) (TW (OW l O) T), ∀ i, c i = kappa T (c₀ i) :=
    ⟨c₀.map (LinearEquiv.ofBijective
      { toFun := kappa T, map_add' := map_add _, map_smul' := kappa_smul T } (kappa_bijective T)),
      fun _ => rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : M →+ TW (OW l O) T, ∀ x, J x = kappa T (J₀ x) := ⟨(kappa T).comp J₀, fun _ => rfl⟩
  have hJs : ∀ (s : (Wq l a)⟦X⟧) x, J (s • x) = iR K t ϖ (toAc t K s) • J x := fun s x => by
    rw [hJ, hJ, hJ₀, kappa_smul, iR_toAc]
  have hc' : ∀ i, c i = J (β i) := fun i => by rw [hc, hc₀, hJ]
  have hN : ∀ x, x ∈ J.range ↔ ∃ s : Fin q → (Wq l a)⟦X⟧, x = ∑ i, inclW l (ϖ.ev a (s i)) • c i := by
    intro x
    simp only [hc', hW, ← iR_toAc K t, ← hJs]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨β.repr y, by rw [← map_sum, β.sum_repr]⟩
    · rintro ⟨s, rfl⟩
      exact ⟨_, map_sum _ _ _⟩
  have hs : ∀ f, ∀ x ∈ J.range, iR K t ϖ f • x ∈ J.range := by
    rintro f _ ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) f
    rw [map_sum, Finset.sum_smul]
    refine sum_mem fun i _ => ?_
    obtain ⟨z, hz⟩ := hO₀ (Module.Free.chooseBasis ℤ_[l] O i) (s i • y)
    refine ⟨z, ?_⟩
    rw [hJ, hz, kappa_mulZ, ← hJ, hJs, map_smul, smul_assoc]
  have hE : ∀ (k : ℕ) (x : WCb l ⊗[ℤ_[l]] ↥T.L.T), iR K t ϖ (fun _ => EIn l e _) ^ k • kappa T x =
      kappa T (inclW l (ϖ.ev a (eis l a e)) ^ k • x) := fun k x => by
    rw [kappa_smul, iR_E, Algebra.TensorProduct.tmul_pow, one_pow]
  obtain ⟨b, hb, hb'⟩ := exists_basis t ϖ hW ((latBasis T).baseChange (OW l O)) c J.range hN hs
  obtain ⟨P, hP, hP'⟩ := exists_ident t ϖ (TWmap (frobOW l O) T).toAddMonoidHom (TWmap_smul T) b J.range hb
    hb' hs (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨k, m, hm⟩ := hφ y
      refine ⟨k, m, ?_⟩
      rw [hJ, hJ, ← hm, ← hE, kappa_frob]
      rfl) c (fun i => ⟨_, (hc' i).symm⟩) (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨k, s, hm⟩ := hφ' y
      refine ⟨k, fun i => toAc t K (s i), ?_⟩
      rw [hJ, hE, hm, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [kappa_smul, kappa_frob, iR_toAc, hc]
      rfl)
  exact ⟨_, P, ⟨b.equivFun.symm, hP⟩, fun y =>
    Iff.trans (exists_congr fun x => by rw [hJ, eq_comm]) (hP' y)⟩

theorem nonempty_bkMod (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) (T : Lat a O K ϖ)
    (h : letI := zlLat T; ∃ E : FCrys l ↥(OL (ϖ.field a)), IsRealisation (ϖ.field a) E ↥T.L.T (actZ T)) :
    Nonempty (BKMod t ϖ T) := by
  letI := zlLat T
  obtain ⟨E, j, H⟩ := h
  have : IsLocalRing (ϖ.prism a).A := inferInstanceAs (IsLocalRing (Wq l a)⟦X⟧)
  obtain ⟨q, β, c₀, hc₀, hφ, hφ'⟩ := LocalValue.general (ϖ.toAinf a) E H.bc
    (fun y => TensorProduct.map (frobW l).toLinearMap LinearMap.id y) H.j_φ
    (Q := eis l a e) (Ideal.mem_span_singleton_self _) ((inclW l).comp (ϖ.ev a)) (fun _ => rfl)
    (ϖ.isUnit_inclW_ev_eis a).ne_zero
  letI : Module (Wq l a)⟦X⟧ (E.M (ϖ.prism a)) := E.mod (ϖ.prism a)
  obtain ⟨n, P, I, hI⟩ := exists_ident_of_basis t ϖ T (M := E.M (ϖ.prism a)) β
    (j.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom) c₀
    (fun s x => (congrArg j ((E.tr (ϖ.toAinf a)).map_smulₛₗ s x)).trans (j.map_smulₛₗ _ _)) hc₀ hφ hφ'
    fun o y => by
      obtain ⟨u, hu, -⟩ := (BS l _ _ _ H.ainf).2 _ _ _ _ E E j j H H (mulZ T o)
        fun g x => ((T.actT g).map_smul o x).symm
      exact ⟨u.u _ y, (congrArg j (u.u_tr (ϖ.toAinf a) y).symm).trans (hu _)⟩
  exact ⟨⟨n, P, I, E, j, H, hI⟩⟩

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (T : Lat a O K ϖ), (letI := zlLat T; ∃ E : FCrys l ↥(OL (ϖ.field a)), IsRealisation (ϖ.field a) E ↥T.L.T (actZ T)) → Nonempty (BKMod t ϖ T) :=
  fun BS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t ϖ T h => nonempty_bkMod t ϖ BS T h

end GlobalTheory.BKReal.OfCrystal
