import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhSmall

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

namespace UpperTheory.V.Alg.KillLoc

open Matrix

section MC

variable {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] [Fintype ι] [DecidableEq ι] {I : Ideal R}

private def MC (I : Ideal R) (f : Γ → Matrix ι ι R) : Prop :=
  ∀ n : ℕ, IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ n)).mapMatrix (f g)

private theorem mk_eq_iff {J : Ideal R} {A B : Matrix ι ι R} :
    (Ideal.Quotient.mk J).mapMatrix A = (Ideal.Quotient.mk J).mapMatrix B ↔ ∀ a b, A a b - B a b ∈ J := by
  rw [← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, map_apply, Ideal.Quotient.eq]

private theorem MC_iff {f : Γ → Matrix ι ι R} : MC I f ↔ ∀ a b, AdicCont I fun g => f g a b := by
  constructor
  · intro h a b n
    exact (h n).comp fun M => M a b
  · intro h n
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have : ∀ᶠ y in nhds g, ∀ a b, Ideal.Quotient.mk (I ^ n) (f y a b) = Ideal.Quotient.mk (I ^ n) (f g a b) :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
        (IsLocallyConstant.iff_eventually_eq _).1 (h a b n) g
    filter_upwards [this] with y hy
    ext a b
    exact hy a b

private theorem MC.mul {f g : Γ → Matrix ι ι R} (hf : MC I f) (hg : MC I g) : MC I fun x => f x * g x := fun n => by
  simp only [map_mul]
  exact (hf n).mul (hg n)

private theorem MC.sub {f g : Γ → Matrix ι ι R} (hf : MC I f) (hg : MC I g) : MC I fun x => f x - g x := fun n => by
  simp only [map_sub]
  exact (hf n).sub (hg n)

private theorem MC.comp {Δ : Type} [TopologicalSpace Δ] {f : Γ → Matrix ι ι R} (hf : MC I f) {φ : Δ → Γ}
    (hφ : Continuous φ) : MC I fun x => f (φ x) := fun n => (hf n).comp_continuous hφ

private theorem MC.of_lc {f : Γ → Matrix ι ι R} (hf : IsLocallyConstant f) : MC I f := fun _ => hf.comp _

end MC

private theorem ker_inf {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Ideal R)
    (hK : maximalIdeal R * K = ⊥) : ∃ N, ∀ k ∈ K, k ∈ maximalIdeal R ^ N → k = 0 := by
  have htor : Module.IsTorsionBySet R K (maximalIdeal R) := by
    rintro ⟨k, hk⟩ ⟨a, ha⟩
    apply Subtype.ext
    show a * k = 0
    rw [← Ideal.mem_bot, ← hK]
    exact Ideal.mul_mem_mul ha hk
  have hart : IsArtinian R K := by
    letI : Module (ResidueField R) K := htor.module
    haveI : IsScalarTower R (ResidueField R) K := htor.isScalarTower
    haveI : Module.Finite (ResidueField R) K := Module.Finite.of_restrictScalars_finite R _ _
    exact isArtinian_of_surjective_algebraMap (R := ResidueField R) (S := R) (M := K) residue_surjective
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := R) (M := K)
    ⟨fun n => OrderDual.toDual (Submodule.comap K.subtype (maximalIdeal R ^ n)),
      fun a b hab => Submodule.comap_mono (Ideal.pow_le_pow_right hab)⟩
  refine ⟨N, fun x hx hxN => ?_⟩
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  intro n
  rcases le_total n N with h | h
  · exact Ideal.pow_le_pow_right h hxN
  · have h1 : Submodule.comap K.subtype (maximalIdeal R ^ N) = Submodule.comap K.subtype (maximalIdeal R ^ n) :=
      hN n h
    have h2 : (⟨x, hx⟩ : K) ∈ Submodule.comap K.subtype (maximalIdeal R ^ N) := hxN
    rw [h1] at h2
    exact h2

private theorem ker_coord (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (K : Ideal R) (hK : maximalIdeal R * K = ⊥) :
    ∃ (n : ℕ) (ψ : (Fin n → ResidueField O) →+ R), Function.Injective ψ ∧ (∀ c, ψ c ∈ K) ∧ (∀ x ∈ K, ∃ c, ψ c = x) ∧
      ∀ x c, x * ψ c = ψ (res O R x • c) := by
  have htor : Module.IsTorsionBySet R K (maximalIdeal R) := by
    rintro ⟨k, hk⟩ ⟨a, ha⟩
    apply Subtype.ext
    show a * k = 0
    rw [← Ideal.mem_bot, ← hK]
    exact Ideal.mul_mem_mul ha hk
  letI : Module (ResidueField R) K := htor.module
  haveI : IsScalarTower R (ResidueField R) K := htor.isScalarTower
  haveI : Module.Finite (ResidueField R) K := Module.Finite.of_restrictScalars_finite R _ _
  let e : ResidueField O ≃+* ResidueField R := RingEquiv.ofBijective _ (resMap_bijective O R)
  have he : ∀ x, e (res O R x) = residue R x := fun x => e.apply_symm_apply _
  let b := (Module.finBasis (ResidueField R) K).equivFun
  let ψ : (Fin (Module.finrank (ResidueField R) K) → ResidueField O) →+ R :=
    { toFun := fun c => (b.symm fun u => e (c u) : K)
      map_zero' := by
        have : (fun u : Fin (Module.finrank (ResidueField R) K) => e ((0 : Fin _ → ResidueField O) u)) = 0 := by
          funext u; simp
        rw [this, map_zero]; rfl
      map_add' := fun c d => by
        have : (fun u => e ((c + d) u)) = (fun u => e (c u)) + fun u => e (d u) := by
          funext u; simp
        rw [this, map_add]; rfl }
  refine ⟨_, ψ, fun c d h => ?_, fun c => (b.symm fun u => e (c u)).2, fun x hx => ⟨fun u => e.symm (b ⟨x, hx⟩ u), ?_⟩,
    fun x c => ?_⟩
  · have := b.symm.injective (Subtype.ext h)
    funext u
    exact e.injective (congrFun this u)
  · show ((b.symm fun u => e (e.symm (b ⟨x, hx⟩ u)) : K) : R) = x
    simp only [RingEquiv.apply_symm_apply]
    rw [show (fun u => b ⟨x, hx⟩ u) = b ⟨x, hx⟩ from rfl, b.symm_apply_apply]
  · show x * ((b.symm fun u => e (c u) : K) : R) = ((b.symm fun u => e ((res O R x • c) u) : K) : R)
    have : (fun u => e ((res O R x • c) u)) = residue R x • fun u => e (c u) := by
      funext u; simp [he]
    rw [this, map_smul, show residue R x = algebraMap R _ x from rfl, algebraMap_smul]
    rfl

private theorem ker_mat (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (K : Ideal R) (hK : maximalIdeal R * K = ⊥) (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ (n : ℕ) (Ψ : (Fin n → Matrix ι ι (ResidueField O)) →+ Matrix ι ι R), Function.Injective Ψ ∧
      (∀ Y a b, Ψ Y a b ∈ K) ∧ (∀ Z : Matrix ι ι R, (∀ a b, Z a b ∈ K) → ∃ Y, Ψ Y = Z) ∧
      (∀ (A : Matrix ι ι R) Y, A * Ψ Y = Ψ fun u => A.map (res O R) * Y u) ∧
      (∀ (A : Matrix ι ι R) Y, Ψ Y * A = Ψ fun u => Y u * A.map (res O R)) ∧
      (∀ Y, (Ψ Y)ᵀ = Ψ fun u => (Y u)ᵀ) ∧ ∀ Y a b, Ψ Y a b = 0 ↔ ∀ u, Y u a b = 0 := by
  obtain ⟨n, ψ, h1, h2, h3, h4⟩ := ker_coord O K hK
  let Ψ : (Fin n → Matrix ι ι (ResidueField O)) →+ Matrix ι ι R :=
    { toFun := fun Y => Matrix.of fun a b => ψ fun u => Y u a b
      map_zero' := by ext a b; exact map_zero ψ
      map_add' := fun Y Z => by ext a b; exact map_add ψ _ _ }
  have hΨ : ∀ Y a b, Ψ Y a b = ψ fun u => Y u a b := fun _ _ _ => rfl
  refine ⟨n, Ψ, fun Y Z h => ?_, fun Y a b => h2 _, fun Z hZ => ?_, fun A Y => ?_, fun A Y => ?_, fun Y => rfl,
    fun Y a b => ?_⟩
  · ext u a b
    exact congrFun (h1 (congrFun (congrFun h a) b)) u
  · choose c hc using fun a b => h3 _ (hZ a b)
    refine ⟨fun u => Matrix.of fun a b => c a b u, ?_⟩
    ext a b
    exact hc a b
  · ext a b
    simp only [mul_apply, hΨ, h4, ← map_sum]
    congr 1
    funext u
    simp
  · ext a b
    simp only [mul_apply, hΨ, mul_comm (ψ _), h4, ← map_sum]
    congr 1
    funext u
    simp [mul_comm]
  · rw [hΨ, map_eq_zero_iff ψ h1, funext_iff]
    rfl

section Mask

variable {O : Type} [CommRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
  {k : Type} [CommRing k] [Algebra O k]

open Classical in
private noncomputable def mask (w : ι → X) (j : X) : Matrix ι ι k →+ Matrix ι ι k where
  toFun Y := Matrix.of fun a b => if w a - w b = j then Y a b else 0
  map_zero' := by ext a b; simp
  map_add' Y Z := by ext a b; simp only [of_apply, Matrix.add_apply]; split_ifs <;> simp

open Classical in
omit [Fintype ι] [DecidableEq ι] in
private theorem mask_apply (j : X) (Y : Matrix ι ι k) (a b : ι) :
    mask w j Y a b = if w a - w b = j then Y a b else 0 := rfl

omit [DecidableEq ι] in
private theorem mask_left (j : X) {A : Matrix ι ι k} (hA : ∀ a b, w a ≠ w b → A a b = 0) (Y : Matrix ι ι k) :
    mask w j (A * Y) = A * mask w j Y := by
  ext a b
  simp only [mask_apply, mul_apply]
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι)), ← Finset.sum_ite_irrel]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : w a = w c
  · rw [h]; split_ifs <;> simp
  · simp [hA a c h]

omit [DecidableEq ι] in
private theorem mask_right (j : X) {A : Matrix ι ι k} (hA : ∀ a b, w a ≠ w b → A a b = 0) (Y : Matrix ι ι k) :
    mask w j (Y * A) = mask w j Y * A := by
  ext a b
  simp only [mask_apply, mul_apply]
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι)), ← Finset.sum_ite_irrel]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : w c = w b
  · rw [h]; split_ifs <;> simp
  · simp [hA c b h]

private theorem mask_mem (Φ : FormData O w) (j : X) {Y : Matrix ι ι k} (hY : Y ∈ Φ.g k) : mask w j Y ∈ Φ.gw k j := by
  refine ⟨⟨?_, fun a b h => by simp [mask_apply, hY.2 a b h]⟩, fun a b h => by simp [mask_apply, h]⟩
  ext a b
  have h0 := congrFun (congrFun hY.1 a) b
  have hJ : ∀ c d, w c + w d ≠ Φ.c → Φ.JR k c d = 0 := fun c d h => by
    have : Φ.J c d = 0 := by_contra fun n => h (Φ.hw c d n)
    simp [FormData.JR, this]
  simp only [Matrix.add_apply, mul_apply, transpose_apply, mask_apply, Matrix.zero_apply] at h0 ⊢
  have e1 : ∀ c, w c + w b = Φ.c → w c - w a = Φ.c - w a - w b := fun c h => by rw [← h]; abel
  have e2 : ∀ c, w a + w c = Φ.c → w c - w b = Φ.c - w a - w b := fun c h => by rw [← h]; abel
  by_cases hj : Φ.c - w a - w b = j
  · rw [← h0]
    congr 1 <;> refine Finset.sum_congr rfl fun c _ => ?_
    · by_cases h : w c + w b = Φ.c
      · rw [e1 c h, if_pos hj]
      · simp [hJ c b h]
    · by_cases h : w a + w c = Φ.c
      · rw [e2 c h, if_pos hj]
      · simp [hJ a c h]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro c _
      by_cases h : w a + w c = Φ.c
      · rw [e2 c h, if_neg hj, mul_zero]
      · simp [hJ a c h]
    · intro c _
      by_cases h : w c + w b = Φ.c
      · rw [e1 c h, if_neg hj, zero_mul]
      · simp [hJ c b h]

omit [Fintype ι] [DecidableEq ι] in
private theorem sum_mask (S : Finset X) (hS : ∀ a b, w a - w b ∈ S) (Y : Matrix ι ι k) :
    ∑ j ∈ S, mask w j Y = Y := by
  classical
  ext a b
  rw [Matrix.sum_apply]
  simp only [mask_apply]
  convert (Finset.sum_ite_eq S (w a - w b) fun _ => Y a b).trans (if_pos (hS a b))

private theorem cob_all (Φ : FormData O w) {Γ : Type} [Group Γ] [TopologicalSpace Γ] {ρ : Γ →* Matrix ι ι k}
    (hρ : Φ.Normalises ρ) (N : Subgroup Γ)
    (H : ∀ (j : X) (κ : Γ × Γ → Φ.gw k j), IsLocallyConstant κ →
      (∀ s t u, FormData.adRep hρ j s (κ (t, u)) + κ (s, t * u) = κ (s * t, u) + κ (s, t)) →
      (∀ s t, ∀ n ∈ N, ∀ n' ∈ N, κ (s * n, t * n') = κ (s, t)) → ∃ a : Γ → Φ.gw k j, IsLocallyConstant a ∧
        (∀ s, ∀ n ∈ N, a (s * n) = a s) ∧ dOne (FormData.adRep hρ j) a = κ)
    (κ : Γ × Γ → Matrix ι ι k) (h0 : ∀ x, κ x ∈ Φ.g k) (h1 : IsLocallyConstant κ)
    (h2 : ∀ s t u, ρ s * κ (t, u) * ρ s⁻¹ + κ (s, t * u) = κ (s * t, u) + κ (s, t))
    (h3 : ∀ s t, ∀ n ∈ N, ∀ n' ∈ N, κ (s * n, t * n') = κ (s, t)) :
    ∃ a : Γ → Matrix ι ι k, (∀ s, a s ∈ Φ.g k) ∧ IsLocallyConstant a ∧ (∀ s, ∀ n ∈ N, a (s * n) = a s) ∧
      ∀ s t, a s + ρ s * a t * ρ s⁻¹ - a (s * t) = κ (s, t) := by
  classical
  have hw := hρ.2.2
  have key := fun j => H j (fun x => ⟨mask w j (κ x), mask_mem Φ j (h0 x)⟩)
    (by
      rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
      intro x
      filter_upwards [h1 x] with y hy
      exact Subtype.ext (congrArg (mask w j) hy))
    (fun s t u => Subtype.ext (by
      have := congrArg (mask w j) (h2 s t u)
      rw [map_add, map_add, mask_right j (hw _), mask_left j (hw _)] at this
      exact this))
    (fun s t n hn n' hn' => Subtype.ext (congrArg (mask w j) (h3 s t n hn n' hn')))
  choose a a1 a2 a3 using key
  let S : Finset X := Finset.univ.image fun p : ι × ι => w p.1 - w p.2
  have hS : ∀ a b, w a - w b ∈ S := fun a b => Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, rfl⟩
  refine ⟨fun s => ∑ j ∈ S, (a j s : Matrix ι ι k), fun s => Submodule.sum_mem _ fun j _ => (a j s).2.1, ?_,
    fun s n hn => by simp only [a2 _ s n hn], fun s t => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have : ∀ᶠ y in nhds x, ∀ j ∈ S, a j y = a j x :=
      (Filter.eventually_all_finset S).2 fun j _ => (IsLocallyConstant.iff_eventually_eq _).1 (a1 j) x
    filter_upwards [this] with y hy
    exact Finset.sum_congr rfl fun j hj => by rw [hy j hj]
  · rw [← sum_mask S hS (κ (s, t)), Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => congrArg Subtype.val (congrFun (a3 j) (s, t))

end Mask

section Small

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
  (Φ : FormData O w) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R']
  [IsCO O R'] (p : R →ₐ[O] R')

private theorem lift_pow (hp : Function.Surjective p) (n : ℕ) (a : R) (ha : p a ∈ maximalIdeal R' ^ n) :
    ∃ k ∈ RingHom.ker p, a - k ∈ maximalIdeal R ^ n := by
  have hmap : (maximalIdeal R).map p = maximalIdeal R' := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun r hr => ?_) fun r hr => ?_
    · show p r ∈ maximalIdeal R'
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hr
    · obtain ⟨r, rfl⟩ := hp r
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff] at hr
      exact Ideal.mem_map_of_mem _ hr
  rw [← hmap, ← Ideal.map_pow] at ha
  obtain ⟨u, hu, hua⟩ := (Ideal.mem_map_iff_of_surjective p hp).1 ha
  refine ⟨a - u, ?_, by simpa using hu⟩
  rw [RingHom.mem_ker, map_sub, hua, sub_self]

private theorem hh_near {J : Ideal R} (hJ : ∀ k ∈ RingHom.ker p, k ∈ J → k = 0) {H h : Matrix ι ι R} (hH : Φ.HH H)
    (hh : Φ.HH (h.map p)) (e : (Ideal.Quotient.mk J).mapMatrix h = (Ideal.Quotient.mk J).mapMatrix H) : Φ.HH h := by
  obtain ⟨a1, a2, a3⟩ := hH
  obtain ⟨b1, b2, b3⟩ := hh
  have jp : (Φ.JR R).map p = Φ.JR R' := by
    ext a b
    simp [FormData.JR]
  refine ⟨?_, fun a b n => hJ _ (b2 a b n) ?_, ?_⟩
  · have e1 : (hᵀ * Φ.JR R * h).map p = (Φ.JR R).map p := by
      rw [Matrix.map_mul, Matrix.map_mul, transpose_map, jp, b1]
    have e2 : (Ideal.Quotient.mk J).mapMatrix (hᵀ * Φ.JR R * h) = (Ideal.Quotient.mk J).mapMatrix (Φ.JR R) := by
      conv_rhs => rw [← a1]
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map] at e ⊢
      rw [e]
    ext a b
    rw [← sub_eq_zero]
    refine hJ _ ?_ (mk_eq_iff.1 e2 a b)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact congrFun (congrFun e1 a) b
  · simpa [a2 a b n] using mk_eq_iff.1 e a b
  · rw [← b3]
    ext a b
    simp [res_map]

private theorem hh_section (hp : Function.Surjective p) {N : ℕ}
    (hN : ∀ k ∈ RingHom.ker p, k ∈ maximalIdeal R ^ N → k = 0)
    (hl : ∀ h' : Matrix ι ι R', Φ.HH h' → ∃ h : Matrix ι ι R, Φ.HH h ∧ h.map p = h') :
    ∃ σ : Matrix ι ι R' → Matrix ι ι R, (∀ h', Φ.HH h' → Φ.HH (σ h') ∧ (σ h').map p = h') ∧
      ∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → Matrix ι ι R'), (∀ s, Φ.HH (f s)) → MC (maximalIdeal R') f →
        MC (maximalIdeal R) fun s => σ (f s) := by
  have hs : ∀ c : Matrix ι ι (R' ⧸ maximalIdeal R' ^ N), ∃ H : Matrix ι ι R, ∀ h', ∃ h : Matrix ι ι R,
      Φ.HH h' → (Ideal.Quotient.mk _).mapMatrix h' = c → Φ.HH h ∧ h.map p = h' ∧
        ∀ a b, h a b - H a b ∈ maximalIdeal R ^ N := by
    intro c
    by_cases hc : ∃ h', Φ.HH h' ∧ (Ideal.Quotient.mk _).mapMatrix h' = c
    · obtain ⟨h0, k1, k2⟩ := hc
      obtain ⟨H, H1, H2⟩ := hl h0 k1
      refine ⟨H, fun h' => ?_⟩
      by_cases hc' : (Ideal.Quotient.mk _).mapMatrix h' = c
      swap
      · exact ⟨0, fun _ e => absurd e hc'⟩
      have : ∀ a b, ∃ y : R, p y = h' a b ∧ y - H a b ∈ maximalIdeal R ^ N := fun a b => by
        obtain ⟨x, hx⟩ := hp (h' a b)
        obtain ⟨k, hk, hxk⟩ := lift_pow p hp N (x - H a b) (by
          rw [map_sub, hx, show p (H a b) = h0 a b from congrFun (congrFun H2 a) b]
          exact mk_eq_iff.1 (hc'.trans k2.symm) a b)
        exact ⟨x - k, by rw [map_sub, hx, RingHom.mem_ker.1 hk, sub_zero], by rwa [sub_right_comm]⟩
      choose y y1 y2 using this
      have e : (Matrix.of y).map p = h' := by
        ext a b
        exact y1 a b
      exact ⟨Matrix.of y, fun k3 _ => ⟨hh_near Φ p hN H1 (e ▸ k3) (mk_eq_iff.2 y2), e, y2⟩⟩
    · exact ⟨0, fun h' => ⟨0, fun k1 k2 => absurd ⟨h', k1, k2⟩ hc⟩⟩
  choose H σ hσ using hs
  refine ⟨fun h' => σ ((Ideal.Quotient.mk _).mapMatrix h') h', fun h' k => ⟨(hσ _ h' k rfl).1, (hσ _ h' k rfl).2.1⟩,
    fun Γ _ f f1 f2 n => ?_⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (f2 (max n N)) g] with s hs
  have h1 := mk_eq_iff.1 hs
  have h2 : (Ideal.Quotient.mk (maximalIdeal R' ^ N)).mapMatrix (f s) = (Ideal.Quotient.mk _).mapMatrix (f g) :=
    mk_eq_iff.2 fun a b => Ideal.pow_le_pow_right (le_max_right _ _) (h1 a b)
  obtain ⟨-, u1, u2⟩ := hσ _ _ (f1 s) rfl
  obtain ⟨-, v1, v2⟩ := hσ _ _ (f1 g) rfl
  refine mk_eq_iff.2 fun a b => ?_
  have h3 := sub_mem (u2 a b) (v2 a b)
  nth_rewrite 2 [h2] at h3
  rw [sub_sub_sub_cancel_right] at h3
  have u3 := congrFun (congrFun u1 a) b
  have v3 := congrFun (congrFun v1 a) b
  rw [map_apply] at u3 v3
  have h5 := h1 a b
  rw [← u3, ← v3, ← map_sub] at h5
  obtain ⟨k, hk, hyk⟩ := lift_pow p hp (max n N) _ h5
  have h4 : k = 0 := hN k hk (by
    simpa using sub_mem h3 (Ideal.pow_le_pow_right (le_max_right _ _) hyk))
  rw [h4, sub_zero] at hyk
  exact Ideal.pow_le_pow_right (le_max_left _ _) hyk

private theorem cob_ker (K : Ideal R) (hK : maximalIdeal R * K = ⊥) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {rbar : Γ →* Matrix ι ι (ResidueField O)} (hbar : Φ.Normalises rbar) (N : Subgroup Γ)
    (H : ∀ (j : X) (κ : Γ × Γ → Φ.gw (ResidueField O) j), IsLocallyConstant κ →
      (∀ s t u, FormData.adRep hbar j s (κ (t, u)) + κ (s, t * u) = κ (s * t, u) + κ (s, t)) →
      (∀ s t, ∀ n ∈ N, ∀ n' ∈ N, κ (s * n, t * n') = κ (s, t)) → ∃ a : Γ → Φ.gw (ResidueField O) j,
        IsLocallyConstant a ∧ (∀ s, ∀ n ∈ N, a (s * n) = a s) ∧ dOne (FormData.adRep hbar j) a = κ)
    (ρ : Γ → Matrix ι ι R) (hρ : ∀ s, (ρ s).map (res O R) = rbar s)
    (κ : Γ × Γ → Matrix ι ι R) (h0 : ∀ x, κ x ∈ Φ.g R) (h0' : ∀ x a b, κ x a b ∈ K) (h1 : IsLocallyConstant κ)
    (h2 : ∀ s t u, ρ s * κ (t, u) * ρ s⁻¹ + κ (s, t * u) = κ (s * t, u) + κ (s, t))
    (h3 : ∀ s t, ∀ n ∈ N, ∀ n' ∈ N, κ (s * n, t * n') = κ (s, t)) :
    ∃ a : Γ → Matrix ι ι R, (∀ s, a s ∈ Φ.g R) ∧ (∀ s i j, a s i j ∈ K) ∧ IsLocallyConstant a ∧
      (∀ s, ∀ n ∈ N, a (s * n) = a s) ∧ ∀ s t, a s + ρ s * a t * ρ s⁻¹ - a (s * t) = κ (s, t) := by
  obtain ⟨n, Ψ, p1, p2, p3, p4, p5, p6, p7⟩ := ker_mat O K hK ι
  have jr : (Φ.JR R).map (res O R) = Φ.JR (ResidueField O) := by
    ext a b
    simp [FormData.JR]
  have hg : ∀ Y, Ψ Y ∈ Φ.g R ↔ ∀ u, Y u ∈ Φ.g (ResidueField O) := fun Y => by
    have e : (Ψ Y)ᵀ * Φ.JR R + Φ.JR R * Ψ Y = 0 ↔
        ∀ u, (Y u)ᵀ * Φ.JR (ResidueField O) + Φ.JR (ResidueField O) * Y u = 0 := by
      rw [p6, p4, p5, jr, ← map_add, map_eq_zero_iff Ψ p1, funext_iff]
      rfl
    constructor
    · rintro ⟨k1, k2⟩ u
      exact ⟨e.1 k1 u, fun a b h => (p7 Y a b).1 (k2 a b h) u⟩
    · intro h
      exact ⟨e.2 fun u => (h u).1, fun a b k => (p7 Y a b).2 fun u => (h u).2 a b k⟩
  choose c hc using fun x => p3 (κ x) (h0' x)
  have key := fun u => cob_all Φ hbar N H (fun x => c x u) (fun x => (hg _).1 (hc x ▸ h0 x) u)
    (by
      rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
      intro x
      filter_upwards [h1 x] with y hy
      exact congrFun (p1 (by rw [hc, hc, hy])) u)
    (fun s t v => by
      have := h2 s t v
      simp only [← hc] at this
      rw [p4, p5, hρ, hρ, ← map_add, ← map_add] at this
      exact congrFun (p1 this) u)
    (fun s t m hm m' hm' => congrFun (p1 (by rw [hc, hc, h3 s t m hm m' hm'])) u)
  choose a a0 a1 a2 a3 using key
  refine ⟨fun s => Ψ fun u => a u s, fun s => (hg _).2 fun u => a0 u s, fun s => p2 _, ?_,
    fun s m hm => by simp only [a2 _ s m hm], fun s t => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have : ∀ᶠ y in nhds x, ∀ u, a u y = a u x :=
      Filter.eventually_all.2 fun u => (IsLocallyConstant.iff_eventually_eq _).1 (a1 u) x
    filter_upwards [this] with y hy
    simp only [hy]
  · rw [p4, p5, hρ, hρ, ← map_add, ← map_sub, ← hc]
    congr 1
    funext u
    exact a3 u s t

private theorem absorb (K : Ideal R) (hK : maximalIdeal R * K = ⊥) {h Z : Matrix ι ι R} (hh : h.map (res O R) = 1)
    (hZ : ∀ a b, Z a b ∈ K) : h * Z = Z ∧ Z * h = Z := by
  obtain ⟨n, Ψ, p1, p2, p3, p4, p5, p6, p7⟩ := ker_mat O K hK ι
  obtain ⟨Y, rfl⟩ := p3 Z hZ
  rw [p4, p5, hh]
  simp

end Small

end UpperTheory.V.Alg.KillLoc

open UpperTheory.V.Alg.KillLoc in
theorem UpperTheory.V.Alg.kill_loc :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (N : Subgroup Γ) [N.Normal], (∀ n ∈ N, r0.hom n = 1) →
      (∀ (j : X) (κ : Γ × Γ → Φ.gw (ResidueField O) j), IsLocallyConstant κ → (∀ s t u, FormData.adRep hbar j s (κ (t, u)) + κ (s, t * u) = κ (s * t, u) + κ (s, t)) →
        (∀ s t, ∀ n ∈ N, ∀ n' ∈ N, κ (s * n, t * n') = κ (s, t)) → ∃ a : Γ → Φ.gw (ResidueField O) j, IsLocallyConstant a ∧ (∀ s, ∀ n ∈ N, a (s * n) = a s) ∧ dOne (FormData.adRep hbar j) a = κ) →
      Φ.IsLocCond r0.hom N (killCond rbar N) := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar hr0 N hNn hN H
  refine ⟨fun R _ _ _ r _ => ?_, fun R _ _ _ r r' h _ hh e hL n hn => ?_, fun R _ _ _ r r' t _ _ e hL n hn => ?_, ?_,
    fun R R' _ _ _ _ _ _ p _ _ r₁ r₂ _ _ _ hL => ?_⟩
  · refine ⟨Ideal.span {x | ∃ n ∈ N, ∃ a b, x = r.hom n a b - (1 : Matrix ι ι R) a b}, fun R' _ _ _ f => ?_⟩
    have one : ∀ a b, f ((1 : Matrix ι ι R) a b) = (1 : Matrix ι ι R') a b := fun a b => by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    constructor
    · intro hL
      show Ideal.span _ ≤ RingHom.ker f
      rw [Ideal.span_le]
      rintro _ ⟨n, hn, a, b, rfl⟩
      show f _ = 0
      rw [map_sub, one, ← hL n hn, Lift.map_hom, sub_self]
    · intro h n hn
      ext a b
      have := h _ (Ideal.subset_span ⟨n, hn, a, b, rfl⟩)
      rwa [map_sub, one, sub_eq_zero] at this
  · obtain ⟨h', -, e1, -⟩ := (hh_group O ι X w Φ R).2.2.1 h hh
    have := congrArg (· * h') (e n)
    simpa [hL n hn, mul_assoc, e1] using this
  · ext a b
    rw [e, hL n hn]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  swap
  · exact ⟨fun h n hn => (h n hn).trans (hL n hn).symm, fun h n hn => (h n hn).trans (hL n hn)⟩
  intro R R' _ _ _ _ _ _ p hp hK r' hr' hL
  obtain ⟨M, hM⟩ := ker_inf _ hK
  obtain ⟨s1, s2, s3⟩ := hh_small O ι X w Φ h2 R R' p hp hK
  obtain ⟨g1, g2, g3, -, g5, -⟩ := hh_group O ι X w Φ R
  obtain ⟨σ, σ1, σ2⟩ := hh_section Φ p hp hM s1
  let ρ : Γ →* Matrix ι ι R := (r0.map (Algebra.ofId O R)).hom
  let ρ' : Γ →* Matrix ι ι R' := (r0.map (Algebra.ofId O R')).hom
  have ρc : MC (maximalIdeal R) ρ := MC_iff.2 (r0.map (Algebra.ofId O R)).cont
  have ρc' : MC (maximalIdeal R') ρ' := MC_iff.2 (r0.map (Algebra.ofId O R')).cont
  have ρr : ∀ s, (ρ s).map (res O R) = rbar s := fun s => by
    ext a b
    exact (r0.map (Algebra.ofId O R)).red s a b
  have ρp : ∀ s, p.mapMatrix (ρ s) = ρ' s := fun s => by
    ext a b
    exact p.commutes _
  have ρN : ∀ n ∈ N, ρ n = 1 := fun n hn => by
    show (Algebra.ofId O R).mapMatrix (r0.hom n) = 1
    rw [hN n hn, map_one]
  have ρN' : ∀ n ∈ N, ρ' n = 1 := fun n hn => by rw [← ρp, ρN n hn, map_one]
  have ρ1 : ∀ s, ρ s * ρ s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have ρ2 : ∀ s, ρ s⁻¹ * ρ s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  have ρ3 : ∀ s (A : Matrix ι ι R), ρ s⁻¹ * (ρ s * A) = A := fun s A => by rw [← mul_assoc, ρ2, one_mul]
  have ρ3' : ∀ s (A : Matrix ι ι R'), ρ' s⁻¹ * (ρ' s * A) = A := fun s A => by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hr'' : ∀ s, Φ.HH (r'.hom s * ρ' s⁻¹) := hr'
  have g5' : ∀ s (h : Matrix ι ι R), Φ.HH h → Φ.HH (ρ s * h * ρ s⁻¹) := g5 Γ r0.hom hr0
  obtain ⟨h, h1, hp1, hc, hn⟩ : ∃ h : Γ → Matrix ι ι R, (∀ s, Φ.HH (h s)) ∧
      (∀ s, p.mapMatrix (h s) = r'.hom s * ρ' s⁻¹) ∧ MC (maximalIdeal R) h ∧ ∀ s, ∀ n ∈ N, h (s * n) = h s := by
    refine ⟨fun s => σ (r'.hom s * ρ' s⁻¹), fun s => (σ1 _ (hr'' s)).1, fun s => (σ1 _ (hr'' s)).2,
      σ2 Γ _ hr'' ((MC_iff.2 r'.cont).mul (ρc'.comp continuous_inv)), fun s n hn => ?_⟩
    simp only [map_mul, mul_inv_rev, hL n hn, ρN' _ (N.inv_mem hn), mul_one, one_mul]
  obtain ⟨κ, hκ⟩ : ∃ κ : Γ × Γ → Matrix ι ι R, ∀ x, κ x = h x.1 * (ρ x.1 * h x.2 * ρ x.1⁻¹) - h (x.1 * x.2) :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∀ s t, p.mapMatrix (h (s * t)) = p.mapMatrix (h s * (ρ s * h t * ρ s⁻¹)) := fun s t => by
    simp only [map_mul, hp1, ρp, mul_inv_rev, mul_assoc, ρ3']
  have κg : ∀ x, κ x ∈ Φ.g R := fun x => by
    rw [hκ]
    exact s2 _ _ (h1 _) (g2 _ _ (h1 _) (g5' _ _ (h1 _))) (e0 _ _)
  have κK : ∀ x a b, κ x a b ∈ RingHom.ker p := fun x a b => by
    have : p.mapMatrix (κ x) = 0 := by rw [hκ, map_sub, e0, sub_self]
    exact congrFun (congrFun this a) b
  have κc : IsLocallyConstant κ := by
    have k1 : MC (maximalIdeal R) κ := by
      rw [funext hκ]
      exact ((hc.comp continuous_fst).mul (((ρc.comp continuous_fst).mul (hc.comp continuous_snd)).mul
        (ρc.comp continuous_fst.inv))).sub (hc.comp continuous_mul)
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (k1 M) x] with y hy
    ext a b
    exact sub_eq_zero.1 (hM _ (sub_mem (κK y a b) (κK x a b)) (mk_eq_iff.1 hy a b))
  have adK : ∀ s (Z : Matrix ι ι R), (∀ a b, Z a b ∈ RingHom.ker p) → ∀ a b, (ρ s * Z * ρ s⁻¹) a b ∈ RingHom.ker p :=
    fun s Z hZ a b => by
      simp only [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _
        (Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hZ _ _))
  obtain ⟨a, a0, aK, ac, an, ad⟩ := cob_ker Φ _ hK hbar N H ρ ρr κ κg κK κc
    (fun s t u => by
      rw [← (absorb _ hK (h1 s).2.2 (adK s _ (κK (t, u)))).1,
        ← (absorb _ hK (g5' (s * t) _ (h1 u)).2.2 (κK (s, t))).2]
      simp only [hκ, map_mul, mul_inv_rev, mul_sub, sub_mul, mul_assoc, ρ3]
      abel)
    (fun s t n hn' n' hn'' => by
      have : h (s * n * (t * n')) = h (s * t) := by
        rw [← mul_assoc, hn _ _ hn'', ← hn (s * t) _ (hNn.conj_mem' n hn' t)]
        congr 1
        group
      simp only [hκ, this, hn _ _ hn', hn _ _ hn'', map_mul, mul_inv_rev, ρN _ hn', ρN _ (N.inv_mem hn'), mul_one,
        one_mul])
  have ap : ∀ s, p.mapMatrix (a s) = 0 := fun s => by
    ext i j
    exact aK s i j
  have k1 : ∀ s, Φ.HH (h s - a s) := fun s => by
    rw [sub_eq_add_neg]
    exact s3 _ _ (h1 s) (neg_mem (a0 s)) (show p.mapMatrix (-a s) = 0 by rw [map_neg, ap, neg_zero])
  have mul : ∀ s t, (h (s * t) - a (s * t)) * ρ (s * t) = (h s - a s) * ρ s * ((h t - a t) * ρ t) := fun s t => by
    have e1 : (h s - a s) * ρ s * ((h t - a t) * ρ t) = (h s * (ρ s * h t * ρ s⁻¹) - a s * (ρ s * h t * ρ s⁻¹) -
        (h s - a s) * (ρ s * a t * ρ s⁻¹)) * ρ (s * t) := by
      simp only [map_mul, mul_sub, sub_mul, mul_assoc, ρ3]
    rw [e1, (absorb _ hK (g5' s _ (h1 t)).2.2 (aK s)).2, (absorb _ hK (k1 s).2.2 (adK s _ (aK t))).1]
    congr 1
    have := ad s t
    rw [hκ] at this
    simp only at this
    rw [eq_sub_iff_add_eq] at this
    rw [← this]
    abel
  have one : (h 1 - a 1) * ρ 1 = 1 := by
    obtain ⟨h', -, e1, -⟩ := g3 _ (k1 1)
    have := congrArg (· * h') (mul 1 1)
    simp only [mul_one, map_one, mul_assoc, e1] at this ⊢
    exact this.symm
  let r : Γ →* Matrix ι ι R := { toFun := fun s => (h s - a s) * ρ s, map_one' := one, map_mul' := mul }
  have rp : ∀ s, p.mapMatrix (r s) = r'.hom s := fun s => by
    show p.mapMatrix ((h s - a s) * ρ s) = _
    rw [map_mul, map_sub, ap, sub_zero, hp1, ρp, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  refine ⟨⟨r, MC_iff.1 ((hc.sub (MC.of_lc ac)).mul ρc), fun s i j => ?_⟩, fun s => ?_, fun n hn' => ?_, ?_⟩
  · rw [← res_map p, ← r'.red, ← rp]
    rfl
  · show Φ.HH ((h s - a s) * ρ s * ρ s⁻¹)
    rw [mul_assoc, ρ1, mul_one]
    exact k1 s
  · show (h n - a n) * ρ n = 1
    rw [← one, ← hn 1 n hn', ← an 1 n hn', one_mul, ρN n hn', map_one]
  · ext s i j
    exact congrFun (congrFun (rp s) i) j
