import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCoreStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.ClassCore

theorem cm_refl {X : Type} [AddCommGroup X] (N : ℕ) (x : X) : CongMod N x x := ⟨0, by simp⟩

theorem cm_symm {X : Type} [AddCommGroup X] {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h; exact ⟨-w, by simp⟩

theorem cm_trans {X : Type} [AddCommGroup X] {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) :
    CongMod N x z := by
  obtain ⟨w, rfl⟩ := h; obtain ⟨w', rfl⟩ := h'; exact ⟨w' + w, by rw [smul_add, add_assoc]⟩

theorem cm_map {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {N : ℕ} (g : X →+ Y) {x y : X} (h : CongMod N x y) :
    CongMod N (g x) (g y) := by
  obtain ⟨w, rfl⟩ := h; exact ⟨g w, by simp [map_nsmul]⟩

theorem qW_one {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (μ : Fin 1 → X) :
    qW !![(1 : ℤ)] β μ = β (μ 0) (μ 0) := by
  simp [qW]

theorem exists_min {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, x ≠ 0 → 0 < β x x)
    (N : ℕ) (μ : Fin 1 → X) : ∃ μ' : Fin 1 → X, (∀ u, CongMod N (μ' u) (μ u)) ∧
      ∀ μ'' : Fin 1 → X, (∀ u, CongMod N (μ'' u) (μ u)) → qW !![(1 : ℤ)] β μ' ≤ qW !![(1 : ℤ)] β μ'' := by
  have hnn : ∀ x, 0 ≤ β x x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  obtain ⟨n, ⟨μ', hμ', rfl⟩, hmin⟩ := WellFounded.has_min Nat.lt_wfRel.wf
    {n | ∃ μ' : Fin 1 → X, (∀ u, CongMod N (μ' u) (μ u)) ∧ (qW !![(1 : ℤ)] β μ').toNat = n}
    ⟨_, μ, fun u => cm_refl N _, rfl⟩
  refine ⟨μ', hμ', fun μ'' h => ?_⟩
  have := hmin _ ⟨μ'', h, rfl⟩
  have key := not_lt.1 this
  simp only [qW_one] at key ⊢
  have h1 := hnn (μ' 0); have h2 := hnn (μ'' 0)
  have e1 := Int.toNat_of_nonneg h1; have e2 := Int.toNat_of_nonneg h2
  omega

end GlobalTheory.UPoinc.ClassCore

namespace GlobalTheory.UPoinc.ClassCore

theorem exists_norm_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime]
    {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X) :
    ∃ e : PadicAlgCl p, ‖e‖ = Real.exp (-(t.sc * t.T.be x x)) := by
  have hnn : 0 ≤ t.T.be x x := by simpa using IsMonomial.nonneg t.T.mono 0 x
  set a := t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) with ha
  have ha0 : a ≠ 0 := (map_ne_zero t.ι).2 ((map_ne_zero_iff _ (IsFractionRing.injective t.T.V _)).2 t.T.irr.ne_zero)
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  refine ⟨a ^ (t.T.be x x).toNat, ?_⟩
  have e1 : ((t.T.be x x : ℤ) : ℝ) = (((t.T.be x x).toNat : ℕ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [norm_pow, e1, UCTrait.sc, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

end GlobalTheory.UPoinc.ClassCore

namespace GlobalTheory.UPoinc.ClassCore

theorem main_of_core (hcore : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw
    : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C
    : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar
    : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk
    z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞
    E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀
    : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_
    : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_
    : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁
    Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂)
    a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k
    : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X
    y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ
    : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c
    u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β
    y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β
    y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ
    u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ
    u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) /
    2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk
    z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞
    E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r
    * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ) : ∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l
    : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p
    : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p
    Dw.q) p (X₁.M.Z.presheaf.stalk
    z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞
    E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀
    : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_
    : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_
    : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁
    Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂)
    a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k
    : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 1
    → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1
    : ℤ)] t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε
    : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 1 → Φ.X y), ∀ S : Finset (Fin 1 → Φ.X
    y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c
    u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (a
    : 𝓞 E) x, CongMod N (γ (a • x)) (a • γ x)) ∧ (N
    : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c
    κ) = f (fun u => γ (c u)) κ := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ p _ z₁ Φ hΦ y₀ N₀
  obtain ⟨N, hN₀, hdvd, Ω₂, i1, i2, i3, i4, hc⟩ := hcore E H Dw hpq l Xo c C X₁ p z₁ Φ hΦ y₀ N₀
  refine ⟨N, hN₀, hdvd, Ω₂, i1, i2, i3, i4, ?_⟩
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra
  intro 𝔷 h𝔷 ev' h1 h2 h3
  obtain ⟨k, Q, F, hk0, hcls, hle, heq, hgal⟩ := hc 𝔷 h𝔷 ev' h1 h2 h3
  classical
  let qv : ∀ y, (Fin 1 → Φ.X y) → ℤ := fun y μ => qW !![(1 : ℤ)] (Φ.β y) μ
  let Cg : ∀ y, (Fin 1 → Φ.X y) → (Fin 1 → Φ.X y) → Prop := fun y μ μ' => ∀ u, CongMod N (μ u) (μ' u)
  let sel : ∀ y, (Fin 1 → Φ.X y) → (Fin 1 → Φ.X y) := fun y μ =>
    Classical.epsilon (fun μ' => Cg y μ' μ ∧ ∀ μ'', Cg y μ'' μ → qv y μ' ≤ qv y μ'')
  have hsel : ∀ y μ, Cg y (sel y μ) μ ∧ ∀ μ'', Cg y μ'' μ → qv y (sel y μ) ≤ qv y μ'' := fun y μ =>
    Classical.epsilon_spec (exists_min (Φ.β y) (Φ.pos y) N μ)
  have hselc : ∀ y μ μ', Cg y μ μ' → sel y μ = sel y μ' := by
    intro y μ μ' h
    show Classical.epsilon _ = Classical.epsilon _
    congr 1
    funext μ₁
    apply propext
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun u => cm_trans (h₁ u) (h u), fun μ'' h'' => h₂ μ'' fun u => cm_trans (h'' u) (cm_symm (h u))⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun u => cm_trans (h₁ u) (cm_symm (h u)), fun μ'' h'' => h₂ μ'' fun u => cm_trans (h'' u) (h u)⟩
  let NS : ∀ y, (Fin 1 → Φ.X y) → Prop := fun y μ => ∃ μ', Cg y μ' μ ∧ μ' ≠ μ ∧ qv y μ' ≤ qv y μ
  let wit : ∀ y, (Fin 1 → Φ.X y) → (Fin 1 → Φ.X y) := fun y μ => if h : NS y μ then h.choose else μ
  have hwit : ∀ y μ, NS y μ → Cg y (wit y μ) μ ∧ wit y μ ≠ μ ∧ qv y (wit y μ) ≤ qv y μ := by
    intro y μ h
    simp only [wit, dif_pos h]
    exact h.choose_spec
  have hel : ∀ y μ, ∃ e : PadicAlgCl p, ‖e‖ = Real.exp (-(Φ.sc y * qv y μ)) := by
    intro y μ
    obtain ⟨t, -, e', he'⟩ := hΦ y
    obtain ⟨e, he⟩ := exists_norm_eq t (e' (μ 0))
    refine ⟨e, ?_⟩
    rw [he, ← he']
    simp only [qv, qW_one]
  choose el hel using hel
  let g : ∀ y, (Fin 1 → Φ.X y) → (Fin 1 → Φ.X y) → PadicAlgCl p := fun y μ ν =>
    if NS y μ then (if ν = μ then el y μ else if ν = wit y μ then -el y μ else 0) else 0
  let Q' : Type := Q ⊕ (Σ y, (Fin 1 → Φ.X y))
  let t : ∀ y, (Fin 1 → Φ.X y) → Q' → PadicAlgCl p := fun y ν =>
    Sum.elim (fun κ => if ν = sel y ν then ev' y (F (fun u => (k y).symm (ν u)) κ) ^ 2 else 0)
      (fun s => if h : y = s.1 then g s.1 s.2 (h ▸ ν) else 0)
  let f : (Fin 1 → Φ.X y₀) → Q' → integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂ := fun cc =>
    Sum.elim (fun κ => F cc κ ^ 2) (fun _ => 0)
  refine ⟨fun y => (k y).toLinearMap.restrictScalars ℤ, Q', t, f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (k y₀).toLinearMap.restrictScalars ℤ = _
    rw [hk0]; rfl
  · intro y
    refine ⟨fun a x => ⟨0, by simp⟩, (k y).symm.restrictScalars ℤ, ?_⟩
    have : ((k y).symm.restrictScalars ℤ).toLinearMap ∘ₗ (k y).toLinearMap.restrictScalars ℤ = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.det_id, sub_self]
    exact dvd_zero _
  · have hsc : ∀ y, 0 < Φ.sc y := Φ.sc_pos
    have hsq : ∀ y (μ : Fin 1 → Φ.X y) κ, μ = sel y μ →
        ‖ev' y (F (fun u => (k y).symm (μ u)) κ) ^ 2‖ ≤ Real.exp (-(Φ.sc y * qv y μ)) := by
      intro y μ κ hμ
      have h := hle y (fun u => (k y).symm (μ u)) κ μ (fun u => by
        simp only [LinearEquiv.apply_symm_apply]; exact cm_refl N _) (fun μ' h' => by
          have := (hsel y μ).2 μ' h'
          rw [← hμ] at this
          exact this)
      rw [norm_pow]
      calc ‖ev' y (F _ κ)‖ ^ 2 ≤ Real.exp (-(Φ.sc y * qv y μ) / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hg : ∀ y (μ ν : Fin 1 → Φ.X y), ‖g y μ ν‖ ≤ Real.exp (-(Φ.sc y * qv y ν)) := by
      intro y μ ν
      simp only [g]
      split_ifs with hN hν hw
      · subst hν; rw [hel]
      · subst hw; rw [norm_neg, hel]
        refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (hsc y).le))
        exact_mod_cast (hwit y μ hN).2.2
      · rw [norm_zero]; exact (Real.exp_pos _).le
      · rw [norm_zero]; exact (Real.exp_pos _).le
    refine ⟨fun y μ κ => ?_, fun y μ => ?_⟩
    · rcases κ with κ | ⟨y', μ'⟩
      · simp only [t, Sum.elim_inl]
        split_ifs with hμ
        · exact hsq y μ κ hμ
        · rw [norm_zero]; exact (Real.exp_pos _).le
      · simp only [t, Sum.elim_inr]
        split_ifs with h
        · subst h; exact hg y μ' μ
        · rw [norm_zero]; exact (Real.exp_pos _).le
    · by_cases hns : NS y μ
      · refine ⟨Sum.inr ⟨y, μ⟩, ?_⟩
        simp only [t, Sum.elim_inr, dif_pos rfl, g, if_pos hns, if_pos rfl]
        exact hel y μ
      · have hstrict : ∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ →
            qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ' := by
          intro μ' h1 h2
          by_contra h3
          exact hns ⟨μ', h1, h2, not_lt.1 h3⟩
        obtain ⟨cc, κ, hcc, hnorm⟩ := heq y μ hstrict
        have hsel' : sel y μ = μ := by
          by_contra hne
          have := hstrict _ (hsel y μ).1 hne
          exact absurd ((hsel y μ).2 μ (fun u => cm_refl N _)) (not_le.2 this)
        have hF : F (fun u => (k y).symm (μ u)) κ = F cc κ := by
          refine hcls _ _ κ (fun u => ?_)
          have := cm_map (k y).symm.toLinearMap.toAddMonoidHom (hcc u)
          simpa using this
        refine ⟨Sum.inl κ, ?_⟩
        simp only [t, Sum.elim_inl, hsel', if_pos rfl]
        rw [if_pos trivial, hF, norm_pow, hnorm, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  · rintro cc cc' (κ | s) h
    · simp only [f, Sum.elim_inl, hcls cc cc' κ h]
    · rfl
  · intro y cc κ ε hε
    rcases κ with κ | ⟨y', μ⟩
    · set s := sel y (fun u => k y (cc u)) with hs
      refine ⟨{s}, fun S hS hS₀ => ?_⟩
      have hS' : ∀ μ ∈ S, Cg y μ (fun u => k y (cc u)) := fun μ hμ u => by simpa using hS μ hμ u
      have hmem : s ∈ S := hS₀ s (Finset.mem_singleton_self _) (fun u => by simpa using (hsel y _).1 u)
      have hss : sel y s = s := hselc y s _ (hsel y _).1
      have hsum : ∑ μ ∈ S, t y μ (Sum.inl κ) = t y s (Sum.inl κ) := by
        refine Finset.sum_eq_single_of_mem s hmem (fun μ hμ hne => ?_)
        simp only [t, Sum.elim_inl]
        rw [if_neg]
        intro h
        exact hne (h.trans (hselc y μ _ (hS' μ hμ)))
      have hF : F (fun u => (k y).symm (s u)) κ = F cc κ := by
        refine hcls _ _ κ (fun u => ?_)
        have := cm_map (k y).symm.toLinearMap.toAddMonoidHom ((hsel y (fun u => k y (cc u))).1 u)
        simpa using this
      rw [hsum]
      simp only [t, Sum.elim_inl, hss]
      rw [if_pos trivial, hF]
      simp [f, hε.le]
    · by_cases hy : y = y'
      · subst hy
        refine ⟨{μ, wit y μ}, fun S hS hS₀ => ?_⟩
        have hS' : ∀ ν ∈ S, Cg y ν (fun u => k y (cc u)) := fun ν hν u => by simpa using hS ν hν u
        have hsum : ∑ ν ∈ S, t y ν (Sum.inr ⟨y, μ⟩) = 0 := by
          simp only [t, Sum.elim_inr, dif_pos rfl, dite_true]
          by_cases hns : NS y μ
          · obtain ⟨hw1, hw2, -⟩ := hwit y μ hns
            simp only [g, if_pos hns]
            by_cases hc : Cg y μ (fun u => k y (cc u))
            · have hμS : μ ∈ S := hS₀ μ (by simp) (fun u => by simpa using hc u)
              have hwS : wit y μ ∈ S := hS₀ _ (by simp) (fun u => by simpa using cm_trans (hw1 u) (hc u))
              have e : ∀ ν : Fin 1 → Φ.X y, (if ν = μ then el y μ else if ν = wit y μ then -el y μ else 0) =
                  (if ν = μ then el y μ else 0) + (if ν = wit y μ then -el y μ else 0) := by
                intro ν
                by_cases h1 : ν = μ
                · subst h1; simp [hw2.symm]
                · simp [h1]
              rw [Finset.sum_congr rfl (fun ν _ => e ν), Finset.sum_add_distrib, Finset.sum_ite_eq' S μ,
                Finset.sum_ite_eq' S (wit y μ), if_pos hμS, if_pos hwS, add_neg_cancel]
            · refine Finset.sum_eq_zero (fun ν hν => ?_)
              have h1 : ν ≠ μ := fun h => hc (h ▸ hS' ν hν)
              have h2 : ν ≠ wit y μ := fun h => hc (fun u => cm_trans (cm_symm (hw1 u)) (h ▸ hS' ν hν u))
              simp [h1, h2]
          · simp [g, hns]
        rw [hsum]
        simp [f, hε.le]
      · refine ⟨∅, fun S _ _ => ?_⟩
        have hsum : ∑ ν ∈ S, t y ν (Sum.inr ⟨y', μ⟩) = 0 :=
          Finset.sum_eq_zero (fun ν _ => by simp [t, hy])
        rw [hsum]
        simp [f, hε.le]
  · intro σ hσ
    obtain ⟨γ, hdet, hcong, hF⟩ := hgal σ hσ
    refine ⟨γ.toLinearMap.restrictScalars ℤ, fun a x => ⟨0, by simp⟩, hdet, hcong, ?_⟩
    rintro cc (κ | s)
    · simp [f, hF]
    · simp [f]

end GlobalTheory.UPoinc.ClassCore

namespace GlobalTheory.UPoinc.ClassCore

theorem classSums_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1 : ℤ)] t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 1 → Φ.X y), ∀ S : Finset (Fin 1 → Φ.X y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (a : 𝓞 E) x, CongMod N (γ (a • x)) (a • γ x)) ∧ (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ :=
  main_of_core GlobalTheory.T.unitary_classSums_deeper_level_geometric_core

end GlobalTheory.UPoinc.ClassCore
