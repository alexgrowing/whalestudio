import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.MOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IdemCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bezout

set_option autoImplicit false

noncomputable section

open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Core

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

private theorem kill {a : A} {N : ℕ} {I : Ideal A} (ha : ∀ x ∈ I, (N : A) ∣ a * x) {w : M}
    (hw : w ∈ (I • ⊤ : Submodule A M)) : ∃ z : M, a • w = N • z := by
  refine Submodule.smul_induction_on hw ?_ ?_
  · intro c hc m _
    obtain ⟨d, hd⟩ := ha c hc
    exact ⟨d • m, by rw [smul_smul, hd, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  · rintro x y ⟨z, hz⟩ ⟨z', hz'⟩
    exact ⟨z + z', by rw [smul_add, hz, hz', smul_add]⟩

private theorem ef_nsmul (EF : LinearMap.BilinForm ℤ M) (N : ℕ) (x y : M) :
    EF (N • x) y = (N : ℤ) * EF x y := by
  simp

private theorem dvd_left (EF : LinearMap.BilinForm ℤ M) {N : ℕ} {c : A} (hc : (N : A) ∣ c) (x y : M) :
    (N : ℤ) ∣ EF (c • x) y := by
  obtain ⟨d, rfl⟩ := hc
  rw [mul_smul, Nat.cast_smul_eq_nsmul, ef_nsmul]
  exact Dvd.intro _ rfl

private theorem skew (EF : LinearMap.BilinForm ℤ M) (alt : ∀ x, EF x x = 0) (x y : M) :
    EF x y = - EF y x := by
  have := alt (x + y)
  simp only [map_add, LinearMap.add_apply, alt] at this
  linarith

variable (bar : A ≃+* A) (EF : LinearMap.BilinForm ℤ M)

private theorem iso_step (hbb : ∀ c, bar (bar c) = c) (alt : ∀ x, EF x x = 0)
    (adj : ∀ (c : A) (x y : M), EF (c • x) y = EF x (bar c • y))
    (N : ℕ) (u : Ideal A) (ε : A) (g h : M →ₗ[A] M) (k : M →+ M)
    (h1 : 1 - ε ∈ u) (h2 : bar ε ∈ u) (h3 : ∀ x ∈ u, (N : A) ∣ ε * x) (h4 : (N : A) ∣ ε + bar ε - 1)
    (hhg : ∀ x, h (g x) - x ∈ (u • ⊤ : Submodule A M))
    (hk : ∀ x y, (N : ℤ) ∣ EF (h x) y - EF x (k y)) (x y : M) :
    (N : ℤ) ∣ EF (ε • g x + bar ε • k x) (ε • g y + bar ε • k y) - EF x y := by
  have hee : (N : A) ∣ ε * bar ε := h3 _ h2
  have hsq : (N : A) ∣ ε * ε - ε := by
    obtain ⟨d, hd⟩ := h3 _ h1
    exact ⟨-d, by linear_combination -hd⟩
  have cross : ∀ x y, (N : ℤ) ∣ EF (ε • g x) (bar ε • k y) - EF (ε • x) y := by
    intro x y
    obtain ⟨z, hz⟩ := kill h3 (hhg x)
    have e1 : EF (ε • g x) (bar ε • k y) = EF (ε • ε • g x) (k y) := (adj ε _ _).symm
    obtain ⟨a, ha⟩ := hk (ε • ε • g x) y
    have e2 : h (ε • ε • g x) = N • (ε • z) + (ε * ε - ε) • x + ε • x := by
      rw [map_smul, map_smul, smul_comm N ε z, ← hz]
      module
    obtain ⟨b, hb⟩ := dvd_left EF hsq x y
    rw [e2] at ha
    simp only [map_add, LinearMap.add_apply, ef_nsmul] at ha
    rw [e1]
    exact ⟨EF (ε • z) y + b - a, by linear_combination hb - ha⟩
  obtain ⟨a₁, h₁⟩ := dvd_left EF hee (g x) (g y)
  obtain ⟨a₂, h₂⟩ := dvd_left EF hee (k x) (k y)
  obtain ⟨a₃, h₃⟩ := cross x y
  obtain ⟨a₄, h₄⟩ := cross y x
  obtain ⟨a₅, h₅⟩ := dvd_left EF h4 x y
  have f₁ : EF (ε • g x) (ε • g y) = EF ((ε * bar ε) • g x) (g y) := by
    rw [mul_comm, mul_smul, adj (bar ε), hbb]
  have f₂ : EF (bar ε • k x) (bar ε • k y) = EF ((ε * bar ε) • k x) (k y) := by
    rw [mul_smul, adj ε]
  have f₃ : EF (bar ε • k x) (ε • g y) = - EF (ε • g y) (bar ε • k x) := skew EF alt _ _
  have f₄ : EF (ε • y) x = - EF (bar ε • x) y := by
    rw [adj (bar ε), hbb]
    exact skew EF alt _ _
  have f₅ : EF ((ε + bar ε - 1) • x) y = EF (ε • x) y + EF (bar ε • x) y - EF x y := by
    rw [sub_smul, add_smul, one_smul]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  simp only [map_add, LinearMap.add_apply]
  rw [f₁, f₂, f₃, h₁, h₂]
  exact ⟨a₁ + a₂ + a₃ - a₄ + a₅, by linear_combination h₃ - h₄ + h₅ - f₅ - f₄⟩

private theorem lin_step (N : ℕ) (ε b : A) (g : M →ₗ[A] M) (k : M →+ M)
    (c : A) (x : M) (hk : ∃ z, k (c • x) = c • k x + N • z) :
    ∃ z, ε • g (c • x) + b • k (c • x) = c • (ε • g x + b • k x) + N • z := by
  obtain ⟨z, hz⟩ := hk
  refine ⟨b • z, ?_⟩
  rw [hz, map_smul, smul_add, smul_add, smul_comm N b z, smul_comm ε c, smul_comm b c]
  abel

private theorem smul_le (I : Ideal A) (h : M →ₗ[A] M) {v : M} (hv : v ∈ (I • ⊤ : Submodule A M)) :
    h v ∈ (I • ⊤ : Submodule A M) := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro c hc m _
    rw [map_smul]
    exact Submodule.smul_mem_smul hc Submodule.mem_top
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

private theorem diff_mem (u : Ideal A) (g h h' : M →ₗ[A] M)
    (hhg : ∀ x, h (g x) - x ∈ (u • ⊤ : Submodule A M))
    (hgh : ∀ x, g (h x) - x ∈ (u • ⊤ : Submodule A M))
    (hgh' : ∀ x, g (h' x) - x ∈ (u • ⊤ : Submodule A M)) (y : M) :
    h' y - h y ∈ (u • ⊤ : Submodule A M) := by
  have e : h' y - h y = h ((g (h' y) - y) - (g (h y) - y)) - (h (g (h' y - h y)) - (h' y - h y)) := by
    simp only [map_sub]
    abel
  rw [e]
  exact sub_mem (smul_le u h (sub_mem (hgh' y) (hgh y))) (hhg _)

private theorem tow_step (alt : ∀ x, EF x x = 0) (hbb : ∀ c, bar (bar c) = c)
    (adj : ∀ (c : A) (x y : M), EF (c • x) y = EF x (bar c • y))
    (N : ℕ) (u : Ideal A) (ε ε' : A) (g h h' : M →ₗ[A] M) (k k' : M →+ M)
    (h3 : ∀ x ∈ u, (N : A) ∣ ε * x) (hεε : (N : A) ∣ ε' - ε)
    (hhg : ∀ x, h (g x) - x ∈ (u • ⊤ : Submodule A M))
    (hgh : ∀ x, g (h x) - x ∈ (u • ⊤ : Submodule A M))
    (hgh' : ∀ x, g (h' x) - x ∈ (u • ⊤ : Submodule A M))
    (hk : ∀ x y, (N : ℤ) ∣ EF (h x) y - EF x (k y))
    (hk' : ∀ x y, (N : ℤ) ∣ EF (h' x) y - EF x (k' y))
    (nd : ∀ x : M, (∀ y, (N : ℤ) ∣ EF x y) → ∃ z, x = 0 + N • z) (x : M) :
    ∃ z, ε' • g x + bar ε' • k' x = ε • g x + bar ε • k x + N • z := by
  have hmid : ∃ z, bar ε • (k' x - k x) = 0 + N • z := by
    refine nd _ fun y => ?_
    obtain ⟨w, hw⟩ := kill h3 (diff_mem u g h h' hhg hgh hgh' y)
    obtain ⟨a, ha⟩ := hk (ε • y) x
    obtain ⟨b, hb⟩ := hk' (ε • y) x
    have e₁ : EF (bar ε • (k' x - k x)) y = EF (k' x) (ε • y) - EF (k x) (ε • y) := by
      rw [adj (bar ε), hbb]
      simp only [map_sub, LinearMap.sub_apply]
    have e₂ : EF (h' (ε • y)) x - EF (h (ε • y)) x = (N : ℤ) * EF w x := by
      have e₀ : h' (ε • y) - h (ε • y) = ε • (h' y - h y) := by simp only [map_smul, smul_sub]
      rw [← ef_nsmul, ← hw, ← e₀]
      simp only [map_sub, LinearMap.sub_apply]
    rw [e₁, skew EF alt (k' x), skew EF alt (k x)]
    exact ⟨b - a - EF w x, by linear_combination hb - ha - e₂⟩
  obtain ⟨z, hz⟩ := hmid
  obtain ⟨d, hd⟩ := hεε
  have hd' : bar ε' - bar ε = (N : A) * bar d := by
    rw [← map_sub, hd, map_mul, map_natCast]
  refine ⟨d • g x + bar d • k' x + z, ?_⟩
  have e₁ : ε' = ε + (N : A) * d := by linear_combination hd
  have e₂ : bar ε' = bar ε + (N : A) * bar d := by linear_combination hd'
  rw [zero_add] at hz
  have e₃ : bar ε • k' x = bar ε • k x + N • z := by
    rw [← hz, smul_sub]
    abel
  rw [e₂, add_smul, e₃, e₁, add_smul, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    smul_add, smul_add]
  abel

private theorem lev_step (𝔟 : Ideal A) (ε b : A) (h1 : 1 - ε ∈ 𝔟) (h2 : b ∈ 𝔟) (v w : M) :
    (ε • v + b • w) - v ∈ (𝔟 • ⊤ : Submodule A M) := by
  have e : (ε • v + b • w) - v = b • w - (1 - ε) • v := by module
  rw [e]
  exact sub_mem (Submodule.smul_mem_smul h2 Submodule.mem_top) (Submodule.smul_mem_smul h1 Submodule.mem_top)

end Core

private theorem lift_of_eq (A M : Type) [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] (u 𝔞 : Ideal A) (hu : u ≠ ⊥) (hf : ∃ f : ℕ, u ^ f ≤ 𝔞)
    (P : Submodule A M) (hP : P = 𝔞 • ⊤) (g₀ : (M ⧸ P) ≃ₗ[A] (M ⧸ P)) :
    ∃ (g : M →ₗ[A] M) (h : ℕ → (M →ₗ[A] M)), (∀ x, P.mkQ (g x) = g₀ (P.mkQ x)) ∧
      ∀ e x, g (h e x) - x ∈ (u ^ e • ⊤ : Submodule A M) ∧ h e (g x) - x ∈ (u ^ e • ⊤ : Submodule A M) := by
  subst hP
  exact liftUnit A M u 𝔞 hu hf g₀

theorem qSys : QSys := by
  intro q _ D hm r hr 𝔞 hf g₀
  obtain ⟨hbij, hproj, hfin⟩ := mOne q D hm
  obtain ⟨ε, hε⟩ := idem q D r hr
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI : Module.Finite (𝓞 D.F) D.O := Module.Finite.of_surjective (Algebra.linearMap _ _) hbij.2
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.trans D.O D.La
  haveI : Module.Projective (𝓞 D.F) D.La := by
    let ρ : D.O ≃+* 𝓞 D.F := (RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) hbij).symm
    letI i₁ : RingHomInvPair (ρ : D.O →+* 𝓞 D.F) (ρ.symm : 𝓞 D.F →+* D.O) := RingHomInvPair.of_ringEquiv ρ
    letI i₂ : RingHomInvPair (ρ.symm : 𝓞 D.F →+* D.O) (ρ : D.O →+* 𝓞 D.F) := RingHomInvPair.symm _ _
    let e₂ : D.La ≃ₛₗ[(ρ : D.O →+* 𝓞 D.F)] D.La :=
      { AddEquiv.refl D.La with
        map_smul' := fun c x => by
          change c • x = algebraMap (𝓞 D.F) D.O (ρ c) • x
          congr 1
          exact ((RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) hbij).apply_symm_apply c).symm }
    exact Module.Projective.of_equiv (σ' := (ρ.symm : 𝓞 D.F →+* D.O)) e₂
  have hbb : ∀ c, D.bar (D.bar c) = c := fun c => hbij.1 (by
    have := D.star_star (algebraMap _ _ c)
    rw [D.star_F, MulOpposite.unop_op, D.star_F, MulOpposite.unop_op] at this
    exact this)
  have adjA : ∀ (c : 𝓞 D.F) (x y : D.La), D.EF (c • x) y = D.EF x (D.bar c • y) := fun c x y => by
    have := D.adj (algebraMap _ _ c) x y
    rw [D.star_F, MulOpposite.unop_op] at this
    exact this
  have hP : (wSub D 𝔞 1).restrictScalars (𝓞 D.F) = 𝔞 • (⊤ : Submodule (𝓞 D.F) D.La) := by
    apply le_antisymm
    · intro x hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ ((Submodule.restrictScalars_mem _ _ _).1 hx)
      · rintro _ ⟨c, hc, z, rfl⟩
        exact Submodule.smul_mem_smul (by rwa [pow_one] at hc) Submodule.mem_top
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro b a _ ha
        obtain ⟨c, rfl⟩ := hbij.2 b
        exact Submodule.smul_mem _ c ha
    · refine Submodule.smul_le.2 fun c hc x _ => ?_
      exact Submodule.subset_span ⟨c, by rwa [pow_one], x, rfl⟩
  have hu : ES.uIdeal D r ≠ ⊥ := by
    intro h0
    have h1 := ES.p_mem_uIdeal D r
    rw [h0, Ideal.mem_bot] at h1
    exact (Fact.out : q.Prime).ne_zero (Nat.cast_eq_zero.1 h1)
  let e₀ := Submodule.Quotient.restrictScalarsEquiv (𝓞 D.F) (wSub D 𝔞 1)
  obtain ⟨g, h, hg, hgh⟩ := lift_of_eq (𝓞 D.F) D.La (ES.uIdeal D r) 𝔞 hu hf _ hP
    (e₀.trans ((g₀.restrictScalars (𝓞 D.F)).trans e₀.symm))
  have hg' : ∀ x, (wSub D 𝔞 1).mkQ (g x) = g₀ ((wSub D 𝔞 1).mkQ x) := fun x => by
    have he : ∀ y, e₀ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := fun _ => rfl
    have := congrArg e₀ (hg x)
    simpa [he] using this
  let hO : ℕ → (D.La →ₗ[D.O] D.La) := fun e =>
    { toFun := h e
      map_add' := map_add _
      map_smul' := fun c x => by
        obtain ⟨a, rfl⟩ := hbij.2 c
        exact map_smul (h e) a x }
  choose k hk hkl using fun e => (adj q D e).2.1 (hO e)
  have hcast : ∀ e : ℕ, ((q ^ e : ℕ) : 𝓞 D.F) = (q : 𝓞 D.F) ^ e := fun e => by push_cast; rfl
  refine ⟨fun e => AddMonoidHom.mk' (fun x => ε e • g x + D.bar (ε e) • k e x) fun x y => by
    simp only [map_add, smul_add]; abel, fun e => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hε e
  rw [← hcast] at h4 h5
  have h3' : ∀ x ∈ ES.uIdeal D r ^ e, ((q ^ e : ℕ) : 𝓞 D.F) ∣ ε e * x := fun x hx => by
    rw [hcast]; exact h3 x hx
  refine ⟨fun c x => ?_, fun x y => ?_, fun x => ?_, fun hq x => ?_⟩
  · obtain ⟨a, rfl⟩ := hbij.2 c
    exact lin_step (q ^ e) (ε e) (D.bar (ε e)) g (k e) a x (hkl e _ x)
  · exact iso_step D.bar D.EF hbb D.alt adjA (q ^ e) _ (ε e) g (h e) (k e) h1 h2 h3' h4
      (fun x => (hgh e x).2) (hk e) x y
  · exact tow_step D.bar D.EF D.alt hbb adjA (q ^ e) _ (ε e) (ε (e + 1)) g (h e) (h (e + 1)) (k e) (k (e + 1)) h3' h5
      (fun x => (hgh e x).2) (fun x => (hgh e x).1)
      (fun x => Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ e)) (hgh (e + 1) x).1)
      (hk e)
      (fun x y => dvd_trans (by exact_mod_cast pow_dvd_pow q (Nat.le_succ e)) (hk (e + 1) x y))
      (adj q D e).1 x
  · have hle := h6 𝔞 hf hq
    have hmem := lev_step 𝔞 (ε e) (D.bar (ε e)) (hle h1) (hle h2) (g x) (k e x)
    rw [← hP] at hmem
    rw [← hg' x]
    exact (Submodule.Quotient.eq _).2 hmem

end UpperTheory.Gal.FiniteEtaleModels.O
