import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

section Ip

variable (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_conj (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def ipL (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' := ip_add_right R x
  map_smul' c y := ip_smul_right R c x y

theorem ip_add_left (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  rw [← ip_conj R y, ip_add_right, map_add, ip_conj, ip_conj]

theorem ip_smul_left (c : ℂ) (x y : Fin g → ℂ) : R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  rw [← ip_conj R y, ip_smul_right, map_mul, ip_conj]

theorem ip_self_pos {x : Fin g → ℂ} (hx : x ≠ 0) : 0 < (R.ip x x).re := R.pos x hx

theorem ip_self_nonneg (x : Fin g → ℂ) : 0 ≤ (R.ip x x).re := by
  by_cases hx : x = 0
  · subst hx
    simp [RiemLat.ip]
  · exact (ip_self_pos R hx).le

theorem ip_self_eq_zero {x : Fin g → ℂ} (h : R.ip x x = 0) : x = 0 := by
  by_contra hx
  have := ip_self_pos R hx
  rw [h] at this
  simp at this

def TanSp (_ : RiemLat E g Λ) : Type := Fin g → ℂ

instance : AddCommGroup (TanSp R) := inferInstanceAs (AddCommGroup (Fin g → ℂ))

instance : Module ℂ (TanSp R) := inferInstanceAs (Module ℂ (Fin g → ℂ))

def core : InnerProductSpace.Core ℂ (TanSp R) where
  inner x y := R.ip x y
  conj_inner_symm x y := ip_conj R y x
  re_inner_nonneg x := ip_self_nonneg R x
  add_left x y z := ip_add_left R x y z
  smul_left x y r := ip_smul_left R r x y
  definite x h := ip_self_eq_zero R h

theorem ip_cs (x y : Fin g → ℂ) : ‖R.ip x y‖ ^ 2 ≤ (R.ip x x).re * (R.ip y y).re := by
  letI : NormedAddCommGroup (TanSp R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (TanSp R) := InnerProductSpace.ofCore (core R).toCore
  have h1 : ‖(inner ℂ (show TanSp R from x) (show TanSp R from y) : ℂ)‖ ≤ _ := norm_inner_le_norm _ _
  have h2 : (R.ip x x).re = ‖(show TanSp R from x)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (show TanSp R from x)
  have h3 : (R.ip y y).re = ‖(show TanSp R from y)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (show TanSp R from y)
  have h4 : R.ip x y = (inner ℂ (show TanSp R from x) (show TanSp R from y) : ℂ) := rfl
  rw [h2, h3, h4, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem exists_frame (S : Submodule ℂ (Fin g → ℂ)) (m : ℕ) (h : Module.finrank ℂ S = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ c, e c ∈ S) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∑ c, starRingEnd ℂ (R.ip (e c) x) * R.ip (e c) y = R.ip x y := by
  letI : NormedAddCommGroup (TanSp R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (TanSp R) := InnerProductSpace.ofCore (core R).toCore
  letI : FiniteDimensional ℂ (TanSp R) := inferInstanceAs (FiniteDimensional ℂ (Fin g → ℂ))
  let S' : Submodule ℂ (TanSp R) := S
  have h' : Module.finrank ℂ S' = m := h
  let b := (stdOrthonormalBasis ℂ S').reindex (finCongr h')
  refine ⟨fun c => ((b c : S') : TanSp R), fun c => (b c).2, fun x hx y hy => ?_⟩
  have key := b.sum_inner_mul_inner (⟨x, hx⟩ : S') (⟨y, hy⟩ : S')
  refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) key
  exact congrArg (· * R.ip (((b c : S') : TanSp R)) y) (ip_conj R (((b c : S') : TanSp R)) x)

end Ip

section Eig

variable (R : RiemLat E g Λ)

theorem ip_sum_right {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (x : Fin g → ℂ) :
    R.ip x (∑ i ∈ t, f i) = ∑ i ∈ t, R.ip x (f i) := map_sum (ipL R x) f t

theorem ip_sum_left {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (y : Fin g → ℂ) :
    R.ip (∑ i ∈ t, f i) y = ∑ i ∈ t, R.ip (f i) y := by
  rw [← ip_conj R y, ip_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => ip_conj R y (f i)

theorem mem_eigSp_iff' {s : 𝓞 E →+* ℂ} {x : Fin g → ℂ} : x ∈ eigSp R.B s ↔ ∀ a, R.B a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

omit [IsCMField E] in

theorem comp_ne {s s' : E →+* ℂ} (h : s ≠ s') :
    s.comp (algebraMap (𝓞 E) E) ≠ s'.comp (algebraMap (𝓞 E) E) :=
  fun e => h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e)

omit [IsCMField E] in

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

omit [IsCMField E] in
theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

omit [IsCMField E] in
theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

theorem ip_eig (s : E →+* ℂ) {x' : Fin g → ℂ} (hx' : x' ∈ eigSp R.B (s.comp (algebraMap (𝓞 E) E)))
    (x : Fin g → ℂ) : R.ip x' x = R.ip x' (eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x) := by
  obtain ⟨-, -, h3, h4, h5⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  conv_lhs => rw [← h4 x]
  rw [ip_sum_right, Finset.sum_eq_single s]
  · intro s' _ hs
    exact h5 _ _ (comp_ne hs.symm) _ hx' _ ((h3 _).1 x)
  · simp

theorem ip_self_sum (x : Fin g → ℂ) :
    R.ip x x = ∑ s : E →+* ℂ, R.ip (eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x)
      (eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x) := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  calc R.ip x x = R.ip (∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x) x := by rw [h4]
    _ = ∑ s : E →+* ℂ, R.ip (eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x) x := ip_sum_left R _ _ _
    _ = _ := Finset.sum_congr rfl fun s _ => ip_eig R s ((h3 _).1 x) x

theorem sum_ip_le {Ψ : Type} [Fintype Ψ] (emb : Ψ → (𝓞 E →+* ℂ)) (hemb : Function.Injective emb)
    (x : Fin g → ℂ) :
    ∑ τ, (R.ip (eigComp R.B (emb τ) x) (eigComp R.B (emb τ) x)).re ≤ (R.ip x x).re := by
  classical
  let sE : Ψ → (E →+* ℂ) := fun τ => extEmb (emb τ)
  have hsE : ∀ τ, (sE τ).comp (algebraMap (𝓞 E) E) = emb τ := fun τ => extEmb_comp (emb τ)
  have hinj : Function.Injective sE := fun a b h => hemb (by rw [← hsE, ← hsE, h])
  have e : ∑ τ, (R.ip (eigComp R.B (emb τ) x) (eigComp R.B (emb τ) x)).re =
      ∑ s ∈ Finset.univ.image sE, (R.ip (eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x)
        (eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x)).re := by
    rw [Finset.sum_image fun a _ b _ h => hinj h]
    exact Finset.sum_congr rfl fun τ _ => by rw [hsE]
  rw [e, ip_self_sum R x, Complex.re_sum]
  exact Finset.sum_le_univ_sum_of_nonneg fun s => ip_self_nonneg R _

open Classical in

def frame (s : 𝓞 E →+* ℂ) (m : ℕ) : Fin m → Fin g → ℂ :=
  if h : Module.finrank ℂ (eigSp R.B s) = m then (exists_frame R _ m h).choose else 0

theorem frame_parseval {s : 𝓞 E →+* ℂ} {m : ℕ} (h : Module.finrank ℂ (eigSp R.B s) = m)
    {x y : Fin g → ℂ} (hx : x ∈ eigSp R.B s) (hy : y ∈ eigSp R.B s) :
    ∑ c, starRingEnd ℂ (R.ip (frame R s m c) x) * R.ip (frame R s m c) y = R.ip x y := by
  rw [frame, dif_pos h]
  exact (exists_frame R _ m h).choose_spec.2 x hx y hy

def lieOf (s : 𝓞 E →+* ℂ) (m : ℕ) (v : Λ) : Fin m → ℂ :=
  fun c => R.ip (frame R s m c) (eigComp R.B s (R.P v))

theorem lieOf_add (s : 𝓞 E →+* ℂ) (m : ℕ) (v w : Λ) :
    lieOf R s m (v + w) = lieOf R s m v + lieOf R s m w := by
  obtain ⟨-, -, h3, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  funext c
  have h := (h3 s).2.2.1 1 (R.P v) (R.P w)
  rw [one_smul, one_smul] at h
  simp only [lieOf, map_add, h, ip_add_right, Pi.add_apply]

theorem lieOf_smul (s : 𝓞 E →+* ℂ) (m : ℕ) (a : 𝓞 E) (v : Λ) :
    lieOf R s m (a • v) = s a • lieOf R s m v := by
  obtain ⟨-, -, h3, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  funext c
  simp only [lieOf, R.act, (h3 s).2.2.2, ip_smul_right, Pi.smul_apply, smul_eq_mul]

theorem lieOf_gram {s : 𝓞 E →+* ℂ} {m : ℕ} (h : Module.finrank ℂ (eigSp R.B s) = m) (v v' : Λ) :
    star (lieOf R s m v) ⬝ᵥ lieOf R s m v' = R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P v')) := by
  obtain ⟨-, -, h3, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  exact frame_parseval R h ((h3 s).1 _) ((h3 s).1 _)

theorem lieOf_sq {s : 𝓞 E →+* ℂ} {m : ℕ} (h : Module.finrank ℂ (eigSp R.B s) = m) (v : Λ) :
    ∑ c, ‖lieOf R s m v c‖ ^ 2 = (R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P v))).re := by
  rw [← lieOf_gram R h v v]
  simp only [dotProduct, Pi.star_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

def lieL (s : 𝓞 E →+* ℂ) (m : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  LinearMap.pi fun c => ipL R (frame R s m c)

theorem lieOf_linInd {s : 𝓞 E →+* ℂ} {m : ℕ} (h : Module.finrank ℂ (eigSp R.B s) = m) {ρ : ℕ}
    (v : Fin ρ → Λ) (hl : LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a))) :
    LinearIndependent ℂ fun a => lieOf R s m (v a) := by
  obtain ⟨-, -, h3, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  refine hl.map (f := lieL R s m) ?_
  rw [Submodule.disjoint_def]
  intro x hx hk
  have hxS : x ∈ eigSp R.B s :=
    (Submodule.span_le (p := eigSp R.B s)).2 (by rintro _ ⟨a, rfl⟩; exact (h3 s).1 _) hx
  have hz : ∀ c, R.ip (frame R s m c) x = 0 := fun c => congrFun (LinearMap.mem_ker.1 hk) c
  have hp := frame_parseval R h hxS hxS
  simp only [hz, mul_zero, Finset.sum_const_zero] at hp
  exact ip_self_eq_zero R hp.symm

end Eig

theorem gram_unit {F₀ : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ} (h : Function.Bijective F₀) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Λ) : IsUnit (Matrix.of fun a c => F₀ (b a) (b c)).det := by
  have hu := LinearEquiv.isUnit_det (LinearEquiv.ofBijective F₀ h) b b.dualBasis
  have e : LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective F₀ h : Λ →ₗ[ℤ] (Λ →ₗ[ℤ] ℤ)) =
      (Matrix.of fun a c => F₀ (b a) (b c))ᵀ := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [e, Matrix.det_transpose] at hu
  exact hu

section Family

variable {K : Type} {J : K → Type} {Ψ : Type}

open Classical in

def normFam (T : Set ((Σ k, J k) → ℂ)) (R : ((Σ k, J k) → ℂ) → RiemLat E g Λ) (w : (Σ k, J k) → ℂ) (v : Λ) : ℝ :=
  if w ∈ T then (R w).normSq v else 0

open Classical in

def lieFam (T : Set ((Σ k, J k) → ℂ)) (R : ((Σ k, J k) → ℂ) → RiemLat E g Λ) (emb : Ψ → (𝓞 E →+* ℂ)) (m : ℕ)
    (w : (Σ k, J k) → ℂ) (τ : Ψ) (v : Λ) : Fin m → ℂ :=
  if w ∈ T then lieOf (R w) (emb τ) m v else 0

variable {T : Set ((Σ k, J k) → ℂ)} {R : ((Σ k, J k) → ℂ) → RiemLat E g Λ} {w : (Σ k, J k) → ℂ}

theorem normFam_of_mem (h : w ∈ T) : normFam T R w = (R w).normSq := by
  funext v
  simp [normFam, h]

theorem lieFam_of_mem (emb : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (h : w ∈ T) (τ : Ψ) :
    lieFam T R emb m w τ = lieOf (R w) (emb τ) m := by
  funext v
  simp [lieFam, h]

theorem lieFam_add (emb : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (w : (Σ k, J k) → ℂ) (τ : Ψ) (v v' : Λ) :
    lieFam T R emb m w τ (v + v') = lieFam T R emb m w τ v + lieFam T R emb m w τ v' := by
  by_cases h : w ∈ T
  · rw [lieFam_of_mem emb m h]
    exact lieOf_add _ _ _ _ _
  · simp [lieFam, h]

theorem lieFam_smul (emb : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (w : (Σ k, J k) → ℂ) (τ : Ψ) (a : 𝓞 E) (v : Λ) :
    lieFam T R emb m w τ (a • v) = emb τ a • lieFam T R emb m w τ v := by
  by_cases h : w ∈ T
  · rw [lieFam_of_mem emb m h]
    exact lieOf_smul _ _ _ _ _
  · simp [lieFam, h]

theorem form_sq_le (R : RiemLat E g Λ) (v v' : Λ) :
    ((R.form v v' : ℤ) : ℝ) ^ 2 ≤ R.normSq v * R.normSq v' := by
  have h := R.im v v'
  have cs := ip_cs R (R.P v') (R.P v)
  have e : R.P v ⬝ᵥ R.Hm *ᵥ star (R.P v') = R.ip (R.P v') (R.P v) := rfl
  rw [e] at h
  rw [← h]
  have h2 : (R.ip (R.P v') (R.P v)).im ^ 2 ≤ ‖R.ip (R.P v') (R.P v)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [mul_self_nonneg (R.ip (R.P v') (R.P v)).re]
  have e2 : R.normSq v * R.normSq v' = (R.ip (R.P v') (R.P v')).re * (R.ip (R.P v) (R.P v)).re := mul_comm _ _
  rw [e2]
  exact h2.trans cs

theorem normSq_pos' (R : RiemLat E g Λ) {v : Λ} (hv : v ≠ 0) : 0 < R.normSq v := by
  obtain ⟨h1, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  exact R.pos (R.P v) fun h0 => hv (h1 (by rw [h0, map_zero]))

theorem sum_lie_le [Fintype Ψ] (R : RiemLat E g Λ) (emb : Ψ → (𝓞 E →+* ℂ)) (hemb : Function.Injective emb) {m : ℕ}
    (hrk : ∀ τ, Module.finrank ℂ (eigSp R.B (emb τ)) = m) (v : Λ) :
    ∑ τ, ∑ c, ‖lieOf R (emb τ) m v c‖ ^ 2 ≤ R.normSq v := by
  simp only [fun τ => lieOf_sq R (hrk τ) v]
  exact sum_ip_le R emb hemb (R.P v)

end Family

theorem cuspData_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (V : Ψ → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (Dc : ComponentData II Ψ K J Ω V) (T : Set ((Σ k, J k) → ℂ)) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F₀ : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (emb : Ψ → (𝓞 E →+* ℂ)) (R : ((Σ k, J k) → ℂ) → RiemLat E g Λ), T.Nonempty → Function.Injective emb → (∀ w ∈ T, (R w).form = F₀) → (∀ w ∈ T, ∀ τ, Module.finrank ℂ (eigSp (R w).B (emb τ)) = Dc.N - Dc.j) → (∀ w ∈ T, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c w ∈ T ∧ R (torusSmul c w) = R w) → ∃ C : CuspDataOn Dc T (𝓞 E) Λ, C.emb = emb ∧ ∀ w ∈ T, Origin.IsPeriodAt C w (R w).P (R w).Hm (fun a => LinearMap.toMatrix' ((R w).B a)) := by
  intro E _ _ _ II Ψ _ K _ J _ Ω _ _ V _ _ Dc T g Λ _ _ F₀ emb R hT hemb hform hrk htor
  obtain ⟨w₀, hw₀⟩ := hT
  haveI := (R w₀).free
  haveI := (R w₀).fin
  have hbij : Function.Bijective F₀ := hform w₀ hw₀ ▸ (R w₀).unimod
  have halt : ∀ v, F₀ v v = 0 := hform w₀ hw₀ ▸ (R w₀).alt
  refine ⟨{
    rank := Module.finrank ℤ Λ
    basis := Module.finBasis ℤ Λ
    form := F₀
    alt := halt
    unimod := gram_unit hbij _
    emb := emb
    normSq := normFam T R
    normSq_pos := fun z hz v hv => by
      rw [normFam_of_mem hz]
      exact normSq_pos' _ hv
    form_le := fun z hz v v' => by
      rw [normFam_of_mem hz, ← hform z hz]
      exact form_sq_le _ v v'
    lie := lieFam T R emb (Dc.N - Dc.j)
    lie_add := fun z τ v v' => lieFam_add emb _ z τ v v'
    lie_smul := fun z τ a v => lieFam_smul emb _ z τ a v
    lie_le := fun z hz v => by
      rw [normFam_of_mem hz]
      simp only [lieFam_of_mem emb _ hz]
      exact sum_lie_le _ emb hemb (hrk z hz) v
    inj := fun z hz τ I hI ρ v hv hli => by
      simp only [lieFam_of_mem emb _ hz]
      have hI' : IsIsoSub (R z).form I := by rw [hform z hz]; exact hI
      exact lieOf_linInd _ (hrk z hz τ) v ((GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Unit (R z) I hI' (emb τ)).2 ρ v hv hli)
    torus := fun z hz c hc => by
      obtain ⟨h1, h2⟩ := htor z hz c hc
      refine ⟨?_, ?_⟩
      · rw [normFam_of_mem h1, normFam_of_mem hz, h2]
      · funext τ
        rw [lieFam_of_mem emb _ h1, lieFam_of_mem emb _ hz, h2] }, rfl, fun w hw => ?_⟩
  obtain ⟨-, -, h3, -, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit (R w)
  refine ⟨fun a v => ?_, fun v => ?_, fun v v' => ?_, fun τ => eigComp (R w).B (emb τ),
    fun τ x => ⟨fun a => ?_, fun x' hx' => ?_⟩, fun τ v v' => ?_⟩
  · rw [(R w).act, LinearMap.toMatrix'_mulVec]
  · show normFam T R w v = _
    rw [normFam_of_mem hw]
    rfl
  · show ((F₀ v v' : ℤ) : ℝ) = _
    rw [← hform w hw]
    exact ((R w).im v v').symm
  · rw [LinearMap.toMatrix'_mulVec]
    exact (mem_eigSp_iff' (R w)).1 ((h3 _).1 x) a
  · have hx'' : x' ∈ eigSp (R w).B (emb τ) := (mem_eigSp_iff' (R w)).2 fun a => by
      have := hx' a
      rwa [LinearMap.toMatrix'_mulVec] at this
    rw [← extEmb_comp (emb τ)] at hx''
    have key := ip_eig (R w) (extEmb (emb τ)) hx'' x
    rw [extEmb_comp] at key
    show ipL (R w) x' (x - eigComp (R w).B (emb τ) x) = 0
    rw [map_sub, sub_eq_zero]
    exact key
  · show star (lieFam T R emb (Dc.N - Dc.j) w τ v) ⬝ᵥ lieFam T R emb (Dc.N - Dc.j) w τ v' = _
    rw [lieFam_of_mem emb _ hw]
    exact lieOf_gram (R w) (hrk w hw τ) v v'

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin
