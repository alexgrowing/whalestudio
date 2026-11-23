import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

section Mat

variable {R : Type} [CommRing R]

def uQ (x y t : R) : M4 R := !![1, 0, 0, 0; x, 1, 0, 0; y, 0, 1, 0; t, y, -x, 1]

theorem uQ_mul (x y t x' y' t' : R) : uQ x y t * uQ x' y' t' = uQ (x + x') (y + y') (t + y * x' - x * y' + t') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uQ, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem uQ_zero : uQ (0 : R) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uQ]

theorem adj_uQ (x y t : R) : adj (uQ x y t) = uQ (-x) (-y) (-t) := by
  ext i j
  rw [adj_apply]
  fin_cases i <;> fin_cases j <;> simp [uQ, sgn, Fin.rev] <;> ring

theorem isLow_uQ (x y t : R) : IsLow (uQ x y t) := by
  refine ⟨?_, fun i => by fin_cases i <;> rfl, fun i j hij => ?_⟩
  · rw [IsGSp, adj_uQ, uQ_mul, one_smul]
    convert uQ_zero (R := R) using 2 <;> ring
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)

theorem suppM_uQ (x y t : R) : SuppM qQ (uQ x y t) := by
  intro i j h1 h2
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl h1 | exact absurd (by decide) h2

theorem diag_mul_uQ (d : Fin 4 → R) (ρ σ : R) (h1 : d 1 = ρ * d 0) (h2 : d 2 = σ * d 0) (h3 : d 3 = ρ * σ * d 0) (x y t : R) :
    Matrix.diagonal d * uQ x y t = uQ (ρ * x) (σ * y) (ρ * σ * t) * Matrix.diagonal d := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [uQ, h1, h2, h3] <;> ring

end Mat

namespace Fr

variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)

abbrev wN (N : Set Γ) : Fr O Γ := { Φ with N := N }

theorem rt_add (w w' : ℤ × ℤ) (g : Γ) : Φ.rt (w + w') g = Φ.rt w g * Φ.rt w' g := by
  simp only [rt, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_add, Prod.snd_add, zpow_add]
  ac_rfl

variable [TopologicalSpace Γ]

structure Coc (w : ℤ × ℤ) (x : Γ → R) : Prop where
  lc : IsLocallyConstant x
  coc : ∀ g h, x (g * h) = x g + a (Φ.rt w g) * x h
  kill : ∀ g ∈ Φ.N, x g = 0

structure Cup (w w' : ℤ × ℤ) (x y z : Γ → R) (m : Φ.ι → R) : Prop where
  lc : IsLocallyConstant z
  coc : ∀ g h, z (g * h) = z g + a (Φ.rt (w + w') g) * z h + y g * a (Φ.rt w g) * x h
  kill : ∀ g ∈ Φ.N, z g = 0
  loc : ∀ v, ∃ o, ∀ s ∈ Φ.Gv v, z s = o - a (Φ.rt (w + w') s) * o - y s * a (Φ.rt w s) * m v

example (w w' : ℤ × ℤ) : Φ.Cup a w w' 0 0 0 0 :=
  ⟨IsLocallyConstant.const 0, by simp, by simp, fun _ => ⟨0, by simp⟩⟩

def Gys (l : ℕ) (𝒩 : Set Γ → Prop) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ 1)) Γ M), ContAction ρ → (∀ g ∈ Φ.N, ρ g = 1) → ∀ m0 : M, m0 ≠ 0 →
    ∃ N', 𝒩 N' ∧ ∃ c ∈ Z1 ρ, (∀ g ∈ N', c g = 0) ∧ (∀ v, ∃ m, ∀ s ∈ Φ.Gv v, c s = ρ s m - m) ∧
      ∃ g, ρ g = 1 ∧ c g ≠ 0 ∧ c g ∈ Submodule.span (ZMod (l ^ 1)) {m0}

end Fr

def ramLine {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation R D M) (I : Subgroup D) (m0 : M) : Submodule R (H1 ρ) :=
  (⨅ g ∈ I, (Submodule.span R {m0}).comap ((LinearMap.proj g : (D → M) →ₗ[R] M).comp (Z1 ρ).subtype)).map (Submodule.mkQ _)

theorem mem_ramLine {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation R D M) (I : Subgroup D) (m0 : M) (x : H1 ρ) :
    x ∈ ramLine ρ I m0 ↔ ∃ f : Z1 ρ, (∀ g ∈ I, f.1 g ∈ Submodule.span R {m0}) ∧ Submodule.Quotient.mk f = x := by
  unfold ramLine
  rw [Submodule.mem_map]
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.proj_apply, Submodule.mkQ_apply]

section Glob

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]

def UnrOut (ρ : Representation R (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ v ∉ S, ∀ A, IsPlaceOver A v → ∀ g ∈ Ine (F := F) A, ρ g = 1

def Zunr (ρ : Representation R (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (G F Ω → M) :=
  {c | c ∈ Z1 ρ ∧ ∀ v ∉ S, ∀ A, IsPlaceOver A v → ∀ g ∈ Ine (F := F) A, c g = 0}

def TrivAt (l : ℕ) [Fact l.Prime] (ρ : Representation R (G F Ω) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ A, IsPlaceOver A v → ∀ g ∈ Dec (F := F) A, ρ g = 1 ∧ cycMod F Ω l 1 g = 1

open Classical in

def gysL (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (Av : S → ValuationSubring Ω) (m0 : M) : LocCond ρ (locFam S Av) := fun v =>
  if v.1 ∈ S₀ then ⊥ else ramLine (ρ.comp (locFam S Av v)) ((Ine (F := F) (Av v)).subgroupOf (Dec (F := F) (Av v))) m0

abbrev gysSel (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (Av : S → ValuationSubring Ω) (m0 : M) : Submodule R (H1 ρ) :=
  Sel ρ (locFam S Av) (continuous_locFam S Av) (gysL S₀ S ρ Av m0)

end Glob

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : UpperTheory.V.HV.Coef l}

def Tower.Next {D : Raw Ω c} (T : Tower D) (W : Finset ℕ) (N : Set (G T.F Ω)) : Prop :=
  ∃ W' : Finset ℕ, W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ N = (T.fr W').N

theorem Tower.Next.sub {D : Raw Ω c} {T : Tower D} {W : Finset ℕ} {N : Set (G T.F Ω)} (h : T.Next W N) : N ⊆ (T.fr W).N := by
  obtain ⟨W', h1, -, rfl⟩ := h
  rintro g ⟨A, hA, hg⟩
  exact ⟨A, fun p hp => hA p (Finset.insert_subset_insert _ h1 hp), hg⟩

end UpperTheory.V.Ws

end
