import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]

def latOn (D : HTChart A K c p R N (Module.Dual K Li)) (V : Submodule K Li) (t : K) (B : Subring K) : Set Li :=
  {e | e ∈ V ∧ ∀ w ∈ D.om', t * w e ∈ B}

def IsLocIn (A : Type) {K : Type} [CommRing A] [Field K] [Algebra A K] (B : Subring K) : Prop :=
  (∀ a : A, algebraMap A K a ∈ B) ∧
    ∀ b ∈ B, ∃ u a : A, algebraMap A K u ≠ 0 ∧ (algebraMap A K u)⁻¹ ∈ B ∧ algebraMap A K u * b = algebraMap A K a

end
end GlobalTheory.CompanionTheory.Ar.Flat.HTL

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem exists_extend_lin {A K V W : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W]
    (M : Submodule A V) (g : M →ₗ[A] W) : ∃ G : V →ₗ[K] W, ∀ z : M, G z = g z := by
  classical
  obtain ⟨b, hbM, -, hsp, hli⟩ := exists_linearIndepOn_id_extension (K := K) (s := ∅) (t := (M : Set V)) (by simp) (by simp)
  let bb := Basis.extend hli
  let f : V → W := fun x => if h : x ∈ M then g ⟨x, h⟩ else 0
  let G : V →ₗ[K] W := bb.constr K fun i => f i.1
  have hGb : ∀ x ∈ b, G x = f x := fun x hx => by
    have hx' : x ∈ hli.extend (Set.subset_univ b) := hli.subset_extend _ hx
    have := bb.constr_basis K (fun i => f i.1) ⟨x, hx'⟩
    simpa [bb, G, Basis.extend_apply_self] using this
  have hG : ∀ x (hx : x ∈ Submodule.span A b) (h : x ∈ M), G x = g ⟨x, h⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro h
      rw [hGb x hx]
      simp [f, h]
    | zero =>
      intro h
      have : (⟨0, h⟩ : M) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have h2 : y ∈ M := Submodule.span_le.2 hbM hy
      have : (⟨x + y, h⟩ : M) = ⟨x, h1⟩ + ⟨y, h2⟩ := rfl
      rw [map_add, ihx h1, ihy h2, this, map_add]
    | smul a x hx ih =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have : (⟨a • x, h⟩ : M) = a • ⟨x, h1⟩ := rfl
      rw [this, g.map_smul, ← ih h1, LinearMap.map_smul_of_tower]
  have hden : ∀ v ∈ Submodule.span K b, ∃ a : A, algebraMap A K a ≠ 0 ∧ a • v ∈ Submodule.span A b := by
    intro v hv
    have hinj := IsFractionRing.injective A K
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simp, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨a', ha', hy⟩ := hy
      refine ⟨a * a', by rw [map_mul]; exact mul_ne_zero ha ha', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul r x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) r
      have hv0 : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hv)
      refine ⟨v * a, by rw [map_mul]; exact mul_ne_zero hv0 ha, ?_⟩
      have : (v * a) • (algebraMap A K u / algebraMap A K v) • x = u • a • x := by
        rw [← algebraMap_smul K (v * a), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact Submodule.smul_mem _ _ hx
  refine ⟨G, fun z => ?_⟩
  obtain ⟨a, ha, haz⟩ := hden z (hsp z.2)
  have h1 := hG _ haz (M.smul_mem a z.2)
  have h2 : (⟨a • (z : V), M.smul_mem a z.2⟩ : M) = a • z := rfl
  rw [h2, g.map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K a (G (z : V)), ← algebraMap_smul K a (g z)] at h1
  exact smul_right_injective W ha h1

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]
  (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li)

theorem eigProj_dual (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w = w ∘ₗ eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ := by
  ext v
  simp [eigProj, LinearMap.sum_apply, hact]

theorem eigProj_apply (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w e = w e := by
  rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
  congr 1
  have h1 : ∀ a : 𝓞 E, ρ (RingOfIntegers.mapRingEquiv c a) e = σ (a : E) • e := fun a => by
    rw [LatBasic.mem_eigSp.1 he]
    simp [hc]
  have h2 : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ e = e := by
    apply LatBasic.eigProj_of_mem
    rw [LatBasic.mem_eigSp]
    exact fun a => h1 a
  exact h2

theorem exists_vec [IsDomain A] [IsFractionRing A K] (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (g : Module.Dual A (D.omHT σ)) :
    ∃ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom), ∀ z : D.omHT σ,
      (z : Module.Dual K Li) e = algebraMap A K (g z) := by
  haveI : Module.Finite K (Module.Dual K Li) := by
    obtain ⟨S, hS⟩ := D.om_lat.fg
    refine ⟨⟨S, ?_⟩⟩
    rw [← D.om_lat.span_eq_top, ← hS, Submodule.span_span_of_tower]
  haveI : Module.Finite K Li := (Module.finite_dual_iff K).1 inferInstance
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) (D.omHT σ) ((Algebra.linearMap A K) ∘ₗ g)
  let v : Li := (Module.evalEquiv K Li).symm G
  have hv : ∀ w : Module.Dual K Li, w v = G w := fun w => by
    simpa [v] using Module.apply_evalEquiv_symm_apply w G
  refine ⟨eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v, ?_, ?_⟩
  · have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
    rw [LatBasic.mem_eigSp] at h ⊢
    intro a
    have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      apply RingOfIntegers.ext
      simp [hc]
    have := h (RingOfIntegers.mapRingEquiv c a)
    simpa [hinv] using this
  · intro z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = (z : Module.Dual K Li) := hz
    have he : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
      rw [LatBasic.mem_eigSp] at h ⊢
      intro a
      have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
        apply RingOfIntegers.ext
        simp [hc]
      have := h (RingOfIntegers.mapRingEquiv c a)
      simpa [hinv] using this
    rw [← hz', eigProj_apply D ρ hc hact σ he w]
    have h2 : w (eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v) = (eigProj D.ρΩ σ w) v := by
      rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
    rw [h2, hz', hv, hG z]
    rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
