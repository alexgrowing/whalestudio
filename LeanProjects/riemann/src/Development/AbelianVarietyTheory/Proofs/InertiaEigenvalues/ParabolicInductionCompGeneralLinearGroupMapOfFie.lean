import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil Matrix

namespace GlobalTheory.IndField

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

section Gen

variable {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁] [IsNonarchimedeanLocalField K₁]
  [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂] [IsNonarchimedeanLocalField K₂]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullFun (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L) :
    IndSp e ρ₁ →ₗ[ℂ] IndSp e ρ₂ where
  toFun f := ⟨⟨fun x => f.1.1 (s x), fun p g => by
      show f.1.1 (s ((p : GL n K₂) * g)) =
        (deltaHalf K₂ m (leviProj K₂ e p) : ℂ) • ρ₂ (leviProj K₂ e p) (f.1.1 (s g))
      rw [map_mul, parInd_law e ρ₁ f ⟨s p, hP p⟩ (s g), hL, hδ, hρ]⟩, by
      apply mem_smoothPart_of_nhds
      have h1 : s ⁻¹' {g | ind (parab K₁ e) ((twist ρ₁ (deltaHalf K₁ m)).comp (leviProj K₁ e)) g f.1 = f.1}
          ∈ nhds (1 : GL n K₂) :=
        (f.2.preimage hs).mem_nhds (by simp)
      refine Filter.mem_of_superset h1 fun x hx => ?_
      refine Subtype.ext (funext fun y => ?_)
      show f.1.1 (s (y * x)) = f.1.1 (s y)
      rw [map_mul]
      exact congrArg (fun v : indSpace (parab K₁ e) ((twist ρ₁ (deltaHalf K₁ m)).comp (leviProj K₁ e)) =>
        (v : GL n K₁ → W) (s y)) hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullFun_apply (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L)
    (f : IndSp e ρ₁) (x : GL n K₂) :
    (pullFun e s hs t hP hL hρ hδ f).1.1 x = f.1.1 (s x) := rfl

end Gen

section Gen2

variable {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁] [IsNonarchimedeanLocalField K₁]
  [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂] [IsNonarchimedeanLocalField K₂]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullMap (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L) :
    Representation.IntertwiningMap ((parInd e ρ₁).comp s) (parInd e ρ₂) :=
  ⟨pullFun e s hs t hP hL hρ hδ, fun g => LinearMap.ext fun f =>
    Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (s x * s g) = f.1.1 (s (x * g))
      rw [map_mul]))⟩

end Gen2

section Map

variable {R S : Type} [CommRing R] [CommRing S]

def blockMap (φ : R →+* S) : Levi R m →* Levi S m :=
  MonoidHom.pi fun a => (GeneralLinearGroup.map φ).comp (Pi.evalMonoidHom (fun a => GL (m a) R) a)

@[simp] theorem blockMap_apply (φ : R →+* S) (L : Levi R m) (a : α) :
    blockMap φ L a = GeneralLinearGroup.map φ (L a) := rfl

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem map_mem_parab (e : (Σ a, m a) ≃ n) (φ : R →+* S) (p : parab R e) :
    GeneralLinearGroup.map φ (p : GL n R) ∈ parab S e :=
  mem_parab.2 fun i j h => by
    rw [GeneralLinearGroup.map_apply, mem_parab.1 p.2 i j h, map_zero]

theorem leviProj_map (e : (Σ a, m a) ≃ n) (φ : R →+* S) (p : parab R e) :
    leviProj S e ⟨GeneralLinearGroup.map φ (p : GL n R), map_mem_parab e φ p⟩ =
      blockMap φ (leviProj R e p) :=
  funext fun _ => Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem continuous_glMap [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →+* S) (hφ : Continuous φ) : Continuous (GeneralLinearGroup.map (n := n) φ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hφ : Continuous fun g : GL n R => (g : Matrix n n R).map φ)
  · have : (fun g : GL n R => (((GeneralLinearGroup.map φ g)⁻¹ : GL n S) : Matrix n n S)) =
        fun g => ((g⁻¹ : GL n R) : Matrix n n R).map φ := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map hφ

end Map

theorem deltaHalf_blockMap {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsNonarchimedeanLocalField K₁] [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsNonarchimedeanLocalField K₂] (φ : K₂ →+* K₁)
    (hn : ∀ y : K₂ˣ, nabs K₁ (Units.map φ.toMonoidHom y) = nabs K₂ y) (L : Levi K₂ m) :
    deltaHalf K₁ m (blockMap φ L) = deltaHalf K₂ m L := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => Units.ext ?_
  rw [val_absPow, val_absPow, blockMap_apply, GeneralLinearGroup.map_det]
  exact congrArg (fun r : ℝ => ((r : ℂ)) ^ _) (hn _)

theorem multiProd_comp_glMap : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → (∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x) → ∀ {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.multiProd e σ).comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) (GlobalTheory.SmGL.multiProd e fun a => (σ a).comp (Matrix.GeneralLinearGroup.map (n := m a) i.symm.toRingHom))) := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' hn α n m _ _ _ _ _ _ e X _ _ σ
  have hn' : ∀ y : k'ˣ, nabs k (Units.map i.symm.toRingHom.toMonoidHom y) = nabs k' y := fun y => by
    have h := hn (Units.map i.symm.toRingHom.toMonoidHom y)
    rw [show Units.map i.toRingHom.toMonoidHom (Units.map i.symm.toRingHom.toMonoidHom y) = y from
      Units.ext (by simp)] at h
    exact h.symm
  let Φ := pullMap e (ρ₁ := piTensor σ) (ρ₂ := piTensor fun a => (σ a).comp
      (GeneralLinearGroup.map (n := m a) i.symm.toRingHom))
    (GeneralLinearGroup.map i.symm.toRingHom) (continuous_glMap _ hi')
    (blockMap i.symm.toRingHom) (fun p => map_mem_parab e _ p) (fun p => leviProj_map e _ p)
    (fun _ => rfl) (fun L => deltaHalf_blockMap _ hn' L)
  let Ψ := pullFun e (ρ₁ := piTensor fun a => (σ a).comp
      (GeneralLinearGroup.map (n := m a) i.symm.toRingHom)) (ρ₂ := piTensor σ)
    (GeneralLinearGroup.map i.toRingHom) (continuous_glMap _ hi)
    (blockMap i.toRingHom) (fun p => map_mem_parab e _ p) (fun p => leviProj_map e _ p)
    (fun L => by
      show piTensor σ L = piTensor σ (fun a => GeneralLinearGroup.map i.symm.toRingHom
        (GeneralLinearGroup.map i.toRingHom (L a)))
      congr 1
      funext a
      ext
      simp) (fun L => deltaHalf_blockMap _ hn L)
  refine ⟨GlobalTheory.LocGL.equivOfBijective Φ (Function.bijective_iff_has_inverse.2 ⟨Ψ, fun f => ?_, fun f => ?_⟩)⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom x)) = f.1.1 x
    rw [show GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom x) = x from
      Matrix.GeneralLinearGroup.ext fun _ _ => by simp]
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom x)) = f.1.1 x
    rw [show GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom x) = x from
      Matrix.GeneralLinearGroup.ext fun _ _ => by simp]

end GlobalTheory.IndField
