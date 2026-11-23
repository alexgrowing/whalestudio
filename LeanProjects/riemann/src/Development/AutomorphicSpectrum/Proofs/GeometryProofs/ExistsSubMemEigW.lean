import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

open Module

section Map

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

def vmap (f : R →+* S) (y : (Fin d → R) × (Fin d → R)) : (Fin d → S) × (Fin d → S) :=
  (fun i => f (y.1 i), fun i => f (y.2 i))

theorem vmap_add (f : R →+* S) (y y' : (Fin d → R) × (Fin d → R)) :
    vmap f (y + y') = vmap f y + vmap f y' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_sub (f : R →+* S) (y y' : (Fin d → R) × (Fin d → R)) :
    vmap f (y - y') = vmap f y - vmap f y' := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_zero (f : R →+* S) : vmap f (0 : (Fin d → R) × (Fin d → R)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_smul (f : R →+* S) (c : R) (y : (Fin d → R) × (Fin d → R)) :
    vmap f (c • y) = f c • vmap f y := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [vmap]

theorem vmap_sum {A : Type} (s : Finset A) (f : R →+* S) (y : A → (Fin d → R) × (Fin d → R)) :
    vmap f (∑ i ∈ s, y i) = ∑ i ∈ s, vmap f (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vmap_zero f
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, vmap_add, ih]

theorem vmap_comp {T : Type} [CommRing T] (f : R →+* S) (g : S →+* T) (y : (Fin d → R) × (Fin d → R)) :
    vmap g (vmap f y) = vmap (g.comp f) y := rfl

theorem lin_map (f : R →+* S) (φ : Germ.Pt R 1 d) (m : ℕ) :
    lin (fun i => MvPowerSeries.map f (φ i)) m = (lin φ m).map f := by
  ext i j
  simp [lin, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem bil_map (f : R →+* S) (g : Germ.PS R 2 d) (m n : ℕ) :
    bil (MvPowerSeries.map f g) m n = (bil g m n).map f := by
  ext i j
  simp [bil, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem map_mulVec' (f : R →+* S) (M : Matrix (Fin d) (Fin d) R) (v : Fin d → R) :
    (fun i => f (M.mulVec v i)) = (M.map f).mulVec fun i => f (v i) :=
  funext fun i => RingHom.map_mulVec _ _ _ _

theorem vmap_transH (f : R →+* S) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d)
    (y : (Fin d → R) × (Fin d → R)) :
    vmap f (transH φ ψ lam y) = transH (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i))
      (MvPowerSeries.map f lam) (vmap f y) := by
  rw [transH_apply, transH_apply, lin_map, lin_map, bil_map]
  refine Prod.ext ?_ ?_
  · exact map_mulVec' f _ _
  · have h1 := map_mulVec' f (lin ψ 1).transpose (y.2 + (bil lam 1 1).transpose.mulVec y.1)
    have h2 := map_mulVec' f (bil lam 1 1).transpose y.1
    change (fun i => f ((lin ψ 1).transpose.mulVec (y.2 + (bil lam 1 1).transpose.mulVec y.1) i)) = _
    rw [h1, Matrix.transpose_map]
    congr 1
    change _ = (fun i => f (y.2 i)) + ((bil lam 1 1).map f).transpose.mulVec fun i => f (y.1 i)
    rw [← Matrix.transpose_map, ← h2]
    funext i
    simp

variable {O : Type} [CommRing O] [StarRing O]

theorem rho_map {f : R →+* S} {B : Germ.FB R d O} {B₂ : Germ.FB S d O} (h : IsMapOf f B B₂) (a : O) :
    rho B₂ a = (rho B a).map f := by
  have : B₂.A.act a = fun i => MvPowerSeries.map f (B.A.act a i) := funext (h.act a)
  rw [rho, this, lin_map]
  rfl

theorem vmap_rhoH {f : R →+* S} {B : Germ.FB R d O} {B₂ : Germ.FB S d O} (h : IsMapOf f B B₂) (a : O)
    (y : (Fin d → R) × (Fin d → R)) : vmap f (rhoH B a y) = rhoH B₂ a (vmap f y) := by
  rw [rhoH_apply, rhoH_apply, rho_map h, rho_map h, h.ad, bil_map]
  refine Prod.ext ?_ ?_
  · exact map_mulVec' f _ _
  · have h1 := map_mulVec' f (rho B (star a)).transpose y.2
    have h2 := map_mulVec' f (bil (B.ad a) 1 1).transpose y.1
    rw [Matrix.transpose_map] at h1 h2
    change (fun i => f (((rho B (star a)).transpose.mulVec y.2 - (bil (B.ad a) 1 1).transpose.mulVec y.1) i)) = _
    change _ = ((rho B (star a)).map f).transpose.mulVec (fun i => f (y.2 i)) -
      ((bil (B.ad a) 1 1).map f).transpose.mulVec fun i => f (y.1 i)
    rw [← Matrix.transpose_map, ← Matrix.transpose_map] at *
    rw [← h1, ← h2]
    funext i
    simp

end Map

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

section H

variable {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]

def IsHBasis {R : Type} [CommRing R] {d r : ℕ} (B : Germ.FB R d (𝓞 E))
    (x : Fin r → (Fin d → R) × (Fin d → R)) : Prop :=
  LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) = ⊤

def eigW {R : Type} [CommRing R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (τ : 𝓞 E →+* R) :
    Submodule R ((Fin d → R) × (Fin d → R)) :=
  ⨆ a : 𝓞 E, LinearMap.range (rhoH B a - τ a • LinearMap.id)

theorem vmap_mem_eigW {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {f : R →+* S} {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB S d (𝓞 E)} (h : IsMapOf f B B₂) (τ : 𝓞 E →+* R) {y : (Fin d → R) × (Fin d → R)}
    (hy : y ∈ eigW B τ) : vmap f y ∈ eigW B₂ (f.comp τ) := by
  refine Submodule.iSup_induction (motive := fun y => vmap f y ∈ eigW B₂ (f.comp τ)) _ hy ?_ ?_ ?_
  · rintro a _ ⟨w, rfl⟩
    refine Submodule.mem_iSup_of_mem a ⟨vmap f w, ?_⟩
    simp [vmap_sub, vmap_smul, vmap_rhoH h]
  · simp [vmap_zero]
  · intro y y' h1 h2
    rw [vmap_add]
    exact add_mem h1 h2

theorem eigW_induction {R : Type} [CommRing R] {d : ℕ} {B : Germ.FB R d (𝓞 E)} {τ : 𝓞 E →+* R}
    {P : (Fin d → R) × (Fin d → R) → Prop} {w : (Fin d → R) × (Fin d → R)} (hw : w ∈ eigW B τ)
    (hg : ∀ a y, P (rhoH B a y - τ a • y)) (h0 : P 0) (hadd : ∀ y y', P y → P y' → P (y + y')) : P w := by
  refine Submodule.iSup_induction (motive := P) _ hw ?_ h0 hadd
  rintro a _ ⟨y, rfl⟩
  exact hg a y

theorem exists_sub_mem_eigW {R : Type} [CommRing R] {d r : ℕ} {B : Germ.FB R d (𝓞 E)}
    {x : Fin r → (Fin d → R) × (Fin d → R)} (h : IsHBasis B x) (τ : 𝓞 E →+* R)
    (y : (Fin d → R) × (Fin d → R)) : ∃ m : Fin r → R, y - ∑ l, m l • x l ∈ eigW B τ := by
  have hy : y ∈ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) := h.2 ▸ trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    classical
    refine ⟨Pi.single q.1 (τ (RingOfIntegers.basis E q.2)), ?_⟩
    refine Submodule.mem_iSup_of_mem (RingOfIntegers.basis E q.2) ⟨x q.1, ?_⟩
    simp [Pi.single_apply, ite_smul]
  | zero => exact ⟨0, by simp⟩
  | add y y' _ _ h1 h2 =>
    obtain ⟨m, hm⟩ := h1
    obtain ⟨m', hm'⟩ := h2
    refine ⟨m + m', ?_⟩
    have := add_mem hm hm'
    convert this using 1
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul c y _ h1 =>
    obtain ⟨m, hm⟩ := h1
    refine ⟨c • m, ?_⟩
    have := (eigW B τ).smul_mem c hm
    convert this using 1
    simp only [Pi.smul_apply, smul_sub, Finset.smul_sum, smul_eq_mul, mul_smul]

theorem vmap_rel {R R' K L : Type} [CommRing R] [CommRing R'] [CommRing K] [CommRing L] {d r : ℕ} (v₀ : R →+* K)
    (v : R' →+* L) (j : L →+* K) (c : R' →+* R) (h : j.comp v = v₀.comp c) (φ' ψ' : Germ.Pt R 1 d)
    (lam' : Germ.PS R 2 d) (x' : (Fin d → R') × (Fin d → R')) (m : Fin r → R)
    (x : Fin r → (Fin d → R) × (Fin d → R)) :
    vmap v₀ (transH φ' ψ' lam' (vmap c x') - ∑ l, m l • x l) =
      transH (fun i => MvPowerSeries.map v₀ (φ' i)) (fun i => MvPowerSeries.map v₀ (ψ' i))
        (MvPowerSeries.map v₀ lam') (vmap j (vmap v x')) - ∑ l, v₀ (m l) • vmap v₀ (x l) := by
  rw [vmap_sub, vmap_transH, vmap_comp, vmap_comp, h, vmap_sum]
  simp only [vmap_smul]

end H

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)}

def toVec (Ω : Type) [Field Ω] (d : ℕ) :
    ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  LinearMap.prodMap LinearMap.id (dotProductBilin Ω Ω)

def toH (S : GermSys t ξ M) (p : Cpt ξ) (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))

theorem toH_add (S : GermSys t ξ M) (p : Cpt ξ)
    (y y' : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (y + y') = toH S p y + toH S p y' := by
  simp [toH, vmap_add]

theorem toH_sub (S : GermSys t ξ M) (p : Cpt ξ)
    (y y' : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (y - y') = toH S p y - toH S p y' := by
  simp [toH, vmap_sub]

theorem toH_zero (S : GermSys t ξ M) (p : Cpt ξ) :
    toH S p (0 : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) = 0 := by
  simp [toH, vmap_zero]

theorem toH_smul (S : GermSys t ξ M) (p : Cpt ξ) (c : X.presheaf.stalk p.1)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (c • y) = genMap ξ p c • toH S p y := by
  simp [toH, vmap_smul]

theorem toH_sum {A : Type} (s : Finset A) (S : GermSys t ξ M) (p : Cpt ξ)
    (y : A → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (∑ i ∈ s, y i) = ∑ i ∈ s, toH S p (y i) := by
  simp [toH, vmap_sum]

theorem toH_spec (S : GermSys t ξ M) (p q : Cpt ξ) (h : q.1 ⤳ p.1) {φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk q.1) 2 d}
    (he : transH (S.φ p) (S.ψ p) (S.lam p) = transH (S.φ q) (S.ψ q) (S.lam q) ∘ₗ
      transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
        (MvPowerSeries.map (genMap ξ q) lam'))
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p y = toH S q (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom y)) := by
  have h1 : (genMap ξ q).comp (X.presheaf.stalkSpecializes h).hom = genMap ξ p :=
    RingHom.ext fun s => ProjectiveLinePlaces.genMap_specializes h q.2 p.2 s
  rw [toH, toH, vmap_transH, vmap_comp, h1, he]
  rfl

end Gen

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
