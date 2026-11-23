import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

def VecAt {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ) : Prop :=
  ∀ (m : ℕ) (s : Fin m → 𝔐.Li), (∀ a, ∃ v, 𝔐.M.ValAt (z t₀) (s a) v) →
    ∃ x : Fin m → (Fin n → ℂ) → Fin g → ℂ, (∀ a, AnalyticAt ℂ (x a) t₀) ∧ ∀ᶠ t in 𝓝 t₀, ∃ v : Fin m → (epsAt (z t) ⟶ 𝔐.t.G),
      (∀ a, 𝔐.M.ValAt (z t) (s a) (v a)) ∧ FibreLatVec 𝔐.t (z t) (R t) (fun a => x a t) v

structure KUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ) where
  ι : Type
  fin : Finite ι
  Di : ι → Datum H
  sig : ∀ k, (Di k).p = D.p ∧ (Di k).q = D.q
  F : ∀ k, UnivFam E (CMType H) j j' n g (Di k).La
  q_eq : ∀ k, (F k).q = q
  form_eq : ∀ k, (F k).form = (Di k).EF ∨ (F k).form = -(Di k).EF
  σ_eq : ∀ k τ, (F k).σ τ = κ.comp (labelEmb c (sm τ))
  Γ : ∀ k, Subgroup ((Di k).La ≃ₗ[𝓞 E] (Di k).La)
  mem_Γ : ∀ k γ, γ ∈ Γ k ↔ InLevel l (Di k) γ
  arith : ∀ k, (F k).IsArith (Γ k)
  pt : ι → (Fin n → ℂ) → (Sp ℂ ⟶ Y.X)
  hol : ∀ k, IsHolTo (ballDom q) (pt k)
  comp_s_eq_spMap_of_isOver : ∀ k, ∀ t ∈ ballDom q, pt k t ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))
  interior : ∀ k, ∀ t ∈ ballDom q, centre (pt k t) ∈ abLocus Y.t.G
  disj : ∀ k k', ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, pt k t = pt k' t' → k = k'
  fibre : ∀ k, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, pt k t = pt k t' ↔ (F k).Eqv (Γ k) t t'
  onto : ∀ p : Sp ℂ ⟶ Y.X, centre p ∈ abLocus Y.t.G → p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) →
    ∃ k, ∃ t ∈ ballDom q, pt k t = p
  lat : ∀ k, ∀ t ∈ ballDom q, FibreLat Y.t (pt k t) ((F k).R t)
  vec : ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (k : ι) (V : Set (Fin n → ℂ)) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)), IsOpen V → V ⊆ ballDom q →
    IsHolTo V z → (∀ t ∈ V, z t ≫ 𝔐.f = pt k t) → ∀ t₀ ∈ V, VecAt 𝔐 (F k).R z t₀
  locc : ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y.X)), IsOpen T → IsPreconnected T → IsHolTo T y →
    (∀ b ∈ T, centre (y b) ∈ abLocus Y.t.G) → (∀ b ∈ T, y b ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) →
    ∀ b ∈ T, ∀ b' ∈ T, ∀ k k', ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, y b = pt k t → y b' = pt k' t' → k = k'

def VecOfPeriods : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (κ : c.F →+* ℂ) (σ : KA l →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (n : ℕ) (V : Set (Fin n → ℂ))
    (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (xF : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c))
    (R : (Fin n → ℂ) → RiemLat E g (FU.Di i).La) (P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)))
    (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V → IsHolTo V z → IsHolTo V xF → IsHolPeriods (FU.Di i) ty V P →
    (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V) →
    (∀ t ∈ V, (R t).form = (FU.Di i).EF ∧ IsUnit (h t).det ∧ (∀ x, P t x = h t *ᵥ (R t).P x) ∧
      xF t ≫ Y.j = z t ≫ 𝔐.f ∧ xF t ≫ pullback.fst _ _ = FU.u i (P t) ∧ xF t ≫ pullback.snd _ _ = spMap κ) →
    ∀ t₀ ∈ V, VecAt 𝔐 R z t₀

def KUnifConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ),
    Nonempty (KUnif Y sm j j' n g q κ) → Nonempty (KUnif Y sm j j' n g q ((starRingEnd ℂ).comp κ))

end SheetDecomposition
