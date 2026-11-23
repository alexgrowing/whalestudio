import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKintIffIntegralEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKintIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionProductDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlPiEquivSymmContinuous
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinP

def FinConj {H : Type} [Group H] (U : Subgroup H) (a : H) : Prop :=
  ∀ E : Finset H, ∃ D : Finset H, ∀ x : H, (∃ e ∈ E, ∃ k ∈ U, x⁻¹ * a * x = e * k) →
    ∃ t : H, t * a = a * t ∧ ∃ d ∈ D, ∃ k ∈ U, x = t * d * k

theorem finConj_of_central {H : Type} [Group H] (U : Subgroup H) (a : H) (ha : ∀ x, x * a = a * x) :
    FinConj U a :=
  fun _ => ⟨{1}, fun x _ => ⟨x, ha x, 1, Finset.mem_singleton_self _, 1, U.one_mem, by simp⟩⟩

theorem finConj_prod {H₁ H₂ : Type} [Group H₁] [Group H₂] (U₁ : Subgroup H₁) (U₂ : Subgroup H₂) (a₁ : H₁)
    (a₂ : H₂) (h₁ : FinConj U₁ a₁) (h₂ : FinConj U₂ a₂) : FinConj (U₁.prod U₂) (a₁, a₂) := by
  intro E
  obtain ⟨D₁, hD₁⟩ := h₁ (E.image Prod.fst)
  obtain ⟨D₂, hD₂⟩ := h₂ (E.image Prod.snd)
  refine ⟨D₁ ×ˢ D₂, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  have hk' := Subgroup.mem_prod.1 hk
  obtain ⟨t₁, ht₁, d₁, hd₁, k₁, hk₁, hx₁⟩ :=
    hD₁ x.1 ⟨e.1, Finset.mem_image_of_mem _ he, k.1, hk'.1, congrArg Prod.fst hx⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, k₂, hk₂, hx₂⟩ :=
    hD₂ x.2 ⟨e.2, Finset.mem_image_of_mem _ he, k.2, hk'.2, congrArg Prod.snd hx⟩
  exact ⟨(t₁, t₂), Prod.ext ht₁ ht₂, (d₁, d₂), Finset.mem_product.2 ⟨hd₁, hd₂⟩, (k₁, k₂),
    Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩, Prod.ext hx₁ hx₂⟩

theorem finConj_pi {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)] (U : ∀ i, Subgroup (H i))
    (a : ∀ i, H i) (h : ∀ i, FinConj (U i) (a i)) : FinConj (Subgroup.pi Set.univ U) a := by
  intro E
  choose D hD using fun i => h i (E.image fun e => e i)
  refine ⟨Fintype.piFinset D, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  choose t ht d hd k' hk' hxe using fun i =>
    hD i (x i) ⟨e i, Finset.mem_image_of_mem _ he, k i, hk i (Set.mem_univ i), congrFun hx i⟩
  exact ⟨t, funext ht, d, Fintype.mem_piFinset.2 hd, k', fun i _ => hk' i, funext hxe⟩

theorem finConj_map {H H' : Type} [Group H] [Group H'] (ψ : H ≃* H') (U : Subgroup H) (U' : Subgroup H')
    (hU : ∀ k, k ∈ U ↔ ψ k ∈ U') (a : H) (h : FinConj U' (ψ a)) : FinConj U a := by
  intro E
  obtain ⟨D, hD⟩ := h (E.image ψ)
  refine ⟨D.image ψ.symm, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  obtain ⟨t, ht, d, hd, k', hk', hxe⟩ := hD (ψ x) ⟨ψ e, Finset.mem_image_of_mem _ he, ψ k, (hU k).1 hk,
    by rw [← map_inv, ← map_mul, ← map_mul, hx, map_mul]⟩
  refine ⟨ψ.symm t, ?_, ψ.symm d, Finset.mem_image_of_mem _ hd, ψ.symm k', (hU _).2 (by simpa using hk'), ?_⟩
  · apply ψ.injective; simp [map_mul, ht]
  · apply ψ.injective; simp [map_mul, hxe]

theorem finConj_field {k : Type} [NontriviallyNormedField k] {n : ℕ} (U : Subgroup (GL (Fin n) k))
    (hUo : IsOpen (U : Set (GL (Fin n) k))) (hUc : IsCompact (U : Set (GL (Fin n) k))) (a : GL (Fin n) k)
    (ha : (a : Matrix (Fin n) (Fin n) k).charpoly.Separable) : FinConj U a := by
  intro E
  set Z : Set (Matrix (Fin n) (Fin n) k) := (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) ''
    (⋃ e ∈ E, (fun u => e * u) '' (U : Set (GL (Fin n) k))) with hZdef
  have hZ : IsCompact Z := (E.isCompact_biUnion fun e _ =>
    hUc.image (continuous_const.mul continuous_id)).image Units.continuous_val
  obtain ⟨C, hC, hCg⟩ := GlobalTheory.OrbCpt.gl_orbit_cpt (a : Matrix (Fin n) (Fin n) k) ha Z hZ
  have hCi : IsCompact ((fun c => c⁻¹) '' C) := hC.image continuous_inv
  obtain ⟨D, hD⟩ := hCi.elim_finite_subcover (fun d : GL (Fin n) k => (fun u => d * u) '' (U : Set _))
    (fun d => isOpenMap_mul_left d _ hUo)
    (fun y _ => Set.mem_iUnion.2 ⟨y, 1, U.one_mem, mul_one y⟩)
  refine ⟨D, fun x ⟨e, he, u, hu, hx⟩ => ?_⟩
  have hxZ : ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * a *
      ((x⁻¹⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Z :=
    ⟨x⁻¹ * a * x, Set.mem_iUnion₂.2 ⟨e, he, u, hu, hx.symm⟩, by simp [inv_inv]⟩
  obtain ⟨c, hc, t, ht, hxct⟩ := hCg x⁻¹ hxZ
  obtain ⟨d, hdD, v, hv, hdv⟩ := Set.mem_iUnion₂.1 (hD ⟨c, hc, rfl⟩)
  have ht' : t * a = a * t := Units.ext ht
  refine ⟨t⁻¹, ?_, d, hdD, v, hv, ?_⟩
  · calc t⁻¹ * a = t⁻¹ * (a * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * a) * t⁻¹ := by rw [ht']
      _ = a * t⁻¹ := by group
  · have hdv' : d * v = c⁻¹ := hdv
    rw [mul_assoc, hdv', ← _root_.mul_inv_rev, ← hxct, inv_inv]

def glPi {R S : Type} [CommRing R] [CommRing S] (k n : ℕ) (e : R ≃+* (Fin k → S)) :
    GL (Fin n) R ≃* (Fin k → GL (Fin n) S) :=
  (Units.mapEquiv (e.mapMatrix.trans (matPiEquiv S n k)).toMulEquiv).trans MulEquiv.piUnits

theorem glPi_mem_iff {R S : Type} [CommRing R] [CommRing S] (k n : ℕ) (e : R ≃+* (Fin k → S))
    (A : Subring R) (B : Subring S) (hAB : ∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) (g : GL (Fin n) R) :
    g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range ↔
      glPi k n e g ∈ Subgroup.pi Set.univ (fun _ => (GeneralLinearGroup.map (n := Fin n) B.subtype).range) := by
  rw [Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_range_map_subtype_iff, hAB]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨fun a b => h1 a b i, fun a b => h2 a b i⟩
  · intro h
    exact ⟨fun a b i => (h i).1 a b, fun a b i => (h i).2 a b⟩

variable (p : ℕ) [Fact p.Prime]

theorem finConj_res_split (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [hK : FiniteDimensional ℚ_[p] K] (n r : ℕ)
    (k m : ℕ) (hm : 0 < m) (e : KQ p K r ≃+* (Fin k → ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m))
    (hint : ∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K m)
    (g : GL (Fin n) K) (hg : (g : Matrix (Fin n) (Fin n) K).charpoly.Separable) :
    FinConj (Kres p K n r) (GeneralLinearGroup.map (inclK p K r).toRingHom g) := by
  have hp0 : ‖algebraMap ℚ_[p] (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) p‖ = (p : ℝ)⁻¹ := by
    show ‖algebraMap ℚ_[p] (PadicAlgCl p) p‖ = _
    rw [PadicAlgCl.norm_extends, Padic.norm_p]
  have hp1 : (p : ℝ)⁻¹ ≠ 1 := inv_ne_one.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt.ne')
  have hp2 : (p : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  letI : NontriviallyNormedField (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) :=
    NontriviallyNormedField.ofNormNeOne ⟨algebraMap ℚ_[p] (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) p, ?_, ?_⟩
  rotate_left
  · intro h; rw [h, norm_zero] at hp0; exact hp2 hp0.symm
  · rw [hp0]; exact hp1
  refine finConj_map (glPi _ n e) _ _ (fun k => glPi_mem_iff _ n e _ _ hint k) _ ?_
  refine finConj_pi _ _ fun i => ?_
  refine finConj_field _ (GlobalTheory.LKLoc.isOpen_Kint p K n m) (GlobalTheory.LKLoc.isCompact_Kint p K hK n m hm) _ ?_
  have hmat : ((glPi _ n e (GeneralLinearGroup.map (inclK p K r).toRingHom g) i : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _) = (g : Matrix (Fin n) (Fin n) K).map
        (((Pi.evalRingHom _ i).comp e.toRingHom).comp (inclK p K r).toRingHom) := by
    ext a b; rfl
  rw [hmat, Matrix.charpoly_map]
  exact hg.map

theorem finConj_res (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [hK : FiniteDimensional ℚ_[p] K] (n r : ℕ)
    (hr : 0 < r) (g : GL (Fin n) K) (hg : (g : Matrix (Fin n) (Fin n) K).charpoly.Separable) :
    FinConj (Kres p K n r) (GeneralLinearGroup.map (inclK p K r).toRingHom g) := by
  obtain ⟨e, τ, -, -, -, -, -, hint⟩ :=
    GlobalTheory.T.unramified_extension_product_decomposition p K hK (ReciprocityTheory.DiscreteGroups.LocalClassField.fK p K) r (ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK p K hK) hr
  exact finConj_res_split p K n r _ _ (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr))
    e hint g hg

end GlobalTheory.OrbFinP

namespace GlobalTheory.OrbFinP

theorem orbit_fin_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ →
    ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ x : Gr G r,
      (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, x⁻¹ * inclG G r γ * x = e * k) →
      ∃ t : Gr G r, t * inclG G r γ = inclG G r γ * t ∧ ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, x = t * d * k := by
  intro p _ G r hr γ hγ
  have key : FinConj (KHT p G.m G.n r G.Fw) (inclG G r γ) := by
    show FinConj ((GlobalTheory.LKLoc.Kint p (Q0 p) 1 r).prod (Subgroup.pi Set.univ fun i => Kres p (G.Fw i) G.n r))
      (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom γ.1),
        fun w => GeneralLinearGroup.map (inclK p (G.Fw w) r).toRingHom (γ.2 w))
    refine finConj_prod _ _ _ _ (finConj_of_central _ _ fun x => ?_)
      (finConj_pi _ _ fun w => finConj_res p (G.Fw w) G.n r hr (γ.2 w) (hγ w))
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  exact key

end GlobalTheory.OrbFinP
