import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalWeilPairingEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilEqTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCubWeilTorsMap
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.ModelWeil

theorem spMap_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Sp B) :
    spMap f x = PrimeSpectrum.comap f x := by
  simp [spMap, Spec.map_base]; rfl

theorem spMap_comp_apply {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (s : A →+* B) (x : Sp C) :
    spMap (g.comp s) x = spMap s (spMap g x) := by
  rw [spMap_apply, spMap_apply, spMap_apply]; rfl

theorem mem_asIdeal_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Sp B) (a : A) :
    a ∈ PrimeSpectrum.asIdeal (spMap f x) ↔ f a ∈ PrimeSpectrum.asIdeal x := by
  rw [spMap_apply]; rfl

theorem exists_unit_range_subset {R A : Type} [CommRing R] [CommRing A] (V : (Sp A).Opens) (s : A →+* R)
    (k : Type) [Field k] [Algebra R k] (h : Set.range (spMap ((algebraMap R k).comp s)) ⊆ V) :
    ∃ r : R, algebraMap R k r ≠ 0 ∧ ∀ (B : Type) [CommRing B] [Algebra R B], IsUnit (algebraMap R B r) →
      Set.range (spMap ((algebraMap R B).comp s)) ⊆ V := by
  obtain ⟨pt⟩ : Nonempty (Sp k) := inferInstance
  let U : Set (Sp R) := (fun x => spMap s x) ⁻¹' (V : Set (Sp A))
  have hU : IsOpen U := V.isOpen.preimage (spMap s).continuous
  have hq : spMap (algebraMap R k) pt ∈ U := by
    have := h ⟨pt, rfl⟩
    rw [spMap_comp_apply] at this
    exact this
  obtain ⟨_, ⟨r, rfl⟩, hqr, hrU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq hU
  refine ⟨r, fun h0 => hqr ?_, fun B _ _ hu => ?_⟩
  · change r ∈ PrimeSpectrum.asIdeal (spMap (algebraMap R k) pt)
    rw [mem_asIdeal_spMap, h0]
    exact zero_mem _
  · rintro _ ⟨P, rfl⟩
    rw [spMap_comp_apply]
    apply hrU
    change r ∉ PrimeSpectrum.asIdeal (spMap (algebraMap R B) P)
    rw [mem_asIdeal_spMap]
    exact fun hm => (PrimeSpectrum.isPrime P).ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)

theorem isProper_of_range_subset_abLocus {S : Scheme.{0}} (G : Over S) {k : Type} [Field k] [IsAlgClosed k]
    (f : Sp k ⟶ S) (h : Set.range f ⊆ abLocus G) : IsProper (pullback.snd G.hom f) := by
  obtain ⟨pt⟩ : Nonempty (Sp k) := inferInstance
  exact h ⟨pt, rfl⟩ k f ⟨pt, rfl⟩

theorem apply_charElem_tateMap {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (GG : PDivGroup p R) (φ : GG ⟶ GG.dual)
    (c : GG.Tate) (n : ℕ) (s : GG.A n →ₐ[R] R) :
    s (charElem (tateMap GG GG.dual R φ c) n) = c.pt n (φ.app n (toConv s.toLinearMap)) := by
  have h := apply_charElem (tateMap GG GG.dual R φ c) n (toConv s.toLinearMap)
  rw [tateMap_pt] at h
  exact h

end GlobalTheory.GroupBplus.Aff.ModelWeil

namespace GlobalTheory.GroupBplus.Aff

open ModelWeil in

theorem weilIs_model_pol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (t : SAB H (Sp R)) (t₀ : SAB H (Sp K)) (mK : SABMap t₀ t (spMap (algebraMap R K))) (GG₀ : PDivGroup p K) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀) (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsOfType Dw t₀ → IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ → ∀ (GG : PDivGroup p R) (θ : TorsionMap t.G GG) (e : GG₀ ≅ GG.baseChange K), IsModel K θ → GenCompat mK.φ θ θ₀ e → ∀ φ : GG ⟶ GG.dual, pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom = e.hom ≫ PDivGroup.baseChangeMap K φ → ∀ τ : Dw.La →+ GG.Tate, (∀ x, tateMap _ _ K e.hom (τ₀ x) = bcTate K (τ x)) → ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra R k], (p : k) ≠ 0 → Set.range (spMap (algebraMap R k)) ⊆ abLocus t.G → ∀ (x x' : Tors t.G (p ^ n) k) (y : Dw.La) (u : kˣ), θ.pt n k x' = tatePt (τ y) n k → (u : k) = θ.pt n k x (charElem (tateMap GG GG.dual R φ (τ y)) n) → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) x.1 x'.1 (unitOn u) := by
  intro E _ _ _ H Dw p _ R K _ _ _ _ _ _ _ _ t t₀ mK GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hT hP GG θ e hM hC φ hφ τ hτ n k _ _ _ hp hk
    x x' y u hx' hu
  classical
  obtain ⟨hfin, hsep, -⟩ := GlobalTheory.HopfPoints.finite_points_separate_rank R K (GG.A n)
  haveI := hfin
  obtain ⟨s, hs⟩ := GlobalTheory.finiteAlg_fieldPoint_factors_through_base R K (GG.A n) hsep k (θ.pt n k x)
  set s' : GG.A n →ₐ[R] R := (τ y).pt n with hs'
  obtain ⟨V, hV⟩ := (hM n).opn
  have hVk : ∀ σ : GG.A n →ₐ[R] R, (Algebra.ofId R k).comp σ ∈ Set.range (θ.pt n k) →
      ∃ r : R, algebraMap R k r ≠ 0 ∧ ∀ (B : Type) [CommRing B] [Algebra R B], IsUnit (algebraMap R B r) →
        (Algebra.ofId R B).comp σ ∈ {φ : GG.A n →ₐ[R] B | Set.range (spMap (φ : GG.A n →+* B)) ⊆ V} := by
    rintro σ ⟨w, hw⟩
    have := (hV k).mapsTo (Set.mem_univ w)
    change Set.range (spMap ((θ.pt n k w : GG.A n →ₐ[R] k) : GG.A n →+* k)) ⊆ V at this
    rw [hw] at this
    obtain ⟨r, hr, hB⟩ := exists_unit_range_subset V (σ : GG.A n →+* R) k this
    refine ⟨r, hr, fun B _ _ hu => ?_⟩
    have e : (((Algebra.ofId R B).comp σ : GG.A n →ₐ[R] B) : GG.A n →+* B) = (algebraMap R B).comp (σ : GG.A n →+* R) :=
      RingHom.ext fun _ => rfl
    show Set.range (spMap (((Algebra.ofId R B).comp σ : GG.A n →ₐ[R] B) : GG.A n →+* B)) ⊆ V
    rw [e]
    exact hB B hu
  obtain ⟨r₁, hr₁, hV₁⟩ := hVk s ⟨x, hs⟩
  obtain ⟨r₂, hr₂, hV₂⟩ := hVk s' ⟨x', hx'⟩
  set r := r₁ * r₂ with hr
  have hrk : algebraMap R k r ≠ 0 := by rw [map_mul]; exact mul_ne_zero hr₁ hr₂
  have hr0 : r ≠ 0 := fun h0 => hrk (by rw [h0, map_zero])
  let S := Localization.Away r
  have huS : IsUnit (algebraMap R S r) := IsLocalization.Away.algebraMap_isUnit r
  have huS₁ : IsUnit (algebraMap R S r₁) := isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact huS)
  have huS₂ : IsUnit (algebraMap R S r₂) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact huS)
  obtain ⟨z, -, hz⟩ := (hV S).surjOn (hV₁ S huS₁)
  obtain ⟨z', -, hz'⟩ := (hV S).surjOn (hV₂ S huS₂)
  change θ.pt n S z = (Algebra.ofId R S).comp s at hz
  change θ.pt n S z' = (Algebra.ofId R S).comp s' at hz'
  let ψ : S →ₐ[R] k := IsLocalization.Away.liftAlgHom (S := S) r (f := Algebra.ofId R k) (isUnit_iff_ne_zero.2 hrk)
  have hrK : algebraMap R K r ≠ 0 := fun h0 => hr0 (IsFractionRing.injective R K (by rw [h0, map_zero]))
  let ιK : S →ₐ[R] K := IsLocalization.Away.liftAlgHom (S := S) r (f := Algebra.ofId R K) (isUnit_iff_ne_zero.2 hrK)
  have hofId : ∀ (C : Type) [CommRing C] [Algebra R C] (χ : S →ₐ[R] C) (σ : GG.A n →ₐ[R] R),
      χ.comp ((Algebra.ofId R S).comp σ) = (Algebra.ofId R C).comp σ := fun C _ _ χ σ => by
    rw [← AlgHom.comp_assoc, Subsingleton.elim (χ.comp (Algebra.ofId R S)) (Algebra.ofId R C)]
  have hinj : ∀ w w' : Tors t.G (p ^ n) k, θ.pt n k w = θ.pt n k w' → w = w' := fun w w' h =>
    (hV k).injOn (Set.mem_univ w) (Set.mem_univ w') h
  have hxz : torsMap ψ z = x := hinj _ _ (by rw [θ.nat n S k ψ z _ rfl, hz, hofId, hs])
  have hxz' : torsMap ψ z' = x' := hinj _ _ (by rw [θ.nat n S k ψ z' _ rfl, hz', hofId, hx'])
  obtain ⟨ζ, hζ⟩ := exists_unit_cubWeil_torsMap E H R t (p ^ n) S z z'
  have hK := CubPair.cubWeil_eq_transport E H Dw p R K t t₀ mK GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hT hP GG θ e hM hC n
    (torsMap ιK z) (torsMap ιK z') (Units.map (ιK : S →* K) ζ) s s'
    (by rw [θ.nat n S K ιK z _ rfl, hz, hofId]) (by rw [θ.nat n S K ιK z' _ rfl, hz', hofId]) (hζ K ιK)
  rw [hφ, Iso.inv_hom_id_assoc] at hK
  change (ιK ζ : K) = Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s') _
    ((1 : K) ⊗ₜ[R] φ.app n (toConv s.toLinearMap)) at hK
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, _root_.one_mul, AlgHom.comp_apply, ← apply_charElem_tateMap] at hK
  set w := s (charElem (tateMap GG GG.dual R φ (τ y)) n) with hw
  have hιK : Function.Injective ιK := by
    change Function.Injective (IsLocalization.lift (M := Submonoid.powers r) (S := S) _)
    rw [IsLocalization.lift_injective_iff]
    intro a b
    rw [(IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hr0)).eq_iff]
    exact (IsFractionRing.injective R K).eq_iff.symm
  have hζS : (ζ : S) = algebraMap R S w := hιK (by rw [hK]; exact (ιK.commutes w).symm)
  have hψζ : Units.map (ψ : S →* k) ζ = u := Units.ext (by
    change ψ ζ = (u : k)
    rw [hζS, ψ.commutes, hu, hs]
    rfl)
  have hcub := hζ k ψ
  rw [hxz, hxz', hψζ] at hcub
  have hpr := isProper_of_range_subset_abLocus t.G (spMap (algebraMap R k)) hk
  have key : ∀ g : Sp k ⟶ Sp R, 𝟙 _ ≫ spMap (algebraMap R k) = g → ∀ (a b : Over.mk g ⟶ t.G) (c : Γ(Sp k, ⊤)ˣ),
      GlobalTheory.UU.CubWeil t.cub (p ^ n) a b c → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) a b c := by
    rintro _ rfl a b c h
    exact GlobalTheory.FlatTors.weilIs_of_cubWeil_of_proper (spMap (algebraMap R k)) t.G t.semi hpr t.cub (p ^ n)
      (Over.mk (𝟙 _)) a b c h
  exact key _ (Category.id_comp _) x.1 x'.1 _ hcub

end GlobalTheory.GroupBplus.Aff
