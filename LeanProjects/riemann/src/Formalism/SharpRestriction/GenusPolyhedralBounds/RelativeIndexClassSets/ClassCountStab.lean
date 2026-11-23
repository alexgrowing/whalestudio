import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralClass
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStmt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountGenIn
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountSurj

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Stab

open Formalism.UG Formalism.UG.CS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

abbrev GamA (σ : E →ₐ[F] E) (J : Matrix n n E) : Subgroup (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
  (ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))

abbrev KA (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) :
    Subgroup (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
  (levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))

abbrev bcA (γ : GL n E) : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ

abbrev latA (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
      (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  latS (F := F) (FiniteAdeleRing (𝓞 F) F)
    (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ

theorem exists_place_two : ∃ v : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hpZ : Prime ((2 : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨Q, hQ, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F)
    (Ideal.span {((2 : ℕ) : ℤ)})
  have hmem : ((2 : ℕ) : 𝓞 F) ∈ Q := by
    have : ((2 : ℕ) : ℤ) ∈ Q.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : ((2 : ℕ) : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

instance finiteAdeleRing_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨v, -⟩ := exists_place_two (F := F)
  exact (evalV F v).toRingHom.domain_nontrivial

theorem glEquiv_one : glEquiv (1 : GL n E) = LinearEquiv.refl E (n → E) := by
  ext x i
  rw [Formalism.UG.P.glEquiv_apply']
  simp

theorem gmap_refl (M : Submodule (𝓞 E) (n → E)) :
    Formalism.HermitianLatticesTheory.gmap (LinearEquiv.refl E (n → E)) M = M := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem glEquiv_injective : Function.Injective (glEquiv (K := E) (n := n)) := by
  intro a b hab
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Formalism.UG.P.glEquiv_apply', ← Formalism.UG.P.glEquiv_apply', hab]

theorem globLat_left (Λ : Submodule (𝓞 E) (n → E)) (γ : GL n E)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    globLat (bcA γ * g) Λ = Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat g Λ) := by
  have := Formalism.UG.P.global_lattice_equiv_holds F E n Λ γ g 1 (one_mem _)
  rwa [mul_one] at this

theorem globLat_right (Λ : Submodule (𝓞 E) (n → E))
    (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hk : k ∈ stabGL (latA (F := F) Λ)) :
    globLat (g * k) Λ = globLat g Λ := by
  have := Formalism.UG.P.global_lattice_equiv_holds F E n Λ 1 g k hk
  rwa [map_one, one_mul, glEquiv_one, gmap_refl] at this

theorem stab_of_globLat_eq (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
    (g g' : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (h : globLat g Λ = globLat g' Λ) :
    g'⁻¹ * g ∈ stabGL (latA (F := F) Λ) := by
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.fg
  have hSR := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E n Λ hfin hΛ.span_eq_top
  intro x
  have h1 := hSR g ((g : Matrix n n _) *ᵥ x)
  have h2 := hSR g' ((g : Matrix n n _) *ᵥ x)
  rw [h] at h1
  have h3 := h1.symm.trans h2
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h3
  exact h3

theorem stab_iff (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ) (γ : GL n E)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    g⁻¹ * bcA γ * g ∈ stabGL (latA (F := F) Λ) ↔
      Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat g Λ) = globLat g Λ := by
  constructor
  · intro hk
    rw [← globLat_left, ← globLat_right Λ g _ hk]
    congr 1
    group
  · intro hM
    rw [← globLat_left] at hM
    have := inv_mem (stab_of_globLat_eq Λ hΛ _ _ hM.symm)
    convert this using 1
    group

section Herm

variable [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
  (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E)

include hσ in
theorem sig_eq : (σ : E →+* E) = starRingEnd E := by
  ext e
  exact hσ e

include hσ in
theorem mem_UJ_iff (γ : GL n E) : γ ∈ UJ (σ : E →+* E) (Formalism.UG.gram h) ↔ glEquiv γ ∈ Formalism.HermitianLatticesTheory.isom h := by
  rw [sig_eq σ hσ]
  exact Formalism.UG.P.hermitian_lattice_correspondence_holds E n h γ

def autMat (M : Submodule (𝓞 E) (n → E)) : Set (GL n E) :=
  {γ | γ ∈ UJ (σ : E →+* E) (Formalism.UG.gram h) ∧ Formalism.HermitianLatticesTheory.gmap (glEquiv γ) M = M}

include hσ in
theorem autMat_bij (M : Submodule (𝓞 E) (n → E)) :
    Function.Bijective (fun γ : autMat σ h M =>
      (⟨glEquiv γ.1, (mem_UJ_iff σ hσ h γ.1).1 γ.2.1, γ.2.2⟩ : Formalism.ThetaLiftIndependence.autL h M)) := by
  constructor
  · intro a b hab
    exact Subtype.ext (glEquiv_injective (congrArg Subtype.val hab))
  · rintro ⟨u, hu, huM⟩
    obtain ⟨γ, rfl⟩ := Formalism.UG.P.hermitian_correspondence_surjective_holds E n h u hu
    exact ⟨⟨γ, (mem_UJ_iff σ hσ h γ).2 hu, huM⟩, rfl⟩

theorem bcA_mem_UPts (J : Matrix n n E) (γ : GL n E) (hγ : γ ∈ UJ (σ : E →+* E) J) :
    bcA γ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
  Formalism.UG.P.rational_points_le_holds F E n σ J (FiniteAdeleRing (𝓞 F) F) ⟨γ, hγ, rfl⟩

def ratPt (J : Matrix n n E) (γ : GL n E) (hγ : γ ∈ UJ (σ : E →+* E) J) : GamA (F := F) σ J :=
  ⟨⟨bcA γ, bcA_mem_UPts σ J γ hγ⟩, Subgroup.mem_subgroupOf.2 ⟨γ, hγ, rfl⟩⟩

theorem ratPt_mem_stabAt (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
    (hΛ : Submodule.IsLattice E Λ) (g : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (γ : GL n E)
    (hγ : γ ∈ UJ (σ : E →+* E) J) :
    ratPt σ J γ hγ ∈ stabAt (GamA σ J) (KA σ J Λ) g ↔
      Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) =
        globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ := by
  rw [← stab_iff Λ hΛ]
  constructor
  · intro hm
    have hm' : (g⁻¹ * ((ratPt σ J γ hγ : GamA σ J) : UPts σ J (FiniteAdeleRing (𝓞 F) F)) * g) ∈ KA σ J Λ := hm
    have hm2 : ((g⁻¹ * ((ratPt σ J γ hγ : GamA σ J) : UPts σ J (FiniteAdeleRing (𝓞 F) F)) * g :
        UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL n _) ∈ levelAfL σ J Λ := Subgroup.mem_subgroupOf.1 hm'
    exact hm2.2
  · intro hm
    show (g⁻¹ * ((ratPt σ J γ hγ : GamA σ J) : UPts σ J (FiniteAdeleRing (𝓞 F) F)) * g) ∈ KA σ J Λ
    refine Subgroup.mem_subgroupOf.2 ?_
    exact Subgroup.mem_inf.2 ⟨(g⁻¹ * ((ratPt σ J γ hγ : GamA σ J) : UPts σ J (FiniteAdeleRing (𝓞 F) F)) * g).2, hm⟩

theorem stabMat_bij (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
    (g : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
    Function.Bijective (fun γ : autMat σ h (globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) =>
      (⟨ratPt σ (Formalism.UG.gram h) γ.1 γ.2.1, (ratPt_mem_stabAt σ (Formalism.UG.gram h) Λ hΛ g γ.1 γ.2.1).2 γ.2.2⟩ :
        stabAt (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g)) := by
  constructor
  · intro a b hab
    have h1 : bcA (F := F) a.1 = bcA b.1 :=
      congrArg (fun x : stabAt (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g =>
        ((x.1.1 : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
          GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) hab
    exact Subtype.ext (Formalism.UG.P.UG_inclusion_injective F E n (FiniteAdeleRing (𝓞 F) F) inferInstance h1)
  · rintro ⟨⟨⟨x, hxU⟩, hxΓ⟩, hx⟩
    obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_subgroupOf.1 hxΓ
    have hγx' : bcA γ = x := hγx
    subst hγx'
    exact ⟨⟨γ, hγ, (ratPt_mem_stabAt σ (Formalism.UG.gram h) Λ hΛ g γ hγ).1 hx⟩, rfl⟩

def stabEquiv (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
    (g : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
    stabAt (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g ≃
      Formalism.ThetaLiftIndependence.autL h (globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) :=
  (Equiv.ofBijective _ (stabMat_bij σ h Λ hΛ g)).symm.trans (Equiv.ofBijective _ (autMat_bij σ hσ h _))

theorem stabEquiv_apply (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
    (g : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F))
    (x : stabAt (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g) (γ : GL n E)
    (hx : ((x.1.1 : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
      GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = bcA γ) :
    (stabEquiv σ hσ h Λ hΛ g x).1 = glEquiv γ := by
  obtain ⟨a, rfl⟩ := (Equiv.ofBijective _ (stabMat_bij σ h Λ hΛ g)).surjective x
  have ha : a.1 = γ := Formalism.UG.P.UG_inclusion_injective F E n (FiniteAdeleRing (𝓞 F) F) inferInstance hx
  subst ha
  simp [stabEquiv]

include hσ in
theorem card_stabAt (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
    (g : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
    Nat.card (stabAt (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g) =
      Nat.card (Formalism.ThetaLiftIndependence.autL h (globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ)) :=
  Nat.card_congr (stabEquiv σ hσ h Λ hΛ g)

theorem gmap_mul (u v : (n → E) ≃ₗ[E] (n → E)) (M : Submodule (𝓞 E) (n → E)) :
    Formalism.HermitianLatticesTheory.gmap (u * v) M = Formalism.HermitianLatticesTheory.gmap u (Formalism.HermitianLatticesTheory.gmap v M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨v y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_one (M : Submodule (𝓞 E) (n → E)) :
    Formalism.HermitianLatticesTheory.gmap (1 : (n → E) ≃ₗ[E] (n → E)) M = M := gmap_refl M

theorem gmap_inv {u : (n → E) ≃ₗ[E] (n → E)} {M N : Submodule (𝓞 E) (n → E)}
    (hu : Formalism.HermitianLatticesTheory.gmap u N = M) : Formalism.HermitianLatticesTheory.gmap u⁻¹ M = N := by
  rw [← hu, ← gmap_mul, inv_mul_cancel, gmap_one]

include hσ in

theorem mk_eq_of_isom (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
    (g g' : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) (u : (n → E) ≃ₗ[E] (n → E))
    (hu : u ∈ Formalism.HermitianLatticesTheory.isom h)
    (hM : Formalism.HermitianLatticesTheory.gmap u (globLat (g' : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) =
      globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) :
    DoubleCoset.mk (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g =
      DoubleCoset.mk (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g' := by
  obtain ⟨γ, rfl⟩ := Formalism.UG.P.hermitian_correspondence_surjective_holds E n h u hu
  exact Formalism.UG.P.class_injective_of_span_recovery (Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds)
    Formalism.UG.P.global_lattice_equiv_holds F E n σ (Formalism.UG.gram h) Λ (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top g g' γ
    ((mem_UJ_iff σ hσ h γ).2 hu) hM.symm

include hσ in

theorem isom_of_mk_eq (Λ : Submodule (𝓞 E) (n → E))
    (g g' : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F))
    (hc : DoubleCoset.mk (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g =
      DoubleCoset.mk (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g') :
    ∃ u ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap u (globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) =
      globLat (g' : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ := by
  obtain ⟨a, ha, k, hk, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 hc
  obtain ⟨γ, hγ, hγa⟩ := Subgroup.mem_subgroupOf.1 ha
  have hk' : (k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ levelAfL σ (Formalism.UG.gram h) Λ :=
    Subgroup.mem_subgroupOf.1 hk
  refine ⟨glEquiv γ, (mem_UJ_iff σ hσ h γ).1 hγ, ?_⟩
  have hγa' : bcA γ = (a : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := hγa
  rw [Subgroup.coe_mul, Subgroup.coe_mul, globLat_right Λ _ _ hk'.2, ← hγa', globLat_left]

section Mass

variable (hsymm : h.IsSymm) (hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
  (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
  (hIn : ∀ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ ∈ Formalism.HermitianLatticesTheory.genus h Λ)
  (hSurj : ∀ M ∈ Formalism.HermitianLatticesTheory.genus h Λ, ∃ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ = M)

include hσ hsymm hpos hΛ in
theorem finite_stabAt (g : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
    Finite (stabAt (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) g) := by
  have hL := Formalism.UG.P.global_lattice_isLattice_holds F E n Λ (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have hf : Finite (Formalism.ThetaLiftIndependence.autL h (globLat (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ)) :=
    (Formalism.HermitianLatticesTheory.autFinite E (n → E) h hsymm hpos _ hL).to_subtype
  exact Finite.of_equiv _ (stabEquiv σ hσ h Λ hΛ g).symm

include hσ hsymm hpos hΛ hIn in
theorem finite_classSet : Finite (ClassSet (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ)) := by
  obtain ⟨⟨s0, hs0⟩, -, -⟩ := Formalism.HermitianLatticesTheory.massBasic E (n → E) h hsymm hpos Λ hΛ
  have hex : ∀ c : ClassSet (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ), ∃ N : s0, ∃ u ∈ Formalism.HermitianLatticesTheory.isom h,
      Formalism.HermitianLatticesTheory.gmap u N.1 = globLat ((Quotient.out c : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
        GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ := by
    intro c
    obtain ⟨N, ⟨hN, u, hu, huN⟩, -⟩ := hs0.2 _ (hIn _ (Quotient.out c).2)
    exact ⟨⟨N, hN⟩, u, hu, huN⟩
  choose f hf using hex
  refine Finite.of_injective f ?_
  intro c c' hcc
  obtain ⟨u, hu, huN⟩ := hf c
  obtain ⟨u', hu', huN'⟩ := hf c'
  rw [← DoubleCoset.out_eq' _ _ c, ← DoubleCoset.out_eq' _ _ c']
  refine mk_eq_of_isom σ hσ h Λ hΛ _ _ (u * u'⁻¹) (mul_mem hu (inv_mem hu')) ?_
  rw [gmap_mul, gmap_inv huN', ← hcc, huN]

include hσ hΛ in
theorem glob_injective (s : ClassSet (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) → UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F))
    (hs : ∀ c, DoubleCoset.mk (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) (s c) = c) :
    Function.Injective (fun c => globLat ((s c : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
      GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ) := by
  intro c c' hcc
  rw [← hs c, ← hs c']
  refine mk_eq_of_isom σ hσ h Λ hΛ _ _ 1 (one_mem _) ?_
  rw [gmap_one]
  exact hcc.symm

include hσ hΛ hIn hSurj in

theorem isClassReps_glob [Fintype (ClassSet (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ))]
    [DecidableEq (Submodule (𝓞 E) (n → E))]
    (s : ClassSet (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) → UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F))
    (hs : ∀ c, DoubleCoset.mk (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) (s c) = c) :
    Formalism.ThetaLiftIndependence.IsClassReps h Λ (Finset.univ.image (fun c =>
      globLat ((s c : UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F)) :
        GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Λ)) := by
  constructor
  · intro M hM
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hM
    exact hIn _ (s c).2
  · intro M hM
    obtain ⟨g, hg, rfl⟩ := hSurj M hM
    set c := DoubleCoset.mk (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) ⟨g, hg⟩ with hc
    obtain ⟨u, hu, huM⟩ := isom_of_mk_eq σ hσ h Λ (s c) ⟨g, hg⟩ (hs c)
    refine ⟨_, ⟨Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, u, hu, huM⟩, ?_⟩
    rintro N ⟨hN, u', hu', hu'M⟩
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hN
    have : c = c' := by
      rw [hc, ← hs c']
      exact mk_eq_of_isom σ hσ h Λ hΛ ⟨g, hg⟩ (s c') u' hu' hu'M
    rw [this]

include hσ hsymm hpos hΛ hIn hSurj in

theorem mass_eq_sum
    (s : ClassSet (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) → UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F))
    (hs : ∀ c, DoubleCoset.mk (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) (s c) = c) :
    Formalism.HermitianLatticesTheory.mass h Λ = ∑ᶠ c : ClassSet (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ),
      ((Nat.card (stabAt (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ) (s c)) : ℕ) : ℝ)⁻¹ := by
  classical
  have := finite_classSet σ hσ h hsymm hpos Λ hΛ hIn
  have := Fintype.ofFinite (ClassSet (GamA σ (Formalism.UG.gram h)) (KA σ (Formalism.UG.gram h) Λ))
  obtain ⟨-, hm, -⟩ := Formalism.HermitianLatticesTheory.massBasic E (n → E) h hsymm hpos Λ hΛ
  rw [hm _ (isClassReps_glob σ hσ h Λ hΛ hIn hSurj s hs),
    Finset.sum_image (fun a _ b _ hab => glob_injective σ hσ h Λ hΛ s hs hab),
    finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun c _ => by rw [card_stabAt σ hσ h Λ hΛ]

end Mass

end Herm

section Std

open Formalism.MainNotions.StandardLattice

variable {k : ℕ} [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)

theorem gram_stdForm : gram (stdForm E k) = 1 := by
  ext i j
  simp only [Formalism.UG.gram, Formalism.MainNotions.Gaps.MI.stdForm_apply', Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [Pi.single_apply]
  · simp [Pi.single_apply, hij, Ne.symm hij]

include hσ in
theorem stabAut : StabAut σ (1 : Matrix (Fin k) (Fin k) E) := by
  have := card_stabAt σ hσ (stdForm E k) (stdLat E k) (Formalism.MainNotions.Gaps.MI.stdLat_isLattice' E k)
  rw [gram_stdForm] at this
  exact this

variable (hc : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))

include hσ hc in
theorem kFinite (hIn : GenusIn σ (1 : Matrix (Fin k) (Fin k) E)) :
    KFinite σ (1 : Matrix (Fin k) (Fin k) E) := by
  have h1 := finite_classSet σ hσ (stdForm E k) (Formalism.MainNotions.Gaps.MI.stdForm_isSymm E k)
    (Formalism.MainNotions.Gaps.MI.stdForm_def E hc k) (stdLat E k) (Formalism.MainNotions.Gaps.MI.stdLat_isLattice' E k)
  have h2 := finite_stabAt σ hσ (stdForm E k) (Formalism.MainNotions.Gaps.MI.stdForm_isSymm E k)
    (Formalism.MainNotions.Gaps.MI.stdForm_def E hc k) (stdLat E k) (Formalism.MainNotions.Gaps.MI.stdLat_isLattice' E k)
  rw [gram_stdForm] at h1 h2
  exact ⟨h1 hIn, h2⟩

include hσ hc in
theorem massSum (hIn : GenusIn σ (1 : Matrix (Fin k) (Fin k) E))
    (hSurj : GenusSurj σ (1 : Matrix (Fin k) (Fin k) E)) :
    MassSum σ (1 : Matrix (Fin k) (Fin k) E) := by
  have h1 := mass_eq_sum σ hσ (stdForm E k) (Formalism.MainNotions.Gaps.MI.stdForm_isSymm E k)
    (Formalism.MainNotions.Gaps.MI.stdForm_def E hc k) (stdLat E k) (Formalism.MainNotions.Gaps.MI.stdLat_isLattice' E k)
  rw [gram_stdForm] at h1
  exact h1 hIn hSurj

include hσ hc in

theorem kFinite_std (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (hθ : ∃ θ, σ θ ≠ θ) :
    KFinite σ (1 : Matrix (Fin k) (Fin k) E) :=
  kFinite σ hσ hc (Formalism.MainNotions.Gaps.CC.WA.genusIn σ hσ hfix hθ)

include hσ hc in

theorem massSum_std (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (hθ : ∃ θ, σ θ ≠ θ) :
    MassSum σ (1 : Matrix (Fin k) (Fin k) E) :=
  massSum σ hσ hc (Formalism.MainNotions.Gaps.CC.WA.genusIn σ hσ hfix hθ) (Formalism.MainNotions.Gaps.CC.Surj.genusSurj σ hσ hfix)

end Std

end Formalism.MainNotions.Gaps.CC.Stab
