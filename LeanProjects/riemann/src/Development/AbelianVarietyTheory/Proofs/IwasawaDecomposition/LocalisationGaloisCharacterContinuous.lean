import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCont

open IsLocalRing

theorem continuous_of_le_comap {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (h : maximalIdeal A ≤ (maximalIdeal B).comap φ) : Continuous φ := by
  apply continuous_of_continuousAt_zero φ.toAddMonoidHom
  rw [isAdic_iff] at hA hB
  intro s hs
  simp only [map_zero] at hs
  obtain ⟨n, hn⟩ := hB.2 s hs
  have h1 : ((maximalIdeal A ^ n : Ideal A) : Set A) ∈ nhds (0 : A) :=
    (hA.1 n).mem_nhds (Ideal.zero_mem _)
  refine Filter.mem_map.2 (Filter.mem_of_superset h1 fun a ha => hn ?_)
  have : (maximalIdeal A ^ n).map φ ≤ maximalIdeal B ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h) n
  exact this (Ideal.mem_map_of_mem φ ha)

theorem comap_maximalIdeal_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : (maximalIdeal O).comap (algebraMap ℤ_[p] O) = maximalIdeal ℤ_[p] :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal O))

theorem p_mem_maximalIdeal {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : ((p : ℕ) : O) ∈ maximalIdeal O := by
  have hp : ((p : ℕ) : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  rw [← comap_maximalIdeal_padicInt O] at hp
  simpa using hp

theorem le_comap_of_padicInt {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [IsLocalRing A] [Algebra ℤ_[p] A]
    [Module.Finite ℤ_[p] A] [CommRing B] [IsLocalRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] (φ : A →+* B)
    (hφ : ∀ z, φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[p] B z) : maximalIdeal A ≤ (maximalIdeal B).comap φ := by
  have hc : ((maximalIdeal B).comap φ).comap (algebraMap ℤ_[p] A) = maximalIdeal ℤ_[p] := by
    rw [Ideal.comap_comap, ← comap_maximalIdeal_padicInt B]
    congr 1
    exact RingHom.ext hφ
  haveI : ((maximalIdeal B).comap φ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[p]) _ (by rw [hc]; infer_instance)
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem continuous_of_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p = q) {A B : Type} [CommRing A] [IsLocalRing A]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] [IsLocalRing B]
    [Algebra ℤ_[q] B] [Module.Finite ℤ_[q] B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[q] B z') : Continuous φ := by
  subst hpq
  exact continuous_of_le_comap hA hB φ (le_comap_of_padicInt φ fun z => hφ z z HEq.rfl)

theorem continuous_algebraMap_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] [TopologicalSpace O] [IsTopologicalRing O] (hO : IsAdic (maximalIdeal O)) :
    Continuous (algebraMap ℤ_[p] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[p] O) ?_
  rw [ContinuousAt, map_zero, hO.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[p]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (p_mem_maximalIdeal O) n)

section Units

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem continuous_units {O : Type} [Monoid O] [TopologicalSpace O] (φ : Γ →* Oˣ)
    (h : Continuous fun g => (φ g : O)) : Continuous φ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have : (fun g => ((φ g)⁻¹ : Oˣ).val) = fun g => (φ g⁻¹ : O) := by
    funext g; rw [map_inv]
  rw [this]
  exact h.comp continuous_inv

theorem continuous_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B] (f : A →* B)
    (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

theorem continuous_of_isOpen_ker {N : Type} [Group N] [TopologicalSpace N] (φ : Γ →* N)
    (h : IsOpen (φ.ker : Set Γ)) : Continuous φ := by
  refine IsLocallyConstant.continuous fun s => ?_
  have e : φ ⁻¹' s = ⋃ x ∈ φ ⁻¹' s, (fun g => x⁻¹ * g) ⁻¹' (φ.ker : Set Γ) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_iUnion, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, exists_prop]
    constructor
    · intro hg; exact ⟨g, hg, inv_mul_cancel _⟩
    · rintro ⟨x, hx, hxg⟩
      rw [inv_mul_eq_one] at hxg
      rwa [← hxg]
  rw [e]
  exact isOpen_biUnion fun x _ => h.preimage (continuous_const.mul continuous_id)

end Units

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem chiN_continuous : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0), (∀ j w, TwAlgAt C X j w (twC j w)) → (∀ j w, IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om))) → ∀ (i : LocT (base M C hR X hS)) (c : ℕ), Continuous (fun g => ((chiN (base M C hR X hS) C (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i)) i c g : (OOf (base M C hR X hS) i)ˣ) : OOf (base M C hR X hS) i)) := by
  intro D M C hR X hS twC ψ0 hP htw hker i c
  have hadic : ∀ j w, IsAdic (maximalIdeal (OcC X j w)) := oc_adic X
  have htwc : ∀ j w, Continuous (twC j w) := fun j w =>
    continuous_of_heq (C.twI_l w) (D.ntw.twistBaseCoefficientRing_isAdic (C.twI w)) (hadic j w) (twC j w) (htw j w)
  have h1 : Continuous (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i)
      (C.sd (wOf (base M C hR X hS) i))) :=
    continuous_units _ (D.ntw.twistCharacterFamily_continuous _ _ _)
  have h2 : Continuous (psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)) :=
    continuous_of_isOpen_ker _ (hker _ _)
  have h3 : Continuous (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (htwc _ _)
  haveI : Fact (lOf (base M C hR X hS) i).Prime := ⟨D.what₂.places.resChar_prime _⟩
  letI : Algebra ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).algOc _ _
  haveI : Module.Finite ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).finOc _ _
  have h4 : Continuous (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (continuous_algebraMap_padicInt _ (hadic _ _))
  have h5 := continuous_cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i)
  refine Units.continuous_val.comp ?_
  change Continuous fun g =>
    ((show (OOf (base M C hR X hS) i)ˣ from (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom)
      (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i) (C.sd (wOf (base M C hR X hS) i)) g)) *
      (show (OOf (base M C hR X hS) i)ˣ from psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i) g)) *
    (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom
      (cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i) g)) ^ (-((c : ℤ) - 1))
  exact ((h3.comp h1).mul h2).mul ((h4.comp h5).zpow _)

end GlobalTheory.HeckeLocCont
