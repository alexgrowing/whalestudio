import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.HRatInvOfTriv
import Formalism.LocalRingCardinality.Lemmas

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems NumberField IsDedekindDomain

section Gen

variable {LL Kf : Type} [Field LL] [Field Kf] (e : LL →+* Kf)
variable {V W T : Type} [AddCommGroup V] [Module LL V] [AddCommGroup W] [Module Kf W]
  (ev : T → W →ₗ[Kf] Kf) (φ : V →+ W)

theorem span_inv (hsep : ∀ F : W, (∀ t, ev t F = 0) → F = 0)
    (hsm : ∀ (a : LL) x, φ (a • x) = e a • φ x) (hval : ∀ x, IsRat e ev (φ x))
    (S : Set (W →ₗ[Kf] W)) (hT : ∀ Tm ∈ S, ∀ x, ∃ y, φ y = Tm (φ x))
    {ξ : W} (hξ : ξ ∈ Submodule.span Kf (Set.range φ)) (hinv : ∀ Tm ∈ S, Tm ξ = ξ) :
    ξ ∈ Submodule.span Kf (φ '' {x | ∀ Tm ∈ S, Tm (φ x) = φ x}) := by
  let _ : Algebra LL Kf := e.toAlgebra
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hξ
  set C : Submodule LL Kf := Submodule.span LL (Set.range fun x : c.support => c x) with hC
  have : FiniteDimensional LL C := FiniteDimensional.span_of_finite LL (Set.finite_range _)
  let κ := Module.finBasis LL C
  have hext : ∀ j, ∃ g : Kf →ₗ[LL] LL, g.comp C.subtype = κ.coord j := fun j => LinearMap.exists_extend (κ.coord j)
  choose π hπ using hext
  have hcx : ∀ x ∈ c.support, c x = ∑ j, e (π j (c x)) * (κ j : Kf) := by
    intro x hx
    have hmem : c x ∈ C := Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    have h1 := κ.sum_repr ⟨c x, hmem⟩
    have h2 : ∀ j, π j (c x) = κ.repr ⟨c x, hmem⟩ j := fun j => by
      have := LinearMap.congr_fun (hπ j) ⟨c x, hmem⟩
      simpa using this
    conv_lhs => rw [show c x = ((⟨c x, hmem⟩ : C) : Kf) from rfl, ← h1]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2, Submodule.coe_smul, Algebra.smul_def]
    rfl
  let ξj : Fin (Module.finrank LL C) → V := fun j => c.sum fun x a => π j a • x
  have hdec : (c.sum fun x a => a • φ x) = ∑ j, (κ j : Kf) • φ (ξj j) := by
    simp only [ξj, Finsupp.sum, map_sum, hsm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    have h1 : c x • φ x = ∑ j, ((κ j : Kf) * e (π j (c x))) • φ x := by
      conv_lhs => rw [hcx x hx]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
    exact h1
  rw [hdec]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ξj j, ?_, rfl⟩)
  intro Tm hTm

  choose y hy using hT Tm hTm
  have hzero : ∑ j, (κ j : Kf) • φ (y (ξj j) - ξj j) = 0 := by
    simp only [map_sub, hy, smul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ x, (κ x : Kf) • Tm (φ (ξj x)) = Tm (∑ x, (κ x : Kf) • φ (ξj x)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun x _ => (map_smul Tm _ _).symm
    rw [h2, ← hdec, hinv Tm hTm, sub_self]
  have hli : LinearIndependent LL fun j => (κ j : Kf) :=
    κ.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
  have hφz : φ (y (ξj j) - ξj j) = 0 := by
    refine hsep _ fun t => ?_
    choose q hq using fun j' => hval (y (ξj j') - ξj j') t
    have h3 := congrArg (ev t) hzero
    rw [map_sum, map_zero] at h3
    simp only [map_smul, smul_eq_mul, ← hq] at h3
    have h4 : ∑ j', q j' • (κ j' : Kf) = 0 := by
      rw [← h3]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [Algebra.smul_def, mul_comm]
      rfl
    have h5 := Fintype.linearIndependent_iff.1 hli q h4 j
    rw [← hq, h5, map_zero]
  rw [map_sub, sub_eq_zero, hy] at hφz
  exact hφz

end Gen

section Inv

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] [NumberField LL] (e : LL →+* G.Kf)

def evX (m : (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) →₀ ℕ) :
    G.P.Xsp →ₗ[G.Kf] G.Kf := MvPolynomial.lcoeff G.Kf m

theorem evX_sep (F : G.P.Xsp) (h : ∀ m, evX G m F = 0) : F = 0 := by
  exact MvPolynomial.ext F 0 fun m => by simpa [evX] using h m

theorem map_e_smul (a : LL) (Q : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :
    MvPolynomial.map e (a • Q) = e a • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem map_e_rat (Q : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :
    IsRat e (evX G) (MvPolynomial.map e Q) := fun m => ⟨Q.coeff m, by simp [evX, MvPolynomial.coeff_map]⟩

theorem inv_span [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (hA : RatActG G e) (i : G.comp) (L0 : G.P.Tup) (hB : RatBasisAt G e L0)
    (ξ : G.P.Xsp) (hξ : ξ ∈ G.P.HtupW L0) (hI : InvAt G i L0 ξ) :
    ξ ∈ Submodule.span G.O {ξ' | ξ' ∈ G.P.HtupW L0 ∧ InvAt G i L0 ξ' ∧ RatX G e ξ'} := by
  let φ : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL →+ G.P.Xsp :=
    (MvPolynomial.map e).toAddMonoidHom
  have hφ : ∀ (a : LL) Q, φ (a • Q) = e a • φ Q := map_e_smul G e

  let Lr : Submodule (𝓞 LL) (MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :=
    { carrier := {Q | MvPolynomial.map e Q ∈ G.P.HtupW L0}
      add_mem' := by
        intro Q Q' h h'
        simp only [Set.mem_ofPred_eq, map_add] at h h' ⊢
        exact Submodule.add_mem _ h h'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := by
        intro a Q h
        simp only [Set.mem_ofPred_eq] at h ⊢
        obtain ⟨o, ho⟩ := (hσ (algebraMap (𝓞 LL) LL a)).1 (w.valuation_le_one a)
        have : MvPolynomial.map e (a • Q) = o • MvPolynomial.map e Q := by
          rw [← algebraMap_smul G.Kf o, ho, ← map_e_smul G e, algebraMap_smul]
          rfl
        convert Submodule.smul_mem _ o h using 1
        exact this }

  let Ur : Submodule LL (MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :=
    { carrier := {Q | InvAt G i L0 (MvPolynomial.map e Q)}
      add_mem' := fun {Q Q'} h h' γ hγ => by
        rw [map_add, map_add, smul_add, h γ hγ, h' γ hγ]
      zero_mem' := fun γ _ => by rw [map_zero, map_zero, smul_zero]
      smul_mem' := fun a Q h γ hγ => by
        show ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (MvPolynomial.map e (a • Q)) = MvPolynomial.map e (a • Q)
        rw [map_e_smul, map_smul, smul_comm, h γ hγ] }

  have h1 : ξ ∈ Submodule.span G.O (φ '' (Lr : Set _)) := by
    refine Submodule.span_mono ?_ (htupW_rat G e L0 hB hξ)
    rintro _ ⟨hx, Q, rfl⟩
    exact ⟨Q, hx, rfl⟩

  let S : Set (G.P.Xsp →ₗ[G.Kf] G.P.Xsp) := {Tm | ∃ γ : (G.lev i).Γ, (G.lev i).smul γ L0 = L0 ∧
    Tm = (algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)) • (G.lev i).actX γ}
  have hTm : ∀ γ (X : G.P.Xsp), ((algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)) • (G.lev i).actX γ) X =
      ((G.lev i).χ γ : G.O) • (G.lev i).actX γ X := fun γ X => by
    rw [LinearMap.smul_apply, algebraMap_smul]
  have h2 : ξ ∈ Submodule.span G.Kf (φ '' (Ur : Set _)) := by
    have hspan : ξ ∈ Submodule.span G.Kf (Set.range φ) := by
      have : Submodule.span G.O (φ '' (Lr : Set _)) ≤ (Submodule.span G.Kf (Set.range φ)).restrictScalars G.O := by
        rw [Submodule.span_le]
        rintro _ ⟨Q, _, rfl⟩
        exact Submodule.subset_span ⟨Q, rfl⟩
      exact this h1
    have := span_inv e (evX G) φ (evX_sep G) hφ (map_e_rat G e) S (by
        rintro Tm ⟨γ, _, rfl⟩ Q
        obtain ⟨Q', hQ'⟩ := hA i γ (MvPolynomial.map e Q) ⟨Q, rfl⟩
        exact ⟨Q', by rw [hTm]; exact hQ'⟩)
      hspan (by
        rintro Tm ⟨γ, hγ, rfl⟩
        rw [hTm]; exact hI γ hγ)
    refine Submodule.span_mono ?_ this
    rintro _ ⟨Q, hQ, rfl⟩
    refine ⟨Q, fun γ hγ => ?_, rfl⟩
    have := hQ _ ⟨γ, hγ, rfl⟩
    rw [hTm] at this
    exact this

  have hb : LinearIndependent G.Kf (φ ∘ (MvPolynomial.basisMonomials _ LL)) := by
    have e1 : φ ∘ (MvPolynomial.basisMonomials _ LL) = MvPolynomial.basisMonomials _ G.Kf := by
      funext m
      simp [φ, MvPolynomial.coe_basisMonomials]
    rw [e1]
    exact (MvPolynomial.basisMonomials _ G.Kf).linearIndependent
  have h3 := (Formalism.BasicNotions.FBC.flat_ext w e hσ φ hφ (MvPolynomial.basisMonomials _ LL) hb).2 Lr Ur
  have h4 : ξ ∈ Submodule.span G.O (φ '' ((Lr ⊓ Ur.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) _) : Set _)) := by
    rw [← h3]
    exact ⟨h1, h2⟩
  refine Submodule.span_mono ?_ h4
  rintro _ ⟨Q, ⟨hQ1, hQ2⟩, rfl⟩
  exact ⟨hQ1, hQ2, Q, rfl⟩

theorem hRatInv_of [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (hA : RatActG G e) (hB : RatBasis G e) : HRatInv G e :=
  fun i L0 hL0 ξ hξ => inv_span G e w hσ hA i L0 (hB L0 hL0) ξ hξ.1 hξ.2

theorem mRatSpan_of_rat_inv [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (h2 : G.FinClasses) (hL : RatLev G e) (hB : RatBasis G e) :
    MRatSpan G.P G.comp e G.M :=
  mRatSpan_inv G e h2 (Formalism.L2.G.Cmp.equivSys_HtupW G) (ratActG_of G e hL) (hRatInv_of G e w hσ (ratActG_of G e hL) hB)

end Inv

end Formalism.L2.G.Cmp
