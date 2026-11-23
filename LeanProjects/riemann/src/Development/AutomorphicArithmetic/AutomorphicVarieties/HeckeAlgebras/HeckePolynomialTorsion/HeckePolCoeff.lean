import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.KerTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.KillsLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.OElRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FormRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.PolarInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.PolarIffLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
import Mathlib.RingTheory.Teichmuller
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeckePolMap
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.AlgebraTools.Det
open UpperTheory.V.HV (Coef)

namespace UpperTheory.V.Hi.JEx

theorem rels {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R]
    [Algebra O R] {n : ℕ} (D : GDet n R F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Rˣ) {X : Type} (K : Type) [CommRing K]
    [Algebra O K] (f : X → R →ₐ[O] K) (ρ : X → F.G₀ →* GL (Fin n) K) (hsep : ∀ a, (∀ x, f x a = 0) → a = 0)
    (hD : ∀ x, D.map (f x : R →+* K) = GDet.ofRep (mat (ρ x))) (hP : ∀ x, ∃ P, F.IsForm O n (ρ x) P)
    (hfl : ∀ x v, HasFlag ((ρ x).comp (F.φ v)) fun i => pushCh (f x : R →+* K) (ψ v i)) :
    F.IsPolar O D ∧ (∀ v g, D.Kills (F.oEl v (ψ v) g)) ∧
      ∀ g, (∀ x, ρ x g = 1) → D.Kills (MonoidAlgebra.single g 1 - 1) := by
  have kt := kerTest (fun _ : X => K) (fun x => (f x : R →+* K)) (fun x => mat (ρ x)) D hsep hD
  refine ⟨polarInj F O R n D (fun _ : X => K) f hsep fun x => ?_, fun v g => kt _ fun x => ?_, fun g hg => kt _ fun x => ?_⟩
  · obtain ⟨P, hP⟩ := hP x
    rw [hD]
    intro B _ _ _ _ y
    exact (formRep F O K n (ρ x) P hP).2.2 B y
  · rw [← oElRep F O K n (ρ x) v _ (hfl x v) g]
    congr 1
    simp [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def]
  · simp [GDet.repAlg, mat, hg x]

theorem teich {l : ℕ} [hl : Fact l.Prime] {F : GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1 := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  haveI : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
  let j : ResidueField c.O →+* Perfection (c.O ⧸ maximalIdeal c.O) l :=
    Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O) (RingHom.id (ResidueField c.O))
  have hj : ∀ x, Perfection.coeff (c.O ⧸ maximalIdeal c.O) l 0 (j x) = x := fun x =>
    RingHom.congr_fun ((Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)).symm_apply_apply
      (RingHom.id (ResidueField c.O))) x
  let τ : ResidueField c.O →* c.O := (Perfection.teichmuller l (maximalIdeal c.O)).comp j
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨(Perfection.mk_teichmuller (j _)).trans (hj _), ?_⟩,
    fun i g hg => by rw [MonoidHom.comp_apply, hg, map_one]⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]

theorem res_lc {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [TopologicalSpace Γ] {f : Γ → R}
    (hf : AdicCont (maximalIdeal R) f) : IsLocallyConstant fun g => res O R (f g) := by
  have hk : ∀ a ∈ maximalIdeal R ^ 1, (res O R : R →+* ResidueField O) a = 0 := fun a ha =>
    (res_eq_zero_iff O R a).2 (by simpa using ha)
  exact (hf 1).comp (Ideal.Quotient.lift _ (res O R : R →+* ResidueField O) hk)

theorem cont_map {O R R' Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R']
    [IsCO O R'] [TopologicalSpace Γ] (φ : R →ₐ[O] R') {f : Γ → R} (hf : AdicCont (maximalIdeal R) f) :
    AdicCont (maximalIdeal R') fun g => φ (f g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (φ : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show φ y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hf N).comp (Ideal.quotientMap _ (φ : R →+* R') hle)

theorem lc_of_open {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B] (χ : Γ →* B)
    (h : IsOpen (χ.ker : Set Γ)) : IsLocallyConstant χ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker χ h

theorem red_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid F O n) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R F.G₀) (hD : D.IsCont (maximalIdeal R))
    (S : Set F.G₀) (hS : Dense S)
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map (res O R : R →+* ResidueField O) = r.Dbar.chi (MonoidAlgebra.single g 1)) :
    D.map (res O R : R →+* ResidueField O) = r.Dbar := by
  letI : TopologicalSpace (ResidueField O) := ⊥
  haveI : DiscreteTopology (ResidueField O) := ⟨rfl⟩
  refine extDense _ _ S hS (fun i _ => ?_) (fun i _ => repCont _ ?_ i) fun g hg => ?_
  · simp only [(mapApi D _).2.2.1]
    exact (res_lc (hD i)).continuous
  · refine Continuous.matrix_diagonal (continuous_pi fun i => IsLocallyConstant.continuous ?_)
    exact (lc_of_open _ (r.chib_open i)).comp Units.val
  · rw [← h g hg, ← (mapApi D _).1]
    simp

theorem heckePol_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) :
    (heckePol n q a).map f = heckePol n q fun j => f (a j) :=
  _root_.UpperTheory.Reformulated.B.Qk6.heckePol_map f n q a

theorem heckePol_coeff {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (j : ℕ) (hj : j ≤ n) :
    (-1) ^ j * (heckePol n q a).coeff (n - j) = (q : A) ^ (j * (j - 1) / 2) * a j := by
  rw [heckePol, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul, coeff_X_pow_self, mul_one, mul_assoc, ← mul_assoc, ← mul_pow]
    simp
  · intro i hi hij
    rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
    have := Finset.mem_range.1 hi
    omega
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

theorem eq_of_prod {C : Type} [CommGroup C] {n : ℕ} (x y : Fin n → C)
    (h : ∀ j, ∏ i with i ≤ j, x i = ∏ i with i ≤ j, y i) (j : Fin n) : x j = y j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have e : (Finset.univ.filter fun i : Fin n => i ≤ j) = insert j (Finset.univ.filter fun i => i < j) := by
      ext i
      simp [le_iff_eq_or_lt]
    have h1 := h j
    rw [e, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_congr rfl fun i hi => ih i (Finset.mem_filter.1 hi).2] at h1
    exact mul_right_cancel h1

end UpperTheory.V.Hi.JEx
