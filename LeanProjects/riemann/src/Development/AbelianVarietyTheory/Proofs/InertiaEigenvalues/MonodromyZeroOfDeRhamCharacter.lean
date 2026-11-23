import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.TypeInertia

variable {D : D7}

theorem cont_iotaOQ (hPH : tiePH (D := D)) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Continuous (iotaOQ D.nd D.naut i) := by
  have h : (iotaOQ D.nd D.naut i : D.nd.O i → Qbar (D.nd.l i)) =
      fun x => (((D.nbr i w hw).toLL x : ↥(D.nbr i w hw).LL.1) : Loc.Om (D.nd.l i)) :=
    funext (hPH i w hw).1
  rw [h]
  exact continuous_subtype_val.comp (continuous_subtype_val.comp (D.nbr i w hw).eO_cont)

theorem cont_mapRep (hPH : tiePH (D := D)) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (D.nd.O i))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) (D.nd.O i)) : Matrix (Fin a) (Fin a) (D.nd.O i))) :
    Continuous fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin a) (Qbar (D.nd.l i))) :
      Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) :=
  hc.matrix_map (cont_iotaOQ hPH i w hw)

theorem potCrys_of (h0 : SumRepresentations.tie0 D) (hPH : tiePH (D := D)) (i : D.nd.Loc)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {a : ℕ}
    (ρ : GE D.nd →* GL (Fin a) (D.nd.O i))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) (D.nd.O i)) : Matrix (Fin a) (Fin a) (D.nd.O i)))
    (hdR : D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) ρ) w)
    (hm : D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) w)) :
    Br.IsPotCrysW D.loc D.nbr i w hw ρ := by
  have hQ := (h0.2.2.2.1 i a _ w hw (cont_mapRep hPH i w hw ρ hc)).2 ⟨hdR, hm⟩
  exact ((hPH i w hw).2.1 a ρ hc).2.2.1.1 hQ

theorem cont_chiGL (i : D.nd.Loc) :
    Continuous fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
  have h := D.nd.chi_cont i 1
  have e : (fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i))) =
      fun g => Matrix.scalar (Fin 1) ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) := by
    funext g; rfl
  rw [e]
  exact Continuous.matrix_diagonal (continuous_pi fun _ => h)

theorem twGL_one_chi {k : Type} [Field k] {Γ : Type} [Group Γ] (χ : Γ →* GL (Fin 1) k) :
    SumRepresentations.At.twGL (1 : Γ →* GL (Fin 1) k) (Matrix.GeneralLinearGroup.det.comp χ) = χ := by
  ext g a b
  fin_cases a; fin_cases b
  simp [SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_matrix_apply]

theorem mapRep_one {A B : Type} [CommRing A] [CommRing B] {Γ : Type} [Group Γ] {a : ℕ} (f : A →+* B) :
    mapRep f (1 : Γ →* GL (Fin a) A) = 1 := by
  ext g x y
  simp [mapRep]

theorem crys_one (hPH : tiePH (D := D)) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    D.naut.IsCrysW i (1 : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) w := by
  have hc : Continuous fun g => (((1 : GE D.nd →* GL (Fin 1) (D.nd.O i)) g : GL (Fin 1) (D.nd.O i)) :
      Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by simpa using continuous_const
  have h := ((hPH i w hw).2.1 1 (1 : GE D.nd →* GL (Fin 1) (D.nd.O i)) hc).1.2
  rw [mapRep_one] at h
  apply h
  haveI := (D.nbr i w hw).LL.2
  show IsCrys _ _
  exact GlobalTheory.TrivCrys.isCrys_of_trivial _ _ (fun g x => by simp [LocBridge.rep])

theorem monodromy_zero_of_deRham_character (h0 : SumRepresentations.tie0 D) (hPH : tiePH (D := D)) (i : D.nd.Loc)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i)))
    (hc : Continuous fun g => ((χ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))))
    (hdR : D.naut.IsdRW i χ w) : D.naut.mono0 (D.naut.wdOf i χ w) := by
  have h1c : SumRepresentations.At.ContQ D.nd i (1 : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) := by
    unfold SumRepresentations.At.ContQ; simpa using continuous_const
  have hcr := (h0.2.2.1 i 1 1 w hw h1c).1 (crys_one hPH i w hw)
  have hm1 : D.naut.mono0 (D.naut.wdOf i (1 : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) w) :=
    D.naut.unr_mono0 _ hcr.2
  have htw := ((h0.2.2.2.2.2 i).2.2.2 1 1 χ h1c hc).2.1 w (Or.inr hcr.1) (Or.inr hdR)
  rw [twGL_one_chi] at htw
  rw [htw, D.naut.monomial_char_iff _ _ (D.naut.wdOf_dim i χ w)]
  exact hm1

section Alg

variable {g : ℕ} [hg : Fact g.Prime]

theorem sub_one_dvd_card_GL {r a : ℕ} (ha : 1 ≤ a) (har : a ≤ r) :
    g ^ a - 1 ∣ Nat.card (GL (Fin r) (ZMod g)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  have hmem : (⟨r - a, by omega⟩ : Fin r) ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ _
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
  refine ⟨g ^ (r - a), ?_⟩
  simp only
  have e : g ^ r = g ^ a * g ^ (r - a) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.sub_mul, one_mul, mul_comm]

theorem pow_card_GL_eq_one {r : ℕ} (hr : 1 ≤ r) {y : Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {p : (ZMod g)[X]}
    (hp : p ≠ 0) (hd : p.natDegree ≤ r) (hroot : aeval y p = 0) :
    y ^ Nat.card (GL (Fin r) (ZMod g)) = 1 := by
  set K := IntermediateField.adjoin (ZMod g) ({y} : Set (Formalism.CyclotomicNorms.Fbar g))
  have hint : IsIntegral (ZMod g) y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  set a := Module.finrank (ZMod g) K
  have ha : a = (minpoly (ZMod g) y).natDegree := IntermediateField.adjoin.finrank hint
  have hda : a ≤ r := by
    rw [ha]
    have := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (ZMod g) y hp hroot)
    omega
  have ha1 : 1 ≤ a := Module.finrank_pos
  have hcard : Fintype.card K = g ^ a := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  let y' : K := ⟨y, IntermediateField.mem_adjoin_simple_self _ _⟩
  have hy' : y' ≠ 0 := fun h => hy (congrArg Subtype.val h)
  have h1 : y' ^ (g ^ a - 1) = 1 := by
    rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one y' hy'
  obtain ⟨m, hm⟩ := sub_one_dvd_card_GL (g := g) ha1 hda
  rw [hm, pow_mul]
  have : y ^ (g ^ a - 1) = 1 := congrArg Subtype.val h1
  rw [this, one_pow]

def ySet (S : (ZMod g)[X]) (c : (ZMod g)ˣ) : Finset (Formalism.CyclotomicNorms.Fbar g) :=
  (Formalism.CyclotomicNorms.rootsBar S).toFinset ∪
    {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (c : ZMod g), algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((c⁻¹ : (ZMod g)ˣ) : ZMod g)}

theorem mem_rootsBar {S : (ZMod g)[X]} (hS : S ≠ 0) {y : Formalism.CyclotomicNorms.Fbar g} :
    y ∈ Formalism.CyclotomicNorms.rootsBar S ↔ aeval y S = 0 := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.mem_roots', Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
  exact ⟨fun h => h.2, fun h => ⟨(Polynomial.map_ne_zero_iff (algebraMap (ZMod g) _).injective).2 hS, h⟩⟩

theorem alg_spec {r N : ℕ} (hr : 1 ≤ r) (hN : Nat.card (GL (Fin r) (ZMod g)) ∣ N) (x : ZMod g) (hx : x ≠ 0) :
    algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) x ≠ 0 ∧ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) x) ^ N = 1 := by
  have h0 : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) x ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap (ZMod g) _).injective]; exact hx
  refine ⟨h0, ?_⟩
  obtain ⟨m, rfl⟩ := hN
  rw [pow_mul, pow_card_GL_eq_one hr h0 (X_sub_C_ne_zero x) (by rw [natDegree_X_sub_C]; exact hr)
    (by rw [map_sub, aeval_X, aeval_C, sub_self]), one_pow]

theorem ySet_spec {r N : ℕ} (hr : 1 ≤ r) (hN : Nat.card (GL (Fin r) (ZMod g)) ∣ N) {S : (ZMod g)[X]}
    (hS : S ≠ 0) (hS0 : S.coeff 0 ≠ 0) (hSd : S.natDegree ≤ r) (c : (ZMod g)ˣ) :
    ∀ y ∈ ySet S c, y ≠ 0 ∧ y ^ N = 1 := by
  intro y hy
  rw [ySet, Finset.mem_union, Multiset.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy | rfl | rfl
  · rw [mem_rootsBar hS] at hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [← Polynomial.coeff_zero_eq_aeval_zero', map_eq_zero_iff _ (algebraMap (ZMod g) _).injective] at hy
      exact hS0 hy
    refine ⟨hy0, ?_⟩
    obtain ⟨m, rfl⟩ := hN
    rw [pow_mul, pow_card_GL_eq_one hr hy0 hS hSd hy, one_pow]
  · exact alg_spec hr hN _ c.ne_zero
  · exact alg_spec hr hN _ (c⁻¹).ne_zero

theorem ySet_card {r : ℕ} {S : (ZMod g)[X]} (hSd : S.natDegree ≤ r) (c : (ZMod g)ˣ) :
    (ySet S c).card ≤ r + 2 := by
  unfold ySet
  refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
  · refine (Multiset.toFinset_card_le _).trans ?_
    unfold Formalism.CyclotomicNorms.rootsBar
    refine (Polynomial.card_roots' _).trans ?_
    rw [Polynomial.natDegree_map]; exact hSd
  · exact (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])

theorem alg_mem_ySet (S : (ZMod g)[X]) {c u : (ZMod g)ˣ} (hu : u = c ∨ u = c⁻¹) :
    algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (u : ZMod g) ∈ ySet S c := by
  unfold ySet
  refine Finset.mem_union_right _ ?_
  rcases hu with rfl | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem root_mem_ySet {S : (ZMod g)[X]} (hS : S ≠ 0) {c u : (ZMod g)ˣ} (hu : u = c ∨ u = c⁻¹) (t : ℕ)
    {y : Formalism.CyclotomicNorms.Fbar g} (hy : y ∈ Formalism.CyclotomicNorms.rootsBar (S * (X - C (u : ZMod g)) ^ t)) : y ∈ ySet S c := by
  have hne : S * (X - C (u : ZMod g)) ^ t ≠ 0 := mul_ne_zero hS (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [mem_rootsBar hne, map_mul, map_pow, mul_eq_zero] at hy
  rcases hy with hy | hy
  · unfold ySet
    exact Finset.mem_union_left _ (Multiset.mem_toFinset.2 ((mem_rootsBar hS).2 hy))
  · have h1 : aeval y (X - C (u : ZMod g)) = 0 := by
      by_contra hne; exact pow_ne_zero t hne hy
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
    rw [h1]; exact alg_mem_ySet S hu

theorem inv_mem_image {Y : Finset (Formalism.CyclotomicNorms.Fbar g)} {y : Formalism.CyclotomicNorms.Fbar g} (hy : y ∈ Y) :
    y⁻¹ ∈ Y.image (·⁻¹) := Finset.mem_image_of_mem _ hy

theorem image_spec {Y : Finset (Formalism.CyclotomicNorms.Fbar g)} {N : ℕ} (h : ∀ y ∈ Y, y ≠ 0 ∧ y ^ N = 1) :
    ∀ y ∈ Y.image (·⁻¹), y ≠ 0 ∧ y ^ N = 1 := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨h1, h2⟩ := h z hz
  exact ⟨inv_ne_zero h1, by rw [inv_pow, h2, inv_one]⟩

end Alg

theorem rootsBar_X_sub_C {g : ℕ} [Fact g.Prime] (a : ZMod g) :
    Formalism.CyclotomicNorms.rootsBar (X - C a) = {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) a} := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.roots_X_sub_C]

theorem inePol_char (P : Pend D) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hwk : w ∈ placesOver D.host.E (D.host.g k)) (L : D.naut.LP w) (a : ZMod (D.host.g k))
    (hlab : D.naut.items₂ k w L = X - C a) (hdim : D.naut.lpDim L = 1) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      D.naut.inePol L σ = X - C (P.om k w (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) a) σ) := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro σ hσ
  have h := P.inertiaCharpoly_eigenvalues k w hwk L (by rw [hlab, natDegree_X_sub_C, hdim]) σ hσ
  rw [h, hlab, rootsBar_X_sub_C, Multiset.map_singleton, Multiset.prod_singleton]

theorem inertial_chars : ∀ (D : D7) (P : Pend D), TypeLGC P → SumRepresentations.tie0 D → tiePH (D := D) → tieChi (D := D) →
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
  ∀ Xs : Set (D.nd.X i), TypeLocus P i k Xs →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
  ∃ (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))) (u : Fb (D.host.g k) (D.host.g_prime k)),
    u ∈ Y ∧ (∀ y ∈ Y, y ≠ 0 ∧ y ^ D.what₂.restRowsFiniteGroupCard = 1) ∧ Y.card ≤ D.R.nV + 1 ∧
    (∀ x ∈ Xs, Br.IsPotCrysW D.loc D.nbr i w hw (r x) ∧
      ∃ M : Multiset (Fb (D.host.g k) (D.host.g_prime k)), (∀ y ∈ M, y ∈ Y) ∧
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
            (M.map fun y => X - C (P.om k w y σ)).prod) ∧
    Br.IsPotCrysW D.loc D.nbr i w hw (chiGL i) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (chiGL i)) w) σ = X - C (P.om k w u σ) := by
  intro D P hLGC h0 hPH hChi i k hik r hr Xs hXs w hw
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hwk : w ∈ placesOver D.host.E (D.host.g k) := hik ▸ hw
  obtain ⟨v, hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hwk
  obtain ⟨s, hs, hx⟩ := hXs
  obtain ⟨S, hS0, hSc, hSd, hSx⟩ : ∃ S : (ZMod (D.host.g k))[X], S ≠ 0 ∧ S.coeff 0 ≠ 0 ∧
      S.natDegree ≤ D.R.r ∧ ∀ x ∈ Xs, S = s v := by
    by_cases hne : Xs.Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      obtain ⟨PI, -, hτ⟩ := hx x0 hx0
      obtain ⟨τ, -, hl⟩ := hτ v
      obtain ⟨hm, hd, hc⟩ := (P.lz k).lab_spec τ
      rw [hl] at hm hd hc
      exact ⟨s v, hm.ne_zero, hc, hd.le, fun _ _ => rfl⟩
    · exact ⟨1, one_ne_zero, by rw [coeff_one_zero]; exact one_ne_zero,
        by rw [natDegree_one]; exact Nat.zero_le _, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hr1 : 1 ≤ D.R.r := by have := D.R.two_le_m; unfold Ranks.r; omega
  have hN : Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ∣ D.what₂.restRowsFiniteGroupCard := by
    rw [D.nd.restN_card_levelGroup_eq]
    exact (dvd_pow_self _ (by unfold Ranks.f Ranks.n; positivity)).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
  have hcard : D.R.r + 2 ≤ D.R.nV + 1 := by
    have := D.R.rank_add_five_le; unfold Ranks.nV; unfold Ranks.r at *; omega
  have hY := GlobalTheory.TypeInertia.ySet_spec hr1 hN hS0 hSc hSd (PairedCharacterCondition.chiJ D i k v)
  have hYc := GlobalTheory.TypeInertia.ySet_card hSd (PairedCharacterCondition.chiJ D i k v)
  obtain ⟨u, hu, hχ⟩ := hChi i k hik v
  have hcχ := GlobalTheory.TypeInertia.cont_chiGL (D := D) i
  have hpt : ∀ x ∈ Xs, ∃ ux : (ZMod (D.host.g k))ˣ, (ux = PairedCharacterCondition.chiJ D i k v ∨ ux = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧
      ∀ M : Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k)),
        ((w = D.naut.plGw k v ∧ M = Formalism.CyclotomicNorms.rootsBar (S * (X - C (ux : ZMod (D.host.g k))) ^ D.R.t)) ∨
          (IsConjPl D.host (D.naut.plGw k v) w ∧
            M = (Formalism.CyclotomicNorms.rootsBar (S * (X - C (ux : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹))) →
        Br.IsPotCrysW D.loc D.nbr i w hw (r x) ∧
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
            (M.map fun y => X - C (P.om k w y σ)).prod := by
    intro x hxX
    obtain ⟨PI, hPI, hτ⟩ := hx x hxX
    obtain ⟨τ, hτk, hl⟩ := hτ v
    have hSv := hSx x hxX
    obtain ⟨ux, hux, hM⟩ := hLGC i k hik r hr x PI hPI v τ hτk (by rw [hl]; exact (hs v).1)
      (by rw [hl]; exact (hs v).2)
    refine ⟨ux, hux, fun M hMc => ?_⟩
    obtain ⟨hdR, hm0, hine⟩ := hM w M (by rw [hl, ← hSv]; exact hMc)
    exact ⟨GlobalTheory.TypeInertia.potCrys_of h0 hPH i w hw (r x) (hr x).1 hdR hm0, hine⟩
  have hchiQ : ∀ a : ZMod (D.host.g k), Br.IsdRW D.loc D.nbr i w hw (chiGL i) →
      D.naut.items₂ k w (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (chiGL i)) w) = X - C a →
      Br.IsPotCrysW D.loc D.nbr i w hw (chiGL i) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (chiGL i)) w) σ =
          X - C (P.om k w (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) a) σ) := by
    intro a hdR hlab
    have hdRQ := ((hPH i w hw).2.1 1 (chiGL i) hcχ).2.1.2 hdR
    refine ⟨GlobalTheory.TypeInertia.potCrys_of h0 hPH i w hw _ hcχ hdRQ
      (GlobalTheory.TypeInertia.monodromy_zero_of_deRham_character h0 hPH i w hw _ (GlobalTheory.TypeInertia.cont_mapRep hPH i w hw _ hcχ) hdRQ), ?_⟩
    exact GlobalTheory.TypeInertia.inePol_char P k w hwk _ a hlab (D.naut.wdOf_dim i _ w)
  rcases hv with hfix | hconj
  · obtain ⟨hdR, hlab⟩ := (hχ w hw).1 hfix
    refine ⟨GlobalTheory.TypeInertia.ySet S (PairedCharacterCondition.chiJ D i k v), algebraMap _ _ (u : ZMod (D.host.g k)),
      GlobalTheory.TypeInertia.alg_mem_ySet S hu, hY, hYc.trans hcard, ?_, hchiQ _ hdR hlab⟩
    intro x hxX
    obtain ⟨ux, hux, hpx⟩ := hpt x hxX
    exact ⟨(hpx _ (Or.inl ⟨hfix, rfl⟩)).1, _, fun y hy => GlobalTheory.TypeInertia.root_mem_ySet hS0 hux _ hy,
      (hpx _ (Or.inl ⟨hfix, rfl⟩)).2⟩
  · obtain ⟨hdR, hlab⟩ := (hχ w hw).2 hconj
    refine ⟨(GlobalTheory.TypeInertia.ySet S (PairedCharacterCondition.chiJ D i k v)).image (·⁻¹),
      algebraMap _ _ ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)), ?_,
      GlobalTheory.TypeInertia.image_spec hY, Finset.card_image_le.trans (hYc.trans hcard), ?_, hchiQ _ hdR hlab⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact GlobalTheory.TypeInertia.inv_mem_image (GlobalTheory.TypeInertia.alg_mem_ySet S hu)
    · intro x hxX
      obtain ⟨ux, hux, hpx⟩ := hpt x hxX
      refine ⟨(hpx _ (Or.inr ⟨hconj, rfl⟩)).1, _, fun y hy => ?_, (hpx _ (Or.inr ⟨hconj, rfl⟩)).2⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact GlobalTheory.TypeInertia.inv_mem_image (GlobalTheory.TypeInertia.root_mem_ySet hS0 hux _ hz)

end GlobalTheory.TypeInertia
