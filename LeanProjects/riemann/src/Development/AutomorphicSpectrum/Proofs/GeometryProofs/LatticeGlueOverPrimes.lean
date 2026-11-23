import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LatGlue

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem unitAt_nat_iff [CharZero Ω] (q : Cpt ξ) {n : ℕ} (hn : n ≠ 0) :
    unitAt ξ q (n : Ω) ↔ IsUnit (n : regAt ξ q) := by
  have hn' : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
  constructor
  · rintro ⟨-, -, hinv⟩
    refine IsUnit.of_mul_eq_one (⟨(n : Ω)⁻¹, hinv⟩ : regAt ξ q) (Subtype.ext ?_)
    show ((n : regAt ξ q) : Ω) * (n : Ω)⁻¹ = 1
    push_cast
    exact mul_inv_cancel₀ hn'
  · rintro ⟨u, hu⟩
    refine ⟨hn', natCast_mem _ n, ?_⟩
    have h1 : (n : Ω) * (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q) : Ω) = 1 := by
      have := congrArg (Subtype.val) (u.mul_inv)
      rw [hu] at this
      simpa using this
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact Subtype.property _

theorem not_inFibre_of_inFibre [CharZero Ω] (hξ : IsCptGen ξ) (q : Cpt ξ) {l l' : ℕ} (hl : l.Prime)
    (hl' : l'.Prime) (hne : l ≠ l') (h : InFibre ξ l q) : ¬ InFibre ξ l' q := by
  have hloc : IsLocalRing (regAt ξ q) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hξ q).1
  have hcop : IsCoprime (l : ℤ) (l' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl hl').2 hne)
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom (regAt ξ q))
  simp only [eq_intCast, Int.cast_natCast] at hab
  intro h'
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with hu | hu
  · exact h ((unitAt_nat_iff q hl.ne_zero).2 (isUnit_of_mul_isUnit_right hu))
  · exact h' ((unitAt_nat_iff q hl'.ne_zero).2 (isUnit_of_mul_isUnit_right hu))

theorem isUnit_nat_of_primes [CharZero Ω] (q : Cpt ξ) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ n : ℕ, n.Prime → n ∣ m → ¬ InFibre ξ n q) : IsUnit (m : regAt ξ q) := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one => simp
  | prime_mul p a hp ih =>
    have ha : a ≠ 0 := right_ne_zero_of_mul hm
    rw [Nat.cast_mul]
    refine IsUnit.mul ?_ (ih ha fun n hn hd => h n hn (Dvd.dvd.mul_left hd p))
    exact (unitAt_nat_iff q hp.ne_zero).1 (not_not.1 (h p hp (dvd_mul_right p a)))

theorem mem_regAt_of_mul [CharZero Ω] (q : Cpt ξ) {m' m : ℕ} (hm : m ≠ 0) (hd : m' ∣ m)
    (hu : ∀ n : ℕ, n.Prime → n ∣ m → ¬ InFibre ξ n q) {a : Ω} (ha : (m' : Ω) * a ∈ regAt ξ q) :
    a ∈ regAt ξ q := by
  obtain ⟨-, -, hinv⟩ := (unitAt_nat_iff q hm).2 (isUnit_nat_of_primes q m hm hu)
  obtain ⟨k, rfl⟩ := hd
  have hm' : ((m' * k : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hm
  have : a = ((m' * k : ℕ) : Ω)⁻¹ * ((k : Ω) * ((m' : Ω) * a)) := by
    field_simp
    push_cast at hm' ⊢
    field_simp
  rw [this]
  exact mul_mem hinv (mul_mem (natCast_mem _ k) ha)

theorem exists_open_avoid (P : Finset ℕ) (p : Cpt ξ) (h : ∀ n ∈ P, ¬ InFibre ξ n p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ n ∈ P, ¬ InFibre ξ n q := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ hn => absurd hn (Finset.notMem_empty _)⟩
  | insert a s _ ih =>
    obtain ⟨U, hU, HU⟩ := ih fun n hn => h n (Finset.mem_insert_of_mem hn)
    obtain ⟨U', hU', HU'⟩ := (regAt_unitAt_open X Ω ξ p (a : Ω)).2
      (not_not.1 (h a (Finset.mem_insert_self a s)))
    refine ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq n hn => ?_⟩
    rcases Finset.mem_insert.1 hn with rfl | hn
    · exact not_not.2 (HU' q hq.2)
    · exact HU q hq.1 n hn

theorem exists_matrix {r : ℕ} (b c : Fin r → E) (hc : LinearIndependent Ω c)
    (hs : Submodule.span Ω (Set.range b) ≤ Submodule.span Ω (Set.range c)) :
    ∃ A : Fin r → Fin r → Ω, (∀ i, b i = ∑ j, A i j • c j) ∧
      ∀ R : Subring Ω, (∀ i, b i ∈ Submodule.span R (Set.range c)) → ∀ i j, A i j ∈ R := by
  have h1 : ∀ i, ∃ f : Fin r → Ω, ∑ j, f j • c j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hs (Submodule.subset_span ⟨i, rfl⟩))
  choose A hA using h1
  refine ⟨A, fun i => (hA i).symm, fun R hR i j => ?_⟩
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hR i)
  have h0 : ∑ k, ((f k : Ω) - A i k) • c k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hA i, sub_eq_zero, ← hf]
    rfl
  have := Fintype.linearIndependent_iff.1 hc _ h0 j
  rw [← sub_eq_zero.1 this]
  exact (f j).2

theorem span_le_of_coeff {r : ℕ} (R : Subring Ω) (b c : Fin r → E) (A : Fin r → Fin r → Ω)
    (hb : ∀ i, b i = ∑ j, A i j • c j) (hA : ∀ i j, A i j ∈ R) :
    Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range c) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [hb i]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem _ (⟨A i j, hA i j⟩ : R) (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_nat_mul_mem [CharZero Ω] (hξ : IsCptGen ξ) (W : X.Opens) (hW : IsAffineOpen W) (a : Ω)
    (h : ∀ q : Cpt ξ, q.1 ∈ W → (∀ n : ℕ, n.Prime → ¬ InFibre ξ n q) → a ∈ regAt ξ q) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ W → (m : Ω) * a ∈ regAt ξ q := by
  by_cases hη : genPt ξ ∈ W
  swap
  · exact ⟨1, one_ne_zero, fun q hq => absurd (q.2.mem_open W.2 hq) hη⟩
  let φ : Γ(X, W) →+* Ω := (X.presheaf.germ W (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom
  have hφ : ∀ (q : Cpt ξ) (hq : q.1 ∈ W) (s : Γ(X, W)), genMap ξ q (X.presheaf.germ W q.1 hq s) = φ s :=
    fun q hq s => genMap_germ_eq_stalk_closed ξ q W hq hη s
  let D : Ideal Γ(X, W) :=
    { carrier := {s | ∃ t, φ s * a = φ t}
      add_mem' := by
        rintro x y ⟨t, ht⟩ ⟨u, hu⟩
        exact ⟨t + u, by rw [map_add, map_add, add_mul, ht, hu]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨t, ht⟩
        exact ⟨c * t, by rw [smul_eq_mul, map_mul, map_mul, _root_.mul_assoc, ht]⟩ }
  by_cases hD : ∃ n : ℕ, n ≠ 0 ∧ (n : Γ(X, W)) ∈ D
  · obtain ⟨n, hn, t, ht⟩ := hD
    refine ⟨n, hn, fun q hq => ?_⟩
    rw [map_natCast] at ht
    rw [ht, ← hφ q hq]
    exact ⟨_, rfl⟩
  exfalso
  let M : Submonoid Γ(X, W) :=
    { carrier := {x | ∃ n : ℕ, n ≠ 0 ∧ (n : Γ(X, W)) = x}
      one_mem' := ⟨1, one_ne_zero, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, rfl⟩ ⟨k, hk, rfl⟩
        exact ⟨n * k, mul_ne_zero hn hk, by simp⟩ }
  have hdisj : Disjoint (D : Set Γ(X, W)) M := by
    refine Set.disjoint_left.2 ?_
    rintro _ hx ⟨n, hn, rfl⟩
    exact hD ⟨n, hn, hx⟩
  obtain ⟨Q, hQ, hDQ, hQM⟩ := Ideal.exists_le_prime_disjoint D M hdisj
  let z : PrimeSpectrum Γ(X, W) := ⟨Q, hQ⟩
  have hxW : hW.fromSpec z ∈ W := by
    have := hW.range_fromSpec
    exact (Set.ext_iff.1 this _).1 ⟨z, rfl⟩
  let x : W := ⟨hW.fromSpec z, hxW⟩
  have hxz : hW.primeIdealOf x = z := by
    apply hW.fromSpec.isOpenEmbedding.injective
    exact hW.fromSpec_primeIdealOf x

  have hPD : (hW.primeIdealOf ⟨genPt ξ, hη⟩).asIdeal ≤ D := by
    intro s hs
    refine ⟨0, ?_⟩
    rw [map_zero]
    by_contra hne
    have hφs : φ s ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, hη⟩ : W)
    have hloc := hW.isLocalization_stalk ⟨genPt ξ, hη⟩
    have hu : IsUnit (algebraMap Γ(X, W) (X.presheaf.stalk (genPt ξ)) s) := by
      obtain ⟨y, hy⟩ := hξ.bij.2 (φ s)⁻¹
      refine IsUnit.of_mul_eq_one y (hξ.bij.1 ?_)
      refine ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).trans
        (Eq.trans ?_ ((Scheme.stalkClosedPointTo ξ).hom.map_one).symm)
      rw [hy]
      exact mul_inv_cancel₀ hφs
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (genPt ξ))
      (hW.primeIdealOf ⟨genPt ξ, hη⟩).asIdeal s).1 hu) hs
  have hspec : genPt ξ ⤳ x.1 := by
    have h1 : hW.primeIdealOf ⟨genPt ξ, hη⟩ ⤳ z :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (hPD.trans hDQ)
    have h2 := h1.map hW.fromSpec.continuous
    rwa [hW.fromSpec_primeIdealOf] at h2
  let q : Cpt ξ := ⟨x.1, hspec⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have hloc := hW.isLocalization_stalk x
  have hunit : ∀ s : Γ(X, W), s ∉ Q → IsUnit (X.presheaf.germ W x.1 x.2 s) := by
    intro s hs
    have : s ∈ (hW.primeIdealOf x).asIdeal.primeCompl := by
      intro h'
      rw [hxz] at h'
      exact hs h'
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x.1)
      (hW.primeIdealOf x).asIdeal s).2 this
  have hchar : ∀ n : ℕ, n.Prime → ¬ InFibre ξ n q := by
    intro n hn hfib
    have hnQ : (n : Γ(X, W)) ∉ Q := fun hmem =>
      Set.disjoint_left.1 hQM hmem ⟨n, hn.ne_zero, rfl⟩
    have := RegAtMono.unitAt_of_isUnit ξ q (hunit _ hnQ)
    rw [hφ q x.2, map_natCast] at this
    exact hfib this
  obtain ⟨g, hg⟩ := h q x.2 hchar
  obtain ⟨r, t, hrt, ht⟩ := stalk_eq_germ_div_of_affine hW x g
  have htD : t ∈ Q := by
    refine hDQ ⟨r, ?_⟩
    rw [← hφ q x.2, ← hφ q x.2, ← hg, mul_comm, ← map_mul]
    exact congrArg (genMap ξ q) hrt
  have := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x.1)
      (hW.primeIdealOf x).asIdeal t).1 ht
  apply this
  rw [hxz]
  exact htD

theorem exists_nat_span_eq [CharZero Ω] (hξ : IsCptGen ξ) (W : X.Opens) (hW : IsAffineOpen W) {r : ℕ}
    (b c : Fin r → E) (hb : LinearIndependent Ω b) (hc : LinearIndependent Ω c)
    (hs : Submodule.span Ω (Set.range b) = Submodule.span Ω (Set.range c))
    (h : ∀ q : Cpt ξ, q.1 ∈ W → (∀ n : ℕ, n.Prime → ¬ InFibre ξ n q) →
      Submodule.span (regAt ξ q) (Set.range b) = Submodule.span (regAt ξ q) (Set.range c)) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ W → (∀ n : ℕ, n.Prime → n ∣ m → ¬ InFibre ξ n q) →
      Submodule.span (regAt ξ q) (Set.range b) = Submodule.span (regAt ξ q) (Set.range c) := by
  obtain ⟨A, hA, hA'⟩ := exists_matrix b c hc hs.le
  obtain ⟨B, hB, hB'⟩ := exists_matrix c b hb hs.ge
  have h1 : ∀ i j, ∃ m : ℕ, m ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ W → (m : Ω) * A i j ∈ regAt ξ q := fun i j =>
    exists_nat_mul_mem hξ W hW _ fun q hq hch =>
      hA' (regAt ξ q) (fun i => (h q hq hch) ▸ Submodule.subset_span ⟨i, rfl⟩) i j
  have h2 : ∀ i j, ∃ m : ℕ, m ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ W → (m : Ω) * B i j ∈ regAt ξ q := fun i j =>
    exists_nat_mul_mem hξ W hW _ fun q hq hch =>
      hB' (regAt ξ q) (fun i => (h q hq hch).symm ▸ Submodule.subset_span ⟨i, rfl⟩) i j
  choose m1 hm1 hr1 using h1
  choose m2 hm2 hr2 using h2
  have hm : (∏ i, ∏ j, (m1 i j * m2 i j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ =>
      mul_ne_zero (hm1 i j) (hm2 i j)
  have hd : ∀ i j, m1 i j * m2 i j ∣ ∏ i, ∏ j, (m1 i j * m2 i j) := fun i j =>
    (Finset.dvd_prod_of_mem (fun j => m1 i j * m2 i j) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (m1 i j * m2 i j)) (Finset.mem_univ i))
  refine ⟨_, hm, fun q hq hu => le_antisymm ?_ ?_⟩
  · exact span_le_of_coeff _ b c A hA fun i j =>
      mem_regAt_of_mul q hm ((dvd_mul_right _ _).trans (hd i j)) hu (hr1 i j q hq)
  · exact span_le_of_coeff _ c b B hB fun i j =>
      mem_regAt_of_mul q hm ((dvd_mul_left _ _).trans (hd i j)) hu (hr2 i j q hq)

theorem local_step [CharZero Ω] [IsLocallyNoetherian X] (hξ : IsCptGen ξ) (S : Finset ℕ) (L₀ M : Lat ξ E)
    (l r : ℕ) (V : Submodule Ω E) (hS : ∀ l ∈ S, l.Prime) (hl : l ∈ S)
    (H0 : L₀.IsVBOn {q | ∀ l ∈ S, ¬ InFibre ξ l q} r V)
    (Hl : M.IsVBOn {q | ∀ l' : ℕ, l'.Prime → l' ≠ l → ¬ InFibre ξ l' q} r V)
    (hag : ∀ q : Cpt ξ, (∀ l' : ℕ, l'.Prime → ¬ InFibre ξ l' q) → M q = L₀ q)
    (p : Cpt ξ) (hp : InFibre ξ l p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧
      LinearIndependent Ω b ∧ ∀ q : Cpt ξ, q.1 ∈ U →
        (InFibre ξ l q → M q = Submodule.span (regAt ξ q) (Set.range b)) ∧
        (¬ InFibre ξ l q → (∀ n ∈ S, ¬ InFibre ξ n q) ∧
          L₀ q = Submodule.span (regAt ξ q) (Set.range b)) := by
  classical
  have hlp := hS l hl
  have hT : ∀ q : Cpt ξ, InFibre ξ l q → ∀ l' : ℕ, l'.Prime → l' ≠ l → ¬ InFibre ξ l' q :=
    fun q hq l' hl' hne => not_inFibre_of_inFibre hξ q hlp hl' hne.symm hq
  obtain ⟨U₀, hU₀, b, hbV, hb⟩ := Hl p (hT p hp)
  have hbLI := (hb p (hT p hp) hU₀).1
  obtain ⟨U₁, hU₁, hav⟩ := exists_open_avoid (S.erase l) p fun n hn =>
    hT p hp n (hS n (Finset.mem_of_mem_erase hn)) (Finset.ne_of_mem_erase hn)
  obtain ⟨U₂, hU₂aff, hpU₂, hU₂sub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := U₀ ⊓ U₁) (x := p.1) ⟨hU₀, hU₁⟩
  have hsub0 : ∀ {x : X}, x ∈ U₂ → x ∈ U₀ := fun hx => (hU₂sub hx).1
  have hsub1 : ∀ {x : X}, x ∈ U₂ → x ∈ U₁ := fun hx => (hU₂sub hx).2
  have hT0 : ∀ q : Cpt ξ, q.1 ∈ U₂ → ¬ InFibre ξ l q → ∀ n ∈ S, ¬ InFibre ξ n q := by
    intro q hq hql n hn
    by_cases hnl : n = l
    · exact hnl ▸ hql
    · exact hav q (hsub1 hq) n (Finset.mem_erase.2 ⟨hnl, hn⟩)
  let C : Set X := {x | x ∈ U₂ ∧ ∃ q : Cpt ξ, q.1 = x ∧ ¬ InFibre ξ l q}
  have hC : IsCompact C := by
    haveI : IsNoetherianRing Γ(X, U₂) := IsLocallyNoetherian.component_noetherian ⟨U₂, hU₂aff⟩
    have hN : TopologicalSpace.NoetherianSpace (U₂ : Set X) :=
      noetherianSpace_of_isAffineOpen U₂ hU₂aff
    have hcpt := hN.isCompact (Subtype.val ⁻¹' C : Set (U₂ : Set X))
    have := Subtype.isCompact_iff.1 hcpt
    rwa [Subtype.image_preimage_coe, Set.inter_eq_right.2 (fun x hx => hx.1)] at this
  have key : ∀ x ∈ C, ∃ W : X.Opens, x ∈ W ∧ ∃ m : ℕ, m ≠ 0 ∧ ∀ q : Cpt ξ, q.1 ∈ W → ¬ InFibre ξ l q →
      (∀ n : ℕ, n.Prime → n ∣ m → ¬ InFibre ξ n q) →
      L₀ q = Submodule.span (regAt ξ q) (Set.range b) := by
    rintro x ⟨hxU, q₀, rfl, hq₀⟩
    have hq₀T := hT0 q₀ hxU hq₀
    obtain ⟨W₀, hW₀, c, hcV, hc⟩ := H0 q₀ hq₀T
    have hcLI := (hc q₀ hq₀T hW₀).1
    obtain ⟨W, hWaff, hq₀W, hWsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := W₀ ⊓ U₂) (x := q₀.1) ⟨hW₀, hxU⟩
    obtain ⟨m, hm, hmq⟩ := exists_nat_span_eq hξ W hWaff b c hbLI hcLI (hbV.trans hcV.symm)
      (fun q hq hch => by
        have e1 := (hb q (fun l' h _ => hch l' h) (hsub0 (hWsub hq).2)).2
        have e2 := (hc q (fun n hn => hch n (hS n hn)) (hWsub hq).1).2
        rw [← e1, ← e2]
        exact hag q hch)
    refine ⟨W, hq₀W, m, hm, fun q hq hql hqm => ?_⟩
    rw [(hc q (hT0 q (hWsub hq).2 hql) (hWsub hq).1).2, hmq q hq hqm]
  choose! Wf hxW mf hmf hWf using key
  obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun x => (Wf x : Set X))
    (fun x hx => (Wf x).2.mem_nhds (hxW x hx))
  have hm : (∏ x ∈ t, mf x) ≠ 0 := Finset.prod_ne_zero_iff.2 fun x hx => hmf x (htC x hx)
  obtain ⟨U₃, hU₃, hav3⟩ := exists_open_avoid ((∏ x ∈ t, mf x).primeFactors.erase l) p fun n hn =>
    hT p hp n (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hn)) (Finset.ne_of_mem_erase hn)
  refine ⟨U₂ ⊓ U₃, ⟨hpU₂, hU₃⟩, b, hbV, hbLI, fun q hq => ⟨fun hql => ?_, fun hql => ⟨hT0 q hq.1 hql, ?_⟩⟩⟩
  · exact (hb q (hT q hql) (hsub0 hq.1)).2
  · have hqC : q.1 ∈ C := ⟨hq.1, q, rfl, hql⟩
    obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.1 (hcov hqC)
    refine hWf x (htC x hx) q hqx hql fun n hn hnd => ?_
    by_cases hnl : n = l
    · exact hnl ▸ hql
    · refine hav3 q hq.2 n (Finset.mem_erase.2 ⟨hnl, Nat.mem_primeFactors.2 ⟨hn, ?_, hm⟩⟩)
      exact hnd.trans (Finset.dvd_prod_of_mem mf hx)

end GlobalTheory.CompanionTheory.Ar.LatGlue

namespace GlobalTheory.CompanionTheory.Ar

theorem lat_glue : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] [CharZero Ω] [IsLocallyNoetherian X] (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) (r : ℕ) (V : Submodule Ω E), IsCptGen ξ → (∀ l ∈ S, l.Prime) → L₀.IsVBOn {q | ∀ l ∈ S, ¬ InFibre ξ l q} r V → (∀ l ∈ S, (Lp l).IsVBOn {q | ∀ l' : ℕ, l'.Prime → l' ≠ l → ¬ InFibre ξ l' q} r V) → (∀ l ∈ S, ∀ q : Cpt ξ, (∀ l' : ℕ, l'.Prime → ¬ InFibre ξ l' q) → Lp l q = L₀ q) → ∃ L : Lat ξ E, L.IsVB r V ∧ (∀ q : Cpt ξ, (∀ l ∈ S, ¬ InFibre ξ l q) → L q = L₀ q) ∧ ∀ l ∈ S, ∀ q : Cpt ξ, InFibre ξ l q → L q = Lp l q := by
  intro X Ω _ ξ E _ _ _ _ S L₀ Lp r V hξ hS H0 Hp hag
  classical
  let L : Lat ξ E := fun q => if h : ∃ l ∈ S, InFibre ξ l q then Lp h.choose q else L₀ q
  have hL1 : ∀ q : Cpt ξ, (∀ l ∈ S, ¬ InFibre ξ l q) → L q = L₀ q := by
    intro q hq
    exact dif_neg (by rintro ⟨l, hl, h⟩; exact hq l hl h)
  have hL2 : ∀ l ∈ S, ∀ q : Cpt ξ, InFibre ξ l q → L q = Lp l q := by
    intro l hl q hq
    have h : ∃ l ∈ S, InFibre ξ l q := ⟨l, hl, hq⟩
    have e : h.choose = l := by
      by_contra hne
      exact LatGlue.not_inFibre_of_inFibre hξ q (hS _ h.choose_spec.1) (hS l hl) hne
        h.choose_spec.2 hq
    show (if h : ∃ l ∈ S, InFibre ξ l q then Lp h.choose q else L₀ q) = Lp l q
    rw [dif_pos h, e]
  refine ⟨L, ?_, hL1, hL2⟩
  intro p _
  by_cases h : ∃ l ∈ S, InFibre ξ l p
  · obtain ⟨l, hl, hp⟩ := h
    obtain ⟨U, hU, b, hV, hLI, hq⟩ :=
      LatGlue.local_step hξ S L₀ (Lp l) l r V hS hl H0 (Hp l hl) (hag l hl) p hp
    refine ⟨U, hU, b, hV, fun q _ hqU => ⟨hLI, ?_⟩⟩
    by_cases hql : InFibre ξ l q
    · rw [hL2 l hl q hql]
      exact (hq q hqU).1 hql
    · rw [hL1 q ((hq q hqU).2 hql).1]
      exact ((hq q hqU).2 hql).2
  · have hpT : ∀ l ∈ S, ¬ InFibre ξ l p := fun l hl hp => h ⟨l, hl, hp⟩
    obtain ⟨U, hU, b, hV, hb⟩ := H0 p hpT
    obtain ⟨U₁, hU₁, hav⟩ := LatGlue.exists_open_avoid S p hpT
    refine ⟨U ⊓ U₁, ⟨hU, hU₁⟩, b, hV, fun q _ hq => ?_⟩
    have hqT := hav q hq.2
    have := hb q hqT hq.1
    exact ⟨this.1, (hL1 q hqT).trans this.2⟩

end GlobalTheory.CompanionTheory.Ar
