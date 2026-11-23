import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.LevSurj

theorem exists_section {R : Type} (K : Type) {A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K]
    [Algebra R K] [IsFractionRing R K] [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Flat R A]
    (m : Ideal A) [m.IsPrime] : ∃ σ : A →ₐ[R] R, RingHom.ker σ ≤ m := by
  obtain ⟨q, hqm, hq, hq0⟩ := Ideal.exists_ideal_le_liesOver_of_le (R := R) (p := ⊥) (q := m.under R) m bot_le
  have hinj : Function.Injective (algebraMap R (A ⧸ q)) := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    have h1 : algebraMap R A s ∈ q := Ideal.Quotient.eq_zero_iff_mem.1 hs
    have h2 : s ∈ q.under R := h1
    rw [← hq0.over] at h2
    exact h2
  haveI : FaithfulSMul R (A ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  obtain ⟨g, -⟩ := exists_algHom_comp_eq (A := R) (K := K) (IsAlgClosed.lift (R := R) (S := A ⧸ q) (M := K))
  have hg : RingHom.ker g = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := R) (by
    rw [eq_bot_iff]
    intro s hs
    have : g (algebraMap R _ s) = 0 := hs
    rw [g.commutes] at this
    exact this)
  refine ⟨g.comp (Ideal.Quotient.mkₐ R q), fun b hb => hqm ?_⟩
  have h3 : Ideal.Quotient.mk q b ∈ RingHom.ker g := hb
  rw [hg] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

variable {R : Type} [CommRing R]

theorem conv_inv {A B : Type} [CommRing A] [HopfAlgebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B) :
    toConv (f.comp (HopfAlgebra.antipodeAlgHom R A)) * toConv f = 1 := by
  have h := AlgHom.comp_convMul_distrib f (toConv (HopfAlgebra.antipodeAlgHom R A)) (toConv (AlgHom.id R A))
  rw [AlgHom.antipode_id_cancel] at h
  apply WithConv.ofConv_injective
  refine h.symm.trans ?_
  ext a
  simp [AlgHom.convOne_def]

theorem range_subset_iff {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (V : (Sp A).Opens) :
    Set.range (spMap φ) ⊆ V ↔ ∀ x : PrimeSpectrum B, PrimeSpectrum.comap φ x ∈ V := by
  constructor
  · intro h x
    exact h ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

theorem range_subset_of_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B) (V : (Sp A).Opens)
    (h : PrimeSpectrum.comap φ (IsLocalRing.closedPoint B) ∈ V) : Set.range (spMap φ) ⊆ V := by
  rw [range_subset_iff]
  intro x
  exact ((IsLocalRing.specializes_closedPoint x).map (PrimeSpectrum.continuous_comap φ)).mem_open V.2 h

variable {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {N : ℕ} {A : Type} [CommRing A] [HopfAlgebra R A]

theorem pt_one (θ : TorsPt G N A) (B : Type) [CommRing B] [Algebra R B] :
    θ.pt B 1 = (Algebra.ofId R B).comp (counitAlgHom R A) := by
  have h := θ.mul B 1 1
  rw [_root_.mul_one] at h
  have h2 := conv_inv (θ.pt B 1)
  have h3 : toConv (θ.pt B 1) = 1 := by
    calc toConv (θ.pt B 1) = (toConv ((θ.pt B 1).comp (HopfAlgebra.antipodeAlgHom R A)) * toConv (θ.pt B 1)) *
        toConv (θ.pt B 1) := by rw [h2, _root_.one_mul]
      _ = 1 := by rw [_root_.mul_assoc, ← h, h2]
  exact congrArg ofConv h3

theorem pt_inj {K : Type} [Field K] [Algebra R K] {θ : TorsPt G N A} (hθ : IsLevel K θ) (B : Type) [CommRing B]
    [Algebra R B] : Function.Injective (θ.pt B) := by
  obtain ⟨V, hV⟩ := hθ.opn
  exact Set.injOn_univ.1 (hV B).injOn

theorem torsMap_inj {K : Type} [Field K] [Algebra R K] {θ : TorsPt G N A} (hθ : IsLevel K θ) {B C : Type} [CommRing B]
    [Algebra R B] [CommRing C] [Algebra R C] (jj : B →ₐ[R] C) (hjj : Function.Injective jj) :
    Function.Injective (torsMap (G := G) (N := N) jj) := by
  intro x y h
  apply pt_inj hθ
  have h1 := congrArg (θ.pt C) h
  rw [θ.nat, θ.nat] at h1
  ext a
  exact hjj (congr($h1 a))

theorem ker_trivial {K : Type} [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    [Module.Finite R A] [Module.Flat R A] {N' : ℕ} (h : N ∣ N') {A' : Type} [CommRing A'] [HopfAlgebra R A']
    {θ : TorsPt G N A} {θ' : TorsPt G N' A'} (hθ : IsLevel K θ) (hθ' : IsLevel K θ') (g : A' →ₐ[R] A)
    (hg : ∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B), θ'.pt B (torsIncl h z) = (θ.pt B z).comp g)
    {B : Type} [CommRing B] [Algebra R B] (δ : A →ₐ[R] B)
    (hδ : δ.comp g = (Algebra.ofId R B).comp (counitAlgHom R A')) :
    δ = (Algebra.ofId R B).comp (counitAlgHom R A) := by
  obtain ⟨V, hV⟩ := hθ.opn
  obtain ⟨V', hV'⟩ := hθ'.opn
  have hδV : Set.range (spMap (δ : A →+* B)) ⊆ V := by
    rw [range_subset_iff]
    intro x
    let P : PrimeSpectrum A := PrimeSpectrum.comap (δ : A →+* B) x
    obtain ⟨s, hs⟩ := exists_section (R := R) K P.asIdeal
    let q : Ideal R := P.asIdeal.comap (algebraMap R A)
    let L := Localization.AtPrime q
    have hsP : ∀ a, s a ∈ q ↔ a ∈ P.asIdeal := fun a => by
      have h1 : a - algebraMap R A (s a) ∈ P.asIdeal := hs (by simp [RingHom.mem_ker])
      constructor
      · intro h2
        simpa using P.asIdeal.add_mem h1 h2
      · intro h2
        show algebraMap R A (s a) ∈ P.asIdeal
        simpa using P.asIdeal.sub_mem h2 h1
    have hL : ∀ r : R, algebraMap R L r ∈ IsLocalRing.maximalIdeal L ↔ r ∈ q := fun r =>
      IsLocalization.AtPrime.to_map_mem_maximal_iff L q r
    have hq : q.primeCompl ≤ nonZeroDivisors R := Ideal.primeCompl_le_nonZeroDivisors q
    have hu : ∀ y : q.primeCompl, IsUnit (Algebra.ofId R K y) := fun y =>
      IsLocalization.map_units K (⟨y.1, hq y.2⟩ : nonZeroDivisors R)
    let jj : L →ₐ[R] K := IsLocalization.liftAlgHom (M := q.primeCompl) hu
    have hjj : Function.Injective jj := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
      have h1 : jj (IsLocalization.mk' L a b * algebraMap R L b) = 0 := by
        rw [map_mul]; exact mul_eq_zero_of_left hy _
      rw [IsLocalization.mk'_spec, jj.commutes] at h1
      have h2 : a = 0 := (IsFractionRing.injective R K) (h1.trans (map_zero _).symm)
      simp [h2]
    let sL : A →ₐ[R] L := (Algebra.ofId R L).comp s
    have h1 : Set.range (spMap ((sL.comp g : A' →ₐ[R] L) : A' →+* L)) ⊆ V' := by
      apply range_subset_of_local
      have h2 := (range_subset_iff _ _).1 ((hV' B).mapsTo (Set.mem_univ 1)) x
      rw [pt_one, ← hδ] at h2
      convert h2 using 1
      ext a
      exact (hL _).trans (hsP _)
    obtain ⟨z', -, hz'⟩ := (hV' L).surjOn h1
    obtain ⟨t, ht⟩ := hθ.gen.2 (jj.comp sL)
    have h3 : torsMap jj z' = torsIncl h t := by
      apply pt_inj hθ'
      rw [θ'.nat, hz', hg, ht]
      rfl
    have h4 : z'.1 ^ N = 1 := by
      have h5 : (⟨z'.1 ^ N, (z' ^ N).2⟩ : Tors G N' L) = 1 := by
        apply torsMap_inj hθ' jj hjj
        apply Subtype.ext
        have h6 : spOver jj ≫ z'.1 = t.1 := congrArg Subtype.val h3
        change spOver jj ≫ z'.1 ^ N = spOver jj ≫ 1
        rw [MonObj.comp_pow, h6, t.2, MonObj.comp_one]
      exact congrArg Subtype.val h5
    let z : Tors G N L := ⟨z'.1, h4⟩
    have h7 : torsMap jj z = t := Subtype.ext (show spOver jj ≫ z'.1 = t.1 from congrArg Subtype.val h3)
    have h8 : θ.pt L z = sL := by
      rw [← h7, θ.nat] at ht
      ext a
      exact hjj (congr($ht a))
    have h9 := (range_subset_iff _ _).1 ((hV L).mapsTo (Set.mem_univ z)) (IsLocalRing.closedPoint L)
    rw [h8] at h9
    convert h9 using 1
    ext a
    exact ((hL _).trans (hsP _)).symm
  obtain ⟨w, -, hw⟩ := (hV B).surjOn hδV
  have h1 : torsIncl h w = 1 := by
    apply pt_inj hθ'
    rw [hg, hw, hδ, pt_one]
  have h2 : w = 1 := Subtype.ext (show w.1 = 1 from congrArg Subtype.val h1)
  rw [← hw, h2, pt_one]

theorem level_surjective : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N N' : ℕ) (h : N ∣ N'), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (A' : Type) [CommRing A'] [HopfAlgebra R A'] [IsCocomm R A'] [Module.Finite R A'] [Module.Projective R A'] (θ : TorsPt G N A) (θ' : TorsPt G N' A'), IsLevel K θ → IsLevel K θ' → ∀ g : A' →ₐc[R] A, (∀ (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B), θ'.pt B (torsIncl h z) = (θ.pt B z).comp (g : A' →ₐ[R] A)) → Function.Surjective g := by
  intro R K _ _ _ _ _ _ _ _ G _ _ _ N N' h _ A _ _ _ _ _ A' _ _ _ _ _ θ θ' hθ hθ' g hg
  have hc : ∀ (T : Type) [CommRing T] [Algebra R T] (g₁ g₂ : A →ₐ[R] T),
      g₁.comp (g : A' →ₐ[R] A) = g₂.comp (g : A' →ₐ[R] A) → g₁ = g₂ := by
    intro T _ _ φ ψ e
    let φi := toConv (φ.comp (HopfAlgebra.antipodeAlgHom R A))
    have h1 : φi * toConv φ = 1 := conv_inv φ
    have h2 : (φi * toConv ψ).ofConv = (Algebra.ofId R T).comp (counitAlgHom R A) := by
      apply ker_trivial h hθ hθ' _ hg
      rw [AlgHom.convMul_comp_bialgHom_distrib]
      simp only [ofConv_toConv]
      rw [← e]
      have := AlgHom.convMul_comp_bialgHom_distrib φi (toConv φ) g
      simp only [ofConv_toConv] at this
      rw [← this, h1]
      ext a
      simp [AlgHom.convOne_def]
    have h3 : φi * toConv ψ = 1 := WithConv.ofConv_injective h2
    apply WithConv.toConv_injective
    calc toConv φ = toConv φ * (φi * toConv ψ) := by rw [h3, _root_.mul_one]
      _ = toConv ψ := by rw [← _root_.mul_assoc, _root_.mul_comm (toConv φ), h1, _root_.one_mul]
  let f : A' →ₐ[R] A := g
  have hf : f.Finite := AlgHom.Finite.of_comp_finite (f := Algebra.ofId R A') (by
        rw [Algebra.comp_ofId]; exact RingHom.finite_algebraMap.2 inferInstance)
  algebraize [f.toRingHom]
  have : Module.Finite A' A := hf
  refine (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := A') (A := A)).1 ?_
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro b
  have := hc (A ⊗[A'] A) ((Algebra.TensorProduct.includeRight : A →ₐ[A'] A ⊗[A'] A).restrictScalars R)
    ((Algebra.TensorProduct.includeLeft : A →ₐ[A'] A ⊗[A'] A).restrictScalars R) (by
      ext a
      exact ((Algebra.TensorProduct.includeRight : A →ₐ[A'] A ⊗[A'] A).commutes a).trans
        ((Algebra.TensorProduct.includeLeft : A →ₐ[A'] A ⊗[A'] A).commutes a).symm)
  exact congr($this b)

end GlobalTheory.GroupBplus.Aff.LevSurj
