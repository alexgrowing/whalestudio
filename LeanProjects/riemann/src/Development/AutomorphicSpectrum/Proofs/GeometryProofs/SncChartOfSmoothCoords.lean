import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem exists_cover_basicOpen {Z : Scheme.{0}} {W : Z.Opens} (hW : IsAffineOpen W) {n : ℕ}
    (V : Fin n → Z.affineOpens) (hV : ∀ y : Z, ∃ j, y ∈ (V j : Z.Opens)) :
    ∃ (m : ℕ) (u c : Fin m → Γ(Z, W)), ∑ l, c l * u l = 1 ∧
      ∀ l, ∃ (j : Fin n) (v : Γ(Z, (V j : Z.Opens))), Z.basicOpen (u l) = Z.basicOpen v := by
  classical
  let s : Set Γ(Z, W) :=
    {f | ∃ (j : Fin n) (v : Γ(Z, (V j : Z.Opens))), Z.basicOpen f = Z.basicOpen v}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hV x
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hW (V j).2 x ⟨hx, hj⟩
    exact Opens.mem_iSup.2 ⟨⟨f, j, g, e⟩, hxf⟩
  have h1 : (1 : Γ(Z, W)) ∈ Ideal.span s := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : Γ(Z, W)), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x * (x : Γ(Z, W))

theorem smooth_secAlgebra {Z : Scheme.{0}} (g : Z ⟶ Sp ℚ) (e : ℕ)
    (hsm : SmoothOfRelativeDimension e g) {D : Z.Opens} (hD : IsAffineOpen D) :
    @Algebra.Smooth ℚ _ Γ(Z, D) _ (secAlgebra g D) := by
  have h0 : Smooth g := hsm.smooth
  have h1 := Smooth.smooth_appLE (f := g) (isAffineOpen_top _) hD (fun _ _ => trivial)
  exact RingHom.Smooth.propertyIsLocal.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℚ)).symm.commRingCatIsoToRingEquiv h1

theorem coords_of_formallyEtale {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
    [Algebra R S] [IsScalarTower ℚ R S] [Algebra.FormallyEtale R S] {e : ℕ} (z : Fin e → R)
    (h1 : LinearIndependent R fun i => KaehlerDifferential.D ℚ R (z i))
    (h2 : Submodule.span R (Set.range fun i => KaehlerDifferential.D ℚ R (z i)) = ⊤) :
    LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) ∧
      Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) = ⊤ := by
  let b := Module.Basis.mk h1 h2.ge
  let b' := (b.baseChange S).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℚ R S)
  have hb : (fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) = b' := by
    funext i
    simp [b', b, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]
  rw [hb]
  exact ⟨b'.linearIndependent, b'.span_eq⟩

theorem exists_point_of_prime {Z : Scheme.{0}} {D : Z.Opens} (hD : IsAffineOpen D)
    (q : Ideal Γ(Z, D)) (hq : q.IsPrime) :
    ∃ t ∈ D, ∀ s : Γ(Z, D), s ∈ q ↔ t ∉ Z.basicOpen s := by
  refine ⟨hD.fromSpec ⟨q, hq⟩, hD.fromSpec_preimage_self.ge trivial, fun s => ?_⟩
  have h := hD.fromSpec_preimage_basicOpen s
  have h2 : (hD.fromSpec ⟨q, hq⟩ ∈ Z.basicOpen s) ↔ (⟨q, hq⟩ : PrimeSpectrum Γ(Z, D)) ∈ PrimeSpectrum.basicOpen s := by
    rw [← h]
    rfl
  rw [h2]
  simp

theorem range_valMap_basicOpen {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z)
    {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (u : Γ(Z, W)) (hu : valR ζ W u ≠ 0) (D : Z.Opens)
    (hDu : D = Z.basicOpen u) :
    ∃ hD : ⊤ ≤ ζ ⁻¹ᵁ D, Set.range (valMap ζ D hD).hom =
      (Algebra.adjoin ℚ (insert (valR ζ W u)⁻¹ (A : Set Ω)) : Subalgebra ℚ Ω) := by
  subst hDu
  have hD : ⊤ ≤ ζ ⁻¹ᵁ Z.basicOpen u := (le_preimage_basicOpen_iff ζ h u).2 (isUnit_iff_ne_zero.2 hu)
  have hle : Z.basicOpen u ≤ W := Z.basicOpen_le u
  have hres : ∀ w : Γ(Z, W), (valMap ζ _ hD).hom ((Z.presheaf.map (homOfLE hle).op).hom w) = valR ζ W w :=
    fun w => by rw [← valR_eq _ _ hD, valR_res ζ hle hD]
  refine ⟨hD, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    have := hW.isLocalization_basicOpen u
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj u x
    have h1 := congrArg (valMap ζ _ hD).hom ha
    rw [map_mul, map_pow] at h1
    have h2 : ∀ t : Γ(Z, W), (valMap ζ _ hD).hom (algebraMap Γ(Z, W) Γ(Z, Z.basicOpen u) t) = valR ζ W t :=
      hres
    rw [h2, h2] at h1
    have h3 : (valMap ζ _ hD).hom x = valR ζ W a * ((valR ζ W u)⁻¹) ^ k := by
      rw [← h1, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]
    have hv : ∀ w : Γ(Z, W), valR ζ W w ∈ (A : Set Ω) := fun w => by
      rw [← hA, valR_eq _ _ h]; exact ⟨w, rfl⟩
    rw [h3]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (hv a)))
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)
  · intro x hx
    have hAr : ∀ a ∈ A, a ∈ Set.range (valMap ζ _ hD).hom := fun a ha => by
      have : a ∈ Set.range (valMap ζ W h).hom := by rw [hA]; exact ha
      obtain ⟨w, rfl⟩ := this
      exact ⟨_, (hres w).trans (valR_eq _ _ h _)⟩
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · have hunit : IsUnit ((Z.presheaf.map (homOfLE hle).op).hom u) :=
          RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace u
        obtain ⟨b, hb⟩ := hunit.exists_right_inv
        refine ⟨b, (inv_eq_of_mul_eq_one_right ?_).symm⟩
        rw [← hres u, ← map_mul, hb, map_one]
      · exact hAr x hx
    | algebraMap r => exact hAr _ (Subalgebra.algebraMap_mem _ r)
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩

theorem snc_on_basicOpen {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z)
    [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W)
    (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) (u : Γ(Z, W)) (hu : valR ζ W u ≠ 0)
    {V : Z.Opens} (hV : IsAffineOpen V) (v : Γ(Z, V)) (huv : Z.basicOpen u = Z.basicOpen v)
    (z : Fin e → Γ(Z, V)) (k : ℕ) (hk : k ≤ e) (hz : IsCoords g V z)
    (hT : (V : Set Z) ∩ T = {y | y ∈ V ∧ ∃ i : Fin e, (i : ℕ) < k ∧ y ∉ Z.basicOpen (z i)})
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (valR ζ W u)⁻¹ (A : Set Ω))) :
    Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
      LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
      Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
      ∀ q : Ideal S, q.IsPrime →
        ((∀ s : S, (s : Ω) = valR ζ W σ → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  obtain ⟨hD, hr⟩ := range_valMap_basicOpen ζ hW h A hA u hu (Z.basicOpen v) huv.symm
  rw [← hS] at hr
  have hDaff : IsAffineOpen (Z.basicOpen v) := hV.basicOpen v
  have hDW : Z.basicOpen v ≤ W := huv ▸ Z.basicOpen_le u
  have hDV : Z.basicOpen v ≤ V := Z.basicOpen_le v
  letI iV := secAlgebra g V
  letI iD := secAlgebra g (Z.basicOpen v)
  let ψ := (valMap ζ (Z.basicOpen v) hD).hom
  have hψ : ∀ x, ψ x ∈ S := fun x => by
    have : ψ x ∈ Set.range ψ := ⟨x, rfl⟩
    rw [show Set.range ψ = (S : Set Ω) from hr] at this
    exact this
  let φ : Γ(Z, Z.basicOpen v) ≃+* S := RingEquiv.ofBijective (ψ.codRestrict S hψ) (by
    refine ⟨fun a b hab => valMap_injective ζ hD (congrArg Subtype.val hab), fun s => ?_⟩
    have hs : (s : Ω) ∈ Set.range ψ := by
      rw [show Set.range ψ = (S : Set Ω) from hr]
      exact s.2
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, Subtype.ext hx⟩)
  have hφ : ∀ x, (φ x : Ω) = ψ x := fun _ => rfl
  haveI hs0 : Algebra.Smooth ℚ Γ(Z, Z.basicOpen v) := smooth_secAlgebra g e hsm hDaff
  have hsmooth : Algebra.Smooth ℚ S := Algebra.Smooth.of_equiv φ.toRatAlgEquiv
  refine ⟨hsmooth, ?_⟩

  haveI := hV.isLocalization_basicOpen v
  haveI : Algebra.FormallyEtale Γ(Z, V) Γ(Z, Z.basicOpen v) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers v)
  haveI : IsScalarTower ℚ Γ(Z, V) Γ(Z, Z.basicOpen v) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨c1, c2⟩ := coords_of_formallyEtale (R := Γ(Z, V)) (S := Γ(Z, Z.basicOpen v)) z hz.1 hz.2

  letI iS : Algebra Γ(Z, Z.basicOpen v) S := φ.toRingHom.toAlgebra
  haveI : Algebra.FormallyEtale Γ(Z, Z.basicOpen v) S :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := φ) fun _ => rfl)
  haveI : IsScalarTower ℚ Γ(Z, Z.basicOpen v) S :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨d1, d2⟩ := coords_of_formallyEtale (R := Γ(Z, Z.basicOpen v)) (S := S) _ c1 c2
  refine ⟨_, k, hk, d1, d2, fun q hq => ?_⟩
  have hq' : (q.comap φ.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨t, htD, ht⟩ := exists_point_of_prime hDaff _ hq'
  have hmem : ∀ x, φ x ∈ q ↔ t ∉ Z.basicOpen x := ht
  have htV : t ∈ V := hDV htD
  have htW : t ∈ W := hDW htD
  have hzt : ∀ i, algebraMap Γ(Z, Z.basicOpen v) S (algebraMap Γ(Z, V) Γ(Z, Z.basicOpen v) (z i)) ∈ q ↔
      t ∉ Z.basicOpen (z i) := fun i => by
    refine (hmem _).trans (not_congr ?_)
    have := Z.basicOpen_res (z i) (homOfLE hDV).op
    rw [show algebraMap Γ(Z, V) Γ(Z, Z.basicOpen v) (z i) =
      (Z.presheaf.map (homOfLE hDV).op).hom (z i) from rfl, this]
    exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
  let sσ : Γ(Z, Z.basicOpen v) := (Z.presheaf.map (homOfLE hDW).op).hom σ
  have hsσ : (φ sσ : Ω) = valR ζ W σ := by
    rw [hφ, ← valR_res ζ hDW hD σ, valR_eq _ _ hD]
  have hσt : φ sσ ∈ q ↔ t ∈ T := by
    refine (hmem _).trans ?_
    rw [hσ t htW, not_iff_not, Z.basicOpen_res σ (homOfLE hDW).op]
    exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
  have hTt : t ∈ T ↔ ∃ i : Fin e, (i : ℕ) < k ∧ t ∉ Z.basicOpen (z i) := by
    have h1 : t ∈ (V : Set Z) ∩ T ↔ t ∈ T := ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
    rw [← h1, hT]
    exact ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
  constructor
  · intro H
    obtain ⟨i, hi, hit⟩ := hTt.1 (hσt.1 (H _ hsσ))
    exact ⟨i, hi, (hzt i).2 hit⟩
  · rintro ⟨i, hi, hit⟩ s hs
    have : s = φ sσ := Subtype.ext (hs.trans hsσ.symm)
    rw [this]
    exact hσt.2 (hTt.2 ⟨i, hi, (hzt i).1 hit⟩)

theorem sncChart_of_coords (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z)
    [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) (W : Z.Opens)
    (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) : SncChart A e (valR ζ W σ) := by
  obtain ⟨n, V, hcov, hV⟩ := hc
  obtain ⟨m, u, c, hsum, hl⟩ := exists_cover_basicOpen hW V hcov
  have hv : ∀ w : Γ(Z, W), valR ζ W w ∈ A := fun w => by
    have : valR ζ W w ∈ Set.range (valMap ζ W h).hom := by
      rw [valR_eq _ _ h]
      exact ⟨w, rfl⟩
    rw [hA] at this
    exact this
  refine ⟨m, fun l => valR ζ W (u l), fun l => valR ζ W (c l), fun l => hv _, fun l => hv _, ?_,
    fun l hf S hS => ?_⟩
  · simp only [valR_eq _ _ h]
    simp only [← map_mul, ← map_sum, hsum, map_one]
  · obtain ⟨j, v, huv⟩ := hl l
    obtain ⟨z, k, hk, hz, hT⟩ := hV j
    exact snc_on_basicOpen ζ g e T hsm hW h A hA σ hσ (u l) hf (V j).2 v huv z k hk hz hT S hS

end GlobalTheory.CompanionTheory.Ar.SncRes
