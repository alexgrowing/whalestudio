import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineCover

variable {Y : Scheme.{0}} {M : LB Y}

theorem exists_quotient (s t : M.Sec) :
    ∃ r : Γ(Y, nonzeroLocus t), ∀ (y : Y) (k : M.ι), y ∈ nonzeroLocus t → y ∈ M.U k →
      gs (𝟙 Y) y _ (s.f k) = gs (𝟙 Y) y _ r * gs (𝟙 Y) y _ (t.f k) := by
  have loc : ∀ k, ∃ a : Γ(Y, Y.basicOpen (t.f k)), ∀ y ∈ Y.basicOpen (t.f k),
      gs (𝟙 Y) y _ (s.f k) = gs (𝟙 Y) y _ a * gs (𝟙 Y) y _ (t.f k) := fun k => by
    obtain ⟨b, hb⟩ := (show IsUnit (resG Y (Y.basicOpen_le (t.f k)) (t.f k)) from
      Y.toRingedSpace.isUnit_res_basicOpen (t.f k)).exists_left_inv
    refine ⟨resG Y (Y.basicOpen_le _) (s.f k) * b, fun y hy => ?_⟩
    have e : gs (𝟙 Y) y (Y.basicOpen (t.f k)) (b * resG Y (Y.basicOpen_le _) (t.f k)) =
        gs (𝟙 Y) y (Y.basicOpen (t.f k)) 1 := congrArg _ hb
    rw [gs_mul _ y _ hy, gs_res _ y _ hy, gs_eq _ y _ hy 1, map_one, map_one] at e
    rw [gs_mul _ y _ hy, gs_res _ y _ hy, _root_.mul_assoc, e, _root_.mul_one]
  choose a ha using loc
  obtain ⟨r, hr, -⟩ := Y.sheaf.existsUnique_gluing' (fun k => Y.basicOpen (t.f k)) (nonzeroLocus t)
    (fun k => homOfLE (basicOpen_le_nonzeroLocus t k)) le_rfl a (fun k l => fn_ext fun y hy => by
      have hk : y ∈ M.U k := Y.basicOpen_le _ hy.1
      have hl : y ∈ M.U l := Y.basicOpen_le _ hy.2
      refine (gs_res (𝟙 Y) y inf_le_left hy (a k)).trans
        (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy (a l)).symm)
      have u : IsUnit (gs (𝟙 Y) y _ (t.f k)) := (LBGerm.isUnit_gs_iff (𝟙 Y) y _ hk _).2 hy.1
      refine u.mul_right_cancel ?_
      rw [← ha k y hy.1, gs_compat s (𝟙 Y) y hk hl, gs_compat t (𝟙 Y) y hk hl, ha l y hy.2, mul_left_comm])
  refine ⟨r, fun y k hy hk => ?_⟩
  have hy' := (mem_nonzeroLocus_iff_basicOpen t hk).1 hy
  rw [ha k y hy', ← hr k]
  exact congrArg (· * _) (gs_res (𝟙 Y) y (basicOpen_le_nonzeroLocus t k) hy' r)

theorem gs_sum_mul {I : Type} [Fintype I] (c : I → Γ(Y, ⊤)) {U : Y.Opens} (b : I → Γ(Y, U)) (y : Y)
    (hy : y ∈ U) :
    gs (𝟙 Y) y U (∑ i, resG Y le_top (c i) * b i) = ∑ i, gs (𝟙 Y) y ⊤ (c i) * gs (𝟙 Y) y U (b i) := by
  rw [gs_eq _ y U hy, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← gs_eq _ y U hy, gs_mul _ y U hy, gs_res _ y _ hy]

theorem exists_sec_sum {I : Type} [Fintype I] (c : I → Γ(Y, ⊤)) (s : I → M.Sec) :
    ∃ t : M.Sec, ∀ k, t.f k = ∑ i, resG Y le_top (c i) * (s i).f k :=
  ⟨⟨fun k => ∑ i, resG Y le_top (c i) * (s i).f k, fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (DVR.SecOps.secScale (c i) (s i)).compat j j'⟩, fun _ => rfl⟩

theorem isAffineOpen_nonzeroLocus_sum (hM : M.IsLB) {I : Type} [Fintype I] (c : I → Γ(Y, ⊤)) (s : I → M.Sec)
    (hs : ∀ i, IsAffineOpen (nonzeroLocus (s i))) (t : M.Sec)
    (ht : ∀ k, t.f k = ∑ i, resG Y le_top (c i) * (s i).f k) : IsAffineOpen (nonzeroLocus t) := by
  choose r hr using fun i => exists_quotient (s i) t
  refine isAffineOpen_of_isAffineOpen_basicOpen _ (Set.range r) ?_ ?_
  · have e : ∑ i, resG Y le_top (c i) * r i = 1 := fn_ext fun y hy => by
      obtain ⟨k, hk⟩ := exists_chart hM y
      have u := (mem_nonzeroLocus_iff_isUnit t hk).1 hy
      refine u.mul_right_cancel ?_
      rw [gs_sum_mul _ _ y hy, gs_eq _ y _ hy 1, map_one, map_one, _root_.one_mul, Finset.sum_mul]
      simp only [_root_.mul_assoc, ← hr _ y k hy hk]
      rw [ht k, gs_sum_mul _ _ y hk]
    rw [Ideal.eq_top_iff_one, ← e]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have e : Y.basicOpen (r i) = nonzeroLocus t ⊓ nonzeroLocus (s i) := by
      ext y
      obtain ⟨k, hk⟩ := exists_chart hM y
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hy : y ∈ nonzeroLocus t := Y.basicOpen_le _ h
        refine ⟨hy, (mem_nonzeroLocus_iff_isUnit _ hk).2 ?_⟩
        rw [hr i y k hy hk]
        exact ((LBGerm.isUnit_gs_iff (𝟙 Y) y _ hy _).2 h).mul ((mem_nonzeroLocus_iff_isUnit t hk).1 hy)
      · have u := (mem_nonzeroLocus_iff_isUnit _ hk).1 h.2
        rw [hr i y k h.1 hk] at u
        exact (LBGerm.isUnit_gs_iff (𝟙 Y) y _ h.1 _).1 (isUnit_of_mul_isUnit_left u)
    rw [e]
    exact isAffineOpen_nonzeroLocus_inf hM t (hs i)

theorem exists_isUnit_sum {K : Type} [Field K] [Infinite K] {I J : Type} [Fintype I] [Finite J]
    (R : J → Type) [∀ j, CommRing (R j)] [∀ j, IsLocalRing (R j)] (ψ : ∀ j, K →+* R j) (a : ∀ j, I → R j)
    (h : ∀ j, ∃ i, IsUnit (a j i)) : ∃ c : I → K, ∀ j, IsUnit (∑ i, ψ j (c i) * a j i) := by
  classical
  let p : J → Submodule K (I → K) := fun j =>
    { carrier := {c | ∑ i, ψ j (c i) * a j i ∈ IsLocalRing.maximalIdeal (R j)}
      add_mem' := fun {c d} hc hd => by
        have := (IsLocalRing.maximalIdeal (R j)).add_mem hc hd
        simpa [add_mul, Finset.sum_add_distrib] using this
      zero_mem' := by simp
      smul_mem' := fun e c hc => by
        have := (IsLocalRing.maximalIdeal (R j)).mul_mem_left (ψ j e) hc
        simpa [Finset.mul_sum, _root_.mul_assoc] using this }
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p fun j hj => by
    obtain ⟨i, hi⟩ := h j
    have : ∑ l, ψ j ((Pi.single i 1 : I → K) l) * a j l ∈ IsLocalRing.maximalIdeal (R j) :=
      (hj.ge Submodule.mem_top : (Pi.single i 1 : I → K) ∈ p j)
    rw [Finset.sum_eq_single i (fun l _ hl => by simp [Pi.single_eq_of_ne hl]) (by simp)] at this
    simp only [Pi.single_eq_same, map_one, _root_.one_mul] at this
    exact this hi
  exact ⟨c, fun j => not_not.1 (hc j)⟩

theorem exists_isAffineOpen_of_finite {K : Type} [Field K] [Infinite K] (φ : K →+* Γ(Y, ⊤)) (hM : M.IsLB)
    {I : Type} [Fintype I] (s : I → M.Sec) (hc : ⨆ i, nonzeroLocus (s i) = ⊤)
    (hs : ∀ i, IsAffineOpen (nonzeroLocus (s i))) (F : Set Y) (hF : F.Finite) :
    ∃ D : Y.Opens, IsAffineOpen D ∧ ∀ y ∈ F, y ∈ D := by
  have := hF.to_subtype
  choose k hk using fun y : F => exists_chart hM y.1
  obtain ⟨c, h⟩ := exists_isUnit_sum (K := K) (fun y : F => Y.presheaf.stalk y.1)
    (fun y => ((Y.presheaf.germ ⊤ y.1 trivial).hom).comp φ) (fun y i => gs (𝟙 Y) y.1 _ ((s i).f (k y)))
    fun y => by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (show y.1 ∈ (⊤ : Y.Opens) from trivial))
      exact ⟨i, (mem_nonzeroLocus_iff_isUnit _ (hk y)).1 hi⟩
  obtain ⟨t, ht⟩ := exists_sec_sum (fun i => φ (c i)) s
  refine ⟨_, isAffineOpen_nonzeroLocus_sum hM _ s hs t ht, fun y hy => ?_⟩
  rw [mem_nonzeroLocus_iff_isUnit t (hk ⟨y, hy⟩), ht, gs_sum_mul _ _ y (hk ⟨y, hy⟩)]
  convert h ⟨y, hy⟩ using 3 with i
  exact gs_eq (𝟙 Y) y ⊤ trivial _

theorem exists_affine_le_coheight {X : Scheme.{0}} [NoetherianSpace X]
    (h : ∀ F : Set X, F.Finite → ∃ D : X.Opens, IsAffineOpen D ∧ ∀ y ∈ F, y ∈ D) (n : ℕ) :
    ∃ D : Fin n → X.Opens, (∀ i, IsAffineOpen (D i)) ∧
      ∀ x : X, x ∉ ⨆ i, D i → (n : ℕ∞) ≤ Order.coheight x := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun x _ => by simp⟩
  | succ n ih =>
    obtain ⟨D, hD, hn⟩ := ih
    obtain ⟨S, hS, hc, hi, e⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible (⨆ i, D i).isOpen.isClosed_compl
    have := hS.to_subtype
    choose ξ hξ using fun C : S => QuasiSober.sober (hi C.1 C.2) (hc C.1 C.2)
    obtain ⟨D', hD', hF⟩ := h (Set.range ξ) (Set.finite_range _)
    refine ⟨Fin.cons D' D, Fin.cases hD' hD, fun x hx => ?_⟩
    have h₁ : x ∉ D' := fun h' => hx (Opens.mem_iSup.2 ⟨0, h'⟩)
    have h₂ : x ∈ ⋃₀ S := by
      rw [← e]
      intro h'
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h'
      exact hx (Opens.mem_iSup.2 ⟨i.succ, hi⟩)
    obtain ⟨C, hC, hxC⟩ := h₂
    have h₃ : ξ ⟨C, hC⟩ ∉ ⨆ i, D i :=
      (e.ge (⟨C, hC, (hξ ⟨C, hC⟩).mem⟩ : ξ ⟨C, hC⟩ ∈ ⋃₀ S) :)
    have hlt : x < ξ ⟨C, hC⟩ :=
      ⟨(hξ ⟨C, hC⟩).specializes hxC, fun h' => h₁ (Specializes.mem_open h' D'.isOpen (hF _ ⟨_, rfl⟩))⟩
    exact_mod_cast (add_le_add_left (hn _ h₃) 1).trans (Order.coheight_add_one_le hlt)

theorem ringKrullDim_le_of_quasiFinite (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun P Q h =>
    lt_of_le_of_ne (Ideal.comap_mono h.le) fun e => h.ne (PrimeSpectrum.ext
      (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) _ _ h.le (congrArg PrimeSpectrum.asIdeal e)))

theorem coheight_le_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) {g : ℕ}
    (hf : SmoothOfRelativeDimension g f) (x : X) : Order.coheight x ≤ g := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hf.exists_isStandardSmoothOfRelativeDimension x
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain rfl : U = ⊤ := top_le_iff.1 fun p _ => by
    rw [Subsingleton.elim p (f x)]
    exact e hx
  obtain ⟨φ, -, hφ⟩ := h.exists_etale_mvPolynomial
  let _ := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin g) Γ(Spec (CommRingCat.of K), ⊤)) Γ(X, V) := hφ
  have h₁ := ringKrullDim_le_of_quasiFinite (MvPolynomial (Fin g) Γ(Spec (CommRingCat.of K), ⊤)) Γ(X, V)
  rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.mapEquiv (Fin g)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h₁
  have h₂ := (Ideal.height_le_ringKrullDim_of_isPrime (I := (hV.primeIdealOf ⟨x, hx⟩).asIdeal)).trans h₁
  rw [idealHeight_eq_coheight Γ(X, V) (hV.primeIdealOf ⟨x, hx⟩),
    ← coheight_eq_of_isOpenImmersion (x := hV.primeIdealOf ⟨x, hx⟩) hV.fromSpec] at h₂
  have h₃ : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  rw [h₃] at h₂
  simp only [zero_add, Nat.card_eq_fintype_card, Fintype.card_fin] at h₂
  exact_mod_cast h₂

theorem exists_cover_of_infinite (K : Type) [Field K] [Infinite K] (P : PolAV (Spec (CommRingCat.of K))) :
    ∃ D : Fin (P.g + 1) → P.A.left.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have := P.isAb.proper
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : IsNoetherian P.A.left := ⟨⟩
  obtain ⟨N, -, m, s, hc, hs⟩ := P.ample ⊤ (isAffineOpen_top _)
  obtain ⟨D, hD, h⟩ := exists_affine_le_coheight (X := P.A.left) (fun F hF => by
    obtain ⟨D, hD, h⟩ := exists_isAffineOpen_of_finite
      (((P.A.hom ⁻¹ᵁ ⊤).ι ≫ P.A.hom).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      (DVR.linComb_isLB P.L P.isLB _ _) s hc (fun i => (hs i).1) ((P.A.hom ⁻¹ᵁ ⊤).ι ⁻¹' F)
      (hF.preimage (P.A.hom ⁻¹ᵁ ⊤).ι.isOpenEmbedding.injective.injOn)
    exact ⟨_, hD.image_of_isOpenImmersion (P.A.hom ⁻¹ᵁ ⊤).ι, fun y hy =>
      ⟨⟨y, trivial⟩, h ⟨y, trivial⟩ hy, rfl⟩⟩) (P.g + 1)
  refine ⟨D, hD, top_le_iff.1 fun x _ => not_not.1 fun hx => ?_⟩
  have := (h x hx).trans (coheight_le_of_smooth P.A.hom P.smoothDim x)
  exact Nat.not_succ_le_self _ (by exact_mod_cast this)

theorem exists_cover :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X), IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), ∃ D : Fin (P.g + 1) → P.A.left.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ :=
  fun _ _ K _ _ P => exists_cover_of_infinite K P

end GlobalTheory.AffineCover
