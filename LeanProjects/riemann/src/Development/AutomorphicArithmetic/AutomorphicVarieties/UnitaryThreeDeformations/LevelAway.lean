import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem la_avg {A H C : Type} [CommRing A] [IsLocalRing A] [Group H] [Group C] [Finite C] (φ : H →* C)
    (hC : IsUnit (Nat.card C : A)) (a b : H →* GL (Fin 3) A) (ha : ∀ s, φ s = 1 → a s = 1) (hb : ∀ s, φ s = 1 → b s = 1)
    (hab : ∀ s, EntIn (maximalIdeal A) ((a s : Matrix (Fin 3) (Fin 3) A) - (b s : Matrix (Fin 3) (Fin 3) A))) :
    ∃ M : GL (Fin 3) A, ∀ s, a s = M * b s * M⁻¹ := by
  classical
  haveI : Finite (H ⧸ φ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  letI := Fintype.ofFinite (H ⧸ φ.ker)
  have hQ : IsUnit (Fintype.card (H ⧸ φ.ker) : A) := by
    have h1 : Fintype.card (H ⧸ φ.ker) ∣ Nat.card C := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast h1) hC
  let a' := QuotientGroup.lift φ.ker a ha
  let b' := QuotientGroup.lift φ.ker b hb
  let M : Matrix (Fin 3) (Fin 3) A := ∑ q, ((a' q * (b' q)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
  have hred : ∀ q, (residue A).mapMatrix ((a' q * (b' q)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = 1 := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (residue A).mapMatrix (a s : Matrix (Fin 3) (Fin 3) A) =
        (residue A).mapMatrix (b s : Matrix (Fin 3) (Fin 3) A) := by
      ext i j
      exact Ideal.Quotient.eq.2 (hab s i j)
    show (residue A).mapMatrix ((a s * (b s)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = 1
    rw [Units.val_mul, map_mul, h1, ← map_mul, Units.mul_inv, map_one]
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, ← residue_ne_zero_iff_isUnit, RingHom.map_det, ← isUnit_iff_ne_zero,
      ← Matrix.isUnit_iff_isUnit_det, map_sum]
    simp only [hred, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have := (hQ.map (residue A)).map (algebraMap _ (Matrix (Fin 3) (Fin 3) (ResidueField A)))
    simpa using this
  refine ⟨hM.unit, fun s => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  show (a' s : Matrix (Fin 3) (Fin 3) A) * M = M * b' s
  rw [Finset.mul_sum, Finset.sum_mul, eq_comm, ← Equiv.sum_comp (Equiv.mulLeft (s : H ⧸ φ.ker))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  simp only [Equiv.coe_mulLeft, map_mul]
  group

private theorem la_left {R : Type} [CommRing R] (k : GG 3 R) (t : Rˣ) :
    (k * GG.ofGL (tor R t) * k⁻¹).left = k.left * tor R t * k.left⁻¹ := by
  have h : k * GG.ofGL (tor R t) = GG.ofGL (k.left * tor R t * k.left⁻¹) * k := by
    refine SemidirectProduct.ext ?_ (by simp)
    rcases Int.units_eq_one_or k.right with h | h <;> simp [h, theta_tor]
  rw [h, mul_inv_cancel_right]
  rfl

private theorem la_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (t : Rˣ) :
    GG.map f (GG.ofGL (tor R t)) = GG.ofGL (tor S (Units.map f.toMonoidHom t)) := by
  refine SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor R t : Matrix (Fin 3) (Fin 3) R).map f = (tor S _ : Matrix (Fin 3) (Fin 3) S)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero f)]
  simp only [← map_zpow]
  rfl

private theorem la_D {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R) (hr : HasMult η r) (h : CondD η Ψ I r) :
    ∃ k : GG 3 R, ∀ s ∈ I, η s = 1 →
      r s = k * GG.ofGL (tor R (Units.map (algebraMap O R).toMonoidHom (Ψ s))) * k⁻¹ := by
  obtain ⟨k, -, hk⟩ := h
  refine ⟨GG.ofGL k, fun s hs hη => ?_⟩
  have h1 : conjBy k⁻¹ r s = GG.ofGL (tor R (Units.map (algebraMap O R).toMonoidHom (Ψ s))) := by
    refine SemidirectProduct.ext (Units.ext ?_) (by simp [conjBy, hr s, hη])
    show (conjBy k⁻¹ r s).mat = (tor R _ : Matrix (Fin 3) (Fin 3) R)
    rw [tor_val]
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [hk.ine s hs hη, Matrix.diagonal_apply_eq, ← map_zpow]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hab]
      rcases lt_or_gt_of_ne hab with h | h
      · exact hk.low s hη a b (by have : (a : ℕ) < b := h; simp only [wt, wt1]; omega)
      · exact hk.tri s hη a b (by have : (b : ℕ) < a := h; simp only [wt, wt1]; omega)
  rw [← h1]
  simp [conjBy, mul_assoc]

private theorem la_U {O R D : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R] [IsLocalRing R]
    [Algebra O R] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R) (hr : Red η Ψ r)
    (h : CondU η Ψ I r) (ht : ∀ s ∈ kerBar η Ψ I, Ψ s = 1) :
    ∃ k : GG 3 R, ∀ s ∈ I, η s = 1 →
      r s = k * GG.ofGL (tor R (Units.map (algebraMap O R).toMonoidHom (Ψ s))) * k⁻¹ := by
  have hu : IsUnit (Nat.card (ResidueField O)ˣ : O) := by
    letI := Fintype.ofFinite (ResidueField O)
    rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.card_units, Nat.card_eq_fintype_card,
      Nat.cast_pred Fintype.card_pos, FiniteField.cast_card_eq_zero]
    simp
  have hu' : IsUnit (Nat.card (ResidueField O)ˣ : R) := by simpa using hu.map (algebraMap O R)
  let H : Subgroup D := I ⊓ η.ker
  obtain ⟨M, hM⟩ := la_avg (((Units.map (residue O).toMonoidHom).comp Ψ).comp H.subtype) hu'
    ((glPart η r hr.mult).comp (Subgroup.inclusion inf_le_right))
    ((tor R).comp ((Units.map (algebraMap O R).toMonoidHom).comp (Ψ.comp H.subtype)))
    (fun s hs => congrArg SemidirectProduct.left (h s ⟨s.2, hs⟩))
    (fun s hs => by simp [ht s ⟨s.2, hs⟩])
    (fun s => by
      have h1 := congrArg GG.mat (la_map (algebraMap O R) (Ψ s))
      have h2 := hr.red s
      rw [show (r0 η Ψ s).mat.map (algebraMap O R) = _ from h1] at h2
      exact h2)
  refine ⟨GG.ofGL M, fun s hs hη => ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  exact SemidirectProduct.ext (hM ⟨s, hs, hη⟩) ((hr.mult s).trans hη)

open IsDedekindDomain UpperTheory.V in
open scoped Pointwise in
private theorem la_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have h : IsLift (RingEquiv.refl k) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ⟩

open UpperTheory.V in
private theorem la_cls {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (s : G ℚ Ω)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : Chr.cls ℚ Ω N s = 1 :=
  (Chr.clsFacts ℚ Ω N).2.2.1 s 1 fun ζ hζ => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one, h ζ hζ]

open UpperTheory.V UpperTheory.V.Base in
private theorem la_eta {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] [IsScalarTower ℚ K Ω] (hK : IsQi K) (s : G K Ω) : eta4 Ω (galEmb ℚ K Ω s) = 1 := by
  obtain ⟨-, i, hi⟩ := hK
  have hj : algebraMap K Ω i * algebraMap K Ω i = -1 := by rw [← map_mul, hi, map_neg, map_one]
  have hs : s (algebraMap K Ω i) = algebraMap K Ω i := s.commutes i
  generalize algebraMap K Ω i = j at hj hs
  have h : Chr.cls ℚ Ω 4 (galEmb ℚ K Ω s) = 1 := la_cls 4 _ fun ζ hζ => by
    have h0 : (ζ - 1) * (ζ + 1) * (ζ - j) * (ζ + j) = 0 := by linear_combination hζ - (ζ ^ 2 - 1) * hj
    rw [galEmb_apply]
    simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at h0
    rcases h0 with ((rfl | rfl) | rfl) | rfl <;> simp [hs]
  simp [eta4, Chr.dirG, h]

private theorem la_loc {O G Γ ι K : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [Group G] [Group Γ]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) [Field K]
    [Algebra O K] (g₁ : Γ) (r : Γ →* GG 3 K) (hr : F.IsCharZeroPt g₁ r) (v : ι) (hv : v ≠ F.vl) :
    ∃ k : GG 3 K, ∀ s ∈ F.Iv v, F.ηv v s = 1 →
      r (F.loc v s) = k * GG.ofGL (tor K (Units.map (algebraMap O K).toMonoidHom (F.Ψv v s))) * k⁻¹ := by
  obtain ⟨A, _, _, t, r', hp, he⟩ := hr
  have hred : Red (F.ηv v) (F.Ψv v) (r'.comp (F.loc v)) := ⟨fun g => hp.mult _, fun g => hp.red _⟩
  obtain ⟨k, hk⟩ : ∃ k : GG 3 A, ∀ s ∈ F.Iv v, F.ηv v s = 1 → (r'.comp (F.loc v)) s =
      k * GG.ofGL (tor A (Units.map (algebraMap O A).toMonoidHom (F.Ψv v s))) * k⁻¹ := by
    by_cases hb : v ∈ F.Sb
    · exact la_D _ _ _ _ hred.mult ((hp.loc v).2.1 hb)
    · have hT : v ∉ F.Tb := fun h => h.elim hv hb
      exact la_U _ _ _ _ hred ((hp.loc v).2.2 hT) (hF.teich v hT)
  refine ⟨(GG.ofGL (tor K t))⁻¹ * GG.map (A.val : A →+* K) k, fun s hs hη => ?_⟩
  have h1 : GG.map (A.val : A →+* K) (r' (F.loc v s)) = GG.ofGL (tor K t) * r (F.loc v s) * (GG.ofGL (tor K t))⁻¹ :=
    DFunLike.congr_fun he _
  have h2 : r' (F.loc v s) = _ := hk s hs hη
  rw [h2, map_mul, map_mul, map_inv, la_map] at h1
  have h3 : Units.map (A.val : A →+* K).toMonoidHom (Units.map (algebraMap O A).toMonoidHom (F.Ψv v s)) =
      Units.map (algebraMap O K).toMonoidHom (F.Ψv v s) := Units.ext (A.val.commutes _)
  rw [h3] at h1
  rw [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_assoc, ← mul_assoc _ _ (GG.ofGL (tor K t)),
    ← mul_assoc _ _ (GG.ofGL (tor K t)), ← mul_assoc (GG.map _ k), h1]
  group

open UpperTheory.V UpperTheory.V.Base in
theorem UpperTheory.V.UnitaryThreeInertia.levelAway_of_pt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω], IsQi K → ∀ (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r → ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), (∀ s : G K Ω, (ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)) = (r (toGS Ω _ (s.restrictScalars ℚ))).mat) → Af.LevelAway l N ρ := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hD S A F hF K _ _ _ _ hK g₁ _ r hr ρ hρ w hw
  have hok := hostFrame_ok Ω c e ψ o₁ hD S A F hF
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ,
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
  refine ⟨B, hB, ?_⟩
  have hρ' : ∀ s, ρ s = (r (toGS Ω _ (galEmb ℚ K Ω s))).left := fun s => Units.ext (hρ s)
  have hI : ∀ s ∈ Ine (F := K) B, galEmb ℚ K Ω s ∈ Ine (F := ℚ) B := fun s hs => hs
  have hl : ¬ B.valuation (l : Ω) < 1 := fun h => hw (((places K Ω l B).2.2.1 w hB).1 h)
  obtain ⟨p1, p2, p3, p4⟩ := places ℚ Ω l B
  have htriv : (∀ s ∈ Ine (F := ℚ) B, toGS Ω (S : Set Pl) s = 1) →
      ∃ χ : Fin 3 → G K Ω →* (Qbar l)ˣ, (∀ i, Af.KillsMu N (χ i)) ∧ Af.IsDiagOn ρ (Ine (F := K) B) χ := fun h =>
    ⟨fun _ => 1, fun _ _ _ => rfl, 1, fun s hs => by rw [hρ', h _ (hI s hs), map_one]; simp⟩
  by_cases hT : B = ⊤
  · exact htriv fun s hs => by rw [(p2 hT).1, Subgroup.mem_bot] at hs; rw [hs, map_one]
  obtain ⟨v, hv⟩ := p1 hT
  by_cases hvS : v ∈ S
  swap
  · refine htriv fun s hs => (QuotientGroup.eq_one_iff s).2 ?_
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
    simp only [Set.mem_iUnion]
    exact ⟨v, hvS, B, hv, hs⟩
  have hvl : (⟨v, hvS⟩ : S) ≠ F.vl := fun h => hl ((p3 v hv).2 (by have := hF.vl; rw [← h] at this; exact this))
  obtain ⟨k, hk⟩ := la_loc F hok g₁ r hr ⟨v, hvS⟩ hvl
  obtain ⟨g, hg⟩ := la_conj (hF.isOver ⟨v, hvS⟩) hv
  let θ : G K Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp
    ((Chr.dirG ℚ Ω ψ).comp (galEmb ℚ K Ω))
  refine ⟨fun i => θ ^ wt1 i, fun i s hs => ?_, ((r (toGS Ω _ g) * k).left)⁻¹, fun s hs => ?_⟩
  · have : Chr.cls ℚ Ω N (galEmb ℚ K Ω s) = 1 := la_cls N _ hs
    simp [θ, Chr.dirG, this]
  have h2 := hg _ (hI s hs)
  have h3 : g⁻¹ * galEmb ℚ K Ω s * g ∈ F.D ⟨v, hvS⟩ := by rw [hF.D]; exact h2.1
  have h4 : F.ηv ⟨v, hvS⟩ ⟨_, h3⟩ = 1 := by
    show F.η.comp F.π (g⁻¹ * galEmb ℚ K Ω s * g) = 1
    rw [hF.η, map_mul, map_mul, la_eta hK, map_inv, mul_one, inv_mul_cancel]
  have h5 : F.Ψv ⟨v, hvS⟩ ⟨_, h3⟩ = Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω s) := by
    show F.Ψ.comp F.π (g⁻¹ * galEmb ℚ K Ω s * g) = _
    have : cycZ ℚ Ω l (galEmb ℚ K Ω s) = 1 := p4 hl (hI s hs)
    rw [hF.Ψ, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    simp [Chr.Psi, chiO, this]
  have h6 := hk ⟨_, h3⟩ (by rw [Subgroup.mem_subgroupOf, hF.I]; exact h2) h4
  have h7 : F.loc ⟨v, hvS⟩ ⟨_, h3⟩ = (toGS Ω _ g)⁻¹ * toGS Ω _ (galEmb ℚ K Ω s) * toGS Ω _ g := by
    show F.π (g⁻¹ * galEmb ℚ K Ω s * g) = _
    rw [hF.π, map_mul, map_mul, map_inv]
  rw [h5, h7, map_mul, map_mul, map_inv] at h6
  have h8 : r (toGS Ω _ (galEmb ℚ K Ω s)) =
      r (toGS Ω _ g) * k * GG.ofGL (tor _ (θ s)) * (r (toGS Ω _ g) * k)⁻¹ := by
    rw [_root_.mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc _ k⁻¹, ← mul_assoc k, ← mul_assoc k]
    erw [← h6]
    group
  rw [hρ', h8, la_left, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right, tor_val]
  rfl
